open Core
open Readers


type syn_tac = (Dom.tp * Syn.t) elab
type chk_tac = Dom.tp -> Syn.t elab


let match_goal goal k = k (Eval.force goal)

let chk_tac k = fun goal -> match_goal goal k
let syn_tac tac = tac

let run_syn (t : syn_tac) : (Dom.tp * Syn.t) elab = t
let run_chk (t : chk_tac) : goal:Dom.tp -> Syn.t elab = fun ~goal -> t goal

let mode_switch (t : syn_tac) : chk_tac = let open ElabMonad in fun goal ->
  let* synthed,e = run_syn t in
  (* printf "%s\n=======\n%s\n=======\n%s\n\n" (Dom.show synthed) (Syn.show e) (Dom.show goal); *)
  let+ () = lift_conv @@ Conv.conv goal synthed Dom.U in
  e


module U = 
struct
  open ElabMonad
  
  let formation : chk_tac = chk_tac @@ function
    | Dom.U -> ret Syn.U
    | _ -> fail "Type has type Type"

end

module Singleton =
struct
  open ElabMonad
  let formation (tm : chk_tac) (tp : chk_tac) : chk_tac = chk_tac @@ function    
    | Dom.U ->
      let* tp = run_chk ~goal:Dom.U tp in
      let* tp_d = lift_eval @@ Eval.eval tp in
      let+ tm = run_chk ~goal:tp_d tm in
      Syn.Singleton {tm ; tp}
    | _ -> fail "Singleton.formation"
  
  let intro (e : chk_tac) : chk_tac = chk_tac @@ function
    | Dom.Singleton {tm ; tp} -> 
      let* e = run_chk ~goal:tp e in
      let* e_d = lift_eval @@ Eval.eval e in
      let+ () = lift_conv @@ Conv.conv e_d tm tp in
      Syn.InS e
    | _ -> fail "Singleton.intro"
  
  let elim (e : syn_tac) : syn_tac =
    let* tp,e = run_syn e in
    match_goal tp @@ function
      | Dom.Singleton {tp ; _} -> ret (tp, Syn.OutS e)
      | _ -> fail "Singleton.elim"

  let infer : chk_tac = chk_tac @@ function
    | Dom.Singleton {tm ; tp} ->
      let+ tm = lift_quote ~unfold:false @@ Quote.quote tm tp in
      Syn.InS tm
    | _ -> fail "Singleton.infer"

end

module Pi =
struct
  open ElabMonad
  let formation (x : string) (dom : chk_tac) (ran : chk_tac) : chk_tac = chk_tac @@ function
    | Dom.U -> 
      let* dom_s = run_chk ~goal:Dom.U dom in
      let* dom_d = lift_eval @@ Eval.eval dom_s in
      let+ ran_s = abstract ~name:x ~tp:dom_d @@ fun _ -> run_chk ~goal:Dom.U ran in
      Syn.Pi (x,dom_s,ran_s)
    | _ -> fail "Pi.formation"


  let intro (x : string) (body : chk_tac) : chk_tac = chk_tac @@ function
    | Dom.Pi (_,dom,ran) -> 
      let+ body = abstract ~name:x ~tp:dom @@ fun v -> 
        let* body_tp = lift_comp @@ Eval.do_clo ran v in 
        run_chk ~goal:body_tp body
      in
      Syn.Lam (x,body)
    | _ -> fail "Pi.intro"

  let elim (f : syn_tac) (e : chk_tac) : syn_tac =
    let* tp,f = run_syn f in
    match_goal tp @@ function
      | Dom.Pi (_,dom,ran) -> 
        let* e = run_chk ~goal:dom e in
        let* e_dom = lift_eval @@ Eval.eval e in
        let+ tp = lift_comp @@ Eval.do_clo ran e_dom in
        tp,Syn.Ap (f,e)
      | _ -> fail "Pi.elim"
end

module Signature =
struct
  open ElabMonad


  let formation fields = chk_tac @@ function
    | Dom.U -> 
      let rec go = function
        | [] -> ret Syn.Nil
        | (field,tac) :: fields ->
          let* tp = run_chk ~goal:Dom.U tac in
          let* tp_d = lift_eval @@ Eval.eval tp in
          let+ fields = abstract ~name:field ~tp:tp_d @@ fun _ -> go fields in
          Syn.Cons (field,tp,fields)
      in
      let+ fields = go fields in
      Syn.Sig fields
    | _ -> fail "Signature.formation"

  let intro xs = chk_tac @@ function
    | Dom.Sig sign ->
      let rec go fields xs =
        match fields,xs with
          | Dom.Nil, [] -> ret []
          | Dom.Cons (field,tp,sign), (field', tac) :: xs -> 
            let* tac,xs = match tp,String.equal field field' with
              | _, true -> ret (tac,xs) 
              | Dom.Singleton _,false -> ret (Singleton.infer , (field',tac)::xs)
              | _ -> fail "Missing record field"
            in
            let* x = run_chk ~goal:tp tac in
            let* x_d = lift_eval @@ Eval.eval x in
            let* fields = lift_comp @@ Eval.do_sig_clo sign x_d in
            let+ xs = go fields xs in
            (field,x) :: xs
          | Dom.Cons (field,(Dom.Singleton _ as tp),sign), [] ->
            let* x = run_chk ~goal:tp Singleton.infer in
            let* x_d = lift_eval @@ Eval.eval x in
            let* fields = lift_comp @@ Eval.do_sig_clo sign x_d in
            let+ xs = go fields xs in
            (field,x) :: xs
          | _ -> fail "Signature.intro"
      in 
      let+ xs = go sign xs in
      Syn.Struct xs
    | _ -> fail "Signature.intro"

  let elim (field : string) (s : syn_tac) : syn_tac =
    let* tp,s = run_syn s in
    let* s_d = lift_eval @@ Eval.eval s in
    match_goal tp @@ function
      | Dom.Sig fields -> 
        let rec go = function
          | Dom.Nil -> fail (sprintf "Couldn't find field %s" field)
          | Dom.Cons (field',tp,_) when String.equal field field' ->
            ret (tp, Syn.Proj (field,s))
          | Dom.Cons (field' , _, sign) ->
            let* proj = lift_comp @@ Eval.do_proj field' s_d in
            let* sign = lift_comp @@ Eval.do_sig_clo sign proj in
            go sign
        in
        go fields
      | _ -> fail (sprintf "Expected record but found %s" (Dom.show tp))
  
  let patch (patches : [`Patch of string * chk_tac | `Field of string] list) (sig_tac : chk_tac) : chk_tac = chk_tac @@ function
    | Dom.U ->
      let rec go patches sign =
        match patches,sign with
          | `Patch (field,patch) :: patches, Dom.Cons (field',tp,sign) when String.equal field field' -> 
            let* tm = run_chk ~goal:tp patch in
            let* tp = lift_quote ~unfold:false @@ Quote.quote tp Dom.U in
            let sub = Syn.Singleton {tm ; tp} in
            let* sub_d = lift_eval @@ Eval.eval sub in
            abstract ~name:field ~tp:sub_d @@ fun v ->
            let* v = lift_comp @@ Eval.do_outS v in
            let* sign = lift_comp @@ Eval.do_sig_clo sign v in
            let+ sign = go patches sign in
            Syn.Cons (field,sub,sign)
          | `Field field :: patches, Dom.Cons (field',tp,sign) when String.equal field field' -> 
            abstract ~name:field ~tp @@ fun v ->
            let* sign = lift_comp @@ Eval.do_sig_clo sign v in
            let* tp = lift_quote ~unfold:false @@ Quote.quote tp Dom.U in
            let+ sign = go patches sign in
            Syn.Cons (field,tp,sign)
          | [], _ -> lift_quote ~unfold:false @@ Quote.quote_sig sign
          | _ -> fail "too many patches"
      in      
      let* sign = run_chk ~goal:Dom.U sig_tac in
      let* sign_d = lift_eval @@ Eval.eval sign in
      begin
      match Eval.force sign_d with
        | Dom.Sig sign -> 
          let+ sign = go patches sign in
          Syn.Sig sign
        | _ -> fail "patching non-record"
      end
    | _ -> fail "Signature.patch"

  (* let curry (fam : syn_tac) : syn_tac = syn_tac @@ 
    let* tp,tm = run_syn fam in
    let rec go = function
      | Dom.Pi (x,dom,ran) -> 
      | _ -> fail "currying non function"
    in
    fail ""
 *)
(* 
  let uncurry (tac : chk_tac) : chk_tac = chk_tac @@ function
    | Dom.U ->
      let* tp = run_chk ~goal:Dom.U tac in
      let* tp_d = lift_eval @@ Eval.eval tp in
      let rec go = function
        | Dom.Pi (name,dom,ran) -> 
          let* ran = abstract ~name ~tp:dom @@ fun v -> lift_comp @@ Eval.do_clo ran v in
          let* sign,tp = go ran in
          let* sign = lift_quote ~unfold:false @@ Quote.quote_sig sign in
          let+ sign = lift_eval @@ Eval.mk_clo sign in
          Dom.Cons (name,dom,sign),tp
        | tp -> 
          let+ tp = lift_quote ~unfold:false @@ Quote.quote tp Dom.U in
          Dom.Nil,tp
      in
      let+ dom,ran = go tp_d in

    | _ -> fail "uncurry" *)

  let is_sig_indexed_type_fam = function 
    | Dom.Pi (name,Dom.Sig sign,ran) -> 
      let+ ran = abstract ~name ~tp:(Dom.Sig sign) @@ fun v -> lift_comp @@ Eval.do_clo ran v in
      begin
      match ran with
        | Dom.U -> Some sign
        | _ -> None
      end
    | _ -> ret None

  (* List : sig {A : Type} -> Type ==> sig {A : Type ; pt : List struct {A => A}}  *)
  let total (fam : syn_tac) : chk_tac = chk_tac @@ function
    | Dom.U -> 
      let rec mk_total fib acc = function
        | Dom.Nil -> 
          let* ap = lift_comp @@ Eval.do_ap fib (Dom.Struct (List.rev acc)) in
          let+ clo = lift_eval @@ Eval.mk_clo Syn.Nil in
          Dom.Cons ("pt",ap,clo)
        | Dom.Cons (field,tp,sign) ->
          let* sign = abstract ~name:field ~tp @@ fun v -> 
            let* sign = lift_comp @@ Eval.do_sig_clo sign v in
            let* sign = mk_total fib ((field,v) :: acc) sign in
            lift_quote ~unfold:false @@ Quote.quote_sig sign
          in
          let+ clo = lift_eval @@ Eval.mk_clo sign in
          Dom.Cons (field,tp,clo)
      in
      let* tp,tm = run_syn fam in
      let* fib = lift_eval @@ Eval.eval tm in
      let* sign_opt = is_sig_indexed_type_fam tp in
      begin
      match sign_opt with
        | Some sign ->
          let* total = mk_total fib [] sign in
              let+ total = lift_quote ~unfold:false @@ Quote.quote_sig total in
              Syn.Sig total
        | None -> fail "Can only take total space of a sig-indexed type family"
      end
    | _ -> fail "Signature.total"

  let extract_fields = function
    | Dom.Nil -> []
    | Dom.Cons (f,_,{tm = sign ; _}) ->
      let rec go = function
        | Syn.Nil -> []
        | Syn.Cons (f,_,sign) -> f :: go sign
      in
      f :: go sign
  

  (* let fill_sig (pt_tac : chk_tac) : chk_tac = chk_tac @@ function
    | Dom.Sig sign -> 
      let rec go = function 
        | Dom.Nil -> fail "filling signature without pt"
        | Dom.Cons (field,tp,sign) ->
          let* tm = if String.equal field "pt" then run_chk ~goal:tp pt_tac else run_chk ~goal:tp Singleton.infer in
          let* tm_d = lift_eval @@ Eval.eval tm in
          let* sign = lift_comp @@ Eval.do_sig_clo sign tm_d in
          let+ sign = go sign in 
          (field,tm) :: sign
      in
      let+ xs = go sign in
      Syn.Struct xs
    | _ -> fail "filling non-sig" *)

end


module Var =
struct
  open ElabMonad
  let intro (x : string) : syn_tac =
    let* ctx = read_local in
    let* global = read_global in
    match Local_ctx.find_tp_and_idx x ctx with
      | Some (i,tp) -> ret (tp, Syn.Idx i)
      | None -> 
        match Global_ctx.find_name ~name:x ~ctx:global with
          | Some (tp,_) -> ret (tp, Syn.Def x)
          | None -> fail ("unbound variable: "^x)
end

module Hole =
struct
  open ElabMonad
  let intro : chk_tac = fun goal ->
    let* goal = lift_quote ~unfold:false @@ Quote.quote goal Dom.U in
    let* goal = lift_print @@ Pretty.print goal in 
    let* {tps ; _} = read_local in
    let+ tps = sequence @@ List.map tps ~f:(fun (v,(_,tp)) -> let+ tp = lift_quote ~unfold:false @@ Quote.quote tp Dom.U in (v,tp)) in
    let tps = Pretty.print_local_ctx tps in
    raise (Hole (sprintf "Hole:%s\n\n⊢ %s" tps goal))
end

module Point =
struct
  open ElabMonad

  let intro (tac : syn_tac) : syn_tac = syn_tac @@
    let* tp,tm = run_syn tac in
    let* tp = lift_quote ~unfold:false @@ Quote.quote tp Dom.U in
    let+ sign = lift_eval @@ Eval.eval @@ Syn.Sig (Syn.Cons ("tp",Syn.U,Syn.Cons ("pt",Syn.Idx 0,Syn.Nil))) in
    sign, Syn.Struct [("tp",tp) ; ("pt",tm)]

end
 
module Implicit =
struct
  open ElabMonad
  (* Kinda cannot believe how well this works, thanks cooltt devs!! *)
  let rec intro_singletons (t : chk_tac) : chk_tac = fun goal -> run_chk ~goal @@ 
  match_goal goal @@ function
    | Dom.Singleton _ -> Singleton.intro @@ intro_singletons t
    | _ -> t

  let rec elim_singletons (t : syn_tac) : syn_tac =
    let* tp,e = run_syn t in
    match_goal tp @@ function
      | Dom.Singleton _ -> elim_singletons @@ Singleton.elim (ret (tp,e))
      | _ -> ret (tp,e)
(* 
  let intro_point (t : chk_tac) : chk_tac = chk_tac @@ function
    |  *)

  let intro_conversions (t : syn_tac) : chk_tac = chk_tac @@ fun goal -> 
    match goal with
      | Dom.U -> 
        let* tp, _ = run_syn t in
        let* sign_opt = Signature.is_sig_indexed_type_fam tp in 
        begin
        match sign_opt with
          | Some _ -> run_chk ~goal:Dom.U @@ Signature.total t
          | None -> run_chk ~goal:Dom.U @@ mode_switch t
        end
      | _ -> run_chk ~goal @@ mode_switch t


end
