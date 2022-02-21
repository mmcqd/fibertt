open Core
open Readers


type syn_tac = (Dom.tp * Syn.t) elab
type chk_tac = Dom.tp -> Syn.t elab


let match_goal goal k = k (Eval.force goal)

let chk_tac k = fun goal -> match_goal goal k
let syn_tac tac = tac

let run_syn (t : syn_tac) : (Dom.tp * Syn.t) elab = t
let run_chk (t : chk_tac) : goal:Dom.tp -> Syn.t elab = fun ~goal -> t goal


module U = 
struct
  open ElabMonad
  
  let formation : chk_tac = chk_tac @@ function
    | Dom.U -> ret Syn.U
    | _ -> failwith "U.formation"

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
    | _ -> failwith "Singleton.formation"
  
  let intro (e : chk_tac) : chk_tac = chk_tac @@ function
    | Dom.Singleton {tm ; tp} -> 
      let* e = run_chk ~goal:tp e in
      let* e_d = lift_eval @@ Eval.eval e in
      let+ () = lift_conv @@ Conv.conv e_d tm tp in
      Syn.InS e
    | _ -> failwith "Singleton.intro"
  
  let elim (e : syn_tac) : syn_tac =
    let+ tp,e = run_syn e in
    match_goal tp @@ function
      | Dom.Singleton {tp ; _} -> tp, Syn.OutS e
      | _ -> failwith "Sineleton.elim"

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
    | _ -> failwith "Pi.formation"


  let intro (x : string) (body : chk_tac) : chk_tac = chk_tac @@ function
    | Dom.Pi (_,dom,ran) -> 
      let+ body = abstract ~name:x ~tp:dom @@ fun v -> 
        let* body_tp = lift_comp @@ Eval.do_clo ran v in 
        run_chk ~goal:body_tp body
      in
      Syn.Lam (x,body)
    | _ -> failwith "Pi.intro"

  let elim (f : syn_tac) (e : chk_tac) : syn_tac =
    let* tp,f = run_syn f in
    match_goal tp @@ function
      | Dom.Pi (_,dom,ran) -> 
        let* e = run_chk ~goal:dom e in
        let* e_dom = lift_eval @@ Eval.eval e in
        let+ tp = lift_comp @@ Eval.do_clo ran e_dom in
        tp,Syn.Ap (f,e)
      | _ -> failwith "Pi.elim"
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
    | _ -> failwith "Signature.formation"

  let intro xs = chk_tac @@ function
    | Dom.Sig sign ->
      let rec go fields xs =
        match fields,xs with
          | Dom.Nil, [] -> ret []
          | Dom.Cons (field,tp,sign), (field', tac) :: xs when String.equal field field' -> 
            let* x = run_chk ~goal:tp tac in
            let* x_d = lift_eval @@ Eval.eval x in
            let* fields = lift_comp @@ Eval.do_sig_clo sign x_d in
            let+ xs = go fields xs in
            (field,x) :: xs
          | _ -> failwith "Signature.intro"
      in 
      let+ xs = go sign xs in
      Syn.Struct xs
    | _ -> failwith "Signature.intro"

  let elim (field : string) (s : syn_tac) : syn_tac =
    let* tp,s = run_syn s in
    let* s_d = lift_eval @@ Eval.eval s in
    match_goal tp @@ function
      | Dom.Sig fields -> 
        let rec go = function
          | Dom.Nil -> failwith "Couldn't find field"
          | Dom.Cons (field',tp,_) when String.equal field field' ->
            ret (tp, Syn.Proj (field,s))
          | Dom.Cons (field' , _, sign) ->
            let* proj = lift_comp @@ Eval.do_proj field' s_d in
            let* sign = lift_comp @@ Eval.do_sig_clo sign proj in
            go sign
        in
        go fields
      | _ -> failwith (sprintf "Expected record but found %s" (Dom.show tp))
  
  let patch (patches : [`Patch of string * chk_tac | `Var of string] list) (sig_tac : chk_tac) : chk_tac = chk_tac @@ function
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
          | `Var field :: patches, Dom.Cons (field',tp,sign) when String.equal field field' -> 
            abstract ~name:field ~tp @@ fun v ->
            let* sign = lift_comp @@ Eval.do_sig_clo sign v in
            let* tp = lift_quote ~unfold:false @@ Quote.quote tp Dom.U in
            let+ sign = go patches sign in
            Syn.Cons (field,tp,sign)
          | [], _ -> lift_quote ~unfold:false @@ Quote.quote_sig sign
          | _ -> failwith "too many patches"
      in      
      let* sign = run_chk ~goal:Dom.U sig_tac in
      let* sign_d = lift_eval @@ Eval.eval sign in
      begin
      match Eval.force sign_d with
        | Dom.Sig sign -> 
          let+ sign = go patches sign in
          Syn.Sig sign
        | _ -> failwith "patching non-record"
      end
    | _ -> failwith "Signature.patch"

  let rec sig_append sig1 sig2 =
    match sig1 with
      | Syn.Nil -> sig2
      | Syn.Cons (f,tp,sig1) -> Syn.Cons (f,tp, sig_append sig1 sig2)

  (* List : sig {A : Type} -> Type ==> sig {A : Type ; fib : List struct {A => A}}  *)
  let total (fam : syn_tac) : chk_tac = chk_tac @@ function
    | Dom.U -> 
      let rec mk_total fib acc = function
        | Dom.Nil -> 
          let* ap = lift_comp @@ Eval.do_ap fib (Dom.Struct (List.rev acc)) in
          let+ clo = lift_eval @@ Eval.mk_clo Syn.Nil in
          Dom.Cons ("fib",ap,clo)
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
      begin
      match tp with
        | Dom.Pi (name,Dom.Sig sign,ran) ->
          let* ran = abstract ~name ~tp:(Dom.Sig sign) @@ fun v -> lift_comp @@ Eval.do_clo ran v in
          begin
          match ran with
            | Dom.U ->       
              let* total = mk_total fib [] sign in
              let+ total = lift_quote ~unfold:false @@ Quote.quote_sig total in
              Syn.Sig total
            | _ -> failwith "Taking total space of non type family"
          end
        | _ -> failwith "taking total space of non sig-indexed type family"
      end
    | _ -> failwith "Signature.total"

  let extract_fields = function
    | Dom.Nil -> []
    | Dom.Cons (f,_,{tm = sign ; _}) ->
      let rec go = function
        | Syn.Nil -> []
        | Syn.Cons (f,_,sign) -> f :: go sign
      in
      f :: go sign

end


module Var =
struct
  open ElabMonad
  let intro (x : string) : syn_tac =
    let* ctx = read_local in
    let+ global = read_global in
    match Local_ctx.find_tp_and_idx x ctx with
      | Some (i,tp) -> tp, Syn.Idx i
      | None -> 
        match Global_ctx.find_name ~name:x ~ctx:global with
          | Some (tp,_) -> tp, Syn.Def x
          | None -> failwith ("unbound variable: "^x)
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
 