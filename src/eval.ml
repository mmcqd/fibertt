open Core
open Readers

let mk_clo tm : 'a Dom.clo eval =
  let open EvalMonad in
  let+ env = read_env in
  Dom.{tm ; env}

let rec eval : Syn.t -> Dom.t eval = let open EvalMonad in function
  | Syn.U -> ret Dom.U
  | Syn.Idx i -> find_idx i
  | Syn.Def name ->
    let+ tp,tm = find_name name in
    Dom.Neu {hd = Def {name ; value = lazy tm} ; sp = [] ; tp}
  | Syn.Lam (x,body) -> 
    let+ body = mk_clo body in
    Dom.Lam (x,body)
  | Syn.Ap (f,e) ->
    let* f = eval f in
    let* e = eval e in
    lift_comp @@ do_ap f e 
  | Syn.Pi (x,dom,ran) ->
    let+ dom,ran = eval_fam dom ran in
    Dom.Pi (x,dom,ran)
  | Syn.InS e ->
    let+ e = eval e in
    Dom.InS e
  | Syn.OutS e -> 
    let* e = eval e in
    lift_comp @@ do_outS e
  | Syn.Singleton {tm ; tp} ->
    let* tm = eval tm in
    let+ tp = eval tp in
    Dom.Singleton {tm ; tp}
  | Syn.Struct xs -> 
    let fields,xs = List.unzip xs in
    let+ xs = sequence @@ List.map ~f:eval xs in
    Dom.Struct (List.zip_exn fields xs)
  | Syn.Proj (field,r) -> 
    let* r = eval r in
    lift_comp @@ do_proj field r
  | Syn.Sig fields -> 
    let+ fields = eval_sig fields in
    Dom.Sig fields

and eval_sig = let open EvalMonad in function
  | Syn.Nil -> ret Dom.Nil
  | Syn.Cons (field,tp,sign) -> 
    let+ (tp,sign) = eval_fam tp sign in
    Dom.Cons (field,tp,sign)
    
and eval_fam : 'a. Syn.t -> 'a -> (Dom.t * 'a Dom.clo) eval = let open EvalMonad in fun base fam ->
  let* base = eval base in
  let+ fam = mk_clo fam in
  (base,fam)

and do_ap f e = let open CompMonad in
  match f with
    | Dom.Lam (_,clo) -> do_clo clo e
    | Dom.Neu {hd ; sp ; tp} ->
      begin
      match force tp with
        | Dom.Pi (_,dom,ran) ->
          let* tp = do_clo ran e in
          let+ hd = do_hd (fun v -> do_ap v e) hd in
          Dom.Neu {hd ; sp = Dom.Ap {tm = e ; tp = dom} :: sp ; tp}
        | _ -> failwith (sprintf "do_ap - expected pi: %s" (Dom.show tp))
      end
    | _ -> failwith "do_ap"

and do_outS e = let open CompMonad in
  match e with
    | Dom.InS e' -> ret e'
    | Dom.Neu {tp ; _} -> 
      begin
      match force tp with
        | Dom.Singleton {tm ; _} -> ret tm
        | _ -> failwith "do_outS"
      end
    | _ -> failwith "do_outS"

and do_proj field s = let open CompMonad in
  match s with
    | Dom.Struct xs -> ret (List.Assoc.find_exn ~equal:String.equal xs field)
    | Dom.Neu {hd ; sp ; tp} ->
      begin
      match force tp with
        | Dom.Sig fields ->
          let* hd = do_hd (do_proj field) hd in
          do_proj_neu hd sp field fields
        | _ -> failwith (sprintf "do_proj - %s" (Dom.show tp))
      end
    | _ -> failwith "do_proj"
      

and do_proj_neu hd sp field = let open CompMonad in function
  | Dom.Nil -> failwith "do_proj_neu"
  | Dom.Cons (field',tp,_) when String.equal field field' -> ret @@ Dom.Neu {hd ; sp = Dom.Proj field :: sp ; tp}
  | Dom.Cons (field',_,sign) as tp ->
    let* proj = do_proj_neu hd sp field' tp in
    let* sign = do_sig_clo sign proj in
    do_proj_neu hd sp field sign


and do_hd f = let open CompMonad in function
  | Dom.Def {name ; value} -> 
    let+ global = CompMonad.read in  
    let value = Lazy.map ~f:(fun v -> run_exn (f v) global) value in
    Dom.Def {name ; value}
  | hd -> ret hd


and do_spine hd : Dom.elim list -> Dom.t comp = let open CompMonad in List.fold_right ~init:(ret hd) ~f:(fun elim sp ->
  let* sp = sp in 
  match elim with 
    | Dom.Ap {tm ; _} -> do_ap sp tm
    | Dom.Proj field -> do_proj field sp)

and do_clo : Syn.t Dom.clo -> Dom.t -> Dom.t comp = fun clo e ->
  CompMonad.lift_eval clo.env @@
  EvalMonad.extend e @@
  eval clo.tm

and do_multi_clo : Syn.t Dom.clo -> Dom.t list -> Dom.t comp = fun clo es ->
  CompMonad.lift_eval clo.env @@ 
  EvalMonad.multi_extend es @@
  eval clo.tm

and do_sig_clo : Syn.signature Dom.clo -> Dom.t -> Dom.signature comp = fun clo e ->
  CompMonad.lift_eval clo.env @@
  EvalMonad.extend e @@
  eval_sig clo.tm

and force : Dom.t -> Dom.t = function
  | Dom.Neu {hd = Def {value ; _} ; _ } -> force @@ Lazy.force value
  | d -> d



(* 
  
x : sig {A : Type ; B : Type}

split x at x y => ...with
  | (x,y) => ...

  
*)