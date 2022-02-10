open Core
open Readers

let mk_clo syn : Dom.clo eval =
  let open EvalMonad in
  let+ env = read_env in
  Dom.{syn ; env}

let rec eval : Syn.t -> Dom.t eval = let open EvalMonad in function
  | Syn.U -> ret Dom.U
  | Syn.Idx i ->
    let+ env = read_env in
    List.nth_exn env i
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
  | Syn.RTyCons (field, tp, rest) ->
    let+ tp,rest = eval_fam tp rest in
    Dom.RTyCons (field,tp,rest)
  | Syn.RTyNil -> ret Dom.RTyNil
  | Syn.RCons (field,x,xs) -> 
    let* x = eval x in
    let+ xs = eval xs in
    Dom.RCons (field, x, xs)
  | Syn.RNil -> ret Dom.RNil
  | Syn.Proj (field,r) -> 
    let* r = eval r in
    lift_comp @@ do_proj field r
  | Syn.Rest r ->
    let* r = eval r in
    lift_comp @@ do_rest r

and eval_fam base fam = let open EvalMonad in
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
        | _ -> failwith "do_ap"
      end
    | _ -> failwith "do_ap"

and do_outS e = let open CompMonad in
  match e with
    | Dom.InS e' -> ret e'
    | Dom.Neu {hd ; sp ; tp} -> 
      begin
      match force tp with
        | Dom.Singleton {tp ; tm} -> 
          let+ hd = do_hd do_outS hd in
          Dom.Neu {hd ; sp = Dom.OutS {tm ; tp} :: sp ; tp}
        | _ -> failwith "do_outS"
      end
    | _ -> failwith "do_outS"

and do_proj field r = let open CompMonad in
  match r with
    | Dom.RCons (field',x,_) when String.equal field field' -> ret x
    | Dom.RCons (_,_,xs) -> do_proj field xs
    | Dom.Neu {hd ; sp ; tp} ->
      let* tp = do_proj_tp field r tp in
      let+ hd = do_hd (do_proj field) hd in
      Dom.Neu {hd ; sp = Dom.Proj field :: sp ; tp}
    | _ -> failwith "do_proj"

and do_proj_tp field r tp = let open CompMonad in
  match force tp with
    | Dom.RTyCons (field',tp,_) when String.equal field field' -> ret tp
    | Dom.RTyCons (field',_,rest) -> 
      let* f = do_proj field' r in
      let* rest = do_clo rest f in
      do_proj_tp field r rest
    | _ -> failwith "do_proj_tp"
  
and do_rest r = let open CompMonad in
  match r with
    | Dom.RCons (_,_,xs) -> ret xs
    | Dom.Neu {hd ; sp ; tp} ->
      begin
      match force tp with
        | Dom.RTyCons (field,_,rest) -> 
          let* hd = do_hd do_rest hd in
          let* f = do_proj field r in
          let+ rest = do_clo rest f in
          Dom.Neu {hd ; sp = Dom.Rest :: sp ; tp = rest}
        | _ -> failwith "do_rest"
      end
    | _ -> failwith "do_rest"
      

and do_hd f = let open CompMonad in function
  | Dom.Def {name ; value} -> 
    let+ global = CompMonad.read in  
    let value = Lazy.map ~f:(fun v -> run (f v) global) value in
    Dom.Def {name ; value}
  | hd -> ret hd

and do_clo : Dom.clo -> Dom.t -> 'a CompMonad.t = fun clo e ->
  CompMonad.lift_eval clo.env @@
  EvalMonad.extend e @@
  eval clo.syn


and force : Dom.t -> Dom.t = function
  | Dom.Neu {hd = Def {value ; _} ; _ } -> force @@ Lazy.force value
  | d -> d