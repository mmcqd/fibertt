open Core
open Readers

let rec term : Syn.t -> string print = let open PrintMonad in function
  | Lam (x,body) -> 
    let+ body = abstract x @@ term body in
    sprintf "\\%s => %s" x body
  | Pi ("_",dom,ran) ->
    let* dom = match dom with Pi _ -> atom dom | _ -> term dom in
    let+ ran = abstract "_" @@ term ran in
    sprintf "%s -> %s" dom ran
  | Pi (x,dom,ran) ->
    let* dom = term dom in
    let+ ran = abstract x @@ term ran in
    sprintf "(%s : %s) -> %s" x dom ran
  | Ap (f,e) ->
    let* f = match f with Ap _ -> term f | _ -> atom f in
    let+ e = atom e in
    sprintf "%s %s" f e
  | InS e -> term e
  | OutS e -> term e
  | Singleton {tm ; tp} ->
    let* tm = atom tm in
    let+ tp = atom tp in
    sprintf "Sub %s %s" tp tm
  | (RTyCons _ | RTyNil) as r ->
    let+ r = record_ty r in
    sprintf "sig {%s}" r
  | (RCons _ | RNil) as r ->
    let+ r = record r in
    sprintf "struct {%s}" r
  | t -> atom t

and atom : Syn.t -> string print = let open PrintMonad in function
  | U -> ret "Type"
  | Idx i -> idx i
  | Def name -> ret name
  | InS e -> atom e
  | OutS e -> atom e
  | Proj (field,e) ->
    let+ e = atom e in
    sprintf "%s.%s" e field
  | a -> 
    let+ a = term a in
    sprintf "(%s)" a

and record = let open PrintMonad in function
  | RNil -> ret ""
  | RCons (field,x,RNil) ->
    let+ x = term x in
    sprintf "%s => %s" field x
  | RCons (field,x,xs) ->
    let* x = term x in
    let+ xs = record xs in
    sprintf "%s => %s ; %s" field x xs
  | _ -> failwith "ill formed record"

and record_ty = let open PrintMonad in function
  | RTyNil -> ret ""
  | RTyCons (field,tp,RTyNil) ->
    let+ tp = term tp in
    sprintf "%s : %s" field tp
  | RTyCons (field,tp,rest) ->
    let* tp = term tp in
    let+ rest = abstract field @@ record_ty rest in
    sprintf "%s : %s ; %s" field tp rest
  | _ -> failwith "ill formed record"

let print = term