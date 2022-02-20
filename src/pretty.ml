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
  | Struct xs -> 
    let+ xs = record xs in
    sprintf "struct {%s}" xs
  | Sig fields -> 
    let+ fields = record_ty fields in
    sprintf "sig {%s}" fields
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
  | [] -> ret ""
  | [(field,x)] ->
    let+ x = term x in
    sprintf "%s => %s" field x
  | (field,x) :: xs ->
    let* x = term x in
    let+ xs = record xs in
    sprintf "%s => %s ; %s" field x xs

and record_ty = let open PrintMonad in function
  | Syn.Nil -> ret ""
  | Syn.Cons (field,tp,Nil) ->
    let+ tp = term tp in
    sprintf "%s : %s" field tp
  | Syn.Cons (field,tp,rest) ->
    let* tp = term tp in
    let+ rest = abstract field @@ record_ty rest in
    sprintf "%s : %s ; %s" field tp rest

let print = term