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
    let* f = match f with Lam _ | OutS _ | InS _ -> atom f | _ -> term f in
    let+ e = match e with Ap _ | Singleton _ | InS _ | OutS _ -> atom e | _ -> term e in
    sprintf "%s %s" f e
  | InS e -> term e
  | OutS e -> term e
  | Singleton {tm ; tp} ->
    let* tm = atom tm in
    let+ tp = atom tp in
    sprintf "Sub %s %s" tp tm
  | t -> atom t

and atom : Syn.t -> string print = let open PrintMonad in function
  | U -> ret "Type"
  | Idx i -> idx i
  | Def name -> ret name
  | InS e -> atom e
  | OutS e -> atom e
  | a -> 
    let+ a = term a in
    sprintf "(%s)" a

let print = term