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
  | Sig fields -> 
    let+ fields = signature fields in
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
  | Struct xs -> 
    let+ xs = structure xs in
    sprintf "{%s}" xs
  | a -> 
    let+ a = term a in
    sprintf "(%s)" a

and structure = let open PrintMonad in function
  | [] -> ret ""
  | [(field,x)] ->
    let+ x = term x in
    sprintf "%s => %s" field x
  | (field,x) :: xs ->
    let* x = term x in
    let+ xs = structure xs in
    sprintf "%s => %s ; %s" field x xs

and signature = let open PrintMonad in function
  | Syn.Nil -> ret ""
  (* | Syn.Cons (_,Syn.Singleton _,Nil) -> ret "" *)
  | Syn.Cons (field,tp,Nil) ->
    let+ tp = term tp in
    sprintf "%s : %s" field tp
  (* | Syn.Cons (field,Syn.Singleton _,rest) ->
    abstract field @@ signature rest *)
  | Syn.Cons (field,tp,rest) ->
    let* tp = term tp in
    let+ rest = abstract field @@ signature rest in
    sprintf "%s : %s ; %s" field tp rest

let print = term

let rec print_local_ctx_ (tps : (string * Syn.t) list) : string print = let open PrintMonad in
  match tps with
    | [] -> ret ""
    | (v,tp) :: tps -> 
      let* tp = print tp in
      abstract v @@
      let+ tps = print_local_ctx_ tps in
      sprintf "%s : %s\n%s" v tp tps

let print_local_ctx tps : string = 
  match print_local_ctx_ tps [] with
    | Ok s -> s
    | Error e -> raise e