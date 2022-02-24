open Core
open Tactic


let rec check (tm : Raw.t) : chk_tac = chk_tac @@ fun goal -> 
  (* printf "CHECK %s AT %s\n\n" (Raw.show tm) (Dom.show goal); *)
  Readers.ElabMonad.scope (fun ctx -> {ctx with loc = tm.loc}) @@
  run_chk ~goal @@
  match tm.con with
    | Raw.InferSingleton -> Singleton.infer
    | _ ->
  Implicit.intro_singletons @@
  match tm.con with
    | Raw.Hole -> Hole.intro
    | Raw.U -> U.formation
    | Raw.Pi ([],ran) -> check ran
    | Raw.Pi (([],_) :: doms,ran) -> check {tm with con = Raw.Pi (doms,ran)}
    | Raw.Pi ((x::xs,dom) :: doms,ran) -> Pi.formation x (check dom) (check {tm with con = Raw.Pi ((xs,dom) :: doms,ran)})
    | Raw.Lam ([],body) -> check body
    | Raw.Lam (x::xs , body) -> Pi.intro x (check {tm with con = Raw.Lam (xs,body)})
    | Raw.Singleton {tm ; tp} -> Singleton.formation (check tm) (check tp)
    | Raw.Sig fields -> Signature.formation (List.map ~f:(fun (field,tp) -> (field,check tp)) fields)
    | Raw.Struct xs -> Signature.intro (List.map ~f:(fun (field,tp) -> (field,check tp)) xs)
    | Raw.Patch (e,patches) -> Signature.patch (List.map patches ~f:(function `Patch (f,tm) -> `Patch (f,check tm) | `Field x -> `Field x)) (check e) 
    | Raw.Total fam -> Signature.total (synth fam)
    | _ -> 
      (* Needed so that we can retype synthable terms with more specific Singleton types *)
      match goal with
        | Dom.Pi (x,_,_) -> 
          let x = if String.equal x "_" then Fresh.fresh_var () else x in
          Pi.intro x (check {tm with con = Raw.Ap (tm,[{con = Var x ; loc = tm.loc}])})
        | Dom.Sig sign -> Signature.intro (List.map (Signature.extract_fields sign) ~f:(fun field -> (field,check @@ Raw.{con = Proj (field,tm) ; loc = tm.loc})))
        | _ -> Implicit.intro_conversions (synth tm)

and synth (tm : Raw.t) : syn_tac = 
  (* printf "SYNTH %s\n\n" (Raw.show tm); *)
  Readers.ElabMonad.scope (fun ctx -> {ctx with loc = tm.loc}) @@
  Implicit.elim_singletons @@
  match tm.con with
    | Var x -> Var.intro x
    | Raw.Ap (f,[]) -> synth f
    | Raw.Ap (f, x :: xs) -> Pi.elim (synth {tm with con = Raw.Ap (f,xs)}) (check x)
    | Raw.Proj (field,r) -> Signature.elim field (synth r)
    | Raw.Point e -> Point.intro (synth e)
    | _ -> failwith "failed to synth"