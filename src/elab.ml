open Core
open Readers
open Tactic
open ElabMonad


let mode_switch (t : syn_tac) : chk_tac = fun goal ->
  let* synthed,e = run_syn t in
  (* printf "%s\n=======\n%s\n=======\n%s\n\n" (Dom.show synthed) (Syn.show e) (Dom.show goal); *)
  let+ () = lift_conv @@ Conv.conv goal synthed Dom.U in
  e


let rec check (tm : Raw.t) : chk_tac = chk_tac @@ fun goal -> 
  (* printf "CHECK %s AT %s\n\n" (Raw.show tm) (Dom.show goal); *)
  run_chk ~goal @@
  Implicit.intro_singletons @@
  match tm.con with
    | Raw.U -> U.formation
    | Raw.Pi ([],ran) -> check ran
    | Raw.Pi (([],_) :: doms,ran) -> check {tm with con = Raw.Pi (doms,ran)}
    | Raw.Pi ((x::xs,dom) :: doms,ran) -> Pi.formation x (check dom) (check {tm with con = Raw.Pi ((xs,dom) :: doms,ran)})
    | Raw.Lam ([],body) -> check body
    | Raw.Lam (x::xs , body) -> Pi.intro x (check {tm with con = Raw.Lam (xs,body)})
    | Raw.Singleton {tm ; tp} -> Singleton.formation (check tm) (check tp)
    | Raw.Sig fields -> Signature.formation (List.map ~f:(fun (field,tp) -> (field,check tp)) fields)
    | Raw.Struct xs -> Signature.intro (List.map ~f:(fun (field,tp) -> (field,check tp)) xs)
    | Raw.Patch (e,patches) -> Signature.patch (List.map patches ~f:(function `Patch (f,tm) -> `Patch (f,check tm) | `Var x -> `Var x)) (check e) 
    | Raw.Point e -> Point.intro (synth e)
    | _ -> 
      (* Needed so that we can retype synthable terms with more specific Singleton types *)
      match goal with
        | Dom.Pi (x,_,_) -> 
          let x = if String.equal x "_" then Fresh.fresh_var () else x in
          Pi.intro x (check {tm with con = Raw.Ap (tm,[{con = Var x ; loc = tm.loc}])})
        | Dom.Sig sign -> Signature.intro (List.map (Signature.extract_fields sign) ~f:(fun field -> (field,check @@ Raw.{con = Proj (field,tm) ; loc = tm.loc})))
        | _ -> mode_switch (synth tm)

and synth (tm : Raw.t) : syn_tac = 
  (* printf "SYNTH %s\n\n" (Raw.show tm); *)
  Implicit.elim_singletons @@
  match tm.con with
    | Var x -> Var.intro x
    | Raw.Ap (f,[]) -> synth f
    | Raw.Ap (f, x :: xs) -> Pi.elim (synth {tm with con = Raw.Ap (f,xs)}) (check x)
    | Raw.Proj (field,r) -> Signature.elim field (synth r)
    | _ -> failwith "failed to synth"