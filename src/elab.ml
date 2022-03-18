open Core
open Tactic
open Readers.ElabMonad


let rec check (tm : Raw.t) : chk_tac = fun goal -> 
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
    | Raw.Patch (e,patches) -> fun goal ->
      let rec elab_patches ps = List.map ps ~f:(function
        | `Patch (f,tm) -> `Patch (f,check tm)
        | `RecPatch (f,ps) -> `RecPatch (f,elab_patches ps)
        | `Field f -> `Field f
      ) 
      in
      let* patched = run_chk ~goal @@ Signature.patch (elab_patches patches) (check e) in
      ret patched
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
    | Raw.Point e -> Point.syn (synth e)
    | _ -> fail @@ Error (sprintf "failed to synth %s" (Raw.show tm))


(* Idea I had to handle subtyping coercion obligations introduced by macro-like operations like Patcg *)
and re_check (tm : Syn.t) : chk_tac = fun goal -> 
  printf "REHECK %s AT %s\n\n" (Syn.show tm) (Dom.show goal);
  run_chk ~goal @@
  Implicit.intro_singletons @@
  match tm with
    | Syn.U -> U.formation
    | Syn.Pi (x,dom,ran) -> Pi.formation x (re_check dom) (re_check ran)
    | Syn.Lam (x,body) -> Pi.intro x (re_check body)
    | Syn.Singleton {tm ; tp} -> Singleton.formation (re_check tm) (re_check tp)
    | Syn.Sig sign -> Signature.formation (List.map ~f:(fun (field,tp) -> (field,re_check tp)) (Syn.signature_to_list sign))
    | Syn.Struct xs -> Signature.intro (List.map ~f:(fun (field,tp) -> (field,re_check tp)) xs)
    | Syn.InS e -> fun goal ->
      let* e = run_chk ~goal @@ re_check e in
      ret @@ Syn.InS e 
    | _ -> 
      (* Needed so that we can retype synthable terms with more specific Singleton types *)
      match goal with
        | Dom.Pi (x,_,_) -> 
          fun goal ->
          let x = if String.equal x "_" then Fresh.fresh_var () else x in
          let* _,v = Var.intro x in
          run_chk ~goal @@ Pi.intro x (re_check (Syn.Ap (tm,v)))
        | Dom.Sig sign -> Signature.intro (List.map (Signature.extract_fields sign) ~f:(fun field -> (field,re_check @@ Syn.Proj (field,tm))))
        | _ -> Implicit.intro_conversions (re_synth tm)

and re_synth (tm : Syn.t) : syn_tac =  
  printf "RESYNTH %s\n\n" (Syn.show tm);
  Implicit.elim_singletons @@
  match tm with
    | Syn.Idx i -> Var.idx i
    | Syn.Def x -> Var.def x
    | Syn.Ap (f, x) -> Pi.elim (re_synth f) (re_check x)
    | Syn.Proj (field,r) -> Signature.elim field (re_synth r)
    | Syn.OutS s -> Singleton.outS (re_synth s) 
    | _ -> fail @@ Error (sprintf "failed to synth %s" (Syn.show tm))