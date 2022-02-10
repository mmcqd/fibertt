open Core
open Readers
open Tactic
open ElabMonad

(* Kinda cannot believe how well this works, thanks cooltt devs!! *)
let rec intro_singletons (t : chk_tac) : chk_tac = fun goal -> run_chk ~goal @@
  match Eval.force goal with
    | Dom.Singleton _ -> Singleton.intro @@ intro_singletons t
    | _ -> t

let rec elim_singletons (t : syn_tac) : syn_tac =
  let* tp,e = run_syn t in
  match Eval.force tp with
    | Dom.Singleton _ -> elim_singletons @@ Singleton.elim (ret (tp,e))
    | _ -> ret (tp,e)

let mode_switch (t : syn_tac) : chk_tac = fun goal ->
  let* synthed,e = run_syn t in
  try 
  let+ () = lift_conv @@ Conv.conv goal synthed Dom.U in
  e
  with _ ->
    let* goal = lift_quote ~unfold:false @@ Quote.quote goal Dom.U in
    let* synthed = lift_quote ~unfold:false @@ Quote.quote synthed Dom.U in 
    let* goal = lift_print @@ Pretty.print goal in
    let* synthed = lift_print @@ Pretty.print synthed in
    failwith (sprintf "%s <> %s" synthed goal)

let rec check (tm : Raw.t) : chk_tac = intro_singletons @@
  match tm.con with
    | Raw.U -> U.formation
    | Raw.Pi ([],ran) -> check ran
    | Raw.Pi (([],_) :: doms,ran) -> check {tm with con = Raw.Pi (doms,ran)}
    | Raw.Pi ((x::xs,dom) :: doms,ran) -> Pi.formation x (check dom) (fun _ -> check {tm with con = Raw.Pi ((xs,dom) :: doms,ran)})
    | Raw.Lam ([],body) -> check body
    | Raw.Lam (x::xs , body) -> Pi.intro x (fun _ -> check {tm with con = Raw.Lam (xs,body)})
    | Raw.Singleton {tm ; tp} -> Singleton.formation (check tm) (check tp)
    | Raw.RecordTy [] -> Record.nil_formation
    | Raw.RecordTy ((field,tp) :: rest) -> Record.cons_formation field (check tp) (fun _ -> check {tm with con = Raw.RecordTy rest})
    | Raw.Record [] -> Record.nil_intro
    | Raw.Record ((field,x) :: xs) -> Record.cons_intro field (check x) (check {tm with con = Raw.Record xs})
    | _ -> mode_switch (synth tm)

and synth (tm : Raw.t) : syn_tac = elim_singletons @@
  match tm.con with
    | Var x -> Var.intro x
    | Raw.Ap (f,[]) -> synth f
    | Raw.Ap (f, x :: xs) -> Pi.elim (synth {tm with con = Raw.Ap (f,xs)}) (check x)
    | Raw.Proj (field,r) -> Record.elim field (synth r)
    | _ -> failwith "failed to synth"