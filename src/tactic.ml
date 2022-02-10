open Core
open Readers


type syn_tac = (Dom.tp * Syn.t) elab
type chk_tac = Dom.tp -> Syn.t elab

let run_syn (t : syn_tac) : (Dom.tp * Syn.t) elab = t
let run_chk (t : chk_tac) : goal:Dom.tp -> Syn.t elab = fun ~goal -> t goal


module U = 
struct
  open ElabMonad
  
  let formation : chk_tac = fun goal ->
    match Eval.force goal with
      | Dom.U -> ret Syn.U
      | _ -> failwith "U.formation"

end

module Pi =
struct
  open ElabMonad
  let formation (x : string) (dom : chk_tac) (ran : Dom.t -> chk_tac) : chk_tac = fun goal ->
    match Eval.force goal with
      | Dom.U -> 
        let* dom_s = run_chk ~goal:Dom.U dom in
        let* dom_d = lift_eval @@ Eval.eval dom_s in
        let+ ran_s = abstract ~name:x ~tp:dom_d @@ fun v -> run_chk ~goal:Dom.U (ran v) in
        Syn.Pi (x,dom_s,ran_s)
      | _ -> failwith "Pi.formation"

  let intro (x : string) (body : Dom.t -> chk_tac) : chk_tac = fun goal ->
    match Eval.force goal with
      | Dom.Pi (_,dom,ran) -> 
        let+ body = abstract ~name:x ~tp:dom @@ fun v -> 
          let* body_tp = lift_comp @@ Eval.do_clo ran v in 
          run_chk ~goal:body_tp (body v)
        in
        Syn.Lam (x,body)
      | _ -> failwith "Pi.intro"

  let elim (f : syn_tac) (e : chk_tac) : syn_tac =
    let* tp,f = run_syn f in
    match Eval.force tp with
      | Dom.Pi (_,dom,ran) -> 
        let* e = run_chk ~goal:dom e in
        let* e_dom = lift_eval @@ Eval.eval e in
        let+ tp = lift_comp @@ Eval.do_clo ran e_dom in
        tp,Syn.Ap (f,e)
      | _ -> failwith "Pi.elim"
end

module Singleton =
struct
  open ElabMonad
  let formation (tm : chk_tac) (tp : chk_tac) : chk_tac = fun goal ->
    match Eval.force goal with
      | Dom.U ->
        let* tp = run_chk ~goal:Dom.U tp in
        let* tp_d = lift_eval @@ Eval.eval tp in
        let+ tm = run_chk ~goal:tp_d tm in
        Syn.Singleton {tm ; tp}
      | _ -> failwith "Singleton.formation"
  
  let intro (e : chk_tac) : chk_tac = fun goal ->
    match Eval.force goal with
      | Dom.Singleton {tm ; tp} -> 
        let* e = run_chk ~goal:tp e in
        let* e_d = lift_eval @@ Eval.eval e in
        let+ () = lift_conv @@ Conv.conv e_d tm tp 
          (* let* tm = lift_quote ~unfold:false @@ Quote.quote tm tp in
          let* tm = lift_print @@ Pretty.print tm in
          let* e = lift_print @@ Pretty.print e in
          failwith (sprintf "%s <> %s" e tm)  *)
        in
        Syn.InS e
      | _ -> failwith "Singleton.intro"
  
  let elim (e : syn_tac) : syn_tac =
    let+ tp,e = run_syn e in
    match Eval.force tp with
      | Dom.Singleton {tp ; _} -> tp, Syn.OutS e
      | _ -> failwith "Sineleton.elim"

end

module Var =
struct
  open ElabMonad
  let intro (x : string) : syn_tac =
    let* ctx = read_local in
    let+ global = read_global in
    match Local_ctx.find_tp_and_idx x ctx with
      | Some (i,tp) -> tp, Syn.Idx i
      | None -> 
        match Global_ctx.find_name ~name:x ~ctx:global with
          | Some (tp,_) -> tp, Syn.Def x
          | None -> failwith ("unbound variable: "^x)
end