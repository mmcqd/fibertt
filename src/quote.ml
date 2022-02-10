open Core
open Readers


let lvl_to_idx (l : int) : int quote = let open QuoteMonad in
  let+ lvl = read_lvl in 
  Local_ctx.lvl_to_idx lvl l

let rec quote (tm : Dom.t) (tp : Dom.tp) : Syn.t quote = let open QuoteMonad in
  match Eval.force tp,tm with
    | Dom.U, Dom.U -> ret Syn.U
    | Dom.U, Dom.Pi (x,dom,ran) ->
      let+ (dom_s,ran_s) = quote_fam dom ran in
      Syn.Pi (x,dom_s,ran_s)
    | Dom.Pi (_,dom,ran), Dom.Lam (y,body) ->
      let+ body = abstract ~tp:dom @@ fun x -> 
        let* body_tp = lift_comp @@ Eval.do_clo ran x in 
        let* body = lift_comp @@ Eval.do_clo body x in 
        quote body body_tp
      in
      Syn.Lam (y,body) 
    | Dom.U, Dom.Singleton {tm ; tp} ->
      let* tm = quote tm tp in
      let+ tp = quote tp Dom.U in
      Syn.Singleton {tm ; tp}
    | Dom.Singleton {tp ; _}, Dom.InS e ->
      let+ e = quote e tp in
      Syn.InS e
    |_ ,Dom.Neu {hd = Def {name ; value} ; sp ; _} ->
      let* unfold = read_unfold in
      if unfold then quote (Lazy.force value) tp else quote_spine (Syn.Def name) sp
    | _,Dom.Neu {hd = Lvl l ; sp ; _} -> 
      let* i = lvl_to_idx l in 
      quote_spine (Syn.Idx i) sp
    | _ -> failwith (sprintf "quote - %s AT %s" (Dom.show tm) (Dom.show tp))

and quote_spine (hd : Syn.t) : Dom.elim list -> Syn.t quote = let open QuoteMonad in function
  | [] -> ret hd
  | Dom.Ap {tm ; tp} :: sp -> 
    let* f = quote_spine hd sp in 
    let+ e = quote tm tp in
    Syn.Ap (f,e)
  | Dom.OutS _ :: sp ->
    let+ e = quote_spine hd sp in
    Syn.OutS e
  
and quote_fam base fam = let open QuoteMonad in
  let* base_s = quote base Dom.U in
  let+ fam_s = abstract ~tp:base @@ fun x -> let* fam = lift_comp @@ Eval.do_clo fam x in quote fam Dom.U in
  (base_s,fam_s)