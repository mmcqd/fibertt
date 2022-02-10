open Core
open Readers


let quote tm tp : string conv = let open ConvMonad in
  let* tm = lift_quote ~unfold:false @@ Quote.quote tm tp in
  lift_print @@ Pretty.print tm

let rec conv (tm1 : Dom.t) (tm2 : Dom.t) (tp : Dom.tp) : unit conv = let open ConvMonad in
  (* printf "CONV\n\n%s\n-------------\n%s\n\n\n" (Dom.show tm1) (Dom.show tm2); *)
  match Eval.force tp, Eval.force tm1, Eval.force tm2 with
    | Dom.U, Dom.U, Dom.U -> ret ()
    | Dom.U, Dom.Pi (x,dom1,ran1), Dom.Pi (_,dom2,ran2) -> conv_fam x dom1 dom2 ran1 ran2
    | Dom.Pi (x,dom,ran), f1, f2 -> 
      abstract ~name:x ~tp:dom @@ fun v ->
      let* ran = lift_comp @@ Eval.do_clo ran v in
      let* f1 = lift_comp @@ Eval.do_ap f1 v in
      let* f2 = lift_comp @@ Eval.do_ap f2 v in
      conv f1 f2 ran
    | Dom.U, Dom.Singleton s1, Dom.Singleton s2 -> 
      let* () = conv s1.tp s2.tp Dom.U in
      conv s1.tm s2.tm s1.tp
    | Dom.Singleton {tp ; _}, _, _ ->
      let* e1 = lift_comp @@ Eval.do_outS tm1 in
      let* e2 = lift_comp @@ Eval.do_outS tm2 in
      conv e1 e2 tp
    | _, Dom.Neu n1, Dom.Neu n2 -> 
      conv_spine n1.hd n2.hd n1.sp n2.sp
    | _ -> 
      let* tm1 = quote tm1 tp in
      let* tm2 = quote tm2 tp in
      let* tp = quote tp Dom.U in
      failwith (sprintf "%s <> %s : %s" tm1 tm2 tp)

and conv_hd hd1 hd2 = let open ConvMonad in
  match hd1, hd2 with
    | Dom.Lvl l1, Dom.Lvl l2 when Int.equal l1 l2 -> ret ()
    | _ -> failwith (sprintf "%s <> %s" (Dom.show_head hd1) (Dom.show_head hd2))
  
and conv_spine hd1 hd2 sp1 sp2 = let open ConvMonad in 
  match sp1, sp2 with
    | [], [] -> conv_hd hd1 hd2
    | Dom.Ap ap1 :: sp1, Dom.Ap ap2 :: sp2 -> 
      let* () = conv ap1.tm ap2.tm ap1.tp in
      conv_spine hd1 hd2 sp1 sp2

    (* We want (p : Sub A x |- OutS p = x : A), so when converting spines, if we hit and OutS {tm ; tp}, we know the rest of the term is
      definitionally equal to tm 
    *)
    | Dom.OutS o1 :: _, Dom.OutS o2 :: _ ->
      conv o1.tm o2.tm o1.tp
    | Dom.OutS {tm ; tp} :: _, sp2 -> 
      conv tm (Dom.Neu {hd = hd2 ; sp = sp2 ; tp}) tp
    | sp1 , Dom.OutS {tm ; tp} :: _ -> 
      conv (Dom.Neu {hd = hd1 ; sp = sp1 ; tp}) tm tp
    | _ -> failwith (sprintf "%s <> %s" (Dom.show_spine sp1) (Dom.show_spine sp2))

and conv_fam name base1 base2 fam1 fam2 = let open ConvMonad in
  let* () = conv base1 base2 Dom.U in
  abstract ~name ~tp:base1 @@ fun v -> 
  let* fam1 = lift_comp @@ Eval.do_clo fam1 v in
  let* fam2 = lift_comp @@ Eval.do_clo fam2 v in
  let+ () = conv fam1 fam2 Dom.U in
  ()