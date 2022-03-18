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
    | Dom.U, Dom.Sig sign1, Dom.Sig sign2 -> conv_sig sign1 sign2
    | Dom.Sig fields, s1, s2 -> conv_struct fields s1 s2
    (* | _,Dom.Neu {tp = Dom.Singleton {tm ; _} ; _},_ -> conv tm tm2 tp
    | _,_,Dom.Neu {tp = Dom.Singleton {tm ; _} ; _} -> conv tm1 tm tp *)
    | _, Dom.Neu n1, Dom.Neu n2 -> 
      conv_spine n1.hd n2.hd n1.sp n2.sp
    | _ -> 
      fail @@ Error (sprintf "%s <> %s : %s" (Dom.show tm1) (Dom.show tm2) (Dom.show tp))

and conv_sig sign1 sign2 = let open ConvMonad in 
  match sign1,sign2 with
    | Dom.Nil, Dom.Nil -> ret ()
    | Dom.Cons (field1,tp1,sign1), Dom.Cons (field2,tp2,sign2) when String.equal field1 field2 ->
      let* () = conv tp1 tp2 Dom.U in
      let+ () = abstract ~name:field1 ~tp:tp1 @@ fun v ->
        let* sign1 = lift_comp @@ Eval.do_sig_clo sign1 v in
        let* sign2 = lift_comp @@ Eval.do_sig_clo sign2 v in
        conv_sig sign1 sign2
      in
      ()
    | _ -> fail @@ Error "mismatched signatures"

and conv_struct fields s1 s2 = let open ConvMonad in
  match fields with
    | Dom.Nil -> ret ()
    | Dom.Cons (field,tp,sign) ->
      let* proj1 = lift_comp @@ Eval.do_proj field s1 in
      let* proj2 = lift_comp @@ Eval.do_proj field s2 in
      let* () = conv proj1 proj2 tp in
      let* sign = lift_comp @@ Eval.do_sig_clo sign proj1 in
      conv_struct sign s1 s2

and conv_hd hd1 hd2 = let open ConvMonad in
  match hd1, hd2 with
    | Dom.Lvl l1, Dom.Lvl l2 when Int.equal l1 l2 -> ret ()
    | _ -> fail @@ Error (sprintf "%s <> %s" (Dom.show_head hd1) (Dom.show_head hd2))
  
and conv_spine hd1 hd2 sp1 sp2 = let open ConvMonad in 
  match sp1, sp2 with
    | [], [] -> conv_hd hd1 hd2
    | Dom.Ap ap1 :: sp1, Dom.Ap ap2 :: sp2 -> 
      let* () = conv ap1.tm ap2.tm ap1.tp in
      conv_spine hd1 hd2 sp1 sp2
    | Dom.Proj field1 :: sp1, Dom.Proj field2 :: sp2 when String.equal field1 field2 ->
      conv_spine hd1 hd2 sp1 sp2
    | _ -> fail @@ Error (sprintf "%s <> %s" (Dom.show_spine sp1) (Dom.show_spine sp2))

and conv_fam name base1 base2 fam1 fam2 = let open ConvMonad in
  let* () = conv base1 base2 Dom.U in
  abstract ~name ~tp:base1 @@ fun v -> 
  let* fam1 = lift_comp @@ Eval.do_clo fam1 v in
  let* fam2 = lift_comp @@ Eval.do_clo fam2 v in
  let+ () = conv fam1 fam2 Dom.U in
  ()


(* OutS (f x y) == a x y *)