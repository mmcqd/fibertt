open Core
open! Readers

exception ParseError of string

(* In order to handle parsing ambiguity between a term like (a b c) and (a b c : A) -> B
   we introduce a lexer hack where (a b c : A) is automatically converted to Tele (a b c : A)
   which eliminates the ambiguity in the parser
*)

module P = Parser
let rec only_vars_until_colon = function
  | [] -> false
  | (P.COLON,_,_) :: _ -> true
  | (P.IDENT _,_,_) :: ts -> only_vars_until_colon ts
  | _ -> false

let rec insert_tele = function
  | [] -> []
  | (P.LPAREN,s,e) as t :: ts -> if only_vars_until_colon ts then (P.TELE,s,e) :: t :: insert_tele ts else t :: insert_tele ts
  | t :: ts -> t :: insert_tele ts


let token = Lexer.initial

let tokenize style s =
  let lexbuf = match style with 
    | `String -> Lexing.from_string s 
    | `File -> let lexbuf = Lexing.from_channel (Stdlib.open_in s) in
               Lexing.set_filename lexbuf s;
               lexbuf
  in
  let rec go acc = 
    let tok = token lexbuf in
    let start_pos = lexbuf.lex_start_p in
    let end_pos = lexbuf.lex_curr_p in
    match tok with
      | EOF -> List.rev ((tok,start_pos,end_pos) :: acc)
      | tok -> go ((tok,start_pos,end_pos) :: acc)
  in insert_tele @@ go []

let parse style s =
  let toks = ref @@ tokenize style s in
  let prev_tok = ref None in
  let get_tok () = (match !toks with [] -> failwith "empty token list" | t::ts -> toks := ts; prev_tok := (Some t); t) in
  try MenhirLib.Convert.Simplified.traditional2revised Parser.init get_tok with
    | _ -> let (_,s,e) = match !prev_tok with None -> failwith "no prev tok" | Some x -> x in
    raise @@ ParseError (sprintf "%s:%s-%s" s.pos_fname (Raw.show_pos s) (Raw.show_pos e))

let rec show_module_deps = function
  | [] -> ""
  | [x] -> x
  | x::xs -> sprintf "%s <- %s" x (show_module_deps xs)

let rec run_cmd : Raw.cmd -> unit cmd = let open CmdMonad in function
  | Raw.Eval tm ->
    let* tp,tm = lift_elab tm.loc @@ Tactic.run_syn @@ Elab.synth tm in
    let* tm_d = lift_eval @@ Eval.eval tm in
    let* tm_s = lift_quote ~unfold:true @@ Quote.quote tm_d tp in
    let* tp = lift_quote ~unfold:false @@ Quote.quote tp Dom.U in
    let* pp_tp = lift_print @@ Pretty.print tp in 
    let+ pp_tm = lift_print @@ Pretty.print tm_s in
    printf "- : %s\n\n" pp_tp;
    printf "- = %s\n\n" pp_tm
  | Raw.Def {name ; tm} ->
    let* tp,tm = lift_elab tm.loc @@ Tactic.run_syn @@ Elab.synth tm in
    let* tm = lift_eval @@ Eval.eval tm in
    printf "def %s\n\n" name; 
    define ~name ~tm ~tp
  | Raw.DefChk {name ; tm ; tp} ->
    let* tp = lift_elab tp.loc @@ Tactic.run_chk ~goal:Dom.U (Elab.check tp) in
    let* tp_d = lift_eval @@ Eval.eval tp in 
    let* tm = lift_elab tm.loc @@ Tactic.run_chk ~goal:tp_d (Elab.check tm) in
    let* tm_d = lift_eval @@ Eval.eval tm in
    printf "def %s\n\n" name; 
    define ~name ~tm:tm_d ~tp:tp_d
  | Raw.DefFun {name ; doms ; ran ; body} ->
    let tp = Raw.{con = Raw.Pi (doms,ran) ; loc = ran.loc} in
    let tm = Raw.{con = Raw.Lam (List.concat_map ~f:fst doms,body) ; loc = body.loc} in
    run_cmd (Raw.DefChk {name ; tm ; tp})
  | Raw.Import modu ->
    let path = modu ^ ".ftt" in
    let* cmdLocal = read in
    if List.mem ~equal:String.equal cmdLocal.importing path then failwith (sprintf "Cylcic module dependency: %s" (show_module_deps (path :: cmdLocal.importing)));
    printf "import %s\n\n" modu;
    let* () = run_cmd_list @@ parse `File path in
    import path


and run_cmd_list : Raw.cmd list -> unit cmd = fun xs -> let open CmdMonad in 
  let+ _ = sequence @@ List.map ~f:run_cmd xs in
  ()

let rec repl : unit -> unit cmd = let open CmdMonad in fun () ->
  print_string "⊢ ";
  let txt = Stdlib.read_line () in
  if String.equal txt "" then ignore @@ repl ();
  let* () = run_cmd_list @@ parse `String txt in
  repl ()

let _ : unit = let open CmdMonad in
  let args = Sys.get_argv () in
  try
  if Array.length args = 1 then CmdMonad.run_exn {global = Global_ctx.empty ; imported = []} {importing = []} (repl ());
  let cmds = parse `File args.(1) in
  let go = let* () = run_cmd_list cmds in repl () in
  CmdMonad.run_exn {global = Global_ctx.empty ; imported = []} {importing = []} go
  with
    | ElabMonad.Hole h -> print_endline h
    | ElabMonad.Error e -> printf "Elaboration Error:\n%s" e
