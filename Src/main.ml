(* la boucle principale du programme *)

open Format
open Lambda
open Parser_tool
open Parsing
open Parser
open Lexer
open Sys
open Filename
open Typing
open Bindlib

let print_pos () =
          if not (test_console ()) then begin
            let l = !cur_line and c = !cur_col and n = !cur_name in
            pop_all ();
            print_string "*** File \"";
            print_string n;
            print_string "\", line ";
            print_int l;
            print_string "\", column ";
            print_int c;
            print_endline " :"
          end

let print_info ({lbg=l;cbg=c;lnd=l0;cnd=c0} as info) =
        let n = !cur_name and b = ref false in
        if not (test_console ()) then begin
          pop_all (); b := true
        end;
        if is_end_of_file () then begin
          print_string "*** Unexpected end of File \"";
          print_string n;
          print_endline "\"."
        end else begin
	  if info.lbg >= 0 then begin
            print_endline "*** Near:";
            print_input info;
            if !b then begin
              print_string "*** File \"";
              print_string n;
              print_string "\", lin ";
              print_int l;
              print_string ", col ";
              print_int c;
              if l <> l0 || c <> c0 then print_string " up to ";
              if l <> l0 then (print_string "lin "; print_int l0;
                               print_string ", ");
              if c <> c0 || l <> l0 then (print_string "col "; print_int c0);
              print_endline ":"
	    end
	  end else begin
	    print_endline "*** In a old term !"
	  end
        end

let print_pos () =
          print_info {lbg = !cur_line; cbg = !cur_col;
                      lnd = !cur_line; cnd = !cur_col}

let rcfile = ".lambdarc"

let _ =
  open_vbox 0;
  print_newline ();
  print_endline "---------------------------------";
  print_endline "|  The Normaliser, version 2.2  |";
  print_endline "| by C. Raffalli, November 1996 |";
  print_endline "---------------------------------";
  print_newline ();

  try read_file (concat (getenv "HOME") rcfile)
  with Sys_error _ | Not_found -> try read_file rcfile
  with Sys_error _ | Not_found ->
    init := false;
    print_string "Can't read startup file \"";
    print_string rcfile;
    print_endline "\" (ignored)."

let kwd_tbl = Hashtbl.create 83

let _ =
  Hashtbl.add kwd_tbl "let"      (fun i ->Let i);
  Hashtbl.add kwd_tbl "def"      (fun i ->Let i);
  Hashtbl.add kwd_tbl "in"       (fun i ->In i);
  Hashtbl.add kwd_tbl "and"      (fun i ->And i);
  Hashtbl.add kwd_tbl "fun"      (fun i ->Fun i);
  Hashtbl.add kwd_tbl "redef"    (fun i ->Redef i);
  Hashtbl.add kwd_tbl "rec"      (fun i ->Rec i);
  Hashtbl.add kwd_tbl "on"       (fun i ->On);
  Hashtbl.add kwd_tbl "off"      (fun i ->Off);
  Hashtbl.add kwd_tbl "type"     (fun i ->Type);
  Hashtbl.add kwd_tbl "untyped"  (fun i ->Untyped i);
  Hashtbl.add kwd_tbl "quit"     (fun i ->Doquit);
  Hashtbl.add kwd_tbl "include"  (fun i ->Include);
  Hashtbl.add kwd_tbl "path"     (fun i ->Path);
  Hashtbl.add kwd_tbl "print"    (fun i ->Print);
  Hashtbl.add kwd_tbl "prrec"    (fun i ->Prrec);
  Hashtbl.add kwd_tbl "trace"    (fun i ->Dotrace);
  Hashtbl.add kwd_tbl "mode"     (fun i ->Domode);
  Hashtbl.add kwd_tbl "lazy"     (fun i ->Mode Lazy);
  Hashtbl.add kwd_tbl "left"     (fun i ->Mode Left);
  Hashtbl.add kwd_tbl "recursive"(fun i ->Toggle recursive);
  Hashtbl.add kwd_tbl "typed"    (fun i ->Toggle typed);
  Hashtbl.add kwd_tbl "inductive"(fun i ->Toggle inductive);
  Hashtbl.add kwd_tbl "verbose"  (fun i ->Toggle verbose);
  Hashtbl.add kwd_tbl "tab"      (fun i ->Param "tab");
  Hashtbl.add kwd_tbl "max_depth"(fun i ->Param "max_depth");
  Hashtbl.add kwd_tbl "max_indent" (fun i ->Param "max_indent");
  Hashtbl.add kwd_tbl "margin"   (fun i ->Param "margin")

let lex lexbuf =
  match token lexbuf with
    Ident (i,s) as t -> (try Hashtbl.find kwd_tbl s i with Not_found -> t)
  | t -> t


let go() =
    catch_break true;
    let cont = ref true in
    let lexbuf = Lexing.from_function read_fun in
    while !cont do
	  open_vbox 0;(
      try
        flush stdout;
        Parser.cmd lex lexbuf
      with
         Syntax_error (i,s) ->
          print_info i;
          print_string "*** Syntax error, ";
          print_string s;
          resetlex lexbuf;
          print_newline()
       | Parse_error ->
          print_pos ();
          print_string "*** Syntax error.";
          resetlex lexbuf;
          print_newline()
       | Illegal_char s ->
          print_pos ();
          print_string "*** Illegal char: '";
          print_string (String.escaped s);
          print_string "'";
          resetlex lexbuf;
          print_newline()
       | Type_error (i,k,k0) ->
          print_info i;
          print_string "*** Type error: \n";
          print_string "Inferred type is ";
          print_ckind k;
          print_newline();
          print_string "Used type is ";
          print_ckind k0;
          print_newline()
       | Action.Wrong_untyped (i) ->
          print_info i;
          print_string "*** Wrong untyped.\n";
          print_newline();
      | Failure s ->
          print_newline();
          print_string "*** Failed: "; print_string s; print_newline()
      | Invalid_argument s ->
          print_newline();
          print_string "*** Invalid_argument: "; print_string s;
          print_newline()
      | Break ->
          print_newline();
          print_string "*** User interupt"; print_newline()
      | Out_of_memory ->
          print_newline();
          print_string "*** Out of memory"; print_newline()
      | Quit ->
          cont := false; ()
      | Bindlib_error ->
          print_newline();
          print_string "*** Bindlib_error"; print_newline()
      | _ ->
          print_newline();
          print_string "*** Unknow exception !"; print_newline()
    );
    close_box ()
  done;
  flush stdout

let _ =
  go();
  print_endline "Bye.";
  flush stdout
