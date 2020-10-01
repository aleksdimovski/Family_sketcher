(***************************************************)
(*                                                 *)
(*                        Main                     *)
(*                                                 *)
(*             Aleksandar Dimovski                 *)
(*          Mother Teresa Uni, Skopje              *)
(*                   2018 - 2019                   *)
(*                                                 *)
(***************************************************)

(* parsing *)
open AbstractSyntax
open ItoA

let analysis = ref "single"
let domain = ref "boxes"
let filename = ref ""
let fmt = ref Format.std_formatter
let main = ref "main"
let minimal = ref false
let precondition = ref "true"
let time = ref true
let noinline = ref false


let parseFile filename =
  let f = open_in filename in
  let lex = Lexing.from_channel f in
  try
    lex.Lexing.lex_curr_p <- { lex.Lexing.lex_curr_p
                               with Lexing.pos_fname = filename; };
    let r = Parser.file Lexer.start lex in
    close_in f; r
  with
  | Parser.Error ->
    Printf.eprintf "Parse Error (Invalid Syntax) near %s\n"
      (IntermediateSyntax.position_tostring lex.Lexing.lex_start_p);
    failwith "Parse Error"
  | Failure e ->
    if e == "lexing: empty token" then 
      begin
        Printf.eprintf "Parse Error (Invalid Token) near %s\n" (IntermediateSyntax.position_tostring lex.Lexing.lex_start_p);
        failwith "Parse Error"
      end 
    else
      failwith e

let parse_args () =
  let rec doit args =
    match args with
    (* General arguments -------------------------------------------*)
    | "-domain"::x::r -> (* abstract domain: boxes|octagons|polyhedra *)
      domain := x; doit r
    | "-timeout"::x::r -> (* analysis timeout *)
      Iterator.timeout := float_of_string x; doit r
    | "-joinfwd"::x::r -> (* widening delay in forward analysis *)
      Iterator.joinfwd := int_of_string x; doit r
    | "-joinbwd"::x::r -> (* widening delay in backward analysis *)
      Iterator.joinbwd := int_of_string x; doit r
    | "-main"::x::r -> (* analyzer entry point *) main := x; doit r
    | "-meetbwd"::x::r -> (* dual widening delay in backward analysis *)
      Iterator.meetbwd := int_of_string x; doit r
    | "-minimal"::r -> (* analysis result only *)
      minimal := true; Iterator.minimal := true; doit r
    | "-refine"::r -> (* refine in backward analysis *)
      Iterator.refine := true; doit r
    | "-retrybwd"::x::r ->
      Iterator.retrybwd := int_of_string x;
      (*DecisionTree.retrybwd := int_of_string x;*)
      doit r
    | "-tracefwd"::r -> (* forward analysis trace *)
      Iterator.tracefwd := true; doit r
    (* Single analysis -------------------------------*)
    | "-single"::r -> (* single analysis *)
      analysis := "single"; doit r
    (* Tuple analysis -------------------------------*)
    | "-tuple"::r -> (* tuple analysis *)
      analysis := "tuple"; doit r
    | "-tree"::r -> (* dection tree analysis *)
      analysis := "tree"; doit r
    | "-time"::r -> (* track analysis time *)
      time := true; doit r
    | "-timebwd"::r -> (* track backward analysis time *)
      Iterator.timebwd := true; doit r
    | "-timefwd"::r -> (* track forward analysis time *)
      Iterator.timefwd := true; doit r
    | "-precondition"::c::r -> (* optional precondition that holds 
                                  at the start of the program, default = true *)
      precondition := c; doit r 
    | "-noinline"::r -> (* don't inline function calls, only for CFG based analysis *)
      noinline := true; doit r
    | x::r -> filename := x; doit r
    | [] -> ()
  in
  doit (List.tl (Array.to_list Sys.argv))

(* do all *)

module SingleBoxes =
  SingleAnalysisIterator.SingleAnalysisIterator(Numerical.B)
module SingleOctagons =
  SingleAnalysisIterator.SingleAnalysisIterator(Numerical.O)
module SinglePolyhedra =
  SingleAnalysisIterator.SingleAnalysisIterator(Numerical.P)  

module TupleBoxes =
  TupleAnalysisIterator.TupleAnalysisIterator(Maketuple.TB)
module TupleOctagons =
  TupleAnalysisIterator.TupleAnalysisIterator(Maketuple.TO)
module TuplePolyhedra =
  TupleAnalysisIterator.TupleAnalysisIterator(Maketuple.TP)  

module DTBoxes =
  DTAnalysisIterator.DTAnalysisIterator(MakeDTDomain.DTB)
module DTOctagons =
  DTAnalysisIterator.DTAnalysisIterator(MakeDTDomain.DTO)
module DTPolyhedra =
  DTAnalysisIterator.DTAnalysisIterator(MakeDTDomain.DTP) 


let result = ref false

let run_analysis analysis_function program () =
  try 
    let start = Sys.time () in
    let terminating = analysis_function program !main in
    let stop = Sys.time () in
    Format.fprintf !fmt "Analysis Result: ";
    let result = if terminating then "TRUE" else "UNKNOWN" in
    Format.fprintf !fmt "%s\n" result;
    if !time then
      Format.fprintf !fmt "Time: %f s\n" (stop-.start);
    Format.fprintf !fmt "\nDone.\n"
  with
  | Iterator.Timeout ->
    Format.fprintf !fmt "\nThe Analysis Timed Out!\n";
    Format.fprintf !fmt "\nDone.\n"


(* this function generates all configurations *)
let rec process list = 
	if List.length list = 0 then [[]]
	else match list with
		| [] -> []
		| hd :: tl -> 
			let tmp = ref [] in
			let dom = hd.featDom in
			for i = 0 to (List.length dom)-1 do
				let tmp1 = List.map (fun l -> (hd.featName,List.nth dom i) :: l) (process tl) in 
				tmp := !tmp @ tmp1
			done;
			!tmp;;

let print_configs l =
  print_endline ""; Format.fprintf !fmt "Variants: ";
  if (List.length l == 0) then Format.fprintf !fmt "None " else List.iter (fun el -> print_endline ""; List.iter (fun (key,v) -> Format.fprintf !fmt "% s{%d}, " key v) el) l;;	

let single () =
  if !filename = "" then raise (Invalid_argument "No Source File Specified");
  let sources = parseFile !filename in   
  let (program,_) = ItoA.prog_itoa sources in 
  	let feats_feat = ref [] in 
  StringMap.iter (fun key value -> feats_feat := value :: !feats_feat; Format.fprintf !fmt "Feature: %s - %n \n" key (List.length value.featDom)) !ItoA.features;   
  let configs = process !feats_feat in (*print_configs configs;*)
  if not !minimal then
    begin
      Format.fprintf !fmt "\nAbstract Syntax:\n";
      AbstractSyntax.prog_print !fmt program;
    end;
  let analysis_function =
    match !domain with
    | "boxes" -> SingleBoxes.analyze
    | "octagons" -> SingleOctagons.analyze 
    | "polyhedra" -> SinglePolyhedra.analyze
    | _ -> raise (Invalid_argument "Unknown Abstract Domain")
  in Format.fprintf !fmt "%s\n" !domain; (*run_analysis analysis_function program () *)
  let total_start = Sys.time () in 
  let configs_correct = ref [] in 
  List.iter (fun el -> 
    Format.fprintf !fmt "\n Variant: "; List.iter (fun (key,v) -> Format.fprintf !fmt "% s{%d}, " key v) el; Format.fprintf !fmt " \n"; 
    try 
    let start = Sys.time () in
    let result = analysis_function program !main el in
    let stop = Sys.time () in
    Format.fprintf !fmt "Analysis Result: ";
    Format.fprintf !fmt "%s\n" result;
	if (String.equal result "assert CORRECT") then configs_correct:=el::!configs_correct;
    if !time then
      Format.fprintf !fmt "Time: %f s\n" (stop-.start);
    Format.fprintf !fmt "\nDone.\n"
  with
  | Iterator.Timeout ->
    Format.fprintf !fmt "\nThe Analysis Timed Out!\n";
    Format.fprintf !fmt "\nDone.\n" 
	) configs; 
  let total_stop = Sys.time () in 
  Format.fprintf !fmt "\n SUMMARY RESULTS ... \n";
  Format.fprintf !fmt "CORRECT are ... "; print_configs !configs_correct; 
  Format.fprintf !fmt "\n TOTAL Time: %f s\n" (total_stop-.total_start)
  (* Format.fprintf !fmt "End ... \n"; AbstractSyntax.StringMap.iter (fun key value -> Format.fprintf !fmt "%s " key ) !ItoA.features; Format.fprintf !fmt "%s\n" !domain CONTINUE FROM HERE ...  *)


let liftedtuple () =
  if !filename = "" then raise (Invalid_argument "No Source File Specified");
  let sources = parseFile !filename in
  let (program,_) = ItoA.prog_itoa sources in
  if not !minimal then
    begin
      Format.fprintf !fmt "\nAbstract Syntax:\n";
      AbstractSyntax.prog_print !fmt program;
    end;
  let analysis_function =
    match !domain with
    | "boxes" -> TupleBoxes.analyze 
    | "octagons" -> TupleOctagons.analyze 
    | "polyhedra" -> TuplePolyhedra.analyze
    | _ -> raise (Invalid_argument "Unknown Abstract Domain")
  in Format.fprintf !fmt "%s\n" !domain; 
  Format.fprintf !fmt "End ... \n"; AbstractSyntax.StringMap.iter (fun key v -> Format.fprintf !fmt "%s{%s}" key (typ_tostring(v.featTyp)); List.iter print_int v.featDom) !ItoA.features;
  run_analysis analysis_function program ()
  (* Format.fprintf !fmt "End ... \n"; AbstractSyntax.StringMap.iter (fun key value -> Format.fprintf !fmt "%s " key ) !ItoA.features; Format.fprintf !fmt "%s\n" !domain CONTINUE FROM HERE ...  *)


let lifteddt () =
  if !filename = "" then raise (Invalid_argument "No Source File Specified");
  let sources = parseFile !filename in
  let (program,_) = ItoA.prog_itoa sources in
  if not !minimal then
    begin
      Format.fprintf !fmt "\nAbstract Syntax:\n";
      AbstractSyntax.prog_print !fmt program;
    end;
  let analysis_function =
    match !domain with
    | "boxes" -> DTBoxes.analyze 
    | "octagons" -> DTOctagons.analyze 
    | "polyhedra" -> DTPolyhedra.analyze
    | _ -> raise (Invalid_argument "Unknown Abstract Domain")
  in Format.fprintf !fmt "%s\n" !domain; (*run_analysis analysis_function program () *)
  (* Format.fprintf !fmt "End ... \n"; AbstractSyntax.StringMap.iter (fun key value -> Format.fprintf !fmt "%s " key ) !ItoA.features; Format.fprintf !fmt "%s\n" !domain CONTINUE FROM HERE ...  *)
  try 
    let start = Sys.time () in
    let terminating = analysis_function program !main in
    let stop = Sys.time () in
    (*Format.fprintf !fmt "Analysis Result: ";
    let result = if terminating then "TRUE" else "UNKNOWN" in
    Format.fprintf !fmt "%s\n" result; *)
    if !time then
      Format.fprintf !fmt "\nTime: %f s\n" (stop-.start);
    Format.fprintf !fmt "\nDone.\n"
  with
  | Iterator.Timeout ->
    Format.fprintf !fmt "\nThe Analysis Timed Out!\n";
    Format.fprintf !fmt "\nDone.\n"




(*Main entry point for application*)
let doit () =
  parse_args ();
  match !analysis with
  | "single" -> single ()
  | "tuple" -> liftedtuple ()
  | "tree" -> lifteddt ()
  | _ -> raise (Invalid_argument "Unknown Analysis")

let _ = doit () 
