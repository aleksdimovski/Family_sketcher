(*       ********* OCamllex Lexer ************     *)
(*                                                 *)
(*             Aleksandar Dimovski                 *)
(*          Mother Teresa Uni, Skopje              *)
(*                   2018 - 2019                   *)
(*                                                 *)
(***************************************************)


{
open Lexing
open IntermediateSyntax
open Parser

let keyword = Hashtbl.create 15
let keycpps = Hashtbl.create 10

let _ = List.iter (fun (a,b) -> Hashtbl.add keyword a b)
	[
		"assert", TOK_ASSERT;
		"__VERIFIER_assert", TOK_ASSERT;
		"else", TOK_ELSE;
		"false", TOK_FALSE;
		"if", TOK_IF;
		"int", TOK_INT;
		"unsigned", TOK_UINT;
		"char", TOK_CHAR;
		"bool", TOK_BOOL;
		"features", TOK_FEAT;
		"for", TOK_FOR;
		"return", TOK_RETURN;
		"true", TOK_TRUE;
		"void", TOK_VOID;
		"while", TOK_WHILE;
		"break", TOK_RETURN; (* WARNING: cheating *)
	];
		List.iter (fun (a,b) -> Hashtbl.add keycpps a b)
	[
		"#if", TOK_CPP_IF;
		"#else", TOK_CPP_ELSE;
		"#endif", TOK_CPP_ENDIF;
		"#ifdef", TOK_CPP_IFDEF;
		"#ifndef", TOK_CPP_IFNDEF;
		"#define", TOK_CPP_DEFINE;
	]	
}

let space = [' ' '\t' '\r']+
let newline = "\n" | "\r" | "\r\n"

let digit = ['0'-'9']
let integer = digit digit*

rule start = parse
	| space	{ start lexbuf }
	| ""	{ token lexbuf }

and token = parse
	| ['a'-'z' 'A'-'Z' '_'] ['a'-'z' 'A'-'Z' '0'-'9' '_']* as id
		{ try Hashtbl.find keyword id with Not_found -> TOK_id id }
	| ['#'] ['a'-'z' 'A'-'Z' '0'-'9' '_']* as id
		{ try Hashtbl.find keycpps id with Not_found -> token lexbuf }


	| "("										{ TOK_LPAREN }
	| ")"										{ TOK_RPAREN }
	| "["										{ TOK_LBRACKET }
	| "]"										{ TOK_RBRACKET }
	| "{"										{ TOK_LCURLY }
	| "}"										{ TOK_RCURLY }
	| ","										{ TOK_COMMA }
	| ":"										{ TOK_COLON }
	| ";"										{ TOK_SEMICOLON }
	| "&&"										{ TOK_AND }
	| "||"										{ TOK_OR }
	| "!"										{ TOK_NOT }
	| "<"										{ TOK_LESS }
	| "<="										{ TOK_LESS_EQUAL }
	| "=="										{ TOK_EQUAL_EQUAL }
	| "!="										{ TOK_NOT_EQUAL }
	| ">"										{ TOK_GREATER }
	| ">="										{ TOK_GREATER_EQUAL }
	| "+"										{ TOK_PLUS }
	| "++"										{ TOK_PLUS_PLUS }
	| "-"										{ TOK_MINUS }
	| "--"										{ TOK_MINUS_MINUS }
	| "*"										{ TOK_MULTIPLY } 
	| "/"										{ TOK_DIVIDE }
	| "%"										{ TOK_MODULO }
	| "="										{ TOK_EQUAL }
	| "+="										{ TOK_PLUS_EQUAL }
	| "-="										{ TOK_MINUS_EQUAL }
	| "*="										{ TOK_MULTIPLY_EQUAL }
	| "/="										{ TOK_DIVIDE_EQUAL }
	| "%="										{ TOK_MODULO_EQUAL }
	| "?"										{ TOK_RANDOM }
	| "__VERIFIER_nondet_int()"					{ TOK_RANDOM }
	| "(int*) "? "alloca" [^ ';' '\n' '\r']*	{ TOK_RANDOM }
	| "malloc" [^ ';' '\n' '\r']*				{ TOK_RANDOM }
	| "__VERIFIER_nondet_uint()"				{ TOK_URANDOM }	

	| integer as c				{ TOK_const c }

	| "/*"						{ comment lexbuf; token lexbuf }
	| "//" [^ '\n' '\r']*		{ token lexbuf }
	| "extern" [^ '\n' '\r']*	{ token lexbuf }
	| "#include" [^ '\n' '\r']*	{ token lexbuf }
	| "const "					{ token lexbuf }
	| "__VERIFIER_error();"		{ token lexbuf }
	| "typedef" space "enum"
				space? "{"
				space? "false"
				space? ","
				space? "true"
				space? "}"
				space? "bool"
				space? ";"      { token lexbuf }
	| newline					{ new_line lexbuf; start lexbuf }
	| space						{ token lexbuf }

	| eof						{ TOK_EOF }

and comment = parse
	| "*/"			{ () }
	| [^ '\n' '\r']	{ comment lexbuf }
	| newline		{ new_line lexbuf; comment lexbuf }
