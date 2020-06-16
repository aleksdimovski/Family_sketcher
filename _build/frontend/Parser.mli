
(* The type of tokens. *)

type token = 
  | TOK_id of (string)
  | TOK_const of (string)
  | TOK_WHILE
  | TOK_VOID
  | TOK_URANDOM
  | TOK_UINT
  | TOK_TRUE
  | TOK_SEMICOLON
  | TOK_RPAREN
  | TOK_RETURN
  | TOK_RCURLY
  | TOK_RBRACKET
  | TOK_RANDOM
  | TOK_PLUS_PLUS
  | TOK_PLUS_EQUAL
  | TOK_PLUS
  | TOK_OR
  | TOK_NOT_EQUAL
  | TOK_NOT
  | TOK_MULTIPLY_EQUAL
  | TOK_MULTIPLY
  | TOK_MODULO_EQUAL
  | TOK_MODULO
  | TOK_MINUS_MINUS
  | TOK_MINUS_EQUAL
  | TOK_MINUS
  | TOK_LPAREN
  | TOK_LESS_EQUAL
  | TOK_LESS
  | TOK_LCURLY
  | TOK_LBRACKET
  | TOK_INT
  | TOK_IF
  | TOK_GREATER_EQUAL
  | TOK_GREATER
  | TOK_FOR
  | TOK_FEAT
  | TOK_FALSE
  | TOK_EQUAL_EQUAL
  | TOK_EQUAL
  | TOK_EOF
  | TOK_ELSE
  | TOK_DIVIDE_EQUAL
  | TOK_DIVIDE
  | TOK_CPP_IFNDEF
  | TOK_CPP_IFDEF
  | TOK_CPP_IF
  | TOK_CPP_ENDIF
  | TOK_CPP_ELSE
  | TOK_CPP_DEFINE
  | TOK_COMMA
  | TOK_COLON
  | TOK_CHAR
  | TOK_BOOL
  | TOK_ASSERT
  | TOK_AND

(* This exception is raised by the monolithic API functions. *)

exception Error

(* The monolithic API. *)

val file: (Lexing.lexbuf -> token) -> Lexing.lexbuf -> (IntermediateSyntax.decl list IntermediateSyntax.annotated)
