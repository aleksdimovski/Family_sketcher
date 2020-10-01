
module MenhirBasics = struct
  
  exception Error
  
  type token = 
    | TOK_id of (
# 35 "frontend/Parser.mly"
       (string)
# 11 "frontend/Parser.ml"
  )
    | TOK_const of (
# 71 "frontend/Parser.mly"
       (string)
# 16 "frontend/Parser.ml"
  )
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
  
end

include MenhirBasics

let _eRR =
  MenhirBasics.Error

type _menhir_env = {
  _menhir_lexer: Lexing.lexbuf -> token;
  _menhir_lexbuf: Lexing.lexbuf;
  _menhir_token: token;
  mutable _menhir_error: bool
}

and _menhir_state = 
  | MenhirState234
  | MenhirState230
  | MenhirState228
  | MenhirState226
  | MenhirState223
  | MenhirState215
  | MenhirState214
  | MenhirState211
  | MenhirState208
  | MenhirState207
  | MenhirState203
  | MenhirState199
  | MenhirState197
  | MenhirState193
  | MenhirState188
  | MenhirState185
  | MenhirState183
  | MenhirState181
  | MenhirState171
  | MenhirState156
  | MenhirState154
  | MenhirState152
  | MenhirState150
  | MenhirState148
  | MenhirState146
  | MenhirState142
  | MenhirState139
  | MenhirState134
  | MenhirState133
  | MenhirState131
  | MenhirState129
  | MenhirState127
  | MenhirState122
  | MenhirState120
  | MenhirState112
  | MenhirState106
  | MenhirState101
  | MenhirState98
  | MenhirState95
  | MenhirState92
  | MenhirState90
  | MenhirState88
  | MenhirState85
  | MenhirState82
  | MenhirState79
  | MenhirState77
  | MenhirState75
  | MenhirState72
  | MenhirState70
  | MenhirState52
  | MenhirState44
  | MenhirState39
  | MenhirState35
  | MenhirState34
  | MenhirState32
  | MenhirState29
  | MenhirState27
  | MenhirState22
  | MenhirState18
  | MenhirState17
  | MenhirState14
  | MenhirState11
  | MenhirState4
  | MenhirState1
  | MenhirState0

# 9 "frontend/Parser.mly"
  
open IntermediateSyntax

# 158 "frontend/Parser.ml"

let rec _menhir_goto_separated_nonempty_list_TOK_COMMA_annotate_exp__ : _menhir_env -> 'ttv_tail -> _menhir_state -> (IntermediateSyntax.exp IntermediateSyntax.annotated list) -> 'ttv_return =
  fun _menhir_env _menhir_stack _menhir_s _v ->
    match _menhir_s with
    | MenhirState52 ->
        let _menhir_stack = Obj.magic _menhir_stack in
        let _menhir_stack = Obj.magic _menhir_stack in
        let (x : (IntermediateSyntax.exp IntermediateSyntax.annotated list)) = _v in
        let _v : (IntermediateSyntax.exp IntermediateSyntax.annotated list) = 
# 130 "/usr/share/menhir/standard.mly"
    ( x )
# 170 "frontend/Parser.ml"
         in
        _menhir_goto_loption_separated_nonempty_list_TOK_COMMA_annotate_exp___ _menhir_env _menhir_stack _menhir_s _v
    | MenhirState112 ->
        let _menhir_stack = Obj.magic _menhir_stack in
        let _menhir_stack = Obj.magic _menhir_stack in
        let (xs : (IntermediateSyntax.exp IntermediateSyntax.annotated list)) = _v in
        let (_menhir_stack, _endpos_x_, _menhir_s, (x : (IntermediateSyntax.exp IntermediateSyntax.annotated)), _startpos_x_) = _menhir_stack in
        let _2 = () in
        let _v : (IntermediateSyntax.exp IntermediateSyntax.annotated list) = 
# 217 "/usr/share/menhir/standard.mly"
    ( x :: xs )
# 182 "frontend/Parser.ml"
         in
        _menhir_goto_separated_nonempty_list_TOK_COMMA_annotate_exp__ _menhir_env _menhir_stack _menhir_s _v
    | _ ->
        _menhir_fail ()

and _menhir_run98 : _menhir_env -> 'ttv_tail * Lexing.position * _menhir_state * (IntermediateSyntax.exp IntermediateSyntax.annotated) * Lexing.position -> 'ttv_return =
  fun _menhir_env _menhir_stack ->
    let _menhir_env = _menhir_discard _menhir_env in
    let _tok = _menhir_env._menhir_token in
    match _tok with
    | TOK_FALSE ->
        _menhir_run43 _menhir_env (Obj.magic _menhir_stack) _menhir_env._menhir_lexbuf.Lexing.lex_curr_p MenhirState98 _menhir_env._menhir_lexbuf.Lexing.lex_start_p
    | TOK_LBRACKET ->
        _menhir_run35 _menhir_env (Obj.magic _menhir_stack) MenhirState98 _menhir_env._menhir_lexbuf.Lexing.lex_start_p
    | TOK_LPAREN ->
        _menhir_run34 _menhir_env (Obj.magic _menhir_stack) MenhirState98 _menhir_env._menhir_lexbuf.Lexing.lex_start_p
    | TOK_MINUS ->
        _menhir_run33 _menhir_env (Obj.magic _menhir_stack) MenhirState98 _menhir_env._menhir_lexbuf.Lexing.lex_start_p
    | TOK_MINUS_MINUS ->
        _menhir_run32 _menhir_env (Obj.magic _menhir_stack) _menhir_env._menhir_lexbuf.Lexing.lex_curr_p MenhirState98 _menhir_env._menhir_lexbuf.Lexing.lex_start_p
    | TOK_MULTIPLY ->
        _menhir_run30 _menhir_env (Obj.magic _menhir_stack) MenhirState98 _menhir_env._menhir_lexbuf.Lexing.lex_start_p
    | TOK_NOT ->
        _menhir_run29 _menhir_env (Obj.magic _menhir_stack) MenhirState98 _menhir_env._menhir_lexbuf.Lexing.lex_start_p
    | TOK_PLUS ->
        _menhir_run28 _menhir_env (Obj.magic _menhir_stack) MenhirState98 _menhir_env._menhir_lexbuf.Lexing.lex_start_p
    | TOK_PLUS_PLUS ->
        _menhir_run27 _menhir_env (Obj.magic _menhir_stack) _menhir_env._menhir_lexbuf.Lexing.lex_curr_p MenhirState98 _menhir_env._menhir_lexbuf.Lexing.lex_start_p
    | TOK_RANDOM ->
        _menhir_run26 _menhir_env (Obj.magic _menhir_stack) _menhir_env._menhir_lexbuf.Lexing.lex_curr_p MenhirState98 _menhir_env._menhir_lexbuf.Lexing.lex_start_p
    | TOK_TRUE ->
        _menhir_run25 _menhir_env (Obj.magic _menhir_stack) _menhir_env._menhir_lexbuf.Lexing.lex_curr_p MenhirState98 _menhir_env._menhir_lexbuf.Lexing.lex_start_p
    | TOK_URANDOM ->
        _menhir_run24 _menhir_env (Obj.magic _menhir_stack) _menhir_env._menhir_lexbuf.Lexing.lex_curr_p MenhirState98 _menhir_env._menhir_lexbuf.Lexing.lex_start_p
    | TOK_const _v ->
        _menhir_run20 _menhir_env (Obj.magic _menhir_stack) _menhir_env._menhir_lexbuf.Lexing.lex_curr_p MenhirState98 _v _menhir_env._menhir_lexbuf.Lexing.lex_start_p
    | TOK_id _v ->
        _menhir_run23 _menhir_env (Obj.magic _menhir_stack) _menhir_env._menhir_lexbuf.Lexing.lex_curr_p MenhirState98 _v _menhir_env._menhir_lexbuf.Lexing.lex_start_p
    | _ ->
        assert (not _menhir_env._menhir_error);
        _menhir_env._menhir_error <- true;
        _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) MenhirState98

and _menhir_goto_exp : _menhir_env -> 'ttv_tail -> Lexing.position -> _menhir_state -> (IntermediateSyntax.exp) -> Lexing.position -> 'ttv_return =
  fun _menhir_env _menhir_stack _endpos _menhir_s _v _startpos ->
    let _menhir_stack = (_menhir_stack, _endpos, _menhir_s, _v, _startpos) in
    match _menhir_s with
    | MenhirState215 | MenhirState207 | MenhirState193 | MenhirState18 | MenhirState120 | MenhirState188 | MenhirState129 | MenhirState185 | MenhirState183 | MenhirState181 | MenhirState150 | MenhirState171 | MenhirState154 | MenhirState156 | MenhirState152 | MenhirState148 | MenhirState146 | MenhirState142 | MenhirState131 | MenhirState127 | MenhirState122 | MenhirState22 | MenhirState112 | MenhirState70 | MenhirState52 ->
        let _menhir_stack = Obj.magic _menhir_stack in
        let _menhir_stack = Obj.magic _menhir_stack in
        let (_menhir_stack, _endpos_x_, _menhir_s, (x : (IntermediateSyntax.exp)), _startpos_x_) = _menhir_stack in
        let _startpos = _startpos_x_ in
        let _endpos = _endpos_x_ in
        let _v : (IntermediateSyntax.exp IntermediateSyntax.annotated) = let _endpos = _endpos_x_ in
        let _startpos = _startpos_x_ in
        
# 236 "frontend/Parser.mly"
          ( x, (_startpos, _endpos) )
# 241 "frontend/Parser.ml"
         in
        let _menhir_stack = (_menhir_stack, _endpos, _menhir_s, _v, _startpos) in
        (match _menhir_s with
        | MenhirState70 ->
            let _menhir_stack = Obj.magic _menhir_stack in
            let _menhir_stack = Obj.magic _menhir_stack in
            let (((_menhir_stack, _endpos_e1_, _menhir_s, (e1 : (IntermediateSyntax.exp IntermediateSyntax.annotated)), _startpos_e1_), (o : (IntermediateSyntax.assignOp))), _endpos_e2_, _, (e2 : (IntermediateSyntax.exp IntermediateSyntax.annotated)), _startpos_e2_) = _menhir_stack in
            let _startpos = _startpos_e1_ in
            let _endpos = _endpos_e2_ in
            let _v : (IntermediateSyntax.exp) = 
# 166 "frontend/Parser.mly"
                                                             ( I_assign (e1,o,e2) )
# 254 "frontend/Parser.ml"
             in
            _menhir_goto_exp _menhir_env _menhir_stack _endpos _menhir_s _v _startpos
        | MenhirState112 | MenhirState52 ->
            let _menhir_stack = Obj.magic _menhir_stack in
            assert (not _menhir_env._menhir_error);
            let _tok = _menhir_env._menhir_token in
            (match _tok with
            | TOK_COMMA ->
                let _menhir_stack = Obj.magic _menhir_stack in
                let _menhir_env = _menhir_discard _menhir_env in
                let _tok = _menhir_env._menhir_token in
                (match _tok with
                | TOK_FALSE ->
                    _menhir_run43 _menhir_env (Obj.magic _menhir_stack) _menhir_env._menhir_lexbuf.Lexing.lex_curr_p MenhirState112 _menhir_env._menhir_lexbuf.Lexing.lex_start_p
                | TOK_LBRACKET ->
                    _menhir_run35 _menhir_env (Obj.magic _menhir_stack) MenhirState112 _menhir_env._menhir_lexbuf.Lexing.lex_start_p
                | TOK_LPAREN ->
                    _menhir_run34 _menhir_env (Obj.magic _menhir_stack) MenhirState112 _menhir_env._menhir_lexbuf.Lexing.lex_start_p
                | TOK_MINUS ->
                    _menhir_run33 _menhir_env (Obj.magic _menhir_stack) MenhirState112 _menhir_env._menhir_lexbuf.Lexing.lex_start_p
                | TOK_MINUS_MINUS ->
                    _menhir_run32 _menhir_env (Obj.magic _menhir_stack) _menhir_env._menhir_lexbuf.Lexing.lex_curr_p MenhirState112 _menhir_env._menhir_lexbuf.Lexing.lex_start_p
                | TOK_MULTIPLY ->
                    _menhir_run30 _menhir_env (Obj.magic _menhir_stack) MenhirState112 _menhir_env._menhir_lexbuf.Lexing.lex_start_p
                | TOK_NOT ->
                    _menhir_run29 _menhir_env (Obj.magic _menhir_stack) MenhirState112 _menhir_env._menhir_lexbuf.Lexing.lex_start_p
                | TOK_PLUS ->
                    _menhir_run28 _menhir_env (Obj.magic _menhir_stack) MenhirState112 _menhir_env._menhir_lexbuf.Lexing.lex_start_p
                | TOK_PLUS_PLUS ->
                    _menhir_run27 _menhir_env (Obj.magic _menhir_stack) _menhir_env._menhir_lexbuf.Lexing.lex_curr_p MenhirState112 _menhir_env._menhir_lexbuf.Lexing.lex_start_p
                | TOK_RANDOM ->
                    _menhir_run26 _menhir_env (Obj.magic _menhir_stack) _menhir_env._menhir_lexbuf.Lexing.lex_curr_p MenhirState112 _menhir_env._menhir_lexbuf.Lexing.lex_start_p
                | TOK_TRUE ->
                    _menhir_run25 _menhir_env (Obj.magic _menhir_stack) _menhir_env._menhir_lexbuf.Lexing.lex_curr_p MenhirState112 _menhir_env._menhir_lexbuf.Lexing.lex_start_p
                | TOK_URANDOM ->
                    _menhir_run24 _menhir_env (Obj.magic _menhir_stack) _menhir_env._menhir_lexbuf.Lexing.lex_curr_p MenhirState112 _menhir_env._menhir_lexbuf.Lexing.lex_start_p
                | TOK_const _v ->
                    _menhir_run20 _menhir_env (Obj.magic _menhir_stack) _menhir_env._menhir_lexbuf.Lexing.lex_curr_p MenhirState112 _v _menhir_env._menhir_lexbuf.Lexing.lex_start_p
                | TOK_id _v ->
                    _menhir_run23 _menhir_env (Obj.magic _menhir_stack) _menhir_env._menhir_lexbuf.Lexing.lex_curr_p MenhirState112 _v _menhir_env._menhir_lexbuf.Lexing.lex_start_p
                | _ ->
                    assert (not _menhir_env._menhir_error);
                    _menhir_env._menhir_error <- true;
                    _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) MenhirState112)
            | TOK_RPAREN ->
                let _menhir_stack = Obj.magic _menhir_stack in
                let (_menhir_stack, _endpos_x_, _menhir_s, (x : (IntermediateSyntax.exp IntermediateSyntax.annotated)), _startpos_x_) = _menhir_stack in
                let _v : (IntermediateSyntax.exp IntermediateSyntax.annotated list) = 
# 215 "/usr/share/menhir/standard.mly"
    ( [ x ] )
# 305 "frontend/Parser.ml"
                 in
                _menhir_goto_separated_nonempty_list_TOK_COMMA_annotate_exp__ _menhir_env _menhir_stack _menhir_s _v
            | _ ->
                assert (not _menhir_env._menhir_error);
                _menhir_env._menhir_error <- true;
                let _menhir_stack = Obj.magic _menhir_stack in
                let (_menhir_stack, _, _menhir_s, _, _) = _menhir_stack in
                _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s)
        | MenhirState22 ->
            let _menhir_stack = Obj.magic _menhir_stack in
            assert (not _menhir_env._menhir_error);
            let _tok = _menhir_env._menhir_token in
            (match _tok with
            | TOK_RPAREN ->
                let _menhir_stack = Obj.magic _menhir_stack in
                let _endpos = _menhir_env._menhir_lexbuf.Lexing.lex_curr_p in
                let _menhir_stack = (_menhir_stack, _endpos) in
                let _menhir_env = _menhir_discard _menhir_env in
                let _tok = _menhir_env._menhir_token in
                (match _tok with
                | TOK_ASSERT ->
                    _menhir_run155 _menhir_env (Obj.magic _menhir_stack) MenhirState120 _menhir_env._menhir_lexbuf.Lexing.lex_start_p
                | TOK_CHAR ->
                    _menhir_run8 _menhir_env (Obj.magic _menhir_stack) _menhir_env._menhir_lexbuf.Lexing.lex_curr_p MenhirState120 _menhir_env._menhir_lexbuf.Lexing.lex_start_p
                | TOK_CPP_IF ->
                    _menhir_run151 _menhir_env (Obj.magic _menhir_stack) MenhirState120 _menhir_env._menhir_lexbuf.Lexing.lex_start_p
                | TOK_FALSE ->
                    _menhir_run43 _menhir_env (Obj.magic _menhir_stack) _menhir_env._menhir_lexbuf.Lexing.lex_curr_p MenhirState120 _menhir_env._menhir_lexbuf.Lexing.lex_start_p
                | TOK_FOR ->
                    _menhir_run130 _menhir_env (Obj.magic _menhir_stack) MenhirState120 _menhir_env._menhir_lexbuf.Lexing.lex_start_p
                | TOK_IF ->
                    _menhir_run126 _menhir_env (Obj.magic _menhir_stack) MenhirState120 _menhir_env._menhir_lexbuf.Lexing.lex_start_p
                | TOK_INT ->
                    _menhir_run7 _menhir_env (Obj.magic _menhir_stack) _menhir_env._menhir_lexbuf.Lexing.lex_curr_p MenhirState120 _menhir_env._menhir_lexbuf.Lexing.lex_start_p
                | TOK_LBRACKET ->
                    _menhir_run35 _menhir_env (Obj.magic _menhir_stack) MenhirState120 _menhir_env._menhir_lexbuf.Lexing.lex_start_p
                | TOK_LCURLY ->
                    _menhir_run18 _menhir_env (Obj.magic _menhir_stack) MenhirState120 _menhir_env._menhir_lexbuf.Lexing.lex_start_p
                | TOK_LPAREN ->
                    _menhir_run34 _menhir_env (Obj.magic _menhir_stack) MenhirState120 _menhir_env._menhir_lexbuf.Lexing.lex_start_p
                | TOK_MINUS ->
                    _menhir_run33 _menhir_env (Obj.magic _menhir_stack) MenhirState120 _menhir_env._menhir_lexbuf.Lexing.lex_start_p
                | TOK_MINUS_MINUS ->
                    _menhir_run32 _menhir_env (Obj.magic _menhir_stack) _menhir_env._menhir_lexbuf.Lexing.lex_curr_p MenhirState120 _menhir_env._menhir_lexbuf.Lexing.lex_start_p
                | TOK_MULTIPLY ->
                    _menhir_run30 _menhir_env (Obj.magic _menhir_stack) MenhirState120 _menhir_env._menhir_lexbuf.Lexing.lex_start_p
                | TOK_NOT ->
                    _menhir_run29 _menhir_env (Obj.magic _menhir_stack) MenhirState120 _menhir_env._menhir_lexbuf.Lexing.lex_start_p
                | TOK_PLUS ->
                    _menhir_run28 _menhir_env (Obj.magic _menhir_stack) MenhirState120 _menhir_env._menhir_lexbuf.Lexing.lex_start_p
                | TOK_PLUS_PLUS ->
                    _menhir_run27 _menhir_env (Obj.magic _menhir_stack) _menhir_env._menhir_lexbuf.Lexing.lex_curr_p MenhirState120 _menhir_env._menhir_lexbuf.Lexing.lex_start_p
                | TOK_RANDOM ->
                    _menhir_run26 _menhir_env (Obj.magic _menhir_stack) _menhir_env._menhir_lexbuf.Lexing.lex_curr_p MenhirState120 _menhir_env._menhir_lexbuf.Lexing.lex_start_p
                | TOK_RETURN ->
                    _menhir_run122 _menhir_env (Obj.magic _menhir_stack) MenhirState120 _menhir_env._menhir_lexbuf.Lexing.lex_start_p
                | TOK_SEMICOLON ->
                    _menhir_run121 _menhir_env (Obj.magic _menhir_stack) _menhir_env._menhir_lexbuf.Lexing.lex_curr_p MenhirState120 _menhir_env._menhir_lexbuf.Lexing.lex_start_p
                | TOK_TRUE ->
                    _menhir_run25 _menhir_env (Obj.magic _menhir_stack) _menhir_env._menhir_lexbuf.Lexing.lex_curr_p MenhirState120 _menhir_env._menhir_lexbuf.Lexing.lex_start_p
                | TOK_UINT ->
                    _menhir_run5 _menhir_env (Obj.magic _menhir_stack) MenhirState120 _menhir_env._menhir_lexbuf.Lexing.lex_start_p
                | TOK_URANDOM ->
                    _menhir_run24 _menhir_env (Obj.magic _menhir_stack) _menhir_env._menhir_lexbuf.Lexing.lex_curr_p MenhirState120 _menhir_env._menhir_lexbuf.Lexing.lex_start_p
                | TOK_WHILE ->
                    _menhir_run21 _menhir_env (Obj.magic _menhir_stack) MenhirState120 _menhir_env._menhir_lexbuf.Lexing.lex_start_p
                | TOK_const _v ->
                    _menhir_run20 _menhir_env (Obj.magic _menhir_stack) _menhir_env._menhir_lexbuf.Lexing.lex_curr_p MenhirState120 _v _menhir_env._menhir_lexbuf.Lexing.lex_start_p
                | TOK_id _v ->
                    _menhir_run19 _menhir_env (Obj.magic _menhir_stack) _menhir_env._menhir_lexbuf.Lexing.lex_curr_p MenhirState120 _v _menhir_env._menhir_lexbuf.Lexing.lex_start_p
                | _ ->
                    assert (not _menhir_env._menhir_error);
                    _menhir_env._menhir_error <- true;
                    _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) MenhirState120)
            | _ ->
                assert (not _menhir_env._menhir_error);
                _menhir_env._menhir_error <- true;
                let _menhir_stack = Obj.magic _menhir_stack in
                let (_menhir_stack, _, _menhir_s, _, _) = _menhir_stack in
                _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s)
        | MenhirState122 ->
            let _menhir_stack = Obj.magic _menhir_stack in
            let _menhir_stack = Obj.magic _menhir_stack in
            let (_menhir_stack, _endpos_x_, _menhir_s, (x : (IntermediateSyntax.exp IntermediateSyntax.annotated)), _startpos_x_) = _menhir_stack in
            let _v : (IntermediateSyntax.exp IntermediateSyntax.annotated option) = 
# 102 "/usr/share/menhir/standard.mly"
    ( Some x )
# 393 "frontend/Parser.ml"
             in
            _menhir_goto_option_annotate_exp__ _menhir_env _menhir_stack _menhir_s _v
        | MenhirState127 ->
            let _menhir_stack = Obj.magic _menhir_stack in
            assert (not _menhir_env._menhir_error);
            let _tok = _menhir_env._menhir_token in
            (match _tok with
            | TOK_RPAREN ->
                let _menhir_stack = Obj.magic _menhir_stack in
                let _endpos = _menhir_env._menhir_lexbuf.Lexing.lex_curr_p in
                let _menhir_stack = (_menhir_stack, _endpos) in
                let _menhir_env = _menhir_discard _menhir_env in
                let _tok = _menhir_env._menhir_token in
                (match _tok with
                | TOK_ASSERT ->
                    _menhir_run155 _menhir_env (Obj.magic _menhir_stack) MenhirState129 _menhir_env._menhir_lexbuf.Lexing.lex_start_p
                | TOK_CHAR ->
                    _menhir_run8 _menhir_env (Obj.magic _menhir_stack) _menhir_env._menhir_lexbuf.Lexing.lex_curr_p MenhirState129 _menhir_env._menhir_lexbuf.Lexing.lex_start_p
                | TOK_CPP_IF ->
                    _menhir_run151 _menhir_env (Obj.magic _menhir_stack) MenhirState129 _menhir_env._menhir_lexbuf.Lexing.lex_start_p
                | TOK_FALSE ->
                    _menhir_run43 _menhir_env (Obj.magic _menhir_stack) _menhir_env._menhir_lexbuf.Lexing.lex_curr_p MenhirState129 _menhir_env._menhir_lexbuf.Lexing.lex_start_p
                | TOK_FOR ->
                    _menhir_run130 _menhir_env (Obj.magic _menhir_stack) MenhirState129 _menhir_env._menhir_lexbuf.Lexing.lex_start_p
                | TOK_IF ->
                    _menhir_run126 _menhir_env (Obj.magic _menhir_stack) MenhirState129 _menhir_env._menhir_lexbuf.Lexing.lex_start_p
                | TOK_INT ->
                    _menhir_run7 _menhir_env (Obj.magic _menhir_stack) _menhir_env._menhir_lexbuf.Lexing.lex_curr_p MenhirState129 _menhir_env._menhir_lexbuf.Lexing.lex_start_p
                | TOK_LBRACKET ->
                    _menhir_run35 _menhir_env (Obj.magic _menhir_stack) MenhirState129 _menhir_env._menhir_lexbuf.Lexing.lex_start_p
                | TOK_LCURLY ->
                    _menhir_run18 _menhir_env (Obj.magic _menhir_stack) MenhirState129 _menhir_env._menhir_lexbuf.Lexing.lex_start_p
                | TOK_LPAREN ->
                    _menhir_run34 _menhir_env (Obj.magic _menhir_stack) MenhirState129 _menhir_env._menhir_lexbuf.Lexing.lex_start_p
                | TOK_MINUS ->
                    _menhir_run33 _menhir_env (Obj.magic _menhir_stack) MenhirState129 _menhir_env._menhir_lexbuf.Lexing.lex_start_p
                | TOK_MINUS_MINUS ->
                    _menhir_run32 _menhir_env (Obj.magic _menhir_stack) _menhir_env._menhir_lexbuf.Lexing.lex_curr_p MenhirState129 _menhir_env._menhir_lexbuf.Lexing.lex_start_p
                | TOK_MULTIPLY ->
                    _menhir_run30 _menhir_env (Obj.magic _menhir_stack) MenhirState129 _menhir_env._menhir_lexbuf.Lexing.lex_start_p
                | TOK_NOT ->
                    _menhir_run29 _menhir_env (Obj.magic _menhir_stack) MenhirState129 _menhir_env._menhir_lexbuf.Lexing.lex_start_p
                | TOK_PLUS ->
                    _menhir_run28 _menhir_env (Obj.magic _menhir_stack) MenhirState129 _menhir_env._menhir_lexbuf.Lexing.lex_start_p
                | TOK_PLUS_PLUS ->
                    _menhir_run27 _menhir_env (Obj.magic _menhir_stack) _menhir_env._menhir_lexbuf.Lexing.lex_curr_p MenhirState129 _menhir_env._menhir_lexbuf.Lexing.lex_start_p
                | TOK_RANDOM ->
                    _menhir_run26 _menhir_env (Obj.magic _menhir_stack) _menhir_env._menhir_lexbuf.Lexing.lex_curr_p MenhirState129 _menhir_env._menhir_lexbuf.Lexing.lex_start_p
                | TOK_RETURN ->
                    _menhir_run122 _menhir_env (Obj.magic _menhir_stack) MenhirState129 _menhir_env._menhir_lexbuf.Lexing.lex_start_p
                | TOK_SEMICOLON ->
                    _menhir_run121 _menhir_env (Obj.magic _menhir_stack) _menhir_env._menhir_lexbuf.Lexing.lex_curr_p MenhirState129 _menhir_env._menhir_lexbuf.Lexing.lex_start_p
                | TOK_TRUE ->
                    _menhir_run25 _menhir_env (Obj.magic _menhir_stack) _menhir_env._menhir_lexbuf.Lexing.lex_curr_p MenhirState129 _menhir_env._menhir_lexbuf.Lexing.lex_start_p
                | TOK_UINT ->
                    _menhir_run5 _menhir_env (Obj.magic _menhir_stack) MenhirState129 _menhir_env._menhir_lexbuf.Lexing.lex_start_p
                | TOK_URANDOM ->
                    _menhir_run24 _menhir_env (Obj.magic _menhir_stack) _menhir_env._menhir_lexbuf.Lexing.lex_curr_p MenhirState129 _menhir_env._menhir_lexbuf.Lexing.lex_start_p
                | TOK_WHILE ->
                    _menhir_run21 _menhir_env (Obj.magic _menhir_stack) MenhirState129 _menhir_env._menhir_lexbuf.Lexing.lex_start_p
                | TOK_const _v ->
                    _menhir_run20 _menhir_env (Obj.magic _menhir_stack) _menhir_env._menhir_lexbuf.Lexing.lex_curr_p MenhirState129 _v _menhir_env._menhir_lexbuf.Lexing.lex_start_p
                | TOK_id _v ->
                    _menhir_run19 _menhir_env (Obj.magic _menhir_stack) _menhir_env._menhir_lexbuf.Lexing.lex_curr_p MenhirState129 _v _menhir_env._menhir_lexbuf.Lexing.lex_start_p
                | _ ->
                    assert (not _menhir_env._menhir_error);
                    _menhir_env._menhir_error <- true;
                    _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) MenhirState129)
            | _ ->
                assert (not _menhir_env._menhir_error);
                _menhir_env._menhir_error <- true;
                let _menhir_stack = Obj.magic _menhir_stack in
                let (_menhir_stack, _, _menhir_s, _, _) = _menhir_stack in
                _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s)
        | MenhirState142 ->
            let _menhir_stack = Obj.magic _menhir_stack in
            let _menhir_stack = Obj.magic _menhir_stack in
            let ((_menhir_stack, _menhir_s, (d : (string IntermediateSyntax.annotated)), _startpos_d_), _endpos_e_, _, (e : (IntermediateSyntax.exp IntermediateSyntax.annotated)), _startpos_e_) = _menhir_stack in
            let _2 = () in
            let _v : (IntermediateSyntax.declarator) = 
# 99 "frontend/Parser.mly"
                                                      ( d, Some e )
# 476 "frontend/Parser.ml"
             in
            _menhir_goto_declarator _menhir_env _menhir_stack _menhir_s _v
        | MenhirState146 ->
            let _menhir_stack = Obj.magic _menhir_stack in
            assert (not _menhir_env._menhir_error);
            let _tok = _menhir_env._menhir_token in
            (match _tok with
            | TOK_SEMICOLON ->
                let _menhir_stack = Obj.magic _menhir_stack in
                let _endpos = _menhir_env._menhir_lexbuf.Lexing.lex_curr_p in
                let _startpos = _menhir_env._menhir_lexbuf.Lexing.lex_start_p in
                let _menhir_stack = (_menhir_stack, _endpos, _startpos) in
                let _menhir_env = _menhir_discard _menhir_env in
                let _tok = _menhir_env._menhir_token in
                (match _tok with
                | TOK_FALSE ->
                    _menhir_run43 _menhir_env (Obj.magic _menhir_stack) _menhir_env._menhir_lexbuf.Lexing.lex_curr_p MenhirState148 _menhir_env._menhir_lexbuf.Lexing.lex_start_p
                | TOK_LBRACKET ->
                    _menhir_run35 _menhir_env (Obj.magic _menhir_stack) MenhirState148 _menhir_env._menhir_lexbuf.Lexing.lex_start_p
                | TOK_LPAREN ->
                    _menhir_run34 _menhir_env (Obj.magic _menhir_stack) MenhirState148 _menhir_env._menhir_lexbuf.Lexing.lex_start_p
                | TOK_MINUS ->
                    _menhir_run33 _menhir_env (Obj.magic _menhir_stack) MenhirState148 _menhir_env._menhir_lexbuf.Lexing.lex_start_p
                | TOK_MINUS_MINUS ->
                    _menhir_run32 _menhir_env (Obj.magic _menhir_stack) _menhir_env._menhir_lexbuf.Lexing.lex_curr_p MenhirState148 _menhir_env._menhir_lexbuf.Lexing.lex_start_p
                | TOK_MULTIPLY ->
                    _menhir_run30 _menhir_env (Obj.magic _menhir_stack) MenhirState148 _menhir_env._menhir_lexbuf.Lexing.lex_start_p
                | TOK_NOT ->
                    _menhir_run29 _menhir_env (Obj.magic _menhir_stack) MenhirState148 _menhir_env._menhir_lexbuf.Lexing.lex_start_p
                | TOK_PLUS ->
                    _menhir_run28 _menhir_env (Obj.magic _menhir_stack) MenhirState148 _menhir_env._menhir_lexbuf.Lexing.lex_start_p
                | TOK_PLUS_PLUS ->
                    _menhir_run27 _menhir_env (Obj.magic _menhir_stack) _menhir_env._menhir_lexbuf.Lexing.lex_curr_p MenhirState148 _menhir_env._menhir_lexbuf.Lexing.lex_start_p
                | TOK_RANDOM ->
                    _menhir_run26 _menhir_env (Obj.magic _menhir_stack) _menhir_env._menhir_lexbuf.Lexing.lex_curr_p MenhirState148 _menhir_env._menhir_lexbuf.Lexing.lex_start_p
                | TOK_TRUE ->
                    _menhir_run25 _menhir_env (Obj.magic _menhir_stack) _menhir_env._menhir_lexbuf.Lexing.lex_curr_p MenhirState148 _menhir_env._menhir_lexbuf.Lexing.lex_start_p
                | TOK_URANDOM ->
                    _menhir_run24 _menhir_env (Obj.magic _menhir_stack) _menhir_env._menhir_lexbuf.Lexing.lex_curr_p MenhirState148 _menhir_env._menhir_lexbuf.Lexing.lex_start_p
                | TOK_const _v ->
                    _menhir_run20 _menhir_env (Obj.magic _menhir_stack) _menhir_env._menhir_lexbuf.Lexing.lex_curr_p MenhirState148 _v _menhir_env._menhir_lexbuf.Lexing.lex_start_p
                | TOK_id _v ->
                    _menhir_run23 _menhir_env (Obj.magic _menhir_stack) _menhir_env._menhir_lexbuf.Lexing.lex_curr_p MenhirState148 _v _menhir_env._menhir_lexbuf.Lexing.lex_start_p
                | _ ->
                    assert (not _menhir_env._menhir_error);
                    _menhir_env._menhir_error <- true;
                    _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) MenhirState148)
            | _ ->
                assert (not _menhir_env._menhir_error);
                _menhir_env._menhir_error <- true;
                let _menhir_stack = Obj.magic _menhir_stack in
                let (_menhir_stack, _, _menhir_s, _, _) = _menhir_stack in
                _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s)
        | MenhirState148 ->
            let _menhir_stack = Obj.magic _menhir_stack in
            assert (not _menhir_env._menhir_error);
            let _tok = _menhir_env._menhir_token in
            (match _tok with
            | TOK_RPAREN ->
                let _menhir_stack = Obj.magic _menhir_stack in
                let _endpos = _menhir_env._menhir_lexbuf.Lexing.lex_curr_p in
                let _menhir_stack = (_menhir_stack, _endpos) in
                let _menhir_env = _menhir_discard _menhir_env in
                let _tok = _menhir_env._menhir_token in
                (match _tok with
                | TOK_ASSERT ->
                    _menhir_run155 _menhir_env (Obj.magic _menhir_stack) MenhirState150 _menhir_env._menhir_lexbuf.Lexing.lex_start_p
                | TOK_CHAR ->
                    _menhir_run8 _menhir_env (Obj.magic _menhir_stack) _menhir_env._menhir_lexbuf.Lexing.lex_curr_p MenhirState150 _menhir_env._menhir_lexbuf.Lexing.lex_start_p
                | TOK_CPP_IF ->
                    _menhir_run151 _menhir_env (Obj.magic _menhir_stack) MenhirState150 _menhir_env._menhir_lexbuf.Lexing.lex_start_p
                | TOK_FALSE ->
                    _menhir_run43 _menhir_env (Obj.magic _menhir_stack) _menhir_env._menhir_lexbuf.Lexing.lex_curr_p MenhirState150 _menhir_env._menhir_lexbuf.Lexing.lex_start_p
                | TOK_FOR ->
                    _menhir_run130 _menhir_env (Obj.magic _menhir_stack) MenhirState150 _menhir_env._menhir_lexbuf.Lexing.lex_start_p
                | TOK_IF ->
                    _menhir_run126 _menhir_env (Obj.magic _menhir_stack) MenhirState150 _menhir_env._menhir_lexbuf.Lexing.lex_start_p
                | TOK_INT ->
                    _menhir_run7 _menhir_env (Obj.magic _menhir_stack) _menhir_env._menhir_lexbuf.Lexing.lex_curr_p MenhirState150 _menhir_env._menhir_lexbuf.Lexing.lex_start_p
                | TOK_LBRACKET ->
                    _menhir_run35 _menhir_env (Obj.magic _menhir_stack) MenhirState150 _menhir_env._menhir_lexbuf.Lexing.lex_start_p
                | TOK_LCURLY ->
                    _menhir_run18 _menhir_env (Obj.magic _menhir_stack) MenhirState150 _menhir_env._menhir_lexbuf.Lexing.lex_start_p
                | TOK_LPAREN ->
                    _menhir_run34 _menhir_env (Obj.magic _menhir_stack) MenhirState150 _menhir_env._menhir_lexbuf.Lexing.lex_start_p
                | TOK_MINUS ->
                    _menhir_run33 _menhir_env (Obj.magic _menhir_stack) MenhirState150 _menhir_env._menhir_lexbuf.Lexing.lex_start_p
                | TOK_MINUS_MINUS ->
                    _menhir_run32 _menhir_env (Obj.magic _menhir_stack) _menhir_env._menhir_lexbuf.Lexing.lex_curr_p MenhirState150 _menhir_env._menhir_lexbuf.Lexing.lex_start_p
                | TOK_MULTIPLY ->
                    _menhir_run30 _menhir_env (Obj.magic _menhir_stack) MenhirState150 _menhir_env._menhir_lexbuf.Lexing.lex_start_p
                | TOK_NOT ->
                    _menhir_run29 _menhir_env (Obj.magic _menhir_stack) MenhirState150 _menhir_env._menhir_lexbuf.Lexing.lex_start_p
                | TOK_PLUS ->
                    _menhir_run28 _menhir_env (Obj.magic _menhir_stack) MenhirState150 _menhir_env._menhir_lexbuf.Lexing.lex_start_p
                | TOK_PLUS_PLUS ->
                    _menhir_run27 _menhir_env (Obj.magic _menhir_stack) _menhir_env._menhir_lexbuf.Lexing.lex_curr_p MenhirState150 _menhir_env._menhir_lexbuf.Lexing.lex_start_p
                | TOK_RANDOM ->
                    _menhir_run26 _menhir_env (Obj.magic _menhir_stack) _menhir_env._menhir_lexbuf.Lexing.lex_curr_p MenhirState150 _menhir_env._menhir_lexbuf.Lexing.lex_start_p
                | TOK_RETURN ->
                    _menhir_run122 _menhir_env (Obj.magic _menhir_stack) MenhirState150 _menhir_env._menhir_lexbuf.Lexing.lex_start_p
                | TOK_SEMICOLON ->
                    _menhir_run121 _menhir_env (Obj.magic _menhir_stack) _menhir_env._menhir_lexbuf.Lexing.lex_curr_p MenhirState150 _menhir_env._menhir_lexbuf.Lexing.lex_start_p
                | TOK_TRUE ->
                    _menhir_run25 _menhir_env (Obj.magic _menhir_stack) _menhir_env._menhir_lexbuf.Lexing.lex_curr_p MenhirState150 _menhir_env._menhir_lexbuf.Lexing.lex_start_p
                | TOK_UINT ->
                    _menhir_run5 _menhir_env (Obj.magic _menhir_stack) MenhirState150 _menhir_env._menhir_lexbuf.Lexing.lex_start_p
                | TOK_URANDOM ->
                    _menhir_run24 _menhir_env (Obj.magic _menhir_stack) _menhir_env._menhir_lexbuf.Lexing.lex_curr_p MenhirState150 _menhir_env._menhir_lexbuf.Lexing.lex_start_p
                | TOK_WHILE ->
                    _menhir_run21 _menhir_env (Obj.magic _menhir_stack) MenhirState150 _menhir_env._menhir_lexbuf.Lexing.lex_start_p
                | TOK_const _v ->
                    _menhir_run20 _menhir_env (Obj.magic _menhir_stack) _menhir_env._menhir_lexbuf.Lexing.lex_curr_p MenhirState150 _v _menhir_env._menhir_lexbuf.Lexing.lex_start_p
                | TOK_id _v ->
                    _menhir_run19 _menhir_env (Obj.magic _menhir_stack) _menhir_env._menhir_lexbuf.Lexing.lex_curr_p MenhirState150 _v _menhir_env._menhir_lexbuf.Lexing.lex_start_p
                | _ ->
                    assert (not _menhir_env._menhir_error);
                    _menhir_env._menhir_error <- true;
                    _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) MenhirState150)
            | _ ->
                assert (not _menhir_env._menhir_error);
                _menhir_env._menhir_error <- true;
                let _menhir_stack = Obj.magic _menhir_stack in
                let (_menhir_stack, _, _menhir_s, _, _) = _menhir_stack in
                _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s)
        | MenhirState152 ->
            let _menhir_stack = Obj.magic _menhir_stack in
            assert (not _menhir_env._menhir_error);
            let _tok = _menhir_env._menhir_token in
            (match _tok with
            | TOK_RPAREN ->
                let _menhir_stack = Obj.magic _menhir_stack in
                let _endpos = _menhir_env._menhir_lexbuf.Lexing.lex_curr_p in
                let _menhir_stack = (_menhir_stack, _endpos) in
                let _menhir_env = _menhir_discard _menhir_env in
                let _tok = _menhir_env._menhir_token in
                (match _tok with
                | TOK_ASSERT ->
                    _menhir_run155 _menhir_env (Obj.magic _menhir_stack) MenhirState154 _menhir_env._menhir_lexbuf.Lexing.lex_start_p
                | TOK_CHAR ->
                    _menhir_run8 _menhir_env (Obj.magic _menhir_stack) _menhir_env._menhir_lexbuf.Lexing.lex_curr_p MenhirState154 _menhir_env._menhir_lexbuf.Lexing.lex_start_p
                | TOK_CPP_IF ->
                    _menhir_run151 _menhir_env (Obj.magic _menhir_stack) MenhirState154 _menhir_env._menhir_lexbuf.Lexing.lex_start_p
                | TOK_FALSE ->
                    _menhir_run43 _menhir_env (Obj.magic _menhir_stack) _menhir_env._menhir_lexbuf.Lexing.lex_curr_p MenhirState154 _menhir_env._menhir_lexbuf.Lexing.lex_start_p
                | TOK_FOR ->
                    _menhir_run130 _menhir_env (Obj.magic _menhir_stack) MenhirState154 _menhir_env._menhir_lexbuf.Lexing.lex_start_p
                | TOK_IF ->
                    _menhir_run126 _menhir_env (Obj.magic _menhir_stack) MenhirState154 _menhir_env._menhir_lexbuf.Lexing.lex_start_p
                | TOK_INT ->
                    _menhir_run7 _menhir_env (Obj.magic _menhir_stack) _menhir_env._menhir_lexbuf.Lexing.lex_curr_p MenhirState154 _menhir_env._menhir_lexbuf.Lexing.lex_start_p
                | TOK_LBRACKET ->
                    _menhir_run35 _menhir_env (Obj.magic _menhir_stack) MenhirState154 _menhir_env._menhir_lexbuf.Lexing.lex_start_p
                | TOK_LCURLY ->
                    _menhir_run18 _menhir_env (Obj.magic _menhir_stack) MenhirState154 _menhir_env._menhir_lexbuf.Lexing.lex_start_p
                | TOK_LPAREN ->
                    _menhir_run34 _menhir_env (Obj.magic _menhir_stack) MenhirState154 _menhir_env._menhir_lexbuf.Lexing.lex_start_p
                | TOK_MINUS ->
                    _menhir_run33 _menhir_env (Obj.magic _menhir_stack) MenhirState154 _menhir_env._menhir_lexbuf.Lexing.lex_start_p
                | TOK_MINUS_MINUS ->
                    _menhir_run32 _menhir_env (Obj.magic _menhir_stack) _menhir_env._menhir_lexbuf.Lexing.lex_curr_p MenhirState154 _menhir_env._menhir_lexbuf.Lexing.lex_start_p
                | TOK_MULTIPLY ->
                    _menhir_run30 _menhir_env (Obj.magic _menhir_stack) MenhirState154 _menhir_env._menhir_lexbuf.Lexing.lex_start_p
                | TOK_NOT ->
                    _menhir_run29 _menhir_env (Obj.magic _menhir_stack) MenhirState154 _menhir_env._menhir_lexbuf.Lexing.lex_start_p
                | TOK_PLUS ->
                    _menhir_run28 _menhir_env (Obj.magic _menhir_stack) MenhirState154 _menhir_env._menhir_lexbuf.Lexing.lex_start_p
                | TOK_PLUS_PLUS ->
                    _menhir_run27 _menhir_env (Obj.magic _menhir_stack) _menhir_env._menhir_lexbuf.Lexing.lex_curr_p MenhirState154 _menhir_env._menhir_lexbuf.Lexing.lex_start_p
                | TOK_RANDOM ->
                    _menhir_run26 _menhir_env (Obj.magic _menhir_stack) _menhir_env._menhir_lexbuf.Lexing.lex_curr_p MenhirState154 _menhir_env._menhir_lexbuf.Lexing.lex_start_p
                | TOK_RETURN ->
                    _menhir_run122 _menhir_env (Obj.magic _menhir_stack) MenhirState154 _menhir_env._menhir_lexbuf.Lexing.lex_start_p
                | TOK_SEMICOLON ->
                    _menhir_run121 _menhir_env (Obj.magic _menhir_stack) _menhir_env._menhir_lexbuf.Lexing.lex_curr_p MenhirState154 _menhir_env._menhir_lexbuf.Lexing.lex_start_p
                | TOK_TRUE ->
                    _menhir_run25 _menhir_env (Obj.magic _menhir_stack) _menhir_env._menhir_lexbuf.Lexing.lex_curr_p MenhirState154 _menhir_env._menhir_lexbuf.Lexing.lex_start_p
                | TOK_UINT ->
                    _menhir_run5 _menhir_env (Obj.magic _menhir_stack) MenhirState154 _menhir_env._menhir_lexbuf.Lexing.lex_start_p
                | TOK_URANDOM ->
                    _menhir_run24 _menhir_env (Obj.magic _menhir_stack) _menhir_env._menhir_lexbuf.Lexing.lex_curr_p MenhirState154 _menhir_env._menhir_lexbuf.Lexing.lex_start_p
                | TOK_WHILE ->
                    _menhir_run21 _menhir_env (Obj.magic _menhir_stack) MenhirState154 _menhir_env._menhir_lexbuf.Lexing.lex_start_p
                | TOK_const _v ->
                    _menhir_run20 _menhir_env (Obj.magic _menhir_stack) _menhir_env._menhir_lexbuf.Lexing.lex_curr_p MenhirState154 _v _menhir_env._menhir_lexbuf.Lexing.lex_start_p
                | TOK_id _v ->
                    _menhir_run19 _menhir_env (Obj.magic _menhir_stack) _menhir_env._menhir_lexbuf.Lexing.lex_curr_p MenhirState154 _v _menhir_env._menhir_lexbuf.Lexing.lex_start_p
                | _ ->
                    assert (not _menhir_env._menhir_error);
                    _menhir_env._menhir_error <- true;
                    _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) MenhirState154)
            | _ ->
                assert (not _menhir_env._menhir_error);
                _menhir_env._menhir_error <- true;
                let _menhir_stack = Obj.magic _menhir_stack in
                let (_menhir_stack, _, _menhir_s, _, _) = _menhir_stack in
                _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s)
        | MenhirState156 ->
            let _menhir_stack = Obj.magic _menhir_stack in
            assert (not _menhir_env._menhir_error);
            let _tok = _menhir_env._menhir_token in
            (match _tok with
            | TOK_RPAREN ->
                let _menhir_stack = Obj.magic _menhir_stack in
                let _endpos = _menhir_env._menhir_lexbuf.Lexing.lex_curr_p in
                let _menhir_stack = (_menhir_stack, _endpos) in
                let _menhir_env = _menhir_discard _menhir_env in
                let _tok = _menhir_env._menhir_token in
                (match _tok with
                | TOK_SEMICOLON ->
                    let _menhir_stack = Obj.magic _menhir_stack in
                    let _endpos = _menhir_env._menhir_lexbuf.Lexing.lex_curr_p in
                    let _startpos = _menhir_env._menhir_lexbuf.Lexing.lex_start_p in
                    let _menhir_env = _menhir_discard _menhir_env in
                    let _menhir_stack = Obj.magic _menhir_stack in
                    let _endpos__5_ = _endpos in
                    let _startpos__5_ = _startpos in
                    let ((((_menhir_stack, _menhir_s, _startpos__1_), _startpos__2_), _endpos_e_, _, (e : (IntermediateSyntax.exp IntermediateSyntax.annotated)), _startpos_e_), _endpos__4_) = _menhir_stack in
                    let _5 = () in
                    let _4 = () in
                    let _2 = () in
                    let _1 = () in
                    let _startpos = _startpos__1_ in
                    let _endpos = _endpos__5_ in
                    let _v : (IntermediateSyntax.stmt) = 
# 140 "frontend/Parser.mly"
                                                                  ( I_assert e )
# 704 "frontend/Parser.ml"
                     in
                    _menhir_goto_exp_stmt _menhir_env _menhir_stack _endpos _menhir_s _v _startpos
                | _ ->
                    assert (not _menhir_env._menhir_error);
                    _menhir_env._menhir_error <- true;
                    let _menhir_stack = Obj.magic _menhir_stack in
                    let ((_menhir_stack, _, _menhir_s, _, _), _) = _menhir_stack in
                    _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s)
            | _ ->
                assert (not _menhir_env._menhir_error);
                _menhir_env._menhir_error <- true;
                let _menhir_stack = Obj.magic _menhir_stack in
                let (_menhir_stack, _, _menhir_s, _, _) = _menhir_stack in
                _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s)
        | MenhirState18 | MenhirState193 | MenhirState120 | MenhirState129 | MenhirState188 | MenhirState185 | MenhirState150 | MenhirState154 | MenhirState171 ->
            let _menhir_stack = Obj.magic _menhir_stack in
            assert (not _menhir_env._menhir_error);
            let _tok = _menhir_env._menhir_token in
            (match _tok with
            | TOK_SEMICOLON ->
                let _menhir_stack = Obj.magic _menhir_stack in
                let _endpos = _menhir_env._menhir_lexbuf.Lexing.lex_curr_p in
                let _startpos = _menhir_env._menhir_lexbuf.Lexing.lex_start_p in
                let _menhir_env = _menhir_discard _menhir_env in
                let _menhir_stack = Obj.magic _menhir_stack in
                let _endpos__2_ = _endpos in
                let _startpos__2_ = _startpos in
                let (_menhir_stack, _endpos_e_, _menhir_s, (e : (IntermediateSyntax.exp IntermediateSyntax.annotated)), _startpos_e_) = _menhir_stack in
                let _2 = () in
                let _startpos = _startpos_e_ in
                let _endpos = _endpos__2_ in
                let _v : (IntermediateSyntax.stmt) = 
# 139 "frontend/Parser.mly"
                                           ( I_exp e )
# 739 "frontend/Parser.ml"
                 in
                _menhir_goto_exp_stmt _menhir_env _menhir_stack _endpos _menhir_s _v _startpos
            | _ ->
                assert (not _menhir_env._menhir_error);
                _menhir_env._menhir_error <- true;
                let _menhir_stack = Obj.magic _menhir_stack in
                let (_menhir_stack, _, _menhir_s, _, _) = _menhir_stack in
                _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s)
        | MenhirState131 ->
            let _menhir_stack = Obj.magic _menhir_stack in
            assert (not _menhir_env._menhir_error);
            let _tok = _menhir_env._menhir_token in
            (match _tok with
            | TOK_SEMICOLON ->
                let _menhir_stack = Obj.magic _menhir_stack in
                let _endpos = _menhir_env._menhir_lexbuf.Lexing.lex_curr_p in
                let _startpos = _menhir_env._menhir_lexbuf.Lexing.lex_start_p in
                let _menhir_stack = (_menhir_stack, _endpos, _startpos) in
                let _menhir_env = _menhir_discard _menhir_env in
                let _tok = _menhir_env._menhir_token in
                (match _tok with
                | TOK_FALSE ->
                    _menhir_run43 _menhir_env (Obj.magic _menhir_stack) _menhir_env._menhir_lexbuf.Lexing.lex_curr_p MenhirState181 _menhir_env._menhir_lexbuf.Lexing.lex_start_p
                | TOK_LBRACKET ->
                    _menhir_run35 _menhir_env (Obj.magic _menhir_stack) MenhirState181 _menhir_env._menhir_lexbuf.Lexing.lex_start_p
                | TOK_LPAREN ->
                    _menhir_run34 _menhir_env (Obj.magic _menhir_stack) MenhirState181 _menhir_env._menhir_lexbuf.Lexing.lex_start_p
                | TOK_MINUS ->
                    _menhir_run33 _menhir_env (Obj.magic _menhir_stack) MenhirState181 _menhir_env._menhir_lexbuf.Lexing.lex_start_p
                | TOK_MINUS_MINUS ->
                    _menhir_run32 _menhir_env (Obj.magic _menhir_stack) _menhir_env._menhir_lexbuf.Lexing.lex_curr_p MenhirState181 _menhir_env._menhir_lexbuf.Lexing.lex_start_p
                | TOK_MULTIPLY ->
                    _menhir_run30 _menhir_env (Obj.magic _menhir_stack) MenhirState181 _menhir_env._menhir_lexbuf.Lexing.lex_start_p
                | TOK_NOT ->
                    _menhir_run29 _menhir_env (Obj.magic _menhir_stack) MenhirState181 _menhir_env._menhir_lexbuf.Lexing.lex_start_p
                | TOK_PLUS ->
                    _menhir_run28 _menhir_env (Obj.magic _menhir_stack) MenhirState181 _menhir_env._menhir_lexbuf.Lexing.lex_start_p
                | TOK_PLUS_PLUS ->
                    _menhir_run27 _menhir_env (Obj.magic _menhir_stack) _menhir_env._menhir_lexbuf.Lexing.lex_curr_p MenhirState181 _menhir_env._menhir_lexbuf.Lexing.lex_start_p
                | TOK_RANDOM ->
                    _menhir_run26 _menhir_env (Obj.magic _menhir_stack) _menhir_env._menhir_lexbuf.Lexing.lex_curr_p MenhirState181 _menhir_env._menhir_lexbuf.Lexing.lex_start_p
                | TOK_TRUE ->
                    _menhir_run25 _menhir_env (Obj.magic _menhir_stack) _menhir_env._menhir_lexbuf.Lexing.lex_curr_p MenhirState181 _menhir_env._menhir_lexbuf.Lexing.lex_start_p
                | TOK_URANDOM ->
                    _menhir_run24 _menhir_env (Obj.magic _menhir_stack) _menhir_env._menhir_lexbuf.Lexing.lex_curr_p MenhirState181 _menhir_env._menhir_lexbuf.Lexing.lex_start_p
                | TOK_const _v ->
                    _menhir_run20 _menhir_env (Obj.magic _menhir_stack) _menhir_env._menhir_lexbuf.Lexing.lex_curr_p MenhirState181 _v _menhir_env._menhir_lexbuf.Lexing.lex_start_p
                | TOK_id _v ->
                    _menhir_run23 _menhir_env (Obj.magic _menhir_stack) _menhir_env._menhir_lexbuf.Lexing.lex_curr_p MenhirState181 _v _menhir_env._menhir_lexbuf.Lexing.lex_start_p
                | _ ->
                    assert (not _menhir_env._menhir_error);
                    _menhir_env._menhir_error <- true;
                    _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) MenhirState181)
            | _ ->
                assert (not _menhir_env._menhir_error);
                _menhir_env._menhir_error <- true;
                let _menhir_stack = Obj.magic _menhir_stack in
                let (_menhir_stack, _, _menhir_s, _, _) = _menhir_stack in
                _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s)
        | MenhirState181 ->
            let _menhir_stack = Obj.magic _menhir_stack in
            assert (not _menhir_env._menhir_error);
            let _tok = _menhir_env._menhir_token in
            (match _tok with
            | TOK_SEMICOLON ->
                let _menhir_stack = Obj.magic _menhir_stack in
                let _endpos = _menhir_env._menhir_lexbuf.Lexing.lex_curr_p in
                let _startpos = _menhir_env._menhir_lexbuf.Lexing.lex_start_p in
                let _menhir_stack = (_menhir_stack, _endpos, _startpos) in
                let _menhir_env = _menhir_discard _menhir_env in
                let _tok = _menhir_env._menhir_token in
                (match _tok with
                | TOK_FALSE ->
                    _menhir_run43 _menhir_env (Obj.magic _menhir_stack) _menhir_env._menhir_lexbuf.Lexing.lex_curr_p MenhirState183 _menhir_env._menhir_lexbuf.Lexing.lex_start_p
                | TOK_LBRACKET ->
                    _menhir_run35 _menhir_env (Obj.magic _menhir_stack) MenhirState183 _menhir_env._menhir_lexbuf.Lexing.lex_start_p
                | TOK_LPAREN ->
                    _menhir_run34 _menhir_env (Obj.magic _menhir_stack) MenhirState183 _menhir_env._menhir_lexbuf.Lexing.lex_start_p
                | TOK_MINUS ->
                    _menhir_run33 _menhir_env (Obj.magic _menhir_stack) MenhirState183 _menhir_env._menhir_lexbuf.Lexing.lex_start_p
                | TOK_MINUS_MINUS ->
                    _menhir_run32 _menhir_env (Obj.magic _menhir_stack) _menhir_env._menhir_lexbuf.Lexing.lex_curr_p MenhirState183 _menhir_env._menhir_lexbuf.Lexing.lex_start_p
                | TOK_MULTIPLY ->
                    _menhir_run30 _menhir_env (Obj.magic _menhir_stack) MenhirState183 _menhir_env._menhir_lexbuf.Lexing.lex_start_p
                | TOK_NOT ->
                    _menhir_run29 _menhir_env (Obj.magic _menhir_stack) MenhirState183 _menhir_env._menhir_lexbuf.Lexing.lex_start_p
                | TOK_PLUS ->
                    _menhir_run28 _menhir_env (Obj.magic _menhir_stack) MenhirState183 _menhir_env._menhir_lexbuf.Lexing.lex_start_p
                | TOK_PLUS_PLUS ->
                    _menhir_run27 _menhir_env (Obj.magic _menhir_stack) _menhir_env._menhir_lexbuf.Lexing.lex_curr_p MenhirState183 _menhir_env._menhir_lexbuf.Lexing.lex_start_p
                | TOK_RANDOM ->
                    _menhir_run26 _menhir_env (Obj.magic _menhir_stack) _menhir_env._menhir_lexbuf.Lexing.lex_curr_p MenhirState183 _menhir_env._menhir_lexbuf.Lexing.lex_start_p
                | TOK_TRUE ->
                    _menhir_run25 _menhir_env (Obj.magic _menhir_stack) _menhir_env._menhir_lexbuf.Lexing.lex_curr_p MenhirState183 _menhir_env._menhir_lexbuf.Lexing.lex_start_p
                | TOK_URANDOM ->
                    _menhir_run24 _menhir_env (Obj.magic _menhir_stack) _menhir_env._menhir_lexbuf.Lexing.lex_curr_p MenhirState183 _menhir_env._menhir_lexbuf.Lexing.lex_start_p
                | TOK_const _v ->
                    _menhir_run20 _menhir_env (Obj.magic _menhir_stack) _menhir_env._menhir_lexbuf.Lexing.lex_curr_p MenhirState183 _v _menhir_env._menhir_lexbuf.Lexing.lex_start_p
                | TOK_id _v ->
                    _menhir_run23 _menhir_env (Obj.magic _menhir_stack) _menhir_env._menhir_lexbuf.Lexing.lex_curr_p MenhirState183 _v _menhir_env._menhir_lexbuf.Lexing.lex_start_p
                | _ ->
                    assert (not _menhir_env._menhir_error);
                    _menhir_env._menhir_error <- true;
                    _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) MenhirState183)
            | _ ->
                assert (not _menhir_env._menhir_error);
                _menhir_env._menhir_error <- true;
                let _menhir_stack = Obj.magic _menhir_stack in
                let (_menhir_stack, _, _menhir_s, _, _) = _menhir_stack in
                _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s)
        | MenhirState183 ->
            let _menhir_stack = Obj.magic _menhir_stack in
            assert (not _menhir_env._menhir_error);
            let _tok = _menhir_env._menhir_token in
            (match _tok with
            | TOK_RPAREN ->
                let _menhir_stack = Obj.magic _menhir_stack in
                let _endpos = _menhir_env._menhir_lexbuf.Lexing.lex_curr_p in
                let _menhir_stack = (_menhir_stack, _endpos) in
                let _menhir_env = _menhir_discard _menhir_env in
                let _tok = _menhir_env._menhir_token in
                (match _tok with
                | TOK_ASSERT ->
                    _menhir_run155 _menhir_env (Obj.magic _menhir_stack) MenhirState185 _menhir_env._menhir_lexbuf.Lexing.lex_start_p
                | TOK_CHAR ->
                    _menhir_run8 _menhir_env (Obj.magic _menhir_stack) _menhir_env._menhir_lexbuf.Lexing.lex_curr_p MenhirState185 _menhir_env._menhir_lexbuf.Lexing.lex_start_p
                | TOK_CPP_IF ->
                    _menhir_run151 _menhir_env (Obj.magic _menhir_stack) MenhirState185 _menhir_env._menhir_lexbuf.Lexing.lex_start_p
                | TOK_FALSE ->
                    _menhir_run43 _menhir_env (Obj.magic _menhir_stack) _menhir_env._menhir_lexbuf.Lexing.lex_curr_p MenhirState185 _menhir_env._menhir_lexbuf.Lexing.lex_start_p
                | TOK_FOR ->
                    _menhir_run130 _menhir_env (Obj.magic _menhir_stack) MenhirState185 _menhir_env._menhir_lexbuf.Lexing.lex_start_p
                | TOK_IF ->
                    _menhir_run126 _menhir_env (Obj.magic _menhir_stack) MenhirState185 _menhir_env._menhir_lexbuf.Lexing.lex_start_p
                | TOK_INT ->
                    _menhir_run7 _menhir_env (Obj.magic _menhir_stack) _menhir_env._menhir_lexbuf.Lexing.lex_curr_p MenhirState185 _menhir_env._menhir_lexbuf.Lexing.lex_start_p
                | TOK_LBRACKET ->
                    _menhir_run35 _menhir_env (Obj.magic _menhir_stack) MenhirState185 _menhir_env._menhir_lexbuf.Lexing.lex_start_p
                | TOK_LCURLY ->
                    _menhir_run18 _menhir_env (Obj.magic _menhir_stack) MenhirState185 _menhir_env._menhir_lexbuf.Lexing.lex_start_p
                | TOK_LPAREN ->
                    _menhir_run34 _menhir_env (Obj.magic _menhir_stack) MenhirState185 _menhir_env._menhir_lexbuf.Lexing.lex_start_p
                | TOK_MINUS ->
                    _menhir_run33 _menhir_env (Obj.magic _menhir_stack) MenhirState185 _menhir_env._menhir_lexbuf.Lexing.lex_start_p
                | TOK_MINUS_MINUS ->
                    _menhir_run32 _menhir_env (Obj.magic _menhir_stack) _menhir_env._menhir_lexbuf.Lexing.lex_curr_p MenhirState185 _menhir_env._menhir_lexbuf.Lexing.lex_start_p
                | TOK_MULTIPLY ->
                    _menhir_run30 _menhir_env (Obj.magic _menhir_stack) MenhirState185 _menhir_env._menhir_lexbuf.Lexing.lex_start_p
                | TOK_NOT ->
                    _menhir_run29 _menhir_env (Obj.magic _menhir_stack) MenhirState185 _menhir_env._menhir_lexbuf.Lexing.lex_start_p
                | TOK_PLUS ->
                    _menhir_run28 _menhir_env (Obj.magic _menhir_stack) MenhirState185 _menhir_env._menhir_lexbuf.Lexing.lex_start_p
                | TOK_PLUS_PLUS ->
                    _menhir_run27 _menhir_env (Obj.magic _menhir_stack) _menhir_env._menhir_lexbuf.Lexing.lex_curr_p MenhirState185 _menhir_env._menhir_lexbuf.Lexing.lex_start_p
                | TOK_RANDOM ->
                    _menhir_run26 _menhir_env (Obj.magic _menhir_stack) _menhir_env._menhir_lexbuf.Lexing.lex_curr_p MenhirState185 _menhir_env._menhir_lexbuf.Lexing.lex_start_p
                | TOK_RETURN ->
                    _menhir_run122 _menhir_env (Obj.magic _menhir_stack) MenhirState185 _menhir_env._menhir_lexbuf.Lexing.lex_start_p
                | TOK_SEMICOLON ->
                    _menhir_run121 _menhir_env (Obj.magic _menhir_stack) _menhir_env._menhir_lexbuf.Lexing.lex_curr_p MenhirState185 _menhir_env._menhir_lexbuf.Lexing.lex_start_p
                | TOK_TRUE ->
                    _menhir_run25 _menhir_env (Obj.magic _menhir_stack) _menhir_env._menhir_lexbuf.Lexing.lex_curr_p MenhirState185 _menhir_env._menhir_lexbuf.Lexing.lex_start_p
                | TOK_UINT ->
                    _menhir_run5 _menhir_env (Obj.magic _menhir_stack) MenhirState185 _menhir_env._menhir_lexbuf.Lexing.lex_start_p
                | TOK_URANDOM ->
                    _menhir_run24 _menhir_env (Obj.magic _menhir_stack) _menhir_env._menhir_lexbuf.Lexing.lex_curr_p MenhirState185 _menhir_env._menhir_lexbuf.Lexing.lex_start_p
                | TOK_WHILE ->
                    _menhir_run21 _menhir_env (Obj.magic _menhir_stack) MenhirState185 _menhir_env._menhir_lexbuf.Lexing.lex_start_p
                | TOK_const _v ->
                    _menhir_run20 _menhir_env (Obj.magic _menhir_stack) _menhir_env._menhir_lexbuf.Lexing.lex_curr_p MenhirState185 _v _menhir_env._menhir_lexbuf.Lexing.lex_start_p
                | TOK_id _v ->
                    _menhir_run19 _menhir_env (Obj.magic _menhir_stack) _menhir_env._menhir_lexbuf.Lexing.lex_curr_p MenhirState185 _v _menhir_env._menhir_lexbuf.Lexing.lex_start_p
                | _ ->
                    assert (not _menhir_env._menhir_error);
                    _menhir_env._menhir_error <- true;
                    _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) MenhirState185)
            | _ ->
                assert (not _menhir_env._menhir_error);
                _menhir_env._menhir_error <- true;
                let _menhir_stack = Obj.magic _menhir_stack in
                let (_menhir_stack, _, _menhir_s, _, _) = _menhir_stack in
                _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s)
        | MenhirState207 ->
            let _menhir_stack = Obj.magic _menhir_stack in
            assert (not _menhir_env._menhir_error);
            let _tok = _menhir_env._menhir_token in
            (match _tok with
            | TOK_id _v ->
                _menhir_run2 _menhir_env (Obj.magic _menhir_stack) _menhir_env._menhir_lexbuf.Lexing.lex_curr_p MenhirState208 _v _menhir_env._menhir_lexbuf.Lexing.lex_start_p
            | _ ->
                assert (not _menhir_env._menhir_error);
                _menhir_env._menhir_error <- true;
                _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) MenhirState208)
        | MenhirState215 ->
            let _menhir_stack = Obj.magic _menhir_stack in
            let _menhir_stack = Obj.magic _menhir_stack in
            let (((_menhir_stack, _menhir_s, _startpos__1_), _, (t : (string IntermediateSyntax.annotated)), _startpos_t_), _endpos_e_, _, (e : (IntermediateSyntax.exp IntermediateSyntax.annotated)), _startpos_e_) = _menhir_stack in
            let _1 = () in
            let _startpos = _startpos__1_ in
            let _endpos = _endpos_e_ in
            let _v : (IntermediateSyntax.globalDefine) = 
# 102 "frontend/Parser.mly"
                                                             ( t, e )
# 943 "frontend/Parser.ml"
             in
            let _menhir_stack = Obj.magic _menhir_stack in
            let _menhir_stack = Obj.magic _menhir_stack in
            let _endpos_x_ = _endpos in
            let (x : (IntermediateSyntax.globalDefine)) = _v in
            let _startpos_x_ = _startpos in
            let _startpos = _startpos_x_ in
            let _endpos = _endpos_x_ in
            let _v : (IntermediateSyntax.globalDefine IntermediateSyntax.annotated) = let _endpos = _endpos_x_ in
            let _startpos = _startpos_x_ in
            
# 236 "frontend/Parser.mly"
          ( x, (_startpos, _endpos) )
# 957 "frontend/Parser.ml"
             in
            let _menhir_stack = Obj.magic _menhir_stack in
            let _menhir_stack = Obj.magic _menhir_stack in
            let _endpos_d_ = _endpos in
            let (d : (IntermediateSyntax.globalDefine IntermediateSyntax.annotated)) = _v in
            let _startpos_d_ = _startpos in
            let _startpos = _startpos_d_ in
            let _endpos = _endpos_d_ in
            let _v : (IntermediateSyntax.decl) = 
# 83 "frontend/Parser.mly"
                                ( I_define d )
# 969 "frontend/Parser.ml"
             in
            _menhir_goto_decl _menhir_env _menhir_stack _endpos _menhir_s _v _startpos
        | _ ->
            _menhir_fail ())
    | MenhirState34 ->
        let _menhir_stack = Obj.magic _menhir_stack in
        assert (not _menhir_env._menhir_error);
        let _tok = _menhir_env._menhir_token in
        (match _tok with
        | TOK_RPAREN ->
            let _menhir_stack = Obj.magic _menhir_stack in
            let _endpos = _menhir_env._menhir_lexbuf.Lexing.lex_curr_p in
            let _menhir_env = _menhir_discard _menhir_env in
            let _menhir_stack = Obj.magic _menhir_stack in
            let _endpos__3_ = _endpos in
            let ((_menhir_stack, _menhir_s, _startpos__1_), _endpos_e_, _, (e : (IntermediateSyntax.exp)), _startpos_e_) = _menhir_stack in
            let _3 = () in
            let _1 = () in
            let _startpos = _startpos__1_ in
            let _endpos = _endpos__3_ in
            let _v : (IntermediateSyntax.exp) = 
# 233 "frontend/Parser.mly"
                                                     ( e )
# 993 "frontend/Parser.ml"
             in
            _menhir_goto_primary_exp _menhir_env _menhir_stack _endpos _menhir_s _v _startpos
        | _ ->
            assert (not _menhir_env._menhir_error);
            _menhir_env._menhir_error <- true;
            let _menhir_stack = Obj.magic _menhir_stack in
            let (_menhir_stack, _, _menhir_s, _, _) = _menhir_stack in
            _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s)
    | _ ->
        _menhir_fail ()

and _menhir_run101 : _menhir_env -> 'ttv_tail * Lexing.position * _menhir_state * (IntermediateSyntax.exp IntermediateSyntax.annotated) * Lexing.position -> 'ttv_return =
  fun _menhir_env _menhir_stack ->
    let _menhir_env = _menhir_discard _menhir_env in
    let _tok = _menhir_env._menhir_token in
    match _tok with
    | TOK_FALSE ->
        _menhir_run43 _menhir_env (Obj.magic _menhir_stack) _menhir_env._menhir_lexbuf.Lexing.lex_curr_p MenhirState101 _menhir_env._menhir_lexbuf.Lexing.lex_start_p
    | TOK_LBRACKET ->
        _menhir_run35 _menhir_env (Obj.magic _menhir_stack) MenhirState101 _menhir_env._menhir_lexbuf.Lexing.lex_start_p
    | TOK_LPAREN ->
        _menhir_run34 _menhir_env (Obj.magic _menhir_stack) MenhirState101 _menhir_env._menhir_lexbuf.Lexing.lex_start_p
    | TOK_MINUS ->
        _menhir_run33 _menhir_env (Obj.magic _menhir_stack) MenhirState101 _menhir_env._menhir_lexbuf.Lexing.lex_start_p
    | TOK_MINUS_MINUS ->
        _menhir_run32 _menhir_env (Obj.magic _menhir_stack) _menhir_env._menhir_lexbuf.Lexing.lex_curr_p MenhirState101 _menhir_env._menhir_lexbuf.Lexing.lex_start_p
    | TOK_MULTIPLY ->
        _menhir_run30 _menhir_env (Obj.magic _menhir_stack) MenhirState101 _menhir_env._menhir_lexbuf.Lexing.lex_start_p
    | TOK_NOT ->
        _menhir_run29 _menhir_env (Obj.magic _menhir_stack) MenhirState101 _menhir_env._menhir_lexbuf.Lexing.lex_start_p
    | TOK_PLUS ->
        _menhir_run28 _menhir_env (Obj.magic _menhir_stack) MenhirState101 _menhir_env._menhir_lexbuf.Lexing.lex_start_p
    | TOK_PLUS_PLUS ->
        _menhir_run27 _menhir_env (Obj.magic _menhir_stack) _menhir_env._menhir_lexbuf.Lexing.lex_curr_p MenhirState101 _menhir_env._menhir_lexbuf.Lexing.lex_start_p
    | TOK_RANDOM ->
        _menhir_run26 _menhir_env (Obj.magic _menhir_stack) _menhir_env._menhir_lexbuf.Lexing.lex_curr_p MenhirState101 _menhir_env._menhir_lexbuf.Lexing.lex_start_p
    | TOK_TRUE ->
        _menhir_run25 _menhir_env (Obj.magic _menhir_stack) _menhir_env._menhir_lexbuf.Lexing.lex_curr_p MenhirState101 _menhir_env._menhir_lexbuf.Lexing.lex_start_p
    | TOK_URANDOM ->
        _menhir_run24 _menhir_env (Obj.magic _menhir_stack) _menhir_env._menhir_lexbuf.Lexing.lex_curr_p MenhirState101 _menhir_env._menhir_lexbuf.Lexing.lex_start_p
    | TOK_const _v ->
        _menhir_run20 _menhir_env (Obj.magic _menhir_stack) _menhir_env._menhir_lexbuf.Lexing.lex_curr_p MenhirState101 _v _menhir_env._menhir_lexbuf.Lexing.lex_start_p
    | TOK_id _v ->
        _menhir_run23 _menhir_env (Obj.magic _menhir_stack) _menhir_env._menhir_lexbuf.Lexing.lex_curr_p MenhirState101 _v _menhir_env._menhir_lexbuf.Lexing.lex_start_p
    | _ ->
        assert (not _menhir_env._menhir_error);
        _menhir_env._menhir_error <- true;
        _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) MenhirState101

and _menhir_run106 : _menhir_env -> 'ttv_tail * Lexing.position * _menhir_state * (IntermediateSyntax.exp IntermediateSyntax.annotated) * Lexing.position -> 'ttv_return =
  fun _menhir_env _menhir_stack ->
    let _menhir_env = _menhir_discard _menhir_env in
    let _tok = _menhir_env._menhir_token in
    match _tok with
    | TOK_FALSE ->
        _menhir_run43 _menhir_env (Obj.magic _menhir_stack) _menhir_env._menhir_lexbuf.Lexing.lex_curr_p MenhirState106 _menhir_env._menhir_lexbuf.Lexing.lex_start_p
    | TOK_LBRACKET ->
        _menhir_run35 _menhir_env (Obj.magic _menhir_stack) MenhirState106 _menhir_env._menhir_lexbuf.Lexing.lex_start_p
    | TOK_LPAREN ->
        _menhir_run34 _menhir_env (Obj.magic _menhir_stack) MenhirState106 _menhir_env._menhir_lexbuf.Lexing.lex_start_p
    | TOK_MINUS ->
        _menhir_run33 _menhir_env (Obj.magic _menhir_stack) MenhirState106 _menhir_env._menhir_lexbuf.Lexing.lex_start_p
    | TOK_MINUS_MINUS ->
        _menhir_run32 _menhir_env (Obj.magic _menhir_stack) _menhir_env._menhir_lexbuf.Lexing.lex_curr_p MenhirState106 _menhir_env._menhir_lexbuf.Lexing.lex_start_p
    | TOK_MULTIPLY ->
        _menhir_run30 _menhir_env (Obj.magic _menhir_stack) MenhirState106 _menhir_env._menhir_lexbuf.Lexing.lex_start_p
    | TOK_NOT ->
        _menhir_run29 _menhir_env (Obj.magic _menhir_stack) MenhirState106 _menhir_env._menhir_lexbuf.Lexing.lex_start_p
    | TOK_PLUS ->
        _menhir_run28 _menhir_env (Obj.magic _menhir_stack) MenhirState106 _menhir_env._menhir_lexbuf.Lexing.lex_start_p
    | TOK_PLUS_PLUS ->
        _menhir_run27 _menhir_env (Obj.magic _menhir_stack) _menhir_env._menhir_lexbuf.Lexing.lex_curr_p MenhirState106 _menhir_env._menhir_lexbuf.Lexing.lex_start_p
    | TOK_RANDOM ->
        _menhir_run26 _menhir_env (Obj.magic _menhir_stack) _menhir_env._menhir_lexbuf.Lexing.lex_curr_p MenhirState106 _menhir_env._menhir_lexbuf.Lexing.lex_start_p
    | TOK_TRUE ->
        _menhir_run25 _menhir_env (Obj.magic _menhir_stack) _menhir_env._menhir_lexbuf.Lexing.lex_curr_p MenhirState106 _menhir_env._menhir_lexbuf.Lexing.lex_start_p
    | TOK_URANDOM ->
        _menhir_run24 _menhir_env (Obj.magic _menhir_stack) _menhir_env._menhir_lexbuf.Lexing.lex_curr_p MenhirState106 _menhir_env._menhir_lexbuf.Lexing.lex_start_p
    | TOK_const _v ->
        _menhir_run20 _menhir_env (Obj.magic _menhir_stack) _menhir_env._menhir_lexbuf.Lexing.lex_curr_p MenhirState106 _v _menhir_env._menhir_lexbuf.Lexing.lex_start_p
    | TOK_id _v ->
        _menhir_run23 _menhir_env (Obj.magic _menhir_stack) _menhir_env._menhir_lexbuf.Lexing.lex_curr_p MenhirState106 _v _menhir_env._menhir_lexbuf.Lexing.lex_start_p
    | _ ->
        assert (not _menhir_env._menhir_error);
        _menhir_env._menhir_error <- true;
        _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) MenhirState106

and _menhir_reduce15 : _menhir_env -> 'ttv_tail * Lexing.position * _menhir_state * (IntermediateSyntax.exp) * Lexing.position -> 'ttv_return =
  fun _menhir_env _menhir_stack ->
    let (_menhir_stack, _endpos_x_, _menhir_s, (x : (IntermediateSyntax.exp)), _startpos_x_) = _menhir_stack in
    let _startpos = _startpos_x_ in
    let _endpos = _endpos_x_ in
    let _v : (IntermediateSyntax.exp IntermediateSyntax.annotated) = let _endpos = _endpos_x_ in
    let _startpos = _startpos_x_ in
    
# 236 "frontend/Parser.mly"
          ( x, (_startpos, _endpos) )
# 1091 "frontend/Parser.ml"
     in
    let _menhir_stack = (_menhir_stack, _endpos, _menhir_s, _v, _startpos) in
    match _menhir_s with
    | MenhirState95 ->
        let _menhir_stack = Obj.magic _menhir_stack in
        assert (not _menhir_env._menhir_error);
        let _tok = _menhir_env._menhir_token in
        (match _tok with
        | TOK_AND ->
            _menhir_run98 _menhir_env (Obj.magic _menhir_stack)
        | TOK_CHAR | TOK_COMMA | TOK_CPP_DEFINE | TOK_EOF | TOK_FEAT | TOK_INT | TOK_OR | TOK_RPAREN | TOK_SEMICOLON | TOK_UINT | TOK_VOID | TOK_id _ ->
            let _menhir_stack = Obj.magic _menhir_stack in
            let ((_menhir_stack, _menhir_s, (e1 : (IntermediateSyntax.exp IntermediateSyntax.annotated)), _startpos_e1_), _endpos_e2_, _, (e2 : (IntermediateSyntax.exp IntermediateSyntax.annotated)), _startpos_e2_) = _menhir_stack in
            let _2 = () in
            let _startpos = _startpos_e1_ in
            let _endpos = _endpos_e2_ in
            let _v : (IntermediateSyntax.exp) = 
# 178 "frontend/Parser.mly"
                                                                       ( I_or (e1,e2) )
# 1111 "frontend/Parser.ml"
             in
            _menhir_goto_logical_or_exp _menhir_env _menhir_stack _endpos _menhir_s _v _startpos
        | _ ->
            assert (not _menhir_env._menhir_error);
            _menhir_env._menhir_error <- true;
            let _menhir_stack = Obj.magic _menhir_stack in
            let (_menhir_stack, _, _menhir_s, _, _) = _menhir_stack in
            _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s)
    | MenhirState215 | MenhirState207 | MenhirState18 | MenhirState193 | MenhirState120 | MenhirState129 | MenhirState188 | MenhirState185 | MenhirState183 | MenhirState181 | MenhirState150 | MenhirState154 | MenhirState171 | MenhirState156 | MenhirState152 | MenhirState148 | MenhirState146 | MenhirState142 | MenhirState131 | MenhirState127 | MenhirState122 | MenhirState22 | MenhirState34 | MenhirState112 | MenhirState52 | MenhirState70 ->
        let _menhir_stack = Obj.magic _menhir_stack in
        assert (not _menhir_env._menhir_error);
        let _tok = _menhir_env._menhir_token in
        (match _tok with
        | TOK_AND ->
            _menhir_run98 _menhir_env (Obj.magic _menhir_stack)
        | _ ->
            assert (not _menhir_env._menhir_error);
            _menhir_env._menhir_error <- true;
            let _menhir_stack = Obj.magic _menhir_stack in
            let (_menhir_stack, _, _menhir_s, _, _) = _menhir_stack in
            _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s)
    | _ ->
        _menhir_fail ()

and _menhir_goto_logical_or_exp : _menhir_env -> 'ttv_tail -> Lexing.position -> _menhir_state -> (IntermediateSyntax.exp) -> Lexing.position -> 'ttv_return =
  fun _menhir_env _menhir_stack _endpos _menhir_s _v _startpos ->
    let _menhir_stack = (_menhir_stack, _endpos, _menhir_s, _v, _startpos) in
    let _menhir_stack = Obj.magic _menhir_stack in
    assert (not _menhir_env._menhir_error);
    let _tok = _menhir_env._menhir_token in
    match _tok with
    | TOK_CHAR | TOK_COMMA | TOK_CPP_DEFINE | TOK_EOF | TOK_FEAT | TOK_INT | TOK_RPAREN | TOK_SEMICOLON | TOK_UINT | TOK_VOID | TOK_id _ ->
        let _menhir_stack = Obj.magic _menhir_stack in
        let (_menhir_stack, _endpos_e_, _menhir_s, (e : (IntermediateSyntax.exp)), _startpos_e_) = _menhir_stack in
        let _startpos = _startpos_e_ in
        let _endpos = _endpos_e_ in
        let _v : (IntermediateSyntax.exp) = 
# 165 "frontend/Parser.mly"
                               ( e )
# 1151 "frontend/Parser.ml"
         in
        _menhir_goto_exp _menhir_env _menhir_stack _endpos _menhir_s _v _startpos
    | TOK_OR ->
        let _menhir_stack = Obj.magic _menhir_stack in
        let (_menhir_stack, _endpos_x_, _menhir_s, (x : (IntermediateSyntax.exp)), _startpos_x_) = _menhir_stack in
        let _startpos = _startpos_x_ in
        let _v : (IntermediateSyntax.exp IntermediateSyntax.annotated) = let _endpos = _endpos_x_ in
        let _startpos = _startpos_x_ in
        
# 236 "frontend/Parser.mly"
          ( x, (_startpos, _endpos) )
# 1163 "frontend/Parser.ml"
         in
        let _menhir_stack = (_menhir_stack, _menhir_s, _v, _startpos) in
        let _menhir_stack = Obj.magic _menhir_stack in
        assert (not _menhir_env._menhir_error);
        let _tok = _menhir_env._menhir_token in
        (match _tok with
        | TOK_OR ->
            let _menhir_stack = Obj.magic _menhir_stack in
            let _menhir_env = _menhir_discard _menhir_env in
            let _tok = _menhir_env._menhir_token in
            (match _tok with
            | TOK_FALSE ->
                _menhir_run43 _menhir_env (Obj.magic _menhir_stack) _menhir_env._menhir_lexbuf.Lexing.lex_curr_p MenhirState95 _menhir_env._menhir_lexbuf.Lexing.lex_start_p
            | TOK_LBRACKET ->
                _menhir_run35 _menhir_env (Obj.magic _menhir_stack) MenhirState95 _menhir_env._menhir_lexbuf.Lexing.lex_start_p
            | TOK_LPAREN ->
                _menhir_run34 _menhir_env (Obj.magic _menhir_stack) MenhirState95 _menhir_env._menhir_lexbuf.Lexing.lex_start_p
            | TOK_MINUS ->
                _menhir_run33 _menhir_env (Obj.magic _menhir_stack) MenhirState95 _menhir_env._menhir_lexbuf.Lexing.lex_start_p
            | TOK_MINUS_MINUS ->
                _menhir_run32 _menhir_env (Obj.magic _menhir_stack) _menhir_env._menhir_lexbuf.Lexing.lex_curr_p MenhirState95 _menhir_env._menhir_lexbuf.Lexing.lex_start_p
            | TOK_MULTIPLY ->
                _menhir_run30 _menhir_env (Obj.magic _menhir_stack) MenhirState95 _menhir_env._menhir_lexbuf.Lexing.lex_start_p
            | TOK_NOT ->
                _menhir_run29 _menhir_env (Obj.magic _menhir_stack) MenhirState95 _menhir_env._menhir_lexbuf.Lexing.lex_start_p
            | TOK_PLUS ->
                _menhir_run28 _menhir_env (Obj.magic _menhir_stack) MenhirState95 _menhir_env._menhir_lexbuf.Lexing.lex_start_p
            | TOK_PLUS_PLUS ->
                _menhir_run27 _menhir_env (Obj.magic _menhir_stack) _menhir_env._menhir_lexbuf.Lexing.lex_curr_p MenhirState95 _menhir_env._menhir_lexbuf.Lexing.lex_start_p
            | TOK_RANDOM ->
                _menhir_run26 _menhir_env (Obj.magic _menhir_stack) _menhir_env._menhir_lexbuf.Lexing.lex_curr_p MenhirState95 _menhir_env._menhir_lexbuf.Lexing.lex_start_p
            | TOK_TRUE ->
                _menhir_run25 _menhir_env (Obj.magic _menhir_stack) _menhir_env._menhir_lexbuf.Lexing.lex_curr_p MenhirState95 _menhir_env._menhir_lexbuf.Lexing.lex_start_p
            | TOK_URANDOM ->
                _menhir_run24 _menhir_env (Obj.magic _menhir_stack) _menhir_env._menhir_lexbuf.Lexing.lex_curr_p MenhirState95 _menhir_env._menhir_lexbuf.Lexing.lex_start_p
            | TOK_const _v ->
                _menhir_run20 _menhir_env (Obj.magic _menhir_stack) _menhir_env._menhir_lexbuf.Lexing.lex_curr_p MenhirState95 _v _menhir_env._menhir_lexbuf.Lexing.lex_start_p
            | TOK_id _v ->
                _menhir_run23 _menhir_env (Obj.magic _menhir_stack) _menhir_env._menhir_lexbuf.Lexing.lex_curr_p MenhirState95 _v _menhir_env._menhir_lexbuf.Lexing.lex_start_p
            | _ ->
                assert (not _menhir_env._menhir_error);
                _menhir_env._menhir_error <- true;
                _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) MenhirState95)
        | _ ->
            assert (not _menhir_env._menhir_error);
            _menhir_env._menhir_error <- true;
            let _menhir_stack = Obj.magic _menhir_stack in
            let (_menhir_stack, _menhir_s, _, _) = _menhir_stack in
            _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s)
    | _ ->
        assert (not _menhir_env._menhir_error);
        _menhir_env._menhir_error <- true;
        let _menhir_stack = Obj.magic _menhir_stack in
        let (_menhir_stack, _, _menhir_s, _, _) = _menhir_stack in
        _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s

and _menhir_run72 : _menhir_env -> 'ttv_tail * Lexing.position * _menhir_state * (IntermediateSyntax.exp IntermediateSyntax.annotated) * Lexing.position -> 'ttv_return =
  fun _menhir_env _menhir_stack ->
    let _menhir_env = _menhir_discard _menhir_env in
    let _tok = _menhir_env._menhir_token in
    match _tok with
    | TOK_FALSE ->
        _menhir_run43 _menhir_env (Obj.magic _menhir_stack) _menhir_env._menhir_lexbuf.Lexing.lex_curr_p MenhirState72 _menhir_env._menhir_lexbuf.Lexing.lex_start_p
    | TOK_LBRACKET ->
        _menhir_run35 _menhir_env (Obj.magic _menhir_stack) MenhirState72 _menhir_env._menhir_lexbuf.Lexing.lex_start_p
    | TOK_LPAREN ->
        _menhir_run34 _menhir_env (Obj.magic _menhir_stack) MenhirState72 _menhir_env._menhir_lexbuf.Lexing.lex_start_p
    | TOK_MINUS ->
        _menhir_run33 _menhir_env (Obj.magic _menhir_stack) MenhirState72 _menhir_env._menhir_lexbuf.Lexing.lex_start_p
    | TOK_MINUS_MINUS ->
        _menhir_run32 _menhir_env (Obj.magic _menhir_stack) _menhir_env._menhir_lexbuf.Lexing.lex_curr_p MenhirState72 _menhir_env._menhir_lexbuf.Lexing.lex_start_p
    | TOK_MULTIPLY ->
        _menhir_run30 _menhir_env (Obj.magic _menhir_stack) MenhirState72 _menhir_env._menhir_lexbuf.Lexing.lex_start_p
    | TOK_NOT ->
        _menhir_run29 _menhir_env (Obj.magic _menhir_stack) MenhirState72 _menhir_env._menhir_lexbuf.Lexing.lex_start_p
    | TOK_PLUS ->
        _menhir_run28 _menhir_env (Obj.magic _menhir_stack) MenhirState72 _menhir_env._menhir_lexbuf.Lexing.lex_start_p
    | TOK_PLUS_PLUS ->
        _menhir_run27 _menhir_env (Obj.magic _menhir_stack) _menhir_env._menhir_lexbuf.Lexing.lex_curr_p MenhirState72 _menhir_env._menhir_lexbuf.Lexing.lex_start_p
    | TOK_RANDOM ->
        _menhir_run26 _menhir_env (Obj.magic _menhir_stack) _menhir_env._menhir_lexbuf.Lexing.lex_curr_p MenhirState72 _menhir_env._menhir_lexbuf.Lexing.lex_start_p
    | TOK_TRUE ->
        _menhir_run25 _menhir_env (Obj.magic _menhir_stack) _menhir_env._menhir_lexbuf.Lexing.lex_curr_p MenhirState72 _menhir_env._menhir_lexbuf.Lexing.lex_start_p
    | TOK_URANDOM ->
        _menhir_run24 _menhir_env (Obj.magic _menhir_stack) _menhir_env._menhir_lexbuf.Lexing.lex_curr_p MenhirState72 _menhir_env._menhir_lexbuf.Lexing.lex_start_p
    | TOK_const _v ->
        _menhir_run20 _menhir_env (Obj.magic _menhir_stack) _menhir_env._menhir_lexbuf.Lexing.lex_curr_p MenhirState72 _v _menhir_env._menhir_lexbuf.Lexing.lex_start_p
    | TOK_id _v ->
        _menhir_run23 _menhir_env (Obj.magic _menhir_stack) _menhir_env._menhir_lexbuf.Lexing.lex_curr_p MenhirState72 _v _menhir_env._menhir_lexbuf.Lexing.lex_start_p
    | _ ->
        assert (not _menhir_env._menhir_error);
        _menhir_env._menhir_error <- true;
        _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) MenhirState72

and _menhir_run88 : _menhir_env -> 'ttv_tail * Lexing.position * _menhir_state * (IntermediateSyntax.exp IntermediateSyntax.annotated) * Lexing.position -> 'ttv_return =
  fun _menhir_env _menhir_stack ->
    let _menhir_env = _menhir_discard _menhir_env in
    let _tok = _menhir_env._menhir_token in
    match _tok with
    | TOK_FALSE ->
        _menhir_run43 _menhir_env (Obj.magic _menhir_stack) _menhir_env._menhir_lexbuf.Lexing.lex_curr_p MenhirState88 _menhir_env._menhir_lexbuf.Lexing.lex_start_p
    | TOK_LBRACKET ->
        _menhir_run35 _menhir_env (Obj.magic _menhir_stack) MenhirState88 _menhir_env._menhir_lexbuf.Lexing.lex_start_p
    | TOK_LPAREN ->
        _menhir_run34 _menhir_env (Obj.magic _menhir_stack) MenhirState88 _menhir_env._menhir_lexbuf.Lexing.lex_start_p
    | TOK_MINUS ->
        _menhir_run33 _menhir_env (Obj.magic _menhir_stack) MenhirState88 _menhir_env._menhir_lexbuf.Lexing.lex_start_p
    | TOK_MINUS_MINUS ->
        _menhir_run32 _menhir_env (Obj.magic _menhir_stack) _menhir_env._menhir_lexbuf.Lexing.lex_curr_p MenhirState88 _menhir_env._menhir_lexbuf.Lexing.lex_start_p
    | TOK_MULTIPLY ->
        _menhir_run30 _menhir_env (Obj.magic _menhir_stack) MenhirState88 _menhir_env._menhir_lexbuf.Lexing.lex_start_p
    | TOK_NOT ->
        _menhir_run29 _menhir_env (Obj.magic _menhir_stack) MenhirState88 _menhir_env._menhir_lexbuf.Lexing.lex_start_p
    | TOK_PLUS ->
        _menhir_run28 _menhir_env (Obj.magic _menhir_stack) MenhirState88 _menhir_env._menhir_lexbuf.Lexing.lex_start_p
    | TOK_PLUS_PLUS ->
        _menhir_run27 _menhir_env (Obj.magic _menhir_stack) _menhir_env._menhir_lexbuf.Lexing.lex_curr_p MenhirState88 _menhir_env._menhir_lexbuf.Lexing.lex_start_p
    | TOK_RANDOM ->
        _menhir_run26 _menhir_env (Obj.magic _menhir_stack) _menhir_env._menhir_lexbuf.Lexing.lex_curr_p MenhirState88 _menhir_env._menhir_lexbuf.Lexing.lex_start_p
    | TOK_TRUE ->
        _menhir_run25 _menhir_env (Obj.magic _menhir_stack) _menhir_env._menhir_lexbuf.Lexing.lex_curr_p MenhirState88 _menhir_env._menhir_lexbuf.Lexing.lex_start_p
    | TOK_URANDOM ->
        _menhir_run24 _menhir_env (Obj.magic _menhir_stack) _menhir_env._menhir_lexbuf.Lexing.lex_curr_p MenhirState88 _menhir_env._menhir_lexbuf.Lexing.lex_start_p
    | TOK_const _v ->
        _menhir_run20 _menhir_env (Obj.magic _menhir_stack) _menhir_env._menhir_lexbuf.Lexing.lex_curr_p MenhirState88 _v _menhir_env._menhir_lexbuf.Lexing.lex_start_p
    | TOK_id _v ->
        _menhir_run23 _menhir_env (Obj.magic _menhir_stack) _menhir_env._menhir_lexbuf.Lexing.lex_curr_p MenhirState88 _v _menhir_env._menhir_lexbuf.Lexing.lex_start_p
    | _ ->
        assert (not _menhir_env._menhir_error);
        _menhir_env._menhir_error <- true;
        _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) MenhirState88

and _menhir_run90 : _menhir_env -> 'ttv_tail * Lexing.position * _menhir_state * (IntermediateSyntax.exp IntermediateSyntax.annotated) * Lexing.position -> 'ttv_return =
  fun _menhir_env _menhir_stack ->
    let _menhir_env = _menhir_discard _menhir_env in
    let _tok = _menhir_env._menhir_token in
    match _tok with
    | TOK_FALSE ->
        _menhir_run43 _menhir_env (Obj.magic _menhir_stack) _menhir_env._menhir_lexbuf.Lexing.lex_curr_p MenhirState90 _menhir_env._menhir_lexbuf.Lexing.lex_start_p
    | TOK_LBRACKET ->
        _menhir_run35 _menhir_env (Obj.magic _menhir_stack) MenhirState90 _menhir_env._menhir_lexbuf.Lexing.lex_start_p
    | TOK_LPAREN ->
        _menhir_run34 _menhir_env (Obj.magic _menhir_stack) MenhirState90 _menhir_env._menhir_lexbuf.Lexing.lex_start_p
    | TOK_MINUS ->
        _menhir_run33 _menhir_env (Obj.magic _menhir_stack) MenhirState90 _menhir_env._menhir_lexbuf.Lexing.lex_start_p
    | TOK_MINUS_MINUS ->
        _menhir_run32 _menhir_env (Obj.magic _menhir_stack) _menhir_env._menhir_lexbuf.Lexing.lex_curr_p MenhirState90 _menhir_env._menhir_lexbuf.Lexing.lex_start_p
    | TOK_MULTIPLY ->
        _menhir_run30 _menhir_env (Obj.magic _menhir_stack) MenhirState90 _menhir_env._menhir_lexbuf.Lexing.lex_start_p
    | TOK_NOT ->
        _menhir_run29 _menhir_env (Obj.magic _menhir_stack) MenhirState90 _menhir_env._menhir_lexbuf.Lexing.lex_start_p
    | TOK_PLUS ->
        _menhir_run28 _menhir_env (Obj.magic _menhir_stack) MenhirState90 _menhir_env._menhir_lexbuf.Lexing.lex_start_p
    | TOK_PLUS_PLUS ->
        _menhir_run27 _menhir_env (Obj.magic _menhir_stack) _menhir_env._menhir_lexbuf.Lexing.lex_curr_p MenhirState90 _menhir_env._menhir_lexbuf.Lexing.lex_start_p
    | TOK_RANDOM ->
        _menhir_run26 _menhir_env (Obj.magic _menhir_stack) _menhir_env._menhir_lexbuf.Lexing.lex_curr_p MenhirState90 _menhir_env._menhir_lexbuf.Lexing.lex_start_p
    | TOK_TRUE ->
        _menhir_run25 _menhir_env (Obj.magic _menhir_stack) _menhir_env._menhir_lexbuf.Lexing.lex_curr_p MenhirState90 _menhir_env._menhir_lexbuf.Lexing.lex_start_p
    | TOK_URANDOM ->
        _menhir_run24 _menhir_env (Obj.magic _menhir_stack) _menhir_env._menhir_lexbuf.Lexing.lex_curr_p MenhirState90 _menhir_env._menhir_lexbuf.Lexing.lex_start_p
    | TOK_const _v ->
        _menhir_run20 _menhir_env (Obj.magic _menhir_stack) _menhir_env._menhir_lexbuf.Lexing.lex_curr_p MenhirState90 _v _menhir_env._menhir_lexbuf.Lexing.lex_start_p
    | TOK_id _v ->
        _menhir_run23 _menhir_env (Obj.magic _menhir_stack) _menhir_env._menhir_lexbuf.Lexing.lex_curr_p MenhirState90 _v _menhir_env._menhir_lexbuf.Lexing.lex_start_p
    | _ ->
        assert (not _menhir_env._menhir_error);
        _menhir_env._menhir_error <- true;
        _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) MenhirState90

and _menhir_run92 : _menhir_env -> 'ttv_tail * Lexing.position * _menhir_state * (IntermediateSyntax.exp IntermediateSyntax.annotated) * Lexing.position -> 'ttv_return =
  fun _menhir_env _menhir_stack ->
    let _menhir_env = _menhir_discard _menhir_env in
    let _tok = _menhir_env._menhir_token in
    match _tok with
    | TOK_FALSE ->
        _menhir_run43 _menhir_env (Obj.magic _menhir_stack) _menhir_env._menhir_lexbuf.Lexing.lex_curr_p MenhirState92 _menhir_env._menhir_lexbuf.Lexing.lex_start_p
    | TOK_LBRACKET ->
        _menhir_run35 _menhir_env (Obj.magic _menhir_stack) MenhirState92 _menhir_env._menhir_lexbuf.Lexing.lex_start_p
    | TOK_LPAREN ->
        _menhir_run34 _menhir_env (Obj.magic _menhir_stack) MenhirState92 _menhir_env._menhir_lexbuf.Lexing.lex_start_p
    | TOK_MINUS ->
        _menhir_run33 _menhir_env (Obj.magic _menhir_stack) MenhirState92 _menhir_env._menhir_lexbuf.Lexing.lex_start_p
    | TOK_MINUS_MINUS ->
        _menhir_run32 _menhir_env (Obj.magic _menhir_stack) _menhir_env._menhir_lexbuf.Lexing.lex_curr_p MenhirState92 _menhir_env._menhir_lexbuf.Lexing.lex_start_p
    | TOK_MULTIPLY ->
        _menhir_run30 _menhir_env (Obj.magic _menhir_stack) MenhirState92 _menhir_env._menhir_lexbuf.Lexing.lex_start_p
    | TOK_NOT ->
        _menhir_run29 _menhir_env (Obj.magic _menhir_stack) MenhirState92 _menhir_env._menhir_lexbuf.Lexing.lex_start_p
    | TOK_PLUS ->
        _menhir_run28 _menhir_env (Obj.magic _menhir_stack) MenhirState92 _menhir_env._menhir_lexbuf.Lexing.lex_start_p
    | TOK_PLUS_PLUS ->
        _menhir_run27 _menhir_env (Obj.magic _menhir_stack) _menhir_env._menhir_lexbuf.Lexing.lex_curr_p MenhirState92 _menhir_env._menhir_lexbuf.Lexing.lex_start_p
    | TOK_RANDOM ->
        _menhir_run26 _menhir_env (Obj.magic _menhir_stack) _menhir_env._menhir_lexbuf.Lexing.lex_curr_p MenhirState92 _menhir_env._menhir_lexbuf.Lexing.lex_start_p
    | TOK_TRUE ->
        _menhir_run25 _menhir_env (Obj.magic _menhir_stack) _menhir_env._menhir_lexbuf.Lexing.lex_curr_p MenhirState92 _menhir_env._menhir_lexbuf.Lexing.lex_start_p
    | TOK_URANDOM ->
        _menhir_run24 _menhir_env (Obj.magic _menhir_stack) _menhir_env._menhir_lexbuf.Lexing.lex_curr_p MenhirState92 _menhir_env._menhir_lexbuf.Lexing.lex_start_p
    | TOK_const _v ->
        _menhir_run20 _menhir_env (Obj.magic _menhir_stack) _menhir_env._menhir_lexbuf.Lexing.lex_curr_p MenhirState92 _v _menhir_env._menhir_lexbuf.Lexing.lex_start_p
    | TOK_id _v ->
        _menhir_run23 _menhir_env (Obj.magic _menhir_stack) _menhir_env._menhir_lexbuf.Lexing.lex_curr_p MenhirState92 _v _menhir_env._menhir_lexbuf.Lexing.lex_start_p
    | _ ->
        assert (not _menhir_env._menhir_error);
        _menhir_env._menhir_error <- true;
        _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) MenhirState92

and _menhir_reduce6 : _menhir_env -> 'ttv_tail * Lexing.position * _menhir_state * (IntermediateSyntax.exp) * Lexing.position -> 'ttv_return =
  fun _menhir_env _menhir_stack ->
    let (_menhir_stack, _endpos_x_, _menhir_s, (x : (IntermediateSyntax.exp)), _startpos_x_) = _menhir_stack in
    let _startpos = _startpos_x_ in
    let _endpos = _endpos_x_ in
    let _v : (IntermediateSyntax.exp IntermediateSyntax.annotated) = let _endpos = _endpos_x_ in
    let _startpos = _startpos_x_ in
    
# 236 "frontend/Parser.mly"
          ( x, (_startpos, _endpos) )
# 1382 "frontend/Parser.ml"
     in
    let _menhir_stack = (_menhir_stack, _endpos, _menhir_s, _v, _startpos) in
    match _menhir_s with
    | MenhirState98 ->
        let _menhir_stack = Obj.magic _menhir_stack in
        assert (not _menhir_env._menhir_error);
        let _tok = _menhir_env._menhir_token in
        (match _tok with
        | TOK_EQUAL_EQUAL ->
            _menhir_run106 _menhir_env (Obj.magic _menhir_stack)
        | TOK_NOT_EQUAL ->
            _menhir_run101 _menhir_env (Obj.magic _menhir_stack)
        | TOK_AND | TOK_CHAR | TOK_COMMA | TOK_CPP_DEFINE | TOK_EOF | TOK_FEAT | TOK_INT | TOK_OR | TOK_RPAREN | TOK_SEMICOLON | TOK_UINT | TOK_VOID | TOK_id _ ->
            let _menhir_stack = Obj.magic _menhir_stack in
            let ((_menhir_stack, _endpos_e1_, _menhir_s, (e1 : (IntermediateSyntax.exp IntermediateSyntax.annotated)), _startpos_e1_), _endpos_e2_, _, (e2 : (IntermediateSyntax.exp IntermediateSyntax.annotated)), _startpos_e2_) = _menhir_stack in
            let _2 = () in
            let _startpos = _startpos_e1_ in
            let _endpos = _endpos_e2_ in
            let _v : (IntermediateSyntax.exp) = 
# 182 "frontend/Parser.mly"
                                                                      ( I_and (e1,e2) )
# 1404 "frontend/Parser.ml"
             in
            _menhir_goto_logical_and_exp _menhir_env _menhir_stack _endpos _menhir_s _v _startpos
        | _ ->
            assert (not _menhir_env._menhir_error);
            _menhir_env._menhir_error <- true;
            let _menhir_stack = Obj.magic _menhir_stack in
            let (_menhir_stack, _, _menhir_s, _, _) = _menhir_stack in
            _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s)
    | MenhirState215 | MenhirState207 | MenhirState18 | MenhirState193 | MenhirState22 | MenhirState120 | MenhirState127 | MenhirState129 | MenhirState188 | MenhirState131 | MenhirState181 | MenhirState183 | MenhirState185 | MenhirState146 | MenhirState148 | MenhirState150 | MenhirState152 | MenhirState154 | MenhirState171 | MenhirState156 | MenhirState142 | MenhirState122 | MenhirState34 | MenhirState52 | MenhirState112 | MenhirState70 | MenhirState95 ->
        let _menhir_stack = Obj.magic _menhir_stack in
        assert (not _menhir_env._menhir_error);
        let _tok = _menhir_env._menhir_token in
        (match _tok with
        | TOK_EQUAL_EQUAL ->
            _menhir_run106 _menhir_env (Obj.magic _menhir_stack)
        | TOK_NOT_EQUAL ->
            _menhir_run101 _menhir_env (Obj.magic _menhir_stack)
        | _ ->
            assert (not _menhir_env._menhir_error);
            _menhir_env._menhir_error <- true;
            let _menhir_stack = Obj.magic _menhir_stack in
            let (_menhir_stack, _, _menhir_s, _, _) = _menhir_stack in
            _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s)
    | _ ->
        _menhir_fail ()

and _menhir_goto_logical_and_exp : _menhir_env -> 'ttv_tail -> Lexing.position -> _menhir_state -> (IntermediateSyntax.exp) -> Lexing.position -> 'ttv_return =
  fun _menhir_env _menhir_stack _endpos _menhir_s _v _startpos ->
    let _menhir_stack = (_menhir_stack, _endpos, _menhir_s, _v, _startpos) in
    match _menhir_s with
    | MenhirState215 | MenhirState207 | MenhirState193 | MenhirState18 | MenhirState120 | MenhirState188 | MenhirState129 | MenhirState185 | MenhirState183 | MenhirState181 | MenhirState150 | MenhirState171 | MenhirState154 | MenhirState156 | MenhirState152 | MenhirState148 | MenhirState146 | MenhirState142 | MenhirState131 | MenhirState127 | MenhirState122 | MenhirState22 | MenhirState34 | MenhirState112 | MenhirState70 | MenhirState52 ->
        let _menhir_stack = Obj.magic _menhir_stack in
        assert (not _menhir_env._menhir_error);
        let _tok = _menhir_env._menhir_token in
        (match _tok with
        | TOK_CHAR | TOK_COMMA | TOK_CPP_DEFINE | TOK_EOF | TOK_FEAT | TOK_INT | TOK_OR | TOK_RPAREN | TOK_SEMICOLON | TOK_UINT | TOK_VOID | TOK_id _ ->
            let _menhir_stack = Obj.magic _menhir_stack in
            let (_menhir_stack, _endpos_e_, _menhir_s, (e : (IntermediateSyntax.exp)), _startpos_e_) = _menhir_stack in
            let _startpos = _startpos_e_ in
            let _endpos = _endpos_e_ in
            let _v : (IntermediateSyntax.exp) = 
# 177 "frontend/Parser.mly"
                                   ( e )
# 1448 "frontend/Parser.ml"
             in
            _menhir_goto_logical_or_exp _menhir_env _menhir_stack _endpos _menhir_s _v _startpos
        | TOK_AND ->
            _menhir_reduce15 _menhir_env (Obj.magic _menhir_stack)
        | _ ->
            assert (not _menhir_env._menhir_error);
            _menhir_env._menhir_error <- true;
            let _menhir_stack = Obj.magic _menhir_stack in
            let (_menhir_stack, _, _menhir_s, _, _) = _menhir_stack in
            _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s)
    | MenhirState95 ->
        let _menhir_stack = Obj.magic _menhir_stack in
        _menhir_reduce15 _menhir_env (Obj.magic _menhir_stack)
    | _ ->
        _menhir_fail ()

and _menhir_reduce19 : _menhir_env -> 'ttv_tail * Lexing.position * _menhir_state * (IntermediateSyntax.exp) * Lexing.position -> 'ttv_return =
  fun _menhir_env _menhir_stack ->
    let (_menhir_stack, _endpos_x_, _menhir_s, (x : (IntermediateSyntax.exp)), _startpos_x_) = _menhir_stack in
    let _startpos = _startpos_x_ in
    let _endpos = _endpos_x_ in
    let _v : (IntermediateSyntax.exp IntermediateSyntax.annotated) = let _endpos = _endpos_x_ in
    let _startpos = _startpos_x_ in
    
# 236 "frontend/Parser.mly"
          ( x, (_startpos, _endpos) )
# 1475 "frontend/Parser.ml"
     in
    let _menhir_stack = (_menhir_stack, _endpos, _menhir_s, _v, _startpos) in
    match _menhir_s with
    | MenhirState215 | MenhirState207 | MenhirState18 | MenhirState193 | MenhirState120 | MenhirState129 | MenhirState188 | MenhirState185 | MenhirState183 | MenhirState181 | MenhirState150 | MenhirState154 | MenhirState171 | MenhirState156 | MenhirState152 | MenhirState148 | MenhirState146 | MenhirState142 | MenhirState131 | MenhirState127 | MenhirState122 | MenhirState22 | MenhirState34 | MenhirState112 | MenhirState52 | MenhirState98 | MenhirState95 | MenhirState70 ->
        let _menhir_stack = Obj.magic _menhir_stack in
        assert (not _menhir_env._menhir_error);
        let _tok = _menhir_env._menhir_token in
        (match _tok with
        | TOK_GREATER ->
            _menhir_run92 _menhir_env (Obj.magic _menhir_stack)
        | TOK_GREATER_EQUAL ->
            _menhir_run90 _menhir_env (Obj.magic _menhir_stack)
        | TOK_LESS ->
            _menhir_run88 _menhir_env (Obj.magic _menhir_stack)
        | TOK_LESS_EQUAL ->
            _menhir_run72 _menhir_env (Obj.magic _menhir_stack)
        | _ ->
            assert (not _menhir_env._menhir_error);
            _menhir_env._menhir_error <- true;
            let _menhir_stack = Obj.magic _menhir_stack in
            let (_menhir_stack, _, _menhir_s, _, _) = _menhir_stack in
            _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s)
    | MenhirState101 ->
        let _menhir_stack = Obj.magic _menhir_stack in
        assert (not _menhir_env._menhir_error);
        let _tok = _menhir_env._menhir_token in
        (match _tok with
        | TOK_GREATER ->
            _menhir_run92 _menhir_env (Obj.magic _menhir_stack)
        | TOK_GREATER_EQUAL ->
            _menhir_run90 _menhir_env (Obj.magic _menhir_stack)
        | TOK_LESS ->
            _menhir_run88 _menhir_env (Obj.magic _menhir_stack)
        | TOK_LESS_EQUAL ->
            _menhir_run72 _menhir_env (Obj.magic _menhir_stack)
        | TOK_AND | TOK_CHAR | TOK_COMMA | TOK_CPP_DEFINE | TOK_EOF | TOK_EQUAL_EQUAL | TOK_FEAT | TOK_INT | TOK_NOT_EQUAL | TOK_OR | TOK_RPAREN | TOK_SEMICOLON | TOK_UINT | TOK_VOID | TOK_id _ ->
            let _menhir_stack = Obj.magic _menhir_stack in
            let ((_menhir_stack, _endpos_e1_, _menhir_s, (e1 : (IntermediateSyntax.exp IntermediateSyntax.annotated)), _startpos_e1_), _endpos_e2_, _, (e2 : (IntermediateSyntax.exp IntermediateSyntax.annotated)), _startpos_e2_) = _menhir_stack in
            let _2 = () in
            let _startpos = _startpos_e1_ in
            let _endpos = _endpos_e2_ in
            let _v : (IntermediateSyntax.exp) = 
# 187 "frontend/Parser.mly"
                                                                            ( I_neq (e1,e2) )
# 1520 "frontend/Parser.ml"
             in
            _menhir_goto_equality_exp _menhir_env _menhir_stack _endpos _menhir_s _v _startpos
        | _ ->
            assert (not _menhir_env._menhir_error);
            _menhir_env._menhir_error <- true;
            let _menhir_stack = Obj.magic _menhir_stack in
            let (_menhir_stack, _, _menhir_s, _, _) = _menhir_stack in
            _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s)
    | MenhirState106 ->
        let _menhir_stack = Obj.magic _menhir_stack in
        assert (not _menhir_env._menhir_error);
        let _tok = _menhir_env._menhir_token in
        (match _tok with
        | TOK_GREATER ->
            _menhir_run92 _menhir_env (Obj.magic _menhir_stack)
        | TOK_GREATER_EQUAL ->
            _menhir_run90 _menhir_env (Obj.magic _menhir_stack)
        | TOK_LESS ->
            _menhir_run88 _menhir_env (Obj.magic _menhir_stack)
        | TOK_LESS_EQUAL ->
            _menhir_run72 _menhir_env (Obj.magic _menhir_stack)
        | TOK_AND | TOK_CHAR | TOK_COMMA | TOK_CPP_DEFINE | TOK_EOF | TOK_EQUAL_EQUAL | TOK_FEAT | TOK_INT | TOK_NOT_EQUAL | TOK_OR | TOK_RPAREN | TOK_SEMICOLON | TOK_UINT | TOK_VOID | TOK_id _ ->
            let _menhir_stack = Obj.magic _menhir_stack in
            let ((_menhir_stack, _endpos_e1_, _menhir_s, (e1 : (IntermediateSyntax.exp IntermediateSyntax.annotated)), _startpos_e1_), _endpos_e2_, _, (e2 : (IntermediateSyntax.exp IntermediateSyntax.annotated)), _startpos_e2_) = _menhir_stack in
            let _2 = () in
            let _startpos = _startpos_e1_ in
            let _endpos = _endpos_e2_ in
            let _v : (IntermediateSyntax.exp) = 
# 186 "frontend/Parser.mly"
                                                                              ( I_eq (e1,e2) )
# 1551 "frontend/Parser.ml"
             in
            _menhir_goto_equality_exp _menhir_env _menhir_stack _endpos _menhir_s _v _startpos
        | _ ->
            assert (not _menhir_env._menhir_error);
            _menhir_env._menhir_error <- true;
            let _menhir_stack = Obj.magic _menhir_stack in
            let (_menhir_stack, _, _menhir_s, _, _) = _menhir_stack in
            _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s)
    | _ ->
        _menhir_fail ()

and _menhir_goto_equality_exp : _menhir_env -> 'ttv_tail -> Lexing.position -> _menhir_state -> (IntermediateSyntax.exp) -> Lexing.position -> 'ttv_return =
  fun _menhir_env _menhir_stack _endpos _menhir_s _v _startpos ->
    let _menhir_stack = (_menhir_stack, _endpos, _menhir_s, _v, _startpos) in
    match _menhir_s with
    | MenhirState215 | MenhirState207 | MenhirState193 | MenhirState18 | MenhirState120 | MenhirState188 | MenhirState129 | MenhirState185 | MenhirState183 | MenhirState181 | MenhirState150 | MenhirState171 | MenhirState154 | MenhirState156 | MenhirState152 | MenhirState148 | MenhirState146 | MenhirState142 | MenhirState131 | MenhirState127 | MenhirState122 | MenhirState22 | MenhirState34 | MenhirState112 | MenhirState95 | MenhirState70 | MenhirState52 ->
        let _menhir_stack = Obj.magic _menhir_stack in
        assert (not _menhir_env._menhir_error);
        let _tok = _menhir_env._menhir_token in
        (match _tok with
        | TOK_AND | TOK_CHAR | TOK_COMMA | TOK_CPP_DEFINE | TOK_EOF | TOK_FEAT | TOK_INT | TOK_OR | TOK_RPAREN | TOK_SEMICOLON | TOK_UINT | TOK_VOID | TOK_id _ ->
            let _menhir_stack = Obj.magic _menhir_stack in
            let (_menhir_stack, _endpos_e_, _menhir_s, (e : (IntermediateSyntax.exp)), _startpos_e_) = _menhir_stack in
            let _startpos = _startpos_e_ in
            let _endpos = _endpos_e_ in
            let _v : (IntermediateSyntax.exp) = 
# 181 "frontend/Parser.mly"
                                 ( e )
# 1580 "frontend/Parser.ml"
             in
            _menhir_goto_logical_and_exp _menhir_env _menhir_stack _endpos _menhir_s _v _startpos
        | TOK_EQUAL_EQUAL | TOK_NOT_EQUAL ->
            _menhir_reduce6 _menhir_env (Obj.magic _menhir_stack)
        | _ ->
            assert (not _menhir_env._menhir_error);
            _menhir_env._menhir_error <- true;
            let _menhir_stack = Obj.magic _menhir_stack in
            let (_menhir_stack, _, _menhir_s, _, _) = _menhir_stack in
            _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s)
    | MenhirState98 ->
        let _menhir_stack = Obj.magic _menhir_stack in
        _menhir_reduce6 _menhir_env (Obj.magic _menhir_stack)
    | _ ->
        _menhir_fail ()

and _menhir_run82 : _menhir_env -> 'ttv_tail * Lexing.position * _menhir_state * (IntermediateSyntax.exp IntermediateSyntax.annotated) * Lexing.position -> Lexing.position -> 'ttv_return =
  fun _menhir_env _menhir_stack _startpos ->
    let _menhir_stack = (_menhir_stack, _startpos) in
    let _menhir_env = _menhir_discard _menhir_env in
    let _tok = _menhir_env._menhir_token in
    match _tok with
    | TOK_FALSE ->
        _menhir_run43 _menhir_env (Obj.magic _menhir_stack) _menhir_env._menhir_lexbuf.Lexing.lex_curr_p MenhirState82 _menhir_env._menhir_lexbuf.Lexing.lex_start_p
    | TOK_LBRACKET ->
        _menhir_run35 _menhir_env (Obj.magic _menhir_stack) MenhirState82 _menhir_env._menhir_lexbuf.Lexing.lex_start_p
    | TOK_LPAREN ->
        _menhir_run34 _menhir_env (Obj.magic _menhir_stack) MenhirState82 _menhir_env._menhir_lexbuf.Lexing.lex_start_p
    | TOK_MINUS ->
        _menhir_run33 _menhir_env (Obj.magic _menhir_stack) MenhirState82 _menhir_env._menhir_lexbuf.Lexing.lex_start_p
    | TOK_MINUS_MINUS ->
        _menhir_run32 _menhir_env (Obj.magic _menhir_stack) _menhir_env._menhir_lexbuf.Lexing.lex_curr_p MenhirState82 _menhir_env._menhir_lexbuf.Lexing.lex_start_p
    | TOK_MULTIPLY ->
        _menhir_run30 _menhir_env (Obj.magic _menhir_stack) MenhirState82 _menhir_env._menhir_lexbuf.Lexing.lex_start_p
    | TOK_NOT ->
        _menhir_run29 _menhir_env (Obj.magic _menhir_stack) MenhirState82 _menhir_env._menhir_lexbuf.Lexing.lex_start_p
    | TOK_PLUS ->
        _menhir_run28 _menhir_env (Obj.magic _menhir_stack) MenhirState82 _menhir_env._menhir_lexbuf.Lexing.lex_start_p
    | TOK_PLUS_PLUS ->
        _menhir_run27 _menhir_env (Obj.magic _menhir_stack) _menhir_env._menhir_lexbuf.Lexing.lex_curr_p MenhirState82 _menhir_env._menhir_lexbuf.Lexing.lex_start_p
    | TOK_RANDOM ->
        _menhir_run26 _menhir_env (Obj.magic _menhir_stack) _menhir_env._menhir_lexbuf.Lexing.lex_curr_p MenhirState82 _menhir_env._menhir_lexbuf.Lexing.lex_start_p
    | TOK_TRUE ->
        _menhir_run25 _menhir_env (Obj.magic _menhir_stack) _menhir_env._menhir_lexbuf.Lexing.lex_curr_p MenhirState82 _menhir_env._menhir_lexbuf.Lexing.lex_start_p
    | TOK_URANDOM ->
        _menhir_run24 _menhir_env (Obj.magic _menhir_stack) _menhir_env._menhir_lexbuf.Lexing.lex_curr_p MenhirState82 _menhir_env._menhir_lexbuf.Lexing.lex_start_p
    | TOK_const _v ->
        _menhir_run20 _menhir_env (Obj.magic _menhir_stack) _menhir_env._menhir_lexbuf.Lexing.lex_curr_p MenhirState82 _v _menhir_env._menhir_lexbuf.Lexing.lex_start_p
    | TOK_id _v ->
        _menhir_run23 _menhir_env (Obj.magic _menhir_stack) _menhir_env._menhir_lexbuf.Lexing.lex_curr_p MenhirState82 _v _menhir_env._menhir_lexbuf.Lexing.lex_start_p
    | _ ->
        assert (not _menhir_env._menhir_error);
        _menhir_env._menhir_error <- true;
        _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) MenhirState82

and _menhir_run85 : _menhir_env -> 'ttv_tail * Lexing.position * _menhir_state * (IntermediateSyntax.exp IntermediateSyntax.annotated) * Lexing.position -> Lexing.position -> 'ttv_return =
  fun _menhir_env _menhir_stack _startpos ->
    let _menhir_stack = (_menhir_stack, _startpos) in
    let _menhir_env = _menhir_discard _menhir_env in
    let _tok = _menhir_env._menhir_token in
    match _tok with
    | TOK_FALSE ->
        _menhir_run43 _menhir_env (Obj.magic _menhir_stack) _menhir_env._menhir_lexbuf.Lexing.lex_curr_p MenhirState85 _menhir_env._menhir_lexbuf.Lexing.lex_start_p
    | TOK_LBRACKET ->
        _menhir_run35 _menhir_env (Obj.magic _menhir_stack) MenhirState85 _menhir_env._menhir_lexbuf.Lexing.lex_start_p
    | TOK_LPAREN ->
        _menhir_run34 _menhir_env (Obj.magic _menhir_stack) MenhirState85 _menhir_env._menhir_lexbuf.Lexing.lex_start_p
    | TOK_MINUS ->
        _menhir_run33 _menhir_env (Obj.magic _menhir_stack) MenhirState85 _menhir_env._menhir_lexbuf.Lexing.lex_start_p
    | TOK_MINUS_MINUS ->
        _menhir_run32 _menhir_env (Obj.magic _menhir_stack) _menhir_env._menhir_lexbuf.Lexing.lex_curr_p MenhirState85 _menhir_env._menhir_lexbuf.Lexing.lex_start_p
    | TOK_MULTIPLY ->
        _menhir_run30 _menhir_env (Obj.magic _menhir_stack) MenhirState85 _menhir_env._menhir_lexbuf.Lexing.lex_start_p
    | TOK_NOT ->
        _menhir_run29 _menhir_env (Obj.magic _menhir_stack) MenhirState85 _menhir_env._menhir_lexbuf.Lexing.lex_start_p
    | TOK_PLUS ->
        _menhir_run28 _menhir_env (Obj.magic _menhir_stack) MenhirState85 _menhir_env._menhir_lexbuf.Lexing.lex_start_p
    | TOK_PLUS_PLUS ->
        _menhir_run27 _menhir_env (Obj.magic _menhir_stack) _menhir_env._menhir_lexbuf.Lexing.lex_curr_p MenhirState85 _menhir_env._menhir_lexbuf.Lexing.lex_start_p
    | TOK_RANDOM ->
        _menhir_run26 _menhir_env (Obj.magic _menhir_stack) _menhir_env._menhir_lexbuf.Lexing.lex_curr_p MenhirState85 _menhir_env._menhir_lexbuf.Lexing.lex_start_p
    | TOK_TRUE ->
        _menhir_run25 _menhir_env (Obj.magic _menhir_stack) _menhir_env._menhir_lexbuf.Lexing.lex_curr_p MenhirState85 _menhir_env._menhir_lexbuf.Lexing.lex_start_p
    | TOK_URANDOM ->
        _menhir_run24 _menhir_env (Obj.magic _menhir_stack) _menhir_env._menhir_lexbuf.Lexing.lex_curr_p MenhirState85 _menhir_env._menhir_lexbuf.Lexing.lex_start_p
    | TOK_const _v ->
        _menhir_run20 _menhir_env (Obj.magic _menhir_stack) _menhir_env._menhir_lexbuf.Lexing.lex_curr_p MenhirState85 _v _menhir_env._menhir_lexbuf.Lexing.lex_start_p
    | TOK_id _v ->
        _menhir_run23 _menhir_env (Obj.magic _menhir_stack) _menhir_env._menhir_lexbuf.Lexing.lex_curr_p MenhirState85 _v _menhir_env._menhir_lexbuf.Lexing.lex_start_p
    | _ ->
        assert (not _menhir_env._menhir_error);
        _menhir_env._menhir_error <- true;
        _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) MenhirState85

and _menhir_goto_relational_exp : _menhir_env -> 'ttv_tail -> Lexing.position -> _menhir_state -> (IntermediateSyntax.exp) -> Lexing.position -> 'ttv_return =
  fun _menhir_env _menhir_stack _endpos _menhir_s _v _startpos ->
    let _menhir_stack = (_menhir_stack, _endpos, _menhir_s, _v, _startpos) in
    match _menhir_s with
    | MenhirState215 | MenhirState207 | MenhirState193 | MenhirState18 | MenhirState120 | MenhirState188 | MenhirState129 | MenhirState185 | MenhirState183 | MenhirState181 | MenhirState150 | MenhirState171 | MenhirState154 | MenhirState156 | MenhirState152 | MenhirState148 | MenhirState146 | MenhirState142 | MenhirState131 | MenhirState127 | MenhirState122 | MenhirState22 | MenhirState34 | MenhirState112 | MenhirState98 | MenhirState95 | MenhirState70 | MenhirState52 ->
        let _menhir_stack = Obj.magic _menhir_stack in
        assert (not _menhir_env._menhir_error);
        let _tok = _menhir_env._menhir_token in
        (match _tok with
        | TOK_AND | TOK_CHAR | TOK_COMMA | TOK_CPP_DEFINE | TOK_EOF | TOK_EQUAL_EQUAL | TOK_FEAT | TOK_INT | TOK_NOT_EQUAL | TOK_OR | TOK_RPAREN | TOK_SEMICOLON | TOK_UINT | TOK_VOID | TOK_id _ ->
            let _menhir_stack = Obj.magic _menhir_stack in
            let (_menhir_stack, _endpos_e_, _menhir_s, (e : (IntermediateSyntax.exp)), _startpos_e_) = _menhir_stack in
            let _startpos = _startpos_e_ in
            let _endpos = _endpos_e_ in
            let _v : (IntermediateSyntax.exp) = 
# 185 "frontend/Parser.mly"
                                    ( e )
# 1692 "frontend/Parser.ml"
             in
            _menhir_goto_equality_exp _menhir_env _menhir_stack _endpos _menhir_s _v _startpos
        | TOK_GREATER | TOK_GREATER_EQUAL | TOK_LESS | TOK_LESS_EQUAL ->
            _menhir_reduce19 _menhir_env (Obj.magic _menhir_stack)
        | _ ->
            assert (not _menhir_env._menhir_error);
            _menhir_env._menhir_error <- true;
            let _menhir_stack = Obj.magic _menhir_stack in
            let (_menhir_stack, _, _menhir_s, _, _) = _menhir_stack in
            _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s)
    | MenhirState106 | MenhirState101 ->
        let _menhir_stack = Obj.magic _menhir_stack in
        _menhir_reduce19 _menhir_env (Obj.magic _menhir_stack)
    | _ ->
        _menhir_fail ()

and _menhir_reduce5 : _menhir_env -> 'ttv_tail * Lexing.position * _menhir_state * (IntermediateSyntax.exp) * Lexing.position -> 'ttv_return =
  fun _menhir_env _menhir_stack ->
    let (_menhir_stack, _endpos_x_, _menhir_s, (x : (IntermediateSyntax.exp)), _startpos_x_) = _menhir_stack in
    let _startpos = _startpos_x_ in
    let _endpos = _endpos_x_ in
    let _v : (IntermediateSyntax.exp IntermediateSyntax.annotated) = let _endpos = _endpos_x_ in
    let _startpos = _startpos_x_ in
    
# 236 "frontend/Parser.mly"
          ( x, (_startpos, _endpos) )
# 1719 "frontend/Parser.ml"
     in
    let _menhir_stack = (_menhir_stack, _endpos, _menhir_s, _v, _startpos) in
    match _menhir_s with
    | MenhirState72 ->
        let _menhir_stack = Obj.magic _menhir_stack in
        assert (not _menhir_env._menhir_error);
        let _tok = _menhir_env._menhir_token in
        (match _tok with
        | TOK_MINUS ->
            _menhir_run85 _menhir_env (Obj.magic _menhir_stack) _menhir_env._menhir_lexbuf.Lexing.lex_start_p
        | TOK_PLUS ->
            _menhir_run82 _menhir_env (Obj.magic _menhir_stack) _menhir_env._menhir_lexbuf.Lexing.lex_start_p
        | TOK_AND | TOK_CHAR | TOK_COMMA | TOK_CPP_DEFINE | TOK_EOF | TOK_EQUAL_EQUAL | TOK_FEAT | TOK_GREATER | TOK_GREATER_EQUAL | TOK_INT | TOK_LESS | TOK_LESS_EQUAL | TOK_NOT_EQUAL | TOK_OR | TOK_RPAREN | TOK_SEMICOLON | TOK_UINT | TOK_VOID | TOK_id _ ->
            let _menhir_stack = Obj.magic _menhir_stack in
            let ((_menhir_stack, _endpos_e1_, _menhir_s, (e1 : (IntermediateSyntax.exp IntermediateSyntax.annotated)), _startpos_e1_), _endpos_e2_, _, (e2 : (IntermediateSyntax.exp IntermediateSyntax.annotated)), _startpos_e2_) = _menhir_stack in
            let _2 = () in
            let _startpos = _startpos_e1_ in
            let _endpos = _endpos_e2_ in
            let _v : (IntermediateSyntax.exp) = 
# 192 "frontend/Parser.mly"
                                                                        ( I_leq (e1,e2) )
# 1741 "frontend/Parser.ml"
             in
            _menhir_goto_relational_exp _menhir_env _menhir_stack _endpos _menhir_s _v _startpos
        | _ ->
            assert (not _menhir_env._menhir_error);
            _menhir_env._menhir_error <- true;
            let _menhir_stack = Obj.magic _menhir_stack in
            let (_menhir_stack, _, _menhir_s, _, _) = _menhir_stack in
            _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s)
    | MenhirState88 ->
        let _menhir_stack = Obj.magic _menhir_stack in
        assert (not _menhir_env._menhir_error);
        let _tok = _menhir_env._menhir_token in
        (match _tok with
        | TOK_MINUS ->
            _menhir_run85 _menhir_env (Obj.magic _menhir_stack) _menhir_env._menhir_lexbuf.Lexing.lex_start_p
        | TOK_PLUS ->
            _menhir_run82 _menhir_env (Obj.magic _menhir_stack) _menhir_env._menhir_lexbuf.Lexing.lex_start_p
        | TOK_AND | TOK_CHAR | TOK_COMMA | TOK_CPP_DEFINE | TOK_EOF | TOK_EQUAL_EQUAL | TOK_FEAT | TOK_GREATER | TOK_GREATER_EQUAL | TOK_INT | TOK_LESS | TOK_LESS_EQUAL | TOK_NOT_EQUAL | TOK_OR | TOK_RPAREN | TOK_SEMICOLON | TOK_UINT | TOK_VOID | TOK_id _ ->
            let _menhir_stack = Obj.magic _menhir_stack in
            let ((_menhir_stack, _endpos_e1_, _menhir_s, (e1 : (IntermediateSyntax.exp IntermediateSyntax.annotated)), _startpos_e1_), _endpos_e2_, _, (e2 : (IntermediateSyntax.exp IntermediateSyntax.annotated)), _startpos_e2_) = _menhir_stack in
            let _2 = () in
            let _startpos = _startpos_e1_ in
            let _endpos = _endpos_e2_ in
            let _v : (IntermediateSyntax.exp) = 
# 191 "frontend/Parser.mly"
                                                                    ( I_less (e1,e2) )
# 1768 "frontend/Parser.ml"
             in
            _menhir_goto_relational_exp _menhir_env _menhir_stack _endpos _menhir_s _v _startpos
        | _ ->
            assert (not _menhir_env._menhir_error);
            _menhir_env._menhir_error <- true;
            let _menhir_stack = Obj.magic _menhir_stack in
            let (_menhir_stack, _, _menhir_s, _, _) = _menhir_stack in
            _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s)
    | MenhirState90 ->
        let _menhir_stack = Obj.magic _menhir_stack in
        assert (not _menhir_env._menhir_error);
        let _tok = _menhir_env._menhir_token in
        (match _tok with
        | TOK_MINUS ->
            _menhir_run85 _menhir_env (Obj.magic _menhir_stack) _menhir_env._menhir_lexbuf.Lexing.lex_start_p
        | TOK_PLUS ->
            _menhir_run82 _menhir_env (Obj.magic _menhir_stack) _menhir_env._menhir_lexbuf.Lexing.lex_start_p
        | TOK_AND | TOK_CHAR | TOK_COMMA | TOK_CPP_DEFINE | TOK_EOF | TOK_EQUAL_EQUAL | TOK_FEAT | TOK_GREATER | TOK_GREATER_EQUAL | TOK_INT | TOK_LESS | TOK_LESS_EQUAL | TOK_NOT_EQUAL | TOK_OR | TOK_RPAREN | TOK_SEMICOLON | TOK_UINT | TOK_VOID | TOK_id _ ->
            let _menhir_stack = Obj.magic _menhir_stack in
            let ((_menhir_stack, _endpos_e1_, _menhir_s, (e1 : (IntermediateSyntax.exp IntermediateSyntax.annotated)), _startpos_e1_), _endpos_e2_, _, (e2 : (IntermediateSyntax.exp IntermediateSyntax.annotated)), _startpos_e2_) = _menhir_stack in
            let _2 = () in
            let _startpos = _startpos_e1_ in
            let _endpos = _endpos_e2_ in
            let _v : (IntermediateSyntax.exp) = 
# 194 "frontend/Parser.mly"
                                                                          ( I_geq (e1,e2) )
# 1795 "frontend/Parser.ml"
             in
            _menhir_goto_relational_exp _menhir_env _menhir_stack _endpos _menhir_s _v _startpos
        | _ ->
            assert (not _menhir_env._menhir_error);
            _menhir_env._menhir_error <- true;
            let _menhir_stack = Obj.magic _menhir_stack in
            let (_menhir_stack, _, _menhir_s, _, _) = _menhir_stack in
            _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s)
    | MenhirState92 ->
        let _menhir_stack = Obj.magic _menhir_stack in
        assert (not _menhir_env._menhir_error);
        let _tok = _menhir_env._menhir_token in
        (match _tok with
        | TOK_MINUS ->
            _menhir_run85 _menhir_env (Obj.magic _menhir_stack) _menhir_env._menhir_lexbuf.Lexing.lex_start_p
        | TOK_PLUS ->
            _menhir_run82 _menhir_env (Obj.magic _menhir_stack) _menhir_env._menhir_lexbuf.Lexing.lex_start_p
        | TOK_AND | TOK_CHAR | TOK_COMMA | TOK_CPP_DEFINE | TOK_EOF | TOK_EQUAL_EQUAL | TOK_FEAT | TOK_GREATER | TOK_GREATER_EQUAL | TOK_INT | TOK_LESS | TOK_LESS_EQUAL | TOK_NOT_EQUAL | TOK_OR | TOK_RPAREN | TOK_SEMICOLON | TOK_UINT | TOK_VOID | TOK_id _ ->
            let _menhir_stack = Obj.magic _menhir_stack in
            let ((_menhir_stack, _endpos_e1_, _menhir_s, (e1 : (IntermediateSyntax.exp IntermediateSyntax.annotated)), _startpos_e1_), _endpos_e2_, _, (e2 : (IntermediateSyntax.exp IntermediateSyntax.annotated)), _startpos_e2_) = _menhir_stack in
            let _2 = () in
            let _startpos = _startpos_e1_ in
            let _endpos = _endpos_e2_ in
            let _v : (IntermediateSyntax.exp) = 
# 193 "frontend/Parser.mly"
                                                                      ( I_greater (e1,e2) )
# 1822 "frontend/Parser.ml"
             in
            _menhir_goto_relational_exp _menhir_env _menhir_stack _endpos _menhir_s _v _startpos
        | _ ->
            assert (not _menhir_env._menhir_error);
            _menhir_env._menhir_error <- true;
            let _menhir_stack = Obj.magic _menhir_stack in
            let (_menhir_stack, _, _menhir_s, _, _) = _menhir_stack in
            _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s)
    | MenhirState215 | MenhirState207 | MenhirState18 | MenhirState193 | MenhirState22 | MenhirState120 | MenhirState127 | MenhirState129 | MenhirState188 | MenhirState131 | MenhirState181 | MenhirState183 | MenhirState185 | MenhirState146 | MenhirState148 | MenhirState150 | MenhirState152 | MenhirState154 | MenhirState171 | MenhirState156 | MenhirState142 | MenhirState122 | MenhirState34 | MenhirState52 | MenhirState112 | MenhirState70 | MenhirState95 | MenhirState98 | MenhirState106 | MenhirState101 ->
        let _menhir_stack = Obj.magic _menhir_stack in
        assert (not _menhir_env._menhir_error);
        let _tok = _menhir_env._menhir_token in
        (match _tok with
        | TOK_MINUS ->
            _menhir_run85 _menhir_env (Obj.magic _menhir_stack) _menhir_env._menhir_lexbuf.Lexing.lex_start_p
        | TOK_PLUS ->
            _menhir_run82 _menhir_env (Obj.magic _menhir_stack) _menhir_env._menhir_lexbuf.Lexing.lex_start_p
        | _ ->
            assert (not _menhir_env._menhir_error);
            _menhir_env._menhir_error <- true;
            let _menhir_stack = Obj.magic _menhir_stack in
            let (_menhir_stack, _, _menhir_s, _, _) = _menhir_stack in
            _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s)
    | _ ->
        _menhir_fail ()

and _menhir_run75 : _menhir_env -> 'ttv_tail * Lexing.position * _menhir_state * (IntermediateSyntax.exp IntermediateSyntax.annotated) * Lexing.position -> Lexing.position -> 'ttv_return =
  fun _menhir_env _menhir_stack _startpos ->
    let _menhir_stack = (_menhir_stack, _startpos) in
    let _menhir_env = _menhir_discard _menhir_env in
    let _tok = _menhir_env._menhir_token in
    match _tok with
    | TOK_FALSE ->
        _menhir_run43 _menhir_env (Obj.magic _menhir_stack) _menhir_env._menhir_lexbuf.Lexing.lex_curr_p MenhirState75 _menhir_env._menhir_lexbuf.Lexing.lex_start_p
    | TOK_LBRACKET ->
        _menhir_run35 _menhir_env (Obj.magic _menhir_stack) MenhirState75 _menhir_env._menhir_lexbuf.Lexing.lex_start_p
    | TOK_LPAREN ->
        _menhir_run34 _menhir_env (Obj.magic _menhir_stack) MenhirState75 _menhir_env._menhir_lexbuf.Lexing.lex_start_p
    | TOK_MINUS ->
        _menhir_run33 _menhir_env (Obj.magic _menhir_stack) MenhirState75 _menhir_env._menhir_lexbuf.Lexing.lex_start_p
    | TOK_MINUS_MINUS ->
        _menhir_run32 _menhir_env (Obj.magic _menhir_stack) _menhir_env._menhir_lexbuf.Lexing.lex_curr_p MenhirState75 _menhir_env._menhir_lexbuf.Lexing.lex_start_p
    | TOK_MULTIPLY ->
        _menhir_run30 _menhir_env (Obj.magic _menhir_stack) MenhirState75 _menhir_env._menhir_lexbuf.Lexing.lex_start_p
    | TOK_NOT ->
        _menhir_run29 _menhir_env (Obj.magic _menhir_stack) MenhirState75 _menhir_env._menhir_lexbuf.Lexing.lex_start_p
    | TOK_PLUS ->
        _menhir_run28 _menhir_env (Obj.magic _menhir_stack) MenhirState75 _menhir_env._menhir_lexbuf.Lexing.lex_start_p
    | TOK_PLUS_PLUS ->
        _menhir_run27 _menhir_env (Obj.magic _menhir_stack) _menhir_env._menhir_lexbuf.Lexing.lex_curr_p MenhirState75 _menhir_env._menhir_lexbuf.Lexing.lex_start_p
    | TOK_RANDOM ->
        _menhir_run26 _menhir_env (Obj.magic _menhir_stack) _menhir_env._menhir_lexbuf.Lexing.lex_curr_p MenhirState75 _menhir_env._menhir_lexbuf.Lexing.lex_start_p
    | TOK_TRUE ->
        _menhir_run25 _menhir_env (Obj.magic _menhir_stack) _menhir_env._menhir_lexbuf.Lexing.lex_curr_p MenhirState75 _menhir_env._menhir_lexbuf.Lexing.lex_start_p
    | TOK_URANDOM ->
        _menhir_run24 _menhir_env (Obj.magic _menhir_stack) _menhir_env._menhir_lexbuf.Lexing.lex_curr_p MenhirState75 _menhir_env._menhir_lexbuf.Lexing.lex_start_p
    | TOK_const _v ->
        _menhir_run20 _menhir_env (Obj.magic _menhir_stack) _menhir_env._menhir_lexbuf.Lexing.lex_curr_p MenhirState75 _v _menhir_env._menhir_lexbuf.Lexing.lex_start_p
    | TOK_id _v ->
        _menhir_run23 _menhir_env (Obj.magic _menhir_stack) _menhir_env._menhir_lexbuf.Lexing.lex_curr_p MenhirState75 _v _menhir_env._menhir_lexbuf.Lexing.lex_start_p
    | _ ->
        assert (not _menhir_env._menhir_error);
        _menhir_env._menhir_error <- true;
        _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) MenhirState75

and _menhir_run77 : _menhir_env -> 'ttv_tail * Lexing.position * _menhir_state * (IntermediateSyntax.exp IntermediateSyntax.annotated) * Lexing.position -> 'ttv_return =
  fun _menhir_env _menhir_stack ->
    let _menhir_env = _menhir_discard _menhir_env in
    let _tok = _menhir_env._menhir_token in
    match _tok with
    | TOK_FALSE ->
        _menhir_run43 _menhir_env (Obj.magic _menhir_stack) _menhir_env._menhir_lexbuf.Lexing.lex_curr_p MenhirState77 _menhir_env._menhir_lexbuf.Lexing.lex_start_p
    | TOK_LBRACKET ->
        _menhir_run35 _menhir_env (Obj.magic _menhir_stack) MenhirState77 _menhir_env._menhir_lexbuf.Lexing.lex_start_p
    | TOK_LPAREN ->
        _menhir_run34 _menhir_env (Obj.magic _menhir_stack) MenhirState77 _menhir_env._menhir_lexbuf.Lexing.lex_start_p
    | TOK_MINUS ->
        _menhir_run33 _menhir_env (Obj.magic _menhir_stack) MenhirState77 _menhir_env._menhir_lexbuf.Lexing.lex_start_p
    | TOK_MINUS_MINUS ->
        _menhir_run32 _menhir_env (Obj.magic _menhir_stack) _menhir_env._menhir_lexbuf.Lexing.lex_curr_p MenhirState77 _menhir_env._menhir_lexbuf.Lexing.lex_start_p
    | TOK_MULTIPLY ->
        _menhir_run30 _menhir_env (Obj.magic _menhir_stack) MenhirState77 _menhir_env._menhir_lexbuf.Lexing.lex_start_p
    | TOK_NOT ->
        _menhir_run29 _menhir_env (Obj.magic _menhir_stack) MenhirState77 _menhir_env._menhir_lexbuf.Lexing.lex_start_p
    | TOK_PLUS ->
        _menhir_run28 _menhir_env (Obj.magic _menhir_stack) MenhirState77 _menhir_env._menhir_lexbuf.Lexing.lex_start_p
    | TOK_PLUS_PLUS ->
        _menhir_run27 _menhir_env (Obj.magic _menhir_stack) _menhir_env._menhir_lexbuf.Lexing.lex_curr_p MenhirState77 _menhir_env._menhir_lexbuf.Lexing.lex_start_p
    | TOK_RANDOM ->
        _menhir_run26 _menhir_env (Obj.magic _menhir_stack) _menhir_env._menhir_lexbuf.Lexing.lex_curr_p MenhirState77 _menhir_env._menhir_lexbuf.Lexing.lex_start_p
    | TOK_TRUE ->
        _menhir_run25 _menhir_env (Obj.magic _menhir_stack) _menhir_env._menhir_lexbuf.Lexing.lex_curr_p MenhirState77 _menhir_env._menhir_lexbuf.Lexing.lex_start_p
    | TOK_URANDOM ->
        _menhir_run24 _menhir_env (Obj.magic _menhir_stack) _menhir_env._menhir_lexbuf.Lexing.lex_curr_p MenhirState77 _menhir_env._menhir_lexbuf.Lexing.lex_start_p
    | TOK_const _v ->
        _menhir_run20 _menhir_env (Obj.magic _menhir_stack) _menhir_env._menhir_lexbuf.Lexing.lex_curr_p MenhirState77 _v _menhir_env._menhir_lexbuf.Lexing.lex_start_p
    | TOK_id _v ->
        _menhir_run23 _menhir_env (Obj.magic _menhir_stack) _menhir_env._menhir_lexbuf.Lexing.lex_curr_p MenhirState77 _v _menhir_env._menhir_lexbuf.Lexing.lex_start_p
    | _ ->
        assert (not _menhir_env._menhir_error);
        _menhir_env._menhir_error <- true;
        _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) MenhirState77

and _menhir_run79 : _menhir_env -> 'ttv_tail * Lexing.position * _menhir_state * (IntermediateSyntax.exp IntermediateSyntax.annotated) * Lexing.position -> 'ttv_return =
  fun _menhir_env _menhir_stack ->
    let _menhir_env = _menhir_discard _menhir_env in
    let _tok = _menhir_env._menhir_token in
    match _tok with
    | TOK_FALSE ->
        _menhir_run43 _menhir_env (Obj.magic _menhir_stack) _menhir_env._menhir_lexbuf.Lexing.lex_curr_p MenhirState79 _menhir_env._menhir_lexbuf.Lexing.lex_start_p
    | TOK_LBRACKET ->
        _menhir_run35 _menhir_env (Obj.magic _menhir_stack) MenhirState79 _menhir_env._menhir_lexbuf.Lexing.lex_start_p
    | TOK_LPAREN ->
        _menhir_run34 _menhir_env (Obj.magic _menhir_stack) MenhirState79 _menhir_env._menhir_lexbuf.Lexing.lex_start_p
    | TOK_MINUS ->
        _menhir_run33 _menhir_env (Obj.magic _menhir_stack) MenhirState79 _menhir_env._menhir_lexbuf.Lexing.lex_start_p
    | TOK_MINUS_MINUS ->
        _menhir_run32 _menhir_env (Obj.magic _menhir_stack) _menhir_env._menhir_lexbuf.Lexing.lex_curr_p MenhirState79 _menhir_env._menhir_lexbuf.Lexing.lex_start_p
    | TOK_MULTIPLY ->
        _menhir_run30 _menhir_env (Obj.magic _menhir_stack) MenhirState79 _menhir_env._menhir_lexbuf.Lexing.lex_start_p
    | TOK_NOT ->
        _menhir_run29 _menhir_env (Obj.magic _menhir_stack) MenhirState79 _menhir_env._menhir_lexbuf.Lexing.lex_start_p
    | TOK_PLUS ->
        _menhir_run28 _menhir_env (Obj.magic _menhir_stack) MenhirState79 _menhir_env._menhir_lexbuf.Lexing.lex_start_p
    | TOK_PLUS_PLUS ->
        _menhir_run27 _menhir_env (Obj.magic _menhir_stack) _menhir_env._menhir_lexbuf.Lexing.lex_curr_p MenhirState79 _menhir_env._menhir_lexbuf.Lexing.lex_start_p
    | TOK_RANDOM ->
        _menhir_run26 _menhir_env (Obj.magic _menhir_stack) _menhir_env._menhir_lexbuf.Lexing.lex_curr_p MenhirState79 _menhir_env._menhir_lexbuf.Lexing.lex_start_p
    | TOK_TRUE ->
        _menhir_run25 _menhir_env (Obj.magic _menhir_stack) _menhir_env._menhir_lexbuf.Lexing.lex_curr_p MenhirState79 _menhir_env._menhir_lexbuf.Lexing.lex_start_p
    | TOK_URANDOM ->
        _menhir_run24 _menhir_env (Obj.magic _menhir_stack) _menhir_env._menhir_lexbuf.Lexing.lex_curr_p MenhirState79 _menhir_env._menhir_lexbuf.Lexing.lex_start_p
    | TOK_const _v ->
        _menhir_run20 _menhir_env (Obj.magic _menhir_stack) _menhir_env._menhir_lexbuf.Lexing.lex_curr_p MenhirState79 _v _menhir_env._menhir_lexbuf.Lexing.lex_start_p
    | TOK_id _v ->
        _menhir_run23 _menhir_env (Obj.magic _menhir_stack) _menhir_env._menhir_lexbuf.Lexing.lex_curr_p MenhirState79 _v _menhir_env._menhir_lexbuf.Lexing.lex_start_p
    | _ ->
        assert (not _menhir_env._menhir_error);
        _menhir_env._menhir_error <- true;
        _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) MenhirState79

and _menhir_goto_add_exp : _menhir_env -> 'ttv_tail -> Lexing.position -> _menhir_state -> (IntermediateSyntax.exp) -> Lexing.position -> 'ttv_return =
  fun _menhir_env _menhir_stack _endpos _menhir_s _v _startpos ->
    let _menhir_stack = (_menhir_stack, _endpos, _menhir_s, _v, _startpos) in
    match _menhir_s with
    | MenhirState92 | MenhirState90 | MenhirState88 | MenhirState72 ->
        let _menhir_stack = Obj.magic _menhir_stack in
        _menhir_reduce5 _menhir_env (Obj.magic _menhir_stack)
    | MenhirState215 | MenhirState207 | MenhirState18 | MenhirState193 | MenhirState22 | MenhirState120 | MenhirState127 | MenhirState129 | MenhirState188 | MenhirState131 | MenhirState181 | MenhirState183 | MenhirState185 | MenhirState146 | MenhirState148 | MenhirState150 | MenhirState152 | MenhirState154 | MenhirState171 | MenhirState156 | MenhirState142 | MenhirState122 | MenhirState34 | MenhirState52 | MenhirState112 | MenhirState70 | MenhirState95 | MenhirState98 | MenhirState106 | MenhirState101 ->
        let _menhir_stack = Obj.magic _menhir_stack in
        assert (not _menhir_env._menhir_error);
        let _tok = _menhir_env._menhir_token in
        (match _tok with
        | TOK_AND | TOK_CHAR | TOK_COMMA | TOK_CPP_DEFINE | TOK_EOF | TOK_EQUAL_EQUAL | TOK_FEAT | TOK_GREATER | TOK_GREATER_EQUAL | TOK_INT | TOK_LESS | TOK_LESS_EQUAL | TOK_NOT_EQUAL | TOK_OR | TOK_RPAREN | TOK_SEMICOLON | TOK_UINT | TOK_VOID | TOK_id _ ->
            let _menhir_stack = Obj.magic _menhir_stack in
            let (_menhir_stack, _endpos_e_, _menhir_s, (e : (IntermediateSyntax.exp)), _startpos_e_) = _menhir_stack in
            let _startpos = _startpos_e_ in
            let _endpos = _endpos_e_ in
            let _v : (IntermediateSyntax.exp) = 
# 190 "frontend/Parser.mly"
                              ( e )
# 1984 "frontend/Parser.ml"
             in
            _menhir_goto_relational_exp _menhir_env _menhir_stack _endpos _menhir_s _v _startpos
        | TOK_MINUS | TOK_PLUS ->
            _menhir_reduce5 _menhir_env (Obj.magic _menhir_stack)
        | _ ->
            assert (not _menhir_env._menhir_error);
            _menhir_env._menhir_error <- true;
            let _menhir_stack = Obj.magic _menhir_stack in
            let (_menhir_stack, _, _menhir_s, _, _) = _menhir_stack in
            _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s)
    | _ ->
        _menhir_fail ()

and _menhir_reduce17 : _menhir_env -> 'ttv_tail * Lexing.position * _menhir_state * (IntermediateSyntax.exp) * Lexing.position -> 'ttv_return =
  fun _menhir_env _menhir_stack ->
    let (_menhir_stack, _endpos_x_, _menhir_s, (x : (IntermediateSyntax.exp)), _startpos_x_) = _menhir_stack in
    let _startpos = _startpos_x_ in
    let _endpos = _endpos_x_ in
    let _v : (IntermediateSyntax.exp IntermediateSyntax.annotated) = let _endpos = _endpos_x_ in
    let _startpos = _startpos_x_ in
    
# 236 "frontend/Parser.mly"
          ( x, (_startpos, _endpos) )
# 2008 "frontend/Parser.ml"
     in
    let _menhir_stack = (_menhir_stack, _endpos, _menhir_s, _v, _startpos) in
    match _menhir_s with
    | MenhirState215 | MenhirState207 | MenhirState18 | MenhirState193 | MenhirState120 | MenhirState129 | MenhirState188 | MenhirState185 | MenhirState183 | MenhirState181 | MenhirState150 | MenhirState154 | MenhirState171 | MenhirState156 | MenhirState152 | MenhirState148 | MenhirState146 | MenhirState142 | MenhirState131 | MenhirState127 | MenhirState122 | MenhirState22 | MenhirState34 | MenhirState112 | MenhirState52 | MenhirState106 | MenhirState101 | MenhirState98 | MenhirState95 | MenhirState70 | MenhirState92 | MenhirState90 | MenhirState88 | MenhirState72 ->
        let _menhir_stack = Obj.magic _menhir_stack in
        assert (not _menhir_env._menhir_error);
        let _tok = _menhir_env._menhir_token in
        (match _tok with
        | TOK_DIVIDE ->
            _menhir_run79 _menhir_env (Obj.magic _menhir_stack)
        | TOK_MODULO ->
            _menhir_run77 _menhir_env (Obj.magic _menhir_stack)
        | TOK_MULTIPLY ->
            _menhir_run75 _menhir_env (Obj.magic _menhir_stack) _menhir_env._menhir_lexbuf.Lexing.lex_start_p
        | _ ->
            assert (not _menhir_env._menhir_error);
            _menhir_env._menhir_error <- true;
            let _menhir_stack = Obj.magic _menhir_stack in
            let (_menhir_stack, _, _menhir_s, _, _) = _menhir_stack in
            _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s)
    | MenhirState82 ->
        let _menhir_stack = Obj.magic _menhir_stack in
        assert (not _menhir_env._menhir_error);
        let _tok = _menhir_env._menhir_token in
        (match _tok with
        | TOK_DIVIDE ->
            _menhir_run79 _menhir_env (Obj.magic _menhir_stack)
        | TOK_MODULO ->
            _menhir_run77 _menhir_env (Obj.magic _menhir_stack)
        | TOK_MULTIPLY ->
            _menhir_run75 _menhir_env (Obj.magic _menhir_stack) _menhir_env._menhir_lexbuf.Lexing.lex_start_p
        | TOK_AND | TOK_CHAR | TOK_COMMA | TOK_CPP_DEFINE | TOK_EOF | TOK_EQUAL_EQUAL | TOK_FEAT | TOK_GREATER | TOK_GREATER_EQUAL | TOK_INT | TOK_LESS | TOK_LESS_EQUAL | TOK_MINUS | TOK_NOT_EQUAL | TOK_OR | TOK_PLUS | TOK_RPAREN | TOK_SEMICOLON | TOK_UINT | TOK_VOID | TOK_id _ ->
            let _menhir_stack = Obj.magic _menhir_stack in
            let (((_menhir_stack, _endpos_e1_, _menhir_s, (e1 : (IntermediateSyntax.exp IntermediateSyntax.annotated)), _startpos_e1_), _startpos__2_), _endpos_e2_, _, (e2 : (IntermediateSyntax.exp IntermediateSyntax.annotated)), _startpos_e2_) = _menhir_stack in
            let _2 = () in
            let _startpos = _startpos_e1_ in
            let _endpos = _endpos_e2_ in
            let _v : (IntermediateSyntax.exp) = 
# 198 "frontend/Parser.mly"
                                                          ( I_add (e1,e2) )
# 2049 "frontend/Parser.ml"
             in
            _menhir_goto_add_exp _menhir_env _menhir_stack _endpos _menhir_s _v _startpos
        | _ ->
            assert (not _menhir_env._menhir_error);
            _menhir_env._menhir_error <- true;
            let _menhir_stack = Obj.magic _menhir_stack in
            let (_menhir_stack, _, _menhir_s, _, _) = _menhir_stack in
            _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s)
    | MenhirState85 ->
        let _menhir_stack = Obj.magic _menhir_stack in
        assert (not _menhir_env._menhir_error);
        let _tok = _menhir_env._menhir_token in
        (match _tok with
        | TOK_DIVIDE ->
            _menhir_run79 _menhir_env (Obj.magic _menhir_stack)
        | TOK_MODULO ->
            _menhir_run77 _menhir_env (Obj.magic _menhir_stack)
        | TOK_MULTIPLY ->
            _menhir_run75 _menhir_env (Obj.magic _menhir_stack) _menhir_env._menhir_lexbuf.Lexing.lex_start_p
        | TOK_AND | TOK_CHAR | TOK_COMMA | TOK_CPP_DEFINE | TOK_EOF | TOK_EQUAL_EQUAL | TOK_FEAT | TOK_GREATER | TOK_GREATER_EQUAL | TOK_INT | TOK_LESS | TOK_LESS_EQUAL | TOK_MINUS | TOK_NOT_EQUAL | TOK_OR | TOK_PLUS | TOK_RPAREN | TOK_SEMICOLON | TOK_UINT | TOK_VOID | TOK_id _ ->
            let _menhir_stack = Obj.magic _menhir_stack in
            let (((_menhir_stack, _endpos_e1_, _menhir_s, (e1 : (IntermediateSyntax.exp IntermediateSyntax.annotated)), _startpos_e1_), _startpos__2_), _endpos_e2_, _, (e2 : (IntermediateSyntax.exp IntermediateSyntax.annotated)), _startpos_e2_) = _menhir_stack in
            let _2 = () in
            let _startpos = _startpos_e1_ in
            let _endpos = _endpos_e2_ in
            let _v : (IntermediateSyntax.exp) = 
# 199 "frontend/Parser.mly"
                                                           ( I_minus (e1,e2) )
# 2078 "frontend/Parser.ml"
             in
            _menhir_goto_add_exp _menhir_env _menhir_stack _endpos _menhir_s _v _startpos
        | _ ->
            assert (not _menhir_env._menhir_error);
            _menhir_env._menhir_error <- true;
            let _menhir_stack = Obj.magic _menhir_stack in
            let (_menhir_stack, _, _menhir_s, _, _) = _menhir_stack in
            _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s)
    | _ ->
        _menhir_fail ()

and _menhir_goto_mul_exp : _menhir_env -> 'ttv_tail -> Lexing.position -> _menhir_state -> (IntermediateSyntax.exp) -> Lexing.position -> 'ttv_return =
  fun _menhir_env _menhir_stack _endpos _menhir_s _v _startpos ->
    let _menhir_stack = (_menhir_stack, _endpos, _menhir_s, _v, _startpos) in
    match _menhir_s with
    | MenhirState215 | MenhirState207 | MenhirState193 | MenhirState18 | MenhirState120 | MenhirState188 | MenhirState129 | MenhirState185 | MenhirState183 | MenhirState181 | MenhirState150 | MenhirState171 | MenhirState154 | MenhirState156 | MenhirState152 | MenhirState148 | MenhirState146 | MenhirState142 | MenhirState131 | MenhirState127 | MenhirState122 | MenhirState22 | MenhirState34 | MenhirState112 | MenhirState106 | MenhirState101 | MenhirState98 | MenhirState95 | MenhirState92 | MenhirState90 | MenhirState88 | MenhirState72 | MenhirState70 | MenhirState52 ->
        let _menhir_stack = Obj.magic _menhir_stack in
        assert (not _menhir_env._menhir_error);
        let _tok = _menhir_env._menhir_token in
        (match _tok with
        | TOK_DIVIDE | TOK_MODULO | TOK_MULTIPLY ->
            _menhir_reduce17 _menhir_env (Obj.magic _menhir_stack)
        | TOK_AND | TOK_CHAR | TOK_COMMA | TOK_CPP_DEFINE | TOK_EOF | TOK_EQUAL_EQUAL | TOK_FEAT | TOK_GREATER | TOK_GREATER_EQUAL | TOK_INT | TOK_LESS | TOK_LESS_EQUAL | TOK_MINUS | TOK_NOT_EQUAL | TOK_OR | TOK_PLUS | TOK_RPAREN | TOK_SEMICOLON | TOK_UINT | TOK_VOID | TOK_id _ ->
            let _menhir_stack = Obj.magic _menhir_stack in
            let (_menhir_stack, _endpos_e_, _menhir_s, (e : (IntermediateSyntax.exp)), _startpos_e_) = _menhir_stack in
            let _startpos = _startpos_e_ in
            let _endpos = _endpos_e_ in
            let _v : (IntermediateSyntax.exp) = 
# 197 "frontend/Parser.mly"
                          ( e )
# 2109 "frontend/Parser.ml"
             in
            _menhir_goto_add_exp _menhir_env _menhir_stack _endpos _menhir_s _v _startpos
        | _ ->
            assert (not _menhir_env._menhir_error);
            _menhir_env._menhir_error <- true;
            let _menhir_stack = Obj.magic _menhir_stack in
            let (_menhir_stack, _, _menhir_s, _, _) = _menhir_stack in
            _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s)
    | MenhirState85 | MenhirState82 ->
        let _menhir_stack = Obj.magic _menhir_stack in
        _menhir_reduce17 _menhir_env (Obj.magic _menhir_stack)
    | _ ->
        _menhir_fail ()

and _menhir_goto_assign_op : _menhir_env -> 'ttv_tail -> (IntermediateSyntax.assignOp) -> 'ttv_return =
  fun _menhir_env _menhir_stack _v ->
    let _menhir_stack = (_menhir_stack, _v) in
    let _menhir_stack = Obj.magic _menhir_stack in
    assert (not _menhir_env._menhir_error);
    let _tok = _menhir_env._menhir_token in
    match _tok with
    | TOK_FALSE ->
        _menhir_run43 _menhir_env (Obj.magic _menhir_stack) _menhir_env._menhir_lexbuf.Lexing.lex_curr_p MenhirState70 _menhir_env._menhir_lexbuf.Lexing.lex_start_p
    | TOK_LBRACKET ->
        _menhir_run35 _menhir_env (Obj.magic _menhir_stack) MenhirState70 _menhir_env._menhir_lexbuf.Lexing.lex_start_p
    | TOK_LPAREN ->
        _menhir_run34 _menhir_env (Obj.magic _menhir_stack) MenhirState70 _menhir_env._menhir_lexbuf.Lexing.lex_start_p
    | TOK_MINUS ->
        _menhir_run33 _menhir_env (Obj.magic _menhir_stack) MenhirState70 _menhir_env._menhir_lexbuf.Lexing.lex_start_p
    | TOK_MINUS_MINUS ->
        _menhir_run32 _menhir_env (Obj.magic _menhir_stack) _menhir_env._menhir_lexbuf.Lexing.lex_curr_p MenhirState70 _menhir_env._menhir_lexbuf.Lexing.lex_start_p
    | TOK_MULTIPLY ->
        _menhir_run30 _menhir_env (Obj.magic _menhir_stack) MenhirState70 _menhir_env._menhir_lexbuf.Lexing.lex_start_p
    | TOK_NOT ->
        _menhir_run29 _menhir_env (Obj.magic _menhir_stack) MenhirState70 _menhir_env._menhir_lexbuf.Lexing.lex_start_p
    | TOK_PLUS ->
        _menhir_run28 _menhir_env (Obj.magic _menhir_stack) MenhirState70 _menhir_env._menhir_lexbuf.Lexing.lex_start_p
    | TOK_PLUS_PLUS ->
        _menhir_run27 _menhir_env (Obj.magic _menhir_stack) _menhir_env._menhir_lexbuf.Lexing.lex_curr_p MenhirState70 _menhir_env._menhir_lexbuf.Lexing.lex_start_p
    | TOK_RANDOM ->
        _menhir_run26 _menhir_env (Obj.magic _menhir_stack) _menhir_env._menhir_lexbuf.Lexing.lex_curr_p MenhirState70 _menhir_env._menhir_lexbuf.Lexing.lex_start_p
    | TOK_TRUE ->
        _menhir_run25 _menhir_env (Obj.magic _menhir_stack) _menhir_env._menhir_lexbuf.Lexing.lex_curr_p MenhirState70 _menhir_env._menhir_lexbuf.Lexing.lex_start_p
    | TOK_URANDOM ->
        _menhir_run24 _menhir_env (Obj.magic _menhir_stack) _menhir_env._menhir_lexbuf.Lexing.lex_curr_p MenhirState70 _menhir_env._menhir_lexbuf.Lexing.lex_start_p
    | TOK_const _v ->
        _menhir_run20 _menhir_env (Obj.magic _menhir_stack) _menhir_env._menhir_lexbuf.Lexing.lex_curr_p MenhirState70 _v _menhir_env._menhir_lexbuf.Lexing.lex_start_p
    | TOK_id _v ->
        _menhir_run23 _menhir_env (Obj.magic _menhir_stack) _menhir_env._menhir_lexbuf.Lexing.lex_curr_p MenhirState70 _v _menhir_env._menhir_lexbuf.Lexing.lex_start_p
    | _ ->
        assert (not _menhir_env._menhir_error);
        _menhir_env._menhir_error <- true;
        _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) MenhirState70

and _menhir_reduce84 : _menhir_env -> 'ttv_tail * Lexing.position * _menhir_state * (IntermediateSyntax.exp) * Lexing.position -> 'ttv_return =
  fun _menhir_env _menhir_stack ->
    let (_menhir_stack, _endpos_e_, _menhir_s, (e : (IntermediateSyntax.exp)), _startpos_e_) = _menhir_stack in
    let _startpos = _startpos_e_ in
    let _endpos = _endpos_e_ in
    let _v : (IntermediateSyntax.exp) = 
# 202 "frontend/Parser.mly"
                             ( e )
# 2172 "frontend/Parser.ml"
     in
    _menhir_goto_mul_exp _menhir_env _menhir_stack _endpos _menhir_s _v _startpos

and _menhir_reduce21 : _menhir_env -> 'ttv_tail * Lexing.position * _menhir_state * (IntermediateSyntax.exp) * Lexing.position -> 'ttv_return =
  fun _menhir_env _menhir_stack ->
    let (_menhir_stack, _endpos_x_, _menhir_s, (x : (IntermediateSyntax.exp)), _startpos_x_) = _menhir_stack in
    let _startpos = _startpos_x_ in
    let _endpos = _endpos_x_ in
    let _v : (IntermediateSyntax.exp IntermediateSyntax.annotated) = let _endpos = _endpos_x_ in
    let _startpos = _startpos_x_ in
    
# 236 "frontend/Parser.mly"
          ( x, (_startpos, _endpos) )
# 2186 "frontend/Parser.ml"
     in
    let _menhir_stack = (_menhir_stack, _endpos, _menhir_s, _v, _startpos) in
    match _menhir_s with
    | MenhirState44 ->
        let _menhir_stack = Obj.magic _menhir_stack in
        let _menhir_stack = Obj.magic _menhir_stack in
        let ((_menhir_stack, _menhir_s, (o : (IntermediateSyntax.unaryOp)), _startpos_o_), _endpos_e_, _, (e : (IntermediateSyntax.exp IntermediateSyntax.annotated)), _startpos_e_) = _menhir_stack in
        let _startpos = _startpos_o_ in
        let _endpos = _endpos_e_ in
        let _v : (IntermediateSyntax.exp) = 
# 212 "frontend/Parser.mly"
                                         ( I_unary (o,e) )
# 2199 "frontend/Parser.ml"
         in
        _menhir_goto_unary_exp _menhir_env _menhir_stack _endpos _menhir_s _v _startpos
    | MenhirState215 | MenhirState207 | MenhirState193 | MenhirState18 | MenhirState120 | MenhirState188 | MenhirState129 | MenhirState185 | MenhirState183 | MenhirState181 | MenhirState150 | MenhirState171 | MenhirState154 | MenhirState156 | MenhirState152 | MenhirState148 | MenhirState146 | MenhirState142 | MenhirState131 | MenhirState127 | MenhirState122 | MenhirState22 | MenhirState34 | MenhirState112 | MenhirState70 | MenhirState52 ->
        let _menhir_stack = Obj.magic _menhir_stack in
        assert (not _menhir_env._menhir_error);
        let _tok = _menhir_env._menhir_token in
        (match _tok with
        | TOK_DIVIDE_EQUAL ->
            let _menhir_stack = Obj.magic _menhir_stack in
            let _menhir_env = _menhir_discard _menhir_env in
            let _menhir_stack = Obj.magic _menhir_stack in
            let _1 = () in
            let _v : (IntermediateSyntax.assignOp) = 
# 173 "frontend/Parser.mly"
                     ( I_DIVIDE_EQUAL )
# 2215 "frontend/Parser.ml"
             in
            _menhir_goto_assign_op _menhir_env _menhir_stack _v
        | TOK_EQUAL ->
            let _menhir_stack = Obj.magic _menhir_stack in
            let _menhir_env = _menhir_discard _menhir_env in
            let _menhir_stack = Obj.magic _menhir_stack in
            let _1 = () in
            let _v : (IntermediateSyntax.assignOp) = 
# 169 "frontend/Parser.mly"
                ( I_EQUAL )
# 2226 "frontend/Parser.ml"
             in
            _menhir_goto_assign_op _menhir_env _menhir_stack _v
        | TOK_MINUS_EQUAL ->
            let _menhir_stack = Obj.magic _menhir_stack in
            let _menhir_env = _menhir_discard _menhir_env in
            let _menhir_stack = Obj.magic _menhir_stack in
            let _1 = () in
            let _v : (IntermediateSyntax.assignOp) = 
# 171 "frontend/Parser.mly"
                    ( I_MINUS_EQUAL )
# 2237 "frontend/Parser.ml"
             in
            _menhir_goto_assign_op _menhir_env _menhir_stack _v
        | TOK_MODULO_EQUAL ->
            let _menhir_stack = Obj.magic _menhir_stack in
            let _menhir_env = _menhir_discard _menhir_env in
            let _menhir_stack = Obj.magic _menhir_stack in
            let _1 = () in
            let _v : (IntermediateSyntax.assignOp) = 
# 174 "frontend/Parser.mly"
                     ( I_MODULO_EQUAL )
# 2248 "frontend/Parser.ml"
             in
            _menhir_goto_assign_op _menhir_env _menhir_stack _v
        | TOK_MULTIPLY_EQUAL ->
            let _menhir_stack = Obj.magic _menhir_stack in
            let _menhir_env = _menhir_discard _menhir_env in
            let _menhir_stack = Obj.magic _menhir_stack in
            let _1 = () in
            let _v : (IntermediateSyntax.assignOp) = 
# 172 "frontend/Parser.mly"
                      ( I_MULTIPLY_EQUAL )
# 2259 "frontend/Parser.ml"
             in
            _menhir_goto_assign_op _menhir_env _menhir_stack _v
        | TOK_PLUS_EQUAL ->
            let _menhir_stack = Obj.magic _menhir_stack in
            let _menhir_env = _menhir_discard _menhir_env in
            let _menhir_stack = Obj.magic _menhir_stack in
            let _1 = () in
            let _v : (IntermediateSyntax.assignOp) = 
# 170 "frontend/Parser.mly"
                   ( I_PLUS_EQUAL )
# 2270 "frontend/Parser.ml"
             in
            _menhir_goto_assign_op _menhir_env _menhir_stack _v
        | _ ->
            assert (not _menhir_env._menhir_error);
            _menhir_env._menhir_error <- true;
            let _menhir_stack = Obj.magic _menhir_stack in
            let (_menhir_stack, _, _menhir_s, _, _) = _menhir_stack in
            _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s)
    | MenhirState75 ->
        let _menhir_stack = Obj.magic _menhir_stack in
        let _menhir_stack = Obj.magic _menhir_stack in
        let (((_menhir_stack, _endpos_e1_, _menhir_s, (e1 : (IntermediateSyntax.exp IntermediateSyntax.annotated)), _startpos_e1_), _startpos__2_), _endpos_e2_, _, (e2 : (IntermediateSyntax.exp IntermediateSyntax.annotated)), _startpos_e2_) = _menhir_stack in
        let _2 = () in
        let _startpos = _startpos_e1_ in
        let _endpos = _endpos_e2_ in
        let _v : (IntermediateSyntax.exp) = 
# 203 "frontend/Parser.mly"
                                                                ( I_mul (e1,e2) )
# 2289 "frontend/Parser.ml"
         in
        _menhir_goto_mul_exp _menhir_env _menhir_stack _endpos _menhir_s _v _startpos
    | MenhirState77 ->
        let _menhir_stack = Obj.magic _menhir_stack in
        let _menhir_stack = Obj.magic _menhir_stack in
        let ((_menhir_stack, _endpos_e1_, _menhir_s, (e1 : (IntermediateSyntax.exp IntermediateSyntax.annotated)), _startpos_e1_), _endpos_e2_, _, (e2 : (IntermediateSyntax.exp IntermediateSyntax.annotated)), _startpos_e2_) = _menhir_stack in
        let _2 = () in
        let _startpos = _startpos_e1_ in
        let _endpos = _endpos_e2_ in
        let _v : (IntermediateSyntax.exp) = 
# 205 "frontend/Parser.mly"
                                                              ( I_mod (e1,e2) )
# 2302 "frontend/Parser.ml"
         in
        _menhir_goto_mul_exp _menhir_env _menhir_stack _endpos _menhir_s _v _startpos
    | MenhirState79 ->
        let _menhir_stack = Obj.magic _menhir_stack in
        let _menhir_stack = Obj.magic _menhir_stack in
        let ((_menhir_stack, _endpos_e1_, _menhir_s, (e1 : (IntermediateSyntax.exp IntermediateSyntax.annotated)), _startpos_e1_), _endpos_e2_, _, (e2 : (IntermediateSyntax.exp IntermediateSyntax.annotated)), _startpos_e2_) = _menhir_stack in
        let _2 = () in
        let _startpos = _startpos_e1_ in
        let _endpos = _endpos_e2_ in
        let _v : (IntermediateSyntax.exp) = 
# 204 "frontend/Parser.mly"
                                                              ( I_div (e1,e2) )
# 2315 "frontend/Parser.ml"
         in
        _menhir_goto_mul_exp _menhir_env _menhir_stack _endpos _menhir_s _v _startpos
    | MenhirState32 ->
        let _menhir_stack = Obj.magic _menhir_stack in
        let _menhir_stack = Obj.magic _menhir_stack in
        let ((_menhir_stack, _endpos__1_, _menhir_s, _startpos__1_), _endpos_e_, _, (e : (IntermediateSyntax.exp IntermediateSyntax.annotated)), _startpos_e_) = _menhir_stack in
        let _1 = () in
        let _startpos = _startpos__1_ in
        let _endpos = _endpos_e_ in
        let _v : (IntermediateSyntax.exp) = 
# 210 "frontend/Parser.mly"
                                           ( I_predecr e )
# 2328 "frontend/Parser.ml"
         in
        _menhir_goto_unary_exp _menhir_env _menhir_stack _endpos _menhir_s _v _startpos
    | MenhirState29 ->
        let _menhir_stack = Obj.magic _menhir_stack in
        let _menhir_stack = Obj.magic _menhir_stack in
        let ((_menhir_stack, _menhir_s, _startpos__1_), _endpos_e_, _, (e : (IntermediateSyntax.exp IntermediateSyntax.annotated)), _startpos_e_) = _menhir_stack in
        let _1 = () in
        let _startpos = _startpos__1_ in
        let _endpos = _endpos_e_ in
        let _v : (IntermediateSyntax.exp) = 
# 211 "frontend/Parser.mly"
                                     ( I_not e )
# 2341 "frontend/Parser.ml"
         in
        _menhir_goto_unary_exp _menhir_env _menhir_stack _endpos _menhir_s _v _startpos
    | MenhirState27 ->
        let _menhir_stack = Obj.magic _menhir_stack in
        let _menhir_stack = Obj.magic _menhir_stack in
        let ((_menhir_stack, _endpos__1_, _menhir_s, _startpos__1_), _endpos_e_, _, (e : (IntermediateSyntax.exp IntermediateSyntax.annotated)), _startpos_e_) = _menhir_stack in
        let _1 = () in
        let _startpos = _startpos__1_ in
        let _endpos = _endpos_e_ in
        let _v : (IntermediateSyntax.exp) = 
# 209 "frontend/Parser.mly"
                                          ( I_preincr e )
# 2354 "frontend/Parser.ml"
         in
        _menhir_goto_unary_exp _menhir_env _menhir_stack _endpos _menhir_s _v _startpos
    | _ ->
        _menhir_fail ()

and _menhir_goto_list_annotate_stmt__ : _menhir_env -> 'ttv_tail -> _menhir_state -> (IntermediateSyntax.stmt IntermediateSyntax.annotated list) -> 'ttv_return =
  fun _menhir_env _menhir_stack _menhir_s _v ->
    let _menhir_stack = (_menhir_stack, _menhir_s, _v) in
    match _menhir_s with
    | MenhirState18 ->
        let _menhir_stack = Obj.magic _menhir_stack in
        assert (not _menhir_env._menhir_error);
        let _tok = _menhir_env._menhir_token in
        (match _tok with
        | TOK_RCURLY ->
            let _menhir_stack = Obj.magic _menhir_stack in
            let _endpos = _menhir_env._menhir_lexbuf.Lexing.lex_curr_p in
            let _menhir_env = _menhir_discard _menhir_env in
            let _menhir_stack = Obj.magic _menhir_stack in
            let _endpos__3_ = _endpos in
            let ((_menhir_stack, _menhir_s, _startpos__1_), _, (s : (IntermediateSyntax.stmt IntermediateSyntax.annotated list))) = _menhir_stack in
            let _3 = () in
            let _1 = () in
            let _startpos = _startpos__1_ in
            let _endpos = _endpos__3_ in
            let _v : (IntermediateSyntax.stmt IntermediateSyntax.annotated list) = 
# 162 "frontend/Parser.mly"
                                                  ( s )
# 2383 "frontend/Parser.ml"
             in
            (match _menhir_s with
            | MenhirState193 | MenhirState18 | MenhirState120 | MenhirState188 | MenhirState129 | MenhirState185 | MenhirState150 | MenhirState171 | MenhirState154 ->
                let _menhir_stack = Obj.magic _menhir_stack in
                let _menhir_stack = Obj.magic _menhir_stack in
                let _endpos_s_ = _endpos in
                let (s : (IntermediateSyntax.stmt IntermediateSyntax.annotated list)) = _v in
                let _startpos_s_ = _startpos in
                let _startpos = _startpos_s_ in
                let _endpos = _endpos_s_ in
                let _v : (IntermediateSyntax.stmt) = 
# 132 "frontend/Parser.mly"
                   ( I_block s )
# 2397 "frontend/Parser.ml"
                 in
                _menhir_goto_stmt _menhir_env _menhir_stack _endpos _menhir_s _v _startpos
            | MenhirState17 ->
                let _menhir_stack = Obj.magic _menhir_stack in
                let _menhir_stack = Obj.magic _menhir_stack in
                let _endpos_b_ = _endpos in
                let (b : (IntermediateSyntax.stmt IntermediateSyntax.annotated list)) = _v in
                let _startpos_b_ = _startpos in
                let (((((_menhir_stack, _menhir_s, _startpos__1_), _, _startpos__2_), _startpos__3_), _, (xs0 : ((IntermediateSyntax.typ IntermediateSyntax.annotated *
   string IntermediateSyntax.annotated)
  list))), _endpos__5_) = _menhir_stack in
                let _5 = () in
                let _3 = () in
                let _2 = () in
                let _1 = () in
                let _startpos = _startpos__1_ in
                let _endpos = _endpos_b_ in
                let _v : (unit) = let p =
                  let xs = xs0 in
                  
# 206 "/usr/share/menhir/standard.mly"
    ( xs )
# 2420 "frontend/Parser.ml"
                  
                in
                
# 109 "frontend/Parser.mly"
                                                                                                     ( )
# 2426 "frontend/Parser.ml"
                 in
                let _menhir_stack = Obj.magic _menhir_stack in
                let _menhir_stack = Obj.magic _menhir_stack in
                let _endpos_x_ = _endpos in
                let (x : (unit)) = _v in
                let _startpos_x_ = _startpos in
                let _startpos = _startpos_x_ in
                let _endpos = _endpos_x_ in
                let _v : (unit * (Lexing.position * Lexing.position)) = let _endpos = _endpos_x_ in
                let _startpos = _startpos_x_ in
                
# 236 "frontend/Parser.mly"
          ( x, (_startpos, _endpos) )
# 2440 "frontend/Parser.ml"
                 in
                let _menhir_stack = Obj.magic _menhir_stack in
                let _menhir_stack = Obj.magic _menhir_stack in
                let _endpos_d_ = _endpos in
                let (d : (unit * (Lexing.position * Lexing.position))) = _v in
                let _startpos_d_ = _startpos in
                let _startpos = _startpos_d_ in
                let _endpos = _endpos_d_ in
                let _v : (IntermediateSyntax.decl) = 
# 86 "frontend/Parser.mly"
                             ( I_ignore )
# 2452 "frontend/Parser.ml"
                 in
                _menhir_goto_decl _menhir_env _menhir_stack _endpos _menhir_s _v _startpos
            | MenhirState199 ->
                let _menhir_stack = Obj.magic _menhir_stack in
                let _menhir_stack = Obj.magic _menhir_stack in
                let _endpos_b_ = _endpos in
                let (b : (IntermediateSyntax.stmt IntermediateSyntax.annotated list)) = _v in
                let _startpos_b_ = _startpos in
                let (((((_menhir_stack, _menhir_s, _startpos__10_), _, (f : (string IntermediateSyntax.annotated)), _startpos_f_), _startpos__3_), _, _startpos__4_), _endpos__5_) = _menhir_stack in
                let _5 = () in
                let _4 = () in
                let _3 = () in
                let _10 = () in
                let _startpos = _startpos__10_ in
                let _endpos = _endpos_b_ in
                let _v : (IntermediateSyntax.functionDecl) = let t =
                  let _1 = _10 in
                  
# 119 "frontend/Parser.mly"
                ( None )
# 2473 "frontend/Parser.ml"
                  
                in
                
# 113 "frontend/Parser.mly"
                                                                                               ( t, f, [], b )
# 2479 "frontend/Parser.ml"
                 in
                _menhir_goto_function_decl _menhir_env _menhir_stack _endpos _menhir_s _v _startpos
            | MenhirState203 ->
                let _menhir_stack = Obj.magic _menhir_stack in
                let _menhir_stack = Obj.magic _menhir_stack in
                let _endpos_b_ = _endpos in
                let (b : (IntermediateSyntax.stmt IntermediateSyntax.annotated list)) = _v in
                let _startpos_b_ = _startpos in
                let (((((_menhir_stack, _menhir_s, _startpos__10_), _, (f : (string IntermediateSyntax.annotated)), _startpos_f_), _startpos__3_), _, (xs0 : ((IntermediateSyntax.typ IntermediateSyntax.annotated *
   string IntermediateSyntax.annotated)
  list))), _endpos__5_) = _menhir_stack in
                let _5 = () in
                let _3 = () in
                let _10 = () in
                let _startpos = _startpos__10_ in
                let _endpos = _endpos_b_ in
                let _v : (IntermediateSyntax.functionDecl) = let p =
                  let xs = xs0 in
                  
# 206 "/usr/share/menhir/standard.mly"
    ( xs )
# 2501 "frontend/Parser.ml"
                  
                in
                let t =
                  let _1 = _10 in
                  
# 119 "frontend/Parser.mly"
                ( None )
# 2509 "frontend/Parser.ml"
                  
                in
                
# 115 "frontend/Parser.mly"
                                                                                                                      ( t, f, p, b )
# 2515 "frontend/Parser.ml"
                 in
                _menhir_goto_function_decl _menhir_env _menhir_stack _endpos _menhir_s _v _startpos
            | MenhirState230 ->
                let _menhir_stack = Obj.magic _menhir_stack in
                let _menhir_stack = Obj.magic _menhir_stack in
                let _endpos_b_ = _endpos in
                let (b : (IntermediateSyntax.stmt IntermediateSyntax.annotated list)) = _v in
                let _startpos_b_ = _startpos in
                let (((((_menhir_stack, _menhir_s, (t0 : (IntermediateSyntax.typ IntermediateSyntax.annotated)), _startpos_t0_), _, (f : (string IntermediateSyntax.annotated)), _startpos_f_), _startpos__3_), _, _startpos__4_), _endpos__5_) = _menhir_stack in
                let _5 = () in
                let _4 = () in
                let _3 = () in
                let _startpos = _startpos_t0_ in
                let _endpos = _endpos_b_ in
                let _v : (IntermediateSyntax.functionDecl) = let t =
                  let t = t0 in
                  
# 118 "frontend/Parser.mly"
                            ( Some t )
# 2535 "frontend/Parser.ml"
                  
                in
                
# 113 "frontend/Parser.mly"
                                                                                               ( t, f, [], b )
# 2541 "frontend/Parser.ml"
                 in
                _menhir_goto_function_decl _menhir_env _menhir_stack _endpos _menhir_s _v _startpos
            | MenhirState234 ->
                let _menhir_stack = Obj.magic _menhir_stack in
                let _menhir_stack = Obj.magic _menhir_stack in
                let _endpos_b_ = _endpos in
                let (b : (IntermediateSyntax.stmt IntermediateSyntax.annotated list)) = _v in
                let _startpos_b_ = _startpos in
                let (((((_menhir_stack, _menhir_s, (t0 : (IntermediateSyntax.typ IntermediateSyntax.annotated)), _startpos_t0_), _, (f : (string IntermediateSyntax.annotated)), _startpos_f_), _startpos__3_), _, (xs0 : ((IntermediateSyntax.typ IntermediateSyntax.annotated *
   string IntermediateSyntax.annotated)
  list))), _endpos__5_) = _menhir_stack in
                let _5 = () in
                let _3 = () in
                let _startpos = _startpos_t0_ in
                let _endpos = _endpos_b_ in
                let _v : (IntermediateSyntax.functionDecl) = let p =
                  let xs = xs0 in
                  
# 206 "/usr/share/menhir/standard.mly"
    ( xs )
# 2562 "frontend/Parser.ml"
                  
                in
                let t =
                  let t = t0 in
                  
# 118 "frontend/Parser.mly"
                            ( Some t )
# 2570 "frontend/Parser.ml"
                  
                in
                
# 115 "frontend/Parser.mly"
                                                                                                                      ( t, f, p, b )
# 2576 "frontend/Parser.ml"
                 in
                _menhir_goto_function_decl _menhir_env _menhir_stack _endpos _menhir_s _v _startpos
            | _ ->
                _menhir_fail ())
        | _ ->
            assert (not _menhir_env._menhir_error);
            _menhir_env._menhir_error <- true;
            let _menhir_stack = Obj.magic _menhir_stack in
            let (_menhir_stack, _menhir_s, _) = _menhir_stack in
            _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s)
    | MenhirState193 ->
        let _menhir_stack = Obj.magic _menhir_stack in
        let _menhir_stack = Obj.magic _menhir_stack in
        let ((_menhir_stack, _endpos_x_, _menhir_s, (x : (IntermediateSyntax.stmt IntermediateSyntax.annotated))), _, (xs : (IntermediateSyntax.stmt IntermediateSyntax.annotated list))) = _menhir_stack in
        let _v : (IntermediateSyntax.stmt IntermediateSyntax.annotated list) = 
# 187 "/usr/share/menhir/standard.mly"
    ( x :: xs )
# 2594 "frontend/Parser.ml"
         in
        _menhir_goto_list_annotate_stmt__ _menhir_env _menhir_stack _menhir_s _v
    | _ ->
        _menhir_fail ()

and _menhir_goto_exp_stmt : _menhir_env -> 'ttv_tail -> Lexing.position -> _menhir_state -> (IntermediateSyntax.stmt) -> Lexing.position -> 'ttv_return =
  fun _menhir_env _menhir_stack _endpos _menhir_s _v _startpos ->
    let _menhir_stack = Obj.magic _menhir_stack in
    let _menhir_stack = Obj.magic _menhir_stack in
    let _endpos_s_ = _endpos in
    let (s : (IntermediateSyntax.stmt)) = _v in
    let _startpos_s_ = _startpos in
    let _startpos = _startpos_s_ in
    let _endpos = _endpos_s_ in
    let _v : (IntermediateSyntax.stmt) = 
# 126 "frontend/Parser.mly"
                  ( s )
# 2612 "frontend/Parser.ml"
     in
    _menhir_goto_stmt _menhir_env _menhir_stack _endpos _menhir_s _v _startpos

and _menhir_goto_option_annotate_exp__ : _menhir_env -> 'ttv_tail -> _menhir_state -> (IntermediateSyntax.exp IntermediateSyntax.annotated option) -> 'ttv_return =
  fun _menhir_env _menhir_stack _menhir_s _v ->
    let _menhir_stack = (_menhir_stack, _menhir_s, _v) in
    let _menhir_stack = Obj.magic _menhir_stack in
    assert (not _menhir_env._menhir_error);
    let _tok = _menhir_env._menhir_token in
    match _tok with
    | TOK_SEMICOLON ->
        let _menhir_stack = Obj.magic _menhir_stack in
        let _endpos = _menhir_env._menhir_lexbuf.Lexing.lex_curr_p in
        let _startpos = _menhir_env._menhir_lexbuf.Lexing.lex_start_p in
        let _menhir_env = _menhir_discard _menhir_env in
        let _menhir_stack = Obj.magic _menhir_stack in
        let _endpos__3_ = _endpos in
        let _startpos__3_ = _startpos in
        let ((_menhir_stack, _menhir_s, _startpos__1_), _, (e : (IntermediateSyntax.exp IntermediateSyntax.annotated option))) = _menhir_stack in
        let _3 = () in
        let _1 = () in
        let _startpos = _startpos__1_ in
        let _endpos = _endpos__3_ in
        let _v : (IntermediateSyntax.stmt) = 
# 156 "frontend/Parser.mly"
                                                    ( I_return e )
# 2639 "frontend/Parser.ml"
         in
        let _menhir_stack = Obj.magic _menhir_stack in
        let _menhir_stack = Obj.magic _menhir_stack in
        let _endpos_s_ = _endpos in
        let (s : (IntermediateSyntax.stmt)) = _v in
        let _startpos_s_ = _startpos in
        let _startpos = _startpos_s_ in
        let _endpos = _endpos_s_ in
        let _v : (IntermediateSyntax.stmt) = 
# 130 "frontend/Parser.mly"
                   ( s )
# 2651 "frontend/Parser.ml"
         in
        _menhir_goto_stmt _menhir_env _menhir_stack _endpos _menhir_s _v _startpos
    | _ ->
        assert (not _menhir_env._menhir_error);
        _menhir_env._menhir_error <- true;
        let _menhir_stack = Obj.magic _menhir_stack in
        let (_menhir_stack, _menhir_s, _) = _menhir_stack in
        _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s

and _menhir_goto_separated_nonempty_list_TOK_COMMA_declarator_ : _menhir_env -> 'ttv_tail -> _menhir_state -> (IntermediateSyntax.declarator list) -> 'ttv_return =
  fun _menhir_env _menhir_stack _menhir_s _v ->
    match _menhir_s with
    | MenhirState226 | MenhirState133 | MenhirState134 ->
        let _menhir_stack = Obj.magic _menhir_stack in
        let _menhir_stack = Obj.magic _menhir_stack in
        let (x : (IntermediateSyntax.declarator list)) = _v in
        let _v : (IntermediateSyntax.declarator list) = 
# 130 "/usr/share/menhir/standard.mly"
    ( x )
# 2671 "frontend/Parser.ml"
         in
        _menhir_goto_loption_separated_nonempty_list_TOK_COMMA_declarator__ _menhir_env _menhir_stack _menhir_s _v
    | MenhirState139 ->
        let _menhir_stack = Obj.magic _menhir_stack in
        let _menhir_stack = Obj.magic _menhir_stack in
        let (xs : (IntermediateSyntax.declarator list)) = _v in
        let (_menhir_stack, _menhir_s, (x : (IntermediateSyntax.declarator))) = _menhir_stack in
        let _2 = () in
        let _v : (IntermediateSyntax.declarator list) = 
# 217 "/usr/share/menhir/standard.mly"
    ( x :: xs )
# 2683 "frontend/Parser.ml"
         in
        _menhir_goto_separated_nonempty_list_TOK_COMMA_declarator_ _menhir_env _menhir_stack _menhir_s _v
    | _ ->
        _menhir_fail ()

and _menhir_goto_loption_separated_nonempty_list_TOK_COMMA_annotate_exp___ : _menhir_env -> 'ttv_tail -> _menhir_state -> (IntermediateSyntax.exp IntermediateSyntax.annotated list) -> 'ttv_return =
  fun _menhir_env _menhir_stack _menhir_s _v ->
    let _menhir_stack = (_menhir_stack, _menhir_s, _v) in
    let _menhir_stack = Obj.magic _menhir_stack in
    assert (not _menhir_env._menhir_error);
    let _tok = _menhir_env._menhir_token in
    match _tok with
    | TOK_RPAREN ->
        let _menhir_stack = Obj.magic _menhir_stack in
        let _endpos = _menhir_env._menhir_lexbuf.Lexing.lex_curr_p in
        let _menhir_env = _menhir_discard _menhir_env in
        let _menhir_stack = Obj.magic _menhir_stack in
        let _endpos__4_ = _endpos in
        let (((_menhir_stack, _menhir_s, (e : (IntermediateSyntax.exp IntermediateSyntax.annotated)), _startpos_e_), _startpos__2_), _, (xs0 : (IntermediateSyntax.exp IntermediateSyntax.annotated list))) = _menhir_stack in
        let _4 = () in
        let _2 = () in
        let _startpos = _startpos_e_ in
        let _endpos = _endpos__4_ in
        let _v : (IntermediateSyntax.exp) = let p =
          let xs = xs0 in
          
# 206 "/usr/share/menhir/standard.mly"
    ( xs )
# 2712 "frontend/Parser.ml"
          
        in
        
# 222 "frontend/Parser.mly"
                                                                                               ( I_call (e,p) )
# 2718 "frontend/Parser.ml"
         in
        _menhir_goto_postfix_exp _menhir_env _menhir_stack _endpos _menhir_s _v _startpos
    | _ ->
        assert (not _menhir_env._menhir_error);
        _menhir_env._menhir_error <- true;
        let _menhir_stack = Obj.magic _menhir_stack in
        let (_menhir_stack, _menhir_s, _) = _menhir_stack in
        _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s

and _menhir_goto_unary_exp : _menhir_env -> 'ttv_tail -> Lexing.position -> _menhir_state -> (IntermediateSyntax.exp) -> Lexing.position -> 'ttv_return =
  fun _menhir_env _menhir_stack _endpos _menhir_s _v _startpos ->
    let _menhir_stack = (_menhir_stack, _endpos, _menhir_s, _v, _startpos) in
    match _menhir_s with
    | MenhirState27 | MenhirState29 | MenhirState32 | MenhirState79 | MenhirState77 | MenhirState75 | MenhirState44 ->
        let _menhir_stack = Obj.magic _menhir_stack in
        _menhir_reduce21 _menhir_env (Obj.magic _menhir_stack)
    | MenhirState215 | MenhirState207 | MenhirState193 | MenhirState18 | MenhirState120 | MenhirState188 | MenhirState129 | MenhirState185 | MenhirState183 | MenhirState181 | MenhirState150 | MenhirState171 | MenhirState154 | MenhirState156 | MenhirState152 | MenhirState148 | MenhirState146 | MenhirState142 | MenhirState131 | MenhirState127 | MenhirState122 | MenhirState22 | MenhirState34 | MenhirState112 | MenhirState70 | MenhirState52 ->
        let _menhir_stack = Obj.magic _menhir_stack in
        assert (not _menhir_env._menhir_error);
        let _tok = _menhir_env._menhir_token in
        (match _tok with
        | TOK_AND | TOK_CHAR | TOK_COMMA | TOK_CPP_DEFINE | TOK_DIVIDE | TOK_EOF | TOK_EQUAL_EQUAL | TOK_FEAT | TOK_GREATER | TOK_GREATER_EQUAL | TOK_INT | TOK_LESS | TOK_LESS_EQUAL | TOK_MINUS | TOK_MODULO | TOK_MULTIPLY | TOK_NOT_EQUAL | TOK_OR | TOK_PLUS | TOK_RPAREN | TOK_SEMICOLON | TOK_UINT | TOK_VOID | TOK_id _ ->
            _menhir_reduce84 _menhir_env (Obj.magic _menhir_stack)
        | TOK_DIVIDE_EQUAL | TOK_EQUAL | TOK_MINUS_EQUAL | TOK_MODULO_EQUAL | TOK_MULTIPLY_EQUAL | TOK_PLUS_EQUAL ->
            _menhir_reduce21 _menhir_env (Obj.magic _menhir_stack)
        | _ ->
            assert (not _menhir_env._menhir_error);
            _menhir_env._menhir_error <- true;
            let _menhir_stack = Obj.magic _menhir_stack in
            let (_menhir_stack, _, _menhir_s, _, _) = _menhir_stack in
            _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s)
    | MenhirState106 | MenhirState101 | MenhirState98 | MenhirState95 | MenhirState92 | MenhirState90 | MenhirState88 | MenhirState85 | MenhirState82 | MenhirState72 ->
        let _menhir_stack = Obj.magic _menhir_stack in
        _menhir_reduce84 _menhir_env (Obj.magic _menhir_stack)
    | _ ->
        _menhir_fail ()

and _menhir_goto_decl : _menhir_env -> 'ttv_tail -> Lexing.position -> _menhir_state -> (IntermediateSyntax.decl) -> Lexing.position -> 'ttv_return =
  fun _menhir_env _menhir_stack _endpos _menhir_s _v _startpos ->
    let _menhir_stack = (_menhir_stack, _endpos, _menhir_s, _v, _startpos) in
    let _menhir_stack = Obj.magic _menhir_stack in
    assert (not _menhir_env._menhir_error);
    let _tok = _menhir_env._menhir_token in
    match _tok with
    | TOK_CHAR ->
        _menhir_run8 _menhir_env (Obj.magic _menhir_stack) _menhir_env._menhir_lexbuf.Lexing.lex_curr_p MenhirState223 _menhir_env._menhir_lexbuf.Lexing.lex_start_p
    | TOK_CPP_DEFINE ->
        _menhir_run214 _menhir_env (Obj.magic _menhir_stack) MenhirState223 _menhir_env._menhir_lexbuf.Lexing.lex_start_p
    | TOK_FEAT ->
        _menhir_run206 _menhir_env (Obj.magic _menhir_stack) MenhirState223 _menhir_env._menhir_lexbuf.Lexing.lex_start_p
    | TOK_INT ->
        _menhir_run7 _menhir_env (Obj.magic _menhir_stack) _menhir_env._menhir_lexbuf.Lexing.lex_curr_p MenhirState223 _menhir_env._menhir_lexbuf.Lexing.lex_start_p
    | TOK_UINT ->
        _menhir_run5 _menhir_env (Obj.magic _menhir_stack) MenhirState223 _menhir_env._menhir_lexbuf.Lexing.lex_start_p
    | TOK_VOID ->
        _menhir_run1 _menhir_env (Obj.magic _menhir_stack) MenhirState223 _menhir_env._menhir_lexbuf.Lexing.lex_start_p
    | TOK_EOF ->
        _menhir_reduce72 _menhir_env (Obj.magic _menhir_stack) MenhirState223
    | _ ->
        assert (not _menhir_env._menhir_error);
        _menhir_env._menhir_error <- true;
        _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) MenhirState223

and _menhir_reduce70 : _menhir_env -> 'ttv_tail -> _menhir_state -> 'ttv_return =
  fun _menhir_env _menhir_stack _menhir_s ->
    let _v : (IntermediateSyntax.stmt IntermediateSyntax.annotated list) = 
# 185 "/usr/share/menhir/standard.mly"
    ( [] )
# 2787 "frontend/Parser.ml"
     in
    _menhir_goto_list_annotate_stmt__ _menhir_env _menhir_stack _menhir_s _v

and _menhir_goto_selection_stmt : _menhir_env -> 'ttv_tail -> Lexing.position -> _menhir_state -> (IntermediateSyntax.stmt) -> Lexing.position -> 'ttv_return =
  fun _menhir_env _menhir_stack _endpos _menhir_s _v _startpos ->
    let _menhir_stack = Obj.magic _menhir_stack in
    let _menhir_stack = Obj.magic _menhir_stack in
    let _endpos_s_ = _endpos in
    let (s : (IntermediateSyntax.stmt)) = _v in
    let _startpos_s_ = _startpos in
    let _startpos = _startpos_s_ in
    let _endpos = _endpos_s_ in
    let _v : (IntermediateSyntax.stmt) = 
# 127 "frontend/Parser.mly"
                      ( s )
# 2803 "frontend/Parser.ml"
     in
    _menhir_goto_stmt _menhir_env _menhir_stack _endpos _menhir_s _v _startpos

and _menhir_goto_iteration_stmt : _menhir_env -> 'ttv_tail -> Lexing.position -> _menhir_state -> (IntermediateSyntax.stmt) -> Lexing.position -> 'ttv_return =
  fun _menhir_env _menhir_stack _endpos _menhir_s _v _startpos ->
    let _menhir_stack = Obj.magic _menhir_stack in
    let _menhir_stack = Obj.magic _menhir_stack in
    let _endpos_s_ = _endpos in
    let (s : (IntermediateSyntax.stmt)) = _v in
    let _startpos_s_ = _startpos in
    let _startpos = _startpos_s_ in
    let _endpos = _endpos_s_ in
    let _v : (IntermediateSyntax.stmt) = 
# 129 "frontend/Parser.mly"
                      ( s )
# 2819 "frontend/Parser.ml"
     in
    _menhir_goto_stmt _menhir_env _menhir_stack _endpos _menhir_s _v _startpos

and _menhir_goto_conditional_stmt : _menhir_env -> 'ttv_tail -> Lexing.position -> _menhir_state -> (IntermediateSyntax.stmt) -> Lexing.position -> 'ttv_return =
  fun _menhir_env _menhir_stack _endpos _menhir_s _v _startpos ->
    let _menhir_stack = Obj.magic _menhir_stack in
    let _menhir_stack = Obj.magic _menhir_stack in
    let _endpos_s_ = _endpos in
    let (s : (IntermediateSyntax.stmt)) = _v in
    let _startpos_s_ = _startpos in
    let _startpos = _startpos_s_ in
    let _endpos = _endpos_s_ in
    let _v : (IntermediateSyntax.stmt) = 
# 128 "frontend/Parser.mly"
                        ( s )
# 2835 "frontend/Parser.ml"
     in
    _menhir_goto_stmt _menhir_env _menhir_stack _endpos _menhir_s _v _startpos

and _menhir_run19 : _menhir_env -> 'ttv_tail -> Lexing.position -> _menhir_state -> (
# 35 "frontend/Parser.mly"
       (string)
# 2842 "frontend/Parser.ml"
) -> Lexing.position -> 'ttv_return =
  fun _menhir_env _menhir_stack _endpos _menhir_s _v _startpos ->
    let _menhir_stack = (_menhir_stack, _endpos, _menhir_s, _v, _startpos) in
    let _menhir_env = _menhir_discard _menhir_env in
    let _tok = _menhir_env._menhir_token in
    match _tok with
    | TOK_AND | TOK_DIVIDE | TOK_DIVIDE_EQUAL | TOK_EQUAL | TOK_EQUAL_EQUAL | TOK_GREATER | TOK_GREATER_EQUAL | TOK_LESS | TOK_LESS_EQUAL | TOK_LPAREN | TOK_MINUS | TOK_MINUS_EQUAL | TOK_MINUS_MINUS | TOK_MODULO | TOK_MODULO_EQUAL | TOK_MULTIPLY | TOK_MULTIPLY_EQUAL | TOK_NOT_EQUAL | TOK_OR | TOK_PLUS | TOK_PLUS_EQUAL | TOK_PLUS_PLUS | TOK_SEMICOLON ->
        _menhir_reduce101 _menhir_env (Obj.magic _menhir_stack)
    | TOK_COLON ->
        _menhir_reduce4 _menhir_env (Obj.magic _menhir_stack)
    | _ ->
        assert (not _menhir_env._menhir_error);
        _menhir_env._menhir_error <- true;
        let _menhir_stack = Obj.magic _menhir_stack in
        let (_menhir_stack, _, _menhir_s, _, _) = _menhir_stack in
        _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s

and _menhir_run21 : _menhir_env -> 'ttv_tail -> _menhir_state -> Lexing.position -> 'ttv_return =
  fun _menhir_env _menhir_stack _menhir_s _startpos ->
    let _menhir_stack = (_menhir_stack, _menhir_s, _startpos) in
    let _menhir_env = _menhir_discard _menhir_env in
    let _tok = _menhir_env._menhir_token in
    match _tok with
    | TOK_LPAREN ->
        let _menhir_stack = Obj.magic _menhir_stack in
        let _startpos = _menhir_env._menhir_lexbuf.Lexing.lex_start_p in
        let _menhir_stack = (_menhir_stack, _startpos) in
        let _menhir_env = _menhir_discard _menhir_env in
        let _tok = _menhir_env._menhir_token in
        (match _tok with
        | TOK_FALSE ->
            _menhir_run43 _menhir_env (Obj.magic _menhir_stack) _menhir_env._menhir_lexbuf.Lexing.lex_curr_p MenhirState22 _menhir_env._menhir_lexbuf.Lexing.lex_start_p
        | TOK_LBRACKET ->
            _menhir_run35 _menhir_env (Obj.magic _menhir_stack) MenhirState22 _menhir_env._menhir_lexbuf.Lexing.lex_start_p
        | TOK_LPAREN ->
            _menhir_run34 _menhir_env (Obj.magic _menhir_stack) MenhirState22 _menhir_env._menhir_lexbuf.Lexing.lex_start_p
        | TOK_MINUS ->
            _menhir_run33 _menhir_env (Obj.magic _menhir_stack) MenhirState22 _menhir_env._menhir_lexbuf.Lexing.lex_start_p
        | TOK_MINUS_MINUS ->
            _menhir_run32 _menhir_env (Obj.magic _menhir_stack) _menhir_env._menhir_lexbuf.Lexing.lex_curr_p MenhirState22 _menhir_env._menhir_lexbuf.Lexing.lex_start_p
        | TOK_MULTIPLY ->
            _menhir_run30 _menhir_env (Obj.magic _menhir_stack) MenhirState22 _menhir_env._menhir_lexbuf.Lexing.lex_start_p
        | TOK_NOT ->
            _menhir_run29 _menhir_env (Obj.magic _menhir_stack) MenhirState22 _menhir_env._menhir_lexbuf.Lexing.lex_start_p
        | TOK_PLUS ->
            _menhir_run28 _menhir_env (Obj.magic _menhir_stack) MenhirState22 _menhir_env._menhir_lexbuf.Lexing.lex_start_p
        | TOK_PLUS_PLUS ->
            _menhir_run27 _menhir_env (Obj.magic _menhir_stack) _menhir_env._menhir_lexbuf.Lexing.lex_curr_p MenhirState22 _menhir_env._menhir_lexbuf.Lexing.lex_start_p
        | TOK_RANDOM ->
            _menhir_run26 _menhir_env (Obj.magic _menhir_stack) _menhir_env._menhir_lexbuf.Lexing.lex_curr_p MenhirState22 _menhir_env._menhir_lexbuf.Lexing.lex_start_p
        | TOK_TRUE ->
            _menhir_run25 _menhir_env (Obj.magic _menhir_stack) _menhir_env._menhir_lexbuf.Lexing.lex_curr_p MenhirState22 _menhir_env._menhir_lexbuf.Lexing.lex_start_p
        | TOK_URANDOM ->
            _menhir_run24 _menhir_env (Obj.magic _menhir_stack) _menhir_env._menhir_lexbuf.Lexing.lex_curr_p MenhirState22 _menhir_env._menhir_lexbuf.Lexing.lex_start_p
        | TOK_const _v ->
            _menhir_run20 _menhir_env (Obj.magic _menhir_stack) _menhir_env._menhir_lexbuf.Lexing.lex_curr_p MenhirState22 _v _menhir_env._menhir_lexbuf.Lexing.lex_start_p
        | TOK_id _v ->
            _menhir_run23 _menhir_env (Obj.magic _menhir_stack) _menhir_env._menhir_lexbuf.Lexing.lex_curr_p MenhirState22 _v _menhir_env._menhir_lexbuf.Lexing.lex_start_p
        | _ ->
            assert (not _menhir_env._menhir_error);
            _menhir_env._menhir_error <- true;
            _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) MenhirState22)
    | _ ->
        assert (not _menhir_env._menhir_error);
        _menhir_env._menhir_error <- true;
        let _menhir_stack = Obj.magic _menhir_stack in
        let (_menhir_stack, _menhir_s, _) = _menhir_stack in
        _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s

and _menhir_run121 : _menhir_env -> 'ttv_tail -> Lexing.position -> _menhir_state -> Lexing.position -> 'ttv_return =
  fun _menhir_env _menhir_stack _endpos _menhir_s _startpos ->
    let _menhir_env = _menhir_discard _menhir_env in
    let _menhir_stack = Obj.magic _menhir_stack in
    let _endpos__1_ = _endpos in
    let _startpos__1_ = _startpos in
    let _1 = () in
    let _startpos = _startpos__1_ in
    let _endpos = _endpos__1_ in
    let _v : (IntermediateSyntax.stmt) = 
# 138 "frontend/Parser.mly"
                              ( I_SKIP )
# 2924 "frontend/Parser.ml"
     in
    _menhir_goto_exp_stmt _menhir_env _menhir_stack _endpos _menhir_s _v _startpos

and _menhir_run122 : _menhir_env -> 'ttv_tail -> _menhir_state -> Lexing.position -> 'ttv_return =
  fun _menhir_env _menhir_stack _menhir_s _startpos ->
    let _menhir_stack = (_menhir_stack, _menhir_s, _startpos) in
    let _menhir_env = _menhir_discard _menhir_env in
    let _tok = _menhir_env._menhir_token in
    match _tok with
    | TOK_FALSE ->
        _menhir_run43 _menhir_env (Obj.magic _menhir_stack) _menhir_env._menhir_lexbuf.Lexing.lex_curr_p MenhirState122 _menhir_env._menhir_lexbuf.Lexing.lex_start_p
    | TOK_LBRACKET ->
        _menhir_run35 _menhir_env (Obj.magic _menhir_stack) MenhirState122 _menhir_env._menhir_lexbuf.Lexing.lex_start_p
    | TOK_LPAREN ->
        _menhir_run34 _menhir_env (Obj.magic _menhir_stack) MenhirState122 _menhir_env._menhir_lexbuf.Lexing.lex_start_p
    | TOK_MINUS ->
        _menhir_run33 _menhir_env (Obj.magic _menhir_stack) MenhirState122 _menhir_env._menhir_lexbuf.Lexing.lex_start_p
    | TOK_MINUS_MINUS ->
        _menhir_run32 _menhir_env (Obj.magic _menhir_stack) _menhir_env._menhir_lexbuf.Lexing.lex_curr_p MenhirState122 _menhir_env._menhir_lexbuf.Lexing.lex_start_p
    | TOK_MULTIPLY ->
        _menhir_run30 _menhir_env (Obj.magic _menhir_stack) MenhirState122 _menhir_env._menhir_lexbuf.Lexing.lex_start_p
    | TOK_NOT ->
        _menhir_run29 _menhir_env (Obj.magic _menhir_stack) MenhirState122 _menhir_env._menhir_lexbuf.Lexing.lex_start_p
    | TOK_PLUS ->
        _menhir_run28 _menhir_env (Obj.magic _menhir_stack) MenhirState122 _menhir_env._menhir_lexbuf.Lexing.lex_start_p
    | TOK_PLUS_PLUS ->
        _menhir_run27 _menhir_env (Obj.magic _menhir_stack) _menhir_env._menhir_lexbuf.Lexing.lex_curr_p MenhirState122 _menhir_env._menhir_lexbuf.Lexing.lex_start_p
    | TOK_RANDOM ->
        _menhir_run26 _menhir_env (Obj.magic _menhir_stack) _menhir_env._menhir_lexbuf.Lexing.lex_curr_p MenhirState122 _menhir_env._menhir_lexbuf.Lexing.lex_start_p
    | TOK_TRUE ->
        _menhir_run25 _menhir_env (Obj.magic _menhir_stack) _menhir_env._menhir_lexbuf.Lexing.lex_curr_p MenhirState122 _menhir_env._menhir_lexbuf.Lexing.lex_start_p
    | TOK_URANDOM ->
        _menhir_run24 _menhir_env (Obj.magic _menhir_stack) _menhir_env._menhir_lexbuf.Lexing.lex_curr_p MenhirState122 _menhir_env._menhir_lexbuf.Lexing.lex_start_p
    | TOK_const _v ->
        _menhir_run20 _menhir_env (Obj.magic _menhir_stack) _menhir_env._menhir_lexbuf.Lexing.lex_curr_p MenhirState122 _v _menhir_env._menhir_lexbuf.Lexing.lex_start_p
    | TOK_id _v ->
        _menhir_run23 _menhir_env (Obj.magic _menhir_stack) _menhir_env._menhir_lexbuf.Lexing.lex_curr_p MenhirState122 _v _menhir_env._menhir_lexbuf.Lexing.lex_start_p
    | TOK_SEMICOLON ->
        let _menhir_stack = Obj.magic _menhir_stack in
        let _menhir_s = MenhirState122 in
        let _v : (IntermediateSyntax.exp IntermediateSyntax.annotated option) = 
# 100 "/usr/share/menhir/standard.mly"
    ( None )
# 2968 "frontend/Parser.ml"
         in
        _menhir_goto_option_annotate_exp__ _menhir_env _menhir_stack _menhir_s _v
    | _ ->
        assert (not _menhir_env._menhir_error);
        _menhir_env._menhir_error <- true;
        _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) MenhirState122

and _menhir_run126 : _menhir_env -> 'ttv_tail -> _menhir_state -> Lexing.position -> 'ttv_return =
  fun _menhir_env _menhir_stack _menhir_s _startpos ->
    let _menhir_stack = (_menhir_stack, _menhir_s, _startpos) in
    let _menhir_env = _menhir_discard _menhir_env in
    let _tok = _menhir_env._menhir_token in
    match _tok with
    | TOK_LPAREN ->
        let _menhir_stack = Obj.magic _menhir_stack in
        let _startpos = _menhir_env._menhir_lexbuf.Lexing.lex_start_p in
        let _menhir_stack = (_menhir_stack, _startpos) in
        let _menhir_env = _menhir_discard _menhir_env in
        let _tok = _menhir_env._menhir_token in
        (match _tok with
        | TOK_FALSE ->
            _menhir_run43 _menhir_env (Obj.magic _menhir_stack) _menhir_env._menhir_lexbuf.Lexing.lex_curr_p MenhirState127 _menhir_env._menhir_lexbuf.Lexing.lex_start_p
        | TOK_LBRACKET ->
            _menhir_run35 _menhir_env (Obj.magic _menhir_stack) MenhirState127 _menhir_env._menhir_lexbuf.Lexing.lex_start_p
        | TOK_LPAREN ->
            _menhir_run34 _menhir_env (Obj.magic _menhir_stack) MenhirState127 _menhir_env._menhir_lexbuf.Lexing.lex_start_p
        | TOK_MINUS ->
            _menhir_run33 _menhir_env (Obj.magic _menhir_stack) MenhirState127 _menhir_env._menhir_lexbuf.Lexing.lex_start_p
        | TOK_MINUS_MINUS ->
            _menhir_run32 _menhir_env (Obj.magic _menhir_stack) _menhir_env._menhir_lexbuf.Lexing.lex_curr_p MenhirState127 _menhir_env._menhir_lexbuf.Lexing.lex_start_p
        | TOK_MULTIPLY ->
            _menhir_run30 _menhir_env (Obj.magic _menhir_stack) MenhirState127 _menhir_env._menhir_lexbuf.Lexing.lex_start_p
        | TOK_NOT ->
            _menhir_run29 _menhir_env (Obj.magic _menhir_stack) MenhirState127 _menhir_env._menhir_lexbuf.Lexing.lex_start_p
        | TOK_PLUS ->
            _menhir_run28 _menhir_env (Obj.magic _menhir_stack) MenhirState127 _menhir_env._menhir_lexbuf.Lexing.lex_start_p
        | TOK_PLUS_PLUS ->
            _menhir_run27 _menhir_env (Obj.magic _menhir_stack) _menhir_env._menhir_lexbuf.Lexing.lex_curr_p MenhirState127 _menhir_env._menhir_lexbuf.Lexing.lex_start_p
        | TOK_RANDOM ->
            _menhir_run26 _menhir_env (Obj.magic _menhir_stack) _menhir_env._menhir_lexbuf.Lexing.lex_curr_p MenhirState127 _menhir_env._menhir_lexbuf.Lexing.lex_start_p
        | TOK_TRUE ->
            _menhir_run25 _menhir_env (Obj.magic _menhir_stack) _menhir_env._menhir_lexbuf.Lexing.lex_curr_p MenhirState127 _menhir_env._menhir_lexbuf.Lexing.lex_start_p
        | TOK_URANDOM ->
            _menhir_run24 _menhir_env (Obj.magic _menhir_stack) _menhir_env._menhir_lexbuf.Lexing.lex_curr_p MenhirState127 _menhir_env._menhir_lexbuf.Lexing.lex_start_p
        | TOK_const _v ->
            _menhir_run20 _menhir_env (Obj.magic _menhir_stack) _menhir_env._menhir_lexbuf.Lexing.lex_curr_p MenhirState127 _v _menhir_env._menhir_lexbuf.Lexing.lex_start_p
        | TOK_id _v ->
            _menhir_run23 _menhir_env (Obj.magic _menhir_stack) _menhir_env._menhir_lexbuf.Lexing.lex_curr_p MenhirState127 _v _menhir_env._menhir_lexbuf.Lexing.lex_start_p
        | _ ->
            assert (not _menhir_env._menhir_error);
            _menhir_env._menhir_error <- true;
            _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) MenhirState127)
    | _ ->
        assert (not _menhir_env._menhir_error);
        _menhir_env._menhir_error <- true;
        let _menhir_stack = Obj.magic _menhir_stack in
        let (_menhir_stack, _menhir_s, _) = _menhir_stack in
        _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s

and _menhir_run130 : _menhir_env -> 'ttv_tail -> _menhir_state -> Lexing.position -> 'ttv_return =
  fun _menhir_env _menhir_stack _menhir_s _startpos ->
    let _menhir_stack = (_menhir_stack, _menhir_s, _startpos) in
    let _menhir_env = _menhir_discard _menhir_env in
    let _tok = _menhir_env._menhir_token in
    match _tok with
    | TOK_LPAREN ->
        let _menhir_stack = Obj.magic _menhir_stack in
        let _startpos = _menhir_env._menhir_lexbuf.Lexing.lex_start_p in
        let _menhir_stack = (_menhir_stack, _startpos) in
        let _menhir_env = _menhir_discard _menhir_env in
        let _tok = _menhir_env._menhir_token in
        (match _tok with
        | TOK_CHAR ->
            _menhir_run8 _menhir_env (Obj.magic _menhir_stack) _menhir_env._menhir_lexbuf.Lexing.lex_curr_p MenhirState131 _menhir_env._menhir_lexbuf.Lexing.lex_start_p
        | TOK_FALSE ->
            _menhir_run43 _menhir_env (Obj.magic _menhir_stack) _menhir_env._menhir_lexbuf.Lexing.lex_curr_p MenhirState131 _menhir_env._menhir_lexbuf.Lexing.lex_start_p
        | TOK_INT ->
            _menhir_run7 _menhir_env (Obj.magic _menhir_stack) _menhir_env._menhir_lexbuf.Lexing.lex_curr_p MenhirState131 _menhir_env._menhir_lexbuf.Lexing.lex_start_p
        | TOK_LBRACKET ->
            _menhir_run35 _menhir_env (Obj.magic _menhir_stack) MenhirState131 _menhir_env._menhir_lexbuf.Lexing.lex_start_p
        | TOK_LPAREN ->
            _menhir_run34 _menhir_env (Obj.magic _menhir_stack) MenhirState131 _menhir_env._menhir_lexbuf.Lexing.lex_start_p
        | TOK_MINUS ->
            _menhir_run33 _menhir_env (Obj.magic _menhir_stack) MenhirState131 _menhir_env._menhir_lexbuf.Lexing.lex_start_p
        | TOK_MINUS_MINUS ->
            _menhir_run32 _menhir_env (Obj.magic _menhir_stack) _menhir_env._menhir_lexbuf.Lexing.lex_curr_p MenhirState131 _menhir_env._menhir_lexbuf.Lexing.lex_start_p
        | TOK_MULTIPLY ->
            _menhir_run30 _menhir_env (Obj.magic _menhir_stack) MenhirState131 _menhir_env._menhir_lexbuf.Lexing.lex_start_p
        | TOK_NOT ->
            _menhir_run29 _menhir_env (Obj.magic _menhir_stack) MenhirState131 _menhir_env._menhir_lexbuf.Lexing.lex_start_p
        | TOK_PLUS ->
            _menhir_run28 _menhir_env (Obj.magic _menhir_stack) MenhirState131 _menhir_env._menhir_lexbuf.Lexing.lex_start_p
        | TOK_PLUS_PLUS ->
            _menhir_run27 _menhir_env (Obj.magic _menhir_stack) _menhir_env._menhir_lexbuf.Lexing.lex_curr_p MenhirState131 _menhir_env._menhir_lexbuf.Lexing.lex_start_p
        | TOK_RANDOM ->
            _menhir_run26 _menhir_env (Obj.magic _menhir_stack) _menhir_env._menhir_lexbuf.Lexing.lex_curr_p MenhirState131 _menhir_env._menhir_lexbuf.Lexing.lex_start_p
        | TOK_TRUE ->
            _menhir_run25 _menhir_env (Obj.magic _menhir_stack) _menhir_env._menhir_lexbuf.Lexing.lex_curr_p MenhirState131 _menhir_env._menhir_lexbuf.Lexing.lex_start_p
        | TOK_UINT ->
            _menhir_run5 _menhir_env (Obj.magic _menhir_stack) MenhirState131 _menhir_env._menhir_lexbuf.Lexing.lex_start_p
        | TOK_URANDOM ->
            _menhir_run24 _menhir_env (Obj.magic _menhir_stack) _menhir_env._menhir_lexbuf.Lexing.lex_curr_p MenhirState131 _menhir_env._menhir_lexbuf.Lexing.lex_start_p
        | TOK_const _v ->
            _menhir_run20 _menhir_env (Obj.magic _menhir_stack) _menhir_env._menhir_lexbuf.Lexing.lex_curr_p MenhirState131 _v _menhir_env._menhir_lexbuf.Lexing.lex_start_p
        | TOK_id _v ->
            _menhir_run23 _menhir_env (Obj.magic _menhir_stack) _menhir_env._menhir_lexbuf.Lexing.lex_curr_p MenhirState131 _v _menhir_env._menhir_lexbuf.Lexing.lex_start_p
        | _ ->
            assert (not _menhir_env._menhir_error);
            _menhir_env._menhir_error <- true;
            _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) MenhirState131)
    | _ ->
        assert (not _menhir_env._menhir_error);
        _menhir_env._menhir_error <- true;
        let _menhir_stack = Obj.magic _menhir_stack in
        let (_menhir_stack, _menhir_s, _) = _menhir_stack in
        _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s

and _menhir_run151 : _menhir_env -> 'ttv_tail -> _menhir_state -> Lexing.position -> 'ttv_return =
  fun _menhir_env _menhir_stack _menhir_s _startpos ->
    let _menhir_stack = (_menhir_stack, _menhir_s, _startpos) in
    let _menhir_env = _menhir_discard _menhir_env in
    let _tok = _menhir_env._menhir_token in
    match _tok with
    | TOK_LPAREN ->
        let _menhir_stack = Obj.magic _menhir_stack in
        let _startpos = _menhir_env._menhir_lexbuf.Lexing.lex_start_p in
        let _menhir_stack = (_menhir_stack, _startpos) in
        let _menhir_env = _menhir_discard _menhir_env in
        let _tok = _menhir_env._menhir_token in
        (match _tok with
        | TOK_FALSE ->
            _menhir_run43 _menhir_env (Obj.magic _menhir_stack) _menhir_env._menhir_lexbuf.Lexing.lex_curr_p MenhirState152 _menhir_env._menhir_lexbuf.Lexing.lex_start_p
        | TOK_LBRACKET ->
            _menhir_run35 _menhir_env (Obj.magic _menhir_stack) MenhirState152 _menhir_env._menhir_lexbuf.Lexing.lex_start_p
        | TOK_LPAREN ->
            _menhir_run34 _menhir_env (Obj.magic _menhir_stack) MenhirState152 _menhir_env._menhir_lexbuf.Lexing.lex_start_p
        | TOK_MINUS ->
            _menhir_run33 _menhir_env (Obj.magic _menhir_stack) MenhirState152 _menhir_env._menhir_lexbuf.Lexing.lex_start_p
        | TOK_MINUS_MINUS ->
            _menhir_run32 _menhir_env (Obj.magic _menhir_stack) _menhir_env._menhir_lexbuf.Lexing.lex_curr_p MenhirState152 _menhir_env._menhir_lexbuf.Lexing.lex_start_p
        | TOK_MULTIPLY ->
            _menhir_run30 _menhir_env (Obj.magic _menhir_stack) MenhirState152 _menhir_env._menhir_lexbuf.Lexing.lex_start_p
        | TOK_NOT ->
            _menhir_run29 _menhir_env (Obj.magic _menhir_stack) MenhirState152 _menhir_env._menhir_lexbuf.Lexing.lex_start_p
        | TOK_PLUS ->
            _menhir_run28 _menhir_env (Obj.magic _menhir_stack) MenhirState152 _menhir_env._menhir_lexbuf.Lexing.lex_start_p
        | TOK_PLUS_PLUS ->
            _menhir_run27 _menhir_env (Obj.magic _menhir_stack) _menhir_env._menhir_lexbuf.Lexing.lex_curr_p MenhirState152 _menhir_env._menhir_lexbuf.Lexing.lex_start_p
        | TOK_RANDOM ->
            _menhir_run26 _menhir_env (Obj.magic _menhir_stack) _menhir_env._menhir_lexbuf.Lexing.lex_curr_p MenhirState152 _menhir_env._menhir_lexbuf.Lexing.lex_start_p
        | TOK_TRUE ->
            _menhir_run25 _menhir_env (Obj.magic _menhir_stack) _menhir_env._menhir_lexbuf.Lexing.lex_curr_p MenhirState152 _menhir_env._menhir_lexbuf.Lexing.lex_start_p
        | TOK_URANDOM ->
            _menhir_run24 _menhir_env (Obj.magic _menhir_stack) _menhir_env._menhir_lexbuf.Lexing.lex_curr_p MenhirState152 _menhir_env._menhir_lexbuf.Lexing.lex_start_p
        | TOK_const _v ->
            _menhir_run20 _menhir_env (Obj.magic _menhir_stack) _menhir_env._menhir_lexbuf.Lexing.lex_curr_p MenhirState152 _v _menhir_env._menhir_lexbuf.Lexing.lex_start_p
        | TOK_id _v ->
            _menhir_run23 _menhir_env (Obj.magic _menhir_stack) _menhir_env._menhir_lexbuf.Lexing.lex_curr_p MenhirState152 _v _menhir_env._menhir_lexbuf.Lexing.lex_start_p
        | _ ->
            assert (not _menhir_env._menhir_error);
            _menhir_env._menhir_error <- true;
            _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) MenhirState152)
    | _ ->
        assert (not _menhir_env._menhir_error);
        _menhir_env._menhir_error <- true;
        let _menhir_stack = Obj.magic _menhir_stack in
        let (_menhir_stack, _menhir_s, _) = _menhir_stack in
        _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s

and _menhir_run155 : _menhir_env -> 'ttv_tail -> _menhir_state -> Lexing.position -> 'ttv_return =
  fun _menhir_env _menhir_stack _menhir_s _startpos ->
    let _menhir_stack = (_menhir_stack, _menhir_s, _startpos) in
    let _menhir_env = _menhir_discard _menhir_env in
    let _tok = _menhir_env._menhir_token in
    match _tok with
    | TOK_LPAREN ->
        let _menhir_stack = Obj.magic _menhir_stack in
        let _startpos = _menhir_env._menhir_lexbuf.Lexing.lex_start_p in
        let _menhir_stack = (_menhir_stack, _startpos) in
        let _menhir_env = _menhir_discard _menhir_env in
        let _tok = _menhir_env._menhir_token in
        (match _tok with
        | TOK_FALSE ->
            _menhir_run43 _menhir_env (Obj.magic _menhir_stack) _menhir_env._menhir_lexbuf.Lexing.lex_curr_p MenhirState156 _menhir_env._menhir_lexbuf.Lexing.lex_start_p
        | TOK_LBRACKET ->
            _menhir_run35 _menhir_env (Obj.magic _menhir_stack) MenhirState156 _menhir_env._menhir_lexbuf.Lexing.lex_start_p
        | TOK_LPAREN ->
            _menhir_run34 _menhir_env (Obj.magic _menhir_stack) MenhirState156 _menhir_env._menhir_lexbuf.Lexing.lex_start_p
        | TOK_MINUS ->
            _menhir_run33 _menhir_env (Obj.magic _menhir_stack) MenhirState156 _menhir_env._menhir_lexbuf.Lexing.lex_start_p
        | TOK_MINUS_MINUS ->
            _menhir_run32 _menhir_env (Obj.magic _menhir_stack) _menhir_env._menhir_lexbuf.Lexing.lex_curr_p MenhirState156 _menhir_env._menhir_lexbuf.Lexing.lex_start_p
        | TOK_MULTIPLY ->
            _menhir_run30 _menhir_env (Obj.magic _menhir_stack) MenhirState156 _menhir_env._menhir_lexbuf.Lexing.lex_start_p
        | TOK_NOT ->
            _menhir_run29 _menhir_env (Obj.magic _menhir_stack) MenhirState156 _menhir_env._menhir_lexbuf.Lexing.lex_start_p
        | TOK_PLUS ->
            _menhir_run28 _menhir_env (Obj.magic _menhir_stack) MenhirState156 _menhir_env._menhir_lexbuf.Lexing.lex_start_p
        | TOK_PLUS_PLUS ->
            _menhir_run27 _menhir_env (Obj.magic _menhir_stack) _menhir_env._menhir_lexbuf.Lexing.lex_curr_p MenhirState156 _menhir_env._menhir_lexbuf.Lexing.lex_start_p
        | TOK_RANDOM ->
            _menhir_run26 _menhir_env (Obj.magic _menhir_stack) _menhir_env._menhir_lexbuf.Lexing.lex_curr_p MenhirState156 _menhir_env._menhir_lexbuf.Lexing.lex_start_p
        | TOK_TRUE ->
            _menhir_run25 _menhir_env (Obj.magic _menhir_stack) _menhir_env._menhir_lexbuf.Lexing.lex_curr_p MenhirState156 _menhir_env._menhir_lexbuf.Lexing.lex_start_p
        | TOK_URANDOM ->
            _menhir_run24 _menhir_env (Obj.magic _menhir_stack) _menhir_env._menhir_lexbuf.Lexing.lex_curr_p MenhirState156 _menhir_env._menhir_lexbuf.Lexing.lex_start_p
        | TOK_const _v ->
            _menhir_run20 _menhir_env (Obj.magic _menhir_stack) _menhir_env._menhir_lexbuf.Lexing.lex_curr_p MenhirState156 _v _menhir_env._menhir_lexbuf.Lexing.lex_start_p
        | TOK_id _v ->
            _menhir_run23 _menhir_env (Obj.magic _menhir_stack) _menhir_env._menhir_lexbuf.Lexing.lex_curr_p MenhirState156 _v _menhir_env._menhir_lexbuf.Lexing.lex_start_p
        | _ ->
            assert (not _menhir_env._menhir_error);
            _menhir_env._menhir_error <- true;
            _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) MenhirState156)
    | _ ->
        assert (not _menhir_env._menhir_error);
        _menhir_env._menhir_error <- true;
        let _menhir_stack = Obj.magic _menhir_stack in
        let (_menhir_stack, _menhir_s, _) = _menhir_stack in
        _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s

and _menhir_goto_declarator : _menhir_env -> 'ttv_tail -> _menhir_state -> (IntermediateSyntax.declarator) -> 'ttv_return =
  fun _menhir_env _menhir_stack _menhir_s _v ->
    let _menhir_stack = (_menhir_stack, _menhir_s, _v) in
    let _menhir_stack = Obj.magic _menhir_stack in
    assert (not _menhir_env._menhir_error);
    let _tok = _menhir_env._menhir_token in
    match _tok with
    | TOK_COMMA ->
        let _menhir_stack = Obj.magic _menhir_stack in
        let _menhir_env = _menhir_discard _menhir_env in
        let _tok = _menhir_env._menhir_token in
        (match _tok with
        | TOK_id _v ->
            _menhir_run2 _menhir_env (Obj.magic _menhir_stack) _menhir_env._menhir_lexbuf.Lexing.lex_curr_p MenhirState139 _v _menhir_env._menhir_lexbuf.Lexing.lex_start_p
        | _ ->
            assert (not _menhir_env._menhir_error);
            _menhir_env._menhir_error <- true;
            _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) MenhirState139)
    | TOK_SEMICOLON ->
        let _menhir_stack = Obj.magic _menhir_stack in
        let (_menhir_stack, _menhir_s, (x : (IntermediateSyntax.declarator))) = _menhir_stack in
        let _v : (IntermediateSyntax.declarator list) = 
# 215 "/usr/share/menhir/standard.mly"
    ( [ x ] )
# 3214 "frontend/Parser.ml"
         in
        _menhir_goto_separated_nonempty_list_TOK_COMMA_declarator_ _menhir_env _menhir_stack _menhir_s _v
    | _ ->
        assert (not _menhir_env._menhir_error);
        _menhir_env._menhir_error <- true;
        let _menhir_stack = Obj.magic _menhir_stack in
        let (_menhir_stack, _menhir_s, _) = _menhir_stack in
        _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s

and _menhir_goto_global_decl : _menhir_env -> 'ttv_tail -> Lexing.position -> _menhir_state -> (IntermediateSyntax.globalDecl) -> Lexing.position -> 'ttv_return =
  fun _menhir_env _menhir_stack _endpos _menhir_s _v _startpos ->
    let _menhir_stack = Obj.magic _menhir_stack in
    let _menhir_stack = Obj.magic _menhir_stack in
    let _endpos_x_ = _endpos in
    let (x : (IntermediateSyntax.globalDecl)) = _v in
    let _startpos_x_ = _startpos in
    let _startpos = _startpos_x_ in
    let _endpos = _endpos_x_ in
    let _v : (IntermediateSyntax.globalDecl IntermediateSyntax.annotated) = let _endpos = _endpos_x_ in
    let _startpos = _startpos_x_ in
    
# 236 "frontend/Parser.mly"
          ( x, (_startpos, _endpos) )
# 3238 "frontend/Parser.ml"
     in
    let _menhir_stack = (_menhir_stack, _endpos, _menhir_s, _v, _startpos) in
    match _menhir_s with
    | MenhirState131 ->
        let _menhir_stack = Obj.magic _menhir_stack in
        assert (not _menhir_env._menhir_error);
        let _tok = _menhir_env._menhir_token in
        (match _tok with
        | TOK_FALSE ->
            _menhir_run43 _menhir_env (Obj.magic _menhir_stack) _menhir_env._menhir_lexbuf.Lexing.lex_curr_p MenhirState146 _menhir_env._menhir_lexbuf.Lexing.lex_start_p
        | TOK_LBRACKET ->
            _menhir_run35 _menhir_env (Obj.magic _menhir_stack) MenhirState146 _menhir_env._menhir_lexbuf.Lexing.lex_start_p
        | TOK_LPAREN ->
            _menhir_run34 _menhir_env (Obj.magic _menhir_stack) MenhirState146 _menhir_env._menhir_lexbuf.Lexing.lex_start_p
        | TOK_MINUS ->
            _menhir_run33 _menhir_env (Obj.magic _menhir_stack) MenhirState146 _menhir_env._menhir_lexbuf.Lexing.lex_start_p
        | TOK_MINUS_MINUS ->
            _menhir_run32 _menhir_env (Obj.magic _menhir_stack) _menhir_env._menhir_lexbuf.Lexing.lex_curr_p MenhirState146 _menhir_env._menhir_lexbuf.Lexing.lex_start_p
        | TOK_MULTIPLY ->
            _menhir_run30 _menhir_env (Obj.magic _menhir_stack) MenhirState146 _menhir_env._menhir_lexbuf.Lexing.lex_start_p
        | TOK_NOT ->
            _menhir_run29 _menhir_env (Obj.magic _menhir_stack) MenhirState146 _menhir_env._menhir_lexbuf.Lexing.lex_start_p
        | TOK_PLUS ->
            _menhir_run28 _menhir_env (Obj.magic _menhir_stack) MenhirState146 _menhir_env._menhir_lexbuf.Lexing.lex_start_p
        | TOK_PLUS_PLUS ->
            _menhir_run27 _menhir_env (Obj.magic _menhir_stack) _menhir_env._menhir_lexbuf.Lexing.lex_curr_p MenhirState146 _menhir_env._menhir_lexbuf.Lexing.lex_start_p
        | TOK_RANDOM ->
            _menhir_run26 _menhir_env (Obj.magic _menhir_stack) _menhir_env._menhir_lexbuf.Lexing.lex_curr_p MenhirState146 _menhir_env._menhir_lexbuf.Lexing.lex_start_p
        | TOK_TRUE ->
            _menhir_run25 _menhir_env (Obj.magic _menhir_stack) _menhir_env._menhir_lexbuf.Lexing.lex_curr_p MenhirState146 _menhir_env._menhir_lexbuf.Lexing.lex_start_p
        | TOK_URANDOM ->
            _menhir_run24 _menhir_env (Obj.magic _menhir_stack) _menhir_env._menhir_lexbuf.Lexing.lex_curr_p MenhirState146 _menhir_env._menhir_lexbuf.Lexing.lex_start_p
        | TOK_const _v ->
            _menhir_run20 _menhir_env (Obj.magic _menhir_stack) _menhir_env._menhir_lexbuf.Lexing.lex_curr_p MenhirState146 _v _menhir_env._menhir_lexbuf.Lexing.lex_start_p
        | TOK_id _v ->
            _menhir_run23 _menhir_env (Obj.magic _menhir_stack) _menhir_env._menhir_lexbuf.Lexing.lex_curr_p MenhirState146 _v _menhir_env._menhir_lexbuf.Lexing.lex_start_p
        | _ ->
            assert (not _menhir_env._menhir_error);
            _menhir_env._menhir_error <- true;
            _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) MenhirState146)
    | MenhirState18 | MenhirState193 | MenhirState120 | MenhirState129 | MenhirState188 | MenhirState185 | MenhirState150 | MenhirState154 | MenhirState171 ->
        let _menhir_stack = Obj.magic _menhir_stack in
        let _menhir_stack = Obj.magic _menhir_stack in
        let (_menhir_stack, _endpos_d_, _menhir_s, (d : (IntermediateSyntax.globalDecl IntermediateSyntax.annotated)), _startpos_d_) = _menhir_stack in
        let _startpos = _startpos_d_ in
        let _endpos = _endpos_d_ in
        let _v : (IntermediateSyntax.stmt) = 
# 159 "frontend/Parser.mly"
                             ( I_local d )
# 3288 "frontend/Parser.ml"
         in
        let _menhir_stack = Obj.magic _menhir_stack in
        let _menhir_stack = Obj.magic _menhir_stack in
        let _endpos_s_ = _endpos in
        let (s : (IntermediateSyntax.stmt)) = _v in
        let _startpos_s_ = _startpos in
        let _startpos = _startpos_s_ in
        let _endpos = _endpos_s_ in
        let _v : (IntermediateSyntax.stmt) = 
# 131 "frontend/Parser.mly"
                        ( s )
# 3300 "frontend/Parser.ml"
         in
        _menhir_goto_stmt _menhir_env _menhir_stack _endpos _menhir_s _v _startpos
    | MenhirState0 | MenhirState223 ->
        let _menhir_stack = Obj.magic _menhir_stack in
        let _menhir_stack = Obj.magic _menhir_stack in
        let (_menhir_stack, _endpos_d_, _menhir_s, (d : (IntermediateSyntax.globalDecl IntermediateSyntax.annotated)), _startpos_d_) = _menhir_stack in
        let _startpos = _startpos_d_ in
        let _endpos = _endpos_d_ in
        let _v : (IntermediateSyntax.decl) = 
# 82 "frontend/Parser.mly"
                              ( I_global d )
# 3312 "frontend/Parser.ml"
         in
        _menhir_goto_decl _menhir_env _menhir_stack _endpos _menhir_s _v _startpos
    | _ ->
        _menhir_fail ()

and _menhir_goto_option_unary_op_ : _menhir_env -> 'ttv_tail -> _menhir_state -> (IntermediateSyntax.unaryOp option) -> 'ttv_return =
  fun _menhir_env _menhir_stack _menhir_s _v ->
    let _menhir_stack = (_menhir_stack, _menhir_s, _v) in
    match _menhir_s with
    | MenhirState35 ->
        let _menhir_stack = Obj.magic _menhir_stack in
        assert (not _menhir_env._menhir_error);
        let _tok = _menhir_env._menhir_token in
        (match _tok with
        | TOK_const _v ->
            let _menhir_stack = Obj.magic _menhir_stack in
            let _endpos = _menhir_env._menhir_lexbuf.Lexing.lex_curr_p in
            let _startpos = _menhir_env._menhir_lexbuf.Lexing.lex_start_p in
            let _menhir_stack = (_menhir_stack, _endpos, _v, _startpos) in
            let _menhir_env = _menhir_discard _menhir_env in
            let _tok = _menhir_env._menhir_token in
            (match _tok with
            | TOK_COMMA ->
                let _menhir_stack = Obj.magic _menhir_stack in
                let _menhir_env = _menhir_discard _menhir_env in
                let _tok = _menhir_env._menhir_token in
                (match _tok with
                | TOK_MINUS ->
                    _menhir_run33 _menhir_env (Obj.magic _menhir_stack) MenhirState39 _menhir_env._menhir_lexbuf.Lexing.lex_start_p
                | TOK_PLUS ->
                    _menhir_run28 _menhir_env (Obj.magic _menhir_stack) MenhirState39 _menhir_env._menhir_lexbuf.Lexing.lex_start_p
                | TOK_const _ ->
                    _menhir_reduce90 _menhir_env (Obj.magic _menhir_stack) MenhirState39
                | _ ->
                    assert (not _menhir_env._menhir_error);
                    _menhir_env._menhir_error <- true;
                    _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) MenhirState39)
            | _ ->
                assert (not _menhir_env._menhir_error);
                _menhir_env._menhir_error <- true;
                let _menhir_stack = Obj.magic _menhir_stack in
                let ((_menhir_stack, _menhir_s, _), _, _, _) = _menhir_stack in
                _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s)
        | _ ->
            assert (not _menhir_env._menhir_error);
            _menhir_env._menhir_error <- true;
            let _menhir_stack = Obj.magic _menhir_stack in
            let (_menhir_stack, _menhir_s, _) = _menhir_stack in
            _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s)
    | MenhirState39 ->
        let _menhir_stack = Obj.magic _menhir_stack in
        assert (not _menhir_env._menhir_error);
        let _tok = _menhir_env._menhir_token in
        (match _tok with
        | TOK_const _v ->
            let _menhir_stack = Obj.magic _menhir_stack in
            let _endpos = _menhir_env._menhir_lexbuf.Lexing.lex_curr_p in
            let _startpos = _menhir_env._menhir_lexbuf.Lexing.lex_start_p in
            let _menhir_stack = (_menhir_stack, _endpos, _v, _startpos) in
            let _menhir_env = _menhir_discard _menhir_env in
            let _tok = _menhir_env._menhir_token in
            (match _tok with
            | TOK_RBRACKET ->
                let _menhir_stack = Obj.magic _menhir_stack in
                let _endpos = _menhir_env._menhir_lexbuf.Lexing.lex_curr_p in
                let _menhir_env = _menhir_discard _menhir_env in
                let _menhir_stack = Obj.magic _menhir_stack in
                let _endpos__7_ = _endpos in
                let (((((_menhir_stack, _menhir_s, _startpos__1_), _, (o1 : (IntermediateSyntax.unaryOp option))), _endpos_e1_, (e1 : (
# 71 "frontend/Parser.mly"
       (string)
# 3384 "frontend/Parser.ml"
                )), _startpos_e1_), _, (o2 : (IntermediateSyntax.unaryOp option))), _endpos_e2_, (e2 : (
# 71 "frontend/Parser.mly"
       (string)
# 3388 "frontend/Parser.ml"
                )), _startpos_e2_) = _menhir_stack in
                let _7 = () in
                let _4 = () in
                let _1 = () in
                let _startpos = _startpos__1_ in
                let _endpos = _endpos__7_ in
                let _v : (IntermediateSyntax.exp) = 
# 232 "frontend/Parser.mly"
                                                                                                               ( I_interval (o1,e1,o2,e2) )
# 3398 "frontend/Parser.ml"
                 in
                _menhir_goto_primary_exp _menhir_env _menhir_stack _endpos _menhir_s _v _startpos
            | _ ->
                assert (not _menhir_env._menhir_error);
                _menhir_env._menhir_error <- true;
                let _menhir_stack = Obj.magic _menhir_stack in
                let ((_menhir_stack, _menhir_s, _), _, _, _) = _menhir_stack in
                _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s)
        | _ ->
            assert (not _menhir_env._menhir_error);
            _menhir_env._menhir_error <- true;
            let _menhir_stack = Obj.magic _menhir_stack in
            let (_menhir_stack, _menhir_s, _) = _menhir_stack in
            _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s)
    | _ ->
        _menhir_fail ()

and _menhir_goto_postfix_exp : _menhir_env -> 'ttv_tail -> Lexing.position -> _menhir_state -> (IntermediateSyntax.exp) -> Lexing.position -> 'ttv_return =
  fun _menhir_env _menhir_stack _endpos _menhir_s _v _startpos ->
    let _menhir_stack = (_menhir_stack, _endpos, _menhir_s, _v, _startpos) in
    let _menhir_stack = Obj.magic _menhir_stack in
    assert (not _menhir_env._menhir_error);
    let _tok = _menhir_env._menhir_token in
    match _tok with
    | TOK_AND | TOK_CHAR | TOK_COMMA | TOK_CPP_DEFINE | TOK_DIVIDE | TOK_DIVIDE_EQUAL | TOK_EOF | TOK_EQUAL | TOK_EQUAL_EQUAL | TOK_FEAT | TOK_GREATER | TOK_GREATER_EQUAL | TOK_INT | TOK_LESS | TOK_LESS_EQUAL | TOK_MINUS | TOK_MINUS_EQUAL | TOK_MODULO | TOK_MODULO_EQUAL | TOK_MULTIPLY | TOK_MULTIPLY_EQUAL | TOK_NOT_EQUAL | TOK_OR | TOK_PLUS | TOK_PLUS_EQUAL | TOK_RPAREN | TOK_SEMICOLON | TOK_UINT | TOK_VOID | TOK_id _ ->
        let _menhir_stack = Obj.magic _menhir_stack in
        let (_menhir_stack, _endpos_e_, _menhir_s, (e : (IntermediateSyntax.exp)), _startpos_e_) = _menhir_stack in
        let _startpos = _startpos_e_ in
        let _endpos = _endpos_e_ in
        let _v : (IntermediateSyntax.exp) = 
# 208 "frontend/Parser.mly"
                         ( e )
# 3431 "frontend/Parser.ml"
         in
        _menhir_goto_unary_exp _menhir_env _menhir_stack _endpos _menhir_s _v _startpos
    | TOK_LPAREN | TOK_MINUS_MINUS | TOK_PLUS_PLUS ->
        let _menhir_stack = Obj.magic _menhir_stack in
        let (_menhir_stack, _endpos_x_, _menhir_s, (x : (IntermediateSyntax.exp)), _startpos_x_) = _menhir_stack in
        let _startpos = _startpos_x_ in
        let _v : (IntermediateSyntax.exp IntermediateSyntax.annotated) = let _endpos = _endpos_x_ in
        let _startpos = _startpos_x_ in
        
# 236 "frontend/Parser.mly"
          ( x, (_startpos, _endpos) )
# 3443 "frontend/Parser.ml"
         in
        let _menhir_stack = (_menhir_stack, _menhir_s, _v, _startpos) in
        let _menhir_stack = Obj.magic _menhir_stack in
        assert (not _menhir_env._menhir_error);
        let _tok = _menhir_env._menhir_token in
        (match _tok with
        | TOK_LPAREN ->
            let _menhir_stack = Obj.magic _menhir_stack in
            let _startpos = _menhir_env._menhir_lexbuf.Lexing.lex_start_p in
            let _menhir_stack = (_menhir_stack, _startpos) in
            let _menhir_env = _menhir_discard _menhir_env in
            let _tok = _menhir_env._menhir_token in
            (match _tok with
            | TOK_FALSE ->
                _menhir_run43 _menhir_env (Obj.magic _menhir_stack) _menhir_env._menhir_lexbuf.Lexing.lex_curr_p MenhirState52 _menhir_env._menhir_lexbuf.Lexing.lex_start_p
            | TOK_LBRACKET ->
                _menhir_run35 _menhir_env (Obj.magic _menhir_stack) MenhirState52 _menhir_env._menhir_lexbuf.Lexing.lex_start_p
            | TOK_LPAREN ->
                _menhir_run34 _menhir_env (Obj.magic _menhir_stack) MenhirState52 _menhir_env._menhir_lexbuf.Lexing.lex_start_p
            | TOK_MINUS ->
                _menhir_run33 _menhir_env (Obj.magic _menhir_stack) MenhirState52 _menhir_env._menhir_lexbuf.Lexing.lex_start_p
            | TOK_MINUS_MINUS ->
                _menhir_run32 _menhir_env (Obj.magic _menhir_stack) _menhir_env._menhir_lexbuf.Lexing.lex_curr_p MenhirState52 _menhir_env._menhir_lexbuf.Lexing.lex_start_p
            | TOK_MULTIPLY ->
                _menhir_run30 _menhir_env (Obj.magic _menhir_stack) MenhirState52 _menhir_env._menhir_lexbuf.Lexing.lex_start_p
            | TOK_NOT ->
                _menhir_run29 _menhir_env (Obj.magic _menhir_stack) MenhirState52 _menhir_env._menhir_lexbuf.Lexing.lex_start_p
            | TOK_PLUS ->
                _menhir_run28 _menhir_env (Obj.magic _menhir_stack) MenhirState52 _menhir_env._menhir_lexbuf.Lexing.lex_start_p
            | TOK_PLUS_PLUS ->
                _menhir_run27 _menhir_env (Obj.magic _menhir_stack) _menhir_env._menhir_lexbuf.Lexing.lex_curr_p MenhirState52 _menhir_env._menhir_lexbuf.Lexing.lex_start_p
            | TOK_RANDOM ->
                _menhir_run26 _menhir_env (Obj.magic _menhir_stack) _menhir_env._menhir_lexbuf.Lexing.lex_curr_p MenhirState52 _menhir_env._menhir_lexbuf.Lexing.lex_start_p
            | TOK_TRUE ->
                _menhir_run25 _menhir_env (Obj.magic _menhir_stack) _menhir_env._menhir_lexbuf.Lexing.lex_curr_p MenhirState52 _menhir_env._menhir_lexbuf.Lexing.lex_start_p
            | TOK_URANDOM ->
                _menhir_run24 _menhir_env (Obj.magic _menhir_stack) _menhir_env._menhir_lexbuf.Lexing.lex_curr_p MenhirState52 _menhir_env._menhir_lexbuf.Lexing.lex_start_p
            | TOK_const _v ->
                _menhir_run20 _menhir_env (Obj.magic _menhir_stack) _menhir_env._menhir_lexbuf.Lexing.lex_curr_p MenhirState52 _v _menhir_env._menhir_lexbuf.Lexing.lex_start_p
            | TOK_id _v ->
                _menhir_run23 _menhir_env (Obj.magic _menhir_stack) _menhir_env._menhir_lexbuf.Lexing.lex_curr_p MenhirState52 _v _menhir_env._menhir_lexbuf.Lexing.lex_start_p
            | TOK_RPAREN ->
                let _menhir_stack = Obj.magic _menhir_stack in
                let _menhir_s = MenhirState52 in
                let _v : (IntermediateSyntax.exp IntermediateSyntax.annotated list) = 
# 128 "/usr/share/menhir/standard.mly"
    ( [] )
# 3491 "frontend/Parser.ml"
                 in
                _menhir_goto_loption_separated_nonempty_list_TOK_COMMA_annotate_exp___ _menhir_env _menhir_stack _menhir_s _v
            | _ ->
                assert (not _menhir_env._menhir_error);
                _menhir_env._menhir_error <- true;
                _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) MenhirState52)
        | TOK_MINUS_MINUS ->
            let _menhir_stack = Obj.magic _menhir_stack in
            let _endpos = _menhir_env._menhir_lexbuf.Lexing.lex_curr_p in
            let _startpos = _menhir_env._menhir_lexbuf.Lexing.lex_start_p in
            let _menhir_env = _menhir_discard _menhir_env in
            let _menhir_stack = Obj.magic _menhir_stack in
            let _endpos__2_ = _endpos in
            let _startpos__2_ = _startpos in
            let (_menhir_stack, _menhir_s, (e : (IntermediateSyntax.exp IntermediateSyntax.annotated)), _startpos_e_) = _menhir_stack in
            let _2 = () in
            let _startpos = _startpos_e_ in
            let _endpos = _endpos__2_ in
            let _v : (IntermediateSyntax.exp) = 
# 221 "frontend/Parser.mly"
                                                          ( I_decr e )
# 3513 "frontend/Parser.ml"
             in
            _menhir_goto_postfix_exp _menhir_env _menhir_stack _endpos _menhir_s _v _startpos
        | TOK_PLUS_PLUS ->
            let _menhir_stack = Obj.magic _menhir_stack in
            let _endpos = _menhir_env._menhir_lexbuf.Lexing.lex_curr_p in
            let _startpos = _menhir_env._menhir_lexbuf.Lexing.lex_start_p in
            let _menhir_env = _menhir_discard _menhir_env in
            let _menhir_stack = Obj.magic _menhir_stack in
            let _endpos__2_ = _endpos in
            let _startpos__2_ = _startpos in
            let (_menhir_stack, _menhir_s, (e : (IntermediateSyntax.exp IntermediateSyntax.annotated)), _startpos_e_) = _menhir_stack in
            let _2 = () in
            let _startpos = _startpos_e_ in
            let _endpos = _endpos__2_ in
            let _v : (IntermediateSyntax.exp) = 
# 220 "frontend/Parser.mly"
                                                        ( I_incr e )
# 3531 "frontend/Parser.ml"
             in
            _menhir_goto_postfix_exp _menhir_env _menhir_stack _endpos _menhir_s _v _startpos
        | _ ->
            assert (not _menhir_env._menhir_error);
            _menhir_env._menhir_error <- true;
            let _menhir_stack = Obj.magic _menhir_stack in
            let (_menhir_stack, _menhir_s, _, _) = _menhir_stack in
            _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s)
    | _ ->
        assert (not _menhir_env._menhir_error);
        _menhir_env._menhir_error <- true;
        let _menhir_stack = Obj.magic _menhir_stack in
        let (_menhir_stack, _, _menhir_s, _, _) = _menhir_stack in
        _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s

and _menhir_goto_global_feature : _menhir_env -> 'ttv_tail -> Lexing.position -> _menhir_state -> (IntermediateSyntax.globalFeature) -> Lexing.position -> 'ttv_return =
  fun _menhir_env _menhir_stack _endpos _menhir_s _v _startpos ->
    let _menhir_stack = Obj.magic _menhir_stack in
    let _menhir_stack = Obj.magic _menhir_stack in
    let _endpos_x_ = _endpos in
    let (x : (IntermediateSyntax.globalFeature)) = _v in
    let _startpos_x_ = _startpos in
    let _startpos = _startpos_x_ in
    let _endpos = _endpos_x_ in
    let _v : (IntermediateSyntax.globalFeature IntermediateSyntax.annotated) = let _endpos = _endpos_x_ in
    let _startpos = _startpos_x_ in
    
# 236 "frontend/Parser.mly"
          ( x, (_startpos, _endpos) )
# 3561 "frontend/Parser.ml"
     in
    let _menhir_stack = Obj.magic _menhir_stack in
    let _menhir_stack = Obj.magic _menhir_stack in
    let _endpos_d_ = _endpos in
    let (d : (IntermediateSyntax.globalFeature IntermediateSyntax.annotated)) = _v in
    let _startpos_d_ = _startpos in
    let _startpos = _startpos_d_ in
    let _endpos = _endpos_d_ in
    let _v : (IntermediateSyntax.decl) = 
# 84 "frontend/Parser.mly"
                                 ( I_feature d )
# 3573 "frontend/Parser.ml"
     in
    _menhir_goto_decl _menhir_env _menhir_stack _endpos _menhir_s _v _startpos

and _menhir_goto_function_decl : _menhir_env -> 'ttv_tail -> Lexing.position -> _menhir_state -> (IntermediateSyntax.functionDecl) -> Lexing.position -> 'ttv_return =
  fun _menhir_env _menhir_stack _endpos _menhir_s _v _startpos ->
    let _menhir_stack = Obj.magic _menhir_stack in
    let _menhir_stack = Obj.magic _menhir_stack in
    let _endpos_x_ = _endpos in
    let (x : (IntermediateSyntax.functionDecl)) = _v in
    let _startpos_x_ = _startpos in
    let _startpos = _startpos_x_ in
    let _endpos = _endpos_x_ in
    let _v : (IntermediateSyntax.functionDecl IntermediateSyntax.annotated) = let _endpos = _endpos_x_ in
    let _startpos = _startpos_x_ in
    
# 236 "frontend/Parser.mly"
          ( x, (_startpos, _endpos) )
# 3591 "frontend/Parser.ml"
     in
    let _menhir_stack = Obj.magic _menhir_stack in
    let _menhir_stack = Obj.magic _menhir_stack in
    let _endpos_d_ = _endpos in
    let (d : (IntermediateSyntax.functionDecl IntermediateSyntax.annotated)) = _v in
    let _startpos_d_ = _startpos in
    let _startpos = _startpos_d_ in
    let _endpos = _endpos_d_ in
    let _v : (IntermediateSyntax.decl) = 
# 85 "frontend/Parser.mly"
                               ( I_function d )
# 3603 "frontend/Parser.ml"
     in
    _menhir_goto_decl _menhir_env _menhir_stack _endpos _menhir_s _v _startpos

and _menhir_run18 : _menhir_env -> 'ttv_tail -> _menhir_state -> Lexing.position -> 'ttv_return =
  fun _menhir_env _menhir_stack _menhir_s _startpos ->
    let _menhir_stack = (_menhir_stack, _menhir_s, _startpos) in
    let _menhir_env = _menhir_discard _menhir_env in
    let _tok = _menhir_env._menhir_token in
    match _tok with
    | TOK_ASSERT ->
        _menhir_run155 _menhir_env (Obj.magic _menhir_stack) MenhirState18 _menhir_env._menhir_lexbuf.Lexing.lex_start_p
    | TOK_CHAR ->
        _menhir_run8 _menhir_env (Obj.magic _menhir_stack) _menhir_env._menhir_lexbuf.Lexing.lex_curr_p MenhirState18 _menhir_env._menhir_lexbuf.Lexing.lex_start_p
    | TOK_CPP_IF ->
        _menhir_run151 _menhir_env (Obj.magic _menhir_stack) MenhirState18 _menhir_env._menhir_lexbuf.Lexing.lex_start_p
    | TOK_FALSE ->
        _menhir_run43 _menhir_env (Obj.magic _menhir_stack) _menhir_env._menhir_lexbuf.Lexing.lex_curr_p MenhirState18 _menhir_env._menhir_lexbuf.Lexing.lex_start_p
    | TOK_FOR ->
        _menhir_run130 _menhir_env (Obj.magic _menhir_stack) MenhirState18 _menhir_env._menhir_lexbuf.Lexing.lex_start_p
    | TOK_IF ->
        _menhir_run126 _menhir_env (Obj.magic _menhir_stack) MenhirState18 _menhir_env._menhir_lexbuf.Lexing.lex_start_p
    | TOK_INT ->
        _menhir_run7 _menhir_env (Obj.magic _menhir_stack) _menhir_env._menhir_lexbuf.Lexing.lex_curr_p MenhirState18 _menhir_env._menhir_lexbuf.Lexing.lex_start_p
    | TOK_LBRACKET ->
        _menhir_run35 _menhir_env (Obj.magic _menhir_stack) MenhirState18 _menhir_env._menhir_lexbuf.Lexing.lex_start_p
    | TOK_LCURLY ->
        _menhir_run18 _menhir_env (Obj.magic _menhir_stack) MenhirState18 _menhir_env._menhir_lexbuf.Lexing.lex_start_p
    | TOK_LPAREN ->
        _menhir_run34 _menhir_env (Obj.magic _menhir_stack) MenhirState18 _menhir_env._menhir_lexbuf.Lexing.lex_start_p
    | TOK_MINUS ->
        _menhir_run33 _menhir_env (Obj.magic _menhir_stack) MenhirState18 _menhir_env._menhir_lexbuf.Lexing.lex_start_p
    | TOK_MINUS_MINUS ->
        _menhir_run32 _menhir_env (Obj.magic _menhir_stack) _menhir_env._menhir_lexbuf.Lexing.lex_curr_p MenhirState18 _menhir_env._menhir_lexbuf.Lexing.lex_start_p
    | TOK_MULTIPLY ->
        _menhir_run30 _menhir_env (Obj.magic _menhir_stack) MenhirState18 _menhir_env._menhir_lexbuf.Lexing.lex_start_p
    | TOK_NOT ->
        _menhir_run29 _menhir_env (Obj.magic _menhir_stack) MenhirState18 _menhir_env._menhir_lexbuf.Lexing.lex_start_p
    | TOK_PLUS ->
        _menhir_run28 _menhir_env (Obj.magic _menhir_stack) MenhirState18 _menhir_env._menhir_lexbuf.Lexing.lex_start_p
    | TOK_PLUS_PLUS ->
        _menhir_run27 _menhir_env (Obj.magic _menhir_stack) _menhir_env._menhir_lexbuf.Lexing.lex_curr_p MenhirState18 _menhir_env._menhir_lexbuf.Lexing.lex_start_p
    | TOK_RANDOM ->
        _menhir_run26 _menhir_env (Obj.magic _menhir_stack) _menhir_env._menhir_lexbuf.Lexing.lex_curr_p MenhirState18 _menhir_env._menhir_lexbuf.Lexing.lex_start_p
    | TOK_RETURN ->
        _menhir_run122 _menhir_env (Obj.magic _menhir_stack) MenhirState18 _menhir_env._menhir_lexbuf.Lexing.lex_start_p
    | TOK_SEMICOLON ->
        _menhir_run121 _menhir_env (Obj.magic _menhir_stack) _menhir_env._menhir_lexbuf.Lexing.lex_curr_p MenhirState18 _menhir_env._menhir_lexbuf.Lexing.lex_start_p
    | TOK_TRUE ->
        _menhir_run25 _menhir_env (Obj.magic _menhir_stack) _menhir_env._menhir_lexbuf.Lexing.lex_curr_p MenhirState18 _menhir_env._menhir_lexbuf.Lexing.lex_start_p
    | TOK_UINT ->
        _menhir_run5 _menhir_env (Obj.magic _menhir_stack) MenhirState18 _menhir_env._menhir_lexbuf.Lexing.lex_start_p
    | TOK_URANDOM ->
        _menhir_run24 _menhir_env (Obj.magic _menhir_stack) _menhir_env._menhir_lexbuf.Lexing.lex_curr_p MenhirState18 _menhir_env._menhir_lexbuf.Lexing.lex_start_p
    | TOK_WHILE ->
        _menhir_run21 _menhir_env (Obj.magic _menhir_stack) MenhirState18 _menhir_env._menhir_lexbuf.Lexing.lex_start_p
    | TOK_const _v ->
        _menhir_run20 _menhir_env (Obj.magic _menhir_stack) _menhir_env._menhir_lexbuf.Lexing.lex_curr_p MenhirState18 _v _menhir_env._menhir_lexbuf.Lexing.lex_start_p
    | TOK_id _v ->
        _menhir_run19 _menhir_env (Obj.magic _menhir_stack) _menhir_env._menhir_lexbuf.Lexing.lex_curr_p MenhirState18 _v _menhir_env._menhir_lexbuf.Lexing.lex_start_p
    | TOK_RCURLY ->
        _menhir_reduce70 _menhir_env (Obj.magic _menhir_stack) MenhirState18
    | _ ->
        assert (not _menhir_env._menhir_error);
        _menhir_env._menhir_error <- true;
        _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) MenhirState18

and _menhir_goto_stmt : _menhir_env -> 'ttv_tail -> Lexing.position -> _menhir_state -> (IntermediateSyntax.stmt) -> Lexing.position -> 'ttv_return =
  fun _menhir_env _menhir_stack _endpos _menhir_s _v _startpos ->
    let _menhir_stack = Obj.magic _menhir_stack in
    let _menhir_stack = Obj.magic _menhir_stack in
    let _endpos_x_ = _endpos in
    let (x : (IntermediateSyntax.stmt)) = _v in
    let _startpos_x_ = _startpos in
    let _endpos = _endpos_x_ in
    let _v : (IntermediateSyntax.stmt IntermediateSyntax.annotated) = let _endpos = _endpos_x_ in
    let _startpos = _startpos_x_ in
    
# 236 "frontend/Parser.mly"
          ( x, (_startpos, _endpos) )
# 3683 "frontend/Parser.ml"
     in
    let _menhir_stack = (_menhir_stack, _endpos, _menhir_s, _v) in
    match _menhir_s with
    | MenhirState154 ->
        let _menhir_stack = Obj.magic _menhir_stack in
        assert (not _menhir_env._menhir_error);
        let _tok = _menhir_env._menhir_token in
        (match _tok with
        | TOK_CPP_ELSE ->
            let _menhir_stack = Obj.magic _menhir_stack in
            let _menhir_env = _menhir_discard _menhir_env in
            let _tok = _menhir_env._menhir_token in
            (match _tok with
            | TOK_ASSERT ->
                _menhir_run155 _menhir_env (Obj.magic _menhir_stack) MenhirState171 _menhir_env._menhir_lexbuf.Lexing.lex_start_p
            | TOK_CHAR ->
                _menhir_run8 _menhir_env (Obj.magic _menhir_stack) _menhir_env._menhir_lexbuf.Lexing.lex_curr_p MenhirState171 _menhir_env._menhir_lexbuf.Lexing.lex_start_p
            | TOK_CPP_IF ->
                _menhir_run151 _menhir_env (Obj.magic _menhir_stack) MenhirState171 _menhir_env._menhir_lexbuf.Lexing.lex_start_p
            | TOK_FALSE ->
                _menhir_run43 _menhir_env (Obj.magic _menhir_stack) _menhir_env._menhir_lexbuf.Lexing.lex_curr_p MenhirState171 _menhir_env._menhir_lexbuf.Lexing.lex_start_p
            | TOK_FOR ->
                _menhir_run130 _menhir_env (Obj.magic _menhir_stack) MenhirState171 _menhir_env._menhir_lexbuf.Lexing.lex_start_p
            | TOK_IF ->
                _menhir_run126 _menhir_env (Obj.magic _menhir_stack) MenhirState171 _menhir_env._menhir_lexbuf.Lexing.lex_start_p
            | TOK_INT ->
                _menhir_run7 _menhir_env (Obj.magic _menhir_stack) _menhir_env._menhir_lexbuf.Lexing.lex_curr_p MenhirState171 _menhir_env._menhir_lexbuf.Lexing.lex_start_p
            | TOK_LBRACKET ->
                _menhir_run35 _menhir_env (Obj.magic _menhir_stack) MenhirState171 _menhir_env._menhir_lexbuf.Lexing.lex_start_p
            | TOK_LCURLY ->
                _menhir_run18 _menhir_env (Obj.magic _menhir_stack) MenhirState171 _menhir_env._menhir_lexbuf.Lexing.lex_start_p
            | TOK_LPAREN ->
                _menhir_run34 _menhir_env (Obj.magic _menhir_stack) MenhirState171 _menhir_env._menhir_lexbuf.Lexing.lex_start_p
            | TOK_MINUS ->
                _menhir_run33 _menhir_env (Obj.magic _menhir_stack) MenhirState171 _menhir_env._menhir_lexbuf.Lexing.lex_start_p
            | TOK_MINUS_MINUS ->
                _menhir_run32 _menhir_env (Obj.magic _menhir_stack) _menhir_env._menhir_lexbuf.Lexing.lex_curr_p MenhirState171 _menhir_env._menhir_lexbuf.Lexing.lex_start_p
            | TOK_MULTIPLY ->
                _menhir_run30 _menhir_env (Obj.magic _menhir_stack) MenhirState171 _menhir_env._menhir_lexbuf.Lexing.lex_start_p
            | TOK_NOT ->
                _menhir_run29 _menhir_env (Obj.magic _menhir_stack) MenhirState171 _menhir_env._menhir_lexbuf.Lexing.lex_start_p
            | TOK_PLUS ->
                _menhir_run28 _menhir_env (Obj.magic _menhir_stack) MenhirState171 _menhir_env._menhir_lexbuf.Lexing.lex_start_p
            | TOK_PLUS_PLUS ->
                _menhir_run27 _menhir_env (Obj.magic _menhir_stack) _menhir_env._menhir_lexbuf.Lexing.lex_curr_p MenhirState171 _menhir_env._menhir_lexbuf.Lexing.lex_start_p
            | TOK_RANDOM ->
                _menhir_run26 _menhir_env (Obj.magic _menhir_stack) _menhir_env._menhir_lexbuf.Lexing.lex_curr_p MenhirState171 _menhir_env._menhir_lexbuf.Lexing.lex_start_p
            | TOK_RETURN ->
                _menhir_run122 _menhir_env (Obj.magic _menhir_stack) MenhirState171 _menhir_env._menhir_lexbuf.Lexing.lex_start_p
            | TOK_SEMICOLON ->
                _menhir_run121 _menhir_env (Obj.magic _menhir_stack) _menhir_env._menhir_lexbuf.Lexing.lex_curr_p MenhirState171 _menhir_env._menhir_lexbuf.Lexing.lex_start_p
            | TOK_TRUE ->
                _menhir_run25 _menhir_env (Obj.magic _menhir_stack) _menhir_env._menhir_lexbuf.Lexing.lex_curr_p MenhirState171 _menhir_env._menhir_lexbuf.Lexing.lex_start_p
            | TOK_UINT ->
                _menhir_run5 _menhir_env (Obj.magic _menhir_stack) MenhirState171 _menhir_env._menhir_lexbuf.Lexing.lex_start_p
            | TOK_URANDOM ->
                _menhir_run24 _menhir_env (Obj.magic _menhir_stack) _menhir_env._menhir_lexbuf.Lexing.lex_curr_p MenhirState171 _menhir_env._menhir_lexbuf.Lexing.lex_start_p
            | TOK_WHILE ->
                _menhir_run21 _menhir_env (Obj.magic _menhir_stack) MenhirState171 _menhir_env._menhir_lexbuf.Lexing.lex_start_p
            | TOK_const _v ->
                _menhir_run20 _menhir_env (Obj.magic _menhir_stack) _menhir_env._menhir_lexbuf.Lexing.lex_curr_p MenhirState171 _v _menhir_env._menhir_lexbuf.Lexing.lex_start_p
            | TOK_id _v ->
                _menhir_run19 _menhir_env (Obj.magic _menhir_stack) _menhir_env._menhir_lexbuf.Lexing.lex_curr_p MenhirState171 _v _menhir_env._menhir_lexbuf.Lexing.lex_start_p
            | _ ->
                assert (not _menhir_env._menhir_error);
                _menhir_env._menhir_error <- true;
                _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) MenhirState171)
        | TOK_CPP_ENDIF ->
            let _menhir_stack = Obj.magic _menhir_stack in
            let _endpos = _menhir_env._menhir_lexbuf.Lexing.lex_curr_p in
            let _menhir_env = _menhir_discard _menhir_env in
            let _menhir_stack = Obj.magic _menhir_stack in
            let _endpos__6_ = _endpos in
            let (((((_menhir_stack, _menhir_s, _startpos__1_), _startpos__2_), _endpos_e_, _, (e : (IntermediateSyntax.exp IntermediateSyntax.annotated)), _startpos_e_), _endpos__4_), _endpos_s_, _, (s : (IntermediateSyntax.stmt IntermediateSyntax.annotated))) = _menhir_stack in
            let _6 = () in
            let _4 = () in
            let _2 = () in
            let _1 = () in
            let _startpos = _startpos__1_ in
            let _endpos = _endpos__6_ in
            let _v : (IntermediateSyntax.stmt) = 
# 147 "frontend/Parser.mly"
                                                                                               ( I_ifdef (e,s,None))
# 3767 "frontend/Parser.ml"
             in
            _menhir_goto_conditional_stmt _menhir_env _menhir_stack _endpos _menhir_s _v _startpos
        | _ ->
            assert (not _menhir_env._menhir_error);
            _menhir_env._menhir_error <- true;
            let _menhir_stack = Obj.magic _menhir_stack in
            let (_menhir_stack, _, _menhir_s, _) = _menhir_stack in
            _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s)
    | MenhirState171 ->
        let _menhir_stack = Obj.magic _menhir_stack in
        assert (not _menhir_env._menhir_error);
        let _tok = _menhir_env._menhir_token in
        (match _tok with
        | TOK_CPP_ENDIF ->
            let _menhir_stack = Obj.magic _menhir_stack in
            let _endpos = _menhir_env._menhir_lexbuf.Lexing.lex_curr_p in
            let _menhir_env = _menhir_discard _menhir_env in
            let _menhir_stack = Obj.magic _menhir_stack in
            let _endpos__8_ = _endpos in
            let ((((((_menhir_stack, _menhir_s, _startpos__1_), _startpos__2_), _endpos_e_, _, (e : (IntermediateSyntax.exp IntermediateSyntax.annotated)), _startpos_e_), _endpos__4_), _endpos_s1_, _, (s1 : (IntermediateSyntax.stmt IntermediateSyntax.annotated))), _endpos_s2_, _, (s2 : (IntermediateSyntax.stmt IntermediateSyntax.annotated))) = _menhir_stack in
            let _8 = () in
            let _6 = () in
            let _4 = () in
            let _2 = () in
            let _1 = () in
            let _startpos = _startpos__1_ in
            let _endpos = _endpos__8_ in
            let _v : (IntermediateSyntax.stmt) = 
# 148 "frontend/Parser.mly"
                                                                                                                         ( I_ifdef (e,s1,Some s2) )
# 3798 "frontend/Parser.ml"
             in
            _menhir_goto_conditional_stmt _menhir_env _menhir_stack _endpos _menhir_s _v _startpos
        | _ ->
            assert (not _menhir_env._menhir_error);
            _menhir_env._menhir_error <- true;
            let _menhir_stack = Obj.magic _menhir_stack in
            let (_menhir_stack, _, _menhir_s, _) = _menhir_stack in
            _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s)
    | MenhirState150 ->
        let _menhir_stack = Obj.magic _menhir_stack in
        let _menhir_stack = Obj.magic _menhir_stack in
        let ((((((((_menhir_stack, _menhir_s, _startpos__1_), _startpos__2_), _endpos_d_, _, (d : (IntermediateSyntax.globalDecl IntermediateSyntax.annotated)), _startpos_d_), _endpos_e1_, _, (e1 : (IntermediateSyntax.exp IntermediateSyntax.annotated)), _startpos_e1_), _endpos__5_, _startpos__5_), _endpos_e2_, _, (e2 : (IntermediateSyntax.exp IntermediateSyntax.annotated)), _startpos_e2_), _endpos__7_), _endpos_s_, _, (s : (IntermediateSyntax.stmt IntermediateSyntax.annotated))) = _menhir_stack in
        let _7 = () in
        let _5 = () in
        let _2 = () in
        let _1 = () in
        let _startpos = _startpos__1_ in
        let _endpos = _endpos_s_ in
        let _v : (IntermediateSyntax.stmt) = 
# 153 "frontend/Parser.mly"
                                                                                                                                  ( I_for (d,e1,e2,s) )
# 3820 "frontend/Parser.ml"
         in
        _menhir_goto_iteration_stmt _menhir_env _menhir_stack _endpos _menhir_s _v _startpos
    | MenhirState185 ->
        let _menhir_stack = Obj.magic _menhir_stack in
        let _menhir_stack = Obj.magic _menhir_stack in
        let (((((((((_menhir_stack, _menhir_s, _startpos__1_), _startpos__2_), _endpos_e1_, _, (e1 : (IntermediateSyntax.exp IntermediateSyntax.annotated)), _startpos_e1_), _endpos__4_, _startpos__4_), _endpos_e2_, _, (e2 : (IntermediateSyntax.exp IntermediateSyntax.annotated)), _startpos_e2_), _endpos__6_, _startpos__6_), _endpos_e3_, _, (e3 : (IntermediateSyntax.exp IntermediateSyntax.annotated)), _startpos_e3_), _endpos__8_), _endpos_s_, _, (s : (IntermediateSyntax.stmt IntermediateSyntax.annotated))) = _menhir_stack in
        let _8 = () in
        let _6 = () in
        let _4 = () in
        let _2 = () in
        let _1 = () in
        let _startpos = _startpos__1_ in
        let _endpos = _endpos_s_ in
        let _v : (IntermediateSyntax.stmt) = 
# 152 "frontend/Parser.mly"
                                                                                                                                           ( I_for_simple (e1,e2,e3,s) )
# 3837 "frontend/Parser.ml"
         in
        _menhir_goto_iteration_stmt _menhir_env _menhir_stack _endpos _menhir_s _v _startpos
    | MenhirState129 ->
        let _menhir_stack = Obj.magic _menhir_stack in
        assert (not _menhir_env._menhir_error);
        let _tok = _menhir_env._menhir_token in
        (match _tok with
        | TOK_ELSE ->
            let _menhir_stack = Obj.magic _menhir_stack in
            let _menhir_env = _menhir_discard _menhir_env in
            let _tok = _menhir_env._menhir_token in
            (match _tok with
            | TOK_ASSERT ->
                _menhir_run155 _menhir_env (Obj.magic _menhir_stack) MenhirState188 _menhir_env._menhir_lexbuf.Lexing.lex_start_p
            | TOK_CHAR ->
                _menhir_run8 _menhir_env (Obj.magic _menhir_stack) _menhir_env._menhir_lexbuf.Lexing.lex_curr_p MenhirState188 _menhir_env._menhir_lexbuf.Lexing.lex_start_p
            | TOK_CPP_IF ->
                _menhir_run151 _menhir_env (Obj.magic _menhir_stack) MenhirState188 _menhir_env._menhir_lexbuf.Lexing.lex_start_p
            | TOK_FALSE ->
                _menhir_run43 _menhir_env (Obj.magic _menhir_stack) _menhir_env._menhir_lexbuf.Lexing.lex_curr_p MenhirState188 _menhir_env._menhir_lexbuf.Lexing.lex_start_p
            | TOK_FOR ->
                _menhir_run130 _menhir_env (Obj.magic _menhir_stack) MenhirState188 _menhir_env._menhir_lexbuf.Lexing.lex_start_p
            | TOK_IF ->
                _menhir_run126 _menhir_env (Obj.magic _menhir_stack) MenhirState188 _menhir_env._menhir_lexbuf.Lexing.lex_start_p
            | TOK_INT ->
                _menhir_run7 _menhir_env (Obj.magic _menhir_stack) _menhir_env._menhir_lexbuf.Lexing.lex_curr_p MenhirState188 _menhir_env._menhir_lexbuf.Lexing.lex_start_p
            | TOK_LBRACKET ->
                _menhir_run35 _menhir_env (Obj.magic _menhir_stack) MenhirState188 _menhir_env._menhir_lexbuf.Lexing.lex_start_p
            | TOK_LCURLY ->
                _menhir_run18 _menhir_env (Obj.magic _menhir_stack) MenhirState188 _menhir_env._menhir_lexbuf.Lexing.lex_start_p
            | TOK_LPAREN ->
                _menhir_run34 _menhir_env (Obj.magic _menhir_stack) MenhirState188 _menhir_env._menhir_lexbuf.Lexing.lex_start_p
            | TOK_MINUS ->
                _menhir_run33 _menhir_env (Obj.magic _menhir_stack) MenhirState188 _menhir_env._menhir_lexbuf.Lexing.lex_start_p
            | TOK_MINUS_MINUS ->
                _menhir_run32 _menhir_env (Obj.magic _menhir_stack) _menhir_env._menhir_lexbuf.Lexing.lex_curr_p MenhirState188 _menhir_env._menhir_lexbuf.Lexing.lex_start_p
            | TOK_MULTIPLY ->
                _menhir_run30 _menhir_env (Obj.magic _menhir_stack) MenhirState188 _menhir_env._menhir_lexbuf.Lexing.lex_start_p
            | TOK_NOT ->
                _menhir_run29 _menhir_env (Obj.magic _menhir_stack) MenhirState188 _menhir_env._menhir_lexbuf.Lexing.lex_start_p
            | TOK_PLUS ->
                _menhir_run28 _menhir_env (Obj.magic _menhir_stack) MenhirState188 _menhir_env._menhir_lexbuf.Lexing.lex_start_p
            | TOK_PLUS_PLUS ->
                _menhir_run27 _menhir_env (Obj.magic _menhir_stack) _menhir_env._menhir_lexbuf.Lexing.lex_curr_p MenhirState188 _menhir_env._menhir_lexbuf.Lexing.lex_start_p
            | TOK_RANDOM ->
                _menhir_run26 _menhir_env (Obj.magic _menhir_stack) _menhir_env._menhir_lexbuf.Lexing.lex_curr_p MenhirState188 _menhir_env._menhir_lexbuf.Lexing.lex_start_p
            | TOK_RETURN ->
                _menhir_run122 _menhir_env (Obj.magic _menhir_stack) MenhirState188 _menhir_env._menhir_lexbuf.Lexing.lex_start_p
            | TOK_SEMICOLON ->
                _menhir_run121 _menhir_env (Obj.magic _menhir_stack) _menhir_env._menhir_lexbuf.Lexing.lex_curr_p MenhirState188 _menhir_env._menhir_lexbuf.Lexing.lex_start_p
            | TOK_TRUE ->
                _menhir_run25 _menhir_env (Obj.magic _menhir_stack) _menhir_env._menhir_lexbuf.Lexing.lex_curr_p MenhirState188 _menhir_env._menhir_lexbuf.Lexing.lex_start_p
            | TOK_UINT ->
                _menhir_run5 _menhir_env (Obj.magic _menhir_stack) MenhirState188 _menhir_env._menhir_lexbuf.Lexing.lex_start_p
            | TOK_URANDOM ->
                _menhir_run24 _menhir_env (Obj.magic _menhir_stack) _menhir_env._menhir_lexbuf.Lexing.lex_curr_p MenhirState188 _menhir_env._menhir_lexbuf.Lexing.lex_start_p
            | TOK_WHILE ->
                _menhir_run21 _menhir_env (Obj.magic _menhir_stack) MenhirState188 _menhir_env._menhir_lexbuf.Lexing.lex_start_p
            | TOK_const _v ->
                _menhir_run20 _menhir_env (Obj.magic _menhir_stack) _menhir_env._menhir_lexbuf.Lexing.lex_curr_p MenhirState188 _v _menhir_env._menhir_lexbuf.Lexing.lex_start_p
            | TOK_id _v ->
                _menhir_run19 _menhir_env (Obj.magic _menhir_stack) _menhir_env._menhir_lexbuf.Lexing.lex_curr_p MenhirState188 _v _menhir_env._menhir_lexbuf.Lexing.lex_start_p
            | _ ->
                assert (not _menhir_env._menhir_error);
                _menhir_env._menhir_error <- true;
                _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) MenhirState188)
        | TOK_ASSERT | TOK_CHAR | TOK_CPP_ELSE | TOK_CPP_ENDIF | TOK_CPP_IF | TOK_FALSE | TOK_FOR | TOK_IF | TOK_INT | TOK_LBRACKET | TOK_LCURLY | TOK_LPAREN | TOK_MINUS | TOK_MINUS_MINUS | TOK_MULTIPLY | TOK_NOT | TOK_PLUS | TOK_PLUS_PLUS | TOK_RANDOM | TOK_RCURLY | TOK_RETURN | TOK_SEMICOLON | TOK_TRUE | TOK_UINT | TOK_URANDOM | TOK_WHILE | TOK_const _ | TOK_id _ ->
            let _menhir_stack = Obj.magic _menhir_stack in
            let (((((_menhir_stack, _menhir_s, _startpos__1_), _startpos__2_), _endpos_e_, _, (e : (IntermediateSyntax.exp IntermediateSyntax.annotated)), _startpos_e_), _endpos__4_), _endpos_s_, _, (s : (IntermediateSyntax.stmt IntermediateSyntax.annotated))) = _menhir_stack in
            let _4 = () in
            let _2 = () in
            let _1 = () in
            let _startpos = _startpos__1_ in
            let _endpos = _endpos_s_ in
            let _v : (IntermediateSyntax.stmt) = 
# 143 "frontend/Parser.mly"
                                                                             ( I_if (e,s,None) )
# 3915 "frontend/Parser.ml"
             in
            _menhir_goto_selection_stmt _menhir_env _menhir_stack _endpos _menhir_s _v _startpos
        | _ ->
            assert (not _menhir_env._menhir_error);
            _menhir_env._menhir_error <- true;
            let _menhir_stack = Obj.magic _menhir_stack in
            let (_menhir_stack, _, _menhir_s, _) = _menhir_stack in
            _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s)
    | MenhirState188 ->
        let _menhir_stack = Obj.magic _menhir_stack in
        let _menhir_stack = Obj.magic _menhir_stack in
        let ((((((_menhir_stack, _menhir_s, _startpos__1_), _startpos__2_), _endpos_e_, _, (e : (IntermediateSyntax.exp IntermediateSyntax.annotated)), _startpos_e_), _endpos__4_), _endpos_s1_, _, (s1 : (IntermediateSyntax.stmt IntermediateSyntax.annotated))), _endpos_s2_, _, (s2 : (IntermediateSyntax.stmt IntermediateSyntax.annotated))) = _menhir_stack in
        let _6 = () in
        let _4 = () in
        let _2 = () in
        let _1 = () in
        let _startpos = _startpos__1_ in
        let _endpos = _endpos_s2_ in
        let _v : (IntermediateSyntax.stmt) = 
# 144 "frontend/Parser.mly"
                                                                                                   ( I_if (e,s1,Some s2) )
# 3937 "frontend/Parser.ml"
         in
        _menhir_goto_selection_stmt _menhir_env _menhir_stack _endpos _menhir_s _v _startpos
    | MenhirState120 ->
        let _menhir_stack = Obj.magic _menhir_stack in
        let _menhir_stack = Obj.magic _menhir_stack in
        let (((((_menhir_stack, _menhir_s, _startpos__1_), _startpos__2_), _endpos_e_, _, (e : (IntermediateSyntax.exp IntermediateSyntax.annotated)), _startpos_e_), _endpos__4_), _endpos_s_, _, (s : (IntermediateSyntax.stmt IntermediateSyntax.annotated))) = _menhir_stack in
        let _4 = () in
        let _2 = () in
        let _1 = () in
        let _startpos = _startpos__1_ in
        let _endpos = _endpos_s_ in
        let _v : (IntermediateSyntax.stmt) = 
# 151 "frontend/Parser.mly"
                                                                                          ( I_while (e,s) )
# 3952 "frontend/Parser.ml"
         in
        _menhir_goto_iteration_stmt _menhir_env _menhir_stack _endpos _menhir_s _v _startpos
    | MenhirState193 | MenhirState18 ->
        let _menhir_stack = Obj.magic _menhir_stack in
        assert (not _menhir_env._menhir_error);
        let _tok = _menhir_env._menhir_token in
        (match _tok with
        | TOK_ASSERT ->
            _menhir_run155 _menhir_env (Obj.magic _menhir_stack) MenhirState193 _menhir_env._menhir_lexbuf.Lexing.lex_start_p
        | TOK_CHAR ->
            _menhir_run8 _menhir_env (Obj.magic _menhir_stack) _menhir_env._menhir_lexbuf.Lexing.lex_curr_p MenhirState193 _menhir_env._menhir_lexbuf.Lexing.lex_start_p
        | TOK_CPP_IF ->
            _menhir_run151 _menhir_env (Obj.magic _menhir_stack) MenhirState193 _menhir_env._menhir_lexbuf.Lexing.lex_start_p
        | TOK_FALSE ->
            _menhir_run43 _menhir_env (Obj.magic _menhir_stack) _menhir_env._menhir_lexbuf.Lexing.lex_curr_p MenhirState193 _menhir_env._menhir_lexbuf.Lexing.lex_start_p
        | TOK_FOR ->
            _menhir_run130 _menhir_env (Obj.magic _menhir_stack) MenhirState193 _menhir_env._menhir_lexbuf.Lexing.lex_start_p
        | TOK_IF ->
            _menhir_run126 _menhir_env (Obj.magic _menhir_stack) MenhirState193 _menhir_env._menhir_lexbuf.Lexing.lex_start_p
        | TOK_INT ->
            _menhir_run7 _menhir_env (Obj.magic _menhir_stack) _menhir_env._menhir_lexbuf.Lexing.lex_curr_p MenhirState193 _menhir_env._menhir_lexbuf.Lexing.lex_start_p
        | TOK_LBRACKET ->
            _menhir_run35 _menhir_env (Obj.magic _menhir_stack) MenhirState193 _menhir_env._menhir_lexbuf.Lexing.lex_start_p
        | TOK_LCURLY ->
            _menhir_run18 _menhir_env (Obj.magic _menhir_stack) MenhirState193 _menhir_env._menhir_lexbuf.Lexing.lex_start_p
        | TOK_LPAREN ->
            _menhir_run34 _menhir_env (Obj.magic _menhir_stack) MenhirState193 _menhir_env._menhir_lexbuf.Lexing.lex_start_p
        | TOK_MINUS ->
            _menhir_run33 _menhir_env (Obj.magic _menhir_stack) MenhirState193 _menhir_env._menhir_lexbuf.Lexing.lex_start_p
        | TOK_MINUS_MINUS ->
            _menhir_run32 _menhir_env (Obj.magic _menhir_stack) _menhir_env._menhir_lexbuf.Lexing.lex_curr_p MenhirState193 _menhir_env._menhir_lexbuf.Lexing.lex_start_p
        | TOK_MULTIPLY ->
            _menhir_run30 _menhir_env (Obj.magic _menhir_stack) MenhirState193 _menhir_env._menhir_lexbuf.Lexing.lex_start_p
        | TOK_NOT ->
            _menhir_run29 _menhir_env (Obj.magic _menhir_stack) MenhirState193 _menhir_env._menhir_lexbuf.Lexing.lex_start_p
        | TOK_PLUS ->
            _menhir_run28 _menhir_env (Obj.magic _menhir_stack) MenhirState193 _menhir_env._menhir_lexbuf.Lexing.lex_start_p
        | TOK_PLUS_PLUS ->
            _menhir_run27 _menhir_env (Obj.magic _menhir_stack) _menhir_env._menhir_lexbuf.Lexing.lex_curr_p MenhirState193 _menhir_env._menhir_lexbuf.Lexing.lex_start_p
        | TOK_RANDOM ->
            _menhir_run26 _menhir_env (Obj.magic _menhir_stack) _menhir_env._menhir_lexbuf.Lexing.lex_curr_p MenhirState193 _menhir_env._menhir_lexbuf.Lexing.lex_start_p
        | TOK_RETURN ->
            _menhir_run122 _menhir_env (Obj.magic _menhir_stack) MenhirState193 _menhir_env._menhir_lexbuf.Lexing.lex_start_p
        | TOK_SEMICOLON ->
            _menhir_run121 _menhir_env (Obj.magic _menhir_stack) _menhir_env._menhir_lexbuf.Lexing.lex_curr_p MenhirState193 _menhir_env._menhir_lexbuf.Lexing.lex_start_p
        | TOK_TRUE ->
            _menhir_run25 _menhir_env (Obj.magic _menhir_stack) _menhir_env._menhir_lexbuf.Lexing.lex_curr_p MenhirState193 _menhir_env._menhir_lexbuf.Lexing.lex_start_p
        | TOK_UINT ->
            _menhir_run5 _menhir_env (Obj.magic _menhir_stack) MenhirState193 _menhir_env._menhir_lexbuf.Lexing.lex_start_p
        | TOK_URANDOM ->
            _menhir_run24 _menhir_env (Obj.magic _menhir_stack) _menhir_env._menhir_lexbuf.Lexing.lex_curr_p MenhirState193 _menhir_env._menhir_lexbuf.Lexing.lex_start_p
        | TOK_WHILE ->
            _menhir_run21 _menhir_env (Obj.magic _menhir_stack) MenhirState193 _menhir_env._menhir_lexbuf.Lexing.lex_start_p
        | TOK_const _v ->
            _menhir_run20 _menhir_env (Obj.magic _menhir_stack) _menhir_env._menhir_lexbuf.Lexing.lex_curr_p MenhirState193 _v _menhir_env._menhir_lexbuf.Lexing.lex_start_p
        | TOK_id _v ->
            _menhir_run19 _menhir_env (Obj.magic _menhir_stack) _menhir_env._menhir_lexbuf.Lexing.lex_curr_p MenhirState193 _v _menhir_env._menhir_lexbuf.Lexing.lex_start_p
        | TOK_RCURLY ->
            _menhir_reduce70 _menhir_env (Obj.magic _menhir_stack) MenhirState193
        | _ ->
            assert (not _menhir_env._menhir_error);
            _menhir_env._menhir_error <- true;
            _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) MenhirState193)
    | _ ->
        _menhir_fail ()

and _menhir_reduce37 : _menhir_env -> 'ttv_tail * _menhir_state * (string IntermediateSyntax.annotated) * Lexing.position -> 'ttv_return =
  fun _menhir_env _menhir_stack ->
    let (_menhir_stack, _menhir_s, (d : (string IntermediateSyntax.annotated)), _startpos_d_) = _menhir_stack in
    let _v : (IntermediateSyntax.declarator) = 
# 98 "frontend/Parser.mly"
                                 ( d, None )
# 4025 "frontend/Parser.ml"
     in
    _menhir_goto_declarator _menhir_env _menhir_stack _menhir_s _v

and _menhir_run142 : _menhir_env -> 'ttv_tail * _menhir_state * (string IntermediateSyntax.annotated) * Lexing.position -> 'ttv_return =
  fun _menhir_env _menhir_stack ->
    let _menhir_env = _menhir_discard _menhir_env in
    let _tok = _menhir_env._menhir_token in
    match _tok with
    | TOK_FALSE ->
        _menhir_run43 _menhir_env (Obj.magic _menhir_stack) _menhir_env._menhir_lexbuf.Lexing.lex_curr_p MenhirState142 _menhir_env._menhir_lexbuf.Lexing.lex_start_p
    | TOK_LBRACKET ->
        _menhir_run35 _menhir_env (Obj.magic _menhir_stack) MenhirState142 _menhir_env._menhir_lexbuf.Lexing.lex_start_p
    | TOK_LPAREN ->
        _menhir_run34 _menhir_env (Obj.magic _menhir_stack) MenhirState142 _menhir_env._menhir_lexbuf.Lexing.lex_start_p
    | TOK_MINUS ->
        _menhir_run33 _menhir_env (Obj.magic _menhir_stack) MenhirState142 _menhir_env._menhir_lexbuf.Lexing.lex_start_p
    | TOK_MINUS_MINUS ->
        _menhir_run32 _menhir_env (Obj.magic _menhir_stack) _menhir_env._menhir_lexbuf.Lexing.lex_curr_p MenhirState142 _menhir_env._menhir_lexbuf.Lexing.lex_start_p
    | TOK_MULTIPLY ->
        _menhir_run30 _menhir_env (Obj.magic _menhir_stack) MenhirState142 _menhir_env._menhir_lexbuf.Lexing.lex_start_p
    | TOK_NOT ->
        _menhir_run29 _menhir_env (Obj.magic _menhir_stack) MenhirState142 _menhir_env._menhir_lexbuf.Lexing.lex_start_p
    | TOK_PLUS ->
        _menhir_run28 _menhir_env (Obj.magic _menhir_stack) MenhirState142 _menhir_env._menhir_lexbuf.Lexing.lex_start_p
    | TOK_PLUS_PLUS ->
        _menhir_run27 _menhir_env (Obj.magic _menhir_stack) _menhir_env._menhir_lexbuf.Lexing.lex_curr_p MenhirState142 _menhir_env._menhir_lexbuf.Lexing.lex_start_p
    | TOK_RANDOM ->
        _menhir_run26 _menhir_env (Obj.magic _menhir_stack) _menhir_env._menhir_lexbuf.Lexing.lex_curr_p MenhirState142 _menhir_env._menhir_lexbuf.Lexing.lex_start_p
    | TOK_TRUE ->
        _menhir_run25 _menhir_env (Obj.magic _menhir_stack) _menhir_env._menhir_lexbuf.Lexing.lex_curr_p MenhirState142 _menhir_env._menhir_lexbuf.Lexing.lex_start_p
    | TOK_URANDOM ->
        _menhir_run24 _menhir_env (Obj.magic _menhir_stack) _menhir_env._menhir_lexbuf.Lexing.lex_curr_p MenhirState142 _menhir_env._menhir_lexbuf.Lexing.lex_start_p
    | TOK_const _v ->
        _menhir_run20 _menhir_env (Obj.magic _menhir_stack) _menhir_env._menhir_lexbuf.Lexing.lex_curr_p MenhirState142 _v _menhir_env._menhir_lexbuf.Lexing.lex_start_p
    | TOK_id _v ->
        _menhir_run23 _menhir_env (Obj.magic _menhir_stack) _menhir_env._menhir_lexbuf.Lexing.lex_curr_p MenhirState142 _v _menhir_env._menhir_lexbuf.Lexing.lex_start_p
    | _ ->
        assert (not _menhir_env._menhir_error);
        _menhir_env._menhir_error <- true;
        _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) MenhirState142

and _menhir_goto_separated_nonempty_list_TOK_COMMA_parameter_ : _menhir_env -> 'ttv_tail -> _menhir_state -> ((IntermediateSyntax.typ IntermediateSyntax.annotated *
   string IntermediateSyntax.annotated)
  list) -> 'ttv_return =
  fun _menhir_env _menhir_stack _menhir_s _v ->
    match _menhir_s with
    | MenhirState228 | MenhirState197 | MenhirState4 ->
        let _menhir_stack = Obj.magic _menhir_stack in
        let _menhir_stack = Obj.magic _menhir_stack in
        let (x : ((IntermediateSyntax.typ IntermediateSyntax.annotated *
   string IntermediateSyntax.annotated)
  list)) = _v in
        let _v : ((IntermediateSyntax.typ IntermediateSyntax.annotated *
   string IntermediateSyntax.annotated)
  list) = 
# 130 "/usr/share/menhir/standard.mly"
    ( x )
# 4083 "frontend/Parser.ml"
         in
        _menhir_goto_loption_separated_nonempty_list_TOK_COMMA_parameter__ _menhir_env _menhir_stack _menhir_s _v
    | MenhirState11 ->
        let _menhir_stack = Obj.magic _menhir_stack in
        let _menhir_stack = Obj.magic _menhir_stack in
        let (xs : ((IntermediateSyntax.typ IntermediateSyntax.annotated *
   string IntermediateSyntax.annotated)
  list)) = _v in
        let (_menhir_stack, _menhir_s, (x : (IntermediateSyntax.typ IntermediateSyntax.annotated *
  string IntermediateSyntax.annotated))) = _menhir_stack in
        let _2 = () in
        let _v : ((IntermediateSyntax.typ IntermediateSyntax.annotated *
   string IntermediateSyntax.annotated)
  list) = 
# 217 "/usr/share/menhir/standard.mly"
    ( x :: xs )
# 4100 "frontend/Parser.ml"
         in
        _menhir_goto_separated_nonempty_list_TOK_COMMA_parameter_ _menhir_env _menhir_stack _menhir_s _v
    | _ ->
        _menhir_fail ()

and _menhir_goto_loption_separated_nonempty_list_TOK_COMMA_declarator__ : _menhir_env -> 'ttv_tail -> _menhir_state -> (IntermediateSyntax.declarator list) -> 'ttv_return =
  fun _menhir_env _menhir_stack _menhir_s _v ->
    let _menhir_stack = (_menhir_stack, _menhir_s, _v) in
    match _menhir_s with
    | MenhirState134 ->
        let _menhir_stack = Obj.magic _menhir_stack in
        assert (not _menhir_env._menhir_error);
        let _tok = _menhir_env._menhir_token in
        (match _tok with
        | TOK_SEMICOLON ->
            let _menhir_stack = Obj.magic _menhir_stack in
            let _endpos = _menhir_env._menhir_lexbuf.Lexing.lex_curr_p in
            let _startpos = _menhir_env._menhir_lexbuf.Lexing.lex_start_p in
            let _menhir_env = _menhir_discard _menhir_env in
            let _menhir_stack = Obj.magic _menhir_stack in
            let _endpos__4_ = _endpos in
            let _startpos__4_ = _startpos in
            let (((_menhir_stack, _menhir_s, (t : (IntermediateSyntax.typ IntermediateSyntax.annotated)), _startpos_t_), _, _startpos__2_), _, (xs0 : (IntermediateSyntax.declarator list))) = _menhir_stack in
            let _4 = () in
            let _2 = () in
            let _startpos = _startpos_t_ in
            let _endpos = _endpos__4_ in
            let _v : (IntermediateSyntax.globalDecl) = let g =
              let xs = xs0 in
              
# 206 "/usr/share/menhir/standard.mly"
    ( xs )
# 4133 "frontend/Parser.ml"
              
            in
            
# 90 "frontend/Parser.mly"
                                                                                                 ( t, g )
# 4139 "frontend/Parser.ml"
             in
            _menhir_goto_global_decl _menhir_env _menhir_stack _endpos _menhir_s _v _startpos
        | _ ->
            assert (not _menhir_env._menhir_error);
            _menhir_env._menhir_error <- true;
            let _menhir_stack = Obj.magic _menhir_stack in
            let (_menhir_stack, _menhir_s, _) = _menhir_stack in
            _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s)
    | MenhirState226 | MenhirState133 ->
        let _menhir_stack = Obj.magic _menhir_stack in
        assert (not _menhir_env._menhir_error);
        let _tok = _menhir_env._menhir_token in
        (match _tok with
        | TOK_SEMICOLON ->
            let _menhir_stack = Obj.magic _menhir_stack in
            let _endpos = _menhir_env._menhir_lexbuf.Lexing.lex_curr_p in
            let _startpos = _menhir_env._menhir_lexbuf.Lexing.lex_start_p in
            let _menhir_env = _menhir_discard _menhir_env in
            let _menhir_stack = Obj.magic _menhir_stack in
            let _endpos__3_ = _endpos in
            let _startpos__3_ = _startpos in
            let ((_menhir_stack, _menhir_s, (t : (IntermediateSyntax.typ IntermediateSyntax.annotated)), _startpos_t_), _, (xs0 : (IntermediateSyntax.declarator list))) = _menhir_stack in
            let _3 = () in
            let _startpos = _startpos_t_ in
            let _endpos = _endpos__3_ in
            let _v : (IntermediateSyntax.globalDecl) = let g =
              let xs = xs0 in
              
# 206 "/usr/share/menhir/standard.mly"
    ( xs )
# 4170 "frontend/Parser.ml"
              
            in
            
# 89 "frontend/Parser.mly"
                                                                                       ( t, g )
# 4176 "frontend/Parser.ml"
             in
            _menhir_goto_global_decl _menhir_env _menhir_stack _endpos _menhir_s _v _startpos
        | _ ->
            assert (not _menhir_env._menhir_error);
            _menhir_env._menhir_error <- true;
            let _menhir_stack = Obj.magic _menhir_stack in
            let (_menhir_stack, _menhir_s, _) = _menhir_stack in
            _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s)
    | _ ->
        _menhir_fail ()

and _menhir_goto_loption_separated_nonempty_list_TOK_COMMA_parameter__ : _menhir_env -> 'ttv_tail -> _menhir_state -> ((IntermediateSyntax.typ IntermediateSyntax.annotated *
   string IntermediateSyntax.annotated)
  list) -> 'ttv_return =
  fun _menhir_env _menhir_stack _menhir_s _v ->
    let _menhir_stack = (_menhir_stack, _menhir_s, _v) in
    match _menhir_s with
    | MenhirState4 ->
        let _menhir_stack = Obj.magic _menhir_stack in
        assert (not _menhir_env._menhir_error);
        let _tok = _menhir_env._menhir_token in
        (match _tok with
        | TOK_RPAREN ->
            let _menhir_stack = Obj.magic _menhir_stack in
            let _endpos = _menhir_env._menhir_lexbuf.Lexing.lex_curr_p in
            let _menhir_stack = (_menhir_stack, _endpos) in
            let _menhir_env = _menhir_discard _menhir_env in
            let _tok = _menhir_env._menhir_token in
            (match _tok with
            | TOK_LCURLY ->
                _menhir_run18 _menhir_env (Obj.magic _menhir_stack) MenhirState17 _menhir_env._menhir_lexbuf.Lexing.lex_start_p
            | _ ->
                assert (not _menhir_env._menhir_error);
                _menhir_env._menhir_error <- true;
                _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) MenhirState17)
        | _ ->
            assert (not _menhir_env._menhir_error);
            _menhir_env._menhir_error <- true;
            let _menhir_stack = Obj.magic _menhir_stack in
            let (_menhir_stack, _menhir_s, _) = _menhir_stack in
            _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s)
    | MenhirState197 ->
        let _menhir_stack = Obj.magic _menhir_stack in
        assert (not _menhir_env._menhir_error);
        let _tok = _menhir_env._menhir_token in
        (match _tok with
        | TOK_RPAREN ->
            let _menhir_stack = Obj.magic _menhir_stack in
            let _endpos = _menhir_env._menhir_lexbuf.Lexing.lex_curr_p in
            let _menhir_stack = (_menhir_stack, _endpos) in
            let _menhir_env = _menhir_discard _menhir_env in
            let _tok = _menhir_env._menhir_token in
            (match _tok with
            | TOK_LCURLY ->
                _menhir_run18 _menhir_env (Obj.magic _menhir_stack) MenhirState203 _menhir_env._menhir_lexbuf.Lexing.lex_start_p
            | TOK_SEMICOLON ->
                let _menhir_stack = Obj.magic _menhir_stack in
                let _endpos = _menhir_env._menhir_lexbuf.Lexing.lex_curr_p in
                let _menhir_s = MenhirState203 in
                let _startpos = _menhir_env._menhir_lexbuf.Lexing.lex_start_p in
                let _menhir_env = _menhir_discard _menhir_env in
                let _menhir_stack = Obj.magic _menhir_stack in
                let _endpos__6_ = _endpos in
                let _startpos__6_ = _startpos in
                let (((((_menhir_stack, _menhir_s, _startpos__10_), _, (f : (string IntermediateSyntax.annotated)), _startpos_f_), _startpos__3_), _, (xs0 : ((IntermediateSyntax.typ IntermediateSyntax.annotated *
   string IntermediateSyntax.annotated)
  list))), _endpos__5_) = _menhir_stack in
                let _6 = () in
                let _5 = () in
                let _3 = () in
                let _10 = () in
                let _startpos = _startpos__10_ in
                let _endpos = _endpos__6_ in
                let _v : (IntermediateSyntax.functionDecl) = let p =
                  let xs = xs0 in
                  
# 206 "/usr/share/menhir/standard.mly"
    ( xs )
# 4255 "frontend/Parser.ml"
                  
                in
                let t =
                  let _1 = _10 in
                  
# 119 "frontend/Parser.mly"
                ( None )
# 4263 "frontend/Parser.ml"
                  
                in
                
# 114 "frontend/Parser.mly"
                                                                                                                      ( t, f, p, [] )
# 4269 "frontend/Parser.ml"
                 in
                _menhir_goto_function_decl _menhir_env _menhir_stack _endpos _menhir_s _v _startpos
            | _ ->
                assert (not _menhir_env._menhir_error);
                _menhir_env._menhir_error <- true;
                _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) MenhirState203)
        | _ ->
            assert (not _menhir_env._menhir_error);
            _menhir_env._menhir_error <- true;
            let _menhir_stack = Obj.magic _menhir_stack in
            let (_menhir_stack, _menhir_s, _) = _menhir_stack in
            _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s)
    | MenhirState228 ->
        let _menhir_stack = Obj.magic _menhir_stack in
        assert (not _menhir_env._menhir_error);
        let _tok = _menhir_env._menhir_token in
        (match _tok with
        | TOK_RPAREN ->
            let _menhir_stack = Obj.magic _menhir_stack in
            let _endpos = _menhir_env._menhir_lexbuf.Lexing.lex_curr_p in
            let _menhir_stack = (_menhir_stack, _endpos) in
            let _menhir_env = _menhir_discard _menhir_env in
            let _tok = _menhir_env._menhir_token in
            (match _tok with
            | TOK_LCURLY ->
                _menhir_run18 _menhir_env (Obj.magic _menhir_stack) MenhirState234 _menhir_env._menhir_lexbuf.Lexing.lex_start_p
            | TOK_SEMICOLON ->
                let _menhir_stack = Obj.magic _menhir_stack in
                let _endpos = _menhir_env._menhir_lexbuf.Lexing.lex_curr_p in
                let _menhir_s = MenhirState234 in
                let _startpos = _menhir_env._menhir_lexbuf.Lexing.lex_start_p in
                let _menhir_env = _menhir_discard _menhir_env in
                let _menhir_stack = Obj.magic _menhir_stack in
                let _endpos__6_ = _endpos in
                let _startpos__6_ = _startpos in
                let (((((_menhir_stack, _menhir_s, (t0 : (IntermediateSyntax.typ IntermediateSyntax.annotated)), _startpos_t0_), _, (f : (string IntermediateSyntax.annotated)), _startpos_f_), _startpos__3_), _, (xs0 : ((IntermediateSyntax.typ IntermediateSyntax.annotated *
   string IntermediateSyntax.annotated)
  list))), _endpos__5_) = _menhir_stack in
                let _6 = () in
                let _5 = () in
                let _3 = () in
                let _startpos = _startpos_t0_ in
                let _endpos = _endpos__6_ in
                let _v : (IntermediateSyntax.functionDecl) = let p =
                  let xs = xs0 in
                  
# 206 "/usr/share/menhir/standard.mly"
    ( xs )
# 4318 "frontend/Parser.ml"
                  
                in
                let t =
                  let t = t0 in
                  
# 118 "frontend/Parser.mly"
                            ( Some t )
# 4326 "frontend/Parser.ml"
                  
                in
                
# 114 "frontend/Parser.mly"
                                                                                                                      ( t, f, p, [] )
# 4332 "frontend/Parser.ml"
                 in
                _menhir_goto_function_decl _menhir_env _menhir_stack _endpos _menhir_s _v _startpos
            | _ ->
                assert (not _menhir_env._menhir_error);
                _menhir_env._menhir_error <- true;
                _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) MenhirState234)
        | _ ->
            assert (not _menhir_env._menhir_error);
            _menhir_env._menhir_error <- true;
            let _menhir_stack = Obj.magic _menhir_stack in
            let (_menhir_stack, _menhir_s, _) = _menhir_stack in
            _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s)
    | _ ->
        _menhir_fail ()

and _menhir_reduce101 : _menhir_env -> 'ttv_tail * Lexing.position * _menhir_state * (
# 35 "frontend/Parser.mly"
       (string)
# 4351 "frontend/Parser.ml"
) * Lexing.position -> 'ttv_return =
  fun _menhir_env _menhir_stack ->
    let (_menhir_stack, _endpos_e_, _menhir_s, (e : (
# 35 "frontend/Parser.mly"
       (string)
# 4357 "frontend/Parser.ml"
    )), _startpos_e_) = _menhir_stack in
    let _startpos = _startpos_e_ in
    let _endpos = _endpos_e_ in
    let _v : (IntermediateSyntax.exp) = 
# 229 "frontend/Parser.mly"
                                      ( I_id e )
# 4364 "frontend/Parser.ml"
     in
    _menhir_goto_primary_exp _menhir_env _menhir_stack _endpos _menhir_s _v _startpos

and _menhir_goto_unary_op : _menhir_env -> 'ttv_tail -> _menhir_state -> (IntermediateSyntax.unaryOp) -> Lexing.position -> 'ttv_return =
  fun _menhir_env _menhir_stack _menhir_s _v _startpos ->
    let _menhir_stack = (_menhir_stack, _menhir_s, _v, _startpos) in
    match _menhir_s with
    | MenhirState39 | MenhirState35 ->
        let _menhir_stack = Obj.magic _menhir_stack in
        let _menhir_stack = Obj.magic _menhir_stack in
        let (_menhir_stack, _menhir_s, (x : (IntermediateSyntax.unaryOp)), _startpos_x_) = _menhir_stack in
        let _v : (IntermediateSyntax.unaryOp option) = 
# 102 "/usr/share/menhir/standard.mly"
    ( Some x )
# 4379 "frontend/Parser.ml"
         in
        _menhir_goto_option_unary_op_ _menhir_env _menhir_stack _menhir_s _v
    | MenhirState215 | MenhirState207 | MenhirState193 | MenhirState18 | MenhirState120 | MenhirState188 | MenhirState129 | MenhirState185 | MenhirState183 | MenhirState181 | MenhirState150 | MenhirState171 | MenhirState154 | MenhirState156 | MenhirState152 | MenhirState148 | MenhirState146 | MenhirState142 | MenhirState131 | MenhirState127 | MenhirState122 | MenhirState22 | MenhirState27 | MenhirState29 | MenhirState32 | MenhirState112 | MenhirState106 | MenhirState101 | MenhirState98 | MenhirState95 | MenhirState92 | MenhirState90 | MenhirState88 | MenhirState85 | MenhirState82 | MenhirState79 | MenhirState77 | MenhirState75 | MenhirState72 | MenhirState70 | MenhirState52 | MenhirState44 | MenhirState34 ->
        let _menhir_stack = Obj.magic _menhir_stack in
        assert (not _menhir_env._menhir_error);
        let _tok = _menhir_env._menhir_token in
        (match _tok with
        | TOK_FALSE ->
            _menhir_run43 _menhir_env (Obj.magic _menhir_stack) _menhir_env._menhir_lexbuf.Lexing.lex_curr_p MenhirState44 _menhir_env._menhir_lexbuf.Lexing.lex_start_p
        | TOK_LBRACKET ->
            _menhir_run35 _menhir_env (Obj.magic _menhir_stack) MenhirState44 _menhir_env._menhir_lexbuf.Lexing.lex_start_p
        | TOK_LPAREN ->
            _menhir_run34 _menhir_env (Obj.magic _menhir_stack) MenhirState44 _menhir_env._menhir_lexbuf.Lexing.lex_start_p
        | TOK_MINUS ->
            _menhir_run33 _menhir_env (Obj.magic _menhir_stack) MenhirState44 _menhir_env._menhir_lexbuf.Lexing.lex_start_p
        | TOK_MINUS_MINUS ->
            _menhir_run32 _menhir_env (Obj.magic _menhir_stack) _menhir_env._menhir_lexbuf.Lexing.lex_curr_p MenhirState44 _menhir_env._menhir_lexbuf.Lexing.lex_start_p
        | TOK_MULTIPLY ->
            _menhir_run30 _menhir_env (Obj.magic _menhir_stack) MenhirState44 _menhir_env._menhir_lexbuf.Lexing.lex_start_p
        | TOK_NOT ->
            _menhir_run29 _menhir_env (Obj.magic _menhir_stack) MenhirState44 _menhir_env._menhir_lexbuf.Lexing.lex_start_p
        | TOK_PLUS ->
            _menhir_run28 _menhir_env (Obj.magic _menhir_stack) MenhirState44 _menhir_env._menhir_lexbuf.Lexing.lex_start_p
        | TOK_PLUS_PLUS ->
            _menhir_run27 _menhir_env (Obj.magic _menhir_stack) _menhir_env._menhir_lexbuf.Lexing.lex_curr_p MenhirState44 _menhir_env._menhir_lexbuf.Lexing.lex_start_p
        | TOK_RANDOM ->
            _menhir_run26 _menhir_env (Obj.magic _menhir_stack) _menhir_env._menhir_lexbuf.Lexing.lex_curr_p MenhirState44 _menhir_env._menhir_lexbuf.Lexing.lex_start_p
        | TOK_TRUE ->
            _menhir_run25 _menhir_env (Obj.magic _menhir_stack) _menhir_env._menhir_lexbuf.Lexing.lex_curr_p MenhirState44 _menhir_env._menhir_lexbuf.Lexing.lex_start_p
        | TOK_URANDOM ->
            _menhir_run24 _menhir_env (Obj.magic _menhir_stack) _menhir_env._menhir_lexbuf.Lexing.lex_curr_p MenhirState44 _menhir_env._menhir_lexbuf.Lexing.lex_start_p
        | TOK_const _v ->
            _menhir_run20 _menhir_env (Obj.magic _menhir_stack) _menhir_env._menhir_lexbuf.Lexing.lex_curr_p MenhirState44 _v _menhir_env._menhir_lexbuf.Lexing.lex_start_p
        | TOK_id _v ->
            _menhir_run23 _menhir_env (Obj.magic _menhir_stack) _menhir_env._menhir_lexbuf.Lexing.lex_curr_p MenhirState44 _v _menhir_env._menhir_lexbuf.Lexing.lex_start_p
        | _ ->
            assert (not _menhir_env._menhir_error);
            _menhir_env._menhir_error <- true;
            _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) MenhirState44)
    | _ ->
        _menhir_fail ()

and _menhir_reduce90 : _menhir_env -> 'ttv_tail -> _menhir_state -> 'ttv_return =
  fun _menhir_env _menhir_stack _menhir_s ->
    let _v : (IntermediateSyntax.unaryOp option) = 
# 100 "/usr/share/menhir/standard.mly"
    ( None )
# 4427 "frontend/Parser.ml"
     in
    _menhir_goto_option_unary_op_ _menhir_env _menhir_stack _menhir_s _v

and _menhir_goto_primary_exp : _menhir_env -> 'ttv_tail -> Lexing.position -> _menhir_state -> (IntermediateSyntax.exp) -> Lexing.position -> 'ttv_return =
  fun _menhir_env _menhir_stack _endpos _menhir_s _v _startpos ->
    let _menhir_stack = Obj.magic _menhir_stack in
    let _menhir_stack = Obj.magic _menhir_stack in
    let _endpos_e_ = _endpos in
    let (e : (IntermediateSyntax.exp)) = _v in
    let _startpos_e_ = _startpos in
    let _startpos = _startpos_e_ in
    let _endpos = _endpos_e_ in
    let _v : (IntermediateSyntax.exp) = 
# 219 "frontend/Parser.mly"
                                      ( e )
# 4443 "frontend/Parser.ml"
     in
    _menhir_goto_postfix_exp _menhir_env _menhir_stack _endpos _menhir_s _v _startpos

and _menhir_reduce4 : _menhir_env -> 'ttv_tail * Lexing.position * _menhir_state * (
# 35 "frontend/Parser.mly"
       (string)
# 4450 "frontend/Parser.ml"
) * Lexing.position -> 'ttv_return =
  fun _menhir_env _menhir_stack ->
    let (_menhir_stack, _endpos_x_, _menhir_s, (x : (
# 35 "frontend/Parser.mly"
       (string)
# 4456 "frontend/Parser.ml"
    )), _startpos_x_) = _menhir_stack in
    let _startpos = _startpos_x_ in
    let _v : (string IntermediateSyntax.annotated) = let _endpos = _endpos_x_ in
    let _startpos = _startpos_x_ in
    
# 236 "frontend/Parser.mly"
          ( x, (_startpos, _endpos) )
# 4464 "frontend/Parser.ml"
     in
    let _menhir_stack = (_menhir_stack, _menhir_s, _v, _startpos) in
    match _menhir_s with
    | MenhirState14 ->
        let _menhir_stack = Obj.magic _menhir_stack in
        let _menhir_stack = Obj.magic _menhir_stack in
        let ((_menhir_stack, _menhir_s, (t : (IntermediateSyntax.typ IntermediateSyntax.annotated)), _startpos_t_), _, (d : (string IntermediateSyntax.annotated)), _startpos_d_) = _menhir_stack in
        let _v : (IntermediateSyntax.typ IntermediateSyntax.annotated *
  string IntermediateSyntax.annotated) = 
# 122 "frontend/Parser.mly"
                                                          ( t, d )
# 4476 "frontend/Parser.ml"
         in
        let _menhir_stack = (_menhir_stack, _menhir_s, _v) in
        let _menhir_stack = Obj.magic _menhir_stack in
        assert (not _menhir_env._menhir_error);
        let _tok = _menhir_env._menhir_token in
        (match _tok with
        | TOK_COMMA ->
            let _menhir_stack = Obj.magic _menhir_stack in
            let _menhir_env = _menhir_discard _menhir_env in
            let _tok = _menhir_env._menhir_token in
            (match _tok with
            | TOK_CHAR ->
                _menhir_run8 _menhir_env (Obj.magic _menhir_stack) _menhir_env._menhir_lexbuf.Lexing.lex_curr_p MenhirState11 _menhir_env._menhir_lexbuf.Lexing.lex_start_p
            | TOK_INT ->
                _menhir_run7 _menhir_env (Obj.magic _menhir_stack) _menhir_env._menhir_lexbuf.Lexing.lex_curr_p MenhirState11 _menhir_env._menhir_lexbuf.Lexing.lex_start_p
            | TOK_UINT ->
                _menhir_run5 _menhir_env (Obj.magic _menhir_stack) MenhirState11 _menhir_env._menhir_lexbuf.Lexing.lex_start_p
            | _ ->
                assert (not _menhir_env._menhir_error);
                _menhir_env._menhir_error <- true;
                _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) MenhirState11)
        | TOK_RPAREN ->
            let _menhir_stack = Obj.magic _menhir_stack in
            let (_menhir_stack, _menhir_s, (x : (IntermediateSyntax.typ IntermediateSyntax.annotated *
  string IntermediateSyntax.annotated))) = _menhir_stack in
            let _v : ((IntermediateSyntax.typ IntermediateSyntax.annotated *
   string IntermediateSyntax.annotated)
  list) = 
# 215 "/usr/share/menhir/standard.mly"
    ( [ x ] )
# 4507 "frontend/Parser.ml"
             in
            _menhir_goto_separated_nonempty_list_TOK_COMMA_parameter_ _menhir_env _menhir_stack _menhir_s _v
        | _ ->
            assert (not _menhir_env._menhir_error);
            _menhir_env._menhir_error <- true;
            let _menhir_stack = Obj.magic _menhir_stack in
            let (_menhir_stack, _menhir_s, _) = _menhir_stack in
            _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s)
    | MenhirState133 | MenhirState134 | MenhirState139 ->
        let _menhir_stack = Obj.magic _menhir_stack in
        assert (not _menhir_env._menhir_error);
        let _tok = _menhir_env._menhir_token in
        (match _tok with
        | TOK_EQUAL ->
            _menhir_run142 _menhir_env (Obj.magic _menhir_stack)
        | TOK_COMMA | TOK_SEMICOLON ->
            _menhir_reduce37 _menhir_env (Obj.magic _menhir_stack)
        | _ ->
            assert (not _menhir_env._menhir_error);
            _menhir_env._menhir_error <- true;
            let _menhir_stack = Obj.magic _menhir_stack in
            let (_menhir_stack, _menhir_s, _, _) = _menhir_stack in
            _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s)
    | MenhirState18 | MenhirState193 | MenhirState120 | MenhirState129 | MenhirState188 | MenhirState185 | MenhirState150 | MenhirState154 | MenhirState171 ->
        let _menhir_stack = Obj.magic _menhir_stack in
        assert (not _menhir_env._menhir_error);
        let _tok = _menhir_env._menhir_token in
        (match _tok with
        | TOK_COLON ->
            let _menhir_stack = Obj.magic _menhir_stack in
            let _endpos = _menhir_env._menhir_lexbuf.Lexing.lex_curr_p in
            let _menhir_env = _menhir_discard _menhir_env in
            let _menhir_stack = Obj.magic _menhir_stack in
            let _endpos__2_ = _endpos in
            let (_menhir_stack, _menhir_s, (l : (string IntermediateSyntax.annotated)), _startpos_l_) = _menhir_stack in
            let _2 = () in
            let _startpos = _startpos_l_ in
            let _endpos = _endpos__2_ in
            let _v : (IntermediateSyntax.stmt) = 
# 135 "frontend/Parser.mly"
                                  ( I_label l )
# 4549 "frontend/Parser.ml"
             in
            let _menhir_stack = Obj.magic _menhir_stack in
            let _menhir_stack = Obj.magic _menhir_stack in
            let _endpos_s_ = _endpos in
            let (s : (IntermediateSyntax.stmt)) = _v in
            let _startpos_s_ = _startpos in
            let _startpos = _startpos_s_ in
            let _endpos = _endpos_s_ in
            let _v : (IntermediateSyntax.stmt) = 
# 125 "frontend/Parser.mly"
                     ( s )
# 4561 "frontend/Parser.ml"
             in
            _menhir_goto_stmt _menhir_env _menhir_stack _endpos _menhir_s _v _startpos
        | _ ->
            assert (not _menhir_env._menhir_error);
            _menhir_env._menhir_error <- true;
            let _menhir_stack = Obj.magic _menhir_stack in
            let (_menhir_stack, _menhir_s, _, _) = _menhir_stack in
            _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s)
    | MenhirState1 ->
        let _menhir_stack = Obj.magic _menhir_stack in
        assert (not _menhir_env._menhir_error);
        let _tok = _menhir_env._menhir_token in
        (match _tok with
        | TOK_LPAREN ->
            let _menhir_stack = Obj.magic _menhir_stack in
            let _startpos = _menhir_env._menhir_lexbuf.Lexing.lex_start_p in
            let _menhir_stack = (_menhir_stack, _startpos) in
            let _menhir_env = _menhir_discard _menhir_env in
            let _tok = _menhir_env._menhir_token in
            (match _tok with
            | TOK_CHAR ->
                _menhir_run8 _menhir_env (Obj.magic _menhir_stack) _menhir_env._menhir_lexbuf.Lexing.lex_curr_p MenhirState197 _menhir_env._menhir_lexbuf.Lexing.lex_start_p
            | TOK_INT ->
                _menhir_run7 _menhir_env (Obj.magic _menhir_stack) _menhir_env._menhir_lexbuf.Lexing.lex_curr_p MenhirState197 _menhir_env._menhir_lexbuf.Lexing.lex_start_p
            | TOK_UINT ->
                _menhir_run5 _menhir_env (Obj.magic _menhir_stack) MenhirState197 _menhir_env._menhir_lexbuf.Lexing.lex_start_p
            | TOK_VOID ->
                let _menhir_stack = Obj.magic _menhir_stack in
                let _menhir_s = MenhirState197 in
                let _startpos = _menhir_env._menhir_lexbuf.Lexing.lex_start_p in
                let _menhir_stack = (_menhir_stack, _menhir_s, _startpos) in
                let _menhir_env = _menhir_discard _menhir_env in
                let _tok = _menhir_env._menhir_token in
                (match _tok with
                | TOK_RPAREN ->
                    let _menhir_stack = Obj.magic _menhir_stack in
                    let _endpos = _menhir_env._menhir_lexbuf.Lexing.lex_curr_p in
                    let _menhir_stack = (_menhir_stack, _endpos) in
                    let _menhir_env = _menhir_discard _menhir_env in
                    let _tok = _menhir_env._menhir_token in
                    (match _tok with
                    | TOK_LCURLY ->
                        _menhir_run18 _menhir_env (Obj.magic _menhir_stack) MenhirState199 _menhir_env._menhir_lexbuf.Lexing.lex_start_p
                    | TOK_SEMICOLON ->
                        let _menhir_stack = Obj.magic _menhir_stack in
                        let _endpos = _menhir_env._menhir_lexbuf.Lexing.lex_curr_p in
                        let _menhir_s = MenhirState199 in
                        let _startpos = _menhir_env._menhir_lexbuf.Lexing.lex_start_p in
                        let _menhir_env = _menhir_discard _menhir_env in
                        let _menhir_stack = Obj.magic _menhir_stack in
                        let _endpos__6_ = _endpos in
                        let _startpos__6_ = _startpos in
                        let (((((_menhir_stack, _menhir_s, _startpos__10_), _, (f : (string IntermediateSyntax.annotated)), _startpos_f_), _startpos__3_), _, _startpos__4_), _endpos__5_) = _menhir_stack in
                        let _6 = () in
                        let _5 = () in
                        let _4 = () in
                        let _3 = () in
                        let _10 = () in
                        let _startpos = _startpos__10_ in
                        let _endpos = _endpos__6_ in
                        let _v : (IntermediateSyntax.functionDecl) = let t =
                          let _1 = _10 in
                          
# 119 "frontend/Parser.mly"
                ( None )
# 4627 "frontend/Parser.ml"
                          
                        in
                        
# 112 "frontend/Parser.mly"
                                                                                              ( t, f, [], [] )
# 4633 "frontend/Parser.ml"
                         in
                        _menhir_goto_function_decl _menhir_env _menhir_stack _endpos _menhir_s _v _startpos
                    | _ ->
                        assert (not _menhir_env._menhir_error);
                        _menhir_env._menhir_error <- true;
                        _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) MenhirState199)
                | _ ->
                    assert (not _menhir_env._menhir_error);
                    _menhir_env._menhir_error <- true;
                    let _menhir_stack = Obj.magic _menhir_stack in
                    let (_menhir_stack, _menhir_s, _) = _menhir_stack in
                    _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s)
            | TOK_RPAREN ->
                _menhir_reduce82 _menhir_env (Obj.magic _menhir_stack) MenhirState197
            | _ ->
                assert (not _menhir_env._menhir_error);
                _menhir_env._menhir_error <- true;
                _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) MenhirState197)
        | _ ->
            assert (not _menhir_env._menhir_error);
            _menhir_env._menhir_error <- true;
            let _menhir_stack = Obj.magic _menhir_stack in
            let (_menhir_stack, _menhir_s, _, _) = _menhir_stack in
            _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s)
    | MenhirState208 ->
        let _menhir_stack = Obj.magic _menhir_stack in
        assert (not _menhir_env._menhir_error);
        let _tok = _menhir_env._menhir_token in
        (match _tok with
        | TOK_SEMICOLON ->
            let _menhir_stack = Obj.magic _menhir_stack in
            let _endpos = _menhir_env._menhir_lexbuf.Lexing.lex_curr_p in
            let _startpos = _menhir_env._menhir_lexbuf.Lexing.lex_start_p in
            let _menhir_env = _menhir_discard _menhir_env in
            let _menhir_stack = Obj.magic _menhir_stack in
            let _endpos__5_ = _endpos in
            let _startpos__5_ = _startpos in
            let ((((_menhir_stack, _menhir_s, _startpos__1_), _endpos__2_, _startpos__2_), _endpos_e_, _, (e : (IntermediateSyntax.exp IntermediateSyntax.annotated)), _startpos_e_), _, (t : (string IntermediateSyntax.annotated)), _startpos_t_) = _menhir_stack in
            let _5 = () in
            let _2 = () in
            let _1 = () in
            let _startpos = _startpos__1_ in
            let _endpos = _endpos__5_ in
            let _v : (IntermediateSyntax.globalFeature) = 
# 106 "frontend/Parser.mly"
                                                                         ( t, Some e )
# 4680 "frontend/Parser.ml"
             in
            _menhir_goto_global_feature _menhir_env _menhir_stack _endpos _menhir_s _v _startpos
        | _ ->
            assert (not _menhir_env._menhir_error);
            _menhir_env._menhir_error <- true;
            let _menhir_stack = Obj.magic _menhir_stack in
            let (_menhir_stack, _menhir_s, _, _) = _menhir_stack in
            _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s)
    | MenhirState211 ->
        let _menhir_stack = Obj.magic _menhir_stack in
        assert (not _menhir_env._menhir_error);
        let _tok = _menhir_env._menhir_token in
        (match _tok with
        | TOK_SEMICOLON ->
            let _menhir_stack = Obj.magic _menhir_stack in
            let _endpos = _menhir_env._menhir_lexbuf.Lexing.lex_curr_p in
            let _startpos = _menhir_env._menhir_lexbuf.Lexing.lex_start_p in
            let _menhir_env = _menhir_discard _menhir_env in
            let _menhir_stack = Obj.magic _menhir_stack in
            let _endpos__4_ = _endpos in
            let _startpos__4_ = _startpos in
            let ((_menhir_stack, _menhir_s, _startpos__1_), _, (t : (string IntermediateSyntax.annotated)), _startpos_t_) = _menhir_stack in
            let _4 = () in
            let _2 = () in
            let _1 = () in
            let _startpos = _startpos__1_ in
            let _endpos = _endpos__4_ in
            let _v : (IntermediateSyntax.globalFeature) = 
# 105 "frontend/Parser.mly"
                                                         ( t, None )
# 4711 "frontend/Parser.ml"
             in
            _menhir_goto_global_feature _menhir_env _menhir_stack _endpos _menhir_s _v _startpos
        | _ ->
            assert (not _menhir_env._menhir_error);
            _menhir_env._menhir_error <- true;
            let _menhir_stack = Obj.magic _menhir_stack in
            let (_menhir_stack, _menhir_s, _, _) = _menhir_stack in
            _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s)
    | MenhirState214 ->
        let _menhir_stack = Obj.magic _menhir_stack in
        assert (not _menhir_env._menhir_error);
        let _tok = _menhir_env._menhir_token in
        (match _tok with
        | TOK_FALSE ->
            _menhir_run43 _menhir_env (Obj.magic _menhir_stack) _menhir_env._menhir_lexbuf.Lexing.lex_curr_p MenhirState215 _menhir_env._menhir_lexbuf.Lexing.lex_start_p
        | TOK_LBRACKET ->
            _menhir_run35 _menhir_env (Obj.magic _menhir_stack) MenhirState215 _menhir_env._menhir_lexbuf.Lexing.lex_start_p
        | TOK_LPAREN ->
            _menhir_run34 _menhir_env (Obj.magic _menhir_stack) MenhirState215 _menhir_env._menhir_lexbuf.Lexing.lex_start_p
        | TOK_MINUS ->
            _menhir_run33 _menhir_env (Obj.magic _menhir_stack) MenhirState215 _menhir_env._menhir_lexbuf.Lexing.lex_start_p
        | TOK_MINUS_MINUS ->
            _menhir_run32 _menhir_env (Obj.magic _menhir_stack) _menhir_env._menhir_lexbuf.Lexing.lex_curr_p MenhirState215 _menhir_env._menhir_lexbuf.Lexing.lex_start_p
        | TOK_MULTIPLY ->
            _menhir_run30 _menhir_env (Obj.magic _menhir_stack) MenhirState215 _menhir_env._menhir_lexbuf.Lexing.lex_start_p
        | TOK_NOT ->
            _menhir_run29 _menhir_env (Obj.magic _menhir_stack) MenhirState215 _menhir_env._menhir_lexbuf.Lexing.lex_start_p
        | TOK_PLUS ->
            _menhir_run28 _menhir_env (Obj.magic _menhir_stack) MenhirState215 _menhir_env._menhir_lexbuf.Lexing.lex_start_p
        | TOK_PLUS_PLUS ->
            _menhir_run27 _menhir_env (Obj.magic _menhir_stack) _menhir_env._menhir_lexbuf.Lexing.lex_curr_p MenhirState215 _menhir_env._menhir_lexbuf.Lexing.lex_start_p
        | TOK_RANDOM ->
            _menhir_run26 _menhir_env (Obj.magic _menhir_stack) _menhir_env._menhir_lexbuf.Lexing.lex_curr_p MenhirState215 _menhir_env._menhir_lexbuf.Lexing.lex_start_p
        | TOK_TRUE ->
            _menhir_run25 _menhir_env (Obj.magic _menhir_stack) _menhir_env._menhir_lexbuf.Lexing.lex_curr_p MenhirState215 _menhir_env._menhir_lexbuf.Lexing.lex_start_p
        | TOK_URANDOM ->
            _menhir_run24 _menhir_env (Obj.magic _menhir_stack) _menhir_env._menhir_lexbuf.Lexing.lex_curr_p MenhirState215 _menhir_env._menhir_lexbuf.Lexing.lex_start_p
        | TOK_const _v ->
            _menhir_run20 _menhir_env (Obj.magic _menhir_stack) _menhir_env._menhir_lexbuf.Lexing.lex_curr_p MenhirState215 _v _menhir_env._menhir_lexbuf.Lexing.lex_start_p
        | TOK_id _v ->
            _menhir_run23 _menhir_env (Obj.magic _menhir_stack) _menhir_env._menhir_lexbuf.Lexing.lex_curr_p MenhirState215 _v _menhir_env._menhir_lexbuf.Lexing.lex_start_p
        | _ ->
            assert (not _menhir_env._menhir_error);
            _menhir_env._menhir_error <- true;
            _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) MenhirState215)
    | MenhirState226 ->
        let _menhir_stack = Obj.magic _menhir_stack in
        assert (not _menhir_env._menhir_error);
        let _tok = _menhir_env._menhir_token in
        (match _tok with
        | TOK_EQUAL ->
            _menhir_run142 _menhir_env (Obj.magic _menhir_stack)
        | TOK_LPAREN ->
            let _menhir_stack = Obj.magic _menhir_stack in
            let _startpos = _menhir_env._menhir_lexbuf.Lexing.lex_start_p in
            let _menhir_stack = (_menhir_stack, _startpos) in
            let _menhir_env = _menhir_discard _menhir_env in
            let _tok = _menhir_env._menhir_token in
            (match _tok with
            | TOK_CHAR ->
                _menhir_run8 _menhir_env (Obj.magic _menhir_stack) _menhir_env._menhir_lexbuf.Lexing.lex_curr_p MenhirState228 _menhir_env._menhir_lexbuf.Lexing.lex_start_p
            | TOK_INT ->
                _menhir_run7 _menhir_env (Obj.magic _menhir_stack) _menhir_env._menhir_lexbuf.Lexing.lex_curr_p MenhirState228 _menhir_env._menhir_lexbuf.Lexing.lex_start_p
            | TOK_UINT ->
                _menhir_run5 _menhir_env (Obj.magic _menhir_stack) MenhirState228 _menhir_env._menhir_lexbuf.Lexing.lex_start_p
            | TOK_VOID ->
                let _menhir_stack = Obj.magic _menhir_stack in
                let _menhir_s = MenhirState228 in
                let _startpos = _menhir_env._menhir_lexbuf.Lexing.lex_start_p in
                let _menhir_stack = (_menhir_stack, _menhir_s, _startpos) in
                let _menhir_env = _menhir_discard _menhir_env in
                let _tok = _menhir_env._menhir_token in
                (match _tok with
                | TOK_RPAREN ->
                    let _menhir_stack = Obj.magic _menhir_stack in
                    let _endpos = _menhir_env._menhir_lexbuf.Lexing.lex_curr_p in
                    let _menhir_stack = (_menhir_stack, _endpos) in
                    let _menhir_env = _menhir_discard _menhir_env in
                    let _tok = _menhir_env._menhir_token in
                    (match _tok with
                    | TOK_LCURLY ->
                        _menhir_run18 _menhir_env (Obj.magic _menhir_stack) MenhirState230 _menhir_env._menhir_lexbuf.Lexing.lex_start_p
                    | TOK_SEMICOLON ->
                        let _menhir_stack = Obj.magic _menhir_stack in
                        let _endpos = _menhir_env._menhir_lexbuf.Lexing.lex_curr_p in
                        let _menhir_s = MenhirState230 in
                        let _startpos = _menhir_env._menhir_lexbuf.Lexing.lex_start_p in
                        let _menhir_env = _menhir_discard _menhir_env in
                        let _menhir_stack = Obj.magic _menhir_stack in
                        let _endpos__6_ = _endpos in
                        let _startpos__6_ = _startpos in
                        let (((((_menhir_stack, _menhir_s, (t0 : (IntermediateSyntax.typ IntermediateSyntax.annotated)), _startpos_t0_), _, (f : (string IntermediateSyntax.annotated)), _startpos_f_), _startpos__3_), _, _startpos__4_), _endpos__5_) = _menhir_stack in
                        let _6 = () in
                        let _5 = () in
                        let _4 = () in
                        let _3 = () in
                        let _startpos = _startpos_t0_ in
                        let _endpos = _endpos__6_ in
                        let _v : (IntermediateSyntax.functionDecl) = let t =
                          let t = t0 in
                          
# 118 "frontend/Parser.mly"
                            ( Some t )
# 4815 "frontend/Parser.ml"
                          
                        in
                        
# 112 "frontend/Parser.mly"
                                                                                              ( t, f, [], [] )
# 4821 "frontend/Parser.ml"
                         in
                        _menhir_goto_function_decl _menhir_env _menhir_stack _endpos _menhir_s _v _startpos
                    | _ ->
                        assert (not _menhir_env._menhir_error);
                        _menhir_env._menhir_error <- true;
                        _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) MenhirState230)
                | _ ->
                    assert (not _menhir_env._menhir_error);
                    _menhir_env._menhir_error <- true;
                    let _menhir_stack = Obj.magic _menhir_stack in
                    let (_menhir_stack, _menhir_s, _) = _menhir_stack in
                    _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s)
            | TOK_RPAREN ->
                _menhir_reduce82 _menhir_env (Obj.magic _menhir_stack) MenhirState228
            | _ ->
                assert (not _menhir_env._menhir_error);
                _menhir_env._menhir_error <- true;
                _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) MenhirState228)
        | TOK_COMMA | TOK_SEMICOLON ->
            _menhir_reduce37 _menhir_env (Obj.magic _menhir_stack)
        | _ ->
            assert (not _menhir_env._menhir_error);
            _menhir_env._menhir_error <- true;
            let _menhir_stack = Obj.magic _menhir_stack in
            let (_menhir_stack, _menhir_s, _, _) = _menhir_stack in
            _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s)
    | _ ->
        _menhir_fail ()

and _menhir_fail : unit -> 'a =
  fun () ->
    Printf.fprintf Pervasives.stderr "Internal failure -- please contact the parser generator's developers.\n%!";
    assert false

and _menhir_reduce80 : _menhir_env -> 'ttv_tail -> _menhir_state -> 'ttv_return =
  fun _menhir_env _menhir_stack _menhir_s ->
    let _v : (IntermediateSyntax.declarator list) = 
# 128 "/usr/share/menhir/standard.mly"
    ( [] )
# 4861 "frontend/Parser.ml"
     in
    _menhir_goto_loption_separated_nonempty_list_TOK_COMMA_declarator__ _menhir_env _menhir_stack _menhir_s _v

and _menhir_run134 : _menhir_env -> 'ttv_tail * _menhir_state * (IntermediateSyntax.typ IntermediateSyntax.annotated) * Lexing.position -> _menhir_state -> Lexing.position -> 'ttv_return =
  fun _menhir_env _menhir_stack _menhir_s _startpos ->
    let _menhir_stack = (_menhir_stack, _menhir_s, _startpos) in
    let _menhir_env = _menhir_discard _menhir_env in
    let _tok = _menhir_env._menhir_token in
    match _tok with
    | TOK_id _v ->
        _menhir_run2 _menhir_env (Obj.magic _menhir_stack) _menhir_env._menhir_lexbuf.Lexing.lex_curr_p MenhirState134 _v _menhir_env._menhir_lexbuf.Lexing.lex_start_p
    | TOK_SEMICOLON ->
        _menhir_reduce80 _menhir_env (Obj.magic _menhir_stack) MenhirState134
    | _ ->
        assert (not _menhir_env._menhir_error);
        _menhir_env._menhir_error <- true;
        _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) MenhirState134

and _menhir_goto_list_decl_ : _menhir_env -> 'ttv_tail -> Lexing.position -> _menhir_state -> (IntermediateSyntax.decl list) -> Lexing.position -> 'ttv_return =
  fun _menhir_env _menhir_stack _endpos _menhir_s _v _startpos ->
    match _menhir_s with
    | MenhirState0 ->
        let _menhir_stack = Obj.magic _menhir_stack in
        let _menhir_stack = Obj.magic _menhir_stack in
        let _endpos_x_ = _endpos in
        let (x : (IntermediateSyntax.decl list)) = _v in
        let _startpos_x_ = _startpos in
        let _v : (IntermediateSyntax.decl list IntermediateSyntax.annotated) = let _endpos = _endpos_x_ in
        let _startpos = _startpos_x_ in
        
# 236 "frontend/Parser.mly"
          ( x, (_startpos, _endpos) )
# 4894 "frontend/Parser.ml"
         in
        let _menhir_stack = (_menhir_stack, _menhir_s, _v) in
        let _menhir_stack = Obj.magic _menhir_stack in
        assert (not _menhir_env._menhir_error);
        let _tok = _menhir_env._menhir_token in
        (match _tok with
        | TOK_EOF ->
            let _menhir_stack = Obj.magic _menhir_stack in
            let _menhir_stack = Obj.magic _menhir_stack in
            let (_menhir_stack, _menhir_s, (t : (IntermediateSyntax.decl list IntermediateSyntax.annotated))) = _menhir_stack in
            let _2 = () in
            let _v : (
# 75 "frontend/Parser.mly"
       (IntermediateSyntax.decl list IntermediateSyntax.annotated)
# 4909 "frontend/Parser.ml"
            ) = 
# 79 "frontend/Parser.mly"
                                       ( t )
# 4913 "frontend/Parser.ml"
             in
            let _menhir_stack = Obj.magic _menhir_stack in
            let _menhir_stack = Obj.magic _menhir_stack in
            let (_1 : (
# 75 "frontend/Parser.mly"
       (IntermediateSyntax.decl list IntermediateSyntax.annotated)
# 4920 "frontend/Parser.ml"
            )) = _v in
            Obj.magic _1
        | _ ->
            assert (not _menhir_env._menhir_error);
            _menhir_env._menhir_error <- true;
            let _menhir_stack = Obj.magic _menhir_stack in
            let (_menhir_stack, _menhir_s, _) = _menhir_stack in
            _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s)
    | MenhirState223 ->
        let _menhir_stack = Obj.magic _menhir_stack in
        let _menhir_stack = Obj.magic _menhir_stack in
        let _endpos_xs_ = _endpos in
        let (xs : (IntermediateSyntax.decl list)) = _v in
        let _startpos_xs_ = _startpos in
        let (_menhir_stack, _endpos_x_, _menhir_s, (x : (IntermediateSyntax.decl)), _startpos_x_) = _menhir_stack in
        let _startpos = _startpos_x_ in
        let _endpos = _endpos_xs_ in
        let _v : (IntermediateSyntax.decl list) = 
# 187 "/usr/share/menhir/standard.mly"
    ( x :: xs )
# 4941 "frontend/Parser.ml"
         in
        _menhir_goto_list_decl_ _menhir_env _menhir_stack _endpos _menhir_s _v _startpos
    | _ ->
        _menhir_fail ()

and _menhir_reduce82 : _menhir_env -> 'ttv_tail -> _menhir_state -> 'ttv_return =
  fun _menhir_env _menhir_stack _menhir_s ->
    let _v : ((IntermediateSyntax.typ IntermediateSyntax.annotated *
   string IntermediateSyntax.annotated)
  list) = 
# 128 "/usr/share/menhir/standard.mly"
    ( [] )
# 4954 "frontend/Parser.ml"
     in
    _menhir_goto_loption_separated_nonempty_list_TOK_COMMA_parameter__ _menhir_env _menhir_stack _menhir_s _v

and _menhir_run23 : _menhir_env -> 'ttv_tail -> Lexing.position -> _menhir_state -> (
# 35 "frontend/Parser.mly"
       (string)
# 4961 "frontend/Parser.ml"
) -> Lexing.position -> 'ttv_return =
  fun _menhir_env _menhir_stack _endpos _menhir_s _v _startpos ->
    let _menhir_stack = (_menhir_stack, _endpos, _menhir_s, _v, _startpos) in
    let _menhir_env = _menhir_discard _menhir_env in
    _menhir_reduce101 _menhir_env (Obj.magic _menhir_stack)

and _menhir_run20 : _menhir_env -> 'ttv_tail -> Lexing.position -> _menhir_state -> (
# 71 "frontend/Parser.mly"
       (string)
# 4971 "frontend/Parser.ml"
) -> Lexing.position -> 'ttv_return =
  fun _menhir_env _menhir_stack _endpos _menhir_s _v _startpos ->
    let _menhir_env = _menhir_discard _menhir_env in
    let _menhir_stack = Obj.magic _menhir_stack in
    let _endpos_e_ = _endpos in
    let (e : (
# 71 "frontend/Parser.mly"
       (string)
# 4980 "frontend/Parser.ml"
    )) = _v in
    let _startpos_e_ = _startpos in
    let _startpos = _startpos_e_ in
    let _endpos = _endpos_e_ in
    let _v : (IntermediateSyntax.exp) = 
# 231 "frontend/Parser.mly"
                                         ( I_const e )
# 4988 "frontend/Parser.ml"
     in
    _menhir_goto_primary_exp _menhir_env _menhir_stack _endpos _menhir_s _v _startpos

and _menhir_run24 : _menhir_env -> 'ttv_tail -> Lexing.position -> _menhir_state -> Lexing.position -> 'ttv_return =
  fun _menhir_env _menhir_stack _endpos _menhir_s _startpos ->
    let _menhir_env = _menhir_discard _menhir_env in
    let _menhir_stack = Obj.magic _menhir_stack in
    let _endpos__1_ = _endpos in
    let _startpos__1_ = _startpos in
    let _1 = () in
    let _startpos = _startpos__1_ in
    let _endpos = _endpos__1_ in
    let _v : (IntermediateSyntax.exp) = 
# 227 "frontend/Parser.mly"
                                       ( I_URANDOM )
# 5004 "frontend/Parser.ml"
     in
    _menhir_goto_primary_exp _menhir_env _menhir_stack _endpos _menhir_s _v _startpos

and _menhir_run25 : _menhir_env -> 'ttv_tail -> Lexing.position -> _menhir_state -> Lexing.position -> 'ttv_return =
  fun _menhir_env _menhir_stack _endpos _menhir_s _startpos ->
    let _menhir_env = _menhir_discard _menhir_env in
    let _menhir_stack = Obj.magic _menhir_stack in
    let _endpos__1_ = _endpos in
    let _startpos__1_ = _startpos in
    let _1 = () in
    let _startpos = _startpos__1_ in
    let _endpos = _endpos__1_ in
    let _v : (IntermediateSyntax.exp) = 
# 225 "frontend/Parser.mly"
                                     ( I_TRUE )
# 5020 "frontend/Parser.ml"
     in
    _menhir_goto_primary_exp _menhir_env _menhir_stack _endpos _menhir_s _v _startpos

and _menhir_run26 : _menhir_env -> 'ttv_tail -> Lexing.position -> _menhir_state -> Lexing.position -> 'ttv_return =
  fun _menhir_env _menhir_stack _endpos _menhir_s _startpos ->
    let _menhir_env = _menhir_discard _menhir_env in
    let _menhir_stack = Obj.magic _menhir_stack in
    let _endpos__1_ = _endpos in
    let _startpos__1_ = _startpos in
    let _1 = () in
    let _startpos = _startpos__1_ in
    let _endpos = _endpos__1_ in
    let _v : (IntermediateSyntax.exp) = 
# 226 "frontend/Parser.mly"
                                      ( I_RANDOM )
# 5036 "frontend/Parser.ml"
     in
    _menhir_goto_primary_exp _menhir_env _menhir_stack _endpos _menhir_s _v _startpos

and _menhir_run27 : _menhir_env -> 'ttv_tail -> Lexing.position -> _menhir_state -> Lexing.position -> 'ttv_return =
  fun _menhir_env _menhir_stack _endpos _menhir_s _startpos ->
    let _menhir_stack = (_menhir_stack, _endpos, _menhir_s, _startpos) in
    let _menhir_env = _menhir_discard _menhir_env in
    let _tok = _menhir_env._menhir_token in
    match _tok with
    | TOK_FALSE ->
        _menhir_run43 _menhir_env (Obj.magic _menhir_stack) _menhir_env._menhir_lexbuf.Lexing.lex_curr_p MenhirState27 _menhir_env._menhir_lexbuf.Lexing.lex_start_p
    | TOK_LBRACKET ->
        _menhir_run35 _menhir_env (Obj.magic _menhir_stack) MenhirState27 _menhir_env._menhir_lexbuf.Lexing.lex_start_p
    | TOK_LPAREN ->
        _menhir_run34 _menhir_env (Obj.magic _menhir_stack) MenhirState27 _menhir_env._menhir_lexbuf.Lexing.lex_start_p
    | TOK_MINUS ->
        _menhir_run33 _menhir_env (Obj.magic _menhir_stack) MenhirState27 _menhir_env._menhir_lexbuf.Lexing.lex_start_p
    | TOK_MINUS_MINUS ->
        _menhir_run32 _menhir_env (Obj.magic _menhir_stack) _menhir_env._menhir_lexbuf.Lexing.lex_curr_p MenhirState27 _menhir_env._menhir_lexbuf.Lexing.lex_start_p
    | TOK_MULTIPLY ->
        _menhir_run30 _menhir_env (Obj.magic _menhir_stack) MenhirState27 _menhir_env._menhir_lexbuf.Lexing.lex_start_p
    | TOK_NOT ->
        _menhir_run29 _menhir_env (Obj.magic _menhir_stack) MenhirState27 _menhir_env._menhir_lexbuf.Lexing.lex_start_p
    | TOK_PLUS ->
        _menhir_run28 _menhir_env (Obj.magic _menhir_stack) MenhirState27 _menhir_env._menhir_lexbuf.Lexing.lex_start_p
    | TOK_PLUS_PLUS ->
        _menhir_run27 _menhir_env (Obj.magic _menhir_stack) _menhir_env._menhir_lexbuf.Lexing.lex_curr_p MenhirState27 _menhir_env._menhir_lexbuf.Lexing.lex_start_p
    | TOK_RANDOM ->
        _menhir_run26 _menhir_env (Obj.magic _menhir_stack) _menhir_env._menhir_lexbuf.Lexing.lex_curr_p MenhirState27 _menhir_env._menhir_lexbuf.Lexing.lex_start_p
    | TOK_TRUE ->
        _menhir_run25 _menhir_env (Obj.magic _menhir_stack) _menhir_env._menhir_lexbuf.Lexing.lex_curr_p MenhirState27 _menhir_env._menhir_lexbuf.Lexing.lex_start_p
    | TOK_URANDOM ->
        _menhir_run24 _menhir_env (Obj.magic _menhir_stack) _menhir_env._menhir_lexbuf.Lexing.lex_curr_p MenhirState27 _menhir_env._menhir_lexbuf.Lexing.lex_start_p
    | TOK_const _v ->
        _menhir_run20 _menhir_env (Obj.magic _menhir_stack) _menhir_env._menhir_lexbuf.Lexing.lex_curr_p MenhirState27 _v _menhir_env._menhir_lexbuf.Lexing.lex_start_p
    | TOK_id _v ->
        _menhir_run23 _menhir_env (Obj.magic _menhir_stack) _menhir_env._menhir_lexbuf.Lexing.lex_curr_p MenhirState27 _v _menhir_env._menhir_lexbuf.Lexing.lex_start_p
    | _ ->
        assert (not _menhir_env._menhir_error);
        _menhir_env._menhir_error <- true;
        _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) MenhirState27

and _menhir_run28 : _menhir_env -> 'ttv_tail -> _menhir_state -> Lexing.position -> 'ttv_return =
  fun _menhir_env _menhir_stack _menhir_s _startpos ->
    let _menhir_env = _menhir_discard _menhir_env in
    let _menhir_stack = Obj.magic _menhir_stack in
    let _startpos__1_ = _startpos in
    let _1 = () in
    let _startpos = _startpos__1_ in
    let _v : (IntermediateSyntax.unaryOp) = 
# 215 "frontend/Parser.mly"
            ( I_PLUS )
# 5089 "frontend/Parser.ml"
     in
    _menhir_goto_unary_op _menhir_env _menhir_stack _menhir_s _v _startpos

and _menhir_run29 : _menhir_env -> 'ttv_tail -> _menhir_state -> Lexing.position -> 'ttv_return =
  fun _menhir_env _menhir_stack _menhir_s _startpos ->
    let _menhir_stack = (_menhir_stack, _menhir_s, _startpos) in
    let _menhir_env = _menhir_discard _menhir_env in
    let _tok = _menhir_env._menhir_token in
    match _tok with
    | TOK_FALSE ->
        _menhir_run43 _menhir_env (Obj.magic _menhir_stack) _menhir_env._menhir_lexbuf.Lexing.lex_curr_p MenhirState29 _menhir_env._menhir_lexbuf.Lexing.lex_start_p
    | TOK_LBRACKET ->
        _menhir_run35 _menhir_env (Obj.magic _menhir_stack) MenhirState29 _menhir_env._menhir_lexbuf.Lexing.lex_start_p
    | TOK_LPAREN ->
        _menhir_run34 _menhir_env (Obj.magic _menhir_stack) MenhirState29 _menhir_env._menhir_lexbuf.Lexing.lex_start_p
    | TOK_MINUS ->
        _menhir_run33 _menhir_env (Obj.magic _menhir_stack) MenhirState29 _menhir_env._menhir_lexbuf.Lexing.lex_start_p
    | TOK_MINUS_MINUS ->
        _menhir_run32 _menhir_env (Obj.magic _menhir_stack) _menhir_env._menhir_lexbuf.Lexing.lex_curr_p MenhirState29 _menhir_env._menhir_lexbuf.Lexing.lex_start_p
    | TOK_MULTIPLY ->
        _menhir_run30 _menhir_env (Obj.magic _menhir_stack) MenhirState29 _menhir_env._menhir_lexbuf.Lexing.lex_start_p
    | TOK_NOT ->
        _menhir_run29 _menhir_env (Obj.magic _menhir_stack) MenhirState29 _menhir_env._menhir_lexbuf.Lexing.lex_start_p
    | TOK_PLUS ->
        _menhir_run28 _menhir_env (Obj.magic _menhir_stack) MenhirState29 _menhir_env._menhir_lexbuf.Lexing.lex_start_p
    | TOK_PLUS_PLUS ->
        _menhir_run27 _menhir_env (Obj.magic _menhir_stack) _menhir_env._menhir_lexbuf.Lexing.lex_curr_p MenhirState29 _menhir_env._menhir_lexbuf.Lexing.lex_start_p
    | TOK_RANDOM ->
        _menhir_run26 _menhir_env (Obj.magic _menhir_stack) _menhir_env._menhir_lexbuf.Lexing.lex_curr_p MenhirState29 _menhir_env._menhir_lexbuf.Lexing.lex_start_p
    | TOK_TRUE ->
        _menhir_run25 _menhir_env (Obj.magic _menhir_stack) _menhir_env._menhir_lexbuf.Lexing.lex_curr_p MenhirState29 _menhir_env._menhir_lexbuf.Lexing.lex_start_p
    | TOK_URANDOM ->
        _menhir_run24 _menhir_env (Obj.magic _menhir_stack) _menhir_env._menhir_lexbuf.Lexing.lex_curr_p MenhirState29 _menhir_env._menhir_lexbuf.Lexing.lex_start_p
    | TOK_const _v ->
        _menhir_run20 _menhir_env (Obj.magic _menhir_stack) _menhir_env._menhir_lexbuf.Lexing.lex_curr_p MenhirState29 _v _menhir_env._menhir_lexbuf.Lexing.lex_start_p
    | TOK_id _v ->
        _menhir_run23 _menhir_env (Obj.magic _menhir_stack) _menhir_env._menhir_lexbuf.Lexing.lex_curr_p MenhirState29 _v _menhir_env._menhir_lexbuf.Lexing.lex_start_p
    | _ ->
        assert (not _menhir_env._menhir_error);
        _menhir_env._menhir_error <- true;
        _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) MenhirState29

and _menhir_run30 : _menhir_env -> 'ttv_tail -> _menhir_state -> Lexing.position -> 'ttv_return =
  fun _menhir_env _menhir_stack _menhir_s _startpos ->
    let _menhir_stack = (_menhir_stack, _menhir_s, _startpos) in
    let _menhir_env = _menhir_discard _menhir_env in
    let _tok = _menhir_env._menhir_token in
    match _tok with
    | TOK_id _v ->
        let _menhir_stack = Obj.magic _menhir_stack in
        let _endpos = _menhir_env._menhir_lexbuf.Lexing.lex_curr_p in
        let _startpos = _menhir_env._menhir_lexbuf.Lexing.lex_start_p in
        let _menhir_env = _menhir_discard _menhir_env in
        let _menhir_stack = Obj.magic _menhir_stack in
        let _endpos_e_ = _endpos in
        let (e : (
# 35 "frontend/Parser.mly"
       (string)
# 5148 "frontend/Parser.ml"
        )) = _v in
        let _startpos_e_ = _startpos in
        let (_menhir_stack, _menhir_s, _startpos__1_) = _menhir_stack in
        let _1 = () in
        let _startpos = _startpos__1_ in
        let _endpos = _endpos_e_ in
        let _v : (IntermediateSyntax.exp) = 
# 230 "frontend/Parser.mly"
                                                ( I_id e )
# 5158 "frontend/Parser.ml"
         in
        _menhir_goto_primary_exp _menhir_env _menhir_stack _endpos _menhir_s _v _startpos
    | _ ->
        assert (not _menhir_env._menhir_error);
        _menhir_env._menhir_error <- true;
        let _menhir_stack = Obj.magic _menhir_stack in
        let (_menhir_stack, _menhir_s, _) = _menhir_stack in
        _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s

and _menhir_run32 : _menhir_env -> 'ttv_tail -> Lexing.position -> _menhir_state -> Lexing.position -> 'ttv_return =
  fun _menhir_env _menhir_stack _endpos _menhir_s _startpos ->
    let _menhir_stack = (_menhir_stack, _endpos, _menhir_s, _startpos) in
    let _menhir_env = _menhir_discard _menhir_env in
    let _tok = _menhir_env._menhir_token in
    match _tok with
    | TOK_FALSE ->
        _menhir_run43 _menhir_env (Obj.magic _menhir_stack) _menhir_env._menhir_lexbuf.Lexing.lex_curr_p MenhirState32 _menhir_env._menhir_lexbuf.Lexing.lex_start_p
    | TOK_LBRACKET ->
        _menhir_run35 _menhir_env (Obj.magic _menhir_stack) MenhirState32 _menhir_env._menhir_lexbuf.Lexing.lex_start_p
    | TOK_LPAREN ->
        _menhir_run34 _menhir_env (Obj.magic _menhir_stack) MenhirState32 _menhir_env._menhir_lexbuf.Lexing.lex_start_p
    | TOK_MINUS ->
        _menhir_run33 _menhir_env (Obj.magic _menhir_stack) MenhirState32 _menhir_env._menhir_lexbuf.Lexing.lex_start_p
    | TOK_MINUS_MINUS ->
        _menhir_run32 _menhir_env (Obj.magic _menhir_stack) _menhir_env._menhir_lexbuf.Lexing.lex_curr_p MenhirState32 _menhir_env._menhir_lexbuf.Lexing.lex_start_p
    | TOK_MULTIPLY ->
        _menhir_run30 _menhir_env (Obj.magic _menhir_stack) MenhirState32 _menhir_env._menhir_lexbuf.Lexing.lex_start_p
    | TOK_NOT ->
        _menhir_run29 _menhir_env (Obj.magic _menhir_stack) MenhirState32 _menhir_env._menhir_lexbuf.Lexing.lex_start_p
    | TOK_PLUS ->
        _menhir_run28 _menhir_env (Obj.magic _menhir_stack) MenhirState32 _menhir_env._menhir_lexbuf.Lexing.lex_start_p
    | TOK_PLUS_PLUS ->
        _menhir_run27 _menhir_env (Obj.magic _menhir_stack) _menhir_env._menhir_lexbuf.Lexing.lex_curr_p MenhirState32 _menhir_env._menhir_lexbuf.Lexing.lex_start_p
    | TOK_RANDOM ->
        _menhir_run26 _menhir_env (Obj.magic _menhir_stack) _menhir_env._menhir_lexbuf.Lexing.lex_curr_p MenhirState32 _menhir_env._menhir_lexbuf.Lexing.lex_start_p
    | TOK_TRUE ->
        _menhir_run25 _menhir_env (Obj.magic _menhir_stack) _menhir_env._menhir_lexbuf.Lexing.lex_curr_p MenhirState32 _menhir_env._menhir_lexbuf.Lexing.lex_start_p
    | TOK_URANDOM ->
        _menhir_run24 _menhir_env (Obj.magic _menhir_stack) _menhir_env._menhir_lexbuf.Lexing.lex_curr_p MenhirState32 _menhir_env._menhir_lexbuf.Lexing.lex_start_p
    | TOK_const _v ->
        _menhir_run20 _menhir_env (Obj.magic _menhir_stack) _menhir_env._menhir_lexbuf.Lexing.lex_curr_p MenhirState32 _v _menhir_env._menhir_lexbuf.Lexing.lex_start_p
    | TOK_id _v ->
        _menhir_run23 _menhir_env (Obj.magic _menhir_stack) _menhir_env._menhir_lexbuf.Lexing.lex_curr_p MenhirState32 _v _menhir_env._menhir_lexbuf.Lexing.lex_start_p
    | _ ->
        assert (not _menhir_env._menhir_error);
        _menhir_env._menhir_error <- true;
        _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) MenhirState32

and _menhir_run33 : _menhir_env -> 'ttv_tail -> _menhir_state -> Lexing.position -> 'ttv_return =
  fun _menhir_env _menhir_stack _menhir_s _startpos ->
    let _menhir_env = _menhir_discard _menhir_env in
    let _menhir_stack = Obj.magic _menhir_stack in
    let _startpos__1_ = _startpos in
    let _1 = () in
    let _startpos = _startpos__1_ in
    let _v : (IntermediateSyntax.unaryOp) = 
# 216 "frontend/Parser.mly"
             ( I_MINUS )
# 5217 "frontend/Parser.ml"
     in
    _menhir_goto_unary_op _menhir_env _menhir_stack _menhir_s _v _startpos

and _menhir_run34 : _menhir_env -> 'ttv_tail -> _menhir_state -> Lexing.position -> 'ttv_return =
  fun _menhir_env _menhir_stack _menhir_s _startpos ->
    let _menhir_stack = (_menhir_stack, _menhir_s, _startpos) in
    let _menhir_env = _menhir_discard _menhir_env in
    let _tok = _menhir_env._menhir_token in
    match _tok with
    | TOK_FALSE ->
        _menhir_run43 _menhir_env (Obj.magic _menhir_stack) _menhir_env._menhir_lexbuf.Lexing.lex_curr_p MenhirState34 _menhir_env._menhir_lexbuf.Lexing.lex_start_p
    | TOK_LBRACKET ->
        _menhir_run35 _menhir_env (Obj.magic _menhir_stack) MenhirState34 _menhir_env._menhir_lexbuf.Lexing.lex_start_p
    | TOK_LPAREN ->
        _menhir_run34 _menhir_env (Obj.magic _menhir_stack) MenhirState34 _menhir_env._menhir_lexbuf.Lexing.lex_start_p
    | TOK_MINUS ->
        _menhir_run33 _menhir_env (Obj.magic _menhir_stack) MenhirState34 _menhir_env._menhir_lexbuf.Lexing.lex_start_p
    | TOK_MINUS_MINUS ->
        _menhir_run32 _menhir_env (Obj.magic _menhir_stack) _menhir_env._menhir_lexbuf.Lexing.lex_curr_p MenhirState34 _menhir_env._menhir_lexbuf.Lexing.lex_start_p
    | TOK_MULTIPLY ->
        _menhir_run30 _menhir_env (Obj.magic _menhir_stack) MenhirState34 _menhir_env._menhir_lexbuf.Lexing.lex_start_p
    | TOK_NOT ->
        _menhir_run29 _menhir_env (Obj.magic _menhir_stack) MenhirState34 _menhir_env._menhir_lexbuf.Lexing.lex_start_p
    | TOK_PLUS ->
        _menhir_run28 _menhir_env (Obj.magic _menhir_stack) MenhirState34 _menhir_env._menhir_lexbuf.Lexing.lex_start_p
    | TOK_PLUS_PLUS ->
        _menhir_run27 _menhir_env (Obj.magic _menhir_stack) _menhir_env._menhir_lexbuf.Lexing.lex_curr_p MenhirState34 _menhir_env._menhir_lexbuf.Lexing.lex_start_p
    | TOK_RANDOM ->
        _menhir_run26 _menhir_env (Obj.magic _menhir_stack) _menhir_env._menhir_lexbuf.Lexing.lex_curr_p MenhirState34 _menhir_env._menhir_lexbuf.Lexing.lex_start_p
    | TOK_TRUE ->
        _menhir_run25 _menhir_env (Obj.magic _menhir_stack) _menhir_env._menhir_lexbuf.Lexing.lex_curr_p MenhirState34 _menhir_env._menhir_lexbuf.Lexing.lex_start_p
    | TOK_URANDOM ->
        _menhir_run24 _menhir_env (Obj.magic _menhir_stack) _menhir_env._menhir_lexbuf.Lexing.lex_curr_p MenhirState34 _menhir_env._menhir_lexbuf.Lexing.lex_start_p
    | TOK_const _v ->
        _menhir_run20 _menhir_env (Obj.magic _menhir_stack) _menhir_env._menhir_lexbuf.Lexing.lex_curr_p MenhirState34 _v _menhir_env._menhir_lexbuf.Lexing.lex_start_p
    | TOK_id _v ->
        _menhir_run23 _menhir_env (Obj.magic _menhir_stack) _menhir_env._menhir_lexbuf.Lexing.lex_curr_p MenhirState34 _v _menhir_env._menhir_lexbuf.Lexing.lex_start_p
    | _ ->
        assert (not _menhir_env._menhir_error);
        _menhir_env._menhir_error <- true;
        _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) MenhirState34

and _menhir_run35 : _menhir_env -> 'ttv_tail -> _menhir_state -> Lexing.position -> 'ttv_return =
  fun _menhir_env _menhir_stack _menhir_s _startpos ->
    let _menhir_stack = (_menhir_stack, _menhir_s, _startpos) in
    let _menhir_env = _menhir_discard _menhir_env in
    let _tok = _menhir_env._menhir_token in
    match _tok with
    | TOK_MINUS ->
        _menhir_run33 _menhir_env (Obj.magic _menhir_stack) MenhirState35 _menhir_env._menhir_lexbuf.Lexing.lex_start_p
    | TOK_PLUS ->
        _menhir_run28 _menhir_env (Obj.magic _menhir_stack) MenhirState35 _menhir_env._menhir_lexbuf.Lexing.lex_start_p
    | TOK_const _ ->
        _menhir_reduce90 _menhir_env (Obj.magic _menhir_stack) MenhirState35
    | _ ->
        assert (not _menhir_env._menhir_error);
        _menhir_env._menhir_error <- true;
        _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) MenhirState35

and _menhir_run43 : _menhir_env -> 'ttv_tail -> Lexing.position -> _menhir_state -> Lexing.position -> 'ttv_return =
  fun _menhir_env _menhir_stack _endpos _menhir_s _startpos ->
    let _menhir_env = _menhir_discard _menhir_env in
    let _menhir_stack = Obj.magic _menhir_stack in
    let _endpos__1_ = _endpos in
    let _startpos__1_ = _startpos in
    let _1 = () in
    let _startpos = _startpos__1_ in
    let _endpos = _endpos__1_ in
    let _v : (IntermediateSyntax.exp) = 
# 228 "frontend/Parser.mly"
                                      ( I_FALSE )
# 5289 "frontend/Parser.ml"
     in
    _menhir_goto_primary_exp _menhir_env _menhir_stack _endpos _menhir_s _v _startpos

and _menhir_run2 : _menhir_env -> 'ttv_tail -> Lexing.position -> _menhir_state -> (
# 35 "frontend/Parser.mly"
       (string)
# 5296 "frontend/Parser.ml"
) -> Lexing.position -> 'ttv_return =
  fun _menhir_env _menhir_stack _endpos _menhir_s _v _startpos ->
    let _menhir_stack = (_menhir_stack, _endpos, _menhir_s, _v, _startpos) in
    let _menhir_env = _menhir_discard _menhir_env in
    _menhir_reduce4 _menhir_env (Obj.magic _menhir_stack)

and _menhir_goto_global_typ : _menhir_env -> 'ttv_tail -> Lexing.position -> _menhir_state -> (IntermediateSyntax.typ) -> Lexing.position -> 'ttv_return =
  fun _menhir_env _menhir_stack _endpos _menhir_s _v _startpos ->
    let _menhir_stack = Obj.magic _menhir_stack in
    let _menhir_stack = Obj.magic _menhir_stack in
    let _endpos_x_ = _endpos in
    let (x : (IntermediateSyntax.typ)) = _v in
    let _startpos_x_ = _startpos in
    let _startpos = _startpos_x_ in
    let _v : (IntermediateSyntax.typ IntermediateSyntax.annotated) = let _endpos = _endpos_x_ in
    let _startpos = _startpos_x_ in
    
# 236 "frontend/Parser.mly"
          ( x, (_startpos, _endpos) )
# 5316 "frontend/Parser.ml"
     in
    let _menhir_stack = (_menhir_stack, _menhir_s, _v, _startpos) in
    match _menhir_s with
    | MenhirState228 | MenhirState197 | MenhirState4 | MenhirState11 ->
        let _menhir_stack = Obj.magic _menhir_stack in
        assert (not _menhir_env._menhir_error);
        let _tok = _menhir_env._menhir_token in
        (match _tok with
        | TOK_id _v ->
            _menhir_run2 _menhir_env (Obj.magic _menhir_stack) _menhir_env._menhir_lexbuf.Lexing.lex_curr_p MenhirState14 _v _menhir_env._menhir_lexbuf.Lexing.lex_start_p
        | _ ->
            assert (not _menhir_env._menhir_error);
            _menhir_env._menhir_error <- true;
            _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) MenhirState14)
    | MenhirState18 | MenhirState193 | MenhirState120 | MenhirState129 | MenhirState188 | MenhirState185 | MenhirState150 | MenhirState154 | MenhirState171 | MenhirState131 ->
        let _menhir_stack = Obj.magic _menhir_stack in
        assert (not _menhir_env._menhir_error);
        let _tok = _menhir_env._menhir_token in
        (match _tok with
        | TOK_MULTIPLY ->
            _menhir_run134 _menhir_env (Obj.magic _menhir_stack) MenhirState133 _menhir_env._menhir_lexbuf.Lexing.lex_start_p
        | TOK_id _v ->
            _menhir_run2 _menhir_env (Obj.magic _menhir_stack) _menhir_env._menhir_lexbuf.Lexing.lex_curr_p MenhirState133 _v _menhir_env._menhir_lexbuf.Lexing.lex_start_p
        | TOK_SEMICOLON ->
            _menhir_reduce80 _menhir_env (Obj.magic _menhir_stack) MenhirState133
        | _ ->
            assert (not _menhir_env._menhir_error);
            _menhir_env._menhir_error <- true;
            _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) MenhirState133)
    | MenhirState0 | MenhirState223 ->
        let _menhir_stack = Obj.magic _menhir_stack in
        assert (not _menhir_env._menhir_error);
        let _tok = _menhir_env._menhir_token in
        (match _tok with
        | TOK_MULTIPLY ->
            _menhir_run134 _menhir_env (Obj.magic _menhir_stack) MenhirState226 _menhir_env._menhir_lexbuf.Lexing.lex_start_p
        | TOK_id _v ->
            _menhir_run2 _menhir_env (Obj.magic _menhir_stack) _menhir_env._menhir_lexbuf.Lexing.lex_curr_p MenhirState226 _v _menhir_env._menhir_lexbuf.Lexing.lex_start_p
        | TOK_SEMICOLON ->
            _menhir_reduce80 _menhir_env (Obj.magic _menhir_stack) MenhirState226
        | _ ->
            assert (not _menhir_env._menhir_error);
            _menhir_env._menhir_error <- true;
            _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) MenhirState226)
    | _ ->
        _menhir_fail ()

and _menhir_errorcase : _menhir_env -> 'ttv_tail -> _menhir_state -> 'ttv_return =
  fun _menhir_env _menhir_stack _menhir_s ->
    match _menhir_s with
    | MenhirState234 ->
        let _menhir_stack = Obj.magic _menhir_stack in
        let ((_menhir_stack, _menhir_s, _), _) = _menhir_stack in
        _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s
    | MenhirState230 ->
        let _menhir_stack = Obj.magic _menhir_stack in
        let ((_menhir_stack, _menhir_s, _), _) = _menhir_stack in
        _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s
    | MenhirState228 ->
        let _menhir_stack = Obj.magic _menhir_stack in
        let ((_menhir_stack, _menhir_s, _, _), _) = _menhir_stack in
        _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s
    | MenhirState226 ->
        let _menhir_stack = Obj.magic _menhir_stack in
        let (_menhir_stack, _menhir_s, _, _) = _menhir_stack in
        _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s
    | MenhirState223 ->
        let _menhir_stack = Obj.magic _menhir_stack in
        let (_menhir_stack, _, _menhir_s, _, _) = _menhir_stack in
        _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s
    | MenhirState215 ->
        let _menhir_stack = Obj.magic _menhir_stack in
        let (_menhir_stack, _menhir_s, _, _) = _menhir_stack in
        _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s
    | MenhirState214 ->
        let _menhir_stack = Obj.magic _menhir_stack in
        let (_menhir_stack, _menhir_s, _) = _menhir_stack in
        _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s
    | MenhirState211 ->
        let _menhir_stack = Obj.magic _menhir_stack in
        let (_menhir_stack, _menhir_s, _) = _menhir_stack in
        _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s
    | MenhirState208 ->
        let _menhir_stack = Obj.magic _menhir_stack in
        let (_menhir_stack, _, _menhir_s, _, _) = _menhir_stack in
        _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s
    | MenhirState207 ->
        let _menhir_stack = Obj.magic _menhir_stack in
        let ((_menhir_stack, _menhir_s, _), _, _) = _menhir_stack in
        _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s
    | MenhirState203 ->
        let _menhir_stack = Obj.magic _menhir_stack in
        let ((_menhir_stack, _menhir_s, _), _) = _menhir_stack in
        _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s
    | MenhirState199 ->
        let _menhir_stack = Obj.magic _menhir_stack in
        let ((_menhir_stack, _menhir_s, _), _) = _menhir_stack in
        _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s
    | MenhirState197 ->
        let _menhir_stack = Obj.magic _menhir_stack in
        let ((_menhir_stack, _menhir_s, _, _), _) = _menhir_stack in
        _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s
    | MenhirState193 ->
        let _menhir_stack = Obj.magic _menhir_stack in
        let (_menhir_stack, _, _menhir_s, _) = _menhir_stack in
        _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s
    | MenhirState188 ->
        let _menhir_stack = Obj.magic _menhir_stack in
        let (_menhir_stack, _, _menhir_s, _) = _menhir_stack in
        _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s
    | MenhirState185 ->
        let _menhir_stack = Obj.magic _menhir_stack in
        let ((_menhir_stack, _, _menhir_s, _, _), _) = _menhir_stack in
        _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s
    | MenhirState183 ->
        let _menhir_stack = Obj.magic _menhir_stack in
        let ((_menhir_stack, _, _menhir_s, _, _), _, _) = _menhir_stack in
        _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s
    | MenhirState181 ->
        let _menhir_stack = Obj.magic _menhir_stack in
        let ((_menhir_stack, _, _menhir_s, _, _), _, _) = _menhir_stack in
        _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s
    | MenhirState171 ->
        let _menhir_stack = Obj.magic _menhir_stack in
        let (_menhir_stack, _, _menhir_s, _) = _menhir_stack in
        _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s
    | MenhirState156 ->
        let _menhir_stack = Obj.magic _menhir_stack in
        let ((_menhir_stack, _menhir_s, _), _) = _menhir_stack in
        _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s
    | MenhirState154 ->
        let _menhir_stack = Obj.magic _menhir_stack in
        let ((_menhir_stack, _, _menhir_s, _, _), _) = _menhir_stack in
        _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s
    | MenhirState152 ->
        let _menhir_stack = Obj.magic _menhir_stack in
        let ((_menhir_stack, _menhir_s, _), _) = _menhir_stack in
        _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s
    | MenhirState150 ->
        let _menhir_stack = Obj.magic _menhir_stack in
        let ((_menhir_stack, _, _menhir_s, _, _), _) = _menhir_stack in
        _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s
    | MenhirState148 ->
        let _menhir_stack = Obj.magic _menhir_stack in
        let ((_menhir_stack, _, _menhir_s, _, _), _, _) = _menhir_stack in
        _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s
    | MenhirState146 ->
        let _menhir_stack = Obj.magic _menhir_stack in
        let (_menhir_stack, _, _menhir_s, _, _) = _menhir_stack in
        _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s
    | MenhirState142 ->
        let _menhir_stack = Obj.magic _menhir_stack in
        let (_menhir_stack, _menhir_s, _, _) = _menhir_stack in
        _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s
    | MenhirState139 ->
        let _menhir_stack = Obj.magic _menhir_stack in
        let (_menhir_stack, _menhir_s, _) = _menhir_stack in
        _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s
    | MenhirState134 ->
        let _menhir_stack = Obj.magic _menhir_stack in
        let (_menhir_stack, _menhir_s, _) = _menhir_stack in
        _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s
    | MenhirState133 ->
        let _menhir_stack = Obj.magic _menhir_stack in
        let (_menhir_stack, _menhir_s, _, _) = _menhir_stack in
        _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s
    | MenhirState131 ->
        let _menhir_stack = Obj.magic _menhir_stack in
        let ((_menhir_stack, _menhir_s, _), _) = _menhir_stack in
        _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s
    | MenhirState129 ->
        let _menhir_stack = Obj.magic _menhir_stack in
        let ((_menhir_stack, _, _menhir_s, _, _), _) = _menhir_stack in
        _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s
    | MenhirState127 ->
        let _menhir_stack = Obj.magic _menhir_stack in
        let ((_menhir_stack, _menhir_s, _), _) = _menhir_stack in
        _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s
    | MenhirState122 ->
        let _menhir_stack = Obj.magic _menhir_stack in
        let (_menhir_stack, _menhir_s, _) = _menhir_stack in
        _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s
    | MenhirState120 ->
        let _menhir_stack = Obj.magic _menhir_stack in
        let ((_menhir_stack, _, _menhir_s, _, _), _) = _menhir_stack in
        _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s
    | MenhirState112 ->
        let _menhir_stack = Obj.magic _menhir_stack in
        let (_menhir_stack, _, _menhir_s, _, _) = _menhir_stack in
        _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s
    | MenhirState106 ->
        let _menhir_stack = Obj.magic _menhir_stack in
        let (_menhir_stack, _, _menhir_s, _, _) = _menhir_stack in
        _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s
    | MenhirState101 ->
        let _menhir_stack = Obj.magic _menhir_stack in
        let (_menhir_stack, _, _menhir_s, _, _) = _menhir_stack in
        _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s
    | MenhirState98 ->
        let _menhir_stack = Obj.magic _menhir_stack in
        let (_menhir_stack, _, _menhir_s, _, _) = _menhir_stack in
        _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s
    | MenhirState95 ->
        let _menhir_stack = Obj.magic _menhir_stack in
        let (_menhir_stack, _menhir_s, _, _) = _menhir_stack in
        _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s
    | MenhirState92 ->
        let _menhir_stack = Obj.magic _menhir_stack in
        let (_menhir_stack, _, _menhir_s, _, _) = _menhir_stack in
        _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s
    | MenhirState90 ->
        let _menhir_stack = Obj.magic _menhir_stack in
        let (_menhir_stack, _, _menhir_s, _, _) = _menhir_stack in
        _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s
    | MenhirState88 ->
        let _menhir_stack = Obj.magic _menhir_stack in
        let (_menhir_stack, _, _menhir_s, _, _) = _menhir_stack in
        _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s
    | MenhirState85 ->
        let _menhir_stack = Obj.magic _menhir_stack in
        let ((_menhir_stack, _, _menhir_s, _, _), _) = _menhir_stack in
        _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s
    | MenhirState82 ->
        let _menhir_stack = Obj.magic _menhir_stack in
        let ((_menhir_stack, _, _menhir_s, _, _), _) = _menhir_stack in
        _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s
    | MenhirState79 ->
        let _menhir_stack = Obj.magic _menhir_stack in
        let (_menhir_stack, _, _menhir_s, _, _) = _menhir_stack in
        _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s
    | MenhirState77 ->
        let _menhir_stack = Obj.magic _menhir_stack in
        let (_menhir_stack, _, _menhir_s, _, _) = _menhir_stack in
        _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s
    | MenhirState75 ->
        let _menhir_stack = Obj.magic _menhir_stack in
        let ((_menhir_stack, _, _menhir_s, _, _), _) = _menhir_stack in
        _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s
    | MenhirState72 ->
        let _menhir_stack = Obj.magic _menhir_stack in
        let (_menhir_stack, _, _menhir_s, _, _) = _menhir_stack in
        _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s
    | MenhirState70 ->
        let _menhir_stack = Obj.magic _menhir_stack in
        let ((_menhir_stack, _, _menhir_s, _, _), _) = _menhir_stack in
        _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s
    | MenhirState52 ->
        let _menhir_stack = Obj.magic _menhir_stack in
        let ((_menhir_stack, _menhir_s, _, _), _) = _menhir_stack in
        _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s
    | MenhirState44 ->
        let _menhir_stack = Obj.magic _menhir_stack in
        let (_menhir_stack, _menhir_s, _, _) = _menhir_stack in
        _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s
    | MenhirState39 ->
        let _menhir_stack = Obj.magic _menhir_stack in
        let ((_menhir_stack, _menhir_s, _), _, _, _) = _menhir_stack in
        _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s
    | MenhirState35 ->
        let _menhir_stack = Obj.magic _menhir_stack in
        let (_menhir_stack, _menhir_s, _) = _menhir_stack in
        _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s
    | MenhirState34 ->
        let _menhir_stack = Obj.magic _menhir_stack in
        let (_menhir_stack, _menhir_s, _) = _menhir_stack in
        _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s
    | MenhirState32 ->
        let _menhir_stack = Obj.magic _menhir_stack in
        let (_menhir_stack, _, _menhir_s, _) = _menhir_stack in
        _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s
    | MenhirState29 ->
        let _menhir_stack = Obj.magic _menhir_stack in
        let (_menhir_stack, _menhir_s, _) = _menhir_stack in
        _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s
    | MenhirState27 ->
        let _menhir_stack = Obj.magic _menhir_stack in
        let (_menhir_stack, _, _menhir_s, _) = _menhir_stack in
        _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s
    | MenhirState22 ->
        let _menhir_stack = Obj.magic _menhir_stack in
        let ((_menhir_stack, _menhir_s, _), _) = _menhir_stack in
        _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s
    | MenhirState18 ->
        let _menhir_stack = Obj.magic _menhir_stack in
        let (_menhir_stack, _menhir_s, _) = _menhir_stack in
        _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s
    | MenhirState17 ->
        let _menhir_stack = Obj.magic _menhir_stack in
        let ((_menhir_stack, _menhir_s, _), _) = _menhir_stack in
        _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s
    | MenhirState14 ->
        let _menhir_stack = Obj.magic _menhir_stack in
        let (_menhir_stack, _menhir_s, _, _) = _menhir_stack in
        _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s
    | MenhirState11 ->
        let _menhir_stack = Obj.magic _menhir_stack in
        let (_menhir_stack, _menhir_s, _) = _menhir_stack in
        _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s
    | MenhirState4 ->
        let _menhir_stack = Obj.magic _menhir_stack in
        let ((_menhir_stack, _menhir_s, _), _) = _menhir_stack in
        _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s
    | MenhirState1 ->
        let _menhir_stack = Obj.magic _menhir_stack in
        let (_menhir_stack, _menhir_s, _) = _menhir_stack in
        _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s
    | MenhirState0 ->
        let _menhir_stack = Obj.magic _menhir_stack in
        raise _eRR

and _menhir_reduce72 : _menhir_env -> 'ttv_tail -> _menhir_state -> 'ttv_return =
  fun _menhir_env _menhir_stack _menhir_s ->
    let (_, _startpos) = Obj.magic _menhir_stack in
    let _endpos = _startpos in
    let _v : (IntermediateSyntax.decl list) = 
# 185 "/usr/share/menhir/standard.mly"
    ( [] )
# 5634 "frontend/Parser.ml"
     in
    _menhir_goto_list_decl_ _menhir_env _menhir_stack _endpos _menhir_s _v _startpos

and _menhir_run1 : _menhir_env -> 'ttv_tail -> _menhir_state -> Lexing.position -> 'ttv_return =
  fun _menhir_env _menhir_stack _menhir_s _startpos ->
    let _menhir_stack = (_menhir_stack, _menhir_s, _startpos) in
    let _menhir_env = _menhir_discard _menhir_env in
    let _tok = _menhir_env._menhir_token in
    match _tok with
    | TOK_ASSERT ->
        let _menhir_stack = Obj.magic _menhir_stack in
        let _menhir_s = MenhirState1 in
        let _startpos = _menhir_env._menhir_lexbuf.Lexing.lex_start_p in
        let _menhir_stack = (_menhir_stack, _menhir_s, _startpos) in
        let _menhir_env = _menhir_discard _menhir_env in
        let _tok = _menhir_env._menhir_token in
        (match _tok with
        | TOK_LPAREN ->
            let _menhir_stack = Obj.magic _menhir_stack in
            let _startpos = _menhir_env._menhir_lexbuf.Lexing.lex_start_p in
            let _menhir_stack = (_menhir_stack, _startpos) in
            let _menhir_env = _menhir_discard _menhir_env in
            let _tok = _menhir_env._menhir_token in
            (match _tok with
            | TOK_CHAR ->
                _menhir_run8 _menhir_env (Obj.magic _menhir_stack) _menhir_env._menhir_lexbuf.Lexing.lex_curr_p MenhirState4 _menhir_env._menhir_lexbuf.Lexing.lex_start_p
            | TOK_INT ->
                _menhir_run7 _menhir_env (Obj.magic _menhir_stack) _menhir_env._menhir_lexbuf.Lexing.lex_curr_p MenhirState4 _menhir_env._menhir_lexbuf.Lexing.lex_start_p
            | TOK_UINT ->
                _menhir_run5 _menhir_env (Obj.magic _menhir_stack) MenhirState4 _menhir_env._menhir_lexbuf.Lexing.lex_start_p
            | TOK_RPAREN ->
                _menhir_reduce82 _menhir_env (Obj.magic _menhir_stack) MenhirState4
            | _ ->
                assert (not _menhir_env._menhir_error);
                _menhir_env._menhir_error <- true;
                _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) MenhirState4)
        | _ ->
            assert (not _menhir_env._menhir_error);
            _menhir_env._menhir_error <- true;
            let _menhir_stack = Obj.magic _menhir_stack in
            let (_menhir_stack, _menhir_s, _) = _menhir_stack in
            _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s)
    | TOK_id _v ->
        _menhir_run2 _menhir_env (Obj.magic _menhir_stack) _menhir_env._menhir_lexbuf.Lexing.lex_curr_p MenhirState1 _v _menhir_env._menhir_lexbuf.Lexing.lex_start_p
    | _ ->
        assert (not _menhir_env._menhir_error);
        _menhir_env._menhir_error <- true;
        _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) MenhirState1

and _menhir_run5 : _menhir_env -> 'ttv_tail -> _menhir_state -> Lexing.position -> 'ttv_return =
  fun _menhir_env _menhir_stack _menhir_s _startpos ->
    let _menhir_stack = (_menhir_stack, _menhir_s, _startpos) in
    let _menhir_env = _menhir_discard _menhir_env in
    let _tok = _menhir_env._menhir_token in
    match _tok with
    | TOK_INT ->
        let _menhir_stack = Obj.magic _menhir_stack in
        let _endpos = _menhir_env._menhir_lexbuf.Lexing.lex_curr_p in
        let _startpos = _menhir_env._menhir_lexbuf.Lexing.lex_start_p in
        let _menhir_env = _menhir_discard _menhir_env in
        let _menhir_stack = Obj.magic _menhir_stack in
        let _endpos__2_ = _endpos in
        let _startpos__2_ = _startpos in
        let (_menhir_stack, _menhir_s, _startpos__1_) = _menhir_stack in
        let _2 = () in
        let _1 = () in
        let _startpos = _startpos__1_ in
        let _endpos = _endpos__2_ in
        let _v : (IntermediateSyntax.typ) = 
# 94 "frontend/Parser.mly"
                    ( I_UINT )
# 5706 "frontend/Parser.ml"
         in
        _menhir_goto_global_typ _menhir_env _menhir_stack _endpos _menhir_s _v _startpos
    | _ ->
        assert (not _menhir_env._menhir_error);
        _menhir_env._menhir_error <- true;
        let _menhir_stack = Obj.magic _menhir_stack in
        let (_menhir_stack, _menhir_s, _) = _menhir_stack in
        _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s

and _menhir_run7 : _menhir_env -> 'ttv_tail -> Lexing.position -> _menhir_state -> Lexing.position -> 'ttv_return =
  fun _menhir_env _menhir_stack _endpos _menhir_s _startpos ->
    let _menhir_env = _menhir_discard _menhir_env in
    let _menhir_stack = Obj.magic _menhir_stack in
    let _endpos__1_ = _endpos in
    let _startpos__1_ = _startpos in
    let _1 = () in
    let _startpos = _startpos__1_ in
    let _endpos = _endpos__1_ in
    let _v : (IntermediateSyntax.typ) = 
# 93 "frontend/Parser.mly"
           ( I_INT )
# 5728 "frontend/Parser.ml"
     in
    _menhir_goto_global_typ _menhir_env _menhir_stack _endpos _menhir_s _v _startpos

and _menhir_run206 : _menhir_env -> 'ttv_tail -> _menhir_state -> Lexing.position -> 'ttv_return =
  fun _menhir_env _menhir_stack _menhir_s _startpos ->
    let _menhir_stack = (_menhir_stack, _menhir_s, _startpos) in
    let _menhir_env = _menhir_discard _menhir_env in
    let _tok = _menhir_env._menhir_token in
    match _tok with
    | TOK_BOOL ->
        let _menhir_stack = Obj.magic _menhir_stack in
        let _menhir_env = _menhir_discard _menhir_env in
        let _tok = _menhir_env._menhir_token in
        (match _tok with
        | TOK_id _v ->
            _menhir_run2 _menhir_env (Obj.magic _menhir_stack) _menhir_env._menhir_lexbuf.Lexing.lex_curr_p MenhirState211 _v _menhir_env._menhir_lexbuf.Lexing.lex_start_p
        | _ ->
            assert (not _menhir_env._menhir_error);
            _menhir_env._menhir_error <- true;
            _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) MenhirState211)
    | TOK_INT ->
        let _menhir_stack = Obj.magic _menhir_stack in
        let _endpos = _menhir_env._menhir_lexbuf.Lexing.lex_curr_p in
        let _startpos = _menhir_env._menhir_lexbuf.Lexing.lex_start_p in
        let _menhir_stack = (_menhir_stack, _endpos, _startpos) in
        let _menhir_env = _menhir_discard _menhir_env in
        let _tok = _menhir_env._menhir_token in
        (match _tok with
        | TOK_FALSE ->
            _menhir_run43 _menhir_env (Obj.magic _menhir_stack) _menhir_env._menhir_lexbuf.Lexing.lex_curr_p MenhirState207 _menhir_env._menhir_lexbuf.Lexing.lex_start_p
        | TOK_LBRACKET ->
            _menhir_run35 _menhir_env (Obj.magic _menhir_stack) MenhirState207 _menhir_env._menhir_lexbuf.Lexing.lex_start_p
        | TOK_LPAREN ->
            _menhir_run34 _menhir_env (Obj.magic _menhir_stack) MenhirState207 _menhir_env._menhir_lexbuf.Lexing.lex_start_p
        | TOK_MINUS ->
            _menhir_run33 _menhir_env (Obj.magic _menhir_stack) MenhirState207 _menhir_env._menhir_lexbuf.Lexing.lex_start_p
        | TOK_MINUS_MINUS ->
            _menhir_run32 _menhir_env (Obj.magic _menhir_stack) _menhir_env._menhir_lexbuf.Lexing.lex_curr_p MenhirState207 _menhir_env._menhir_lexbuf.Lexing.lex_start_p
        | TOK_MULTIPLY ->
            _menhir_run30 _menhir_env (Obj.magic _menhir_stack) MenhirState207 _menhir_env._menhir_lexbuf.Lexing.lex_start_p
        | TOK_NOT ->
            _menhir_run29 _menhir_env (Obj.magic _menhir_stack) MenhirState207 _menhir_env._menhir_lexbuf.Lexing.lex_start_p
        | TOK_PLUS ->
            _menhir_run28 _menhir_env (Obj.magic _menhir_stack) MenhirState207 _menhir_env._menhir_lexbuf.Lexing.lex_start_p
        | TOK_PLUS_PLUS ->
            _menhir_run27 _menhir_env (Obj.magic _menhir_stack) _menhir_env._menhir_lexbuf.Lexing.lex_curr_p MenhirState207 _menhir_env._menhir_lexbuf.Lexing.lex_start_p
        | TOK_RANDOM ->
            _menhir_run26 _menhir_env (Obj.magic _menhir_stack) _menhir_env._menhir_lexbuf.Lexing.lex_curr_p MenhirState207 _menhir_env._menhir_lexbuf.Lexing.lex_start_p
        | TOK_TRUE ->
            _menhir_run25 _menhir_env (Obj.magic _menhir_stack) _menhir_env._menhir_lexbuf.Lexing.lex_curr_p MenhirState207 _menhir_env._menhir_lexbuf.Lexing.lex_start_p
        | TOK_URANDOM ->
            _menhir_run24 _menhir_env (Obj.magic _menhir_stack) _menhir_env._menhir_lexbuf.Lexing.lex_curr_p MenhirState207 _menhir_env._menhir_lexbuf.Lexing.lex_start_p
        | TOK_const _v ->
            _menhir_run20 _menhir_env (Obj.magic _menhir_stack) _menhir_env._menhir_lexbuf.Lexing.lex_curr_p MenhirState207 _v _menhir_env._menhir_lexbuf.Lexing.lex_start_p
        | TOK_id _v ->
            _menhir_run23 _menhir_env (Obj.magic _menhir_stack) _menhir_env._menhir_lexbuf.Lexing.lex_curr_p MenhirState207 _v _menhir_env._menhir_lexbuf.Lexing.lex_start_p
        | _ ->
            assert (not _menhir_env._menhir_error);
            _menhir_env._menhir_error <- true;
            _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) MenhirState207)
    | _ ->
        assert (not _menhir_env._menhir_error);
        _menhir_env._menhir_error <- true;
        let _menhir_stack = Obj.magic _menhir_stack in
        let (_menhir_stack, _menhir_s, _) = _menhir_stack in
        _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s

and _menhir_run214 : _menhir_env -> 'ttv_tail -> _menhir_state -> Lexing.position -> 'ttv_return =
  fun _menhir_env _menhir_stack _menhir_s _startpos ->
    let _menhir_stack = (_menhir_stack, _menhir_s, _startpos) in
    let _menhir_env = _menhir_discard _menhir_env in
    let _tok = _menhir_env._menhir_token in
    match _tok with
    | TOK_id _v ->
        _menhir_run2 _menhir_env (Obj.magic _menhir_stack) _menhir_env._menhir_lexbuf.Lexing.lex_curr_p MenhirState214 _v _menhir_env._menhir_lexbuf.Lexing.lex_start_p
    | _ ->
        assert (not _menhir_env._menhir_error);
        _menhir_env._menhir_error <- true;
        _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) MenhirState214

and _menhir_run8 : _menhir_env -> 'ttv_tail -> Lexing.position -> _menhir_state -> Lexing.position -> 'ttv_return =
  fun _menhir_env _menhir_stack _endpos _menhir_s _startpos ->
    let _menhir_env = _menhir_discard _menhir_env in
    let _menhir_stack = Obj.magic _menhir_stack in
    let _endpos__1_ = _endpos in
    let _startpos__1_ = _startpos in
    let _1 = () in
    let _startpos = _startpos__1_ in
    let _endpos = _endpos__1_ in
    let _v : (IntermediateSyntax.typ) = 
# 95 "frontend/Parser.mly"
            ( I_CHAR )
# 5821 "frontend/Parser.ml"
     in
    _menhir_goto_global_typ _menhir_env _menhir_stack _endpos _menhir_s _v _startpos

and _menhir_discard : _menhir_env -> _menhir_env =
  fun _menhir_env ->
    let lexer = _menhir_env._menhir_lexer in
    let lexbuf = _menhir_env._menhir_lexbuf in
    let _tok = lexer lexbuf in
    {
      _menhir_lexer = lexer;
      _menhir_lexbuf = lexbuf;
      _menhir_token = _tok;
      _menhir_error = false;
    }

and file : (Lexing.lexbuf -> token) -> Lexing.lexbuf -> (
# 75 "frontend/Parser.mly"
       (IntermediateSyntax.decl list IntermediateSyntax.annotated)
# 5840 "frontend/Parser.ml"
) =
  fun lexer lexbuf ->
    let _menhir_env = let _tok = Obj.magic () in
    {
      _menhir_lexer = lexer;
      _menhir_lexbuf = lexbuf;
      _menhir_token = _tok;
      _menhir_error = false;
    } in
    Obj.magic (let _menhir_stack = ((), _menhir_env._menhir_lexbuf.Lexing.lex_curr_p) in
    let _menhir_env = _menhir_discard _menhir_env in
    let _tok = _menhir_env._menhir_token in
    match _tok with
    | TOK_CHAR ->
        _menhir_run8 _menhir_env (Obj.magic _menhir_stack) _menhir_env._menhir_lexbuf.Lexing.lex_curr_p MenhirState0 _menhir_env._menhir_lexbuf.Lexing.lex_start_p
    | TOK_CPP_DEFINE ->
        _menhir_run214 _menhir_env (Obj.magic _menhir_stack) MenhirState0 _menhir_env._menhir_lexbuf.Lexing.lex_start_p
    | TOK_FEAT ->
        _menhir_run206 _menhir_env (Obj.magic _menhir_stack) MenhirState0 _menhir_env._menhir_lexbuf.Lexing.lex_start_p
    | TOK_INT ->
        _menhir_run7 _menhir_env (Obj.magic _menhir_stack) _menhir_env._menhir_lexbuf.Lexing.lex_curr_p MenhirState0 _menhir_env._menhir_lexbuf.Lexing.lex_start_p
    | TOK_UINT ->
        _menhir_run5 _menhir_env (Obj.magic _menhir_stack) MenhirState0 _menhir_env._menhir_lexbuf.Lexing.lex_start_p
    | TOK_VOID ->
        _menhir_run1 _menhir_env (Obj.magic _menhir_stack) MenhirState0 _menhir_env._menhir_lexbuf.Lexing.lex_start_p
    | TOK_EOF ->
        _menhir_reduce72 _menhir_env (Obj.magic _menhir_stack) MenhirState0
    | _ ->
        assert (not _menhir_env._menhir_error);
        _menhir_env._menhir_error <- true;
        _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) MenhirState0)

# 238 "frontend/Parser.mly"
  

# 5876 "frontend/Parser.ml"

# 219 "/usr/share/menhir/standard.mly"
  


# 5882 "frontend/Parser.ml"
