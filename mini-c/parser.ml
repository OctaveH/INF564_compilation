
module MenhirBasics = struct
  
  exception Error
  
  type token = 
    | WHILE
    | VERTICALBARVERTICALBAR
    | STRUCT
    | STAR
    | SLASH
    | SIZEOF
    | SEMICOLON
    | RPAR
    | RETURN
    | RBRACE
    | PLUS
    | MINUS
    | LPAR
    | LBRACE
    | INTEGER of (
# 14 "parser.mly"
       (int32)
# 25 "parser.ml"
  )
    | INT
    | IF
    | IDENT of (
# 13 "parser.mly"
       (string)
# 32 "parser.ml"
  )
    | EQOP of (
# 32 "parser.mly"
       (Ptree.binop)
# 37 "parser.ml"
  )
    | EQ
    | EOF
    | ELSE
    | COMP of (
# 33 "parser.mly"
       (Ptree.binop)
# 45 "parser.ml"
  )
    | COMMA
    | BANG
    | ARROW
    | AMPERSANDAMPERSAND
  
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
  | MenhirState114
  | MenhirState110
  | MenhirState104
  | MenhirState98
  | MenhirState95
  | MenhirState93
  | MenhirState89
  | MenhirState87
  | MenhirState79
  | MenhirState77
  | MenhirState75
  | MenhirState73
  | MenhirState71
  | MenhirState69
  | MenhirState67
  | MenhirState65
  | MenhirState63
  | MenhirState61
  | MenhirState55
  | MenhirState53
  | MenhirState51
  | MenhirState49
  | MenhirState48
  | MenhirState45
  | MenhirState42
  | MenhirState40
  | MenhirState39
  | MenhirState38
  | MenhirState33
  | MenhirState32
  | MenhirState27
  | MenhirState25
  | MenhirState20
  | MenhirState16
  | MenhirState12
  | MenhirState9
  | MenhirState8
  | MenhirState7
  | MenhirState6
  | MenhirState4
  | MenhirState1
  | MenhirState0

# 4 "parser.mly"
  

  open Parsing
  open Ptree

  (* Construction d'expressions et d'instructions localisées *)


# 119 "parser.ml"

let rec _menhir_goto_list_stmt_ : _menhir_env -> 'ttv_tail -> _menhir_state -> 'tv_list_stmt_ -> 'ttv_return =
  fun _menhir_env _menhir_stack _menhir_s _v ->
    let _menhir_stack = (_menhir_stack, _menhir_s, _v) in
    match _menhir_s with
    | MenhirState104 ->
        let (_menhir_env : _menhir_env) = _menhir_env in
        let (_menhir_stack : ('freshtv441 * Lexing.position * _menhir_state * 'tv_stmt) * _menhir_state * 'tv_list_stmt_) = Obj.magic _menhir_stack in
        ((let (_menhir_env : _menhir_env) = _menhir_env in
        let (_menhir_stack : ('freshtv439 * Lexing.position * _menhir_state * 'tv_stmt) * _menhir_state * 'tv_list_stmt_) = Obj.magic _menhir_stack in
        ((let ((_menhir_stack, _endpos_x_, _menhir_s, (x : 'tv_stmt)), _, (xs : 'tv_list_stmt_)) = _menhir_stack in
        let _v : 'tv_list_stmt_ = 
# 213 "/home/jc/.opam/4.07.1/lib/menhir/standard.mly"
    ( x :: xs )
# 134 "parser.ml"
         in
        _menhir_goto_list_stmt_ _menhir_env _menhir_stack _menhir_s _v) : 'freshtv440)) : 'freshtv442)
    | MenhirState40 ->
        let (_menhir_env : _menhir_env) = _menhir_env in
        let (_menhir_stack : (('freshtv465 * _menhir_state * Lexing.position) * _menhir_state * 'tv_list_decl_var_) * _menhir_state * 'tv_list_stmt_) = Obj.magic _menhir_stack in
        ((assert (not _menhir_env._menhir_error);
        let _tok = _menhir_env._menhir_token in
        match _tok with
        | RBRACE ->
            let (_menhir_env : _menhir_env) = _menhir_env in
            let (_menhir_stack : (('freshtv461 * _menhir_state * Lexing.position) * _menhir_state * 'tv_list_decl_var_) * _menhir_state * 'tv_list_stmt_) = Obj.magic _menhir_stack in
            let (_endpos : Lexing.position) = _menhir_env._menhir_lexbuf.Lexing.lex_curr_p in
            ((let _menhir_env = _menhir_discard _menhir_env in
            let (_menhir_env : _menhir_env) = _menhir_env in
            let (_menhir_stack : (('freshtv459 * _menhir_state * Lexing.position) * _menhir_state * 'tv_list_decl_var_) * _menhir_state * 'tv_list_stmt_) = Obj.magic _menhir_stack in
            let (_endpos__4_ : Lexing.position) = _endpos in
            ((let (((_menhir_stack, _menhir_s, _startpos__1_), _, (vl : 'tv_list_decl_var_)), _, (sl : 'tv_list_stmt_)) = _menhir_stack in
            let _4 = () in
            let _1 = () in
            let _startpos = _startpos__1_ in
            let _endpos = _endpos__4_ in
            let _v : 'tv_block = 
# 170 "parser.mly"
                                                    ( List.flatten vl, sl )
# 159 "parser.ml"
             in
            let (_menhir_env : _menhir_env) = _menhir_env in
            let (_menhir_stack : 'freshtv457) = _menhir_stack in
            let (_endpos : Lexing.position) = _endpos in
            let (_menhir_s : _menhir_state) = _menhir_s in
            let (_v : 'tv_block) = _v in
            let (_startpos : Lexing.position) = _startpos in
            ((match _menhir_s with
            | MenhirState40 | MenhirState104 | MenhirState87 | MenhirState95 | MenhirState98 ->
                let (_menhir_env : _menhir_env) = _menhir_env in
                let (_menhir_stack : 'freshtv445) = Obj.magic _menhir_stack in
                let (_endpos : Lexing.position) = _endpos in
                let (_menhir_s : _menhir_state) = _menhir_s in
                let (_v : 'tv_block) = _v in
                let (_startpos : Lexing.position) = _startpos in
                ((let (_menhir_env : _menhir_env) = _menhir_env in
                let (_menhir_stack : 'freshtv443) = Obj.magic _menhir_stack in
                let (_endpos__1_ : Lexing.position) = _endpos in
                let (_menhir_s : _menhir_state) = _menhir_s in
                let ((_1 : 'tv_block) : 'tv_block) = _v in
                let (_startpos__1_ : Lexing.position) = _startpos in
                ((let _startpos = _startpos__1_ in
                let _endpos = _endpos__1_ in
                let _v : 'tv_stmt_node = 
# 164 "parser.mly"
   ( Sblock _1 )
# 186 "parser.ml"
                 in
                _menhir_goto_stmt_node _menhir_env _menhir_stack _endpos _menhir_s _v _startpos) : 'freshtv444)) : 'freshtv446)
            | MenhirState38 ->
                let (_menhir_env : _menhir_env) = _menhir_env in
                let (_menhir_stack : ((('freshtv455 * _menhir_state * 'tv_formal) * Lexing.position) * _menhir_state * 'tv_formals) * Lexing.position) = Obj.magic _menhir_stack in
                let (_endpos : Lexing.position) = _endpos in
                let (_menhir_s : _menhir_state) = _menhir_s in
                let (_v : 'tv_block) = _v in
                let (_startpos : Lexing.position) = _startpos in
                ((let (_menhir_env : _menhir_env) = _menhir_env in
                let (_menhir_stack : ((('freshtv453 * _menhir_state * 'tv_formal) * Lexing.position) * _menhir_state * 'tv_formals) * Lexing.position) = Obj.magic _menhir_stack in
                let (_endpos_body_ : Lexing.position) = _endpos in
                let (_ : _menhir_state) = _menhir_s in
                let ((body : 'tv_block) : 'tv_block) = _v in
                let (_startpos_body_ : Lexing.position) = _startpos in
                ((let ((((_menhir_stack, _menhir_s, (f : 'tv_formal)), _startpos__2_), _, (fl : 'tv_formals)), _endpos__4_) = _menhir_stack in
                let _4 = () in
                let _2 = () in
                let _v : 'tv_decl_fun = 
# 84 "parser.mly"
    ( let ty, id = f in
      { fun_typ = ty;
	fun_name = id;
	fun_formals = fl;
	fun_body = body; } )
# 212 "parser.ml"
                 in
                let (_menhir_env : _menhir_env) = _menhir_env in
                let (_menhir_stack : 'freshtv451) = _menhir_stack in
                let (_menhir_s : _menhir_state) = _menhir_s in
                let (_v : 'tv_decl_fun) = _v in
                ((let (_menhir_env : _menhir_env) = _menhir_env in
                let (_menhir_stack : 'freshtv449) = Obj.magic _menhir_stack in
                let (_menhir_s : _menhir_state) = _menhir_s in
                let (_v : 'tv_decl_fun) = _v in
                ((let (_menhir_env : _menhir_env) = _menhir_env in
                let (_menhir_stack : 'freshtv447) = Obj.magic _menhir_stack in
                let (_menhir_s : _menhir_state) = _menhir_s in
                let ((f : 'tv_decl_fun) : 'tv_decl_fun) = _v in
                ((let _v : 'tv_decl = 
# 68 "parser.mly"
    ( Dfun f )
# 229 "parser.ml"
                 in
                _menhir_goto_decl _menhir_env _menhir_stack _menhir_s _v) : 'freshtv448)) : 'freshtv450)) : 'freshtv452)) : 'freshtv454)) : 'freshtv456)
            | _ ->
                _menhir_fail ()) : 'freshtv458)) : 'freshtv460)) : 'freshtv462)
        | _ ->
            assert (not _menhir_env._menhir_error);
            _menhir_env._menhir_error <- true;
            let (_menhir_env : _menhir_env) = _menhir_env in
            let (_menhir_stack : (('freshtv463 * _menhir_state * Lexing.position) * _menhir_state * 'tv_list_decl_var_) * _menhir_state * 'tv_list_stmt_) = Obj.magic _menhir_stack in
            ((let (_menhir_stack, _menhir_s, _) = _menhir_stack in
            _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s) : 'freshtv464)) : 'freshtv466)
    | _ ->
        _menhir_fail ()

and _menhir_reduce33 : _menhir_env -> 'ttv_tail -> _menhir_state -> 'ttv_return =
  fun _menhir_env _menhir_stack _menhir_s ->
    let _v : 'tv_list_stmt_ = 
# 211 "/home/jc/.opam/4.07.1/lib/menhir/standard.mly"
    ( [] )
# 249 "parser.ml"
     in
    _menhir_goto_list_stmt_ _menhir_env _menhir_stack _menhir_s _v

and _menhir_goto_decl : _menhir_env -> 'ttv_tail -> _menhir_state -> 'tv_decl -> 'ttv_return =
  fun _menhir_env _menhir_stack _menhir_s _v ->
    let _menhir_stack = (_menhir_stack, _menhir_s, _v) in
    let (_menhir_env : _menhir_env) = _menhir_env in
    let (_menhir_stack : 'freshtv437 * _menhir_state * 'tv_decl) = Obj.magic _menhir_stack in
    ((assert (not _menhir_env._menhir_error);
    let _tok = _menhir_env._menhir_token in
    match _tok with
    | INT ->
        _menhir_run27 _menhir_env (Obj.magic _menhir_stack) MenhirState114
    | STRUCT ->
        _menhir_run1 _menhir_env (Obj.magic _menhir_stack) MenhirState114
    | EOF ->
        _menhir_reduce29 _menhir_env (Obj.magic _menhir_stack) MenhirState114
    | _ ->
        assert (not _menhir_env._menhir_error);
        _menhir_env._menhir_error <- true;
        _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) MenhirState114) : 'freshtv438)

and _menhir_goto_stmt_node : _menhir_env -> 'ttv_tail -> Lexing.position -> _menhir_state -> 'tv_stmt_node -> Lexing.position -> 'ttv_return =
  fun _menhir_env _menhir_stack _endpos _menhir_s _v _startpos ->
    let (_menhir_env : _menhir_env) = _menhir_env in
    let (_menhir_stack : 'freshtv435) = Obj.magic _menhir_stack in
    let (_endpos : Lexing.position) = _endpos in
    let (_menhir_s : _menhir_state) = _menhir_s in
    let (_v : 'tv_stmt_node) = _v in
    let (_startpos : Lexing.position) = _startpos in
    ((let (_menhir_env : _menhir_env) = _menhir_env in
    let (_menhir_stack : 'freshtv433) = Obj.magic _menhir_stack in
    let (_endpos_s_ : Lexing.position) = _endpos in
    let (_menhir_s : _menhir_state) = _menhir_s in
    let ((s : 'tv_stmt_node) : 'tv_stmt_node) = _v in
    let (_startpos_s_ : Lexing.position) = _startpos in
    ((let _endpos = _endpos_s_ in
    let _v : 'tv_stmt = let _endpos = _endpos_s_ in
    let _startpos = _startpos_s_ in
    
# 149 "parser.mly"
   ( { stmt_node = s; stmt_loc = _startpos, _endpos } )
# 292 "parser.ml"
     in
    let (_menhir_env : _menhir_env) = _menhir_env in
    let (_menhir_stack : 'freshtv431) = _menhir_stack in
    let (_endpos : Lexing.position) = _endpos in
    let (_menhir_s : _menhir_state) = _menhir_s in
    let (_v : 'tv_stmt) = _v in
    ((let _menhir_stack = (_menhir_stack, _endpos, _menhir_s, _v) in
    match _menhir_s with
    | MenhirState95 ->
        let (_menhir_env : _menhir_env) = _menhir_env in
        let (_menhir_stack : (((('freshtv419 * _menhir_state * Lexing.position) * Lexing.position) * Lexing.position * _menhir_state * 'tv_expr * Lexing.position) * Lexing.position) * Lexing.position * _menhir_state * 'tv_stmt) = Obj.magic _menhir_stack in
        ((assert (not _menhir_env._menhir_error);
        let _tok = _menhir_env._menhir_token in
        match _tok with
        | ELSE ->
            let (_menhir_env : _menhir_env) = _menhir_env in
            let (_menhir_stack : (((('freshtv413 * _menhir_state * Lexing.position) * Lexing.position) * Lexing.position * _menhir_state * 'tv_expr * Lexing.position) * Lexing.position) * Lexing.position * _menhir_state * 'tv_stmt) = Obj.magic _menhir_stack in
            ((let _menhir_env = _menhir_discard _menhir_env in
            let _tok = _menhir_env._menhir_token in
            match _tok with
            | BANG ->
                _menhir_run51 _menhir_env (Obj.magic _menhir_stack) MenhirState98 _menhir_env._menhir_lexbuf.Lexing.lex_start_p
            | IDENT _v ->
                _menhir_run2 _menhir_env (Obj.magic _menhir_stack) _menhir_env._menhir_lexbuf.Lexing.lex_curr_p MenhirState98 _v _menhir_env._menhir_lexbuf.Lexing.lex_start_p
            | IF ->
                _menhir_run92 _menhir_env (Obj.magic _menhir_stack) MenhirState98 _menhir_env._menhir_lexbuf.Lexing.lex_start_p
            | INTEGER _v ->
                _menhir_run50 _menhir_env (Obj.magic _menhir_stack) _menhir_env._menhir_lexbuf.Lexing.lex_curr_p MenhirState98 _v _menhir_env._menhir_lexbuf.Lexing.lex_start_p
            | LBRACE ->
                _menhir_run39 _menhir_env (Obj.magic _menhir_stack) MenhirState98 _menhir_env._menhir_lexbuf.Lexing.lex_start_p
            | LPAR ->
                _menhir_run49 _menhir_env (Obj.magic _menhir_stack) MenhirState98 _menhir_env._menhir_lexbuf.Lexing.lex_start_p
            | MINUS ->
                _menhir_run48 _menhir_env (Obj.magic _menhir_stack) MenhirState98 _menhir_env._menhir_lexbuf.Lexing.lex_start_p
            | RETURN ->
                _menhir_run89 _menhir_env (Obj.magic _menhir_stack) MenhirState98 _menhir_env._menhir_lexbuf.Lexing.lex_start_p
            | SEMICOLON ->
                _menhir_run88 _menhir_env (Obj.magic _menhir_stack) _menhir_env._menhir_lexbuf.Lexing.lex_curr_p MenhirState98 _menhir_env._menhir_lexbuf.Lexing.lex_start_p
            | SIZEOF ->
                _menhir_run43 _menhir_env (Obj.magic _menhir_stack) MenhirState98 _menhir_env._menhir_lexbuf.Lexing.lex_start_p
            | WHILE ->
                _menhir_run41 _menhir_env (Obj.magic _menhir_stack) MenhirState98 _menhir_env._menhir_lexbuf.Lexing.lex_start_p
            | _ ->
                assert (not _menhir_env._menhir_error);
                _menhir_env._menhir_error <- true;
                _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) MenhirState98) : 'freshtv414)
        | BANG | IDENT _ | IF | INTEGER _ | LBRACE | LPAR | MINUS | RBRACE | RETURN | SEMICOLON | SIZEOF | WHILE ->
            let (_menhir_env : _menhir_env) = _menhir_env in
            let (_menhir_stack : (((('freshtv415 * _menhir_state * Lexing.position) * Lexing.position) * Lexing.position * _menhir_state * 'tv_expr * Lexing.position) * Lexing.position) * Lexing.position * _menhir_state * 'tv_stmt) = Obj.magic _menhir_stack in
            ((let (((((_menhir_stack, _menhir_s, _startpos__1_), _startpos__2_), _endpos__3_, _, (_3 : 'tv_expr), _startpos__3_), _endpos__4_), _endpos__5_, _, (_5 : 'tv_stmt)) = _menhir_stack in
            let _4 = () in
            let _2 = () in
            let _1 = () in
            let _startpos = _startpos__1_ in
            let _endpos = _endpos__5_ in
            let _v : 'tv_stmt_node = let _endpos = _endpos__5_ in
            let _startpos = _startpos__1_ in
            
# 158 "parser.mly"
   ( Sif (_3, _5, { stmt_node = Sskip; stmt_loc = _startpos, _endpos }) )
# 353 "parser.ml"
             in
            _menhir_goto_stmt_node _menhir_env _menhir_stack _endpos _menhir_s _v _startpos) : 'freshtv416)
        | _ ->
            assert (not _menhir_env._menhir_error);
            _menhir_env._menhir_error <- true;
            let (_menhir_env : _menhir_env) = _menhir_env in
            let (_menhir_stack : (((('freshtv417 * _menhir_state * Lexing.position) * Lexing.position) * Lexing.position * _menhir_state * 'tv_expr * Lexing.position) * Lexing.position) * Lexing.position * _menhir_state * 'tv_stmt) = Obj.magic _menhir_stack in
            ((let (_menhir_stack, _, _menhir_s, _) = _menhir_stack in
            _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s) : 'freshtv418)) : 'freshtv420)
    | MenhirState98 ->
        let (_menhir_env : _menhir_env) = _menhir_env in
        let (_menhir_stack : (((((('freshtv423 * _menhir_state * Lexing.position) * Lexing.position) * Lexing.position * _menhir_state * 'tv_expr * Lexing.position) * Lexing.position) * Lexing.position * _menhir_state * 'tv_stmt)) * Lexing.position * _menhir_state * 'tv_stmt) = Obj.magic _menhir_stack in
        ((let (_menhir_env : _menhir_env) = _menhir_env in
        let (_menhir_stack : (((((('freshtv421 * _menhir_state * Lexing.position) * Lexing.position) * Lexing.position * _menhir_state * 'tv_expr * Lexing.position) * Lexing.position) * Lexing.position * _menhir_state * 'tv_stmt)) * Lexing.position * _menhir_state * 'tv_stmt) = Obj.magic _menhir_stack in
        ((let ((((((_menhir_stack, _menhir_s, _startpos__1_), _startpos__2_), _endpos__3_, _, (_3 : 'tv_expr), _startpos__3_), _endpos__4_), _endpos__5_, _, (_5 : 'tv_stmt)), _endpos__7_, _, (_7 : 'tv_stmt)) = _menhir_stack in
        let _6 = () in
        let _4 = () in
        let _2 = () in
        let _1 = () in
        let _startpos = _startpos__1_ in
        let _endpos = _endpos__7_ in
        let _v : 'tv_stmt_node = 
# 160 "parser.mly"
   ( Sif (_3, _5, _7) )
# 378 "parser.ml"
         in
        _menhir_goto_stmt_node _menhir_env _menhir_stack _endpos _menhir_s _v _startpos) : 'freshtv422)) : 'freshtv424)
    | MenhirState87 ->
        let (_menhir_env : _menhir_env) = _menhir_env in
        let (_menhir_stack : (((('freshtv427 * _menhir_state * Lexing.position) * Lexing.position) * Lexing.position * _menhir_state * 'tv_expr * Lexing.position) * Lexing.position) * Lexing.position * _menhir_state * 'tv_stmt) = Obj.magic _menhir_stack in
        ((let (_menhir_env : _menhir_env) = _menhir_env in
        let (_menhir_stack : (((('freshtv425 * _menhir_state * Lexing.position) * Lexing.position) * Lexing.position * _menhir_state * 'tv_expr * Lexing.position) * Lexing.position) * Lexing.position * _menhir_state * 'tv_stmt) = Obj.magic _menhir_stack in
        ((let (((((_menhir_stack, _menhir_s, _startpos__1_), _startpos__2_), _endpos__3_, _, (_3 : 'tv_expr), _startpos__3_), _endpos__4_), _endpos__5_, _, (_5 : 'tv_stmt)) = _menhir_stack in
        let _4 = () in
        let _2 = () in
        let _1 = () in
        let _startpos = _startpos__1_ in
        let _endpos = _endpos__5_ in
        let _v : 'tv_stmt_node = 
# 162 "parser.mly"
   ( Swhile (_3, _5) )
# 395 "parser.ml"
         in
        _menhir_goto_stmt_node _menhir_env _menhir_stack _endpos _menhir_s _v _startpos) : 'freshtv426)) : 'freshtv428)
    | MenhirState104 | MenhirState40 ->
        let (_menhir_env : _menhir_env) = _menhir_env in
        let (_menhir_stack : 'freshtv429 * Lexing.position * _menhir_state * 'tv_stmt) = Obj.magic _menhir_stack in
        ((assert (not _menhir_env._menhir_error);
        let _tok = _menhir_env._menhir_token in
        match _tok with
        | BANG ->
            _menhir_run51 _menhir_env (Obj.magic _menhir_stack) MenhirState104 _menhir_env._menhir_lexbuf.Lexing.lex_start_p
        | IDENT _v ->
            _menhir_run2 _menhir_env (Obj.magic _menhir_stack) _menhir_env._menhir_lexbuf.Lexing.lex_curr_p MenhirState104 _v _menhir_env._menhir_lexbuf.Lexing.lex_start_p
        | IF ->
            _menhir_run92 _menhir_env (Obj.magic _menhir_stack) MenhirState104 _menhir_env._menhir_lexbuf.Lexing.lex_start_p
        | INTEGER _v ->
            _menhir_run50 _menhir_env (Obj.magic _menhir_stack) _menhir_env._menhir_lexbuf.Lexing.lex_curr_p MenhirState104 _v _menhir_env._menhir_lexbuf.Lexing.lex_start_p
        | LBRACE ->
            _menhir_run39 _menhir_env (Obj.magic _menhir_stack) MenhirState104 _menhir_env._menhir_lexbuf.Lexing.lex_start_p
        | LPAR ->
            _menhir_run49 _menhir_env (Obj.magic _menhir_stack) MenhirState104 _menhir_env._menhir_lexbuf.Lexing.lex_start_p
        | MINUS ->
            _menhir_run48 _menhir_env (Obj.magic _menhir_stack) MenhirState104 _menhir_env._menhir_lexbuf.Lexing.lex_start_p
        | RETURN ->
            _menhir_run89 _menhir_env (Obj.magic _menhir_stack) MenhirState104 _menhir_env._menhir_lexbuf.Lexing.lex_start_p
        | SEMICOLON ->
            _menhir_run88 _menhir_env (Obj.magic _menhir_stack) _menhir_env._menhir_lexbuf.Lexing.lex_curr_p MenhirState104 _menhir_env._menhir_lexbuf.Lexing.lex_start_p
        | SIZEOF ->
            _menhir_run43 _menhir_env (Obj.magic _menhir_stack) MenhirState104 _menhir_env._menhir_lexbuf.Lexing.lex_start_p
        | WHILE ->
            _menhir_run41 _menhir_env (Obj.magic _menhir_stack) MenhirState104 _menhir_env._menhir_lexbuf.Lexing.lex_start_p
        | RBRACE ->
            _menhir_reduce33 _menhir_env (Obj.magic _menhir_stack) MenhirState104
        | _ ->
            assert (not _menhir_env._menhir_error);
            _menhir_env._menhir_error <- true;
            _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) MenhirState104) : 'freshtv430)
    | _ ->
        _menhir_fail ()) : 'freshtv432)) : 'freshtv434)) : 'freshtv436)

and _menhir_run41 : _menhir_env -> 'ttv_tail -> _menhir_state -> Lexing.position -> 'ttv_return =
  fun _menhir_env _menhir_stack _menhir_s _startpos ->
    let _menhir_stack = (_menhir_stack, _menhir_s, _startpos) in
    let _menhir_env = _menhir_discard _menhir_env in
    let _tok = _menhir_env._menhir_token in
    match _tok with
    | LPAR ->
        let (_menhir_env : _menhir_env) = _menhir_env in
        let (_menhir_stack : 'freshtv409 * _menhir_state * Lexing.position) = Obj.magic _menhir_stack in
        let (_startpos : Lexing.position) = _menhir_env._menhir_lexbuf.Lexing.lex_start_p in
        ((let _menhir_stack = (_menhir_stack, _startpos) in
        let _menhir_env = _menhir_discard _menhir_env in
        let _tok = _menhir_env._menhir_token in
        match _tok with
        | BANG ->
            _menhir_run51 _menhir_env (Obj.magic _menhir_stack) MenhirState42 _menhir_env._menhir_lexbuf.Lexing.lex_start_p
        | IDENT _v ->
            _menhir_run2 _menhir_env (Obj.magic _menhir_stack) _menhir_env._menhir_lexbuf.Lexing.lex_curr_p MenhirState42 _v _menhir_env._menhir_lexbuf.Lexing.lex_start_p
        | INTEGER _v ->
            _menhir_run50 _menhir_env (Obj.magic _menhir_stack) _menhir_env._menhir_lexbuf.Lexing.lex_curr_p MenhirState42 _v _menhir_env._menhir_lexbuf.Lexing.lex_start_p
        | LPAR ->
            _menhir_run49 _menhir_env (Obj.magic _menhir_stack) MenhirState42 _menhir_env._menhir_lexbuf.Lexing.lex_start_p
        | MINUS ->
            _menhir_run48 _menhir_env (Obj.magic _menhir_stack) MenhirState42 _menhir_env._menhir_lexbuf.Lexing.lex_start_p
        | SIZEOF ->
            _menhir_run43 _menhir_env (Obj.magic _menhir_stack) MenhirState42 _menhir_env._menhir_lexbuf.Lexing.lex_start_p
        | _ ->
            assert (not _menhir_env._menhir_error);
            _menhir_env._menhir_error <- true;
            _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) MenhirState42) : 'freshtv410)
    | _ ->
        assert (not _menhir_env._menhir_error);
        _menhir_env._menhir_error <- true;
        let (_menhir_env : _menhir_env) = _menhir_env in
        let (_menhir_stack : 'freshtv411 * _menhir_state * Lexing.position) = Obj.magic _menhir_stack in
        ((let (_menhir_stack, _menhir_s, _) = _menhir_stack in
        _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s) : 'freshtv412)

and _menhir_run88 : _menhir_env -> 'ttv_tail -> Lexing.position -> _menhir_state -> Lexing.position -> 'ttv_return =
  fun _menhir_env _menhir_stack _endpos _menhir_s _startpos ->
    let _menhir_env = _menhir_discard _menhir_env in
    let (_menhir_env : _menhir_env) = _menhir_env in
    let (_menhir_stack : 'freshtv407) = Obj.magic _menhir_stack in
    let (_endpos__1_ : Lexing.position) = _endpos in
    let (_menhir_s : _menhir_state) = _menhir_s in
    let (_startpos__1_ : Lexing.position) = _startpos in
    ((let _1 = () in
    let _startpos = _startpos__1_ in
    let _endpos = _endpos__1_ in
    let _v : 'tv_stmt_node = 
# 154 "parser.mly"
   ( Sskip )
# 487 "parser.ml"
     in
    _menhir_goto_stmt_node _menhir_env _menhir_stack _endpos _menhir_s _v _startpos) : 'freshtv408)

and _menhir_run89 : _menhir_env -> 'ttv_tail -> _menhir_state -> Lexing.position -> 'ttv_return =
  fun _menhir_env _menhir_stack _menhir_s _startpos ->
    let _menhir_stack = (_menhir_stack, _menhir_s, _startpos) in
    let _menhir_env = _menhir_discard _menhir_env in
    let _tok = _menhir_env._menhir_token in
    match _tok with
    | BANG ->
        _menhir_run51 _menhir_env (Obj.magic _menhir_stack) MenhirState89 _menhir_env._menhir_lexbuf.Lexing.lex_start_p
    | IDENT _v ->
        _menhir_run2 _menhir_env (Obj.magic _menhir_stack) _menhir_env._menhir_lexbuf.Lexing.lex_curr_p MenhirState89 _v _menhir_env._menhir_lexbuf.Lexing.lex_start_p
    | INTEGER _v ->
        _menhir_run50 _menhir_env (Obj.magic _menhir_stack) _menhir_env._menhir_lexbuf.Lexing.lex_curr_p MenhirState89 _v _menhir_env._menhir_lexbuf.Lexing.lex_start_p
    | LPAR ->
        _menhir_run49 _menhir_env (Obj.magic _menhir_stack) MenhirState89 _menhir_env._menhir_lexbuf.Lexing.lex_start_p
    | MINUS ->
        _menhir_run48 _menhir_env (Obj.magic _menhir_stack) MenhirState89 _menhir_env._menhir_lexbuf.Lexing.lex_start_p
    | SIZEOF ->
        _menhir_run43 _menhir_env (Obj.magic _menhir_stack) MenhirState89 _menhir_env._menhir_lexbuf.Lexing.lex_start_p
    | _ ->
        assert (not _menhir_env._menhir_error);
        _menhir_env._menhir_error <- true;
        _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) MenhirState89

and _menhir_run39 : _menhir_env -> 'ttv_tail -> _menhir_state -> Lexing.position -> 'ttv_return =
  fun _menhir_env _menhir_stack _menhir_s _startpos ->
    let _menhir_stack = (_menhir_stack, _menhir_s, _startpos) in
    let _menhir_env = _menhir_discard _menhir_env in
    let _tok = _menhir_env._menhir_token in
    match _tok with
    | INT ->
        _menhir_run16 _menhir_env (Obj.magic _menhir_stack) MenhirState39
    | STRUCT ->
        _menhir_run7 _menhir_env (Obj.magic _menhir_stack) MenhirState39
    | BANG | IDENT _ | IF | INTEGER _ | LBRACE | LPAR | MINUS | RBRACE | RETURN | SEMICOLON | SIZEOF | WHILE ->
        _menhir_reduce31 _menhir_env (Obj.magic _menhir_stack) MenhirState39
    | _ ->
        assert (not _menhir_env._menhir_error);
        _menhir_env._menhir_error <- true;
        _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) MenhirState39

and _menhir_run92 : _menhir_env -> 'ttv_tail -> _menhir_state -> Lexing.position -> 'ttv_return =
  fun _menhir_env _menhir_stack _menhir_s _startpos ->
    let _menhir_stack = (_menhir_stack, _menhir_s, _startpos) in
    let _menhir_env = _menhir_discard _menhir_env in
    let _tok = _menhir_env._menhir_token in
    match _tok with
    | LPAR ->
        let (_menhir_env : _menhir_env) = _menhir_env in
        let (_menhir_stack : 'freshtv403 * _menhir_state * Lexing.position) = Obj.magic _menhir_stack in
        let (_startpos : Lexing.position) = _menhir_env._menhir_lexbuf.Lexing.lex_start_p in
        ((let _menhir_stack = (_menhir_stack, _startpos) in
        let _menhir_env = _menhir_discard _menhir_env in
        let _tok = _menhir_env._menhir_token in
        match _tok with
        | BANG ->
            _menhir_run51 _menhir_env (Obj.magic _menhir_stack) MenhirState93 _menhir_env._menhir_lexbuf.Lexing.lex_start_p
        | IDENT _v ->
            _menhir_run2 _menhir_env (Obj.magic _menhir_stack) _menhir_env._menhir_lexbuf.Lexing.lex_curr_p MenhirState93 _v _menhir_env._menhir_lexbuf.Lexing.lex_start_p
        | INTEGER _v ->
            _menhir_run50 _menhir_env (Obj.magic _menhir_stack) _menhir_env._menhir_lexbuf.Lexing.lex_curr_p MenhirState93 _v _menhir_env._menhir_lexbuf.Lexing.lex_start_p
        | LPAR ->
            _menhir_run49 _menhir_env (Obj.magic _menhir_stack) MenhirState93 _menhir_env._menhir_lexbuf.Lexing.lex_start_p
        | MINUS ->
            _menhir_run48 _menhir_env (Obj.magic _menhir_stack) MenhirState93 _menhir_env._menhir_lexbuf.Lexing.lex_start_p
        | SIZEOF ->
            _menhir_run43 _menhir_env (Obj.magic _menhir_stack) MenhirState93 _menhir_env._menhir_lexbuf.Lexing.lex_start_p
        | _ ->
            assert (not _menhir_env._menhir_error);
            _menhir_env._menhir_error <- true;
            _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) MenhirState93) : 'freshtv404)
    | _ ->
        assert (not _menhir_env._menhir_error);
        _menhir_env._menhir_error <- true;
        let (_menhir_env : _menhir_env) = _menhir_env in
        let (_menhir_stack : 'freshtv405 * _menhir_state * Lexing.position) = Obj.magic _menhir_stack in
        ((let (_menhir_stack, _menhir_s, _) = _menhir_stack in
        _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s) : 'freshtv406)

and _menhir_goto_separated_nonempty_list_COMMA_expr_ : _menhir_env -> 'ttv_tail -> _menhir_state -> 'tv_separated_nonempty_list_COMMA_expr_ -> 'ttv_return =
  fun _menhir_env _menhir_stack _menhir_s _v ->
    match _menhir_s with
    | MenhirState55 ->
        let (_menhir_env : _menhir_env) = _menhir_env in
        let (_menhir_stack : 'freshtv397) = Obj.magic _menhir_stack in
        let (_menhir_s : _menhir_state) = _menhir_s in
        let (_v : 'tv_separated_nonempty_list_COMMA_expr_) = _v in
        ((let (_menhir_env : _menhir_env) = _menhir_env in
        let (_menhir_stack : 'freshtv395) = Obj.magic _menhir_stack in
        let (_menhir_s : _menhir_state) = _menhir_s in
        let ((x : 'tv_separated_nonempty_list_COMMA_expr_) : 'tv_separated_nonempty_list_COMMA_expr_) = _v in
        ((let _v : 'tv_loption_separated_nonempty_list_COMMA_expr__ = 
# 144 "/home/jc/.opam/4.07.1/lib/menhir/standard.mly"
    ( x )
# 584 "parser.ml"
         in
        _menhir_goto_loption_separated_nonempty_list_COMMA_expr__ _menhir_env _menhir_stack _menhir_s _v) : 'freshtv396)) : 'freshtv398)
    | MenhirState79 ->
        let (_menhir_env : _menhir_env) = _menhir_env in
        let (_menhir_stack : ('freshtv401 * Lexing.position * _menhir_state * 'tv_expr * Lexing.position)) = Obj.magic _menhir_stack in
        let (_menhir_s : _menhir_state) = _menhir_s in
        let (_v : 'tv_separated_nonempty_list_COMMA_expr_) = _v in
        ((let (_menhir_env : _menhir_env) = _menhir_env in
        let (_menhir_stack : ('freshtv399 * Lexing.position * _menhir_state * 'tv_expr * Lexing.position)) = Obj.magic _menhir_stack in
        let (_ : _menhir_state) = _menhir_s in
        let ((xs : 'tv_separated_nonempty_list_COMMA_expr_) : 'tv_separated_nonempty_list_COMMA_expr_) = _v in
        ((let (_menhir_stack, _endpos_x_, _menhir_s, (x : 'tv_expr), _startpos_x_) = _menhir_stack in
        let _2 = () in
        let _v : 'tv_separated_nonempty_list_COMMA_expr_ = 
# 243 "/home/jc/.opam/4.07.1/lib/menhir/standard.mly"
    ( x :: xs )
# 601 "parser.ml"
         in
        _menhir_goto_separated_nonempty_list_COMMA_expr_ _menhir_env _menhir_stack _menhir_s _v) : 'freshtv400)) : 'freshtv402)
    | _ ->
        _menhir_fail ()

and _menhir_run61 : _menhir_env -> 'ttv_tail * Lexing.position * _menhir_state * 'tv_expr * Lexing.position -> 'ttv_return =
  fun _menhir_env _menhir_stack ->
    let _menhir_env = _menhir_discard _menhir_env in
    let _tok = _menhir_env._menhir_token in
    match _tok with
    | BANG ->
        _menhir_run51 _menhir_env (Obj.magic _menhir_stack) MenhirState61 _menhir_env._menhir_lexbuf.Lexing.lex_start_p
    | IDENT _v ->
        _menhir_run2 _menhir_env (Obj.magic _menhir_stack) _menhir_env._menhir_lexbuf.Lexing.lex_curr_p MenhirState61 _v _menhir_env._menhir_lexbuf.Lexing.lex_start_p
    | INTEGER _v ->
        _menhir_run50 _menhir_env (Obj.magic _menhir_stack) _menhir_env._menhir_lexbuf.Lexing.lex_curr_p MenhirState61 _v _menhir_env._menhir_lexbuf.Lexing.lex_start_p
    | LPAR ->
        _menhir_run49 _menhir_env (Obj.magic _menhir_stack) MenhirState61 _menhir_env._menhir_lexbuf.Lexing.lex_start_p
    | MINUS ->
        _menhir_run48 _menhir_env (Obj.magic _menhir_stack) MenhirState61 _menhir_env._menhir_lexbuf.Lexing.lex_start_p
    | SIZEOF ->
        _menhir_run43 _menhir_env (Obj.magic _menhir_stack) MenhirState61 _menhir_env._menhir_lexbuf.Lexing.lex_start_p
    | _ ->
        assert (not _menhir_env._menhir_error);
        _menhir_env._menhir_error <- true;
        _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) MenhirState61

and _menhir_run63 : _menhir_env -> 'ttv_tail * Lexing.position * _menhir_state * 'tv_expr * Lexing.position -> 'ttv_return =
  fun _menhir_env _menhir_stack ->
    let _menhir_env = _menhir_discard _menhir_env in
    let _tok = _menhir_env._menhir_token in
    match _tok with
    | BANG ->
        _menhir_run51 _menhir_env (Obj.magic _menhir_stack) MenhirState63 _menhir_env._menhir_lexbuf.Lexing.lex_start_p
    | IDENT _v ->
        _menhir_run2 _menhir_env (Obj.magic _menhir_stack) _menhir_env._menhir_lexbuf.Lexing.lex_curr_p MenhirState63 _v _menhir_env._menhir_lexbuf.Lexing.lex_start_p
    | INTEGER _v ->
        _menhir_run50 _menhir_env (Obj.magic _menhir_stack) _menhir_env._menhir_lexbuf.Lexing.lex_curr_p MenhirState63 _v _menhir_env._menhir_lexbuf.Lexing.lex_start_p
    | LPAR ->
        _menhir_run49 _menhir_env (Obj.magic _menhir_stack) MenhirState63 _menhir_env._menhir_lexbuf.Lexing.lex_start_p
    | MINUS ->
        _menhir_run48 _menhir_env (Obj.magic _menhir_stack) MenhirState63 _menhir_env._menhir_lexbuf.Lexing.lex_start_p
    | SIZEOF ->
        _menhir_run43 _menhir_env (Obj.magic _menhir_stack) MenhirState63 _menhir_env._menhir_lexbuf.Lexing.lex_start_p
    | _ ->
        assert (not _menhir_env._menhir_error);
        _menhir_env._menhir_error <- true;
        _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) MenhirState63

and _menhir_run67 : _menhir_env -> 'ttv_tail * Lexing.position * _menhir_state * 'tv_expr * Lexing.position -> 'ttv_return =
  fun _menhir_env _menhir_stack ->
    let _menhir_env = _menhir_discard _menhir_env in
    let _tok = _menhir_env._menhir_token in
    match _tok with
    | BANG ->
        _menhir_run51 _menhir_env (Obj.magic _menhir_stack) MenhirState67 _menhir_env._menhir_lexbuf.Lexing.lex_start_p
    | IDENT _v ->
        _menhir_run2 _menhir_env (Obj.magic _menhir_stack) _menhir_env._menhir_lexbuf.Lexing.lex_curr_p MenhirState67 _v _menhir_env._menhir_lexbuf.Lexing.lex_start_p
    | INTEGER _v ->
        _menhir_run50 _menhir_env (Obj.magic _menhir_stack) _menhir_env._menhir_lexbuf.Lexing.lex_curr_p MenhirState67 _v _menhir_env._menhir_lexbuf.Lexing.lex_start_p
    | LPAR ->
        _menhir_run49 _menhir_env (Obj.magic _menhir_stack) MenhirState67 _menhir_env._menhir_lexbuf.Lexing.lex_start_p
    | MINUS ->
        _menhir_run48 _menhir_env (Obj.magic _menhir_stack) MenhirState67 _menhir_env._menhir_lexbuf.Lexing.lex_start_p
    | SIZEOF ->
        _menhir_run43 _menhir_env (Obj.magic _menhir_stack) MenhirState67 _menhir_env._menhir_lexbuf.Lexing.lex_start_p
    | _ ->
        assert (not _menhir_env._menhir_error);
        _menhir_env._menhir_error <- true;
        _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) MenhirState67

and _menhir_run69 : _menhir_env -> 'ttv_tail * Lexing.position * _menhir_state * 'tv_expr * Lexing.position -> 'ttv_return =
  fun _menhir_env _menhir_stack ->
    let _menhir_env = _menhir_discard _menhir_env in
    let _tok = _menhir_env._menhir_token in
    match _tok with
    | BANG ->
        _menhir_run51 _menhir_env (Obj.magic _menhir_stack) MenhirState69 _menhir_env._menhir_lexbuf.Lexing.lex_start_p
    | IDENT _v ->
        _menhir_run2 _menhir_env (Obj.magic _menhir_stack) _menhir_env._menhir_lexbuf.Lexing.lex_curr_p MenhirState69 _v _menhir_env._menhir_lexbuf.Lexing.lex_start_p
    | INTEGER _v ->
        _menhir_run50 _menhir_env (Obj.magic _menhir_stack) _menhir_env._menhir_lexbuf.Lexing.lex_curr_p MenhirState69 _v _menhir_env._menhir_lexbuf.Lexing.lex_start_p
    | LPAR ->
        _menhir_run49 _menhir_env (Obj.magic _menhir_stack) MenhirState69 _menhir_env._menhir_lexbuf.Lexing.lex_start_p
    | MINUS ->
        _menhir_run48 _menhir_env (Obj.magic _menhir_stack) MenhirState69 _menhir_env._menhir_lexbuf.Lexing.lex_start_p
    | SIZEOF ->
        _menhir_run43 _menhir_env (Obj.magic _menhir_stack) MenhirState69 _menhir_env._menhir_lexbuf.Lexing.lex_start_p
    | _ ->
        assert (not _menhir_env._menhir_error);
        _menhir_env._menhir_error <- true;
        _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) MenhirState69

and _menhir_run71 : _menhir_env -> 'ttv_tail * Lexing.position * _menhir_state * 'tv_expr * Lexing.position -> Lexing.position -> 'ttv_return =
  fun _menhir_env _menhir_stack _startpos ->
    let _menhir_stack = (_menhir_stack, _startpos) in
    let _menhir_env = _menhir_discard _menhir_env in
    let _tok = _menhir_env._menhir_token in
    match _tok with
    | BANG ->
        _menhir_run51 _menhir_env (Obj.magic _menhir_stack) MenhirState71 _menhir_env._menhir_lexbuf.Lexing.lex_start_p
    | IDENT _v ->
        _menhir_run2 _menhir_env (Obj.magic _menhir_stack) _menhir_env._menhir_lexbuf.Lexing.lex_curr_p MenhirState71 _v _menhir_env._menhir_lexbuf.Lexing.lex_start_p
    | INTEGER _v ->
        _menhir_run50 _menhir_env (Obj.magic _menhir_stack) _menhir_env._menhir_lexbuf.Lexing.lex_curr_p MenhirState71 _v _menhir_env._menhir_lexbuf.Lexing.lex_start_p
    | LPAR ->
        _menhir_run49 _menhir_env (Obj.magic _menhir_stack) MenhirState71 _menhir_env._menhir_lexbuf.Lexing.lex_start_p
    | MINUS ->
        _menhir_run48 _menhir_env (Obj.magic _menhir_stack) MenhirState71 _menhir_env._menhir_lexbuf.Lexing.lex_start_p
    | SIZEOF ->
        _menhir_run43 _menhir_env (Obj.magic _menhir_stack) MenhirState71 _menhir_env._menhir_lexbuf.Lexing.lex_start_p
    | _ ->
        assert (not _menhir_env._menhir_error);
        _menhir_env._menhir_error <- true;
        _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) MenhirState71

and _menhir_run73 : _menhir_env -> 'ttv_tail * Lexing.position * _menhir_state * 'tv_expr * Lexing.position -> (
# 32 "parser.mly"
       (Ptree.binop)
# 721 "parser.ml"
) -> 'ttv_return =
  fun _menhir_env _menhir_stack _v ->
    let _menhir_stack = (_menhir_stack, _v) in
    let _menhir_env = _menhir_discard _menhir_env in
    let _tok = _menhir_env._menhir_token in
    match _tok with
    | BANG ->
        _menhir_run51 _menhir_env (Obj.magic _menhir_stack) MenhirState73 _menhir_env._menhir_lexbuf.Lexing.lex_start_p
    | IDENT _v ->
        _menhir_run2 _menhir_env (Obj.magic _menhir_stack) _menhir_env._menhir_lexbuf.Lexing.lex_curr_p MenhirState73 _v _menhir_env._menhir_lexbuf.Lexing.lex_start_p
    | INTEGER _v ->
        _menhir_run50 _menhir_env (Obj.magic _menhir_stack) _menhir_env._menhir_lexbuf.Lexing.lex_curr_p MenhirState73 _v _menhir_env._menhir_lexbuf.Lexing.lex_start_p
    | LPAR ->
        _menhir_run49 _menhir_env (Obj.magic _menhir_stack) MenhirState73 _menhir_env._menhir_lexbuf.Lexing.lex_start_p
    | MINUS ->
        _menhir_run48 _menhir_env (Obj.magic _menhir_stack) MenhirState73 _menhir_env._menhir_lexbuf.Lexing.lex_start_p
    | SIZEOF ->
        _menhir_run43 _menhir_env (Obj.magic _menhir_stack) MenhirState73 _menhir_env._menhir_lexbuf.Lexing.lex_start_p
    | _ ->
        assert (not _menhir_env._menhir_error);
        _menhir_env._menhir_error <- true;
        _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) MenhirState73

and _menhir_run75 : _menhir_env -> 'ttv_tail * Lexing.position * _menhir_state * 'tv_expr * Lexing.position -> (
# 33 "parser.mly"
       (Ptree.binop)
# 748 "parser.ml"
) -> 'ttv_return =
  fun _menhir_env _menhir_stack _v ->
    let _menhir_stack = (_menhir_stack, _v) in
    let _menhir_env = _menhir_discard _menhir_env in
    let _tok = _menhir_env._menhir_token in
    match _tok with
    | BANG ->
        _menhir_run51 _menhir_env (Obj.magic _menhir_stack) MenhirState75 _menhir_env._menhir_lexbuf.Lexing.lex_start_p
    | IDENT _v ->
        _menhir_run2 _menhir_env (Obj.magic _menhir_stack) _menhir_env._menhir_lexbuf.Lexing.lex_curr_p MenhirState75 _v _menhir_env._menhir_lexbuf.Lexing.lex_start_p
    | INTEGER _v ->
        _menhir_run50 _menhir_env (Obj.magic _menhir_stack) _menhir_env._menhir_lexbuf.Lexing.lex_curr_p MenhirState75 _v _menhir_env._menhir_lexbuf.Lexing.lex_start_p
    | LPAR ->
        _menhir_run49 _menhir_env (Obj.magic _menhir_stack) MenhirState75 _menhir_env._menhir_lexbuf.Lexing.lex_start_p
    | MINUS ->
        _menhir_run48 _menhir_env (Obj.magic _menhir_stack) MenhirState75 _menhir_env._menhir_lexbuf.Lexing.lex_start_p
    | SIZEOF ->
        _menhir_run43 _menhir_env (Obj.magic _menhir_stack) MenhirState75 _menhir_env._menhir_lexbuf.Lexing.lex_start_p
    | _ ->
        assert (not _menhir_env._menhir_error);
        _menhir_env._menhir_error <- true;
        _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) MenhirState75

and _menhir_run65 : _menhir_env -> 'ttv_tail * Lexing.position * _menhir_state * 'tv_expr * Lexing.position -> 'ttv_return =
  fun _menhir_env _menhir_stack ->
    let _menhir_env = _menhir_discard _menhir_env in
    let _tok = _menhir_env._menhir_token in
    match _tok with
    | IDENT _v ->
        _menhir_run2 _menhir_env (Obj.magic _menhir_stack) _menhir_env._menhir_lexbuf.Lexing.lex_curr_p MenhirState65 _v _menhir_env._menhir_lexbuf.Lexing.lex_start_p
    | _ ->
        assert (not _menhir_env._menhir_error);
        _menhir_env._menhir_error <- true;
        _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) MenhirState65

and _menhir_run77 : _menhir_env -> 'ttv_tail * Lexing.position * _menhir_state * 'tv_expr * Lexing.position -> 'ttv_return =
  fun _menhir_env _menhir_stack ->
    let _menhir_env = _menhir_discard _menhir_env in
    let _tok = _menhir_env._menhir_token in
    match _tok with
    | BANG ->
        _menhir_run51 _menhir_env (Obj.magic _menhir_stack) MenhirState77 _menhir_env._menhir_lexbuf.Lexing.lex_start_p
    | IDENT _v ->
        _menhir_run2 _menhir_env (Obj.magic _menhir_stack) _menhir_env._menhir_lexbuf.Lexing.lex_curr_p MenhirState77 _v _menhir_env._menhir_lexbuf.Lexing.lex_start_p
    | INTEGER _v ->
        _menhir_run50 _menhir_env (Obj.magic _menhir_stack) _menhir_env._menhir_lexbuf.Lexing.lex_curr_p MenhirState77 _v _menhir_env._menhir_lexbuf.Lexing.lex_start_p
    | LPAR ->
        _menhir_run49 _menhir_env (Obj.magic _menhir_stack) MenhirState77 _menhir_env._menhir_lexbuf.Lexing.lex_start_p
    | MINUS ->
        _menhir_run48 _menhir_env (Obj.magic _menhir_stack) MenhirState77 _menhir_env._menhir_lexbuf.Lexing.lex_start_p
    | SIZEOF ->
        _menhir_run43 _menhir_env (Obj.magic _menhir_stack) MenhirState77 _menhir_env._menhir_lexbuf.Lexing.lex_start_p
    | _ ->
        assert (not _menhir_env._menhir_error);
        _menhir_env._menhir_error <- true;
        _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) MenhirState77

and _menhir_goto_decl_var : _menhir_env -> 'ttv_tail -> _menhir_state -> 'tv_decl_var -> 'ttv_return =
  fun _menhir_env _menhir_stack _menhir_s _v ->
    let _menhir_stack = (_menhir_stack, _menhir_s, _v) in
    let (_menhir_env : _menhir_env) = _menhir_env in
    let (_menhir_stack : 'freshtv393 * _menhir_state * 'tv_decl_var) = Obj.magic _menhir_stack in
    ((assert (not _menhir_env._menhir_error);
    let _tok = _menhir_env._menhir_token in
    match _tok with
    | INT ->
        _menhir_run16 _menhir_env (Obj.magic _menhir_stack) MenhirState25
    | STRUCT ->
        _menhir_run7 _menhir_env (Obj.magic _menhir_stack) MenhirState25
    | BANG | IDENT _ | IF | INTEGER _ | LBRACE | LPAR | MINUS | RBRACE | RETURN | SEMICOLON | SIZEOF | WHILE ->
        _menhir_reduce31 _menhir_env (Obj.magic _menhir_stack) MenhirState25
    | _ ->
        assert (not _menhir_env._menhir_error);
        _menhir_env._menhir_error <- true;
        _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) MenhirState25) : 'freshtv394)

and _menhir_goto_separated_nonempty_list_COMMA_formal_ : _menhir_env -> 'ttv_tail -> _menhir_state -> 'tv_separated_nonempty_list_COMMA_formal_ -> 'ttv_return =
  fun _menhir_env _menhir_stack _menhir_s _v ->
    match _menhir_s with
    | MenhirState32 ->
        let (_menhir_env : _menhir_env) = _menhir_env in
        let (_menhir_stack : 'freshtv387) = Obj.magic _menhir_stack in
        let (_menhir_s : _menhir_state) = _menhir_s in
        let (_v : 'tv_separated_nonempty_list_COMMA_formal_) = _v in
        ((let (_menhir_env : _menhir_env) = _menhir_env in
        let (_menhir_stack : 'freshtv385) = Obj.magic _menhir_stack in
        let (_menhir_s : _menhir_state) = _menhir_s in
        let ((x : 'tv_separated_nonempty_list_COMMA_formal_) : 'tv_separated_nonempty_list_COMMA_formal_) = _v in
        ((let _v : 'tv_loption_separated_nonempty_list_COMMA_formal__ = 
# 144 "/home/jc/.opam/4.07.1/lib/menhir/standard.mly"
    ( x )
# 840 "parser.ml"
         in
        _menhir_goto_loption_separated_nonempty_list_COMMA_formal__ _menhir_env _menhir_stack _menhir_s _v) : 'freshtv386)) : 'freshtv388)
    | MenhirState110 ->
        let (_menhir_env : _menhir_env) = _menhir_env in
        let (_menhir_stack : ('freshtv391 * _menhir_state * 'tv_formal)) = Obj.magic _menhir_stack in
        let (_menhir_s : _menhir_state) = _menhir_s in
        let (_v : 'tv_separated_nonempty_list_COMMA_formal_) = _v in
        ((let (_menhir_env : _menhir_env) = _menhir_env in
        let (_menhir_stack : ('freshtv389 * _menhir_state * 'tv_formal)) = Obj.magic _menhir_stack in
        let (_ : _menhir_state) = _menhir_s in
        let ((xs : 'tv_separated_nonempty_list_COMMA_formal_) : 'tv_separated_nonempty_list_COMMA_formal_) = _v in
        ((let (_menhir_stack, _menhir_s, (x : 'tv_formal)) = _menhir_stack in
        let _2 = () in
        let _v : 'tv_separated_nonempty_list_COMMA_formal_ = 
# 243 "/home/jc/.opam/4.07.1/lib/menhir/standard.mly"
    ( x :: xs )
# 857 "parser.ml"
         in
        _menhir_goto_separated_nonempty_list_COMMA_formal_ _menhir_env _menhir_stack _menhir_s _v) : 'freshtv390)) : 'freshtv392)
    | _ ->
        _menhir_fail ()

and _menhir_goto_loption_separated_nonempty_list_COMMA_formal__ : _menhir_env -> 'ttv_tail -> _menhir_state -> 'tv_loption_separated_nonempty_list_COMMA_formal__ -> 'ttv_return =
  fun _menhir_env _menhir_stack _menhir_s _v ->
    let (_menhir_env : _menhir_env) = _menhir_env in
    let (_menhir_stack : 'freshtv383) = Obj.magic _menhir_stack in
    let (_menhir_s : _menhir_state) = _menhir_s in
    let (_v : 'tv_loption_separated_nonempty_list_COMMA_formal__) = _v in
    ((let (_menhir_env : _menhir_env) = _menhir_env in
    let (_menhir_stack : 'freshtv381) = Obj.magic _menhir_stack in
    let (_menhir_s : _menhir_state) = _menhir_s in
    let ((xs : 'tv_loption_separated_nonempty_list_COMMA_formal__) : 'tv_loption_separated_nonempty_list_COMMA_formal__) = _v in
    ((let _v : 'tv_formals = let f = 
# 232 "/home/jc/.opam/4.07.1/lib/menhir/standard.mly"
    ( xs )
# 876 "parser.ml"
     in
    
# 92 "parser.mly"
                                    ( f )
# 881 "parser.ml"
     in
    let (_menhir_env : _menhir_env) = _menhir_env in
    let (_menhir_stack : 'freshtv379) = _menhir_stack in
    let (_menhir_s : _menhir_state) = _menhir_s in
    let (_v : 'tv_formals) = _v in
    ((let _menhir_stack = (_menhir_stack, _menhir_s, _v) in
    let (_menhir_env : _menhir_env) = _menhir_env in
    let (_menhir_stack : (('freshtv377 * _menhir_state * 'tv_formal) * Lexing.position) * _menhir_state * 'tv_formals) = Obj.magic _menhir_stack in
    ((assert (not _menhir_env._menhir_error);
    let _tok = _menhir_env._menhir_token in
    match _tok with
    | RPAR ->
        let (_menhir_env : _menhir_env) = _menhir_env in
        let (_menhir_stack : (('freshtv373 * _menhir_state * 'tv_formal) * Lexing.position) * _menhir_state * 'tv_formals) = Obj.magic _menhir_stack in
        let (_endpos : Lexing.position) = _menhir_env._menhir_lexbuf.Lexing.lex_curr_p in
        ((let _menhir_stack = (_menhir_stack, _endpos) in
        let _menhir_env = _menhir_discard _menhir_env in
        let _tok = _menhir_env._menhir_token in
        match _tok with
        | LBRACE ->
            _menhir_run39 _menhir_env (Obj.magic _menhir_stack) MenhirState38 _menhir_env._menhir_lexbuf.Lexing.lex_start_p
        | _ ->
            assert (not _menhir_env._menhir_error);
            _menhir_env._menhir_error <- true;
            _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) MenhirState38) : 'freshtv374)
    | _ ->
        assert (not _menhir_env._menhir_error);
        _menhir_env._menhir_error <- true;
        let (_menhir_env : _menhir_env) = _menhir_env in
        let (_menhir_stack : (('freshtv375 * _menhir_state * 'tv_formal) * Lexing.position) * _menhir_state * 'tv_formals) = Obj.magic _menhir_stack in
        ((let (_menhir_stack, _menhir_s, _) = _menhir_stack in
        _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s) : 'freshtv376)) : 'freshtv378)) : 'freshtv380)) : 'freshtv382)) : 'freshtv384)

and _menhir_run33 : _menhir_env -> 'ttv_tail -> _menhir_state -> 'ttv_return =
  fun _menhir_env _menhir_stack _menhir_s ->
    let _menhir_stack = (_menhir_stack, _menhir_s) in
    let _menhir_env = _menhir_discard _menhir_env in
    let _tok = _menhir_env._menhir_token in
    match _tok with
    | IDENT _v ->
        _menhir_run2 _menhir_env (Obj.magic _menhir_stack) _menhir_env._menhir_lexbuf.Lexing.lex_curr_p MenhirState33 _v _menhir_env._menhir_lexbuf.Lexing.lex_start_p
    | _ ->
        assert (not _menhir_env._menhir_error);
        _menhir_env._menhir_error <- true;
        _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) MenhirState33

and _menhir_goto_list_decl_var_ : _menhir_env -> 'ttv_tail -> _menhir_state -> 'tv_list_decl_var_ -> 'ttv_return =
  fun _menhir_env _menhir_stack _menhir_s _v ->
    let _menhir_stack = (_menhir_stack, _menhir_s, _v) in
    match _menhir_s with
    | MenhirState6 ->
        let (_menhir_env : _menhir_env) = _menhir_env in
        let (_menhir_stack : ((('freshtv365 * _menhir_state) * Lexing.position * _menhir_state * 'tv_ident * Lexing.position) * Lexing.position) * _menhir_state * 'tv_list_decl_var_) = Obj.magic _menhir_stack in
        ((assert (not _menhir_env._menhir_error);
        let _tok = _menhir_env._menhir_token in
        match _tok with
        | RBRACE ->
            let (_menhir_env : _menhir_env) = _menhir_env in
            let (_menhir_stack : ((('freshtv361 * _menhir_state) * Lexing.position * _menhir_state * 'tv_ident * Lexing.position) * Lexing.position) * _menhir_state * 'tv_list_decl_var_) = Obj.magic _menhir_stack in
            let (_endpos : Lexing.position) = _menhir_env._menhir_lexbuf.Lexing.lex_curr_p in
            ((let _menhir_stack = (_menhir_stack, _endpos) in
            let _menhir_env = _menhir_discard _menhir_env in
            let _tok = _menhir_env._menhir_token in
            match _tok with
            | SEMICOLON ->
                let (_menhir_env : _menhir_env) = _menhir_env in
                let (_menhir_stack : (((('freshtv357 * _menhir_state) * Lexing.position * _menhir_state * 'tv_ident * Lexing.position) * Lexing.position) * _menhir_state * 'tv_list_decl_var_) * Lexing.position) = Obj.magic _menhir_stack in
                let (_endpos : Lexing.position) = _menhir_env._menhir_lexbuf.Lexing.lex_curr_p in
                let (_startpos : Lexing.position) = _menhir_env._menhir_lexbuf.Lexing.lex_start_p in
                ((let _menhir_env = _menhir_discard _menhir_env in
                let (_menhir_env : _menhir_env) = _menhir_env in
                let (_menhir_stack : (((('freshtv355 * _menhir_state) * Lexing.position * _menhir_state * 'tv_ident * Lexing.position) * Lexing.position) * _menhir_state * 'tv_list_decl_var_) * Lexing.position) = Obj.magic _menhir_stack in
                let (_endpos__6_ : Lexing.position) = _endpos in
                let (_startpos__6_ : Lexing.position) = _startpos in
                ((let (((((_menhir_stack, _menhir_s), _endpos_s_, _, (s : 'tv_ident), _startpos_s_), _startpos__3_), _, (fl : 'tv_list_decl_var_)), _endpos__5_) = _menhir_stack in
                let _6 = () in
                let _5 = () in
                let _3 = () in
                let _1 = () in
                let _v : 'tv_decl = 
# 66 "parser.mly"
    ( Dstruct (s, List.flatten fl) )
# 964 "parser.ml"
                 in
                _menhir_goto_decl _menhir_env _menhir_stack _menhir_s _v) : 'freshtv356)) : 'freshtv358)
            | _ ->
                assert (not _menhir_env._menhir_error);
                _menhir_env._menhir_error <- true;
                let (_menhir_env : _menhir_env) = _menhir_env in
                let (_menhir_stack : (((('freshtv359 * _menhir_state) * Lexing.position * _menhir_state * 'tv_ident * Lexing.position) * Lexing.position) * _menhir_state * 'tv_list_decl_var_) * Lexing.position) = Obj.magic _menhir_stack in
                ((let ((_menhir_stack, _menhir_s, _), _) = _menhir_stack in
                _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s) : 'freshtv360)) : 'freshtv362)
        | _ ->
            assert (not _menhir_env._menhir_error);
            _menhir_env._menhir_error <- true;
            let (_menhir_env : _menhir_env) = _menhir_env in
            let (_menhir_stack : ((('freshtv363 * _menhir_state) * Lexing.position * _menhir_state * 'tv_ident * Lexing.position) * Lexing.position) * _menhir_state * 'tv_list_decl_var_) = Obj.magic _menhir_stack in
            ((let (_menhir_stack, _menhir_s, _) = _menhir_stack in
            _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s) : 'freshtv364)) : 'freshtv366)
    | MenhirState25 ->
        let (_menhir_env : _menhir_env) = _menhir_env in
        let (_menhir_stack : ('freshtv369 * _menhir_state * 'tv_decl_var) * _menhir_state * 'tv_list_decl_var_) = Obj.magic _menhir_stack in
        ((let (_menhir_env : _menhir_env) = _menhir_env in
        let (_menhir_stack : ('freshtv367 * _menhir_state * 'tv_decl_var) * _menhir_state * 'tv_list_decl_var_) = Obj.magic _menhir_stack in
        ((let ((_menhir_stack, _menhir_s, (x : 'tv_decl_var)), _, (xs : 'tv_list_decl_var_)) = _menhir_stack in
        let _v : 'tv_list_decl_var_ = 
# 213 "/home/jc/.opam/4.07.1/lib/menhir/standard.mly"
    ( x :: xs )
# 990 "parser.ml"
         in
        _menhir_goto_list_decl_var_ _menhir_env _menhir_stack _menhir_s _v) : 'freshtv368)) : 'freshtv370)
    | MenhirState39 ->
        let (_menhir_env : _menhir_env) = _menhir_env in
        let (_menhir_stack : ('freshtv371 * _menhir_state * Lexing.position) * _menhir_state * 'tv_list_decl_var_) = Obj.magic _menhir_stack in
        ((assert (not _menhir_env._menhir_error);
        let _tok = _menhir_env._menhir_token in
        match _tok with
        | BANG ->
            _menhir_run51 _menhir_env (Obj.magic _menhir_stack) MenhirState40 _menhir_env._menhir_lexbuf.Lexing.lex_start_p
        | IDENT _v ->
            _menhir_run2 _menhir_env (Obj.magic _menhir_stack) _menhir_env._menhir_lexbuf.Lexing.lex_curr_p MenhirState40 _v _menhir_env._menhir_lexbuf.Lexing.lex_start_p
        | IF ->
            _menhir_run92 _menhir_env (Obj.magic _menhir_stack) MenhirState40 _menhir_env._menhir_lexbuf.Lexing.lex_start_p
        | INTEGER _v ->
            _menhir_run50 _menhir_env (Obj.magic _menhir_stack) _menhir_env._menhir_lexbuf.Lexing.lex_curr_p MenhirState40 _v _menhir_env._menhir_lexbuf.Lexing.lex_start_p
        | LBRACE ->
            _menhir_run39 _menhir_env (Obj.magic _menhir_stack) MenhirState40 _menhir_env._menhir_lexbuf.Lexing.lex_start_p
        | LPAR ->
            _menhir_run49 _menhir_env (Obj.magic _menhir_stack) MenhirState40 _menhir_env._menhir_lexbuf.Lexing.lex_start_p
        | MINUS ->
            _menhir_run48 _menhir_env (Obj.magic _menhir_stack) MenhirState40 _menhir_env._menhir_lexbuf.Lexing.lex_start_p
        | RETURN ->
            _menhir_run89 _menhir_env (Obj.magic _menhir_stack) MenhirState40 _menhir_env._menhir_lexbuf.Lexing.lex_start_p
        | SEMICOLON ->
            _menhir_run88 _menhir_env (Obj.magic _menhir_stack) _menhir_env._menhir_lexbuf.Lexing.lex_curr_p MenhirState40 _menhir_env._menhir_lexbuf.Lexing.lex_start_p
        | SIZEOF ->
            _menhir_run43 _menhir_env (Obj.magic _menhir_stack) MenhirState40 _menhir_env._menhir_lexbuf.Lexing.lex_start_p
        | WHILE ->
            _menhir_run41 _menhir_env (Obj.magic _menhir_stack) MenhirState40 _menhir_env._menhir_lexbuf.Lexing.lex_start_p
        | RBRACE ->
            _menhir_reduce33 _menhir_env (Obj.magic _menhir_stack) MenhirState40
        | _ ->
            assert (not _menhir_env._menhir_error);
            _menhir_env._menhir_error <- true;
            _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) MenhirState40) : 'freshtv372)
    | _ ->
        _menhir_fail ()

and _menhir_fail : unit -> 'a =
  fun () ->
    Printf.fprintf stderr "Internal failure -- please contact the parser generator's developers.\n%!";
    assert false

and _menhir_goto_lvalue : _menhir_env -> 'ttv_tail -> Lexing.position -> _menhir_state -> 'tv_lvalue -> Lexing.position -> 'ttv_return =
  fun _menhir_env _menhir_stack _endpos _menhir_s _v _startpos ->
    let _menhir_stack = (_menhir_stack, _endpos, _menhir_s, _v, _startpos) in
    let (_menhir_env : _menhir_env) = _menhir_env in
    let (_menhir_stack : 'freshtv353 * Lexing.position * _menhir_state * 'tv_lvalue * Lexing.position) = Obj.magic _menhir_stack in
    ((assert (not _menhir_env._menhir_error);
    let _tok = _menhir_env._menhir_token in
    match _tok with
    | EQ ->
        let (_menhir_env : _menhir_env) = _menhir_env in
        let (_menhir_stack : 'freshtv347 * Lexing.position * _menhir_state * 'tv_lvalue * Lexing.position) = Obj.magic _menhir_stack in
        ((let _menhir_env = _menhir_discard _menhir_env in
        let _tok = _menhir_env._menhir_token in
        match _tok with
        | BANG ->
            _menhir_run51 _menhir_env (Obj.magic _menhir_stack) MenhirState53 _menhir_env._menhir_lexbuf.Lexing.lex_start_p
        | IDENT _v ->
            _menhir_run2 _menhir_env (Obj.magic _menhir_stack) _menhir_env._menhir_lexbuf.Lexing.lex_curr_p MenhirState53 _v _menhir_env._menhir_lexbuf.Lexing.lex_start_p
        | INTEGER _v ->
            _menhir_run50 _menhir_env (Obj.magic _menhir_stack) _menhir_env._menhir_lexbuf.Lexing.lex_curr_p MenhirState53 _v _menhir_env._menhir_lexbuf.Lexing.lex_start_p
        | LPAR ->
            _menhir_run49 _menhir_env (Obj.magic _menhir_stack) MenhirState53 _menhir_env._menhir_lexbuf.Lexing.lex_start_p
        | MINUS ->
            _menhir_run48 _menhir_env (Obj.magic _menhir_stack) MenhirState53 _menhir_env._menhir_lexbuf.Lexing.lex_start_p
        | SIZEOF ->
            _menhir_run43 _menhir_env (Obj.magic _menhir_stack) MenhirState53 _menhir_env._menhir_lexbuf.Lexing.lex_start_p
        | _ ->
            assert (not _menhir_env._menhir_error);
            _menhir_env._menhir_error <- true;
            _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) MenhirState53) : 'freshtv348)
    | AMPERSANDAMPERSAND | ARROW | COMMA | COMP _ | EQOP _ | MINUS | PLUS | RPAR | SEMICOLON | SLASH | STAR | VERTICALBARVERTICALBAR ->
        let (_menhir_env : _menhir_env) = _menhir_env in
        let (_menhir_stack : 'freshtv349 * Lexing.position * _menhir_state * 'tv_lvalue * Lexing.position) = Obj.magic _menhir_stack in
        ((let (_menhir_stack, _endpos__1_, _menhir_s, (_1 : 'tv_lvalue), _startpos__1_) = _menhir_stack in
        let _startpos = _startpos__1_ in
        let _endpos = _endpos__1_ in
        let _v : 'tv_expr_node = 
# 114 "parser.mly"
    ( Eright _1 )
# 1074 "parser.ml"
         in
        _menhir_goto_expr_node _menhir_env _menhir_stack _endpos _menhir_s _v _startpos) : 'freshtv350)
    | _ ->
        assert (not _menhir_env._menhir_error);
        _menhir_env._menhir_error <- true;
        let (_menhir_env : _menhir_env) = _menhir_env in
        let (_menhir_stack : 'freshtv351 * Lexing.position * _menhir_state * 'tv_lvalue * Lexing.position) = Obj.magic _menhir_stack in
        ((let (_menhir_stack, _, _menhir_s, _, _) = _menhir_stack in
        _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s) : 'freshtv352)) : 'freshtv354)

and _menhir_goto_loption_separated_nonempty_list_COMMA_expr__ : _menhir_env -> 'ttv_tail -> _menhir_state -> 'tv_loption_separated_nonempty_list_COMMA_expr__ -> 'ttv_return =
  fun _menhir_env _menhir_stack _menhir_s _v ->
    let _menhir_stack = (_menhir_stack, _menhir_s, _v) in
    let (_menhir_env : _menhir_env) = _menhir_env in
    let (_menhir_stack : (('freshtv345 * Lexing.position * _menhir_state * 'tv_ident * Lexing.position) * Lexing.position) * _menhir_state * 'tv_loption_separated_nonempty_list_COMMA_expr__) = Obj.magic _menhir_stack in
    ((assert (not _menhir_env._menhir_error);
    let _tok = _menhir_env._menhir_token in
    match _tok with
    | RPAR ->
        let (_menhir_env : _menhir_env) = _menhir_env in
        let (_menhir_stack : (('freshtv341 * Lexing.position * _menhir_state * 'tv_ident * Lexing.position) * Lexing.position) * _menhir_state * 'tv_loption_separated_nonempty_list_COMMA_expr__) = Obj.magic _menhir_stack in
        let (_endpos : Lexing.position) = _menhir_env._menhir_lexbuf.Lexing.lex_curr_p in
        ((let _menhir_env = _menhir_discard _menhir_env in
        let (_menhir_env : _menhir_env) = _menhir_env in
        let (_menhir_stack : (('freshtv339 * Lexing.position * _menhir_state * 'tv_ident * Lexing.position) * Lexing.position) * _menhir_state * 'tv_loption_separated_nonempty_list_COMMA_expr__) = Obj.magic _menhir_stack in
        let (_endpos__4_ : Lexing.position) = _endpos in
        ((let (((_menhir_stack, _endpos_id_, _menhir_s, (id : 'tv_ident), _startpos_id_), _startpos__2_), _, (xs : 'tv_loption_separated_nonempty_list_COMMA_expr__)) = _menhir_stack in
        let _4 = () in
        let _2 = () in
        let _startpos = _startpos_id_ in
        let _endpos = _endpos__4_ in
        let _v : 'tv_expr_node = let el = 
# 232 "/home/jc/.opam/4.07.1/lib/menhir/standard.mly"
    ( xs )
# 1109 "parser.ml"
         in
        
# 140 "parser.mly"
    ( Ecall (id, el) )
# 1114 "parser.ml"
         in
        _menhir_goto_expr_node _menhir_env _menhir_stack _endpos _menhir_s _v _startpos) : 'freshtv340)) : 'freshtv342)
    | _ ->
        assert (not _menhir_env._menhir_error);
        _menhir_env._menhir_error <- true;
        let (_menhir_env : _menhir_env) = _menhir_env in
        let (_menhir_stack : (('freshtv343 * Lexing.position * _menhir_state * 'tv_ident * Lexing.position) * Lexing.position) * _menhir_state * 'tv_loption_separated_nonempty_list_COMMA_expr__) = Obj.magic _menhir_stack in
        ((let (_menhir_stack, _menhir_s, _) = _menhir_stack in
        _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s) : 'freshtv344)) : 'freshtv346)

and _menhir_run43 : _menhir_env -> 'ttv_tail -> _menhir_state -> Lexing.position -> 'ttv_return =
  fun _menhir_env _menhir_stack _menhir_s _startpos ->
    let _menhir_stack = (_menhir_stack, _menhir_s, _startpos) in
    let _menhir_env = _menhir_discard _menhir_env in
    let _tok = _menhir_env._menhir_token in
    match _tok with
    | LPAR ->
        let (_menhir_env : _menhir_env) = _menhir_env in
        let (_menhir_stack : 'freshtv335 * _menhir_state * Lexing.position) = Obj.magic _menhir_stack in
        let (_startpos : Lexing.position) = _menhir_env._menhir_lexbuf.Lexing.lex_start_p in
        ((let _menhir_stack = (_menhir_stack, _startpos) in
        let _menhir_env = _menhir_discard _menhir_env in
        let _tok = _menhir_env._menhir_token in
        match _tok with
        | STRUCT ->
            let (_menhir_env : _menhir_env) = _menhir_env in
            let (_menhir_stack : ('freshtv331 * _menhir_state * Lexing.position) * Lexing.position) = Obj.magic _menhir_stack in
            ((let _menhir_env = _menhir_discard _menhir_env in
            let _tok = _menhir_env._menhir_token in
            match _tok with
            | IDENT _v ->
                _menhir_run2 _menhir_env (Obj.magic _menhir_stack) _menhir_env._menhir_lexbuf.Lexing.lex_curr_p MenhirState45 _v _menhir_env._menhir_lexbuf.Lexing.lex_start_p
            | _ ->
                assert (not _menhir_env._menhir_error);
                _menhir_env._menhir_error <- true;
                _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) MenhirState45) : 'freshtv332)
        | _ ->
            assert (not _menhir_env._menhir_error);
            _menhir_env._menhir_error <- true;
            let (_menhir_env : _menhir_env) = _menhir_env in
            let (_menhir_stack : ('freshtv333 * _menhir_state * Lexing.position) * Lexing.position) = Obj.magic _menhir_stack in
            ((let ((_menhir_stack, _menhir_s, _), _) = _menhir_stack in
            _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s) : 'freshtv334)) : 'freshtv336)
    | _ ->
        assert (not _menhir_env._menhir_error);
        _menhir_env._menhir_error <- true;
        let (_menhir_env : _menhir_env) = _menhir_env in
        let (_menhir_stack : 'freshtv337 * _menhir_state * Lexing.position) = Obj.magic _menhir_stack in
        ((let (_menhir_stack, _menhir_s, _) = _menhir_stack in
        _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s) : 'freshtv338)

and _menhir_run48 : _menhir_env -> 'ttv_tail -> _menhir_state -> Lexing.position -> 'ttv_return =
  fun _menhir_env _menhir_stack _menhir_s _startpos ->
    let _menhir_stack = (_menhir_stack, _menhir_s, _startpos) in
    let _menhir_env = _menhir_discard _menhir_env in
    let _tok = _menhir_env._menhir_token in
    match _tok with
    | BANG ->
        _menhir_run51 _menhir_env (Obj.magic _menhir_stack) MenhirState48 _menhir_env._menhir_lexbuf.Lexing.lex_start_p
    | IDENT _v ->
        _menhir_run2 _menhir_env (Obj.magic _menhir_stack) _menhir_env._menhir_lexbuf.Lexing.lex_curr_p MenhirState48 _v _menhir_env._menhir_lexbuf.Lexing.lex_start_p
    | INTEGER _v ->
        _menhir_run50 _menhir_env (Obj.magic _menhir_stack) _menhir_env._menhir_lexbuf.Lexing.lex_curr_p MenhirState48 _v _menhir_env._menhir_lexbuf.Lexing.lex_start_p
    | LPAR ->
        _menhir_run49 _menhir_env (Obj.magic _menhir_stack) MenhirState48 _menhir_env._menhir_lexbuf.Lexing.lex_start_p
    | MINUS ->
        _menhir_run48 _menhir_env (Obj.magic _menhir_stack) MenhirState48 _menhir_env._menhir_lexbuf.Lexing.lex_start_p
    | SIZEOF ->
        _menhir_run43 _menhir_env (Obj.magic _menhir_stack) MenhirState48 _menhir_env._menhir_lexbuf.Lexing.lex_start_p
    | _ ->
        assert (not _menhir_env._menhir_error);
        _menhir_env._menhir_error <- true;
        _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) MenhirState48

and _menhir_run49 : _menhir_env -> 'ttv_tail -> _menhir_state -> Lexing.position -> 'ttv_return =
  fun _menhir_env _menhir_stack _menhir_s _startpos ->
    let _menhir_stack = (_menhir_stack, _menhir_s, _startpos) in
    let _menhir_env = _menhir_discard _menhir_env in
    let _tok = _menhir_env._menhir_token in
    match _tok with
    | BANG ->
        _menhir_run51 _menhir_env (Obj.magic _menhir_stack) MenhirState49 _menhir_env._menhir_lexbuf.Lexing.lex_start_p
    | IDENT _v ->
        _menhir_run2 _menhir_env (Obj.magic _menhir_stack) _menhir_env._menhir_lexbuf.Lexing.lex_curr_p MenhirState49 _v _menhir_env._menhir_lexbuf.Lexing.lex_start_p
    | INTEGER _v ->
        _menhir_run50 _menhir_env (Obj.magic _menhir_stack) _menhir_env._menhir_lexbuf.Lexing.lex_curr_p MenhirState49 _v _menhir_env._menhir_lexbuf.Lexing.lex_start_p
    | LPAR ->
        _menhir_run49 _menhir_env (Obj.magic _menhir_stack) MenhirState49 _menhir_env._menhir_lexbuf.Lexing.lex_start_p
    | MINUS ->
        _menhir_run48 _menhir_env (Obj.magic _menhir_stack) MenhirState49 _menhir_env._menhir_lexbuf.Lexing.lex_start_p
    | SIZEOF ->
        _menhir_run43 _menhir_env (Obj.magic _menhir_stack) MenhirState49 _menhir_env._menhir_lexbuf.Lexing.lex_start_p
    | _ ->
        assert (not _menhir_env._menhir_error);
        _menhir_env._menhir_error <- true;
        _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) MenhirState49

and _menhir_run50 : _menhir_env -> 'ttv_tail -> Lexing.position -> _menhir_state -> (
# 14 "parser.mly"
       (int32)
# 1215 "parser.ml"
) -> Lexing.position -> 'ttv_return =
  fun _menhir_env _menhir_stack _endpos _menhir_s _v _startpos ->
    let _menhir_env = _menhir_discard _menhir_env in
    let (_menhir_env : _menhir_env) = _menhir_env in
    let (_menhir_stack : 'freshtv329) = Obj.magic _menhir_stack in
    let (_endpos__1_ : Lexing.position) = _endpos in
    let (_menhir_s : _menhir_state) = _menhir_s in
    let ((_1 : (
# 14 "parser.mly"
       (int32)
# 1226 "parser.ml"
    )) : (
# 14 "parser.mly"
       (int32)
# 1230 "parser.ml"
    )) = _v in
    let (_startpos__1_ : Lexing.position) = _startpos in
    ((let _startpos = _startpos__1_ in
    let _endpos = _endpos__1_ in
    let _v : 'tv_expr_node = 
# 138 "parser.mly"
    ( Econst _1 )
# 1238 "parser.ml"
     in
    _menhir_goto_expr_node _menhir_env _menhir_stack _endpos _menhir_s _v _startpos) : 'freshtv330)

and _menhir_run51 : _menhir_env -> 'ttv_tail -> _menhir_state -> Lexing.position -> 'ttv_return =
  fun _menhir_env _menhir_stack _menhir_s _startpos ->
    let _menhir_stack = (_menhir_stack, _menhir_s, _startpos) in
    let _menhir_env = _menhir_discard _menhir_env in
    let _tok = _menhir_env._menhir_token in
    match _tok with
    | BANG ->
        _menhir_run51 _menhir_env (Obj.magic _menhir_stack) MenhirState51 _menhir_env._menhir_lexbuf.Lexing.lex_start_p
    | IDENT _v ->
        _menhir_run2 _menhir_env (Obj.magic _menhir_stack) _menhir_env._menhir_lexbuf.Lexing.lex_curr_p MenhirState51 _v _menhir_env._menhir_lexbuf.Lexing.lex_start_p
    | INTEGER _v ->
        _menhir_run50 _menhir_env (Obj.magic _menhir_stack) _menhir_env._menhir_lexbuf.Lexing.lex_curr_p MenhirState51 _v _menhir_env._menhir_lexbuf.Lexing.lex_start_p
    | LPAR ->
        _menhir_run49 _menhir_env (Obj.magic _menhir_stack) MenhirState51 _menhir_env._menhir_lexbuf.Lexing.lex_start_p
    | MINUS ->
        _menhir_run48 _menhir_env (Obj.magic _menhir_stack) MenhirState51 _menhir_env._menhir_lexbuf.Lexing.lex_start_p
    | SIZEOF ->
        _menhir_run43 _menhir_env (Obj.magic _menhir_stack) MenhirState51 _menhir_env._menhir_lexbuf.Lexing.lex_start_p
    | _ ->
        assert (not _menhir_env._menhir_error);
        _menhir_env._menhir_error <- true;
        _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) MenhirState51

and _menhir_goto_expr_node : _menhir_env -> 'ttv_tail -> Lexing.position -> _menhir_state -> 'tv_expr_node -> Lexing.position -> 'ttv_return =
  fun _menhir_env _menhir_stack _endpos _menhir_s _v _startpos ->
    let (_menhir_env : _menhir_env) = _menhir_env in
    let (_menhir_stack : 'freshtv327) = Obj.magic _menhir_stack in
    let (_endpos : Lexing.position) = _endpos in
    let (_menhir_s : _menhir_state) = _menhir_s in
    let (_v : 'tv_expr_node) = _v in
    let (_startpos : Lexing.position) = _startpos in
    ((let (_menhir_env : _menhir_env) = _menhir_env in
    let (_menhir_stack : 'freshtv325) = Obj.magic _menhir_stack in
    let (_endpos_e_ : Lexing.position) = _endpos in
    let (_menhir_s : _menhir_state) = _menhir_s in
    let ((e : 'tv_expr_node) : 'tv_expr_node) = _v in
    let (_startpos_e_ : Lexing.position) = _startpos in
    ((let _startpos = _startpos_e_ in
    let _endpos = _endpos_e_ in
    let _v : 'tv_expr = let _endpos = _endpos_e_ in
    let _startpos = _startpos_e_ in
    
# 109 "parser.mly"
  ( { expr_node = e; expr_loc = _startpos, _endpos } )
# 1286 "parser.ml"
     in
    let (_menhir_env : _menhir_env) = _menhir_env in
    let (_menhir_stack : 'freshtv323) = _menhir_stack in
    let (_endpos : Lexing.position) = _endpos in
    let (_menhir_s : _menhir_state) = _menhir_s in
    let (_v : 'tv_expr) = _v in
    let (_startpos : Lexing.position) = _startpos in
    ((let _menhir_stack = (_menhir_stack, _endpos, _menhir_s, _v, _startpos) in
    match _menhir_s with
    | MenhirState79 | MenhirState55 ->
        let (_menhir_env : _menhir_env) = _menhir_env in
        let (_menhir_stack : 'freshtv219 * Lexing.position * _menhir_state * 'tv_expr * Lexing.position) = Obj.magic _menhir_stack in
        ((assert (not _menhir_env._menhir_error);
        let _tok = _menhir_env._menhir_token in
        match _tok with
        | AMPERSANDAMPERSAND ->
            _menhir_run77 _menhir_env (Obj.magic _menhir_stack)
        | ARROW ->
            _menhir_run65 _menhir_env (Obj.magic _menhir_stack)
        | COMMA ->
            let (_menhir_env : _menhir_env) = _menhir_env in
            let (_menhir_stack : 'freshtv213 * Lexing.position * _menhir_state * 'tv_expr * Lexing.position) = Obj.magic _menhir_stack in
            ((let _menhir_env = _menhir_discard _menhir_env in
            let _tok = _menhir_env._menhir_token in
            match _tok with
            | BANG ->
                _menhir_run51 _menhir_env (Obj.magic _menhir_stack) MenhirState79 _menhir_env._menhir_lexbuf.Lexing.lex_start_p
            | IDENT _v ->
                _menhir_run2 _menhir_env (Obj.magic _menhir_stack) _menhir_env._menhir_lexbuf.Lexing.lex_curr_p MenhirState79 _v _menhir_env._menhir_lexbuf.Lexing.lex_start_p
            | INTEGER _v ->
                _menhir_run50 _menhir_env (Obj.magic _menhir_stack) _menhir_env._menhir_lexbuf.Lexing.lex_curr_p MenhirState79 _v _menhir_env._menhir_lexbuf.Lexing.lex_start_p
            | LPAR ->
                _menhir_run49 _menhir_env (Obj.magic _menhir_stack) MenhirState79 _menhir_env._menhir_lexbuf.Lexing.lex_start_p
            | MINUS ->
                _menhir_run48 _menhir_env (Obj.magic _menhir_stack) MenhirState79 _menhir_env._menhir_lexbuf.Lexing.lex_start_p
            | SIZEOF ->
                _menhir_run43 _menhir_env (Obj.magic _menhir_stack) MenhirState79 _menhir_env._menhir_lexbuf.Lexing.lex_start_p
            | _ ->
                assert (not _menhir_env._menhir_error);
                _menhir_env._menhir_error <- true;
                _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) MenhirState79) : 'freshtv214)
        | COMP _v ->
            _menhir_run75 _menhir_env (Obj.magic _menhir_stack) _v
        | EQOP _v ->
            _menhir_run73 _menhir_env (Obj.magic _menhir_stack) _v
        | MINUS ->
            _menhir_run71 _menhir_env (Obj.magic _menhir_stack) _menhir_env._menhir_lexbuf.Lexing.lex_start_p
        | PLUS ->
            _menhir_run69 _menhir_env (Obj.magic _menhir_stack)
        | SLASH ->
            _menhir_run67 _menhir_env (Obj.magic _menhir_stack)
        | STAR ->
            _menhir_run63 _menhir_env (Obj.magic _menhir_stack)
        | VERTICALBARVERTICALBAR ->
            _menhir_run61 _menhir_env (Obj.magic _menhir_stack)
        | RPAR ->
            let (_menhir_env : _menhir_env) = _menhir_env in
            let (_menhir_stack : 'freshtv215 * Lexing.position * _menhir_state * 'tv_expr * Lexing.position) = Obj.magic _menhir_stack in
            ((let (_menhir_stack, _endpos_x_, _menhir_s, (x : 'tv_expr), _startpos_x_) = _menhir_stack in
            let _v : 'tv_separated_nonempty_list_COMMA_expr_ = 
# 241 "/home/jc/.opam/4.07.1/lib/menhir/standard.mly"
    ( [ x ] )
# 1349 "parser.ml"
             in
            _menhir_goto_separated_nonempty_list_COMMA_expr_ _menhir_env _menhir_stack _menhir_s _v) : 'freshtv216)
        | _ ->
            assert (not _menhir_env._menhir_error);
            _menhir_env._menhir_error <- true;
            let (_menhir_env : _menhir_env) = _menhir_env in
            let (_menhir_stack : 'freshtv217 * Lexing.position * _menhir_state * 'tv_expr * Lexing.position) = Obj.magic _menhir_stack in
            ((let (_menhir_stack, _, _menhir_s, _, _) = _menhir_stack in
            _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s) : 'freshtv218)) : 'freshtv220)
    | MenhirState61 ->
        let (_menhir_env : _menhir_env) = _menhir_env in
        let (_menhir_stack : (('freshtv225 * Lexing.position * _menhir_state * 'tv_expr * Lexing.position)) * Lexing.position * _menhir_state * 'tv_expr * Lexing.position) = Obj.magic _menhir_stack in
        ((assert (not _menhir_env._menhir_error);
        let _tok = _menhir_env._menhir_token in
        match _tok with
        | AMPERSANDAMPERSAND ->
            _menhir_run77 _menhir_env (Obj.magic _menhir_stack)
        | ARROW ->
            _menhir_run65 _menhir_env (Obj.magic _menhir_stack)
        | COMP _v ->
            _menhir_run75 _menhir_env (Obj.magic _menhir_stack) _v
        | EQOP _v ->
            _menhir_run73 _menhir_env (Obj.magic _menhir_stack) _v
        | MINUS ->
            _menhir_run71 _menhir_env (Obj.magic _menhir_stack) _menhir_env._menhir_lexbuf.Lexing.lex_start_p
        | PLUS ->
            _menhir_run69 _menhir_env (Obj.magic _menhir_stack)
        | SLASH ->
            _menhir_run67 _menhir_env (Obj.magic _menhir_stack)
        | STAR ->
            _menhir_run63 _menhir_env (Obj.magic _menhir_stack)
        | COMMA | RPAR | SEMICOLON | VERTICALBARVERTICALBAR ->
            let (_menhir_env : _menhir_env) = _menhir_env in
            let (_menhir_stack : (('freshtv221 * Lexing.position * _menhir_state * 'tv_expr * Lexing.position)) * Lexing.position * _menhir_state * 'tv_expr * Lexing.position) = Obj.magic _menhir_stack in
            ((let ((_menhir_stack, _endpos__1_, _menhir_s, (_1 : 'tv_expr), _startpos__1_), _endpos__3_, _, (_3 : 'tv_expr), _startpos__3_) = _menhir_stack in
            let _2 = () in
            let _startpos = _startpos__1_ in
            let _endpos = _endpos__3_ in
            let _v : 'tv_expr_node = 
# 118 "parser.mly"
    ( Ebinop (Bor, _1, _3) )
# 1391 "parser.ml"
             in
            _menhir_goto_expr_node _menhir_env _menhir_stack _endpos _menhir_s _v _startpos) : 'freshtv222)
        | _ ->
            assert (not _menhir_env._menhir_error);
            _menhir_env._menhir_error <- true;
            let (_menhir_env : _menhir_env) = _menhir_env in
            let (_menhir_stack : (('freshtv223 * Lexing.position * _menhir_state * 'tv_expr * Lexing.position)) * Lexing.position * _menhir_state * 'tv_expr * Lexing.position) = Obj.magic _menhir_stack in
            ((let (_menhir_stack, _, _menhir_s, _, _) = _menhir_stack in
            _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s) : 'freshtv224)) : 'freshtv226)
    | MenhirState63 ->
        let (_menhir_env : _menhir_env) = _menhir_env in
        let (_menhir_stack : (('freshtv231 * Lexing.position * _menhir_state * 'tv_expr * Lexing.position)) * Lexing.position * _menhir_state * 'tv_expr * Lexing.position) = Obj.magic _menhir_stack in
        ((assert (not _menhir_env._menhir_error);
        let _tok = _menhir_env._menhir_token in
        match _tok with
        | ARROW ->
            _menhir_run65 _menhir_env (Obj.magic _menhir_stack)
        | AMPERSANDAMPERSAND | COMMA | COMP _ | EQOP _ | MINUS | PLUS | RPAR | SEMICOLON | SLASH | STAR | VERTICALBARVERTICALBAR ->
            let (_menhir_env : _menhir_env) = _menhir_env in
            let (_menhir_stack : (('freshtv227 * Lexing.position * _menhir_state * 'tv_expr * Lexing.position)) * Lexing.position * _menhir_state * 'tv_expr * Lexing.position) = Obj.magic _menhir_stack in
            ((let ((_menhir_stack, _endpos__1_, _menhir_s, (_1 : 'tv_expr), _startpos__1_), _endpos__3_, _, (_3 : 'tv_expr), _startpos__3_) = _menhir_stack in
            let _2 = () in
            let _startpos = _startpos__1_ in
            let _endpos = _endpos__3_ in
            let _v : 'tv_expr_node = 
# 130 "parser.mly"
    ( Ebinop (Bmul, _1, _3) )
# 1419 "parser.ml"
             in
            _menhir_goto_expr_node _menhir_env _menhir_stack _endpos _menhir_s _v _startpos) : 'freshtv228)
        | _ ->
            assert (not _menhir_env._menhir_error);
            _menhir_env._menhir_error <- true;
            let (_menhir_env : _menhir_env) = _menhir_env in
            let (_menhir_stack : (('freshtv229 * Lexing.position * _menhir_state * 'tv_expr * Lexing.position)) * Lexing.position * _menhir_state * 'tv_expr * Lexing.position) = Obj.magic _menhir_stack in
            ((let (_menhir_stack, _, _menhir_s, _, _) = _menhir_stack in
            _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s) : 'freshtv230)) : 'freshtv232)
    | MenhirState67 ->
        let (_menhir_env : _menhir_env) = _menhir_env in
        let (_menhir_stack : (('freshtv237 * Lexing.position * _menhir_state * 'tv_expr * Lexing.position)) * Lexing.position * _menhir_state * 'tv_expr * Lexing.position) = Obj.magic _menhir_stack in
        ((assert (not _menhir_env._menhir_error);
        let _tok = _menhir_env._menhir_token in
        match _tok with
        | ARROW ->
            _menhir_run65 _menhir_env (Obj.magic _menhir_stack)
        | AMPERSANDAMPERSAND | COMMA | COMP _ | EQOP _ | MINUS | PLUS | RPAR | SEMICOLON | SLASH | STAR | VERTICALBARVERTICALBAR ->
            let (_menhir_env : _menhir_env) = _menhir_env in
            let (_menhir_stack : (('freshtv233 * Lexing.position * _menhir_state * 'tv_expr * Lexing.position)) * Lexing.position * _menhir_state * 'tv_expr * Lexing.position) = Obj.magic _menhir_stack in
            ((let ((_menhir_stack, _endpos__1_, _menhir_s, (_1 : 'tv_expr), _startpos__1_), _endpos__3_, _, (_3 : 'tv_expr), _startpos__3_) = _menhir_stack in
            let _2 = () in
            let _startpos = _startpos__1_ in
            let _endpos = _endpos__3_ in
            let _v : 'tv_expr_node = 
# 132 "parser.mly"
    ( Ebinop (Bdiv, _1, _3) )
# 1447 "parser.ml"
             in
            _menhir_goto_expr_node _menhir_env _menhir_stack _endpos _menhir_s _v _startpos) : 'freshtv234)
        | _ ->
            assert (not _menhir_env._menhir_error);
            _menhir_env._menhir_error <- true;
            let (_menhir_env : _menhir_env) = _menhir_env in
            let (_menhir_stack : (('freshtv235 * Lexing.position * _menhir_state * 'tv_expr * Lexing.position)) * Lexing.position * _menhir_state * 'tv_expr * Lexing.position) = Obj.magic _menhir_stack in
            ((let (_menhir_stack, _, _menhir_s, _, _) = _menhir_stack in
            _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s) : 'freshtv236)) : 'freshtv238)
    | MenhirState69 ->
        let (_menhir_env : _menhir_env) = _menhir_env in
        let (_menhir_stack : (('freshtv243 * Lexing.position * _menhir_state * 'tv_expr * Lexing.position)) * Lexing.position * _menhir_state * 'tv_expr * Lexing.position) = Obj.magic _menhir_stack in
        ((assert (not _menhir_env._menhir_error);
        let _tok = _menhir_env._menhir_token in
        match _tok with
        | ARROW ->
            _menhir_run65 _menhir_env (Obj.magic _menhir_stack)
        | SLASH ->
            _menhir_run67 _menhir_env (Obj.magic _menhir_stack)
        | STAR ->
            _menhir_run63 _menhir_env (Obj.magic _menhir_stack)
        | AMPERSANDAMPERSAND | COMMA | COMP _ | EQOP _ | MINUS | PLUS | RPAR | SEMICOLON | VERTICALBARVERTICALBAR ->
            let (_menhir_env : _menhir_env) = _menhir_env in
            let (_menhir_stack : (('freshtv239 * Lexing.position * _menhir_state * 'tv_expr * Lexing.position)) * Lexing.position * _menhir_state * 'tv_expr * Lexing.position) = Obj.magic _menhir_stack in
            ((let ((_menhir_stack, _endpos__1_, _menhir_s, (_1 : 'tv_expr), _startpos__1_), _endpos__3_, _, (_3 : 'tv_expr), _startpos__3_) = _menhir_stack in
            let _2 = () in
            let _startpos = _startpos__1_ in
            let _endpos = _endpos__3_ in
            let _v : 'tv_expr_node = 
# 126 "parser.mly"
    ( Ebinop (Badd, _1, _3) )
# 1479 "parser.ml"
             in
            _menhir_goto_expr_node _menhir_env _menhir_stack _endpos _menhir_s _v _startpos) : 'freshtv240)
        | _ ->
            assert (not _menhir_env._menhir_error);
            _menhir_env._menhir_error <- true;
            let (_menhir_env : _menhir_env) = _menhir_env in
            let (_menhir_stack : (('freshtv241 * Lexing.position * _menhir_state * 'tv_expr * Lexing.position)) * Lexing.position * _menhir_state * 'tv_expr * Lexing.position) = Obj.magic _menhir_stack in
            ((let (_menhir_stack, _, _menhir_s, _, _) = _menhir_stack in
            _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s) : 'freshtv242)) : 'freshtv244)
    | MenhirState71 ->
        let (_menhir_env : _menhir_env) = _menhir_env in
        let (_menhir_stack : (('freshtv249 * Lexing.position * _menhir_state * 'tv_expr * Lexing.position) * Lexing.position) * Lexing.position * _menhir_state * 'tv_expr * Lexing.position) = Obj.magic _menhir_stack in
        ((assert (not _menhir_env._menhir_error);
        let _tok = _menhir_env._menhir_token in
        match _tok with
        | ARROW ->
            _menhir_run65 _menhir_env (Obj.magic _menhir_stack)
        | SLASH ->
            _menhir_run67 _menhir_env (Obj.magic _menhir_stack)
        | STAR ->
            _menhir_run63 _menhir_env (Obj.magic _menhir_stack)
        | AMPERSANDAMPERSAND | COMMA | COMP _ | EQOP _ | MINUS | PLUS | RPAR | SEMICOLON | VERTICALBARVERTICALBAR ->
            let (_menhir_env : _menhir_env) = _menhir_env in
            let (_menhir_stack : (('freshtv245 * Lexing.position * _menhir_state * 'tv_expr * Lexing.position) * Lexing.position) * Lexing.position * _menhir_state * 'tv_expr * Lexing.position) = Obj.magic _menhir_stack in
            ((let (((_menhir_stack, _endpos__1_, _menhir_s, (_1 : 'tv_expr), _startpos__1_), _startpos__2_), _endpos__3_, _, (_3 : 'tv_expr), _startpos__3_) = _menhir_stack in
            let _2 = () in
            let _startpos = _startpos__1_ in
            let _endpos = _endpos__3_ in
            let _v : 'tv_expr_node = 
# 128 "parser.mly"
    ( Ebinop (Bsub, _1, _3) )
# 1511 "parser.ml"
             in
            _menhir_goto_expr_node _menhir_env _menhir_stack _endpos _menhir_s _v _startpos) : 'freshtv246)
        | _ ->
            assert (not _menhir_env._menhir_error);
            _menhir_env._menhir_error <- true;
            let (_menhir_env : _menhir_env) = _menhir_env in
            let (_menhir_stack : (('freshtv247 * Lexing.position * _menhir_state * 'tv_expr * Lexing.position) * Lexing.position) * Lexing.position * _menhir_state * 'tv_expr * Lexing.position) = Obj.magic _menhir_stack in
            ((let (_menhir_stack, _, _menhir_s, _, _) = _menhir_stack in
            _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s) : 'freshtv248)) : 'freshtv250)
    | MenhirState73 ->
        let (_menhir_env : _menhir_env) = _menhir_env in
        let (_menhir_stack : (('freshtv255 * Lexing.position * _menhir_state * 'tv_expr * Lexing.position) * (
# 32 "parser.mly"
       (Ptree.binop)
# 1526 "parser.ml"
        )) * Lexing.position * _menhir_state * 'tv_expr * Lexing.position) = Obj.magic _menhir_stack in
        ((assert (not _menhir_env._menhir_error);
        let _tok = _menhir_env._menhir_token in
        match _tok with
        | ARROW ->
            _menhir_run65 _menhir_env (Obj.magic _menhir_stack)
        | COMP _v ->
            _menhir_run75 _menhir_env (Obj.magic _menhir_stack) _v
        | MINUS ->
            _menhir_run71 _menhir_env (Obj.magic _menhir_stack) _menhir_env._menhir_lexbuf.Lexing.lex_start_p
        | PLUS ->
            _menhir_run69 _menhir_env (Obj.magic _menhir_stack)
        | SLASH ->
            _menhir_run67 _menhir_env (Obj.magic _menhir_stack)
        | STAR ->
            _menhir_run63 _menhir_env (Obj.magic _menhir_stack)
        | AMPERSANDAMPERSAND | COMMA | EQOP _ | RPAR | SEMICOLON | VERTICALBARVERTICALBAR ->
            let (_menhir_env : _menhir_env) = _menhir_env in
            let (_menhir_stack : (('freshtv251 * Lexing.position * _menhir_state * 'tv_expr * Lexing.position) * (
# 32 "parser.mly"
       (Ptree.binop)
# 1548 "parser.ml"
            )) * Lexing.position * _menhir_state * 'tv_expr * Lexing.position) = Obj.magic _menhir_stack in
            ((let (((_menhir_stack, _endpos__1_, _menhir_s, (_1 : 'tv_expr), _startpos__1_), (_2 : (
# 32 "parser.mly"
       (Ptree.binop)
# 1553 "parser.ml"
            ))), _endpos__3_, _, (_3 : 'tv_expr), _startpos__3_) = _menhir_stack in
            let _startpos = _startpos__1_ in
            let _endpos = _endpos__3_ in
            let _v : 'tv_expr_node = 
# 122 "parser.mly"
    ( Ebinop (_2, _1, _3) )
# 1560 "parser.ml"
             in
            _menhir_goto_expr_node _menhir_env _menhir_stack _endpos _menhir_s _v _startpos) : 'freshtv252)
        | _ ->
            assert (not _menhir_env._menhir_error);
            _menhir_env._menhir_error <- true;
            let (_menhir_env : _menhir_env) = _menhir_env in
            let (_menhir_stack : (('freshtv253 * Lexing.position * _menhir_state * 'tv_expr * Lexing.position) * (
# 32 "parser.mly"
       (Ptree.binop)
# 1570 "parser.ml"
            )) * Lexing.position * _menhir_state * 'tv_expr * Lexing.position) = Obj.magic _menhir_stack in
            ((let (_menhir_stack, _, _menhir_s, _, _) = _menhir_stack in
            _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s) : 'freshtv254)) : 'freshtv256)
    | MenhirState75 ->
        let (_menhir_env : _menhir_env) = _menhir_env in
        let (_menhir_stack : (('freshtv261 * Lexing.position * _menhir_state * 'tv_expr * Lexing.position) * (
# 33 "parser.mly"
       (Ptree.binop)
# 1579 "parser.ml"
        )) * Lexing.position * _menhir_state * 'tv_expr * Lexing.position) = Obj.magic _menhir_stack in
        ((assert (not _menhir_env._menhir_error);
        let _tok = _menhir_env._menhir_token in
        match _tok with
        | ARROW ->
            _menhir_run65 _menhir_env (Obj.magic _menhir_stack)
        | MINUS ->
            _menhir_run71 _menhir_env (Obj.magic _menhir_stack) _menhir_env._menhir_lexbuf.Lexing.lex_start_p
        | PLUS ->
            _menhir_run69 _menhir_env (Obj.magic _menhir_stack)
        | SLASH ->
            _menhir_run67 _menhir_env (Obj.magic _menhir_stack)
        | STAR ->
            _menhir_run63 _menhir_env (Obj.magic _menhir_stack)
        | AMPERSANDAMPERSAND | COMMA | COMP _ | EQOP _ | RPAR | SEMICOLON | VERTICALBARVERTICALBAR ->
            let (_menhir_env : _menhir_env) = _menhir_env in
            let (_menhir_stack : (('freshtv257 * Lexing.position * _menhir_state * 'tv_expr * Lexing.position) * (
# 33 "parser.mly"
       (Ptree.binop)
# 1599 "parser.ml"
            )) * Lexing.position * _menhir_state * 'tv_expr * Lexing.position) = Obj.magic _menhir_stack in
            ((let (((_menhir_stack, _endpos__1_, _menhir_s, (_1 : 'tv_expr), _startpos__1_), (_2 : (
# 33 "parser.mly"
       (Ptree.binop)
# 1604 "parser.ml"
            ))), _endpos__3_, _, (_3 : 'tv_expr), _startpos__3_) = _menhir_stack in
            let _startpos = _startpos__1_ in
            let _endpos = _endpos__3_ in
            let _v : 'tv_expr_node = 
# 124 "parser.mly"
    ( Ebinop (_2, _1, _3) )
# 1611 "parser.ml"
             in
            _menhir_goto_expr_node _menhir_env _menhir_stack _endpos _menhir_s _v _startpos) : 'freshtv258)
        | _ ->
            assert (not _menhir_env._menhir_error);
            _menhir_env._menhir_error <- true;
            let (_menhir_env : _menhir_env) = _menhir_env in
            let (_menhir_stack : (('freshtv259 * Lexing.position * _menhir_state * 'tv_expr * Lexing.position) * (
# 33 "parser.mly"
       (Ptree.binop)
# 1621 "parser.ml"
            )) * Lexing.position * _menhir_state * 'tv_expr * Lexing.position) = Obj.magic _menhir_stack in
            ((let (_menhir_stack, _, _menhir_s, _, _) = _menhir_stack in
            _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s) : 'freshtv260)) : 'freshtv262)
    | MenhirState77 ->
        let (_menhir_env : _menhir_env) = _menhir_env in
        let (_menhir_stack : (('freshtv267 * Lexing.position * _menhir_state * 'tv_expr * Lexing.position)) * Lexing.position * _menhir_state * 'tv_expr * Lexing.position) = Obj.magic _menhir_stack in
        ((assert (not _menhir_env._menhir_error);
        let _tok = _menhir_env._menhir_token in
        match _tok with
        | ARROW ->
            _menhir_run65 _menhir_env (Obj.magic _menhir_stack)
        | COMP _v ->
            _menhir_run75 _menhir_env (Obj.magic _menhir_stack) _v
        | EQOP _v ->
            _menhir_run73 _menhir_env (Obj.magic _menhir_stack) _v
        | MINUS ->
            _menhir_run71 _menhir_env (Obj.magic _menhir_stack) _menhir_env._menhir_lexbuf.Lexing.lex_start_p
        | PLUS ->
            _menhir_run69 _menhir_env (Obj.magic _menhir_stack)
        | SLASH ->
            _menhir_run67 _menhir_env (Obj.magic _menhir_stack)
        | STAR ->
            _menhir_run63 _menhir_env (Obj.magic _menhir_stack)
        | AMPERSANDAMPERSAND | COMMA | RPAR | SEMICOLON | VERTICALBARVERTICALBAR ->
            let (_menhir_env : _menhir_env) = _menhir_env in
            let (_menhir_stack : (('freshtv263 * Lexing.position * _menhir_state * 'tv_expr * Lexing.position)) * Lexing.position * _menhir_state * 'tv_expr * Lexing.position) = Obj.magic _menhir_stack in
            ((let ((_menhir_stack, _endpos__1_, _menhir_s, (_1 : 'tv_expr), _startpos__1_), _endpos__3_, _, (_3 : 'tv_expr), _startpos__3_) = _menhir_stack in
            let _2 = () in
            let _startpos = _startpos__1_ in
            let _endpos = _endpos__3_ in
            let _v : 'tv_expr_node = 
# 120 "parser.mly"
    ( Ebinop (Band, _1, _3) )
# 1655 "parser.ml"
             in
            _menhir_goto_expr_node _menhir_env _menhir_stack _endpos _menhir_s _v _startpos) : 'freshtv264)
        | _ ->
            assert (not _menhir_env._menhir_error);
            _menhir_env._menhir_error <- true;
            let (_menhir_env : _menhir_env) = _menhir_env in
            let (_menhir_stack : (('freshtv265 * Lexing.position * _menhir_state * 'tv_expr * Lexing.position)) * Lexing.position * _menhir_state * 'tv_expr * Lexing.position) = Obj.magic _menhir_stack in
            ((let (_menhir_stack, _, _menhir_s, _, _) = _menhir_stack in
            _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s) : 'freshtv266)) : 'freshtv268)
    | MenhirState53 ->
        let (_menhir_env : _menhir_env) = _menhir_env in
        let (_menhir_stack : (('freshtv273 * Lexing.position * _menhir_state * 'tv_lvalue * Lexing.position)) * Lexing.position * _menhir_state * 'tv_expr * Lexing.position) = Obj.magic _menhir_stack in
        ((assert (not _menhir_env._menhir_error);
        let _tok = _menhir_env._menhir_token in
        match _tok with
        | AMPERSANDAMPERSAND ->
            _menhir_run77 _menhir_env (Obj.magic _menhir_stack)
        | ARROW ->
            _menhir_run65 _menhir_env (Obj.magic _menhir_stack)
        | COMP _v ->
            _menhir_run75 _menhir_env (Obj.magic _menhir_stack) _v
        | EQOP _v ->
            _menhir_run73 _menhir_env (Obj.magic _menhir_stack) _v
        | MINUS ->
            _menhir_run71 _menhir_env (Obj.magic _menhir_stack) _menhir_env._menhir_lexbuf.Lexing.lex_start_p
        | PLUS ->
            _menhir_run69 _menhir_env (Obj.magic _menhir_stack)
        | SLASH ->
            _menhir_run67 _menhir_env (Obj.magic _menhir_stack)
        | STAR ->
            _menhir_run63 _menhir_env (Obj.magic _menhir_stack)
        | VERTICALBARVERTICALBAR ->
            _menhir_run61 _menhir_env (Obj.magic _menhir_stack)
        | COMMA | RPAR | SEMICOLON ->
            let (_menhir_env : _menhir_env) = _menhir_env in
            let (_menhir_stack : (('freshtv269 * Lexing.position * _menhir_state * 'tv_lvalue * Lexing.position)) * Lexing.position * _menhir_state * 'tv_expr * Lexing.position) = Obj.magic _menhir_stack in
            ((let ((_menhir_stack, _endpos__1_, _menhir_s, (_1 : 'tv_lvalue), _startpos__1_), _endpos__3_, _, (_3 : 'tv_expr), _startpos__3_) = _menhir_stack in
            let _2 = () in
            let _startpos = _startpos__1_ in
            let _endpos = _endpos__3_ in
            let _v : 'tv_expr_node = 
# 116 "parser.mly"
    ( Eassign (_1, _3) )
# 1699 "parser.ml"
             in
            _menhir_goto_expr_node _menhir_env _menhir_stack _endpos _menhir_s _v _startpos) : 'freshtv270)
        | _ ->
            assert (not _menhir_env._menhir_error);
            _menhir_env._menhir_error <- true;
            let (_menhir_env : _menhir_env) = _menhir_env in
            let (_menhir_stack : (('freshtv271 * Lexing.position * _menhir_state * 'tv_lvalue * Lexing.position)) * Lexing.position * _menhir_state * 'tv_expr * Lexing.position) = Obj.magic _menhir_stack in
            ((let (_menhir_stack, _, _menhir_s, _, _) = _menhir_stack in
            _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s) : 'freshtv272)) : 'freshtv274)
    | MenhirState51 ->
        let (_menhir_env : _menhir_env) = _menhir_env in
        let (_menhir_stack : ('freshtv279 * _menhir_state * Lexing.position) * Lexing.position * _menhir_state * 'tv_expr * Lexing.position) = Obj.magic _menhir_stack in
        ((assert (not _menhir_env._menhir_error);
        let _tok = _menhir_env._menhir_token in
        match _tok with
        | ARROW ->
            _menhir_run65 _menhir_env (Obj.magic _menhir_stack)
        | AMPERSANDAMPERSAND | COMMA | COMP _ | EQOP _ | MINUS | PLUS | RPAR | SEMICOLON | SLASH | STAR | VERTICALBARVERTICALBAR ->
            let (_menhir_env : _menhir_env) = _menhir_env in
            let (_menhir_stack : ('freshtv275 * _menhir_state * Lexing.position) * Lexing.position * _menhir_state * 'tv_expr * Lexing.position) = Obj.magic _menhir_stack in
            ((let ((_menhir_stack, _menhir_s, _startpos__1_), _endpos__2_, _, (_2 : 'tv_expr), _startpos__2_) = _menhir_stack in
            let _1 = () in
            let _startpos = _startpos__1_ in
            let _endpos = _endpos__2_ in
            let _v : 'tv_expr_node = 
# 136 "parser.mly"
    ( Eunop (Unot, _2) )
# 1727 "parser.ml"
             in
            _menhir_goto_expr_node _menhir_env _menhir_stack _endpos _menhir_s _v _startpos) : 'freshtv276)
        | _ ->
            assert (not _menhir_env._menhir_error);
            _menhir_env._menhir_error <- true;
            let (_menhir_env : _menhir_env) = _menhir_env in
            let (_menhir_stack : ('freshtv277 * _menhir_state * Lexing.position) * Lexing.position * _menhir_state * 'tv_expr * Lexing.position) = Obj.magic _menhir_stack in
            ((let (_menhir_stack, _, _menhir_s, _, _) = _menhir_stack in
            _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s) : 'freshtv278)) : 'freshtv280)
    | MenhirState49 ->
        let (_menhir_env : _menhir_env) = _menhir_env in
        let (_menhir_stack : ('freshtv287 * _menhir_state * Lexing.position) * Lexing.position * _menhir_state * 'tv_expr * Lexing.position) = Obj.magic _menhir_stack in
        ((assert (not _menhir_env._menhir_error);
        let _tok = _menhir_env._menhir_token in
        match _tok with
        | AMPERSANDAMPERSAND ->
            _menhir_run77 _menhir_env (Obj.magic _menhir_stack)
        | ARROW ->
            _menhir_run65 _menhir_env (Obj.magic _menhir_stack)
        | COMP _v ->
            _menhir_run75 _menhir_env (Obj.magic _menhir_stack) _v
        | EQOP _v ->
            _menhir_run73 _menhir_env (Obj.magic _menhir_stack) _v
        | MINUS ->
            _menhir_run71 _menhir_env (Obj.magic _menhir_stack) _menhir_env._menhir_lexbuf.Lexing.lex_start_p
        | PLUS ->
            _menhir_run69 _menhir_env (Obj.magic _menhir_stack)
        | RPAR ->
            let (_menhir_env : _menhir_env) = _menhir_env in
            let (_menhir_stack : ('freshtv283 * _menhir_state * Lexing.position) * Lexing.position * _menhir_state * 'tv_expr * Lexing.position) = Obj.magic _menhir_stack in
            let (_endpos : Lexing.position) = _menhir_env._menhir_lexbuf.Lexing.lex_curr_p in
            ((let _menhir_env = _menhir_discard _menhir_env in
            let (_menhir_env : _menhir_env) = _menhir_env in
            let (_menhir_stack : ('freshtv281 * _menhir_state * Lexing.position) * Lexing.position * _menhir_state * 'tv_expr * Lexing.position) = Obj.magic _menhir_stack in
            let (_endpos__3_ : Lexing.position) = _endpos in
            ((let ((_menhir_stack, _menhir_s, _startpos__1_), _endpos__2_, _, (_2 : 'tv_expr), _startpos__2_) = _menhir_stack in
            let _3 = () in
            let _1 = () in
            let _startpos = _startpos__1_ in
            let _endpos = _endpos__3_ in
            let _v : 'tv_expr_node = 
# 142 "parser.mly"
    ( _2.expr_node )
# 1771 "parser.ml"
             in
            _menhir_goto_expr_node _menhir_env _menhir_stack _endpos _menhir_s _v _startpos) : 'freshtv282)) : 'freshtv284)
        | SLASH ->
            _menhir_run67 _menhir_env (Obj.magic _menhir_stack)
        | STAR ->
            _menhir_run63 _menhir_env (Obj.magic _menhir_stack)
        | VERTICALBARVERTICALBAR ->
            _menhir_run61 _menhir_env (Obj.magic _menhir_stack)
        | _ ->
            assert (not _menhir_env._menhir_error);
            _menhir_env._menhir_error <- true;
            let (_menhir_env : _menhir_env) = _menhir_env in
            let (_menhir_stack : ('freshtv285 * _menhir_state * Lexing.position) * Lexing.position * _menhir_state * 'tv_expr * Lexing.position) = Obj.magic _menhir_stack in
            ((let (_menhir_stack, _, _menhir_s, _, _) = _menhir_stack in
            _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s) : 'freshtv286)) : 'freshtv288)
    | MenhirState48 ->
        let (_menhir_env : _menhir_env) = _menhir_env in
        let (_menhir_stack : ('freshtv293 * _menhir_state * Lexing.position) * Lexing.position * _menhir_state * 'tv_expr * Lexing.position) = Obj.magic _menhir_stack in
        ((assert (not _menhir_env._menhir_error);
        let _tok = _menhir_env._menhir_token in
        match _tok with
        | ARROW ->
            _menhir_run65 _menhir_env (Obj.magic _menhir_stack)
        | AMPERSANDAMPERSAND | COMMA | COMP _ | EQOP _ | MINUS | PLUS | RPAR | SEMICOLON | SLASH | STAR | VERTICALBARVERTICALBAR ->
            let (_menhir_env : _menhir_env) = _menhir_env in
            let (_menhir_stack : ('freshtv289 * _menhir_state * Lexing.position) * Lexing.position * _menhir_state * 'tv_expr * Lexing.position) = Obj.magic _menhir_stack in
            ((let ((_menhir_stack, _menhir_s, _startpos__1_), _endpos__2_, _, (_2 : 'tv_expr), _startpos__2_) = _menhir_stack in
            let _1 = () in
            let _startpos = _startpos__1_ in
            let _endpos = _endpos__2_ in
            let _v : 'tv_expr_node = 
# 134 "parser.mly"
    ( Eunop (Uminus, _2) )
# 1805 "parser.ml"
             in
            _menhir_goto_expr_node _menhir_env _menhir_stack _endpos _menhir_s _v _startpos) : 'freshtv290)
        | _ ->
            assert (not _menhir_env._menhir_error);
            _menhir_env._menhir_error <- true;
            let (_menhir_env : _menhir_env) = _menhir_env in
            let (_menhir_stack : ('freshtv291 * _menhir_state * Lexing.position) * Lexing.position * _menhir_state * 'tv_expr * Lexing.position) = Obj.magic _menhir_stack in
            ((let (_menhir_stack, _, _menhir_s, _, _) = _menhir_stack in
            _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s) : 'freshtv292)) : 'freshtv294)
    | MenhirState42 ->
        let (_menhir_env : _menhir_env) = _menhir_env in
        let (_menhir_stack : (('freshtv299 * _menhir_state * Lexing.position) * Lexing.position) * Lexing.position * _menhir_state * 'tv_expr * Lexing.position) = Obj.magic _menhir_stack in
        ((assert (not _menhir_env._menhir_error);
        let _tok = _menhir_env._menhir_token in
        match _tok with
        | AMPERSANDAMPERSAND ->
            _menhir_run77 _menhir_env (Obj.magic _menhir_stack)
        | ARROW ->
            _menhir_run65 _menhir_env (Obj.magic _menhir_stack)
        | COMP _v ->
            _menhir_run75 _menhir_env (Obj.magic _menhir_stack) _v
        | EQOP _v ->
            _menhir_run73 _menhir_env (Obj.magic _menhir_stack) _v
        | MINUS ->
            _menhir_run71 _menhir_env (Obj.magic _menhir_stack) _menhir_env._menhir_lexbuf.Lexing.lex_start_p
        | PLUS ->
            _menhir_run69 _menhir_env (Obj.magic _menhir_stack)
        | RPAR ->
            let (_menhir_env : _menhir_env) = _menhir_env in
            let (_menhir_stack : (('freshtv295 * _menhir_state * Lexing.position) * Lexing.position) * Lexing.position * _menhir_state * 'tv_expr * Lexing.position) = Obj.magic _menhir_stack in
            let (_endpos : Lexing.position) = _menhir_env._menhir_lexbuf.Lexing.lex_curr_p in
            ((let _menhir_stack = (_menhir_stack, _endpos) in
            let _menhir_env = _menhir_discard _menhir_env in
            let _tok = _menhir_env._menhir_token in
            match _tok with
            | BANG ->
                _menhir_run51 _menhir_env (Obj.magic _menhir_stack) MenhirState87 _menhir_env._menhir_lexbuf.Lexing.lex_start_p
            | IDENT _v ->
                _menhir_run2 _menhir_env (Obj.magic _menhir_stack) _menhir_env._menhir_lexbuf.Lexing.lex_curr_p MenhirState87 _v _menhir_env._menhir_lexbuf.Lexing.lex_start_p
            | IF ->
                _menhir_run92 _menhir_env (Obj.magic _menhir_stack) MenhirState87 _menhir_env._menhir_lexbuf.Lexing.lex_start_p
            | INTEGER _v ->
                _menhir_run50 _menhir_env (Obj.magic _menhir_stack) _menhir_env._menhir_lexbuf.Lexing.lex_curr_p MenhirState87 _v _menhir_env._menhir_lexbuf.Lexing.lex_start_p
            | LBRACE ->
                _menhir_run39 _menhir_env (Obj.magic _menhir_stack) MenhirState87 _menhir_env._menhir_lexbuf.Lexing.lex_start_p
            | LPAR ->
                _menhir_run49 _menhir_env (Obj.magic _menhir_stack) MenhirState87 _menhir_env._menhir_lexbuf.Lexing.lex_start_p
            | MINUS ->
                _menhir_run48 _menhir_env (Obj.magic _menhir_stack) MenhirState87 _menhir_env._menhir_lexbuf.Lexing.lex_start_p
            | RETURN ->
                _menhir_run89 _menhir_env (Obj.magic _menhir_stack) MenhirState87 _menhir_env._menhir_lexbuf.Lexing.lex_start_p
            | SEMICOLON ->
                _menhir_run88 _menhir_env (Obj.magic _menhir_stack) _menhir_env._menhir_lexbuf.Lexing.lex_curr_p MenhirState87 _menhir_env._menhir_lexbuf.Lexing.lex_start_p
            | SIZEOF ->
                _menhir_run43 _menhir_env (Obj.magic _menhir_stack) MenhirState87 _menhir_env._menhir_lexbuf.Lexing.lex_start_p
            | WHILE ->
                _menhir_run41 _menhir_env (Obj.magic _menhir_stack) MenhirState87 _menhir_env._menhir_lexbuf.Lexing.lex_start_p
            | _ ->
                assert (not _menhir_env._menhir_error);
                _menhir_env._menhir_error <- true;
                _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) MenhirState87) : 'freshtv296)
        | SLASH ->
            _menhir_run67 _menhir_env (Obj.magic _menhir_stack)
        | STAR ->
            _menhir_run63 _menhir_env (Obj.magic _menhir_stack)
        | VERTICALBARVERTICALBAR ->
            _menhir_run61 _menhir_env (Obj.magic _menhir_stack)
        | _ ->
            assert (not _menhir_env._menhir_error);
            _menhir_env._menhir_error <- true;
            let (_menhir_env : _menhir_env) = _menhir_env in
            let (_menhir_stack : (('freshtv297 * _menhir_state * Lexing.position) * Lexing.position) * Lexing.position * _menhir_state * 'tv_expr * Lexing.position) = Obj.magic _menhir_stack in
            ((let (_menhir_stack, _, _menhir_s, _, _) = _menhir_stack in
            _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s) : 'freshtv298)) : 'freshtv300)
    | MenhirState89 ->
        let (_menhir_env : _menhir_env) = _menhir_env in
        let (_menhir_stack : ('freshtv307 * _menhir_state * Lexing.position) * Lexing.position * _menhir_state * 'tv_expr * Lexing.position) = Obj.magic _menhir_stack in
        ((assert (not _menhir_env._menhir_error);
        let _tok = _menhir_env._menhir_token in
        match _tok with
        | AMPERSANDAMPERSAND ->
            _menhir_run77 _menhir_env (Obj.magic _menhir_stack)
        | ARROW ->
            _menhir_run65 _menhir_env (Obj.magic _menhir_stack)
        | COMP _v ->
            _menhir_run75 _menhir_env (Obj.magic _menhir_stack) _v
        | EQOP _v ->
            _menhir_run73 _menhir_env (Obj.magic _menhir_stack) _v
        | MINUS ->
            _menhir_run71 _menhir_env (Obj.magic _menhir_stack) _menhir_env._menhir_lexbuf.Lexing.lex_start_p
        | PLUS ->
            _menhir_run69 _menhir_env (Obj.magic _menhir_stack)
        | SEMICOLON ->
            let (_menhir_env : _menhir_env) = _menhir_env in
            let (_menhir_stack : ('freshtv303 * _menhir_state * Lexing.position) * Lexing.position * _menhir_state * 'tv_expr * Lexing.position) = Obj.magic _menhir_stack in
            let (_endpos : Lexing.position) = _menhir_env._menhir_lexbuf.Lexing.lex_curr_p in
            let (_startpos : Lexing.position) = _menhir_env._menhir_lexbuf.Lexing.lex_start_p in
            ((let _menhir_env = _menhir_discard _menhir_env in
            let (_menhir_env : _menhir_env) = _menhir_env in
            let (_menhir_stack : ('freshtv301 * _menhir_state * Lexing.position) * Lexing.position * _menhir_state * 'tv_expr * Lexing.position) = Obj.magic _menhir_stack in
            let (_endpos__3_ : Lexing.position) = _endpos in
            let (_startpos__3_ : Lexing.position) = _startpos in
            ((let ((_menhir_stack, _menhir_s, _startpos__1_), _endpos__2_, _, (_2 : 'tv_expr), _startpos__2_) = _menhir_stack in
            let _3 = () in
            let _1 = () in
            let _startpos = _startpos__1_ in
            let _endpos = _endpos__3_ in
            let _v : 'tv_stmt_node = 
# 166 "parser.mly"
   ( Sreturn _2 )
# 1916 "parser.ml"
             in
            _menhir_goto_stmt_node _menhir_env _menhir_stack _endpos _menhir_s _v _startpos) : 'freshtv302)) : 'freshtv304)
        | SLASH ->
            _menhir_run67 _menhir_env (Obj.magic _menhir_stack)
        | STAR ->
            _menhir_run63 _menhir_env (Obj.magic _menhir_stack)
        | VERTICALBARVERTICALBAR ->
            _menhir_run61 _menhir_env (Obj.magic _menhir_stack)
        | _ ->
            assert (not _menhir_env._menhir_error);
            _menhir_env._menhir_error <- true;
            let (_menhir_env : _menhir_env) = _menhir_env in
            let (_menhir_stack : ('freshtv305 * _menhir_state * Lexing.position) * Lexing.position * _menhir_state * 'tv_expr * Lexing.position) = Obj.magic _menhir_stack in
            ((let (_menhir_stack, _, _menhir_s, _, _) = _menhir_stack in
            _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s) : 'freshtv306)) : 'freshtv308)
    | MenhirState93 ->
        let (_menhir_env : _menhir_env) = _menhir_env in
        let (_menhir_stack : (('freshtv313 * _menhir_state * Lexing.position) * Lexing.position) * Lexing.position * _menhir_state * 'tv_expr * Lexing.position) = Obj.magic _menhir_stack in
        ((assert (not _menhir_env._menhir_error);
        let _tok = _menhir_env._menhir_token in
        match _tok with
        | AMPERSANDAMPERSAND ->
            _menhir_run77 _menhir_env (Obj.magic _menhir_stack)
        | ARROW ->
            _menhir_run65 _menhir_env (Obj.magic _menhir_stack)
        | COMP _v ->
            _menhir_run75 _menhir_env (Obj.magic _menhir_stack) _v
        | EQOP _v ->
            _menhir_run73 _menhir_env (Obj.magic _menhir_stack) _v
        | MINUS ->
            _menhir_run71 _menhir_env (Obj.magic _menhir_stack) _menhir_env._menhir_lexbuf.Lexing.lex_start_p
        | PLUS ->
            _menhir_run69 _menhir_env (Obj.magic _menhir_stack)
        | RPAR ->
            let (_menhir_env : _menhir_env) = _menhir_env in
            let (_menhir_stack : (('freshtv309 * _menhir_state * Lexing.position) * Lexing.position) * Lexing.position * _menhir_state * 'tv_expr * Lexing.position) = Obj.magic _menhir_stack in
            let (_endpos : Lexing.position) = _menhir_env._menhir_lexbuf.Lexing.lex_curr_p in
            ((let _menhir_stack = (_menhir_stack, _endpos) in
            let _menhir_env = _menhir_discard _menhir_env in
            let _tok = _menhir_env._menhir_token in
            match _tok with
            | BANG ->
                _menhir_run51 _menhir_env (Obj.magic _menhir_stack) MenhirState95 _menhir_env._menhir_lexbuf.Lexing.lex_start_p
            | IDENT _v ->
                _menhir_run2 _menhir_env (Obj.magic _menhir_stack) _menhir_env._menhir_lexbuf.Lexing.lex_curr_p MenhirState95 _v _menhir_env._menhir_lexbuf.Lexing.lex_start_p
            | IF ->
                _menhir_run92 _menhir_env (Obj.magic _menhir_stack) MenhirState95 _menhir_env._menhir_lexbuf.Lexing.lex_start_p
            | INTEGER _v ->
                _menhir_run50 _menhir_env (Obj.magic _menhir_stack) _menhir_env._menhir_lexbuf.Lexing.lex_curr_p MenhirState95 _v _menhir_env._menhir_lexbuf.Lexing.lex_start_p
            | LBRACE ->
                _menhir_run39 _menhir_env (Obj.magic _menhir_stack) MenhirState95 _menhir_env._menhir_lexbuf.Lexing.lex_start_p
            | LPAR ->
                _menhir_run49 _menhir_env (Obj.magic _menhir_stack) MenhirState95 _menhir_env._menhir_lexbuf.Lexing.lex_start_p
            | MINUS ->
                _menhir_run48 _menhir_env (Obj.magic _menhir_stack) MenhirState95 _menhir_env._menhir_lexbuf.Lexing.lex_start_p
            | RETURN ->
                _menhir_run89 _menhir_env (Obj.magic _menhir_stack) MenhirState95 _menhir_env._menhir_lexbuf.Lexing.lex_start_p
            | SEMICOLON ->
                _menhir_run88 _menhir_env (Obj.magic _menhir_stack) _menhir_env._menhir_lexbuf.Lexing.lex_curr_p MenhirState95 _menhir_env._menhir_lexbuf.Lexing.lex_start_p
            | SIZEOF ->
                _menhir_run43 _menhir_env (Obj.magic _menhir_stack) MenhirState95 _menhir_env._menhir_lexbuf.Lexing.lex_start_p
            | WHILE ->
                _menhir_run41 _menhir_env (Obj.magic _menhir_stack) MenhirState95 _menhir_env._menhir_lexbuf.Lexing.lex_start_p
            | _ ->
                assert (not _menhir_env._menhir_error);
                _menhir_env._menhir_error <- true;
                _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) MenhirState95) : 'freshtv310)
        | SLASH ->
            _menhir_run67 _menhir_env (Obj.magic _menhir_stack)
        | STAR ->
            _menhir_run63 _menhir_env (Obj.magic _menhir_stack)
        | VERTICALBARVERTICALBAR ->
            _menhir_run61 _menhir_env (Obj.magic _menhir_stack)
        | _ ->
            assert (not _menhir_env._menhir_error);
            _menhir_env._menhir_error <- true;
            let (_menhir_env : _menhir_env) = _menhir_env in
            let (_menhir_stack : (('freshtv311 * _menhir_state * Lexing.position) * Lexing.position) * Lexing.position * _menhir_state * 'tv_expr * Lexing.position) = Obj.magic _menhir_stack in
            ((let (_menhir_stack, _, _menhir_s, _, _) = _menhir_stack in
            _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s) : 'freshtv312)) : 'freshtv314)
    | MenhirState40 | MenhirState104 | MenhirState87 | MenhirState95 | MenhirState98 ->
        let (_menhir_env : _menhir_env) = _menhir_env in
        let (_menhir_stack : 'freshtv321 * Lexing.position * _menhir_state * 'tv_expr * Lexing.position) = Obj.magic _menhir_stack in
        ((assert (not _menhir_env._menhir_error);
        let _tok = _menhir_env._menhir_token in
        match _tok with
        | AMPERSANDAMPERSAND ->
            _menhir_run77 _menhir_env (Obj.magic _menhir_stack)
        | ARROW ->
            _menhir_run65 _menhir_env (Obj.magic _menhir_stack)
        | COMP _v ->
            _menhir_run75 _menhir_env (Obj.magic _menhir_stack) _v
        | EQOP _v ->
            _menhir_run73 _menhir_env (Obj.magic _menhir_stack) _v
        | MINUS ->
            _menhir_run71 _menhir_env (Obj.magic _menhir_stack) _menhir_env._menhir_lexbuf.Lexing.lex_start_p
        | PLUS ->
            _menhir_run69 _menhir_env (Obj.magic _menhir_stack)
        | SEMICOLON ->
            let (_menhir_env : _menhir_env) = _menhir_env in
            let (_menhir_stack : 'freshtv317 * Lexing.position * _menhir_state * 'tv_expr * Lexing.position) = Obj.magic _menhir_stack in
            let (_endpos : Lexing.position) = _menhir_env._menhir_lexbuf.Lexing.lex_curr_p in
            let (_startpos : Lexing.position) = _menhir_env._menhir_lexbuf.Lexing.lex_start_p in
            ((let _menhir_env = _menhir_discard _menhir_env in
            let (_menhir_env : _menhir_env) = _menhir_env in
            let (_menhir_stack : 'freshtv315 * Lexing.position * _menhir_state * 'tv_expr * Lexing.position) = Obj.magic _menhir_stack in
            let (_endpos__2_ : Lexing.position) = _endpos in
            let (_startpos__2_ : Lexing.position) = _startpos in
            ((let (_menhir_stack, _endpos__1_, _menhir_s, (_1 : 'tv_expr), _startpos__1_) = _menhir_stack in
            let _2 = () in
            let _startpos = _startpos__1_ in
            let _endpos = _endpos__2_ in
            let _v : 'tv_stmt_node = 
# 156 "parser.mly"
   ( Sexpr _1 )
# 2032 "parser.ml"
             in
            _menhir_goto_stmt_node _menhir_env _menhir_stack _endpos _menhir_s _v _startpos) : 'freshtv316)) : 'freshtv318)
        | SLASH ->
            _menhir_run67 _menhir_env (Obj.magic _menhir_stack)
        | STAR ->
            _menhir_run63 _menhir_env (Obj.magic _menhir_stack)
        | VERTICALBARVERTICALBAR ->
            _menhir_run61 _menhir_env (Obj.magic _menhir_stack)
        | _ ->
            assert (not _menhir_env._menhir_error);
            _menhir_env._menhir_error <- true;
            let (_menhir_env : _menhir_env) = _menhir_env in
            let (_menhir_stack : 'freshtv319 * Lexing.position * _menhir_state * 'tv_expr * Lexing.position) = Obj.magic _menhir_stack in
            ((let (_menhir_stack, _, _menhir_s, _, _) = _menhir_stack in
            _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s) : 'freshtv320)) : 'freshtv322)
    | _ ->
        _menhir_fail ()) : 'freshtv324)) : 'freshtv326)) : 'freshtv328)

and _menhir_goto_separated_nonempty_list_COMMA_ident_ : _menhir_env -> 'ttv_tail -> _menhir_state -> 'tv_separated_nonempty_list_COMMA_ident_ -> 'ttv_return =
  fun _menhir_env _menhir_stack _menhir_s _v ->
    let _menhir_stack = (_menhir_stack, _menhir_s, _v) in
    match _menhir_s with
    | MenhirState16 ->
        let (_menhir_env : _menhir_env) = _menhir_env in
        let (_menhir_stack : ('freshtv207 * _menhir_state) * _menhir_state * 'tv_separated_nonempty_list_COMMA_ident_) = Obj.magic _menhir_stack in
        ((assert (not _menhir_env._menhir_error);
        let _tok = _menhir_env._menhir_token in
        match _tok with
        | SEMICOLON ->
            let (_menhir_env : _menhir_env) = _menhir_env in
            let (_menhir_stack : ('freshtv203 * _menhir_state) * _menhir_state * 'tv_separated_nonempty_list_COMMA_ident_) = Obj.magic _menhir_stack in
            let (_endpos : Lexing.position) = _menhir_env._menhir_lexbuf.Lexing.lex_curr_p in
            let (_startpos : Lexing.position) = _menhir_env._menhir_lexbuf.Lexing.lex_start_p in
            ((let _menhir_env = _menhir_discard _menhir_env in
            let (_menhir_env : _menhir_env) = _menhir_env in
            let (_menhir_stack : ('freshtv201 * _menhir_state) * _menhir_state * 'tv_separated_nonempty_list_COMMA_ident_) = Obj.magic _menhir_stack in
            let (_endpos__3_ : Lexing.position) = _endpos in
            let (_startpos__3_ : Lexing.position) = _startpos in
            ((let ((_menhir_stack, _menhir_s), _, (vl : 'tv_separated_nonempty_list_COMMA_ident_)) = _menhir_stack in
            let _3 = () in
            let _1 = () in
            let _v : 'tv_decl_var = 
# 73 "parser.mly"
    ( List.map (fun x -> (Tint, x)) vl )
# 2077 "parser.ml"
             in
            _menhir_goto_decl_var _menhir_env _menhir_stack _menhir_s _v) : 'freshtv202)) : 'freshtv204)
        | _ ->
            assert (not _menhir_env._menhir_error);
            _menhir_env._menhir_error <- true;
            let (_menhir_env : _menhir_env) = _menhir_env in
            let (_menhir_stack : ('freshtv205 * _menhir_state) * _menhir_state * 'tv_separated_nonempty_list_COMMA_ident_) = Obj.magic _menhir_stack in
            ((let (_menhir_stack, _menhir_s, _) = _menhir_stack in
            _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s) : 'freshtv206)) : 'freshtv208)
    | MenhirState20 ->
        let (_menhir_env : _menhir_env) = _menhir_env in
        let (_menhir_stack : (('freshtv211 * Lexing.position * _menhir_state * 'tv_ident * Lexing.position)) * _menhir_state * 'tv_separated_nonempty_list_COMMA_ident_) = Obj.magic _menhir_stack in
        ((let (_menhir_env : _menhir_env) = _menhir_env in
        let (_menhir_stack : (('freshtv209 * Lexing.position * _menhir_state * 'tv_ident * Lexing.position)) * _menhir_state * 'tv_separated_nonempty_list_COMMA_ident_) = Obj.magic _menhir_stack in
        ((let ((_menhir_stack, _endpos_x_, _menhir_s, (x : 'tv_ident), _startpos_x_), _, (xs : 'tv_separated_nonempty_list_COMMA_ident_)) = _menhir_stack in
        let _2 = () in
        let _v : 'tv_separated_nonempty_list_COMMA_ident_ = 
# 243 "/home/jc/.opam/4.07.1/lib/menhir/standard.mly"
    ( x :: xs )
# 2097 "parser.ml"
         in
        _menhir_goto_separated_nonempty_list_COMMA_ident_ _menhir_env _menhir_stack _menhir_s _v) : 'freshtv210)) : 'freshtv212)
    | _ ->
        _menhir_fail ()

and _menhir_goto_separated_nonempty_list_COMMA_star_ident_ : _menhir_env -> 'ttv_tail -> _menhir_state -> 'tv_separated_nonempty_list_COMMA_star_ident_ -> 'ttv_return =
  fun _menhir_env _menhir_stack _menhir_s _v ->
    let _menhir_stack = (_menhir_stack, _menhir_s, _v) in
    match _menhir_s with
    | MenhirState12 ->
        let (_menhir_env : _menhir_env) = _menhir_env in
        let (_menhir_stack : (('freshtv191 * _menhir_state * 'tv_star_ident)) * _menhir_state * 'tv_separated_nonempty_list_COMMA_star_ident_) = Obj.magic _menhir_stack in
        ((let (_menhir_env : _menhir_env) = _menhir_env in
        let (_menhir_stack : (('freshtv189 * _menhir_state * 'tv_star_ident)) * _menhir_state * 'tv_separated_nonempty_list_COMMA_star_ident_) = Obj.magic _menhir_stack in
        ((let ((_menhir_stack, _menhir_s, (x : 'tv_star_ident)), _, (xs : 'tv_separated_nonempty_list_COMMA_star_ident_)) = _menhir_stack in
        let _2 = () in
        let _v : 'tv_separated_nonempty_list_COMMA_star_ident_ = 
# 243 "/home/jc/.opam/4.07.1/lib/menhir/standard.mly"
    ( x :: xs )
# 2117 "parser.ml"
         in
        _menhir_goto_separated_nonempty_list_COMMA_star_ident_ _menhir_env _menhir_stack _menhir_s _v) : 'freshtv190)) : 'freshtv192)
    | MenhirState8 ->
        let (_menhir_env : _menhir_env) = _menhir_env in
        let (_menhir_stack : (('freshtv199 * _menhir_state) * Lexing.position * _menhir_state * 'tv_ident * Lexing.position) * _menhir_state * 'tv_separated_nonempty_list_COMMA_star_ident_) = Obj.magic _menhir_stack in
        ((assert (not _menhir_env._menhir_error);
        let _tok = _menhir_env._menhir_token in
        match _tok with
        | SEMICOLON ->
            let (_menhir_env : _menhir_env) = _menhir_env in
            let (_menhir_stack : (('freshtv195 * _menhir_state) * Lexing.position * _menhir_state * 'tv_ident * Lexing.position) * _menhir_state * 'tv_separated_nonempty_list_COMMA_star_ident_) = Obj.magic _menhir_stack in
            let (_endpos : Lexing.position) = _menhir_env._menhir_lexbuf.Lexing.lex_curr_p in
            let (_startpos : Lexing.position) = _menhir_env._menhir_lexbuf.Lexing.lex_start_p in
            ((let _menhir_env = _menhir_discard _menhir_env in
            let (_menhir_env : _menhir_env) = _menhir_env in
            let (_menhir_stack : (('freshtv193 * _menhir_state) * Lexing.position * _menhir_state * 'tv_ident * Lexing.position) * _menhir_state * 'tv_separated_nonempty_list_COMMA_star_ident_) = Obj.magic _menhir_stack in
            let (_endpos__4_ : Lexing.position) = _endpos in
            let (_startpos__4_ : Lexing.position) = _startpos in
            ((let (((_menhir_stack, _menhir_s), _endpos_s_, _, (s : 'tv_ident), _startpos_s_), _, (vl : 'tv_separated_nonempty_list_COMMA_star_ident_)) = _menhir_stack in
            let _4 = () in
            let _1 = () in
            let _v : 'tv_decl_var = 
# 75 "parser.mly"
    ( let ty = Tstructp s in List.map (fun x -> (ty, x)) vl )
# 2142 "parser.ml"
             in
            _menhir_goto_decl_var _menhir_env _menhir_stack _menhir_s _v) : 'freshtv194)) : 'freshtv196)
        | _ ->
            assert (not _menhir_env._menhir_error);
            _menhir_env._menhir_error <- true;
            let (_menhir_env : _menhir_env) = _menhir_env in
            let (_menhir_stack : (('freshtv197 * _menhir_state) * Lexing.position * _menhir_state * 'tv_ident * Lexing.position) * _menhir_state * 'tv_separated_nonempty_list_COMMA_star_ident_) = Obj.magic _menhir_stack in
            ((let (_menhir_stack, _menhir_s, _) = _menhir_stack in
            _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s) : 'freshtv198)) : 'freshtv200)
    | _ ->
        _menhir_fail ()

and _menhir_run9 : _menhir_env -> 'ttv_tail -> _menhir_state -> 'ttv_return =
  fun _menhir_env _menhir_stack _menhir_s ->
    let _menhir_stack = (_menhir_stack, _menhir_s) in
    let _menhir_env = _menhir_discard _menhir_env in
    let _tok = _menhir_env._menhir_token in
    match _tok with
    | IDENT _v ->
        _menhir_run2 _menhir_env (Obj.magic _menhir_stack) _menhir_env._menhir_lexbuf.Lexing.lex_curr_p MenhirState9 _v _menhir_env._menhir_lexbuf.Lexing.lex_start_p
    | _ ->
        assert (not _menhir_env._menhir_error);
        _menhir_env._menhir_error <- true;
        _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) MenhirState9

and _menhir_goto_formal : _menhir_env -> 'ttv_tail -> _menhir_state -> 'tv_formal -> 'ttv_return =
  fun _menhir_env _menhir_stack _menhir_s _v ->
    let _menhir_stack = (_menhir_stack, _menhir_s, _v) in
    match _menhir_s with
    | MenhirState114 | MenhirState0 ->
        let (_menhir_env : _menhir_env) = _menhir_env in
        let (_menhir_stack : 'freshtv179 * _menhir_state * 'tv_formal) = Obj.magic _menhir_stack in
        ((assert (not _menhir_env._menhir_error);
        let _tok = _menhir_env._menhir_token in
        match _tok with
        | LPAR ->
            let (_menhir_env : _menhir_env) = _menhir_env in
            let (_menhir_stack : 'freshtv175 * _menhir_state * 'tv_formal) = Obj.magic _menhir_stack in
            let (_startpos : Lexing.position) = _menhir_env._menhir_lexbuf.Lexing.lex_start_p in
            ((let _menhir_stack = (_menhir_stack, _startpos) in
            let _menhir_env = _menhir_discard _menhir_env in
            let _tok = _menhir_env._menhir_token in
            match _tok with
            | INT ->
                _menhir_run27 _menhir_env (Obj.magic _menhir_stack) MenhirState32
            | STRUCT ->
                _menhir_run33 _menhir_env (Obj.magic _menhir_stack) MenhirState32
            | RPAR ->
                let (_menhir_env : _menhir_env) = _menhir_env in
                let (_menhir_stack : 'freshtv173) = Obj.magic _menhir_stack in
                let (_menhir_s : _menhir_state) = MenhirState32 in
                ((let _v : 'tv_loption_separated_nonempty_list_COMMA_formal__ = 
# 142 "/home/jc/.opam/4.07.1/lib/menhir/standard.mly"
    ( [] )
# 2197 "parser.ml"
                 in
                _menhir_goto_loption_separated_nonempty_list_COMMA_formal__ _menhir_env _menhir_stack _menhir_s _v) : 'freshtv174)
            | _ ->
                assert (not _menhir_env._menhir_error);
                _menhir_env._menhir_error <- true;
                _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) MenhirState32) : 'freshtv176)
        | _ ->
            assert (not _menhir_env._menhir_error);
            _menhir_env._menhir_error <- true;
            let (_menhir_env : _menhir_env) = _menhir_env in
            let (_menhir_stack : 'freshtv177 * _menhir_state * 'tv_formal) = Obj.magic _menhir_stack in
            ((let (_menhir_stack, _menhir_s, _) = _menhir_stack in
            _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s) : 'freshtv178)) : 'freshtv180)
    | MenhirState110 | MenhirState32 ->
        let (_menhir_env : _menhir_env) = _menhir_env in
        let (_menhir_stack : 'freshtv187 * _menhir_state * 'tv_formal) = Obj.magic _menhir_stack in
        ((assert (not _menhir_env._menhir_error);
        let _tok = _menhir_env._menhir_token in
        match _tok with
        | COMMA ->
            let (_menhir_env : _menhir_env) = _menhir_env in
            let (_menhir_stack : 'freshtv181 * _menhir_state * 'tv_formal) = Obj.magic _menhir_stack in
            ((let _menhir_env = _menhir_discard _menhir_env in
            let _tok = _menhir_env._menhir_token in
            match _tok with
            | INT ->
                _menhir_run27 _menhir_env (Obj.magic _menhir_stack) MenhirState110
            | STRUCT ->
                _menhir_run33 _menhir_env (Obj.magic _menhir_stack) MenhirState110
            | _ ->
                assert (not _menhir_env._menhir_error);
                _menhir_env._menhir_error <- true;
                _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) MenhirState110) : 'freshtv182)
        | RPAR ->
            let (_menhir_env : _menhir_env) = _menhir_env in
            let (_menhir_stack : 'freshtv183 * _menhir_state * 'tv_formal) = Obj.magic _menhir_stack in
            ((let (_menhir_stack, _menhir_s, (x : 'tv_formal)) = _menhir_stack in
            let _v : 'tv_separated_nonempty_list_COMMA_formal_ = 
# 241 "/home/jc/.opam/4.07.1/lib/menhir/standard.mly"
    ( [ x ] )
# 2238 "parser.ml"
             in
            _menhir_goto_separated_nonempty_list_COMMA_formal_ _menhir_env _menhir_stack _menhir_s _v) : 'freshtv184)
        | _ ->
            assert (not _menhir_env._menhir_error);
            _menhir_env._menhir_error <- true;
            let (_menhir_env : _menhir_env) = _menhir_env in
            let (_menhir_stack : 'freshtv185 * _menhir_state * 'tv_formal) = Obj.magic _menhir_stack in
            ((let (_menhir_stack, _menhir_s, _) = _menhir_stack in
            _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s) : 'freshtv186)) : 'freshtv188)
    | _ ->
        _menhir_fail ()

and _menhir_run4 : _menhir_env -> ('ttv_tail * _menhir_state) * Lexing.position * _menhir_state * 'tv_ident * Lexing.position -> 'ttv_return =
  fun _menhir_env _menhir_stack ->
    let _menhir_env = _menhir_discard _menhir_env in
    let _tok = _menhir_env._menhir_token in
    match _tok with
    | IDENT _v ->
        _menhir_run2 _menhir_env (Obj.magic _menhir_stack) _menhir_env._menhir_lexbuf.Lexing.lex_curr_p MenhirState4 _v _menhir_env._menhir_lexbuf.Lexing.lex_start_p
    | _ ->
        assert (not _menhir_env._menhir_error);
        _menhir_env._menhir_error <- true;
        _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) MenhirState4

and _menhir_reduce31 : _menhir_env -> 'ttv_tail -> _menhir_state -> 'ttv_return =
  fun _menhir_env _menhir_stack _menhir_s ->
    let _v : 'tv_list_decl_var_ = 
# 211 "/home/jc/.opam/4.07.1/lib/menhir/standard.mly"
    ( [] )
# 2268 "parser.ml"
     in
    _menhir_goto_list_decl_var_ _menhir_env _menhir_stack _menhir_s _v

and _menhir_run7 : _menhir_env -> 'ttv_tail -> _menhir_state -> 'ttv_return =
  fun _menhir_env _menhir_stack _menhir_s ->
    let _menhir_stack = (_menhir_stack, _menhir_s) in
    let _menhir_env = _menhir_discard _menhir_env in
    let _tok = _menhir_env._menhir_token in
    match _tok with
    | IDENT _v ->
        _menhir_run2 _menhir_env (Obj.magic _menhir_stack) _menhir_env._menhir_lexbuf.Lexing.lex_curr_p MenhirState7 _v _menhir_env._menhir_lexbuf.Lexing.lex_start_p
    | _ ->
        assert (not _menhir_env._menhir_error);
        _menhir_env._menhir_error <- true;
        _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) MenhirState7

and _menhir_run16 : _menhir_env -> 'ttv_tail -> _menhir_state -> 'ttv_return =
  fun _menhir_env _menhir_stack _menhir_s ->
    let _menhir_stack = (_menhir_stack, _menhir_s) in
    let _menhir_env = _menhir_discard _menhir_env in
    let _tok = _menhir_env._menhir_token in
    match _tok with
    | IDENT _v ->
        _menhir_run2 _menhir_env (Obj.magic _menhir_stack) _menhir_env._menhir_lexbuf.Lexing.lex_curr_p MenhirState16 _v _menhir_env._menhir_lexbuf.Lexing.lex_start_p
    | _ ->
        assert (not _menhir_env._menhir_error);
        _menhir_env._menhir_error <- true;
        _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) MenhirState16

and _menhir_goto_list_decl_ : _menhir_env -> 'ttv_tail -> _menhir_state -> 'tv_list_decl_ -> 'ttv_return =
  fun _menhir_env _menhir_stack _menhir_s _v ->
    let _menhir_stack = (_menhir_stack, _menhir_s, _v) in
    match _menhir_s with
    | MenhirState0 ->
        let (_menhir_env : _menhir_env) = _menhir_env in
        let (_menhir_stack : 'freshtv167 * _menhir_state * 'tv_list_decl_) = Obj.magic _menhir_stack in
        ((assert (not _menhir_env._menhir_error);
        let _tok = _menhir_env._menhir_token in
        match _tok with
        | EOF ->
            let (_menhir_env : _menhir_env) = _menhir_env in
            let (_menhir_stack : 'freshtv163 * _menhir_state * 'tv_list_decl_) = Obj.magic _menhir_stack in
            ((let (_menhir_env : _menhir_env) = _menhir_env in
            let (_menhir_stack : 'freshtv161 * _menhir_state * 'tv_list_decl_) = Obj.magic _menhir_stack in
            ((let (_menhir_stack, _menhir_s, (dl : 'tv_list_decl_)) = _menhir_stack in
            let _2 = () in
            let _v : (
# 56 "parser.mly"
      (Ptree.file)
# 2318 "parser.ml"
            ) = 
# 61 "parser.mly"
                       ( dl )
# 2322 "parser.ml"
             in
            let (_menhir_env : _menhir_env) = _menhir_env in
            let (_menhir_stack : 'freshtv159) = _menhir_stack in
            let (_menhir_s : _menhir_state) = _menhir_s in
            let (_v : (
# 56 "parser.mly"
      (Ptree.file)
# 2330 "parser.ml"
            )) = _v in
            ((let (_menhir_env : _menhir_env) = _menhir_env in
            let (_menhir_stack : 'freshtv157) = Obj.magic _menhir_stack in
            let (_menhir_s : _menhir_state) = _menhir_s in
            let (_v : (
# 56 "parser.mly"
      (Ptree.file)
# 2338 "parser.ml"
            )) = _v in
            ((let (_menhir_env : _menhir_env) = _menhir_env in
            let (_menhir_stack : 'freshtv155) = Obj.magic _menhir_stack in
            let (_menhir_s : _menhir_state) = _menhir_s in
            let ((_1 : (
# 56 "parser.mly"
      (Ptree.file)
# 2346 "parser.ml"
            )) : (
# 56 "parser.mly"
      (Ptree.file)
# 2350 "parser.ml"
            )) = _v in
            (Obj.magic _1 : 'freshtv156)) : 'freshtv158)) : 'freshtv160)) : 'freshtv162)) : 'freshtv164)
        | _ ->
            assert (not _menhir_env._menhir_error);
            _menhir_env._menhir_error <- true;
            let (_menhir_env : _menhir_env) = _menhir_env in
            let (_menhir_stack : 'freshtv165 * _menhir_state * 'tv_list_decl_) = Obj.magic _menhir_stack in
            ((let (_menhir_stack, _menhir_s, _) = _menhir_stack in
            _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s) : 'freshtv166)) : 'freshtv168)
    | MenhirState114 ->
        let (_menhir_env : _menhir_env) = _menhir_env in
        let (_menhir_stack : ('freshtv171 * _menhir_state * 'tv_decl) * _menhir_state * 'tv_list_decl_) = Obj.magic _menhir_stack in
        ((let (_menhir_env : _menhir_env) = _menhir_env in
        let (_menhir_stack : ('freshtv169 * _menhir_state * 'tv_decl) * _menhir_state * 'tv_list_decl_) = Obj.magic _menhir_stack in
        ((let ((_menhir_stack, _menhir_s, (x : 'tv_decl)), _, (xs : 'tv_list_decl_)) = _menhir_stack in
        let _v : 'tv_list_decl_ = 
# 213 "/home/jc/.opam/4.07.1/lib/menhir/standard.mly"
    ( x :: xs )
# 2369 "parser.ml"
         in
        _menhir_goto_list_decl_ _menhir_env _menhir_stack _menhir_s _v) : 'freshtv170)) : 'freshtv172)
    | _ ->
        _menhir_fail ()

and _menhir_run2 : _menhir_env -> 'ttv_tail -> Lexing.position -> _menhir_state -> (
# 13 "parser.mly"
       (string)
# 2378 "parser.ml"
) -> Lexing.position -> 'ttv_return =
  fun _menhir_env _menhir_stack _endpos _menhir_s _v _startpos ->
    let _menhir_env = _menhir_discard _menhir_env in
    let (_menhir_env : _menhir_env) = _menhir_env in
    let (_menhir_stack : 'freshtv153) = Obj.magic _menhir_stack in
    let (_endpos_id_ : Lexing.position) = _endpos in
    let (_menhir_s : _menhir_state) = _menhir_s in
    let ((id : (
# 13 "parser.mly"
       (string)
# 2389 "parser.ml"
    )) : (
# 13 "parser.mly"
       (string)
# 2393 "parser.ml"
    )) = _v in
    let (_startpos_id_ : Lexing.position) = _startpos in
    ((let _startpos = _startpos_id_ in
    let _endpos = _endpos_id_ in
    let _v : 'tv_ident = let _endpos = _endpos_id_ in
    let _startpos = _startpos_id_ in
    
# 174 "parser.mly"
             ( { id = id; id_loc = _startpos, _endpos } )
# 2403 "parser.ml"
     in
    let (_menhir_env : _menhir_env) = _menhir_env in
    let (_menhir_stack : 'freshtv151) = _menhir_stack in
    let (_endpos : Lexing.position) = _endpos in
    let (_menhir_s : _menhir_state) = _menhir_s in
    let (_v : 'tv_ident) = _v in
    let (_startpos : Lexing.position) = _startpos in
    ((let _menhir_stack = (_menhir_stack, _endpos, _menhir_s, _v, _startpos) in
    match _menhir_s with
    | MenhirState1 ->
        let (_menhir_env : _menhir_env) = _menhir_env in
        let (_menhir_stack : ('freshtv91 * _menhir_state) * Lexing.position * _menhir_state * 'tv_ident * Lexing.position) = Obj.magic _menhir_stack in
        ((assert (not _menhir_env._menhir_error);
        let _tok = _menhir_env._menhir_token in
        match _tok with
        | LBRACE ->
            let (_menhir_env : _menhir_env) = _menhir_env in
            let (_menhir_stack : ('freshtv87 * _menhir_state) * Lexing.position * _menhir_state * 'tv_ident * Lexing.position) = Obj.magic _menhir_stack in
            let (_startpos : Lexing.position) = _menhir_env._menhir_lexbuf.Lexing.lex_start_p in
            ((let _menhir_stack = (_menhir_stack, _startpos) in
            let _menhir_env = _menhir_discard _menhir_env in
            let _tok = _menhir_env._menhir_token in
            match _tok with
            | INT ->
                _menhir_run16 _menhir_env (Obj.magic _menhir_stack) MenhirState6
            | STRUCT ->
                _menhir_run7 _menhir_env (Obj.magic _menhir_stack) MenhirState6
            | RBRACE ->
                _menhir_reduce31 _menhir_env (Obj.magic _menhir_stack) MenhirState6
            | _ ->
                assert (not _menhir_env._menhir_error);
                _menhir_env._menhir_error <- true;
                _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) MenhirState6) : 'freshtv88)
        | STAR ->
            _menhir_run4 _menhir_env (Obj.magic _menhir_stack)
        | _ ->
            assert (not _menhir_env._menhir_error);
            _menhir_env._menhir_error <- true;
            let (_menhir_env : _menhir_env) = _menhir_env in
            let (_menhir_stack : ('freshtv89 * _menhir_state) * Lexing.position * _menhir_state * 'tv_ident * Lexing.position) = Obj.magic _menhir_stack in
            ((let (_menhir_stack, _, _menhir_s, _, _) = _menhir_stack in
            _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s) : 'freshtv90)) : 'freshtv92)
    | MenhirState4 ->
        let (_menhir_env : _menhir_env) = _menhir_env in
        let (_menhir_stack : ((('freshtv95 * _menhir_state) * Lexing.position * _menhir_state * 'tv_ident * Lexing.position)) * Lexing.position * _menhir_state * 'tv_ident * Lexing.position) = Obj.magic _menhir_stack in
        ((let (_menhir_env : _menhir_env) = _menhir_env in
        let (_menhir_stack : ((('freshtv93 * _menhir_state) * Lexing.position * _menhir_state * 'tv_ident * Lexing.position)) * Lexing.position * _menhir_state * 'tv_ident * Lexing.position) = Obj.magic _menhir_stack in
        ((let (((_menhir_stack, _menhir_s), _endpos_s_, _, (s : 'tv_ident), _startpos_s_), _endpos_id_, _, (id : 'tv_ident), _startpos_id_) = _menhir_stack in
        let _3 = () in
        let _1 = () in
        let _v : 'tv_formal = 
# 97 "parser.mly"
                                   ( Tstructp s, id )
# 2457 "parser.ml"
         in
        _menhir_goto_formal _menhir_env _menhir_stack _menhir_s _v) : 'freshtv94)) : 'freshtv96)
    | MenhirState7 ->
        let (_menhir_env : _menhir_env) = _menhir_env in
        let (_menhir_stack : ('freshtv97 * _menhir_state) * Lexing.position * _menhir_state * 'tv_ident * Lexing.position) = Obj.magic _menhir_stack in
        ((assert (not _menhir_env._menhir_error);
        let _tok = _menhir_env._menhir_token in
        match _tok with
        | STAR ->
            _menhir_run9 _menhir_env (Obj.magic _menhir_stack) MenhirState8
        | _ ->
            assert (not _menhir_env._menhir_error);
            _menhir_env._menhir_error <- true;
            _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) MenhirState8) : 'freshtv98)
    | MenhirState9 ->
        let (_menhir_env : _menhir_env) = _menhir_env in
        let (_menhir_stack : ('freshtv111 * _menhir_state) * Lexing.position * _menhir_state * 'tv_ident * Lexing.position) = Obj.magic _menhir_stack in
        ((let (_menhir_env : _menhir_env) = _menhir_env in
        let (_menhir_stack : ('freshtv109 * _menhir_state) * Lexing.position * _menhir_state * 'tv_ident * Lexing.position) = Obj.magic _menhir_stack in
        ((let ((_menhir_stack, _menhir_s), _endpos_id_, _, (id : 'tv_ident), _startpos_id_) = _menhir_stack in
        let _1 = () in
        let _v : 'tv_star_ident = 
# 79 "parser.mly"
                  ( id )
# 2482 "parser.ml"
         in
        let (_menhir_env : _menhir_env) = _menhir_env in
        let (_menhir_stack : 'freshtv107) = _menhir_stack in
        let (_menhir_s : _menhir_state) = _menhir_s in
        let (_v : 'tv_star_ident) = _v in
        ((let _menhir_stack = (_menhir_stack, _menhir_s, _v) in
        let (_menhir_env : _menhir_env) = _menhir_env in
        let (_menhir_stack : 'freshtv105 * _menhir_state * 'tv_star_ident) = Obj.magic _menhir_stack in
        ((assert (not _menhir_env._menhir_error);
        let _tok = _menhir_env._menhir_token in
        match _tok with
        | COMMA ->
            let (_menhir_env : _menhir_env) = _menhir_env in
            let (_menhir_stack : 'freshtv99 * _menhir_state * 'tv_star_ident) = Obj.magic _menhir_stack in
            ((let _menhir_env = _menhir_discard _menhir_env in
            let _tok = _menhir_env._menhir_token in
            match _tok with
            | STAR ->
                _menhir_run9 _menhir_env (Obj.magic _menhir_stack) MenhirState12
            | _ ->
                assert (not _menhir_env._menhir_error);
                _menhir_env._menhir_error <- true;
                _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) MenhirState12) : 'freshtv100)
        | SEMICOLON ->
            let (_menhir_env : _menhir_env) = _menhir_env in
            let (_menhir_stack : 'freshtv101 * _menhir_state * 'tv_star_ident) = Obj.magic _menhir_stack in
            ((let (_menhir_stack, _menhir_s, (x : 'tv_star_ident)) = _menhir_stack in
            let _v : 'tv_separated_nonempty_list_COMMA_star_ident_ = 
# 241 "/home/jc/.opam/4.07.1/lib/menhir/standard.mly"
    ( [ x ] )
# 2513 "parser.ml"
             in
            _menhir_goto_separated_nonempty_list_COMMA_star_ident_ _menhir_env _menhir_stack _menhir_s _v) : 'freshtv102)
        | _ ->
            assert (not _menhir_env._menhir_error);
            _menhir_env._menhir_error <- true;
            let (_menhir_env : _menhir_env) = _menhir_env in
            let (_menhir_stack : 'freshtv103 * _menhir_state * 'tv_star_ident) = Obj.magic _menhir_stack in
            ((let (_menhir_stack, _menhir_s, _) = _menhir_stack in
            _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s) : 'freshtv104)) : 'freshtv106)) : 'freshtv108)) : 'freshtv110)) : 'freshtv112)
    | MenhirState20 | MenhirState16 ->
        let (_menhir_env : _menhir_env) = _menhir_env in
        let (_menhir_stack : 'freshtv119 * Lexing.position * _menhir_state * 'tv_ident * Lexing.position) = Obj.magic _menhir_stack in
        ((assert (not _menhir_env._menhir_error);
        let _tok = _menhir_env._menhir_token in
        match _tok with
        | COMMA ->
            let (_menhir_env : _menhir_env) = _menhir_env in
            let (_menhir_stack : 'freshtv113 * Lexing.position * _menhir_state * 'tv_ident * Lexing.position) = Obj.magic _menhir_stack in
            ((let _menhir_env = _menhir_discard _menhir_env in
            let _tok = _menhir_env._menhir_token in
            match _tok with
            | IDENT _v ->
                _menhir_run2 _menhir_env (Obj.magic _menhir_stack) _menhir_env._menhir_lexbuf.Lexing.lex_curr_p MenhirState20 _v _menhir_env._menhir_lexbuf.Lexing.lex_start_p
            | _ ->
                assert (not _menhir_env._menhir_error);
                _menhir_env._menhir_error <- true;
                _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) MenhirState20) : 'freshtv114)
        | SEMICOLON ->
            let (_menhir_env : _menhir_env) = _menhir_env in
            let (_menhir_stack : 'freshtv115 * Lexing.position * _menhir_state * 'tv_ident * Lexing.position) = Obj.magic _menhir_stack in
            ((let (_menhir_stack, _endpos_x_, _menhir_s, (x : 'tv_ident), _startpos_x_) = _menhir_stack in
            let _v : 'tv_separated_nonempty_list_COMMA_ident_ = 
# 241 "/home/jc/.opam/4.07.1/lib/menhir/standard.mly"
    ( [ x ] )
# 2548 "parser.ml"
             in
            _menhir_goto_separated_nonempty_list_COMMA_ident_ _menhir_env _menhir_stack _menhir_s _v) : 'freshtv116)
        | _ ->
            assert (not _menhir_env._menhir_error);
            _menhir_env._menhir_error <- true;
            let (_menhir_env : _menhir_env) = _menhir_env in
            let (_menhir_stack : 'freshtv117 * Lexing.position * _menhir_state * 'tv_ident * Lexing.position) = Obj.magic _menhir_stack in
            ((let (_menhir_stack, _, _menhir_s, _, _) = _menhir_stack in
            _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s) : 'freshtv118)) : 'freshtv120)
    | MenhirState27 ->
        let (_menhir_env : _menhir_env) = _menhir_env in
        let (_menhir_stack : ('freshtv123 * _menhir_state) * Lexing.position * _menhir_state * 'tv_ident * Lexing.position) = Obj.magic _menhir_stack in
        ((let (_menhir_env : _menhir_env) = _menhir_env in
        let (_menhir_stack : ('freshtv121 * _menhir_state) * Lexing.position * _menhir_state * 'tv_ident * Lexing.position) = Obj.magic _menhir_stack in
        ((let ((_menhir_stack, _menhir_s), _endpos_id_, _, (id : 'tv_ident), _startpos_id_) = _menhir_stack in
        let _1 = () in
        let _v : 'tv_formal = 
# 96 "parser.mly"
                                   ( Tint,       id )
# 2568 "parser.ml"
         in
        _menhir_goto_formal _menhir_env _menhir_stack _menhir_s _v) : 'freshtv122)) : 'freshtv124)
    | MenhirState33 ->
        let (_menhir_env : _menhir_env) = _menhir_env in
        let (_menhir_stack : ('freshtv127 * _menhir_state) * Lexing.position * _menhir_state * 'tv_ident * Lexing.position) = Obj.magic _menhir_stack in
        ((assert (not _menhir_env._menhir_error);
        let _tok = _menhir_env._menhir_token in
        match _tok with
        | STAR ->
            _menhir_run4 _menhir_env (Obj.magic _menhir_stack)
        | _ ->
            assert (not _menhir_env._menhir_error);
            _menhir_env._menhir_error <- true;
            let (_menhir_env : _menhir_env) = _menhir_env in
            let (_menhir_stack : ('freshtv125 * _menhir_state) * Lexing.position * _menhir_state * 'tv_ident * Lexing.position) = Obj.magic _menhir_stack in
            ((let (_menhir_stack, _, _menhir_s, _, _) = _menhir_stack in
            _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s) : 'freshtv126)) : 'freshtv128)
    | MenhirState45 ->
        let (_menhir_env : _menhir_env) = _menhir_env in
        let (_menhir_stack : ((('freshtv135 * _menhir_state * Lexing.position) * Lexing.position)) * Lexing.position * _menhir_state * 'tv_ident * Lexing.position) = Obj.magic _menhir_stack in
        ((assert (not _menhir_env._menhir_error);
        let _tok = _menhir_env._menhir_token in
        match _tok with
        | RPAR ->
            let (_menhir_env : _menhir_env) = _menhir_env in
            let (_menhir_stack : ((('freshtv131 * _menhir_state * Lexing.position) * Lexing.position)) * Lexing.position * _menhir_state * 'tv_ident * Lexing.position) = Obj.magic _menhir_stack in
            let (_endpos : Lexing.position) = _menhir_env._menhir_lexbuf.Lexing.lex_curr_p in
            ((let _menhir_env = _menhir_discard _menhir_env in
            let (_menhir_env : _menhir_env) = _menhir_env in
            let (_menhir_stack : ((('freshtv129 * _menhir_state * Lexing.position) * Lexing.position)) * Lexing.position * _menhir_state * 'tv_ident * Lexing.position) = Obj.magic _menhir_stack in
            let (_endpos__5_ : Lexing.position) = _endpos in
            ((let (((_menhir_stack, _menhir_s, _startpos__1_), _startpos__2_), _endpos_id_, _, (id : 'tv_ident), _startpos_id_) = _menhir_stack in
            let _5 = () in
            let _3 = () in
            let _2 = () in
            let _1 = () in
            let _startpos = _startpos__1_ in
            let _endpos = _endpos__5_ in
            let _v : 'tv_expr_node = 
# 144 "parser.mly"
    ( Esizeof id )
# 2610 "parser.ml"
             in
            _menhir_goto_expr_node _menhir_env _menhir_stack _endpos _menhir_s _v _startpos) : 'freshtv130)) : 'freshtv132)
        | _ ->
            assert (not _menhir_env._menhir_error);
            _menhir_env._menhir_error <- true;
            let (_menhir_env : _menhir_env) = _menhir_env in
            let (_menhir_stack : ((('freshtv133 * _menhir_state * Lexing.position) * Lexing.position)) * Lexing.position * _menhir_state * 'tv_ident * Lexing.position) = Obj.magic _menhir_stack in
            ((let (_menhir_stack, _, _menhir_s, _, _) = _menhir_stack in
            _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s) : 'freshtv134)) : 'freshtv136)
    | MenhirState40 | MenhirState104 | MenhirState87 | MenhirState95 | MenhirState98 | MenhirState93 | MenhirState89 | MenhirState42 | MenhirState48 | MenhirState49 | MenhirState51 | MenhirState79 | MenhirState77 | MenhirState75 | MenhirState73 | MenhirState71 | MenhirState69 | MenhirState67 | MenhirState63 | MenhirState61 | MenhirState55 | MenhirState53 ->
        let (_menhir_env : _menhir_env) = _menhir_env in
        let (_menhir_stack : 'freshtv145 * Lexing.position * _menhir_state * 'tv_ident * Lexing.position) = Obj.magic _menhir_stack in
        ((assert (not _menhir_env._menhir_error);
        let _tok = _menhir_env._menhir_token in
        match _tok with
        | LPAR ->
            let (_menhir_env : _menhir_env) = _menhir_env in
            let (_menhir_stack : 'freshtv139 * Lexing.position * _menhir_state * 'tv_ident * Lexing.position) = Obj.magic _menhir_stack in
            let (_startpos : Lexing.position) = _menhir_env._menhir_lexbuf.Lexing.lex_start_p in
            ((let _menhir_stack = (_menhir_stack, _startpos) in
            let _menhir_env = _menhir_discard _menhir_env in
            let _tok = _menhir_env._menhir_token in
            match _tok with
            | BANG ->
                _menhir_run51 _menhir_env (Obj.magic _menhir_stack) MenhirState55 _menhir_env._menhir_lexbuf.Lexing.lex_start_p
            | IDENT _v ->
                _menhir_run2 _menhir_env (Obj.magic _menhir_stack) _menhir_env._menhir_lexbuf.Lexing.lex_curr_p MenhirState55 _v _menhir_env._menhir_lexbuf.Lexing.lex_start_p
            | INTEGER _v ->
                _menhir_run50 _menhir_env (Obj.magic _menhir_stack) _menhir_env._menhir_lexbuf.Lexing.lex_curr_p MenhirState55 _v _menhir_env._menhir_lexbuf.Lexing.lex_start_p
            | LPAR ->
                _menhir_run49 _menhir_env (Obj.magic _menhir_stack) MenhirState55 _menhir_env._menhir_lexbuf.Lexing.lex_start_p
            | MINUS ->
                _menhir_run48 _menhir_env (Obj.magic _menhir_stack) MenhirState55 _menhir_env._menhir_lexbuf.Lexing.lex_start_p
            | SIZEOF ->
                _menhir_run43 _menhir_env (Obj.magic _menhir_stack) MenhirState55 _menhir_env._menhir_lexbuf.Lexing.lex_start_p
            | RPAR ->
                let (_menhir_env : _menhir_env) = _menhir_env in
                let (_menhir_stack : 'freshtv137) = Obj.magic _menhir_stack in
                let (_menhir_s : _menhir_state) = MenhirState55 in
                ((let _v : 'tv_loption_separated_nonempty_list_COMMA_expr__ = 
# 142 "/home/jc/.opam/4.07.1/lib/menhir/standard.mly"
    ( [] )
# 2653 "parser.ml"
                 in
                _menhir_goto_loption_separated_nonempty_list_COMMA_expr__ _menhir_env _menhir_stack _menhir_s _v) : 'freshtv138)
            | _ ->
                assert (not _menhir_env._menhir_error);
                _menhir_env._menhir_error <- true;
                _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) MenhirState55) : 'freshtv140)
        | AMPERSANDAMPERSAND | ARROW | COMMA | COMP _ | EQ | EQOP _ | MINUS | PLUS | RPAR | SEMICOLON | SLASH | STAR | VERTICALBARVERTICALBAR ->
            let (_menhir_env : _menhir_env) = _menhir_env in
            let (_menhir_stack : 'freshtv141 * Lexing.position * _menhir_state * 'tv_ident * Lexing.position) = Obj.magic _menhir_stack in
            ((let (_menhir_stack, _endpos__1_, _menhir_s, (_1 : 'tv_ident), _startpos__1_) = _menhir_stack in
            let _startpos = _startpos__1_ in
            let _endpos = _endpos__1_ in
            let _v : 'tv_lvalue = 
# 102 "parser.mly"
    ( Lident _1 )
# 2669 "parser.ml"
             in
            _menhir_goto_lvalue _menhir_env _menhir_stack _endpos _menhir_s _v _startpos) : 'freshtv142)
        | _ ->
            assert (not _menhir_env._menhir_error);
            _menhir_env._menhir_error <- true;
            let (_menhir_env : _menhir_env) = _menhir_env in
            let (_menhir_stack : 'freshtv143 * Lexing.position * _menhir_state * 'tv_ident * Lexing.position) = Obj.magic _menhir_stack in
            ((let (_menhir_stack, _, _menhir_s, _, _) = _menhir_stack in
            _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s) : 'freshtv144)) : 'freshtv146)
    | MenhirState65 ->
        let (_menhir_env : _menhir_env) = _menhir_env in
        let (_menhir_stack : (('freshtv149 * Lexing.position * _menhir_state * 'tv_expr * Lexing.position)) * Lexing.position * _menhir_state * 'tv_ident * Lexing.position) = Obj.magic _menhir_stack in
        ((let (_menhir_env : _menhir_env) = _menhir_env in
        let (_menhir_stack : (('freshtv147 * Lexing.position * _menhir_state * 'tv_expr * Lexing.position)) * Lexing.position * _menhir_state * 'tv_ident * Lexing.position) = Obj.magic _menhir_stack in
        ((let ((_menhir_stack, _endpos__1_, _menhir_s, (_1 : 'tv_expr), _startpos__1_), _endpos__3_, _, (_3 : 'tv_ident), _startpos__3_) = _menhir_stack in
        let _2 = () in
        let _startpos = _startpos__1_ in
        let _endpos = _endpos__3_ in
        let _v : 'tv_lvalue = 
# 104 "parser.mly"
    ( Larrow (_1, _3) )
# 2691 "parser.ml"
         in
        _menhir_goto_lvalue _menhir_env _menhir_stack _endpos _menhir_s _v _startpos) : 'freshtv148)) : 'freshtv150)
    | _ ->
        _menhir_fail ()) : 'freshtv152)) : 'freshtv154)

and _menhir_errorcase : _menhir_env -> 'ttv_tail -> _menhir_state -> 'ttv_return =
  fun _menhir_env _menhir_stack _menhir_s ->
    match _menhir_s with
    | MenhirState114 ->
        let (_menhir_env : _menhir_env) = _menhir_env in
        let (_menhir_stack : 'freshtv3 * _menhir_state * 'tv_decl) = Obj.magic _menhir_stack in
        ((let (_menhir_stack, _menhir_s, _) = _menhir_stack in
        _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s) : 'freshtv4)
    | MenhirState110 ->
        let (_menhir_env : _menhir_env) = _menhir_env in
        let (_menhir_stack : ('freshtv5 * _menhir_state * 'tv_formal)) = Obj.magic _menhir_stack in
        ((let (_menhir_stack, _menhir_s, _) = _menhir_stack in
        _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s) : 'freshtv6)
    | MenhirState104 ->
        let (_menhir_env : _menhir_env) = _menhir_env in
        let (_menhir_stack : 'freshtv7 * Lexing.position * _menhir_state * 'tv_stmt) = Obj.magic _menhir_stack in
        ((let (_menhir_stack, _, _menhir_s, _) = _menhir_stack in
        _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s) : 'freshtv8)
    | MenhirState98 ->
        let (_menhir_env : _menhir_env) = _menhir_env in
        let (_menhir_stack : ((((('freshtv9 * _menhir_state * Lexing.position) * Lexing.position) * Lexing.position * _menhir_state * 'tv_expr * Lexing.position) * Lexing.position) * Lexing.position * _menhir_state * 'tv_stmt)) = Obj.magic _menhir_stack in
        ((let (_menhir_stack, _, _menhir_s, _) = _menhir_stack in
        _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s) : 'freshtv10)
    | MenhirState95 ->
        let (_menhir_env : _menhir_env) = _menhir_env in
        let (_menhir_stack : ((('freshtv11 * _menhir_state * Lexing.position) * Lexing.position) * Lexing.position * _menhir_state * 'tv_expr * Lexing.position) * Lexing.position) = Obj.magic _menhir_stack in
        ((let ((_menhir_stack, _, _menhir_s, _, _), _) = _menhir_stack in
        _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s) : 'freshtv12)
    | MenhirState93 ->
        let (_menhir_env : _menhir_env) = _menhir_env in
        let (_menhir_stack : ('freshtv13 * _menhir_state * Lexing.position) * Lexing.position) = Obj.magic _menhir_stack in
        ((let ((_menhir_stack, _menhir_s, _), _) = _menhir_stack in
        _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s) : 'freshtv14)
    | MenhirState89 ->
        let (_menhir_env : _menhir_env) = _menhir_env in
        let (_menhir_stack : 'freshtv15 * _menhir_state * Lexing.position) = Obj.magic _menhir_stack in
        ((let (_menhir_stack, _menhir_s, _) = _menhir_stack in
        _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s) : 'freshtv16)
    | MenhirState87 ->
        let (_menhir_env : _menhir_env) = _menhir_env in
        let (_menhir_stack : ((('freshtv17 * _menhir_state * Lexing.position) * Lexing.position) * Lexing.position * _menhir_state * 'tv_expr * Lexing.position) * Lexing.position) = Obj.magic _menhir_stack in
        ((let ((_menhir_stack, _, _menhir_s, _, _), _) = _menhir_stack in
        _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s) : 'freshtv18)
    | MenhirState79 ->
        let (_menhir_env : _menhir_env) = _menhir_env in
        let (_menhir_stack : ('freshtv19 * Lexing.position * _menhir_state * 'tv_expr * Lexing.position)) = Obj.magic _menhir_stack in
        ((let (_menhir_stack, _, _menhir_s, _, _) = _menhir_stack in
        _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s) : 'freshtv20)
    | MenhirState77 ->
        let (_menhir_env : _menhir_env) = _menhir_env in
        let (_menhir_stack : ('freshtv21 * Lexing.position * _menhir_state * 'tv_expr * Lexing.position)) = Obj.magic _menhir_stack in
        ((let (_menhir_stack, _, _menhir_s, _, _) = _menhir_stack in
        _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s) : 'freshtv22)
    | MenhirState75 ->
        let (_menhir_env : _menhir_env) = _menhir_env in
        let (_menhir_stack : ('freshtv23 * Lexing.position * _menhir_state * 'tv_expr * Lexing.position) * (
# 33 "parser.mly"
       (Ptree.binop)
# 2755 "parser.ml"
        )) = Obj.magic _menhir_stack in
        ((let ((_menhir_stack, _, _menhir_s, _, _), _) = _menhir_stack in
        _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s) : 'freshtv24)
    | MenhirState73 ->
        let (_menhir_env : _menhir_env) = _menhir_env in
        let (_menhir_stack : ('freshtv25 * Lexing.position * _menhir_state * 'tv_expr * Lexing.position) * (
# 32 "parser.mly"
       (Ptree.binop)
# 2764 "parser.ml"
        )) = Obj.magic _menhir_stack in
        ((let ((_menhir_stack, _, _menhir_s, _, _), _) = _menhir_stack in
        _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s) : 'freshtv26)
    | MenhirState71 ->
        let (_menhir_env : _menhir_env) = _menhir_env in
        let (_menhir_stack : ('freshtv27 * Lexing.position * _menhir_state * 'tv_expr * Lexing.position) * Lexing.position) = Obj.magic _menhir_stack in
        ((let ((_menhir_stack, _, _menhir_s, _, _), _) = _menhir_stack in
        _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s) : 'freshtv28)
    | MenhirState69 ->
        let (_menhir_env : _menhir_env) = _menhir_env in
        let (_menhir_stack : ('freshtv29 * Lexing.position * _menhir_state * 'tv_expr * Lexing.position)) = Obj.magic _menhir_stack in
        ((let (_menhir_stack, _, _menhir_s, _, _) = _menhir_stack in
        _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s) : 'freshtv30)
    | MenhirState67 ->
        let (_menhir_env : _menhir_env) = _menhir_env in
        let (_menhir_stack : ('freshtv31 * Lexing.position * _menhir_state * 'tv_expr * Lexing.position)) = Obj.magic _menhir_stack in
        ((let (_menhir_stack, _, _menhir_s, _, _) = _menhir_stack in
        _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s) : 'freshtv32)
    | MenhirState65 ->
        let (_menhir_env : _menhir_env) = _menhir_env in
        let (_menhir_stack : ('freshtv33 * Lexing.position * _menhir_state * 'tv_expr * Lexing.position)) = Obj.magic _menhir_stack in
        ((let (_menhir_stack, _, _menhir_s, _, _) = _menhir_stack in
        _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s) : 'freshtv34)
    | MenhirState63 ->
        let (_menhir_env : _menhir_env) = _menhir_env in
        let (_menhir_stack : ('freshtv35 * Lexing.position * _menhir_state * 'tv_expr * Lexing.position)) = Obj.magic _menhir_stack in
        ((let (_menhir_stack, _, _menhir_s, _, _) = _menhir_stack in
        _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s) : 'freshtv36)
    | MenhirState61 ->
        let (_menhir_env : _menhir_env) = _menhir_env in
        let (_menhir_stack : ('freshtv37 * Lexing.position * _menhir_state * 'tv_expr * Lexing.position)) = Obj.magic _menhir_stack in
        ((let (_menhir_stack, _, _menhir_s, _, _) = _menhir_stack in
        _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s) : 'freshtv38)
    | MenhirState55 ->
        let (_menhir_env : _menhir_env) = _menhir_env in
        let (_menhir_stack : ('freshtv39 * Lexing.position * _menhir_state * 'tv_ident * Lexing.position) * Lexing.position) = Obj.magic _menhir_stack in
        ((let ((_menhir_stack, _, _menhir_s, _, _), _) = _menhir_stack in
        _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s) : 'freshtv40)
    | MenhirState53 ->
        let (_menhir_env : _menhir_env) = _menhir_env in
        let (_menhir_stack : ('freshtv41 * Lexing.position * _menhir_state * 'tv_lvalue * Lexing.position)) = Obj.magic _menhir_stack in
        ((let (_menhir_stack, _, _menhir_s, _, _) = _menhir_stack in
        _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s) : 'freshtv42)
    | MenhirState51 ->
        let (_menhir_env : _menhir_env) = _menhir_env in
        let (_menhir_stack : 'freshtv43 * _menhir_state * Lexing.position) = Obj.magic _menhir_stack in
        ((let (_menhir_stack, _menhir_s, _) = _menhir_stack in
        _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s) : 'freshtv44)
    | MenhirState49 ->
        let (_menhir_env : _menhir_env) = _menhir_env in
        let (_menhir_stack : 'freshtv45 * _menhir_state * Lexing.position) = Obj.magic _menhir_stack in
        ((let (_menhir_stack, _menhir_s, _) = _menhir_stack in
        _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s) : 'freshtv46)
    | MenhirState48 ->
        let (_menhir_env : _menhir_env) = _menhir_env in
        let (_menhir_stack : 'freshtv47 * _menhir_state * Lexing.position) = Obj.magic _menhir_stack in
        ((let (_menhir_stack, _menhir_s, _) = _menhir_stack in
        _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s) : 'freshtv48)
    | MenhirState45 ->
        let (_menhir_env : _menhir_env) = _menhir_env in
        let (_menhir_stack : (('freshtv49 * _menhir_state * Lexing.position) * Lexing.position)) = Obj.magic _menhir_stack in
        ((let ((_menhir_stack, _menhir_s, _), _) = _menhir_stack in
        _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s) : 'freshtv50)
    | MenhirState42 ->
        let (_menhir_env : _menhir_env) = _menhir_env in
        let (_menhir_stack : ('freshtv51 * _menhir_state * Lexing.position) * Lexing.position) = Obj.magic _menhir_stack in
        ((let ((_menhir_stack, _menhir_s, _), _) = _menhir_stack in
        _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s) : 'freshtv52)
    | MenhirState40 ->
        let (_menhir_env : _menhir_env) = _menhir_env in
        let (_menhir_stack : ('freshtv53 * _menhir_state * Lexing.position) * _menhir_state * 'tv_list_decl_var_) = Obj.magic _menhir_stack in
        ((let (_menhir_stack, _menhir_s, _) = _menhir_stack in
        _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s) : 'freshtv54)
    | MenhirState39 ->
        let (_menhir_env : _menhir_env) = _menhir_env in
        let (_menhir_stack : 'freshtv55 * _menhir_state * Lexing.position) = Obj.magic _menhir_stack in
        ((let (_menhir_stack, _menhir_s, _) = _menhir_stack in
        _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s) : 'freshtv56)
    | MenhirState38 ->
        let (_menhir_env : _menhir_env) = _menhir_env in
        let (_menhir_stack : ((('freshtv57 * _menhir_state * 'tv_formal) * Lexing.position) * _menhir_state * 'tv_formals) * Lexing.position) = Obj.magic _menhir_stack in
        ((let ((_menhir_stack, _menhir_s, _), _) = _menhir_stack in
        _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s) : 'freshtv58)
    | MenhirState33 ->
        let (_menhir_env : _menhir_env) = _menhir_env in
        let (_menhir_stack : 'freshtv59 * _menhir_state) = Obj.magic _menhir_stack in
        ((let (_menhir_stack, _menhir_s) = _menhir_stack in
        _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s) : 'freshtv60)
    | MenhirState32 ->
        let (_menhir_env : _menhir_env) = _menhir_env in
        let (_menhir_stack : ('freshtv61 * _menhir_state * 'tv_formal) * Lexing.position) = Obj.magic _menhir_stack in
        ((let ((_menhir_stack, _menhir_s, _), _) = _menhir_stack in
        _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s) : 'freshtv62)
    | MenhirState27 ->
        let (_menhir_env : _menhir_env) = _menhir_env in
        let (_menhir_stack : 'freshtv63 * _menhir_state) = Obj.magic _menhir_stack in
        ((let (_menhir_stack, _menhir_s) = _menhir_stack in
        _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s) : 'freshtv64)
    | MenhirState25 ->
        let (_menhir_env : _menhir_env) = _menhir_env in
        let (_menhir_stack : 'freshtv65 * _menhir_state * 'tv_decl_var) = Obj.magic _menhir_stack in
        ((let (_menhir_stack, _menhir_s, _) = _menhir_stack in
        _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s) : 'freshtv66)
    | MenhirState20 ->
        let (_menhir_env : _menhir_env) = _menhir_env in
        let (_menhir_stack : ('freshtv67 * Lexing.position * _menhir_state * 'tv_ident * Lexing.position)) = Obj.magic _menhir_stack in
        ((let (_menhir_stack, _, _menhir_s, _, _) = _menhir_stack in
        _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s) : 'freshtv68)
    | MenhirState16 ->
        let (_menhir_env : _menhir_env) = _menhir_env in
        let (_menhir_stack : 'freshtv69 * _menhir_state) = Obj.magic _menhir_stack in
        ((let (_menhir_stack, _menhir_s) = _menhir_stack in
        _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s) : 'freshtv70)
    | MenhirState12 ->
        let (_menhir_env : _menhir_env) = _menhir_env in
        let (_menhir_stack : ('freshtv71 * _menhir_state * 'tv_star_ident)) = Obj.magic _menhir_stack in
        ((let (_menhir_stack, _menhir_s, _) = _menhir_stack in
        _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s) : 'freshtv72)
    | MenhirState9 ->
        let (_menhir_env : _menhir_env) = _menhir_env in
        let (_menhir_stack : 'freshtv73 * _menhir_state) = Obj.magic _menhir_stack in
        ((let (_menhir_stack, _menhir_s) = _menhir_stack in
        _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s) : 'freshtv74)
    | MenhirState8 ->
        let (_menhir_env : _menhir_env) = _menhir_env in
        let (_menhir_stack : ('freshtv75 * _menhir_state) * Lexing.position * _menhir_state * 'tv_ident * Lexing.position) = Obj.magic _menhir_stack in
        ((let (_menhir_stack, _, _menhir_s, _, _) = _menhir_stack in
        _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s) : 'freshtv76)
    | MenhirState7 ->
        let (_menhir_env : _menhir_env) = _menhir_env in
        let (_menhir_stack : 'freshtv77 * _menhir_state) = Obj.magic _menhir_stack in
        ((let (_menhir_stack, _menhir_s) = _menhir_stack in
        _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s) : 'freshtv78)
    | MenhirState6 ->
        let (_menhir_env : _menhir_env) = _menhir_env in
        let (_menhir_stack : (('freshtv79 * _menhir_state) * Lexing.position * _menhir_state * 'tv_ident * Lexing.position) * Lexing.position) = Obj.magic _menhir_stack in
        ((let ((_menhir_stack, _, _menhir_s, _, _), _) = _menhir_stack in
        _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s) : 'freshtv80)
    | MenhirState4 ->
        let (_menhir_env : _menhir_env) = _menhir_env in
        let (_menhir_stack : (('freshtv81 * _menhir_state) * Lexing.position * _menhir_state * 'tv_ident * Lexing.position)) = Obj.magic _menhir_stack in
        ((let (_menhir_stack, _, _menhir_s, _, _) = _menhir_stack in
        _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s) : 'freshtv82)
    | MenhirState1 ->
        let (_menhir_env : _menhir_env) = _menhir_env in
        let (_menhir_stack : 'freshtv83 * _menhir_state) = Obj.magic _menhir_stack in
        ((let (_menhir_stack, _menhir_s) = _menhir_stack in
        _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s) : 'freshtv84)
    | MenhirState0 ->
        let (_menhir_env : _menhir_env) = _menhir_env in
        let (_menhir_stack : 'freshtv85) = Obj.magic _menhir_stack in
        (raise _eRR : 'freshtv86)

and _menhir_reduce29 : _menhir_env -> 'ttv_tail -> _menhir_state -> 'ttv_return =
  fun _menhir_env _menhir_stack _menhir_s ->
    let _v : 'tv_list_decl_ = 
# 211 "/home/jc/.opam/4.07.1/lib/menhir/standard.mly"
    ( [] )
# 2923 "parser.ml"
     in
    _menhir_goto_list_decl_ _menhir_env _menhir_stack _menhir_s _v

and _menhir_run1 : _menhir_env -> 'ttv_tail -> _menhir_state -> 'ttv_return =
  fun _menhir_env _menhir_stack _menhir_s ->
    let _menhir_stack = (_menhir_stack, _menhir_s) in
    let _menhir_env = _menhir_discard _menhir_env in
    let _tok = _menhir_env._menhir_token in
    match _tok with
    | IDENT _v ->
        _menhir_run2 _menhir_env (Obj.magic _menhir_stack) _menhir_env._menhir_lexbuf.Lexing.lex_curr_p MenhirState1 _v _menhir_env._menhir_lexbuf.Lexing.lex_start_p
    | _ ->
        assert (not _menhir_env._menhir_error);
        _menhir_env._menhir_error <- true;
        _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) MenhirState1

and _menhir_run27 : _menhir_env -> 'ttv_tail -> _menhir_state -> 'ttv_return =
  fun _menhir_env _menhir_stack _menhir_s ->
    let _menhir_stack = (_menhir_stack, _menhir_s) in
    let _menhir_env = _menhir_discard _menhir_env in
    let _tok = _menhir_env._menhir_token in
    match _tok with
    | IDENT _v ->
        _menhir_run2 _menhir_env (Obj.magic _menhir_stack) _menhir_env._menhir_lexbuf.Lexing.lex_curr_p MenhirState27 _v _menhir_env._menhir_lexbuf.Lexing.lex_start_p
    | _ ->
        assert (not _menhir_env._menhir_error);
        _menhir_env._menhir_error <- true;
        _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) MenhirState27

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
# 56 "parser.mly"
      (Ptree.file)
# 2968 "parser.ml"
) =
  fun lexer lexbuf ->
    let _menhir_env =
      let (lexer : Lexing.lexbuf -> token) = lexer in
      let (lexbuf : Lexing.lexbuf) = lexbuf in
      ((let _tok = Obj.magic () in
      {
        _menhir_lexer = lexer;
        _menhir_lexbuf = lexbuf;
        _menhir_token = _tok;
        _menhir_error = false;
      }) : _menhir_env)
    in
    Obj.magic (let (_menhir_env : _menhir_env) = _menhir_env in
    let (_menhir_stack : 'freshtv1) = ((), _menhir_env._menhir_lexbuf.Lexing.lex_curr_p) in
    ((let _menhir_env = _menhir_discard _menhir_env in
    let _tok = _menhir_env._menhir_token in
    match _tok with
    | INT ->
        _menhir_run27 _menhir_env (Obj.magic _menhir_stack) MenhirState0
    | STRUCT ->
        _menhir_run1 _menhir_env (Obj.magic _menhir_stack) MenhirState0
    | EOF ->
        _menhir_reduce29 _menhir_env (Obj.magic _menhir_stack) MenhirState0
    | _ ->
        assert (not _menhir_env._menhir_error);
        _menhir_env._menhir_error <- true;
        _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) MenhirState0) : 'freshtv2))

# 269 "/home/jc/.opam/4.07.1/lib/menhir/standard.mly"
  

# 3001 "parser.ml"
