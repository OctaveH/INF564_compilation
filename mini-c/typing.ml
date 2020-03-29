open Ttree

(* utiliser cette exception pour signaler une erreur de typage *)
exception Error of string * Ptree.loc

let localisation (loc:Ptree.loc) (file:string) : unit =
  let pos1, pos2 = loc in
  (* let file = pos1.pos_fname in *)
  let l1 = pos1.pos_lnum in
  let c1 = pos1.pos_cnum - pos1.pos_bol in
  let c2 = pos2.pos_cnum - pos1.pos_bol in
  Format.eprintf "File \"%s\", line %d, characters %d-%d:\n" file l1 c1 c2
  (* "File \"" ^ file ^ "\", line " ^ l1 ^ ", characters " ^ c1 ^ "-" ^ c2 *)


type env = {
  vars : (string, typ) Hashtbl.t;
  strs : (string, structure) Hashtbl.t;
  funs : (string, fun_profil) Hashtbl.t;
}
and fun_profil = {
  fun_ty : typ;
  arg_ty : typ list;
}

let string_of_typ = function
  | Tint -> "int"
  | Tstructp s -> "struct " ^ s.str_name ^ "*"
  | Tvoidstar -> "void*"
  | Ttypenull -> "typenull"

let string_of_struct s =
  let rep = ref "{" in
  let add_string_field id fld = rep := !rep ^ id ^ " : " ^ (string_of_typ fld.field_typ) ^ "; " in
  Hashtbl.iter add_string_field s.str_fields;
  !rep ^ "} (size : " ^ (Int32.to_string s.str_size) ^ ")"

let string_of_fun f =
  let rep = ref "(" in
  let add_string_arg typ = rep := !rep ^ (string_of_typ typ) ^ ", " in
  List.iter add_string_arg f.arg_ty;
  !rep ^ ")"

let string_of_env (e:env) : string =
  let s = ref "\nCONTEXT : \n" in
  let add_string_var name typ = s := !s ^ name ^ " : " ^ (string_of_typ typ) ^ "; " in
  let add_string_str name st = s := !s ^ name ^ " : " ^ (string_of_struct st) ^ "; " in
  let add_string_fun name f = s := !s ^ name ^ " : " ^ (string_of_fun f) ^ "; " in
  s := !s ^ "variables : {";
  Hashtbl.iter add_string_var e.vars;
  s := !s ^ "};\n";
  s := !s ^ "structures : {";
  Hashtbl.iter add_string_str e.strs;
  s := !s ^ "};\n";
  s := !s ^ "functions : {";
  Hashtbl.iter add_string_fun e.funs;
  s := !s ^ "};\n";
  !s

let new_env () =
  let e =
  {
    vars = Hashtbl.create 0;
    strs = Hashtbl.create 0;
    funs = Hashtbl.create 0;
  } in
  Hashtbl.add e.funs "putchar" {fun_ty=Tint; arg_ty=[Tint]};
  Hashtbl.add e.funs "sbrk" {fun_ty=Tvoidstar; arg_ty=[Tint]};
  e

let copy_env (e:env): env =
  {
    vars = Hashtbl.copy e.vars;
    strs = Hashtbl.copy e.strs;
    funs = Hashtbl.copy e.funs;
  }

let find_var_in_ctx (ctx:env) (id:Ptree.ident) : typ =
  try
    Hashtbl.find ctx.vars id.id
  with
  | Not_found ->
    raise (Error (("Variable \"" ^ id.id ^ "\" not declared"), id.id_loc))

let find_str_in_ctx (ctx:env) (id:Ptree.ident) : structure =
  try
    Hashtbl.find ctx.strs id.id
  with
  | Not_found ->
    raise (Error (("Structure \"" ^ id.id ^ "\" not declared"), id.id_loc))

let find_str_field (ctx:env) (str:structure) (id:Ptree.ident) : field =
  try
    Hashtbl.find str.str_fields id.id
  with
  | Not_found -> (*let () = print_string (string_of_env ctx) in*)
    raise (Error (("Structure \"" ^ str.str_name ^ "\" does not have field \"" ^ id.id ^ "\""), id.id_loc))


let find_fun_in_ctx (ctx:env) (id:Ptree.ident) : fun_profil =
  try
    Hashtbl.find ctx.funs id.id
  with
  | Not_found ->
    raise (Error (("Function \"" ^ id.id ^ "\" not declared"), id.id_loc))

let env_to_string (e:env) : string =
  let f_rec_vars (id:string) (t:typ) (s_old:string) : string =
    s_old ^ ", " ^ id in
  let vars = Hashtbl.fold f_rec_vars e.vars "" in
  "{vars : " ^ vars ^ "}"

let to_fun_profil (ft:typ) (ff:decl_var list) : fun_profil =
  let rec types_of (l:decl_var list) : typ list =
    match l with
    | [] -> []
    | (ty, _)::q -> ty::(types_of q)
  in
  {
    fun_ty = ft;
    arg_ty = types_of ff;
  }

let string_of_type = function
  | Tint       -> "int"
  | Tstructp x -> "struct " ^ x.str_name ^ " *"
  | Tvoidstar  -> "void*"
  | Ttypenull  -> "typenull"

let eq (ty1:typ) (ty2:typ) = match ty1, ty2 with
  | Tint, Ttypenull -> true         (* 2.1.2 *)
  | Ttypenull, Tint -> true         (* 2.1.2 *)
  | Ttypenull, Tstructp _ -> true   (* 2.1.2 *)
  | Tstructp _, Ttypenull -> true   (* 2.1.2 *)
  | Tvoidstar, Tstructp _ -> true   (* 2.1.2 *)
  | Tstructp _, Tvoidstar -> true   (* 2.1.2 *)
  | t1, t2 when t1 == t2 -> true
  | Tstructp s1, Tstructp s2 -> s1.str_name == s2.str_name
  | _ -> false

let rec same_types (l1:typ list) (l2:typ list) : bool =
  match l1, l2 with
  | [], [] -> true
  | t1::q1, t2::q2 when eq t1 t2 -> same_types q1 q2
  | _ -> false

let rec type_expr (ctx:env) (e:Ptree.expr) : expr = match e.expr_node with
  | Ptree.Econst 0l -> {expr_node=Econst 0l; expr_typ=Ttypenull}  (* 2.2.1 *)
  | Ptree.Econst n -> {expr_node=Econst n; expr_typ=Tint}         (* 2.2.2 *)
  | Ptree.Eright (Ptree.Lident id) ->                             (* 2.2.3 *)
    {expr_node=Eaccess_local id.id; expr_typ=find_var_in_ctx ctx id}

  | Ptree.Eright (Ptree.Larrow (e, id)) ->                        (* 2.2.4 *)
    let str = type_expr ctx e in
    begin
      match str.expr_typ with
      | Tstructp s ->
        let fld = find_str_field ctx s id in
        {expr_node=Eaccess_field (str, fld); expr_typ=fld.field_typ}
      | _ -> raise (Error ("Not a structure", e.expr_loc))
    end

  | Ptree.Eassign ((Lident id), e) ->                             (* 2.2.6 *)
    let ty1 = find_var_in_ctx ctx id in
    let e2 = type_expr ctx e in
    if eq ty1 e2.expr_typ  then
      {expr_node=Eassign_local (id.id, e2); expr_typ=ty1}
    else
      raise (Error ("Not the right type", e.expr_loc))

  | Ptree.Eassign ((Larrow (e1, id)), e2) ->                      (* 2.2.6 *)
    let str = type_expr ctx e1 in
    let fld =
    begin
      match str.expr_typ with
      | Tstructp s -> find_str_field ctx s id
      | _ -> raise (Error ("Not a structure", e.expr_loc))
    end
    in
    let te2 = type_expr ctx e2 in
    if eq fld.field_typ te2.expr_typ then
      {expr_node=Eassign_field (str, fld, te2); expr_typ=fld.field_typ}
    else
      raise (Error ("Not the right type", e2.expr_loc))

  | Ptree.Eunop (Uminus, e) ->                                    (* 2.2.7 *)
    let te = type_expr ctx e in
    if eq te.expr_typ Tint then
      {expr_node=Eunop(Uminus, te); expr_typ=Tint}
    else
      raise (Error ("Not an int", e.expr_loc))

  | Ptree.Eunop (Unot, e) -> let te = type_expr ctx e in          (* 2.2.8 *)
    {expr_node=Eunop(Unot, te); expr_typ=Tint}

  | Ptree.Ebinop (bo, e1, e2) -> begin
      match bo with
      | (Beq|Bneq|Blt|Ble|Bgt|Bge) ->                             (* 2.2.9 *)
        let te1 = type_expr ctx e1 in
        let te2 = type_expr ctx e2 in
        if eq te1.expr_typ te2.expr_typ then
          {expr_node=Ebinop(bo, te1, te2); expr_typ=Tint}
        else
          raise (Error (("This expressions has type " ^ (string_of_type te2.expr_typ) ^
                         " but is expected to have type " ^ (string_of_type te1.expr_typ)),
                       e2.expr_loc))
          (* raise (Error ("Not the same types (" ^ (loc_to_string e1.expr_loc) ^
                        ") and (" ^ (loc_to_string e2.expr_loc) ^ ")" )) *)

      | (Band|Bor) ->                                             (* 2.2.10 *)
        {expr_node=Ebinop (bo, type_expr ctx e1, type_expr ctx e2); expr_typ=Tint}

      | (Badd|Bsub|Bmul|Bdiv) ->                                  (* 2.2.11 *)
        let te1 = type_expr ctx e1 in
        let te2 = type_expr ctx e2 in
        if eq te1.expr_typ Tint && eq te2.expr_typ Tint then
          {expr_node=Ebinop(bo, te1, te2); expr_typ=Tint}
        else if eq te1.expr_typ Tint then
          raise (Error (("This expressions has type " ^ (string_of_type te2.expr_typ) ^
                         " but is expected to have type int"),
                        e2.expr_loc))
        else
          raise (Error (("This expressions has type " ^ (string_of_type te1.expr_typ) ^
                         " but is expected to have type int"),
                        e2.expr_loc))
    end

  | Ptree.Ecall (id, le) -> let fp = find_fun_in_ctx ctx id in    (* 2.2.12 *)
    let tle = List.map (type_expr ctx) le in
    let typ_list = List.map (function te -> te.expr_typ) tle in
    if same_types typ_list fp.arg_ty then
      {expr_node=Ecall (id.id, tle); expr_typ=fp.fun_ty}
    else
      raise (Error (("Cannot call \"" ^ id.id ^ "\" on these arguments"), id.id_loc))

  | Ptree.Esizeof id -> let s = find_str_in_ctx ctx id in         (* 2.2.5 *)
    {expr_node=Esizeof s; expr_typ=Tint }


let rec type_typ (ctx:env) (ptyp:Ptree.typ) : typ = match ptyp with
  | Ptree.Tint -> Tint
  | Ptree.Tstructp id -> Tstructp (find_str_in_ctx ctx id)

let rec add_decls_var_cxt (ctx:env) (l_decl:Ptree.decl_var list)
    (set_string:(string, unit) Hashtbl.t) : decl_var list =
  match l_decl with
  | [] -> []
  | (ty, id)::q -> begin
      if Hashtbl.mem set_string id.id then
        raise (Error (("Variable \"" ^ id.id ^ "\" already exists in this block"), id.id_loc))
      else (
        let tty = type_typ ctx ty in
        let tdv = tty, id.id in
        Hashtbl.add set_string id.id ();
        Hashtbl.add ctx.vars id.id tty;
        tdv::(add_decls_var_cxt ctx q set_string))
    end

let rec type_instr (ctx:env) (ty0:typ) (s:Ptree.stmt) : stmt =
  match s.stmt_node with
  | Ptree.Sskip -> Sskip (* 2.3.1 *)
  | Ptree.Sexpr e -> Sexpr (type_expr ctx e) (* 2.3.2 *)
  | Ptree.Sif (e, i1, i2) -> (* 2.3.4 *)
    let texpr = type_expr ctx e in
    let tinstr1 = type_instr ctx ty0 i1 in
    let tinstr2 = type_instr ctx ty0 i2 in
    Sif (texpr, tinstr1, tinstr2)
  | Ptree.Swhile (e, i) -> (* 2.3.5 *)
    let texpr = type_expr ctx e in
    let tinstr = type_instr ctx ty0 i in
    Swhile (texpr, tinstr)
  | Ptree.Sblock b -> Sblock (type_block ctx ty0 b)
  | Ptree.Sreturn e ->
    let expr = type_expr ctx e in
    if eq expr.expr_typ ty0
    then Sreturn expr (* 2.3.3 *)
    else
      raise (Error (("This expressions has type " ^ (string_of_type expr.expr_typ) ^
                     " but is expected to have type " ^ (string_of_type ty0)),
                    e.expr_loc))

(* 2.3.6 TODO : fill decl_var list*)
and type_block (ctx:env) (ty0:typ) (b:Ptree.block) : block = match b with
  | [], [] -> [], []
  | [], inst::q -> let dl, sl = type_block ctx ty0 ([], q)
    in dl, ((type_instr ctx ty0 inst)::sl)
  | l_decls_var, l ->
      let ctx_block = copy_env ctx in
      let tdvl = add_decls_var_cxt ctx_block l_decls_var (Hashtbl.create 0) in
      let _, linst = type_block ctx_block ty0 ([], l) in
      (tdvl, linst)

(* 2.4.2 *)
let type_fun (ctx:env) (f:Ptree.decl_fun) : decl_fun =

  let rec extract_fun_formals (ctx:env) (l:Ptree.decl_var list)
      (set_string:(string, unit) Hashtbl.t) : decl_var list =
    match l with
    | [] -> []
    | (ty, id)::q ->
      if Hashtbl.mem set_string id.id then
        raise (Error (("Function \"" ^ f.fun_name.id ^
                      "\" already take an argument named \"" ^ id.id ^ "\""), id.id_loc))
      else
        (* print_string (id.id ^ ", "); *)
        Hashtbl.add set_string id.id ();
        ((type_typ ctx ty), id.id)::(extract_fun_formals ctx q set_string)
  in

  let ft = type_typ ctx f.fun_typ in
  (* print_string ("function " ^ f.fun_name.id ^ " takes aguments : ("); *)
  let ff = extract_fun_formals ctx f.fun_formals (Hashtbl.create 0) in
  (* print_string ")\n"; *)
  Hashtbl.add ctx.funs f.fun_name.id (to_fun_profil ft ff);
  let ctx_block = copy_env ctx in
  let _ = add_decls_var_cxt ctx_block f.fun_formals (Hashtbl.create 0) in
  {
    fun_typ = ft;
    fun_name = f.fun_name.id;
    fun_formals = ff;
    fun_body = type_block ctx_block ft f.fun_body
  }

(* 2.4.1 *)
let add_struc_ctx (ctx:env) (ds:Ptree.decl_struct) : unit =
  let id, l_var = ds in
  let fields = Hashtbl.create 0 in
  let size = Int32.of_int (List.length l_var) in
  let str = {str_name=id.id; str_fields=fields; str_size=size} in
  Hashtbl.add ctx.strs id.id str;
    let rec add_fields (pos:int32) (lv:Ptree.decl_var list) : unit =
    match lv with
    | [] -> ()
    | (ty, vid)::q -> begin
        if Hashtbl.mem fields vid.id then
          raise (Error (("Field \"" ^ id.id ^ "\" already exists in this structure"), id.id_loc))
        else
          let tty = (type_typ ctx ty) in
          let fld = {field_name=vid.id; field_typ=tty; field_pos=pos} in
          Hashtbl.add fields vid.id fld;
          add_fields (Int32.succ pos) q
      end
  in
  add_fields 0l l_var


(* 2.4.3 *)
let rec type_file (ctx:env) (fl:Ptree.file) : file =
  match fl with
  | [] -> []
  | (Ptree.Dstruct (id, dvl))::q ->
    if Hashtbl.mem ctx.strs id.id then
      raise (Error (("Structure \"" ^ id.id ^ "\" already exists"), id.id_loc))
    else
      add_struc_ctx ctx (id, dvl);
      type_file ctx q
  | (Ptree.Dfun df)::q ->
    if Hashtbl.mem ctx.funs df.fun_name.id then
      raise (Error (("Function \"" ^ df.fun_name.id ^ "\" already exists"), df.fun_name.id_loc))
    else
      let tdf = type_fun ctx df in
      tdf::(type_file ctx q)

let program (pfile:Ptree.file) =
  let ctx = new_env () in
  let tf = type_file ctx pfile in
  (* print_string (string_of_env ctx); *)

  tf
