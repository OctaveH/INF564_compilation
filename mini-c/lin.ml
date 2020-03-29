open X86_64
open Ops

let visited = Hashtbl.create 17
type instr = Code of text | Label of Label.t
let code = ref []
let emit l i = code := Code i :: Label l :: !code
let emit_wl i = code := Code i :: !code
let labels = Hashtbl.create 17
let need_label l = Hashtbl.add labels l ()

(* let asm_unop (op:munop) (o:Ltltree.operand) =
  match op with
  | Maddi n -> addq (imm32 n)
  | Msetei n -> *)

let operand (o:Ltltree.operand) : [`Q] operand =
  match o with
  | Reg r -> reg (register64 r)
  | Spilled n -> ind (register64 Register.rbp) ~ofs: n

let ubranch (mub:mubranch) (same:bool) : int32 * (label -> text) =
  match mub, same with
  | Mjz, true -> 0l, jz
  | Mjz, false -> 0l, jnz
  | Mjnz, true -> 0l, jnz
  | Mjnz, false -> 0l, jz
  | Mjlei n, true -> n, jle
  | Mjlei n, false -> n, jg
  | Mjgi n, true -> n, jg
  | Mjgi n, false -> n, jle

let bbranch (mbb:mbbranch) (same:bool) : label -> text =
  match mbb, same with
  | Mjl, true -> jl
  | Mjl, false -> jge
  | Mjle, true -> jle
  | Mjle, false -> jg


let byte_register (o:Ltltree.operand) : [`B] operand =
  match o with
  | Reg r -> reg (register8 (register64 r))
  | Spilled n -> ind (register64 Register.rbp) ~ofs: n

let rec lin g l =
  if not (Hashtbl.mem visited l) then begin
    Hashtbl.add visited l ();
    instr g l (Label.M.find l g)
  end else begin
    need_label l;
    emit_wl (jmp (l :> string))
  end

and instr g l = function
  | Ltltree.Econst (n, o, l1) ->
    emit l (movq (imm32 n) (operand o)); lin g l1
  | Ltltree.Eload (r1, n, r2, l1) ->
    emit l (movq (ind (register64 r1) ~ofs: n) (reg (register64 r2)));
    lin g l1
  | Ltltree.Estore (r1, r2, n, l1) ->
    emit l (movq (reg (register64 r1)) (ind (register64 r2) ~ofs: n));
    lin g l1
  | Ltltree.Egoto l1 when Hashtbl.mem visited l1 ->
    need_label l1;
    emit l (jmp (l1 :> string))
  | Ltltree.Egoto l1 ->
    code := Label l :: !code;
    lin g l1
  | Ltltree.Emunop (op, o, l1) -> begin
      match op with
      | Maddi n -> emit l (addq (imm32 n) (operand o))
      | Msetei n -> emit l (cmpq (imm32 n) (operand o));
        emit_wl (movq (imm32 0l) (operand o));
        emit_wl (sete (byte_register o))
      | Msetnei n -> emit l (cmpq (imm32 n) (operand o));
        emit_wl (movq (imm32 0l) (operand o));
        emit_wl (setne (byte_register o))
    end;
    lin g l1

  | Ltltree.Embinop (op, o1, o2, l1) -> begin
      match op with
      | Mmov -> emit l (movq (operand o1) (operand o2))
      | Madd -> emit l (addq (operand o1) (operand o2))
      | Msub -> emit l (subq (operand o1) (operand o2))
      | Mmul -> emit l (imulq (operand o1) (operand o2))
      | Mdiv -> assert false
      | Msete -> emit l (cmpq (operand o1) (operand o1));
        emit_wl (movq (imm32 0l) (operand o2));
        emit_wl (sete (byte_register o2))
      | Msetne -> emit l (cmpq (operand o1) (operand o1));
        emit_wl (movq (imm32 0l) (operand o2));
        emit_wl (setne (byte_register o2))
      | Msetl -> emit l (cmpq (operand o1) (operand o1));
        emit_wl (movq (imm32 0l) (operand o2));
        emit_wl (setl (byte_register o2))
      | Msetle -> emit l (cmpq (operand o1) (operand o1));
        emit_wl (movq (imm32 0l) (operand o2));
        emit_wl (setle (byte_register o2))
      | Msetg -> emit l (cmpq (operand o1) (operand o1));
        emit_wl (movq (imm32 0l) (operand o2));
        emit_wl (setg (byte_register o2))
      | Msetge -> emit l (cmpq (operand o1) (operand o1));
        emit_wl (movq (imm32 0l) (operand o2));
        emit_wl (setge (byte_register o2))
    end;
    lin g l1

  | Ltltree.Emubranch (mub, o, l1, l2) -> begin
      if not (Hashtbl.mem visited l2) then
        let n, jcc = ubranch mub true in
        (emit l (cmpq (imm32 n) (operand o));
         need_label l1;
         emit_wl (jcc (l1 :> string));
         lin g l2;
         lin g l1)
      else if not (Hashtbl.mem visited l1) then
        let n, jcc_bar = ubranch mub false in
        (emit l (cmpq (imm32 n) (operand o));
         need_label l2;
         emit_wl (jcc_bar (l2 :> string));
         lin g l1;
         lin g l2)
      else
        let n, jcc = ubranch mub true in
        (emit l (cmpq (imm32 n) (operand o));
         need_label l1;
         emit_wl (jcc (l1 :> string));
         need_label l2;
         emit_wl (jmp (l2 :> string)))
    end

  | Ltltree.Embbranch (mbb, o1, o2, l1, l2) -> begin
      if not (Hashtbl.mem visited l2) then
        let jcc = bbranch mbb true in
        (emit l (cmpq (operand o1) (operand o2));
         need_label l1;
         emit_wl (jcc (l1 :> string));
         lin g l2;
         lin g l1)
      else if not (Hashtbl.mem visited l1) then
        let jcc_bar = bbranch mbb false in
        (emit l (cmpq (operand o1) (operand o2));
         need_label l2;
         emit_wl (jcc_bar (l2 :> string));
         lin g l1;
         lin g l2)
      else
        let jcc = bbranch mbb true in
        (emit l (cmpq (operand o1) (operand o2));
         need_label l1;
         emit_wl (jcc (l1 :> string));
         need_label l2;
         emit_wl (jmp (l2 :> string)))
    end

  | Ltltree.Epush (o, l1) ->
    emit l (pushq (operand o));
    lin g l1
  | Ltltree.Ecall (id, l1) ->
    emit l (call id);
    lin g l1
  | Ltltree.Epop (r, l1) ->
    emit l (popq (register64 r));
    lin g l1
  | Ltltree.Ereturn ->
    emit l ret

let filter (i:instr) : bool =
  match i with
  | Label l -> Hashtbl.mem labels l
  | _ -> true

let fun_to_asm (f:Ltltree.deffun) : text =
  code := []; (* ? *)
  lin f.fun_body f.fun_entry;
  code := List.filter filter !code;
  let add_instr (i:instr) (t:text) = match i with
    | Label l -> t ++ label (l :> string)
    | Code c -> t ++ c
  in
  let begining =
    if f.fun_name = "main" then globl f.fun_name ++ label f.fun_name
    else label f.fun_name in
  List.fold_right (add_instr) !code begining

let program (p:Ltltree.file) : program =
  let text = ref nop in
  let data = nop in
  let add_fun () (f:Ltltree.deffun) = text := (fun_to_asm f) ++ !text in
  List.fold_left (add_fun) () p.funs;

  {
    text = !text;
    data = data;
  }
