open Ltltree

(* 1.1 - Construction du graphe d'interférence *)

type arcs = { prefs: Register.set; intfs: Register.set }
type igraph = arcs Register.map

let print_ig ig =
  Register.M.iter (fun r arcs ->
    Format.printf "%s: prefs=@[%a@] intfs=@[%a@]@." (r :> string)
      Register.print_set arcs.prefs Register.print_set arcs.intfs) ig

open Format
let print_color fmt = function
  | Reg hr    -> fprintf fmt "%a" Register.print hr
  | Spilled n -> fprintf fmt "stack %d" n
let print_cm cm =
  Register.M.iter
    (fun r cr -> printf "%a -> %a@\n" Register.print r print_color cr) cm

let new_node () : arcs =
  {prefs=Register.S.empty; intfs=Register.S.empty}

let add_in_prefs (inter_graph:igraph) (r1:Register.t) (r2:Register.t) : igraph =
  let arcs_r1_old = (try Register.M.find r1 inter_graph with Not_found -> new_node ()) in
  let arcs_r2_old = (try Register.M.find r2 inter_graph with Not_found -> new_node ()) in
  let arcs_r1 = {prefs=Register.S.add r2 arcs_r1_old.prefs; intfs=arcs_r1_old.intfs} in
  let arcs_r2 = {prefs=Register.S.add r1 arcs_r2_old.prefs; intfs=arcs_r2_old.intfs} in
  let ig_tmp = Register.M.add r1 arcs_r1 inter_graph in
  Register.M.add r2 arcs_r2 ig_tmp

let add_in_intfs (inter_graph:igraph) (r1:Register.t) (r2:Register.t) : igraph =
  let arcs_r1_old = (try Register.M.find r1 inter_graph with Not_found -> new_node ()) in
  let arcs_r2_old = (try Register.M.find r2 inter_graph with Not_found -> new_node ()) in
  let prefs_r1 = Register.S.remove r2 arcs_r1_old.prefs in
  let prefs_r2 = Register.S.remove r1 arcs_r2_old.prefs in
  let intfs_r1 = Register.S.add r2 arcs_r1_old.intfs in
  let intfs_r2 = Register.S.add r1 arcs_r2_old.intfs in
  let arcs_r1 = {prefs=prefs_r1; intfs=intfs_r1} in
  let arcs_r2 = {prefs=prefs_r2; intfs=intfs_r2} in
  let ig_tmp = Register.M.add r1 arcs_r1 inter_graph in
  Register.M.add r2 arcs_r2 ig_tmp

let add_node (inter_graph:igraph) (r:Register.t) =
  if not (Register.M.mem r inter_graph) then
    Register.M.add r (new_node ()) inter_graph
  else
    inter_graph

let make (l_infos:Ertltree.live_info Label.map) : igraph =
  let inter_graph = ref Register.M.empty in

  let handle_live_info_prefs _ (li:Ertltree.live_info) : unit =
    match li.instr with
    | Embinop(Mmov, r1, r2, _) -> inter_graph := add_in_prefs !inter_graph r1 r2
    | Econst (_, r, _)
    | Emunop (_, r, _)
    | Emubranch (_, r, _, _)
    | Eget_param (_, r, _)
    | Epush_param (r, _) ->
      inter_graph := add_node !inter_graph r
    | Eload (r1, _, r2, _)
    | Estore (r1, r2, _, _)
    | Embinop (_, r1, r2, _)
    | Embbranch (_, r1, r2, _, _) ->
      inter_graph := add_node !inter_graph r1;
      inter_graph := add_node !inter_graph r2
    | _ -> ()
  in

  let handle_live_info_intfs _ (li:Ertltree.live_info) : unit =
    let handle_reg_out r_def = fun r_out -> if (r_out != r_def) then
        inter_graph := add_in_intfs !inter_graph r_def r_out in
    let handle_reg_def = fun r_def -> Register.S.iter (handle_reg_out r_def) li.outs in
    Register.S.iter handle_reg_def li.defs
  in

  Label.M.iter handle_live_info_prefs l_infos;
  Label.M.iter handle_live_info_intfs l_infos;

  !inter_graph

(* 1.2 - Coloration du graphe d'interférence *)

type color = operand
type coloring = color Register.map

let color (inter_graph:igraph) : coloring * int =
  let chosen_color = ref Register.M.empty in
  let todo = ref Register.S.empty in
  Register.M.iter (fun r _ -> if Register.is_pseudo r then todo := Register.S.add r !todo) inter_graph;
  let todo_init = !todo in
  let diff_allocatable = fun node -> Register.S.diff Register.allocatable node.intfs in
  let possible_colors = ref (Register.M.map diff_allocatable inter_graph) in
  possible_colors := Register.M.filter (fun reg _ -> Register.S.mem reg !todo) !possible_colors;

  let register_to_color () : (Register.t * color) option =
    let check_ge_one_color reg colors =
      not(Register.S.is_empty colors) && Register.S.mem reg !todo in
    let at_least_one_color =
      Register.M.filter check_ge_one_color !possible_colors in
    let check_eq_one_color _ colors =
      Register.S.cardinal colors == 1 in
    let exactly_one_color =
      Register.M.filter check_eq_one_color at_least_one_color in

    (* Checks if pref has a chosen color corresponding to one possible color of reg *)
    let check_pref_in_colors reg colors pref =
      (try Register.S.mem (Register.M.find pref !chosen_color) colors
       with Not_found -> false) in

    (* Find preferences which color is known and corresond to one possible color of reg *)
    let find_pref_with_color reg colors : Register.set =
      let prefs = (Register.M.find reg inter_graph).prefs in
      Register.S.filter (check_pref_in_colors reg colors) prefs in

    let check_has_pref_color reg colors =
      not(Register.S.is_empty (find_pref_with_color reg colors)) in

    let exactly_one_color_pref =
      Register.M.filter check_has_pref_color exactly_one_color in
    let at_least_one_color_pref =
      Register.M.filter check_has_pref_color at_least_one_color in

    if not(Register.M.is_empty exactly_one_color_pref) then
      let reg, colors = Register.M.choose exactly_one_color_pref in
      let col = Register.S.choose colors in
      Some (reg, Reg col)

    else if not(Register.M.is_empty exactly_one_color) then
      let reg, colors = Register.M.choose exactly_one_color in
      let col = Register.S.choose colors in
      Some (reg, Reg col)

    else if not(Register.M.is_empty at_least_one_color_pref) then
      let reg, colors = Register.M.choose at_least_one_color_pref in
      let prefs = find_pref_with_color reg colors in
      let pref = (Register.S.choose prefs) in
      let col = Register.M.find pref !chosen_color in
      Some (reg, Reg col)

    else if not(Register.M.is_empty at_least_one_color) then
      let reg, colors = Register.M.choose at_least_one_color in
      let col = Register.S.choose colors in
      Some (reg, Reg col)

    else
      None
  in
  while not(Register.S.is_empty !todo) do
    match register_to_color () with
    | Some (reg, Reg col) ->
      chosen_color := Register.M.add reg col !chosen_color;
      todo := Register.S.remove reg !todo;
      possible_colors := Register.M.filter (fun reg _ -> Register.S.mem reg !todo) !possible_colors;
      let remove_color reg_intf set_col =
        if Register.S.mem reg_intf (Register.M.find reg inter_graph).intfs then
          Register.S.remove col set_col
        else
          set_col
      in
      possible_colors := Register.M.mapi remove_color !possible_colors
    | _ -> let reg = Register.S.choose !todo in
      todo := Register.S.remove reg !todo;
      possible_colors := Register.M.filter (fun reg _ -> Register.S.mem reg !todo) !possible_colors;
  done;

  let colormap = ref Register.M.empty in
  let stack_counter = ref 0 in
  let set_color reg = match Register.M.find_opt reg !chosen_color with
    | Some col -> colormap := Register.M.add reg (Reg col) !colormap
    | None -> stack_counter := !stack_counter + 1;
      colormap := Register.M.add reg (Spilled (-8 * !stack_counter)) !colormap
  in
  Register.S.iter set_color todo_init;

  !colormap, !stack_counter


(* 1.3 - Construction du code LTL *)

let cur_cfg = ref Label.M.empty

let generate (i:instr) =
  let l = Label.fresh () in
  cur_cfg := Label.M.add l i !cur_cfg;
  l

let lookup (c:coloring) (r:Register.t) =
  if Register.is_hw r then
    Reg r
  else
    Register.M.find r c

let instr (c:coloring) (frame_size:int) = function
  | Ertltree.Econst (n, r, l) ->
    Econst (n, lookup c r, l)
  | Ertltree.Eload (r1, n, r2, l) ->
    begin
      match lookup c r1, lookup c r2 with
      | Reg re1, Reg re2 -> Eload (re1, n, re2, l)
      | Reg re1, Spilled n2 ->
        let l2 = generate (Estore (Register.tmp2, Register.rbp, n2, l)) in
        Eload (re1, n, Register.tmp2, l2)
      | Spilled n1, Reg re2 ->
        let l2 = generate (Eload (Register.tmp2, n, re2, l)) in
        Eload (Register.rbp, n1, Register.tmp2, l2)
      | Spilled n1, Spilled n2 ->
        let l3 = generate (Estore (Register.tmp1, Register.rbp, n2, l)) in
        let l2 = generate (Eload (Register.tmp2, n, Register.tmp1, l3)) in
        Eload (Register.rbp, n1, Register.tmp2, l2)
    end
  | Ertltree.Estore (r1, r2, n, l) -> begin
      match lookup c r1, lookup c r2 with
      | Reg re1, Reg re2 -> Estore (re1, re2, n, l)
      | Reg re1, Spilled n2 ->
        let l2 = generate (Estore(re1, Register.tmp2, n, l)) in
        Eload (Register.rbp, n2, Register.tmp2, l2)
      | Spilled n1, Reg re2 ->
        let l2 = generate (Estore (Register.tmp2, re2, n, l)) in
        Eload (Register.rbp, n1, Register.tmp2, l2)
      | Spilled n1, Spilled n2 ->
        let l3 = generate (Estore (Register.tmp2, Register.tmp1, n, l)) in
        let l2 = generate (Eload (Register.rbp, n2, Register.tmp1, l3)) in
        Eload (Register.rbp, n1, Register.tmp2, l2)

  end
  | Ertltree.Emunop (op, r, l) ->
    Emunop (op, lookup c r, l)
  | Ertltree.Embinop (Mmov, r1, r2, l) when (lookup c r1) = (lookup c r2) ->
    Egoto l
  | Ertltree.Embinop (Mmul, r1, r2, l) -> begin
      match lookup c r2 with
      | Reg re2 -> Embinop (Mmul, lookup c r1, Reg re2, l)
      | Spilled n2 ->
        let l2 = generate (Embinop (Mmul, lookup c r1, Reg Register.tmp1, l)) in
        Eload (Register.rbp, n2, Register.tmp1, l2)
  end
  | Ertltree.Embinop (op, r1, r2, l) -> begin
      match lookup c r1, lookup c r2  with
      | Spilled n1, Spilled n2 ->
        let l2 = generate (Embinop (op, Reg Register.tmp1, Spilled n2, l)) in
        Eload (Register.rbp, n1, Register.tmp1, l2)
      | opr1, opr2 -> Embinop (op, opr1, opr2, l)
  end
  | Ertltree.Emubranch (b, r, l1, l2) ->
    Emubranch (b, lookup c r, l1, l2)
  | Ertltree.Embbranch (b, r1, r2, l1, l2) -> begin
      match lookup c r1, lookup c r2 with
      | Spilled n1, Spilled n2 ->
        let l2 = generate (Embbranch (b, Reg Register.tmp1, Spilled n2, l1, l2)) in
        Eload (Register.rbp, n1, Register.tmp1, l2)
      | opr1, opr2 -> Embbranch (b, opr1, opr2, l1, l2)
  end
  | Ertltree.Egoto l ->
    Egoto l
  | Ertltree.Ecall (id, n, l) -> Ecall (id, l)
  | Ertltree.Ealloc_frame l ->
    let l2 = generate (Emunop (Maddi (Int32.of_int(-8 * frame_size)), Reg Register.rsp, l)) in
    let l3 = generate (Embinop (Mmov, Reg Register.rsp, Reg Register.rbp, l2)) in
    Epush (Reg Register.rbp, l3)
  | Ertltree.Edelete_frame l ->
    let l2 = generate (Epop (Register.rbp, l)) in
    Embinop (Mmov, Reg Register.rbp, Reg Register.rsp, l2)
  | Ertltree.Eget_param (n, r, l) -> begin
      match lookup c r with
      | Reg re -> Eload (Register.rbp, n, re, l)
      | Spilled n2 ->
        let l2 = generate (Estore (Register.tmp1, Register.rbp, n2, l)) in
        Eload (Register.rbp, n, Register.tmp1, l2)
  end
  | Ertltree.Epush_param (r, l) -> begin
      match lookup c r with
      | Reg re -> Epush (Reg re, l)
      | Spilled n ->
        let l2 = generate (Epush (Reg Register.tmp1, l)) in
        Eload (Register.rbp, n, Register.tmp1, l2)
  end
  | Ertltree.Ereturn -> Ereturn

let to_ltl_fun (f:Ertltree.deffun) : deffun =
  let live_info = Ertl.liveness f.fun_body in
  let inter_graph = ref (make live_info) in
  let add_missing_reg r =
    if not (Register.M.mem r !inter_graph) then
      inter_graph := Register.M.add r (new_node ()) !inter_graph
  in
  Register.S.iter add_missing_reg f.fun_locals;

  let colors, m = color !inter_graph in
  cur_cfg := Label.M.empty;
  let add_instr l inst =
    let ltl_inst = instr colors m inst in
    cur_cfg := Label.M.add l ltl_inst !cur_cfg
  in
  Label.M.iter add_instr f.fun_body;
  {
    fun_name = f.fun_name;
    fun_entry = f.fun_entry;
    fun_body = !cur_cfg;
  }


let program (ertl_file:Ertltree.file) : file =
  {funs = List.map to_ltl_fun ertl_file.funs}
