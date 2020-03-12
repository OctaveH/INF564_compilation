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

let make (l_infos:Ertltree.live_info Label.map) : igraph =
  let inter_graph = ref Register.M.empty in

  let handle_live_info_prefs _ (li:Ertltree.live_info) : unit =
    match li.instr with
    | Embinop(Mmov, r1, r2, _) -> inter_graph := add_in_prefs !inter_graph r1 r2
    | _ -> ()
  in

  let handle_live_info_intfs _ (li:Ertltree.live_info) : unit =
    let handle_reg_out r_def = fun r_out -> inter_graph := add_in_intfs !inter_graph r_def r_out in
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
  Register.M.iter (fun r _ -> todo := Register.S.add r !todo) inter_graph;
  let diff_allocatable = fun node -> Register.S.diff Register.allocatable node.intfs in
  let possible_colors = ref (Register.M.map diff_allocatable inter_graph) in

  (* DEBUG *)
  (* todo := Register.S.remove "r3" !todo;
  chosen_color := Register.M.add "r3" "a" !chosen_color;
  let a = Register.S.singleton "a" in
  let b = Register.S.singleton "b" in
  let ab = Register.S.union a b in
  possible_colors := Register.M.empty;
  possible_colors := Register.M.add "r1" ab !possible_colors;
  possible_colors := Register.M.add "r2" ab !possible_colors;
  possible_colors := Register.M.add "r4" a !possible_colors;
  possible_colors := Register.M.add "r5" b !possible_colors;
  let print_rm rm =
    let print_col_set cs =
      Register.S.iter (fun c -> print_string c) cs
    in
    Register.M.iter (fun r cols -> print_string (r ^ " : ");print_col_set cols; print_newline()) rm
  in *)
  (* DEBUG *)

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

    (* DEBUG *)
    (* print_rm exactly_one_color_pref;
    print_newline ();
    print_rm exactly_one_color;
    print_newline ();
    print_rm at_least_one_color_pref;
    print_newline ();
    print_rm at_least_one_color;
    print_newline (); *)
    (* DEBUG *)

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
      let remove_color reg_intf set_col =
        if Register.S.mem reg_intf (Register.M.find reg inter_graph).intfs then
          Register.S.remove col set_col
        else
          set_col
      in
      possible_colors := Register.M.mapi remove_color !possible_colors
    | None -> let reg = Register.S.choose !todo in
      todo := Register.S.remove reg !todo;
  done;

  let stack_counter = ref (-1) in
  let set_color reg _ = match Register.M.find_opt reg !chosen_color with
    | Some col -> Reg col
    | None -> stack_counter := !stack_counter + 1;
      Spilled !stack_counter
  in

  Register.M.mapi set_color inter_graph, !stack_counter + 1


(* 1.3 - Construction du code LTL *)

let lookup (c:coloring) (r:Register.t) =
  if Register.is_hw r then Reg r else Register.M.find r c

let instr (c:coloring) (frame_size:int) = function
  | Ertltree.Econst (n, r, l) ->
    Econst (n, lookup c r, l)
  | _ -> assert false


let program (ertl_file:Ertltree.file) : file =
  (* let ig1 = add_in_prefs (add_in_prefs (add_in_prefs Register.M.empty "r1" "r2") "r1" "r3") "r1" "r2" in
  (* print_ig ig1;
  print_newline (); *)
  let ig2 = add_in_intfs (add_in_intfs (add_in_intfs ig1 "r4" "r5") "r1" "r5") "r1" "r2" in
  (* print_ig ig2;
  print_newline (); *)
  let ig3 = add_in_intfs (add_in_intfs (add_in_prefs ig2 "r3" "r4") "r3" "r5") "r3" "r2" in
  print_ig ig3;
  print_newline ();
  let _ = color ig3 in *)

  (* Register.print_set Register.allocatable; *)
  (* let first_function::_ = ertl_file.funs in
  let lis = Ertl.liveness first_function.fun_body in
  let print_li lab li =
    print_string (lab ^ " : ");
    (* Ertl.print_live_info Format.std_formatter li; *)
    print_newline ()
  in

  (* Ertl.print_live_info Format.std_formatter li; *)
  (* Label.M.iter print_li lis; *)
  print_newline ();
  let inter_graph = make lis in
  print_ig inter_graph; *)


  {funs = []}
