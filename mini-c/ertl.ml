open Ertltree

let rec length l = match l with
  |[] -> 0
  |t::q -> 1 + (length q)

let reverse l =
  let rec aux l1 l2 = match l1 with
    |[] -> l2
    |t::q -> aux q (t::l2)
  in aux l []

let graph = ref Label.M.empty

(*génère une étiquette et met i dans le graphe avec cette étiquette, puis renvoie l'étiquette *)
let generate i =
  let l = Label.fresh () in
  graph := Label.M.add l i !graph;
  l
(*Avant ecall*)
let rec push_pile l nextl : instr = match l with
  |[] -> Egoto nextl
  |t::[] -> Epush_param(t,nextl) (*attention c'est un Estore*)
  |t::q -> let newl = generate (Epush_param(t,nextl)) in push_pile q newl
(*Début de fonction*)
let rec pull_pile l nextl n : Label.t = match l with
  |[] -> nextl
  |t::q -> let newl = generate (Eget_param(n,t,nextl)) in pull_pile q newl (n+8) (*attention c'est un Eload*)
(*On met les args dans les registres réels avant Ecall*)
let rec args_caller rfic rreel id k nextl : instr = match (rfic,rreel) with
  |([],_)-> Egoto nextl
  |(t::[],r::qr)->Embinop(Mmov,t,r,nextl)
  |(l,[])-> push_pile (reverse l) nextl
  |(t::qf,r::qr)->let i = Embinop(Mmov,t,r,nextl) in
    let newl= generate i in
    args_caller qf qr id k newl
(*Début de fonction, on met les args dans leur pseudoregistre*)
let rec args_callee rfic rreel nextl : Label.t = match (rfic,rreel) with
  |([],_)-> nextl
  |(l,[])-> pull_pile (reverse l) nextl 16
  |(t::qf,r::qr)->let newl=args_callee qf qr nextl in
    generate(Embinop(Mmov,r,t,newl))

    let callee_saved nextl =
      let rec aux l regl nextl = match l with
        |[] -> (regl,nextl)
        |t::q -> let r=Register.fresh() in
          aux q (r::regl) (generate (Embinop(Mmov,t,r,nextl)))
      in aux Register.callee_saved [] nextl

    let callee_restaured l nextl =
      let rec aux l p nextl = match (l,p) with
        |([],[]) -> nextl
        |(r::qr,p::qp) -> aux qr qp (generate (Embinop(Mmov,r,p,nextl)))
        |_ -> assert(false)
      in aux l (reverse Register.callee_saved) nextl

let begin_fun formals entryl=
  let newl = args_callee formals Register.parameters entryl in
  let (locals,newl2) = callee_saved newl in
  (locals,generate(Ealloc_frame newl2))

let end_fun locals exitl result =
  let l_end = generate Ereturn in
  let l_end2 = generate (Edelete_frame l_end) in
  let l_end3 = callee_restaured locals l_end2 in
  graph := Label.M.add exitl (Embinop(Mmov,result,Register.rax,l_end3)) !graph

let end_fun_terminal locals nextl =
  let l_end = generate (Edelete_frame nextl) in
  callee_restaured locals l_end


(*Optimisation des appels terminaux :
  Côté appelé ->
  Enlève le Ealloc_frame
  Je peux changer la fin de l'appeleur et le début de l'appelé, mais pas la fin de l'appelé, donc je dois garder la partie callee_saved
  Côté appeleur ->
  Enlève le Edelete_frame, le Ereturn,
  le result de rax dans r puis de r dans rax
*)




let to_instr (i:Rtltree.instr) locals exitl: instr = match i with
  | Rtltree.Econst (r, n, l) -> Econst(r, n, l)
  | Rtltree.Eload (r1,n,r2,l) -> Eload (r1,n,r2,l)
  | Rtltree.Estore (r1,r2,n,l) -> Estore (r1,r2,n,l)
  | Rtltree.Emunop (op,r,l) -> Emunop (op,r,l)
  | Rtltree.Embinop (op,r1,r2,l) -> begin match op with
      |Mdiv -> let newl = generate (Embinop(Mmov,Register.rax,r2,l)) in
        let newl2 = generate(Embinop(Mdiv,r1,Register.rax,newl)) in
        Embinop(Mmov,r2,Register.rax,newl2)
      |_ -> Embinop (op,r1,r2,l) end
  | Rtltree.Emubranch (b,r,l1,l2) -> Emubranch (b,r,l1,l2)
  | Rtltree.Embbranch (b,r1,r2,l1,l2) -> Embbranch (b,r1,r2,l1,l2)
  | Rtltree.Egoto l -> Egoto l
  | Rtltree.Ecall (r,id,args,l) ->
    let k = length args in
    if l = exitl then (*Optimisation des appels terminaux*)
      if (k>6) then
        let endl = generate Ereturn in
        let i = Ecall (id,k,endl) in
        let newl = generate i in
        let newl2 = end_fun_terminal locals newl in
        let i3 = Emunop(Maddi (Int32.of_int (8*(6-k))),Register.rsp,newl2) in
        let newl3 = generate i3 in
        args_caller args Register.parameters id k newl3
        (* let i = Embinop(Mmov,Register.result,r,l) in
        let newl = generate i in
        let i2 = Emunop(Maddi (Int32.of_int (8*(6-k))),Register.rsp,newl) in
        let newl2 = generate i2 in
        let i3 = Ecall(id,k,newl2) in
        let newl3 = generate i3 in
          args_caller args Register.parameters id k newl3*)


      else let endl = generate Ereturn in
        let i = Ecall (id,k,endl) in
        let newl = generate i in
        let newl2 = end_fun_terminal locals newl in
        args_caller args Register.parameters id k newl2

    else (*Cas normal*)
      let i = Embinop(Mmov,Register.result,r,l) in
      let newl = generate i in
      if (k>6) then let i2 = Emunop(Maddi (Int32.of_int (8*(6-k))),Register.rsp,newl) in
        let newl2 = generate i2 in
        let i3 = Ecall(id,k,newl2) in
        let newl3 = generate i3 in
        args_caller args Register.parameters id k newl3
      else let i2 = Ecall(id,k,newl) in
        let newl2 = generate i2 in
        args_caller args Register.parameters id k newl2

let  tocfg cfg locals exitl =
  (*graph := Label.M.empty;*)
  let aux l i =
    let newi = to_instr i locals exitl in
    graph := Label.M.add l newi !graph in
  Label.M.iter aux cfg





let tofun (f:Rtltree.deffun) : deffun =

  let k = length f.fun_formals in
  let (locals,entryl) = begin_fun f.fun_formals f.fun_entry in
  tocfg f.fun_body locals f.fun_exit;
  end_fun locals f.fun_exit f.fun_result ;

  {
    fun_name = f.fun_name;
    fun_formals = k; (* nb total d'arguments *)
    fun_locals = f.fun_locals;
    fun_entry = entryl;
    fun_body = !graph;
  }


let program (l:Rtltree.file) : file =
  let rec aux l = match l with
    |[]-> []
    |t::q -> let cfg = tofun t in
      cfg :: (aux q)
  in {funs = aux l.funs}


    (*
Analyse de durée de vie
*)



(*val liveness: Ertltree.cfg -> live_info Label.map*)

let graph_info = ref Label.M.empty

let some_param n =
  let rec aux l k = match (l,k) with
    |([],k) -> []
    |(l,0) -> []
    |(t::q,k)-> t::(aux q (k-1))
  in aux Register.parameters n


let succ_defs_uses i = match i with
  | Econst (n,r,l) -> ([l],[r],[])
  | Eload (r1,n,r2,l) -> ([l],[r2],[r1])
  | Estore (r1,r2,n,l) -> ([l],[r1],[r2])
  | Emunop (n,r,l) -> ([l],[r],[r])
  | Embinop (n,r1,r2,l) -> begin match n with
    |Mdiv -> ([l],[r2],[r1;r2;Register.rax])
    |_ -> ([l],[r2],[r1;r2]) end
  | Emubranch (n,r,l1,l2) -> ([l1;l2],[],[r])
  | Embbranch (n,r1,r2,l1,l2) -> ([l1;l2],[],[r1;r2])
  | Egoto l -> ([l],[],[])
  | Ecall (id,n,l) -> ([l],Register.caller_saved,some_param n)
  | Ealloc_frame l -> ([l],[],[])
  | Edelete_frame l -> ([l],[],[])
  | Eget_param (n,r,l) -> ([l],[r],[])
  | Epush_param (r,l) -> ([l],[],[r])
  | Ereturn -> ([],[],Register.result::Register.callee_saved)

(*Create_live_info crée une Map entre qui relie chaque Label à ses infos
  instr,succ,defs et uses sont bons
  Reste à compléter pred, ins et outs*)
let create_live_info cfg =
  let aux label i =
    let (succ,defs,uses) = succ_defs_uses i in
    let info =
      {
        instr = i;
        succ  = succ ;    (* successeurs *)
        pred  = Label.S.empty;       (* prédécesseurs *)
        defs  = Register.set_of_list defs;    (* définitions *)
        uses  = Register.set_of_list uses;    (* utilisations *)
        ins   = Register.set_of_list uses;    (* variables vivantes en entrée *)
        outs  = Register.S.empty;    (* variables vivantes en sortie *)
      }
    in graph_info := Label.M.add label info !graph_info
  in Label.M.iter aux cfg

let rec add_to_pred l predl = match l with
  |[] -> ()
  |t::q -> let info = Label.M.find t !graph_info in
    (info.pred <- Label.S.add predl info.pred;
     add_to_pred q predl)


let complete_live_info ()=
  let aux label info =
    add_to_pred info.succ label;
  in Label.M.iter aux !graph_info

let kildall_fill_ws =
  let ws = ref Label.S.empty in
  let aux l i = ws := Label.S.add l !ws
  in (Label.M.iter aux !graph;
      ws)

let rec kildall_fill_out succ = match succ with
  |[] -> Register.S.empty
  |l::q -> let t = Label.M.find l !graph_info in
    Register.S.union (t.ins) (kildall_fill_out q)


let rec kildall () =
  let ws = kildall_fill_ws in
  while not (Label.S.is_empty !ws) do
    let l = Label.S.choose !ws in
    let t = Label.M.find l !graph_info in
    let old_ins = t.ins in
    t.outs <- kildall_fill_out t.succ;
    t.ins <- Register.S.union t.ins (Register.S.diff t.outs t.defs);
    if not (Register.S.equal t.ins old_ins) then
      ws := Label.S.union !ws t.pred
  done;
  ()

let liveness cfg =
  graph_info := Label.M.empty;
  create_live_info cfg;
  complete_live_info();
  kildall;
  !graph_info

let rec liveness_file p = match p with
  |[]->[]
  |t::q->(liveness t.fun_body)::(liveness_file q)


let program2 (l:Rtltree.file) =
  let rec aux l = match l with
    |[]-> []
    |t::q -> let cfg = tofun t in
      let li = liveness cfg.fun_body in
      (cfg,li) :: (aux q)
  in aux l.funs
