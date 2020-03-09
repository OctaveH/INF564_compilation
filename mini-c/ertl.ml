open Ertltree

let (p0::p1::p2::p3::p4::p5::[]) = Register.parameters

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
  |t::[] -> Epush_param(t,nextl)
  |t::q -> let newl = generate (Epush_param(t,nextl)) in push_pile q newl
      (*Début de fonction*)
let rec pull_pile l nextl n : Label.t = match l with
  |[] -> nextl
  |t::q -> let newl = generate (Eget_param(n,t,nextl)) in pull_pile q newl (n+8)
      (*On met les args dans les registres réels avant Ecall*)
let rec args_to rfic rreel id k nextl : instr = match (rfic,rreel) with
  |([],_)-> Egoto nextl
  |(t::[],r::qr)->Embinop(Mmov,t,r,nextl)
  |(l,[])-> push_pile l nextl
  |(t::qf,r::qr)->let i = Embinop(Mmov,t,r,nextl) in
    let newl= generate i in
    args_to qf qr id k newl
(*Début de fonction, on met les args dans leur pseudoregistre*)
let rec to_args rfic rreel nextl : Label.t = match (rfic,rreel) with
  |([],_)-> nextl
  |(l,[])-> pull_pile (reverse l) nextl 0
  |(t::qf,r::qr)->let newl=to_args qf qr nextl in
    generate(Embinop(Mmov,r,t,newl))


let to_instr (i:Rtltree.instr) : instr = match i with
  | Rtltree.Econst (r, n, l) -> Econst (r, n, l)
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
  | Rtltree.Ecall (r,id,args,l) -> let k = length args in
    let i = Embinop(Mmov,Register.result,r,l) in
    let newl = generate i in
    if (k>6) then let i2 = Emunop(Maddi (Int32.of_int (8*(6-k))),Register.rsp,newl) in
      let newl2 = generate i2 in
      let i3 = Ecall(id,k,newl2) in
      let newl3 = generate i3 in
      args_to args Register.parameters id k newl3

        else let i2 = Ecall(id,k,newl) in
      let newl2 = generate i2 in
      args_to args Register.parameters id k newl2



let  tocfg  cfg =
  (*graph := Label.M.empty;*)
  let aux l i =
    let newi = to_instr i in
    graph := Label.M.add l newi !graph in
  Label.M.iter aux cfg

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
  in aux l (reverse Register.callee_saved) nextl



let tofun (f:Rtltree.deffun) : deffun =
  tocfg f.fun_body;
  let k = length f.fun_formals in
  let newl = to_args f.fun_formals Register.parameters f.fun_entry in
  let (locals,newl2) = callee_saved newl in
  let newl3 = generate(Ealloc_frame newl2) in
  let l_end = generate Ereturn in
  let l_end2 = generate (Edelete_frame l_end) in
  let l_end3 = callee_restaured locals l_end2 in
  graph := Label.M.add f.fun_exit (Embinop(Mmov,f.fun_result,Register.rax,l_end3)) !graph;
  {
    fun_name = f.fun_name;
    fun_formals = k; (* nb total d'arguments *)
    fun_locals = f.fun_locals;
    fun_entry = newl3;
    fun_body = !graph;
  }



let program (l:Rtltree.file) : file =
  let rec aux m l = match l with
    |[]-> m
    |t::q -> aux ((tofun t)::m) q
  in {funs = aux [] l.funs}
