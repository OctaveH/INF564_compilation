open Rtltree

(*le control flow graph est stocké dans une variable globale*)
let graph = ref Label.M.empty

(*génère une étiquette et met i dans le graphe avec cette étiquette, puis renvoie l'étiquette *)
let generate i =
    let l = Label.fresh () in
    graph := Label.M.add l i !graph;
    l

let snd x = match x with
  |(a,b)->b

let reverse l =
  let rec aux l1 l2 = match l1 with
    |[] -> l2
    |t::q -> aux q (t::l2)
  in aux l []

let match_id varreg id = try
    Hashtbl.find varreg id
  with
  | Not_found ->
    raise (Typing.Error ("Variable \"" ^ id ^ "\" not declared"))


let rec expr varreg (e : Ttree.expr_node) (destr:register) (destl:label) : instr = match e with
  | Econst n -> Econst(n,destr,destl)
  | Eaccess_local id -> let r = match_id varreg id in
      Embinop(Mmov,r,destr,destl)
  | Eaccess_field (e,field) -> let t = e.expr_typ in
    begin match t with
      |Tstructp s -> let f = match_id s.str_fields field.field_name in
        let r = Register.fresh() in
        let i = Eload(r,8*(Int32.to_int f.field_pos),destr,destl) in
        let newl = generate i in
        expr varreg e.expr_node r newl
      |_ -> assert(false) end
  | Eassign_local (id,e) -> let r = match_id varreg id in
    let newl=generate(Embinop(Mmov,destr,r, destl)) in
    expr varreg e.expr_node destr newl
  | Eassign_field (e1,field,e2) -> let t = e1.expr_typ in
    begin match t with
      |Tstructp s -> let f = match_id s.str_fields field.field_name in
        let r1 = Register.fresh() in
        let i = Estore(destr,r1,8*(Int32.to_int f.field_pos),destl) in
        let newl = generate i in
        let newl2 = generate (expr varreg e2.expr_node destr newl) in
        expr varreg e1.expr_node r1 newl2
      |_ -> assert(false) end
  | Eunop (unop,e) -> begin match unop with
      |Ptree.Unot -> begin match e.expr_node with
          |Ttree.Econst n -> if Int32.equal n 0l then Econst(1l,destr,destl) else Econst(0l,destr,destl)
          |e ->
            let newl = generate(Emunop(Msetei 0l,destr,destl)) in
            expr varreg e destr newl end
      |Ptree.Uminus ->  begin match e.expr_node with
          |Econst n -> Econst(Int32.neg n,destr,destl)
          |e -> let rzero = Register.fresh() in
            let newl = generate(Embinop(Msub,rzero,destr,destl)) in
            let newl2 = generate(Econst(0l,destr,newl)) in
            expr varreg e rzero newl2 end end(*let newl = generate (Emunop(munop unop,destr,destl))in
                                      expr e.expr_node destr newl*)
  | Ebinop (binop,e1,e2) -> begin match binop with
      |Ptree.Badd -> begin match (e1.expr_node,e2.expr_node) with
          |(Ttree.Econst m, Ttree.Econst n)->Econst(Int32.add m n,destr,destl)
          |(Ttree.Econst 0l, e) -> expr varreg e destr destl
          |(e, Ttree.Econst 0l) -> expr varreg e destr destl
          |(Ttree.Econst n, e) -> let newl = generate(Emunop(Maddi n,destr,destl)) in
                            expr varreg e destr newl
          |(e, Econst n) -> let newl = generate(Emunop(Maddi n,destr,destl)) in
            expr varreg e destr newl
          |(e1,e2) -> let r1 = Register.fresh() in
            let newl = generate (Embinop(Madd,r1,destr,destl)) in
            let i = expr varreg e1 r1 newl in
            let newl2 = generate(i) in
            expr varreg e2 destr newl2 end
      |Ptree.Bsub -> begin match (e1.expr_node,e2.expr_node) with
          |(Ttree.Econst m, Ttree.Econst n)-> Econst(Int32.sub m n,destr,destl)
          |(e, Ttree.Econst 0l) -> expr varreg e destr destl
          |(e, Econst n) -> let newl = generate(Emunop(Maddi (Int32.neg n),destr,destl)) in
            expr varreg e destr newl
          |(e1,e2) -> let r2 = Register.fresh() in
            let newl = generate (Embinop(Msub,r2,destr,destl)) in
            let i = expr varreg e2 r2 newl in
            let newl2 = generate(i) in
            expr varreg e1 destr newl2 end
      |Ptree.Bmul -> begin match (e1.expr_node,e2.expr_node) with
          |(Ttree.Econst m, Ttree.Econst n)-> Econst(Int32.mul m n,destr,destl)
          |(e, Ttree.Econst 1l) -> expr varreg e destr destl
          |(Ttree.Econst 1l, e) -> expr varreg e destr destl
          |(e1,e2) -> let r1 = Register.fresh() in
            let newl = generate (Embinop(Mmul,r1,destr,destl)) in
            let i = expr varreg e1 r1 newl in
            let newl2 = generate(i) in
            expr varreg e2 destr newl2 end
          (*si on peut faire des décalages, on peut faire de la multiplication par un entier intelligemment*)

      |Ptree.Bdiv -> begin match (e1.expr_node,e2.expr_node) with
          |(Ttree.Econst m, Ttree.Econst n)-> Econst(Int32.div m n,destr,destl)
          |(e, Ttree.Econst 1l) -> expr varreg e destr destl
          |(e1,e2) -> let r2 = Register.fresh() in
            let newl = generate (Embinop(Mdiv,r2,destr,destl)) in
            let i = expr varreg e1 destr newl in
            let newl2 = generate(i) in
            expr varreg e2 r2 newl2 end
      | Ptree.Beq -> begin match (e1.expr_node,e2.expr_node) with
          |(Econst m, Econst n) -> if Int32.compare m n == 0 then Econst(1l,destr,destl) else Econst(0l,destr,destl)
          |(Econst n, e) -> let newl = generate(Emunop(Msetei n,destr,destl)) in
            expr varreg e destr newl
          |(e, Econst n) -> let newl = generate(Emunop(Msetei n,destr,destl)) in
            expr varreg e destr newl
          |(e1,e2) -> let r1 = Register.fresh() in
            let newl = generate (Embinop(Msete,r1,destr,destl)) in
            let i = expr varreg e1 r1 newl in
            let newl2 = generate(i) in
            expr varreg e2 destr newl2 end
      | Ptree.Bneq -> begin match (e1.expr_node,e2.expr_node) with
          |(Econst m, Econst n) -> if Int32.compare m n == 0 then Econst(0l,destr,destl) else Econst(1l,destr,destl)
          |(Econst n, e) -> let newl = generate(Emunop(Msetnei n,destr,destl)) in
            expr varreg e destr newl
          |(e, Econst n) -> let newl = generate(Emunop(Msetnei n,destr,destl)) in
            expr varreg e destr newl
          |(e1,e2) -> let r1 = Register.fresh() in
            let newl = generate (Embinop(Msetne,r1,destr,destl)) in
            let i = expr varreg e1 r1 newl in
            let newl2 = generate(i) in

            expr varreg e2 destr newl2 end
      | Ptree.Blt -> begin match (e1.expr_node,e2.expr_node) with
          |(Econst m, Econst n) -> if Int32.compare m n < 0 then Econst(1l,destr,destl) else Econst(0l,destr,destl)
          |(e1,e2) -> let r1 = Register.fresh() in
            let newl = generate (Embinop(Msetl,r1,destr,destl)) in
            let i = expr varreg e1 r1 newl in
            let newl2 = generate(i) in
            expr varreg e2 destr newl2 end
      | Ptree.Ble -> begin match (e1.expr_node,e2.expr_node) with
          |(Econst m, Econst n) -> if Int32.compare m n <= 0 then Econst(1l,destr,destl) else Econst(0l,destr,destl)
          |(e1,e2) -> let r1 = Register.fresh() in
            let newl = generate (Embinop(Msetle,r1,destr,destl)) in
            let i = expr varreg e1 r1 newl in
            let newl2 = generate(i) in
            expr varreg e2 destr newl2 end
      | Ptree.Bgt -> begin match (e1.expr_node,e2.expr_node) with
          |(Econst m, Econst n) -> if Int32.compare m n > 0 then Econst(1l,destr,destl) else Econst(0l,destr,destl)
          |(e1,e2) -> let r1 = Register.fresh() in
            let newl = generate (Embinop(Msetg,r1,destr,destl)) in
            let i = expr varreg e1 r1 newl in
            let newl2 = generate(i) in
            expr varreg e2 destr newl2 end
      | Ptree.Bge -> begin match (e1.expr_node,e2.expr_node) with
          |(Econst m, Econst n) -> if Int32.compare m n >= 0 then Econst(1l,destr,destl) else Econst(0l,destr,destl)
          |(e1,e2) -> let r1 = Register.fresh() in
            let newl = generate (Embinop(Msetge,r1,destr,destl)) in
            let i = expr varreg e1 r1 newl in
            let newl2 = generate(i) in
            expr varreg e2 destr newl2 end
      |Ptree.Band -> let falsel=generate(Econst(0l,destr,destl)) in
        let truel=generate(Econst(1l,destr,destl)) in
        condition varreg (Ttree.Ebinop (Ptree.Band, e1, e2)) truel falsel

      |Ptree.Bor -> let falsel=generate(Econst(0l,destr,destl)) in
        let truel=generate(Econst(1l,destr,destl)) in
        condition varreg (Ttree.Ebinop (Ptree.Bor, e1, e2)) truel falsel end

  |Ttree.Ecall(id,exprlist) -> let result = Register.fresh() in
    let endcall = Label.fresh() in
    let rec aux nextl (exprlist:Ttree.expr list) reglist = match exprlist with
      |[]->(reglist,(Egoto nextl))
      |e::[]-> let r = Register.fresh() in
      (r::reglist,expr varreg e.expr_node r nextl)
      |e::q -> let r = Register.fresh() in
        let i = expr varreg e.expr_node r nextl in
        let newl = generate i in
        aux newl q (r::reglist)
    in let (reglist,i) = aux endcall exprlist [] in
    (graph := Label.M.add endcall (Ecall(destr, id,reverse reglist,destl)) !graph; i)
  |Ttree.Esizeof s -> Econst (Int32.mul (Int32.of_int 8) s.str_size,destr,destl)




  (*où e est l'expression à traduire, destr le registre de destination de la valeur de cette expression
    et destl l'étiquette où il faut transférer ensuite le contrôle.*)

and condition varreg (e:Ttree.expr_node) truel falsel : instr = match e with
  | Econst n -> if Int32.equal n 0l then (Egoto falsel) else (Egoto truel)
  | Eunop (op,e) -> begin match op with
    |Ptree.Unot -> condition varreg e.expr_node falsel truel
    |Ptree.Uminus -> condition varreg e.expr_node truel falsel end
    | Ebinop (op, e1, e2) -> begin match op with
      |Ptree.Badd -> begin match (e1.expr_node,e2.expr_node) with
          |(Ttree.Econst m, Ttree.Econst n)-> if Int32.add m n == 0l then Egoto truel else Egoto falsel
          |(Ttree.Econst 0l, e) -> condition varreg e truel falsel
          |(e, Ttree.Econst 0l) -> condition varreg e truel falsel

          |(e1,e2) -> let r1 = Register.fresh() in
            let r2 = Register.fresh() in
            let newl = generate (Emubranch(Mjnz,r2,truel,falsel)) in
            let newl2 = generate (Embinop(Madd,r1,r2,newl)) in
            let i = expr varreg e1 r1 newl2 in
            let newl3 = generate(i) in
            expr varreg e2 r2 newl3 end

      |Ptree.Bsub -> begin match (e1.expr_node,e2.expr_node) with
          |(Ttree.Econst m, Ttree.Econst n)-> if Int32.sub m n == 0l then Egoto truel else Egoto falsel
          |(e, Ttree.Econst 0l) -> condition varreg e truel falsel
          |(e1,e2) -> let r1 = Register.fresh() in
            let r2 = Register.fresh() in
            let newl = generate (Emubranch(Mjnz,r2,truel,falsel)) in
            let newl2 = generate (Embinop(Msub,r1,r2,newl)) in
            let i = expr varreg e1 r1 newl2 in
            let newl3 = generate(i) in
            expr varreg e2 r2 newl3 end
      |Ptree.Bmul -> begin match (e1.expr_node,e2.expr_node) with
          |(Ttree.Econst m, Ttree.Econst n)-> if Int32.mul m n == 0l then Egoto truel else Egoto falsel
          |(e, Ttree.Econst 1l) -> condition varreg e truel falsel
          |(Ttree.Econst 1l, e) -> condition varreg e truel falsel
          |(e1,e2) -> let r1 = Register.fresh() in
            let r2 = Register.fresh() in
            let newl = generate (Emubranch(Mjnz,r2,truel,falsel)) in
            let newl2 = generate (Embinop(Mmul,r1,r2,newl)) in
            let i = expr varreg e1 r1 newl2 in
            let newl3 = generate(i) in
            expr varreg e2 r2 newl3 end
      |Ptree.Bdiv -> begin match (e1.expr_node,e2.expr_node) with
          |(Ttree.Econst m, Ttree.Econst n)-> if Int32.div m n == 0l then Egoto truel else Egoto falsel
          |(e, Ttree.Econst 1l) -> condition varreg e truel falsel
          |(e1,e2) -> let r1 = Register.fresh() in
            let r2 = Register.fresh() in
            let newl = generate (Emubranch(Mjnz,r2,truel,falsel)) in
            let newl2 = generate (Embinop(Msub,r1,r2,newl)) in
            let i = expr varreg e1 r1 newl2 in
            let newl3 = generate(i) in
            expr varreg e2 r2 newl3 end
      | Ptree.Beq -> begin match (e1.expr_node,e2.expr_node) with
          |(Econst m, Econst n) -> if Int32.compare m n == 0 then Egoto truel else Egoto falsel
          |(e1,e2) -> let r1 = Register.fresh() in
            let r2 = Register.fresh() in
            let newl = generate (Emubranch(Mjz,r2,truel,falsel)) in
            let newl2 = generate(Embinop(Msub,r1,r2,newl)) in
            let i = expr varreg e1 r1 newl2 in
            let newl3 = generate(i) in
            expr varreg e2 r2 newl3 end
      | Ptree.Bneq -> begin match (e1.expr_node,e2.expr_node) with
          |(Econst m, Econst n) -> if Int32.compare m n == 0 then Egoto falsel else Egoto truel
          |(e1,e2) -> let r1 = Register.fresh() in
            let r2 = Register.fresh() in
            let newl = generate (Emubranch(Mjz,r2,falsel,truel)) in
            let newl2 = generate(Embinop(Msub,r1,r2,newl)) in
            let i = expr varreg e1 r1 newl2 in
            let newl3 = generate(i) in
            expr varreg e2 r2 newl3 end
      | Ptree.Blt -> begin match (e1.expr_node,e2.expr_node) with
          |(Econst m, Econst n) -> if Int32.compare m n < 0 then Egoto truel else Egoto falsel
          |(e1,e2) -> let r1 = Register.fresh() in
            let r2 = Register.fresh() in
            let newl = generate (Embbranch(Mjl,r2,r1,truel,falsel)) in
            let i = expr varreg e1 r1 newl in
            let newl2 = generate(i) in
            expr varreg e2 r2 newl2 end
      | Ptree.Ble -> begin match (e1.expr_node,e2.expr_node) with
          |(Econst m, Econst n) -> if Int32.compare m n <= 0 then Egoto truel else Egoto falsel
          |(Econst n, e) -> let r = Register.fresh() in
            let newl = generate (Emubranch(Mjgi n,r,falsel,truel)) in
            expr varreg e r newl
          |(e, Econst n) -> let r = Register.fresh() in
            let newl = generate (Emubranch(Mjlei n,r,truel,falsel) )in
                expr varreg e r newl
          |(e1,e2) -> let r1 = Register.fresh() in
            let r2 = Register.fresh() in
            let newl = generate (Embbranch(Mjle,r2,r1,truel,falsel)) in
            let i = expr varreg e1 r1 newl in
            let newl2 = generate(i) in
            expr varreg e2 r2 newl2 end
      | Ptree.Bgt -> begin match (e1.expr_node,e2.expr_node) with
          |(Econst m, Econst n) -> if Int32.compare m n > 0 then Egoto truel else Egoto falsel
          |(Econst n, e) -> let r = Register.fresh() in
            let newl = generate (Emubranch(Mjlei n,r,falsel,truel)) in
            expr varreg e r newl
          |(e, Econst n) -> let r = Register.fresh() in (*ce generate marche pas*)
            let newl = generate (Emubranch(Mjgi n,r,truel,falsel)) in
            expr varreg e r newl
          |(e1,e2) -> let r1 = Register.fresh() in
            let r2 = Register.fresh() in
            let newl = generate (Embbranch(Mjl,r1,r2,truel,falsel)) in
            let i = expr varreg e1 r1 newl in
            let newl2 = generate(i) in
            expr varreg e2 r2 newl2 end
      | Ptree.Bge -> begin match (e1.expr_node,e2.expr_node) with
          |(Econst m, Econst n) -> if Int32.compare m n >= 0 then Egoto truel else Egoto falsel
          |(e1,e2) -> let r1 = Register.fresh() in
            let r2 = Register.fresh() in
            let newl = generate (Embbranch(Mjle,r1,r2,truel,falsel)) in
            let i = expr varreg e1 r1 newl in
            let newl2 = generate(i) in
            expr varreg e2 r2 newl2 end
      |Ptree.Band -> condition varreg e1.expr_node (generate(condition varreg e2.expr_node truel falsel)) falsel
      |Ptree.Bor -> condition varreg e1.expr_node truel (generate(condition varreg e2.expr_node truel falsel)) end
                                 (*)|Ecall (id,exprlist)-> let result = Register.fresh() in
    let newl1 = generate (Emubranch(Mjnz,result,truel,falsel)) in
    let endcall = Label.fresh() in
    let rec aux nextl (exprlist:Ttree.expr list) reglist = match exprlist with
      |e::[]-> let r = Register.fresh() in
        (r::reglist,expr varreg e.expr_node r nextl)
      |e::q -> let r = Register.fresh() in
        let i = expr varreg e.expr_node r nextl in
        let newl = generate i in
        aux newl q (r::reglist)
    in let (reglist,i) = aux endcall exprlist [] in
    (graph := Label.M.add endcall (Ecall(result, id,reverse reglist,newl1)) !graph; i)
  | Eaccess_local id -> Emubranch(Mjnz,Hashtbl.find varreg id,truel,falsel)
  | Eaccess_field (e,field) -> let result = Register.fresh() in
    let newl = generate (Emubranch(Mjnz,result,truel,falsel)) in
    let t = e.expr_typ in
    begin match t with
      |Tstructp s -> let f = Hashtbl.find s.str_fields field.field_name in
        let r = Register.fresh() in
        let i = Eload(r,8*f.field_pos,result,newl) in
        let newl2 = generate i in
        expr varreg e.expr_node r newl2
      |_ -> assert(false) end
  | Eassign_local (id,e)-> let r = Register.fresh() in
    let newl = generate (Emubranch(Mjnz,r,truel,falsel)) in
    let newl2 = generate(Embinop(Mmov,r,Hashtbl.find varreg id, newl)) in
    expr varreg e.expr_node r newl2


  | Eassign_field (e1,field,e2)->assert(false)
  | Esizeof s->assert(false)*)
  |e -> let r=Register.fresh() in
    let newl = generate (Emubranch(Mjnz,r,truel,falsel)) in
    expr varreg e r newl



let reg_alloc_for_var varreg (l: Ttree.decl_var list): register list =
  let rec aux_reg_alloc m l = match l with
    |[] -> m
    |t::q -> let r = Register.fresh() in (Hashtbl.add varreg (snd t) r; aux_reg_alloc (r::m) q)
  in aux_reg_alloc [] l





let rec stmt varreg (s : Ttree.stmt) (destl:label) (retr:register) (exitl:label) : instr = match s with
  | Sskip -> Egoto destl
  | Sexpr e -> let r = Register.fresh() in expr varreg e.expr_node r destl (*générer new register ou garder retr ?*)
  | Sif (e, s1, s2) -> let i1 = stmt varreg s1 destl retr exitl in
    let i2 = stmt varreg s2 destl retr exitl in
    let truel = generate i1 in
    let falsel = generate i2 in
    condition varreg e.expr_node truel falsel
  | Swhile (e,s) -> let whilel = Label.fresh() in
    let i = stmt varreg s whilel retr exitl in
    let truel = generate i in
    let i2 = condition varreg e.expr_node truel destl in
    (graph := Label.M.add whilel i2 !graph; Egoto whilel)

(*let whilel = Label.fresh() in
    let i = stmt varreg s whilel retr exitl in
    let truel = generate i in
    (graph := Label.M.add whilel (condition varreg e.expr_node truel destl) !graph;
                      Egoto whilel)*)

  | Sblock block ->
    let (var,body) = block in
    let varlist = reg_alloc_for_var varreg var in
    block_to_cfg varreg destl retr body(*à quel niveau je gère les variables ? là dans ma fonction j'ai  une table var-reg et une liste de reg. Gérer un block c'est presque appeler une fonction interne*)
  | Sreturn e -> expr varreg e.expr_node retr exitl

(* s est l'instruction à traduire et destl l'étiquette où il faut transférer ensuite le contrôle. Lorsque l'instruction est return,
   la valeur renvoyée doit être mise dans le registre retr et le contrôle doit être passé à l'étiquette exitl. *)

(* Écrire une fonction deffun qui traduit une fonction mini-C vers le type Rtltree.deffun des fonctions RTL.
   Il suffit de créer un pseudo-registre pour le résultat et une étiquette pour la sortie,
   avant d'appeler la fonction précédente sur le corps de la fonction mini-C.

   Écrire enfin une fonction qui traduit un programme mini-C vers le type Rtltree.file, en traduisant chacune des fonctions.

*)

and  block_to_cfg varreg exitl result (b:Ttree.stmt list) : instr =
  let rec aux exitl nextl result l = match l with
    |[] -> assert(false)
    |t::[] -> stmt varreg t nextl result exitl
    |t::q -> let i = stmt varreg t nextl result exitl in
      let newl = generate i in
      aux exitl newl result q
  in aux exitl exitl result (reverse b)




let body_to_cfg varreg entryl exitl result (b:Ttree.stmt list) =
  let rec aux exitl nextl result l = match l with
    |[] -> assert(false)
    |t::[] -> let i = stmt varreg t nextl result exitl in
              graph := Label.M.add entryl i !graph
    |t::q -> let i = stmt varreg t nextl result exitl in
      let newl = generate i in
      aux exitl newl result q
  in aux exitl exitl result (reverse b)







(*Production de code*)
(*D'une fonction de Ttree à une vraie fonction*)
(*Allouer pseudo-reg frais (Register.fresh()) pour args, result et vars,
  On part d'un graphe vide avec new label L2(Label.fresh()) pour la sortie
  Le résultat est le label d'entrée L1*)
let declfun_to_deffun (f:Ttree.decl_fun) : deffun =
  let entryl = Label.fresh() in
  let exitl = Label.fresh() in
  let result = Register.fresh() in
  let varreg = Hashtbl.create 100 in
  let args = reg_alloc_for_var varreg f.fun_formals in
  let (var,body) = f.fun_body in

  let varloc = reg_alloc_for_var varreg var in

  (*graph := Label.M.empty;*)
  body_to_cfg varreg entryl exitl result body;
  {fun_name   = f.fun_name;
  fun_formals = reverse args;
  fun_result  = result;
  fun_locals  = Register.set_of_list varloc;
  (* toutes les variables locales de la fonction maintenant regroupées ici *)
  fun_entry   = entryl;
  fun_exit    = exitl;
  fun_body    = !graph;}

(*D'un Ttree.file à une liste de fonction*)
let program (l:Ttree.file) : file =
  let rec aux_tree_to_rtl m l = match l with
    |[]-> m
    |t::q -> let f = declfun_to_deffun t in aux_tree_to_rtl (f::m) q
  in {funs = aux_tree_to_rtl [] l}
