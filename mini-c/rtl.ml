open Rtltree

(*le control flow graph est stocké dans une variable globale*)
let graph = ref Label.M.empty

(*Génère une étiquette et met i dans le graphe avec cette étiquette, puis renvoie l'étiquette *)
let generate i =
  let l = Label.fresh () in
  graph := Label.M.add l i !graph;
  l

(*Quelques fonctions de base*)
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

exception Division_by_zero

(*Traduction des expressions en instructions*)
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
  | Eunop (unop,e) -> let ee = expr varreg e.expr_node destr destl in
    begin match ee with
      |Econst(n,_,l)-> if l==destl then begin match unop with
          |Ptree.Unot -> if Int32.equal n 0l then Econst(1l,destr,destl) else Econst(0l,destr,destl)
          |Ptree.Uminus -> Econst(Int32.neg n,destr,destl) end
        else begin match unop with
          |Ptree.Unot -> let newl = generate(Emunop(Msetei 0l,destr,destl)) in
            expr varreg e.expr_node destr newl
          |Ptree.Uminus -> let rzero = Register.fresh() in
            let newl = generate(Embinop(Msub,rzero,destr,destl)) in
            let newl2 = generate(Econst(0l,destr,newl)) in
            expr varreg e.expr_node rzero newl2 end
      |_ -> begin match unop with
          |Ptree.Unot -> let newl = generate(Emunop(Msetei 0l,destr,destl)) in
            expr varreg e.expr_node destr newl
          |Ptree.Uminus -> let rzero = Register.fresh() in
            let newl = generate(Embinop(Msub,rzero,destr,destl)) in
            let newl2 = generate(Econst(0l,destr,newl)) in
            expr varreg e.expr_node rzero newl2 end end
  | Ebinop (binop,e1,e2) -> begin
      let ee1 = expr varreg e1.expr_node destr destl in (*Les instructions construites ici ne seront pas utilisées*)
      let ee2 = expr varreg e2.expr_node destr destl in
      match (ee1,ee2) with
      |(Econst(n1,_,l1),Econst(n2,_,l2))-> if l1==destl then begin
          if l2==destl then begin try Econst (cc binop n1 n2, destr, destl)
            with Division_by_zero -> let r = Register.fresh() in
              let newl = generate(Embinop(Mdiv,r,destr,destl)) in
              let newl2 = generate(Econst(n1,destr,newl)) in
              Econst(n2,r,newl2) end
          else ce varreg binop n1 e2 destr destl end
        else begin
          if l2==destl then ec varreg binop e1 n2 destr destl
          else ee varreg binop e1 e2 destr destl end
      |(Econst(n,_,l),_)-> if l==destl then ce varreg binop n e2 destr destl
        else ee varreg binop e1 e2 destr destl
      |(_,Econst(n,_,l))-> if l==destl then ec varreg binop e1 n destr destl
        else ee varreg binop e1 e2 destr destl
      |(_,_)->ee varreg binop e1 e2 destr destl end
  |Ttree.Ecall(id,exprlist) ->
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

(*Fonctions pour l'optimisation des opérations binaires*)
and cc b m n = match b with
  |Ptree.Beq -> if Int32.equal m n then 1l else 0l
  |Ptree.Bneq -> if Int32.equal m n then 0l else 1l
  |Ptree.Blt -> if Int32.compare m n < 0 then 1l else 0l
  |Ptree.Ble -> if Int32.compare m n <= 0 then 1l else 0l
  |Ptree.Bgt -> if Int32.compare m n > 0 then 1l else 0l
  |Ptree.Bge -> if Int32.compare m n >= 0 then 1l else 0l
  |Ptree.Badd -> Int32.add m n
  |Ptree.Bsub -> Int32.sub m n
  |Ptree.Bmul -> Int32.mul m n
  |Ptree.Bdiv -> if n=0l then raise Division_by_zero
    else Int32.div m n
  |Ptree.Band -> if Int32.equal m 0l || Int32.equal n 0l then 0l else 1l
  |Ptree.Bor -> if Int32.equal m 0l && Int32.equal n 0l then 0l else 1l

and ce varreg b n e destr destl =
  match b with
  |Ptree.Beq -> let newl = generate(Emunop(Msetei n,destr,destl)) in
    expr varreg e.expr_node destr newl
  |Ptree.Bneq -> let newl = generate(Emunop(Msetnei n,destr,destl)) in
    expr varreg e.expr_node destr newl
  |Ptree.Blt -> let r = Register.fresh() in
    let newl = generate(Embinop(Msetl,r,destr,destl)) in
    let newl2 = generate(Econst(n,r,newl)) in
    expr varreg e.expr_node destr newl2
  |Ptree.Ble -> let r = Register.fresh() in
    let newl = generate(Embinop(Msetle,r,destr,destl)) in
    let newl2 = generate(Econst(n,r,newl)) in
    expr varreg e.expr_node destr newl2
  |Ptree.Bgt -> let r = Register.fresh() in
    let newl = generate(Embinop(Msetg,r,destr,destl)) in
    let newl2 = generate(Econst(n,r,newl)) in
    expr varreg e.expr_node destr newl2
  |Ptree.Bge -> let r = Register.fresh() in
    let newl = generate(Embinop(Msetge,r,destr,destl)) in
    let newl2 = generate(Econst(n,r,newl)) in
    expr varreg e.expr_node destr newl2
  |Ptree.Badd -> if Int32.equal n 0l then expr varreg e.expr_node destr destl
    else let newl = generate(Emunop(Maddi n,destr,destl)) in
      expr varreg e.expr_node destr newl
  |Ptree.Bsub -> let r = Register.fresh() in
    let newl = generate(Embinop(Msub,r,destr,destl)) in
    let newl2 = generate(Econst(n,destr,newl)) in
    expr varreg e.expr_node r newl2
  |Ptree.Bmul -> if Int32.equal n 0l then Econst(0l,destr,destl)
    else begin if Int32.equal n 1l then expr varreg e.expr_node destr destl
      else let r = Register.fresh() in
        let newl = generate(Embinop(Mmul,r,destr,destl)) in
        let newl2 = generate(Econst(n,r,newl)) in
        expr varreg e.expr_node destr newl2 end
  |Ptree.Bdiv -> let r = Register.fresh() in
    let newl = generate(Embinop(Mdiv,r,destr,destl)) in
    let newl2 = generate(Econst(n,destr,newl)) in
    expr varreg e.expr_node r newl2
  |Ptree.Band -> if Int32.equal n 0l then Econst(0l,destr,destl) else
      let falsel=generate(Econst(0l,destr,destl)) in
      let truel=generate(Econst(1l,destr,destl)) in
      condition varreg e.expr_node truel falsel
  |Ptree.Bor -> if Int32.equal n 0l then
      let falsel=generate(Econst(0l,destr,destl)) in
      let truel=generate(Econst(1l,destr,destl)) in
      condition varreg e.expr_node truel falsel
    else Econst(1l,destr,destl)

and ec varreg b e n destr destl =
  match b with
  |Ptree.Beq -> let newl = generate(Emunop(Msetei n,destr,destl)) in
    expr varreg e.expr_node destr newl
  |Ptree.Bneq -> let newl = generate(Emunop(Msetnei n,destr,destl)) in
    expr varreg e.expr_node destr newl
  |Ptree.Blt -> let r = Register.fresh() in
    let newl = generate(Embinop(Msetl,r,destr,destl)) in
    let newl2 = generate(Econst(n,destr,newl)) in
    expr varreg e.expr_node r newl2
  |Ptree.Ble -> let r = Register.fresh() in
    let newl = generate(Embinop(Msetle,r,destr,destl)) in
    let newl2 = generate(Econst(n,destr,newl)) in
    expr varreg e.expr_node r newl2
  |Ptree.Bgt -> let r = Register.fresh() in
    let newl = generate(Embinop(Msetg,r,destr,destl)) in
    let newl2 = generate(Econst(n,destr,newl)) in
    expr varreg e.expr_node r newl2
  |Ptree.Bge -> let r = Register.fresh() in
    let newl = generate(Embinop(Msetge,r,destr,destl)) in
    let newl2 = generate(Econst(n,destr,newl)) in
    expr varreg e.expr_node r newl2
  |Ptree.Badd -> if Int32.equal n 0l then expr varreg e.expr_node destr destl
    else let newl = generate(Emunop(Maddi n,destr,destl)) in
      expr varreg e.expr_node destr newl
  |Ptree.Bsub -> if Int32.equal n 0l then expr varreg e.expr_node destr destl
    else let newl = generate(Emunop(Maddi (Int32.neg n),destr,destl)) in
      expr varreg e.expr_node destr newl
  |Ptree.Bmul -> if Int32.equal n 0l then Econst(0l,destr,destl)
    else begin if Int32.equal n 1l then expr varreg e.expr_node destr destl
      else let r = Register.fresh() in
        let newl = generate(Embinop(Mmul,r,destr,destl)) in
        let newl2 = generate(Econst(n,r,newl)) in
        expr varreg e.expr_node destr newl2 end
  |Ptree.Bdiv -> if Int32.equal n 1l then expr varreg e.expr_node destr destl
    else let r = Register.fresh() in
      let newl = generate(Embinop(Mdiv,r,destr,destl)) in
      let newl2 = generate(Econst(n,r,newl)) in
      expr varreg e.expr_node destr newl2
  |Ptree.Band -> let falsel=generate(Econst(0l,destr,destl)) in
    let truel=generate(Econst(1l,destr,destl)) in
    condition varreg (Ttree.Ebinop (Ptree.Band, e, {expr_node=Econst(n);expr_typ=Tint})) truel falsel
  |Ptree.Bor -> let falsel=generate(Econst(0l,destr,destl)) in
    let truel=generate(Econst(1l,destr,destl)) in
    condition varreg (Ttree.Ebinop (Ptree.Bor, e, {expr_node=Econst(n);expr_typ=Tint})) truel falsel

and ee varreg b e1 e2 destr destl =
  match b with
  |Ptree.Beq -> let r1 = Register.fresh() in
    let newl = generate (Embinop(Msete,r1,destr,destl)) in
    let i = expr varreg e1.expr_node r1 newl in
    let newl2 = generate(i) in
    expr varreg e2.expr_node destr newl2
  |Ptree.Bneq -> let r1 = Register.fresh() in
    let newl = generate (Embinop(Msetne,r1,destr,destl)) in
    let i = expr varreg e1.expr_node r1 newl in
    let newl2 = generate(i) in
    expr varreg e2.expr_node destr newl2
  |Ptree.Blt -> let r1 = Register.fresh() in
    let newl = generate (Embinop(Msetl,r1,destr,destl)) in
    let i = expr varreg e1.expr_node r1 newl in
    let newl2 = generate(i) in
    expr varreg e2.expr_node destr newl2
  |Ptree.Ble -> let r1 = Register.fresh() in
    let newl = generate (Embinop(Msetle,r1,destr,destl)) in
    let i = expr varreg e1.expr_node r1 newl in
    let newl2 = generate(i) in
    expr varreg e2.expr_node destr newl2
  |Ptree.Bgt -> let r1 = Register.fresh() in
    let newl = generate (Embinop(Msetg,r1,destr,destl)) in
    let i = expr varreg e1.expr_node r1 newl in
    let newl2 = generate(i) in
    expr varreg e2.expr_node destr newl2
  |Ptree.Bge -> let r1 = Register.fresh() in
    let newl = generate (Embinop(Msetge,r1,destr,destl)) in
    let i = expr varreg e1.expr_node r1 newl in
    let newl2 = generate(i) in
    expr varreg e2.expr_node destr newl2
  |Ptree.Badd -> let r1 = Register.fresh() in
    let newl = generate (Embinop(Madd,r1,destr,destl)) in
    let i = expr varreg e1.expr_node r1 newl in
    let newl2 = generate(i) in
    expr varreg e2.expr_node destr newl2
  |Ptree.Bsub -> let r2 = Register.fresh() in
    let newl = generate (Embinop(Msub,r2,destr,destl)) in
    let i = expr varreg e1.expr_node destr newl in
    let newl2 = generate(i) in
    expr varreg e2.expr_node r2 newl2
  |Ptree.Bmul -> let r1 = Register.fresh() in
    let newl = generate (Embinop(Mmul,r1,destr,destl)) in
    let i = expr varreg e1.expr_node r1 newl in
    let newl2 = generate(i) in
    expr varreg e2.expr_node destr newl2
  |Ptree.Bdiv -> let r2 = Register.fresh() in
    let newl = generate (Embinop(Mdiv,r2,destr,destl)) in
    let i = expr varreg e1.expr_node destr newl in
    let newl2 = generate(i) in
    expr varreg e2.expr_node r2 newl2
  |Ptree.Band -> let falsel=generate(Econst(0l,destr,destl)) in
    let truel=generate(Econst(1l,destr,destl)) in
    condition varreg (Ttree.Ebinop (Ptree.Band, e1, e2)) truel falsel
  |Ptree.Bor -> let falsel=generate(Econst(0l,destr,destl)) in
    let truel=generate(Econst(1l,destr,destl)) in
    condition varreg (Ttree.Ebinop (Ptree.Bor, e1, e2)) truel falsel

(*Si e est non-nul truel sinon falsel
  Disjonction des cas pour optimiser*)
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
          |_ -> let r=Register.fresh() in
            let newl = generate (Emubranch(Mjnz,r,truel,falsel)) in
            expr varreg e r newl end
      |Ptree.Bsub -> begin match (e1.expr_node,e2.expr_node) with
          |(Ttree.Econst m, Ttree.Econst n)-> if Int32.sub m n == 0l then Egoto truel else Egoto falsel
          |(e, Ttree.Econst 0l) -> condition varreg e truel falsel
          |_ -> let r=Register.fresh() in
            let newl = generate (Emubranch(Mjnz,r,truel,falsel)) in
            expr varreg e r newl end
      |Ptree.Bmul -> begin match (e1.expr_node,e2.expr_node) with
          |(Ttree.Econst m, Ttree.Econst n)-> if Int32.mul m n == 0l then Egoto truel else Egoto falsel
          |(e, Ttree.Econst 1l) -> condition varreg e truel falsel
          |(Ttree.Econst 1l, e) -> condition varreg e truel falsel
          |_ -> let r=Register.fresh() in
            let newl = generate (Emubranch(Mjnz,r,truel,falsel)) in
            expr varreg e r newl end
      |Ptree.Bdiv -> begin match (e1.expr_node,e2.expr_node) with
          |(Ttree.Econst m, Ttree.Econst n)-> if Int32.div m n == 0l then Egoto truel else Egoto falsel
          |(e, Ttree.Econst 1l) -> condition varreg e truel falsel
          |_ -> let r=Register.fresh() in
            let newl = generate (Emubranch(Mjnz,r,truel,falsel)) in
            expr varreg e r newl end
      | Ptree.Beq -> begin match (e1.expr_node,e2.expr_node) with
          |(Econst m, Econst n) -> if Int32.compare m n == 0 then Egoto truel else Egoto falsel
          |_ -> let r=Register.fresh() in
            let newl = generate (Emubranch(Mjnz,r,truel,falsel)) in
            expr varreg e r newl end
      | Ptree.Bneq -> begin match (e1.expr_node,e2.expr_node) with
          |(Econst m, Econst n) -> if Int32.compare m n == 0 then Egoto falsel else Egoto truel
          |_ -> let r=Register.fresh() in
            let newl = generate (Emubranch(Mjnz,r,truel,falsel)) in
            expr varreg e r newl end
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
  |e -> let r=Register.fresh() in
    let newl = generate (Emubranch(Mjnz,r,truel,falsel)) in
    expr varreg e r newl

(*Transforme les arguments et variables locales en registres,
  remplit varreg pour faire le lien entre les deux*)
let reg_alloc_for_var varreg (l: Ttree.decl_var list): register list =
  let rec aux_reg_alloc m l = match l with
    |[] -> m
    |t::q -> let r = Register.fresh() in (Hashtbl.add varreg (snd t) r; aux_reg_alloc (r::m) q)
  in aux_reg_alloc [] l

(*Traduit les stmt en instruction*)
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
  | Sblock block ->
    let (var,body) = block in
    let _ = reg_alloc_for_var varreg var in
    block_to_cfg varreg destl retr body
  | Sreturn e -> expr varreg e.expr_node retr exitl

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

let declfun_to_deffun (f:Ttree.decl_fun) : deffun =
  let entryl = Label.fresh() in
  let exitl = Label.fresh() in
  let result = Register.fresh() in
  let varreg = Hashtbl.create 100 in
  let args = reg_alloc_for_var varreg f.fun_formals in
  let (var,body) = f.fun_body in
  let varloc = reg_alloc_for_var varreg var in
  graph := Label.M.empty;
  body_to_cfg varreg entryl exitl result body;
  {fun_name   = f.fun_name;
   fun_formals = reverse args;
   fun_result  = result;
   fun_locals  = Register.set_of_list varloc;
   fun_entry   = entryl;
   fun_exit    = exitl;
   fun_body    = !graph;}

let program (l:Ttree.file) : file =
  let rec aux_tree_to_rtl m l = match l with
    |[]-> m
    |t::q -> let f = declfun_to_deffun t in aux_tree_to_rtl (f::m) q
  in {funs = aux_tree_to_rtl [] l}
