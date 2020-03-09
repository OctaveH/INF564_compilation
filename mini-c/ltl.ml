(* 1.1 - Construction du graphe d'interférence *)

type arcs = { prefs: Register.set; intfs: Register.set }
type igraph = arcs Register.map

let make (li:Ertltree.live_info Label.map) : igraph =
  let ig = Register.M.empty in
  ig

let program (ertl_file:Ertltree.file) : Ltltree.file =
  {funs = []}
