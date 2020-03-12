(* 1.1 - Construction du graphe d'interférence *)

type arcs = { prefs: Register.set; intfs: Register.set }
type igraph = arcs Register.map

val make: Ertltree.live_info Label.map -> igraph

(* 1.2 - Coloration du graphe d'interférence *)

type color = Ltltree.operand
type coloring = color Register.map

val color: igraph -> coloring * int

val instr: coloring -> int -> Ertltree.instr -> Ltltree.instr

val program: Ertltree.file -> Ltltree.file
