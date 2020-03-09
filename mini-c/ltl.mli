type arcs = { prefs: Register.set; intfs: Register.set }
type igraph = arcs Register.map

val make: Ertltree.live_info Label.map -> igraph

val program: Ertltree.file -> Ltltree.file
