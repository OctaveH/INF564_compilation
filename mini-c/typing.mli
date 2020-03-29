
exception Error of string * Ptree.loc

val localisation: Ptree.loc -> string -> unit

val program: Ptree.file -> Ttree.file
