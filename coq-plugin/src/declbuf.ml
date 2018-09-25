(* In Coq's implementation, a kernel name is represented by ModPath, DirPath, Labels, ...
 * If we directly translate these structures into holboost, the later will become very
 * complicated and in turn hard to be adapted to other HOL provers, i.e. Isabelle. Consequently,
 * we use a buffer here, implemented in the Coq plugin, to map the names (in string) to the
 * kernel names of declarations
 *)

(* this implementation is NOT thread-safe due to a global static buffer *)

type decl =
    | ConstantDecl of Names.constant
    | MutindDecl of Names.mutual_inductive


module DeclBuf = Map.Make(String)

let buf : decl DeclBuf.t ref = ref DeclBuf.empty

let set (name: string) (declaration: decl) : unit =
    if DeclBuf.mem name (!buf) then
        (* FIXME check with the correctness *)
        (* we do not replace existing items in the buffer *)
        ()
    else
        buf := DeclBuf.add name declaration (!buf)

let get (name: string) : decl option =
    try
        Some (DeclBuf.find name (!buf))
    with
        Not_found -> None
