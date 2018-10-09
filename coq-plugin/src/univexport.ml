open Yojson.Basic

module IntMap = Map.Make(Int)

let univ_buffer : Univ.universe IntMap.t ref = ref IntMap.empty

let universe_export (univ:Univ.universe option) : json =
    match univ with
    | None -> `Null
    | Some univ -> begin
        (* type of univ is Univ.Universe.Expr.t list *)
        let hash = Univ.Universe.hash univ in
        if IntMap.mem hash !univ_buffer then
            ()
        else
            univ_buffer := IntMap.add hash univ !univ_buffer
        ;
        `Int hash
    end

let universe_obtain (hash:int) : Univ.universe =
    IntMap.find hash !univ_buffer


let univ_inst_buffer : Univ.Instance.t IntMap.t ref = ref IntMap.empty

let universe_inst_export (univ_inst: Univ.Instance.t) : json =
    let hash = Univ.Instance.hash univ_inst in
    if IntMap.mem hash !univ_inst_buffer then
        ()
    else
        univ_inst_buffer := IntMap.add hash univ_inst !univ_inst_buffer
    ;
    `Int hash

let universe_inst_obtain (hash:int) : Univ.Instance.t = IntMap.find hash !univ_inst_buffer
