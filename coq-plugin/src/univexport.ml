open Yojson.Basic
open Hbcommon

module IntMap = Map.Make(Int)

let pr_univ (univ:Univ.universe) : string =
    let levels = Univ.Universe.levels univ in
    Univ.LSet.fold begin fun level s ->
        (Univ.Level.to_string level) ^ " " ^ s
    end levels ""

let level_export (level:Univ.Level.t) : json =
    let level_segments = String.split_on_char '.' (Univ.Level.to_string level) in
    `List List.(map begin fun s -> `String s end level_segments)

let level_import (json_level: json) : Univ.Level.t =
    match json_level with
    | `List elems ->
        let module_list, offset = List.fold_right begin fun level_element level ->
            let module_list, offset = level in
            match level_element with
            | `String ident -> (ident :: module_list, offset)
            | `Int offset' -> (module_list, offset')
            | _ -> raise (DeserializingFailure ("invalid level element", level_element))
        end elems ([], -1) in
        if offset == -1 then
            raise (DeserializingFailure ("level offset missing", json_level))
        else
            Univ.Level.make (Names.DirPath.make (List.rev (List.map (Names.Id.of_string) module_list))) offset
    | _ -> raise (DeserializingFailure ("invalid level", json_level))

let universe_export (univ:Univ.universe option) : json =
    match univ with
    | None -> `Null
    | Some univ -> begin
        (* type of univ is Univ.Universe.Expr.t list *)
        let str_univ = Pp.(string_of_ppcmds (Univ.Universe.pr univ)) in
        let str_exprs =
            if String.equal (String.sub str_univ 0 3) "max" then
                (* in this case the string looks like `max(..., ...)` *)
                String.sub str_univ 4 (String.length str_univ - 5)
            else
                str_univ
        in
        let list_exprs : string list = List.map String.trim (String.split_on_char ',' str_exprs) in
        let json_exprs : json list =
            List.map begin fun expr ->
                let splitted_expr = String.split_on_char '+' expr in
                let str_level, index =
                    if List.length splitted_expr == 1 then
                        List.nth splitted_expr 0, 0
                    else
                        List.nth splitted_expr 0, int_of_string (List.nth splitted_expr 1)
                in
                `List [
                    `List (List.map (fun s -> `String s) (String.split_on_char '.' str_level));
                    `Int index
                ]
            end list_exprs in
        `List json_exprs
    end

let universe_import (json_univ: json) : Univ.universe =
    match json_univ with
    | _ -> Univ.Universe.type1


let universe_inst_export (univ_inst: Univ.Instance.t) : json =
    let levels = Univ.LSet.elements (Univ.Instance.levels univ_inst) in
    let json_levels : json list =
        List.map begin fun level ->
            let level_segments = String.split_on_char '.' (Univ.Level.to_string level) in
            `List List.(map begin fun s -> `String s end level_segments)
        end levels in
    `List json_levels

let universe_inst_import (json_inst: json) : Univ.Instance.t =
    match json_inst with
    | `List levels ->
            Univ.Instance.of_array (Array.of_list (List.map level_import levels))
    | _ -> raise (DeserializingFailure ("invalid universe instance", json_inst))

let univ_constraint_import (json_lc: json) : Univ.univ_constraint =
    let open Yojson.Basic.Util in
    let left = level_import (json_lc |> member "left") in
    let right = level_import (json_lc |> member "right") in
    let opr = match (json_lc |> member "opr" |> to_string) with
    | "<=" -> Univ.Le
    | "<"  -> Univ.Lt
    | _opr -> raise (Hbcommon.SerializingFailure Printf.(sprintf "unsupported level constraint operator %s" _opr))
    in
    (left, opr, right)

let univ_constraints_import (json_lc: json) : Univ.constraints =
    let open Yojson.Basic.Util in
    let ucs = (List.map univ_constraint_import (json_lc |> to_list)) in
    Univ.Constraint.of_list ucs
