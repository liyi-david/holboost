(*
 * Specification of exported json
 * 
 *)

open Yojson.Basic
open Hbcommon

let json_of_nullable_name (name: Names.Name.t) : json =
    match name with
    | Names.Name.Anonymous -> `Null
    | Names.Name.Name id -> `String (Names.Id.to_string id)

let constr2json (c: Constr.t) : json =
    let rec convert (c: Constr.t) : json = 
        let open Constr in
        `Assoc begin
            match (kind c) with
            | Rel index ->  [ ("type", `String "rel"); ("index", `Int (index - 1)) ] 
            | Var id -> [ ("type", `String "var"); ("name", `String (Names.Id.to_string id)) ]
            | Meta index -> [ ("type", `String "meta"); ("name", `Int index) ]
            (* FIXME Evar *)
            | Evar (index, arr) ->
                    [
                        ("type", `String "evar");
                        ("index", `Int (Evar.repr index));
                        ("constrs", `List Array.(to_list (map convert arr)))
                    ]
            | Sort sort ->
                    let comment = ref "" in
                    let sort_name, sort_univ = match sort with
                        | Sorts.Prop Sorts.Pos -> "set", None
                        | Sorts.Prop Sorts.Null -> "prop", None
                        | Sorts.Type univ -> "type", Some univ
                    in
                    [
                        ("type", `String "sort");
                        ("sort", `String sort_name);
                        ("univ", Univexport.universe_export sort_univ);
                        ("comment", `String !comment);
                    ]
            | Cast (c, kind, types) ->
                    let hash_kind = match kind with
                    | VMcast -> 0
                    | NATIVEcast -> 1
                    | DEFAULTcast -> 2
                    | REVERTcast -> 3
                    in
                    [
                        ("type", `String "cast");
                        ("cast_kind", `Int hash_kind);
                        ("body", (convert c));
                        ("guaranteed_type", (convert types))
                    ]
            | Prod (arg_name, arg_type, body) ->
                    [
                        ("type", `String "prod");
                        ("arg_name", (json_of_nullable_name arg_name));
                        ("arg_type", (convert arg_type));
                        ("body", (convert body))
                    ]
            | Lambda (arg_name, arg_type, body) ->
                    [
                        ("type", `String "lambda");
                        ("arg_name", (json_of_nullable_name arg_name));
                        ("arg_type", (convert arg_type));
                        ("body", (convert body))
                    ]
            | LetIn (arg_name, arg_type, arg_body, body) ->
                    [
                        ("type", `String "lambda");
                        ("arg_name", (json_of_nullable_name arg_name));
                        ("arg_type", (convert arg_type));
                        ("arg_body", (convert arg_body));
                        ("body", (convert body))
                    ]
            | App (func, args) ->
                    [
                        ("type", `String "app");
                        ("func", (convert func));
                        ("args", `List Array.(to_list (map begin fun arg -> (convert arg) end args)))
                    ]
            (* FIXME Universe is currently ignored *)
            | Const (const, univ_inst) ->
                    let const_name = (Names.Constant.to_string const) in
                    [
                        ("type", `String "const");
                        ("name", `String const_name);
                        ("univ_inst", Univexport.universe_inst_export univ_inst)
                    ]
            | Ind ((ind, index), univ_inst) ->
                    [
                        ("type", `String "ind");
                        ("mutind_name", `String (Names.MutInd.to_string ind));
                        ("ind_index", `Int index);
                        ("univ_inst", Univexport.universe_inst_export univ_inst)
                    ]
            | Construct (((ind, index), constructor_index), univ_inst) ->
                    (*
                     * according to `kernel/names.ml`, indexes of multiple inductives start from 0 while indexes of constructors start from 1.
                     * to simplify the case, here we decrease the indexes of constructors by 1, consequently all indexes in the exported json
                     * start from 0
                     *)
                    [
                        ("type", `String "construct");
                        ("mutind_name", `String (Names.MutInd.to_string ind));
                        ("ind_index", `Int index);
                        ("constructor_index", `Int (constructor_index - 1));
                        ("univ_inst", Univexport.universe_inst_export univ_inst)
                    ]
            (* TODO CoFix, Proj *)
            (* FIXME Case *)
            | Case (case_info, _, c, ac) ->
                    let open Constr in
                    let cases = Array.map begin fun case ->
                        (convert case)
                    end ac in
                    let json_case_info = `Assoc [
                        ("ndecls", `List (List.map begin fun ndecl -> `Int ndecl end (Array.to_list case_info.ci_cstr_ndecls)));
                    ] in
                    let cases = Array.to_list cases in
                    [
                        ("type", `String "case");
                        ("case_info", json_case_info);
                        ("term_matched", (convert c));
                        ("term_type", (convert (mkInd case_info.ci_ind)));
                        ("cases", `List cases)
                    ]
            (* FIXME Fix *)
            | Fix _ ->
                    [
                        ("type", `String "fix") 
                    ]
            | _ -> raise (SerializingFailure (Printf.sprintf "unhandled constr type %s" (Pp.string_of_ppcmds (Printer.pr_constr c))))
        end
    in
    
    (* we dont catch exceptions here *)
    convert c

let constrexpr2json (c: Constrexpr.constr_expr) : json =
    let sigma, env = begin
        if Proof_global.there_are_pending_proofs () then
            Pfedit.get_current_goal_context () 
        else
            let env = Global.env () in
            (*
             * I copied the `Evd.from_env` part from Pfedit.get_current_context
             * still I don't know why they need a evar_map even when the corresponding
             * environment is already given ...
             *)
            Evd.from_env env, env
    end in
    let (_, t) = (Constrintern.interp_open_constr env sigma c) in
    constr2json (EConstr.Unsafe.to_constr t)

let rec json2econstr (ext: json) : EConstr.t =
    let open Yojson.Basic.Util in
    let open EConstr in
    let term_type : string = ext |> member "type" |> to_string in
    try
        let result : EConstr.t =
            match term_type with
            | "rel" -> mkRel ((ext |> member "index" |> to_int) + 1)
            | "var" -> mkVar (Names.Id.of_string (ext |> member "name" |> to_string))
            | "sort" -> mkSort begin
                let sort_name : string = (ext |> member "sort" |> to_string) in
                match sort_name with
                | "prop" -> Sorts.prop
                | "set"  -> Sorts.set
                | "type" -> Sorts.Type (Univexport.universe_import (ext |> member "univ"))
                | _ -> raise (DeserializingFailure ("unexpected sort name", ext))
            end
            | "prod" ->
                mkProd (
                    (Names.Name.mk_name (Names.Id.of_string (ext |> member "arg_name" |> to_string))),
                    (json2econstr (ext |> member "arg_type")),
                    (json2econstr (ext |> member "body"))
                )
            | "lambda" ->
                mkLambda (
                    (Names.Name.mk_name (Names.Id.of_string (ext |> member "arg_name" |> to_string))),
                    (json2econstr (ext |> member "arg_type")),
                    (json2econstr (ext |> member "body"))
                )
            | "letin" ->
                mkLetIn (
                    (Names.Name.mk_name (Names.Id.of_string (ext |> member "arg_name" |> to_string))),
                    (json2econstr (ext |> member "arg_type")),
                    (json2econstr (ext |> member "arg_body")),
                    (json2econstr (ext |> member "body"))
                )
            | "app" ->
                    let json_args : json list = ext |> member "args" |> to_list in
                    let econstr_args = List.map json2econstr json_args in
                    mkApp (json2econstr (ext |> member "func"), Array.of_list econstr_args)
            | "cast" ->
                    let cast_kind = match (ext |> member "cast_kind" |> to_int) with
                    | 0 -> Constr.VMcast
                    | 1 -> Constr.NATIVEcast
                    | 2 -> Constr.DEFAULTcast
                    | 3 -> Constr.REVERTcast
                    | _ -> raise (DeserializingFailure ("unsupported cast index", (ext |> member "cast_kind")))
                    in
                    mkCast ((json2econstr (ext |> member "body")), cast_kind, (json2econstr (ext |> member "guaranteed_type")))
            | "const" ->
                let name = ext |> member "name" |> to_string in begin
                    match Declbuf.get name with
                    | Some (Declbuf.ConstantDecl const) -> mkConst const 
                    | _ -> raise (DeserializingFailure (Printf.sprintf "const %s not found in the buffer." name, `Null))
                end
            | "ind" ->
                let name = ext |> member "mutind_name" |> to_string in begin
                    match Declbuf.get name with
                    | Some (Declbuf.MutindDecl mutind) -> mkInd (mutind, (ext |> member "ind_index" |> to_int))
                    | _ -> raise (DeserializingFailure (Printf.sprintf "mutind %s not found in the buffer." name, `Null))
                end
            | "construct" ->
                let name = ext |> member "mutind_name" |> to_string in begin
                    match Declbuf.get name with
                    | Some (Declbuf.MutindDecl mutind) -> mkConstruct (
                        (mutind, (ext |> member "ind_index" |> to_int)),
                        (* IMPORTANT: indexes of constructors start from 1 *)
                        (ext |> member "constructor_index" |> to_int) + 1
                    )
                    | _ -> raise (DeserializingFailure (Printf.sprintf "mutind %s not found in the buffer." name, `Null))
                end
            | _ -> raise (DeserializingFailure (Printf.sprintf "unsupported term type %s" term_type, `Null))
        in
            (* HERE is a pre-allocated space for debuging prints ..... *)
            result
    with
        Type_error (msg, _) ->
            raise (DeserializingFailure (msg, ext))
