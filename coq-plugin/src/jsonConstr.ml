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

let constr2json (sigma: Evd.evar_map) (c: Constr.t) : json =
    let rec convert (c: Constr.t) : json = 
        let open Constr in
        `List begin
            match (kind c) with
            | Rel index -> [ `String "rel"; `Int (index - 1) ] 
            | Var id -> [ `String "var"; `String (Names.Id.to_string id) ]
            | Meta index -> [ `String "meta"; `Int index ]
            | Evar (index, arr) ->
                    let open Evd in
                    let evar_info = find sigma index in
                    [
                        `String "evar";
                        `Int (Evar.repr index);
                        (convert evar_info.evar_concl)
                    ]
            | Sort sort ->
                    let comment = ref "" in
                    let sort_name, sort_univ = match sort with
                        | Sorts.Prop Sorts.Pos -> "set", None
                        | Sorts.Prop Sorts.Null -> "prop", None
                        | Sorts.Type univ -> "type", Some univ
                    in
                    [
                        `String "sort";
                        `String sort_name;
                        JsonUniv.universe_export sort_univ;
                        `String !comment;
                    ]
            | Cast (c, kind, types) ->
                    let hash_kind = match kind with
                    | VMcast -> 0
                    | NATIVEcast -> 1
                    | DEFAULTcast -> 2
                    | REVERTcast -> 3
                    in
                    [
                        `String "cast";
                        `Int hash_kind;
                        (convert c);
                        (convert types)
                    ]
            | Prod (arg_name, arg_type, body) ->
                    [
                        `String "prod";
                        (json_of_nullable_name arg_name);
                        (convert arg_type);
                        (convert body)
                    ]
            | Lambda (arg_name, arg_type, body) ->
                    [
                        `String "lambda";
                        (json_of_nullable_name arg_name);
                        (convert arg_type);
                        (convert body)
                    ]
            | LetIn (arg_name, arg_type, arg_body, body) ->
                    [
                        `String "lambda";
                        (json_of_nullable_name arg_name);
                        (convert arg_type);
                        (convert arg_body);
                        (convert body)
                    ]
            | App (func, args) ->
                    [
                        `String "app";
                        (convert func);
                        `List Array.(to_list (map begin fun arg -> (convert arg) end args))
                    ]
            (* FIXME Universe is currently ignored *)
            | Const (const, univ_inst) ->
                    let const_name = (Names.Constant.to_string const) in
                    [
                        `String "const";
                        `String const_name;
                        JsonUniv.universe_inst_export univ_inst
                    ]
            | Ind ((ind, index), univ_inst) ->
                    [
                        `String "ind";
                        `String (Names.MutInd.to_string ind);
                        `Int index;
                        JsonUniv.universe_inst_export univ_inst
                    ]
            | Construct (((ind, index), constructor_index), univ_inst) ->
                    (*
                     * according to `kernel/names.ml`, indexes of multiple inductives start from 0 while indexes of constructors start from 1.
                     * to simplify the case, here we decrease the indexes of constructors by 1, consequently all indexes in the exported json
                     * start from 0
                     *)
                    [
                        `String "construct";
                        `String (Names.MutInd.to_string ind);
                        `Int index;
                        `Int (constructor_index - 1);
                        JsonUniv.universe_inst_export univ_inst
                    ]
            (* TODO CoFix, Proj *)
            (* FIXME Case *)
            | Case (case_info, _, c, ac) ->
                    let open Constr in
                    let cases = Array.map begin fun case ->
                        (convert case)
                    end ac in
                    let json_case_info = `List (List.map begin fun ndecl -> `Int ndecl end (Array.to_list case_info.ci_cstr_ndecls)) in
                    let cases = Array.to_list cases in
                    [
                        `String "case";
                        json_case_info; (* case_info *)
                        (convert c); (* term_matched *)
                        (convert (mkInd case_info.ci_ind)); (* term_type *)
                        `List cases (* cases *)
                    ]
            (* FIXME Fix *)
            | Fix _ ->
                    [
                        `String "fix"
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
            Evd.from_env env, env
    end in
    let (sigma, t) = (Constrintern.interp_open_constr env sigma c) in
    (constr2json sigma (EConstr.Unsafe.to_constr t))

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
                | "type" -> Sorts.Type (JsonUniv.universe_import (ext |> member "univ"))
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
