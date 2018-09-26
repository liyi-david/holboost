(*
 * Specification of exported json
 * 
 *)

exception SerializingFailure of string
exception DeserializingFailure of string
exception Unimplemented of string

open Yojson.Basic

let write_to_temp_file (content:string) : string =
    let filename = Filename.temp_file "coq_holboost" ".task" in
    let chan = open_out filename in
    Printf.fprintf chan "%s" content;
    close_out chan;
    filename

let post_string (s:string)(target:string) =
    let temp_file = write_to_temp_file s in
    let ic = Unix.open_process_in (Printf.sprintf "curl -s http://%s/prove --data @%s" target temp_file) in
    let all_input = ref "" in begin
        try
            while true do
                all_input := !all_input ^ "\n" ^ (input_line ic)
            done
        with
            End_of_file ->
                close_in ic
    end;
    !all_input

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
                    let sort_name = match sort with
                        | Sorts.Prop Sorts.Pos -> "set"
                        | Sorts.Prop Sorts.Null -> "prop"
                        | Sorts.Type _ -> "type"
                    in
                    [
                        ("type", `String "sort");
                        ("sort", `String sort_name)
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
            | Const (const, _) ->
                    let const_name = (Names.Constant.to_string const) in
                    [
                        ("type", `String "const");
                        ("name", `String const_name)
                    ]
            | Ind ((ind, index), _) ->
                    [
                        ("type", `String "ind");
                        ("mutind_name", `String (Names.MutInd.to_string ind));
                        ("ind_index", `Int index)
                    ]
            | Construct (((ind, index), constructor_index), _) ->
                    (*
                     * according to `kernel/names.ml`, indexes of multiple inductives start from 0 while indexes of constructors start from 1.
                     * to simplify the case, here we decrease the indexes of constructors by 1, consequently all indexes in the exported json
                     * start from 0
                     *)
                    [
                        ("type", `String "construct");
                        ("mutind_name", `String (Names.MutInd.to_string ind));
                        ("ind_index", `Int index);
                        ("constructor_index", `Int (constructor_index - 1))
                    ]
            (* TODO CoFix, Proj *)
            (* FIXME Case *)
            | Case (case_info, _, c, ac) ->
                    let cases = Array.map begin fun case ->
                        (convert case)
                    end ac in
                    let cases = Array.to_list cases in
                    [
                        ("type", `String "case");
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
    let env = Global.env () in
    let sigma = Evd.empty in
    let (t, _) = (Constrintern.interp_constr env sigma c) in
    constr2json t

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
                (* FIXME maybe not type1? *)
                | "type" -> Sorts.type1
                | _ -> raise (DeserializingFailure Printf.(sprintf "unexpected sort %s" sort_name))
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
                    | _ -> raise (DeserializingFailure (Printf.sprintf "unsupported cast index %d" (ext |> member "cast_kind" |> to_int)))
                    in
                    mkCast ((json2econstr (ext |> member "body")), cast_kind, (json2econstr (ext |> member "guaranteed_type")))
            | "const" ->
                let name = ext |> member "name" |> to_string in begin
                    match Declbuf.get name with
                    | Some (Declbuf.ConstantDecl const) -> mkConst const
                    | _ -> raise (DeserializingFailure (Printf.sprintf "const %s not found in the buffer." name))
                end
            | "ind" ->
                let name = ext |> member "mutind_name" |> to_string in begin
                    match Declbuf.get name with
                    | Some (Declbuf.MutindDecl mutind) -> mkInd (mutind, (ext |> member "ind_index" |> to_int))
                    | _ -> raise (DeserializingFailure (Printf.sprintf "mutind %s not found in the buffer." name))
                end
            | "construct" ->
                let name = ext |> member "mutind_name" |> to_string in begin
                    match Declbuf.get name with
                    | Some (Declbuf.MutindDecl mutind) -> mkConstruct (
                        (mutind, (ext |> member "ind_index" |> to_int)),
                        (* IMPORTANT: indexes of constructors start from 1 *)
                        (ext |> member "constructor_index" |> to_int) + 1
                    )
                    | _ -> raise (DeserializingFailure (Printf.sprintf "mutind %s not found in the buffer." name))
                end
            | _ -> raise (DeserializingFailure Printf.(sprintf "unsupported term type %s" term_type))
        in
            (* HERE is a pre-allocated space for debuging prints ..... *)
            result
    with
        Type_error (msg, _) ->
            Feedback.msg_info Pp.(str Printf.(sprintf "failed to convert json to econstr because %s: %s" msg (Yojson.Basic.to_string ext)));
            raise (DeserializingFailure msg)
