(*
 * Specification of exported json
 * 
 *)

exception SerializingFailure of string

let post_string (s:string)(target:string) =
    let ic = Unix.open_process_in (Printf.sprintf "curl -s http://%s/prove --data '%s'" target s) in
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

let string_of_nullable_name (name: Names.Name.t) : string =
    match name with
    | Names.Name.Anonymous -> "null"
    | Names.Name.Name id -> Printf.sprintf "\"%s\"" (Names.Id.to_string id)

let constr2json (c: Constr.t) : string =
    let rec convert (c: Constr.t) : string = 
        let open Constr in
        match (kind c) with
        | Rel index -> Printf.sprintf "{ \"type\" : \"rel\", \"index\" : %d }" index
        | Var id -> Printf.sprintf "{ \"type\" : \"var\", \"id\" : \"%s\" }" (Names.Id.to_string id)
        (* TODO Meta, Evar *)
        | Sort sort ->
                Printf.sprintf "{ \"type\" : \"sort\", \"sort\" : \"%s\"} " (
                    match sort with
                    | Sorts.Prop Sorts.Pos -> "set"
                    | Sorts.Prop Sorts.Null -> "prop"
                    | Sorts.Type _ -> "type"
                )
        (* FIXME Cast *)
        | Cast (c, kind, types) ->
                Printf.sprintf "{ \"type\" : \"cast\" , \"base_term\" : %s, \"cast_kind\" : \" \", \"guaranteed_type\" : \"%s\" }" (convert c) (convert types)
        | Prod (name, var_type, body_type) ->
                Printf.sprintf "{ \"type\" : \"prod\", \"arg_name\": %s, \"arg_type\" : %s, \"body_type\": %s }" (string_of_nullable_name name)(convert var_type) (convert body_type)
        | Lambda (name, var_type, body_type) ->
                Printf.sprintf "{ \"type\" : \"lambda\", \"arg_name\": %s, \"arg_type\" : %s, \"body\": %s }" (string_of_nullable_name name)(convert var_type) (convert body_type)
        | LetIn (arg_name, arg_type, arg_body, body) ->
                Printf.sprintf 
                    "{ \"type\" : \"letin\", \"arg_name\": %s, \"arg_type\": %s, \"arg_body\": %s, \"body\": %s }"
                    (string_of_nullable_name arg_name)
                    (convert arg_type)
                    (convert arg_body)
                    (convert body)
        | App (func, args) ->
                Printf.sprintf "{ \"type\" : \"app\", \"func\" : %s, \"args\" : [ %s ] }" (convert func) (
                    String.concat "," Array.(to_list (map begin fun arg -> (convert arg) end args))
                )
        (* FIXME Universe is currently ignored *)
        | Const (const, _) ->
                Printf.sprintf "{ \"type\" : \"const\", \"name\" : \"%s\" }" (Names.Constant.to_string const)
        | Ind ((ind, index), _) ->
                Printf.sprintf "{ \"type\" : \"ind\", \"name\" : \"%s\", \"index\" : %d }" (Names.MutInd.to_string ind) index
        | Construct (((ind, index), constructor_index), _) ->
                (*
                 * according to `kernel/names.ml`, indexes of multiple inductives start from 0 while indexes of constructors start from 1.
                 * to simplify the case, here we decrease the indexes of constructors by 1, consequently all indexes in the exported json
                 * start from 0
                 *)
                Printf.sprintf "{ \"type\" : \"construct\", \"name\" : \"%s\", \"index\" : %d, \"constructor_index\": %d }" (Names.MutInd.to_string ind) index (constructor_index - 1)
        (* TODO Fix, CoFix, Proj *)
        (* FIXME Case *)
        | Case (case_info, _, c, ac) ->
                let cases = Array.map begin fun case ->
                    (convert case)
                end ac in
                let cases = Array.to_list cases in
                Printf.sprintf
                    "{ \"type\" : \"case\", \"term_matched\" : %s, \"term_type\" : %s , \"cases\" : [ %s ] }"
                    (convert c)
                    (convert (mkInd case_info.ci_ind))
                    (String.concat ", " cases)
        | _ -> raise (SerializingFailure (Printf.sprintf "unhandled constr type %s" (Pp.string_of_ppcmds (Printer.pr_constr c))))
    in
    try
        convert c
    with
    | SerializingFailure msg -> Printf.sprintf "{ error : true, msg : \"%s\" }" msg

let constrexpr2json (c: Constrexpr.constr_expr) : string =
    let env = Global.env () in
    let sigma = Evd.empty in
    let (t, _) = (Constrintern.interp_constr env sigma c) in
    constr2json t

let json2econstr (j: string) =
    ()
