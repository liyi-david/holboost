open Serialize

exception ExportFailure of string


let get_hints (dbs: string list) : string =
    Feedback.msg_info Pp.(str (String.concat ", " dbs));
    "wtf"

let get_context env =
    let str_list = Environ.fold_named_context begin fun env decl str_list ->
        let name = Context.Named.Declaration.get_id decl in
        let name = Names.Id.to_string name in
        let typ  = Context.Named.Declaration.get_type decl in
        let str_context_variable =
            Printf.sprintf "{ \"variable_name\" : \"%s\", \"variable_type\" : %s }" name (constr2json typ) in
        str_context_variable :: str_list
    end env ~init:[] in
    Printf.sprintf "[ %s ]" (String.concat ", " str_list)

let encode_one_inductive_body (body: Declarations.one_inductive_body) : string (* in json format *) =
    let open Declarations in
    let str_constructors : string list ref = ref [] in
    for i = Array.length body.mind_consnames - 1 downto 0 do
        str_constructors := (
            Printf.sprintf "{ \"constructor_name\" : \"%s\" }"
                (Names.Id.to_string (Array.get body.mind_consnames i))
        ) :: !str_constructors
    done;
    let str_constructors = Printf.sprintf "[ %s ]" (String.concat ", " !str_constructors) in
    Printf.sprintf
        "{ \"ind_name\": \"%s\", \"constructors\" : %s  }"
        (Names.Id.to_string body.mind_typename)
        str_constructors

let get_mutinds env = 
    let open Pre_env in
    let open Declarations in
    let pre_env = Environ.pre_env env in
    let global = pre_env.env_globals in
    let str_list = Names.Mindmap_env.fold begin fun key mutind str_list ->
        let mind_body, _ = mutind in
        let str_ind_packets =
            String.concat ", " (Array.to_list (Array.map encode_one_inductive_body mind_body.mind_packets))
        in
        let str_mind = Printf.sprintf
            "{ \"mutind_name\" : \"%s\", \"inds\" : [ %s ] }"
            (Names.MutInd.to_string key)
            str_ind_packets
        in
        str_mind :: str_list
    end global.env_inductives [] in
    Printf.sprintf "[ %s ]" (String.concat ", " str_list)

let get_constants env = 
    let open Pre_env in
    let open Declarations in
    let pre_env = Environ.pre_env env in
    let global = pre_env.env_globals in
    let str_list = Names.Cmap_env.fold begin fun key const str_list ->
        let constant_name = Names.Constant.to_string key in
        let constant_body, _ = const in
        (
            match constant_body.const_type, constant_body.const_body with
            | RegularArity typ, Def const_body_substituted -> begin
                let str_constant_type = constr2json typ in
                (* let str_constant_body = constr2json (Mod_subst.force_constr const_body_substituted) in
                (Printf.sprintf "{ \"constant_name\" : \"%s\", \"constant_type\" : %s, \"constant_body\" : %s }" constant_name str_constant_type str_constant_body) *)
                (Printf.sprintf "{ \"constant_name\" : \"%s\", \"constant_type\" : %s }" constant_name str_constant_type)
            end
            | RegularArity typ, OpaqueDef _ -> begin
                let str_constant_type = constr2json typ in
                (Printf.sprintf "{ \"constant_name\" : \"%s\", \"constant_type\" : %s }" constant_name str_constant_type)
            end
            | _ -> raise (ExportFailure "currently we cannot handle template arity or body-missing constants.")
        )
        :: str_list
    end
    global.env_constants [] in
    Printf.sprintf "[ %s ]" (String.concat ", " str_list)

(* get_task_and_then
 *
 * obtains the goal and its surrounding context and globals as json string. when this is done,
 * the string will be passed to hook for following operations.
 * if cmd is provided, it will be integrated into the task as an additional json field
 *)
let get_task_and_then ?(cmd:string option = None) (hook: string -> unit) : unit Proofview.tactic =
    Proofview.Goal.enter_one begin fun gl ->
        let env = Proofview.Goal.env gl in
        let _ = Proofview.Goal.sigma gl in
        let goal_concl = Proofview.Goal.concl gl in
        let str_goal_concl = Serialize.constr2json (EConstr.Unsafe.to_constr goal_concl) in
        let str_constants = get_constants env in
        let str_context = get_context env in
        let str_mutinds = get_mutinds env in
        let str_task = Printf.sprintf
            "{ \"goal\" : %s, \"constants\" : %s, \"mutinds\": %s, \"context\" : %s, \"command\" : %s }"
            str_goal_concl
            str_constants
            str_mutinds
            str_context
            (match cmd with Some s -> s | None -> "null")
        in begin
            hook str_task;
            Tacticals.New.tclIDTAC
        end
    end
