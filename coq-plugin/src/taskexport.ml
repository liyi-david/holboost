open Serialize
open Mutindexport

exception ExportFailure of string

let get_rewrite_hints (dbs: string list) : string =
    let get_in_single_db (db:string) : string list =
        let open Autorewrite in
        let rules = find_rewrites db in
        List.fold_left begin fun str_rules rule ->
            let str_rule = Printf.sprintf
                "{ \"node\": \"rewrite_rule\", \"type\": %s, \"pattern\": %s, \"lemma\": %s, \"right2left\": %s }"
                (constr2json rule.rew_type)
                (constr2json rule.rew_pat)
                (constr2json rule.rew_lemma)
                (if rule.rew_l2r then "false" else "true")
            in
            str_rule :: str_rules
        end [] rules
    in
    let rules = List.fold_left begin fun (rules: string list) (db:string) ->
        List.append rules (get_in_single_db db)
    end [] dbs in
    Printf.sprintf "[ %s ]" (String.concat ", " rules)

let get_variables env =
    let str_list = Environ.fold_named_context begin fun env decl str_list ->
        let name = Context.Named.Declaration.get_id decl in
        let name = Names.Id.to_string name in
        let typ  = Context.Named.Declaration.get_type decl in
        let str_context_variable =
            Printf.sprintf "{ \"variable_name\" : \"%s\", \"variable_type\" : %s }" name (constr2json typ) in
        str_context_variable :: str_list
    end env ~init:[] in
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
                let str_constant_body = constr2json (Mod_subst.force_constr const_body_substituted) in
                (Printf.sprintf "{ \"constant_name\" : \"%s\", \"constant_type\" : %s, \"constant_body\" : %s }" constant_name str_constant_type str_constant_body)
            end
            | RegularArity typ, _ -> begin
                let str_constant_type = constr2json typ in
                (Printf.sprintf "{ \"constant_name\" : \"%s\", \"constant_type\" : %s }" constant_name str_constant_type)
            end
            | _ -> raise (ExportFailure "currently we cannot handle template arity constants.")
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
        let str_variables = get_variables env in
        let str_mutinds = get_mutinds env in
        let str_task = Printf.sprintf
            "{ \"goal\" : %s, \"constants\" : %s, \"mutinds\": %s, \"variables\" : %s, \"command\" : %s }"
            str_goal_concl
            str_constants
            str_mutinds
            str_variables
            (match cmd with Some s -> s | None -> "null")
        in begin
            hook str_task;
            Tacticals.New.tclIDTAC
        end
    end
