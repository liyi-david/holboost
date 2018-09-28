open Serialize
open Mutindexport
open Yojson.Basic

exception ExportFailure of string

let get_rewrite_hints (dbs: string list) : json =
    let get_in_single_db (db:string) : json list =
        let open Autorewrite in
        let rules = find_rewrites db in
        List.fold_left begin fun json_rules rule ->
            let json_rule =
                `Assoc [
                    ("node", `String "rewrite_rule");
                    ("type", (constr2json rule.rew_type));
                    ("pattern", (constr2json rule.rew_pat));
                    ("lemma", (constr2json rule.rew_lemma));
                    ("right2left", `Bool rule.rew_l2r)
                ]
            in
            json_rule :: json_rules
        end [] rules
    in
    let rules = List.fold_left begin fun (rules: json list) (db:string) ->
        List.append rules (get_in_single_db db)
    end [] dbs in
    (`List rules)

let get_variables env : json =
    let var_list = Environ.fold_named_context begin fun env decl var_list ->
        let name = Context.Named.Declaration.get_id decl in
        let name = Names.Id.to_string name in
        let typ  = Context.Named.Declaration.get_type decl in
        let json_context_variable = `Assoc [ ("variable_name", `String name); ("variable_type", (constr2json typ)) ] in
        json_context_variable :: var_list
    end env ~init:[] in
    (`List var_list)

let get_constants env : json = 
    let open Pre_env in
    let open Declarations in
    let pre_env = Environ.pre_env env in
    let global = pre_env.env_globals in
    let const_list = Names.Cmap_env.fold begin fun key const const_list ->
        (* key is actually Constant.t *)
        let constant_name = Names.Constant.to_string key in
        Declbuf.set constant_name (Declbuf.ConstantDecl key);
        if ((Hbsync.is_builtin constant_name) && !Hbsync.builtin_cached) then begin
            const_list
        end
        else begin
            let constant_body, _ = const in
            (
                match constant_body.const_type, constant_body.const_body with
                | RegularArity typ, Def const_body_substituted -> begin
                    let json_constant_type = constr2json typ in
                    let json_constant_body = constr2json (Mod_subst.force_constr const_body_substituted) in
                    `Assoc [
                        ("constant_name", `String constant_name);
                        ("constant_type", json_constant_type);
                        ("constant_body", json_constant_body);
                        ("is_builtin", `Bool (Hbsync.is_builtin constant_name))
                    ]
                end
                | RegularArity typ, _ -> begin
                    let json_constant_type = constr2json typ in
                    `Assoc [
                        ("constant_name", `String constant_name);
                        ("constant_type", json_constant_type);
                        ("is_builtin", `Bool (Hbsync.is_builtin constant_name))
                    ]
                end
                | _ -> raise (ExportFailure "currently we cannot handle template arity constants.")
            )
            :: const_list
        end
    end
    global.env_constants [] in
    `List const_list

(* get_task_and_then
 *
 * obtains the goal and its surrounding context and globals as json string. when this is done,
 * the string will be passed to hook for following operations.
 * if cmd is provided, it will be integrated into the task as an additional json field
 *)
let get_task_and_then ?(cmd:json = `Null) (hook: json -> unit Proofview.tactic) : unit Proofview.tactic =
    Proofview.Goal.enter_one begin fun gl ->
        let env = Proofview.Goal.env gl in
        let _ = Proofview.Goal.sigma gl in
        let goal_concl = Proofview.Goal.concl gl in
        let json_goal_concl = Serialize.constr2json (EConstr.Unsafe.to_constr goal_concl) in
        let json_constants = get_constants env in
        let json_variables = get_variables env in
        let json_mutinds = get_mutinds env in
        let json_task =
            `Assoc [
                ("goal", json_goal_concl);
                ("constants", json_constants);
                ("mutinds", json_mutinds);
                ("variables", json_variables);
                ("command", cmd)
            ]
        in begin
            hook json_task
        end
    end
