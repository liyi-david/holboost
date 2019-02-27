open JsonConstr
open JsonMutind
open Opaqueproof

open Yojson.Basic

exception ExportFailure of string

(* some flag variables *)
let extract_opaqueproof : bool ref = ref false


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
                    ("left2right", `Bool rule.rew_l2r)
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
            let encode name typ body =
                let lst_body = match body with
                | None -> []
                | Some body -> [ ("constant_body", constr2json body) ]
                in
                `Assoc (
                    [
                        ("constant_name", `String name);
                        ("constant_type", constr2json typ);
                    ] @ lst_body @ [
                        ("is_builtin", `Bool (Hbsync.is_builtin name))
                    ]
                )
            in
            let constant_body, _ = const in
            (
                match constant_body.const_type, constant_body.const_body with
                | RegularArity typ, Def const_body_substituted -> begin
                    encode constant_name typ (Some (Mod_subst.force_constr const_body_substituted))
                end
                | RegularArity typ, OpaqueDef opaque -> begin
                    if !extract_opaqueproof then
                        (* extract opaque proof is time consuming *)
                        let body = Future.force (get_proof empty_opaquetab opaque) in
                        encode constant_name typ (Some body)
                    else
                        encode constant_name typ None
                end
                | RegularArity typ, _ -> begin
                    encode constant_name typ None
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
        Hbprofile.profiling_start "serializing environment to json";
        let env = Proofview.Goal.env gl in
        let _ = Proofview.Goal.sigma gl in
        let goal_concl = Proofview.Goal.concl gl in
        let json_goal_concl = JsonConstr.constr2json (EConstr.Unsafe.to_constr goal_concl) in
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
            Hbprofile.profiling_step "running hook function";
            let hook_new = begin fun j ->
                let res = hook j in
                Hbprofile.profiling_step "applying tactic";
                res
            end in
            Hbprofile.profiling_end_after_tactic (hook_new json_task)
        end
    end

let get_nonproof_task_and_then ?(cmd:json = `Null) (hook: json -> 'a) : 'a =
    Hbprofile.profiling_start "serializing environment to json";
    let env = 
        try
            let _, env = Pfedit.get_current_goal_context () in
            env
        with
            _ -> Global.env ()
    in
    let json_constants = get_constants env in
    let json_variables = get_variables env in
    let json_mutinds = get_mutinds env in
    let json_task =
        `Assoc [
            ("goal", `Null);
            ("constants", json_constants);
            ("mutinds", json_mutinds);
            ("variables", json_variables);
            ("command", cmd)
        ]
    in begin
        Hbprofile.profiling_step "start running hook function";
        let hook_new = begin fun j ->
            let res = hook j in
            Hbprofile.profiling_end ();
            res
        end in
        hook_new json_task
    end
