(*
 * this file contains a set of local tactics, i.e. which do not require communication with
 * remote python servers
 *)

open Proofview
open Proofview.Notations
open Pre_env
open Genredexpr
open Tacexpr
open Libnames
open Ltac_plugin
open G_tactic
open JsonTask

let cbv (pattern: string) : unit tactic =
    let re = Str.regexp pattern in
    tclENV >>=
        fun env ->
            tclEVARMAP >>=
                fun sigma ->
                    let pre_env = Environ.pre_env env in
                    let global = pre_env.env_globals in
                    let matched_or_by_notations = Names.Cmap_env.fold begin fun key const lst ->
                        let name = Names.Constant.to_string key in
                        let constant_body, _ = const in
                        let open Declarations in
                        match constant_body.const_body with
                        | Def _ -> begin
                            if Str.string_match re name 0 then
                                try
                                    let qualid = qualid_of_string name in
                                    let reference = Qualid (None, qualid) in
                                    let _ = Feedback.msg_info Pp.(str "matched: " ++ str name) in
                                    (Misctypes.AN reference) :: lst
                                with
                                    _ -> lst
                            else
                                lst
                        end
                        | _ -> lst
                    end global.env_constants [] in
                    (*
                     * one can change the following flag to change the behavior of cbv. also it can be make more flexible
                     * by changing the syntax of cbv. (though I beleive it is not important by now)
                     *)
                    let gflag = {
                        rBeta = true;
                        (* as suggested by the reference manual, iota reduction is now a shortcut of the following three flags *)
                        rMatch = true;
                        rFix = true;
                        rCofix = true;
                        rZeta = true;
                        rDelta = false; (* refer to definition in genredexpr.ml *)
                        rConst = matched_or_by_notations
                    } in
                    let rexpr_gen : raw_red_expr = Cbv gflag in
                    let raw_tactic : raw_tactic_expr = TacAtom (None, TacReduce (rexpr_gen, G_tactic.all_concl_occs_clause)) in
                    let tactic = Tacinterp.interp raw_tactic in
                    tactic
;;


let boom_autorewrite l extra_cmd =
    let autorewrite_command = `Assoc ([
        ("name", `String "rewrite");
        ("hints", (get_rewrite_hints l))
    ] @ extra_cmd) in
    JsonTask.get_task_and_then ~cmd:autorewrite_command begin 
        fun s ->
            let resp = Hbsync.(post_json s) in
            let open Yojson.Basic.Util in
            if (resp |> member "error" |> to_bool) then begin
                Feedback.msg_info Pp.(str "holboost failed because " ++ str (resp |> member "msg" |> to_string));
                Tacticals.New.tclIDTAC
            end else
                try
                    match (resp |> member "feedback") with
                    | `Null -> begin
                        Feedback.msg_info Pp.(str "holboost rewriting failed to make any new progress.");
                        Tacticals.New.tclIDTAC
                    end
                    | _ -> begin
                        let open Tactics in
                        List.fold_left begin fun prev_tac curr_item ->
                            let ec = JsonConstr.(json2econstr (curr_item |> member "proof")) in
                            let ucs = JsonUniv.univ_constraints_import (curr_item |> member "sideff") in
                            let sigma, env = Pfedit.get_current_context () in
                            let sigma_new = Evd.add_constraints sigma ucs in
                            let sigma_new = Evd.fix_undefined_variables sigma_new in
                            let target = (curr_item |> member "target" |> to_string) in
                            Debug.debug "autorewrite" Printer.(pr_econstr ec);
                            let tac = if String.equal target "__goal__" then
                                Proofview.tclTHEN
                                    (Proofview.Unsafe.tclEVARSADVANCE sigma_new)
                                    (Tactics.apply ec)
                            else
                                Proofview.tclTHEN
                                    (Proofview.Unsafe.tclEVARSADVANCE sigma_new)
                                    (Tactics.Simple.apply_in (Names.id_of_string target) ec)
                            in
                            Proofview.tclTHEN prev_tac tac
                        end Tacticals.New.tclIDTAC (resp |> member "feedback" |> to_list)
                    end
                with
                    Not_found ->
                        Feedback.msg_info Pp.(str "failed to print the returned econstr");
                        Tacticals.New.tclIDTAC
    end
;;

let boom_autorewrite_in_all_hypos l =
    let extra_cmd = [
        ("in", `String "*")
    ] in
    boom_autorewrite l extra_cmd

let boom_autorewrite_curr_goal l =
    let extra_cmd = [] in
    boom_autorewrite l extra_cmd
;;

