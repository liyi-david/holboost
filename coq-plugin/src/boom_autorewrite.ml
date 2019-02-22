open Taskexport;;

let boom_autorewrite l extra_cmd =
    let autorewrite_command = `Assoc ([
        ("name", `String "rewrite");
        ("hints", (get_rewrite_hints l))
    ] @ extra_cmd) in
    Taskexport.get_task_and_then ~cmd:autorewrite_command begin 
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
                            let ec = Serialize.(json2econstr (curr_item |> member "proof")) in
                            let ucs = Univexport.univ_constraints_import (curr_item |> member "sideff") in
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

