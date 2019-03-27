(*i camlp4deps: "parsing/grammar.cma" i*)

open Ltac_plugin
open Stdarg
open Genarg

open Hbtactics

DECLARE PLUGIN "holboost"

let coq_pattern = Pcoq.Constr.pattern

let pr_pattern _ prc _ c = Pp.(str "unimplemented pattern printing")

ARGUMENT EXTEND pattern
    TYPED AS unit
    PRINTED BY pr_pattern
    [ coq_pattern(p) ] -> [ () ]
END

TACTIC EXTEND boom
| [ "boom" ] -> [
    JsonTask.get_task_and_then begin
        fun s ->
            let _ = Hbsync.(post_json s) in
            Tacticals.New.tclIDTAC
    end
] 
| [ "boom" "cbv" string(pat) ] -> [ Hbtactics.cbv pat ]
| [ "boom" "autorewrite" "with" ne_preident_list(l) "in" "*"] -> [
    boom_autorewrite_in_all_hypos l
]
| [ "boom" "autorewrite" "with" ne_preident_list(l) ] -> [
    boom_autorewrite_curr_goal l
]
END;;


VERNAC COMMAND EXTEND Boom_refresh CLASSIFIED AS QUERY
| [ "Boom" "Refresh" ] -> [
    Hbsync.builtin_cached := false;
    Feedback.msg_info Pp.(str "Holboost cache will be forced to reload next time when `B(b)oom` instructions are executed.")
]
END;;

VERNAC COMMAND EXTEND Boom_flags CLASSIFIED AS QUERY
| [ "Boom" "OpaqueProofExtraction" "On" ] -> [ JsonTask.extract_opaqueproof := true; ]
| [ "Boom" "OpaqueProofExtraction" "Off" ] -> [ JsonTask.extract_opaqueproof := false; ]
| [ "Boom" "ExtractConstantBody" "On" ] -> [ JsonTask.extract_constbody := true; ]
| [ "Boom" "ExtractConstantBody" "Off" ] -> [ JsonTask.extract_constbody := false; ]
| [ "Boom" "Debug" "On" ] -> [
    let open Hbdebug in
    debug_flag := true;
    Feedback.msg_info Pp.(str "holboost debug information activated.")
    ]
| [ "Boom" "Debug" "Off" ] -> [
    let open Hbdebug in
    debug_flag := false;
    Feedback.msg_info Pp.(str "holboost debug information deactivated.")
    ]
    | [ "Boom" "Profiling" "On" ] -> [
    Hbprofile.enable_profiling ();
    Feedback.msg_info Pp.(str "holboost profiling activated.")
    ]
    | [ "Boom" "Profiling" "Off" ] -> [
    Hbprofile.enable_profiling ();
    Feedback.msg_info Pp.(str "holboost profiling deactivated.")
    ]
END;;


VERNAC COMMAND EXTEND Boom_render CLASSIFIED AS QUERY
| [ "Boom" "Render" constr(c) "as" string(dotted_id) ] -> [
    let json_constr = JsonConstr.constrexpr2json c in
    let render_command = `Assoc [
        ("name", `String "render");
        ("term", json_constr);
        ("path", `String dotted_id)
    ] in
    JsonTask.get_nonproof_task_and_then ~cmd:render_command begin
        fun s ->
            let resp = Hbsync.(post_json s) in
            let open Yojson.Basic.Util in
            if (resp |> member "error" |> to_bool) then begin
                Feedback.msg_info Pp.(str "holboost failed because " ++ str (resp |> member "msg" |> to_string))
            end else
            ()
    end
    ]
END;;

VERNAC COMMAND EXTEND Boom_guard CLASSIFIED AS QUERY
| [ "Boom" "Guard" "Proved" ] -> [
    let n = Proof_global.get_open_goals () in
    if n > 0 then
        raise Proof.UnfinishedProof
    else
        ()
]
END;;

VERNAC COMMAND EXTEND Boom_check CLASSIFIED AS QUERY
| [ "Boom" "TypeOf" constr(c) ] -> [
    let json_constr = JsonConstr.constrexpr2json c in
    let check_command = `Assoc [
        ("name", `String "check");
        ("term", json_constr);
        ("id", `Null)
    ] in
    JsonTask.get_nonproof_task_and_then ~cmd:check_command begin
        fun s ->
            let resp = Hbsync.(post_json s) in
            let open Yojson.Basic.Util in
            if (resp |> member "error" |> to_bool) then begin
                Feedback.msg_info Pp.(str "holboost failed because " ++ str (resp |> member "msg" |> to_string))
            end else
                try
                    match (resp |> member "feedback") with
                    | `String msg -> Feedback.msg_info Pp.(str msg)
                    | _ -> Feedback.msg_info Pp.(str "invalid feedback from holboost server")
                with
                    Not_found -> Feedback.msg_info Pp.(str "feedback missing")
    end
    ]
| [ "Boom" "Check" constr(c) ] -> [
    let json_constr = JsonConstr.constrexpr2json c in
    let check_command = `Assoc [
        ("name", `String "check");
        ("term", json_constr);
        ("id", `Null);
        ("fullcheck", `Bool true)
    ] in
    JsonTask.get_nonproof_task_and_then ~cmd:check_command begin
        fun s ->
            let resp = Hbsync.(post_json s) in
            let open Yojson.Basic.Util in
            if (resp |> member "error" |> to_bool) then begin
                Feedback.msg_info Pp.(str "holboost failed because " ++ str (resp |> member "msg" |> to_string))
            end else
                try
                    match (resp |> member "feedback") with
                    | `String msg -> Feedback.msg_info Pp.(str msg)
                    | _ -> Feedback.msg_info Pp.(str "invalid feedback from holboost server")
                with
                    Not_found -> Feedback.msg_info Pp.(str "feedback missing")
    end
    ]
    | [ "Boom" "Print" ident(id) ] -> [
        let check_command = `Assoc [
            ("name", `String "check");
            ("term", `Null);
            ("id", `String (Names.Id.to_string id));
        ] in
        JsonTask.get_nonproof_task_and_then ~cmd:check_command begin
            fun s ->
                let resp = Hbsync.(post_json s) in
                let open Yojson.Basic.Util in
                if (resp |> member "error" |> to_bool) then begin
                    Feedback.msg_info Pp.(str "holboost failed because " ++ str (resp |> member "msg" |> to_string))
                end else
                    try
                        match (resp |> member "feedback") with
                        | `String msg -> Feedback.msg_info Pp.(str msg)
                        | _ -> Feedback.msg_info Pp.(str "invalid feedback from holboost server")
                    with
                        Not_found -> Feedback.msg_info Pp.(str "feedback missing")
        end
    ]
    | [ "Boom" "Print" "Cmd" ] -> [ Feedback.msg_info Pp.(str (Hbcommon.get_full_cmd ())) ]
    | [ "Boom" "Print" "Env" ] -> [ Feedback.msg_info (Hbdebug.pr_current_environ ()) ]
    | [ "Boom" "Print" "Sigma" ] -> [ Feedback.msg_info (Hbdebug.pr_sigma ()) ]
    | [ "Boom" "Print" "Universes" ] -> [
        let sigma_opt, env = 
            try
                let sigma, env = Pfedit.get_current_goal_context () in
                Some sigma, env
            with
                _ -> None, Global.env ()
        in
        let univs = Environ.universes env in
        Feedback.msg_info (Hbdebug.pr_ugraph univs);
        match sigma_opt with
        | Some sigma ->
            let ustate = Evd.evar_universe_context sigma in
            Feedback.msg_info (Hbdebug.pr_ustate ustate)
        | None -> ()

    ]
    | [ "Boom" "Remote" string(cmd)] -> [
        let run_command = `Assoc [
            ("name", `String "run");
            ("command", `String cmd);
        ] in
        JsonTask.get_nonproof_task_and_then ~cmd:run_command begin
            fun s ->
                let resp = Hbsync.(post_json s) in
                let open Yojson.Basic.Util in
                try
                    match (resp |> member "feedback") with
                    | `String msg -> Feedback.msg_info Pp.(str msg)
                    | _ -> Feedback.msg_info Pp.(str "invalid feedback from holboost server")
                with
                    Not_found -> Feedback.msg_info Pp.(str "feedback missing")
        end
    ]
END;;


let _ =
    try
        Hbsync.init()
    with
        _ -> Feedback.msg_error Pp.(str "Cannot initialize holboost connection.")
;;
