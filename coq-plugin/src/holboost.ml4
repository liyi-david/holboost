(*i camlp4deps: "parsing/grammar.cma" i*)

open Ltac_plugin
open Stdarg
open Genarg
open Extraargs

open Taskexport

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
    Taskexport.get_task_and_then begin
        fun s ->
            let resp = Hbsync.(post_json s) in
            Tacticals.New.tclIDTAC
    end
] 
| [ "boom" "cbv" string(pat) ] -> [ Hbtactics.cbv pat ]
| [ "boom" "autorewrite" "with" ne_preident_list(l) ] -> [
    let autorewrite_command = `Assoc [
        ("name", `String "rewrite");
        ("hints", (get_rewrite_hints l))
    ] in
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
                        let ec = Serialize.(json2econstr (resp |> member "feedback" |> member "proof")) in
                        let ucs = Univexport.univ_constraints_import (resp |> member "feedback" |> member "sideff") in
                        let sigma, env = Pfedit.get_current_context () in
                        let sigma_new = Evd.add_constraints sigma ucs in
                        let sigma_new = Evd.fix_undefined_variables sigma_new in
                        Debug.debug "autorewrite" Printer.(pr_econstr ec);
                        let open Tactics in
                        Proofview.tclTHEN
                            (Proofview.Unsafe.tclEVARSADVANCE sigma_new)
                            (Tactics.apply ec)
                    end
                with
                    Not_found ->
                        Feedback.msg_info Pp.(str "failed to print the returned econstr");
                        Tacticals.New.tclIDTAC
    end
]
END;;


VERNAC COMMAND EXTEND Boom_debug CLASSIFIED AS QUERY
| [ "Boom" "Debug" "On" ] -> [
    let open Debug in
    debug_flag := true;
    Feedback.msg_info Pp.(str "holboost debug information activated.")
    ]
| [ "Boom" "Debug" "Off" ] -> [
    let open Debug in
    debug_flag := false;
    Feedback.msg_info Pp.(str "holboost debug information deactivated.")
    ]
END;;


VERNAC COMMAND EXTEND Boom_check CLASSIFIED AS QUERY
| [ "Boom" "TypeOf" constr(c) ] -> [
    let json_constr = Serialize.constrexpr2json c in
    let check_command = `Assoc [
        ("name", `String "check");
        ("term", json_constr);
        ("id", `Null)
    ] in
    Taskexport.get_nonproof_task_and_then ~cmd:check_command begin
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
    let json_constr = Serialize.constrexpr2json c in
    let check_command = `Assoc [
        ("name", `String "check");
        ("term", json_constr);
        ("id", `Null);
        ("fullcheck", `Bool true)
    ] in
    Taskexport.get_nonproof_task_and_then ~cmd:check_command begin
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
        Taskexport.get_nonproof_task_and_then ~cmd:check_command begin
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
    | [ "Boom" "Print" "Env" ] -> [ Feedback.msg_info (Debug.pr_current_environ ()) ]
    | [ "Boom" "Print" "Sigma" ] -> [ Feedback.msg_info (Debug.pr_sigma ()) ]
    | [ "Boom" "Print" "Universes" ] -> [
        let sigma_opt, env = 
            try
                let sigma, env = Pfedit.get_current_goal_context () in
                Some sigma, env
            with
                _ -> None, Global.env ()
        in
        let univs = Environ.universes env in
        Feedback.msg_info (Debug.pr_ugraph univs);
        match sigma_opt with
        | Some sigma ->
            let ustate = Evd.evar_universe_context sigma in
            Feedback.msg_info (Debug.pr_ustate ustate)
        | None -> ()

    ]
    | [ "Boom" "Remote" string(cmd)] -> [
        let run_command = `Assoc [
            ("name", `String "run");
            ("command", `String cmd);
        ] in
        Taskexport.get_nonproof_task_and_then ~cmd:run_command begin
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
END;;

(*
VERNAC COMMAND EXTEND Send CLASSIFIED AS QUERY
| [ "Send" constr(c) ] -> [
    Feedback.msg_info Pp.(str Yojson.(to_string (Serialize.constrexpr2json c)));
    Feedback.msg_info Pp.(str Hbsync.(post_json Yojson.(to_string (constrexpr2json c)) "localhost:8081"));
    ]
END;;
*)


let _ =
    try
        Hbsync.init()
    with
        _ -> Feedback.msg_error Pp.(str "Cannot initialize holboost connection.")
;;
