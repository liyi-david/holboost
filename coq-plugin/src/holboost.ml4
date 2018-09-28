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
            Tacticals.New.tclIDTAC
    end
] 
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
                        let ec = Serialize.(json2econstr (resp |> member "feedback")) in
                        let sigma, env = Pfedit.get_current_context () in
                        let _, typ = Typing.type_of env sigma ec in
                        Debug.debug "autorewrite" Printer.(pr_econstr ec);
                        Debug.debug "autorewrite" Printer.(pr_econstr typ);
                        Tactics.apply ec
                    end
                with
                    Not_found ->
                        Feedback.msg_info Pp.(str "failed to print the returned econstr");
                        Tacticals.New.tclIDTAC
    end
]
END;;

VERNAC COMMAND EXTEND Boom_debug CLASSIFIED AS QUERY
| [ "Boom" "debug" "on" ] -> [
    let open Debug in
    debug_flag := true;
    Feedback.msg_info Pp.(str "holboost debug information activated.")
    ]
| [ "Boom" "debug" "off" ] -> [
    let open Debug in
    debug_flag := false;
    Feedback.msg_info Pp.(str "holboost debug information deactivated.")
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
