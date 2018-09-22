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
            Feedback.msg_info Pp.(str Serialize.(post_string s "localhost:8081"))
    end
] 
| [ "boom" "match" "goal" "with" pattern(pat) ] -> [
    (* FIXME *)
    Taskexport.get_task_and_then begin
        fun s ->
            Feedback.msg_info Pp.(str Serialize.(post_string s "localhost:8081"))
    end
]
| [ "boom" "autorewrite" "with" ne_preident_list(l) ] -> [
    let autorewrite_command = `Assoc [
        ("name", `String "rewrite");
        ("hints", (get_rewrite_hints l))
    ] in
    Taskexport.get_task_and_then ~cmd:autorewrite_command begin 
        fun s ->
            let resp = Serialize.(post_string s "localhost:8081") in
            Feedback.msg_info Pp.(str resp);
            let json = Yojson.Basic.from_string resp in
            let open Yojson.Basic.Util in
            ()
    end
]
END;;

VERNAC COMMAND EXTEND Prjson CLASSIFIED AS QUERY
| [ "Prjson" constr(c) ] -> [
    Feedback.msg_info Pp.(str Yojson.(to_string (Serialize.constrexpr2json c)))
    ]
END;;

VERNAC COMMAND EXTEND Send CLASSIFIED AS QUERY
| [ "Send" constr(c) ] -> [
    Feedback.msg_info Pp.(str Yojson.(to_string (Serialize.constrexpr2json c)));
    Feedback.msg_info Pp.(str Serialize.(post_string Yojson.(to_string (constrexpr2json c)) "localhost:8081"));
    ]
END;;

