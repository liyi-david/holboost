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
    Taskexport.get_task_and_then begin
        fun s ->
            Feedback.msg_info Pp.(str Serialize.(post_string s "localhost:8081"))
    end
]
| [ "boom" "autorewrite" "with" ne_preident_list(l) ] -> [
    let autorewrite_command = Some (
        Printf.sprintf "{ \"command\" : \"rewrite\", \"hints\" : %s }" (get_hints l)
    ) in
    Taskexport.get_task_and_then ~cmd:autorewrite_command begin 
        fun s ->
            Feedback.msg_info Pp.(str Serialize.(post_string s "localhost:8081"))
    end
]
END;;

VERNAC COMMAND EXTEND Prjson CLASSIFIED AS QUERY
| [ "Prjson" constr(c) ] -> [
    Feedback.msg_info Pp.(str (Serialize.constrexpr2json c))
    ]
END;;

VERNAC COMMAND EXTEND Send CLASSIFIED AS QUERY
| [ "Send" constr(c) ] -> [
    Feedback.msg_info Pp.(str (Serialize.constrexpr2json c));
    Feedback.msg_info Pp.(str Serialize.(post_string (constrexpr2json c) "localhost:8081"));
    ]
END;;

