(*i camlp4deps: "parsing/grammar.cma" i*)

open Ltac_plugin
open Stdarg

DECLARE PLUGIN "holboost"

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
