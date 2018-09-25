let debug_flag : bool ref = ref false

let debug (m:string) (msg:Pp.std_ppcmds) =
    if !debug_flag then
        Feedback.msg_info Pp.(
            str (Printf.sprintf "Holboost Debug Info [%10s] " m) ++
            msg
        )
    else
        ()
