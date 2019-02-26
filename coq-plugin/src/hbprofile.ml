let profiling = ref false;;

let enable_profiling () =
    profiling := true
;;

let disable_profiling () =
    profiling := false
;;

let profiling_steps : (string * float) list ref = ref [];;

let profiling_start (msg:string) =
    if !profiling then
        profiling_steps := [ (msg, Sys.time ()) ]
    else
        ()
;;

let profiling_step (msg:string) =
    if !profiling then
        if List.length !profiling_steps == 0 then
            profiling_start msg
        else begin
            let last_msg, last_time = List.hd !profiling_steps in
            let curr_time = Sys.time () in
            profiling_steps := (msg, curr_time) :: (last_msg, (curr_time -. last_time)) :: (List.tl !profiling_steps)
        end
    else
        ()
;;

let profiling_step_after_tactic (msg:string) (tac : unit Proofview.tactic) : unit Proofview.tactic =
    Proofview.tclBIND tac begin fun _ ->
        profiling_step msg;
        Tacticals.New.tclIDTAC
    end
;;

let profiling_end () =
    if !profiling then
        let last_msg, last_time = List.hd !profiling_steps in
        let curr_time = Sys.time () in
        profiling_steps := (last_msg, (curr_time -. last_time)) :: (List.tl !profiling_steps);
        Feedback.msg_info Pp.(
            str "===========\n" ++
            str " PROFILING \n" ++
            str "===========\n" ++
            str (
                List.fold_left begin fun s item ->
                    let msg, cost = item in
                    (Printf.sprintf "> %5.4f : %s\n" cost msg) ^ s
                end "" !profiling_steps
            )
        )
    else
        ()
;;

let profiling_end_after_tactic (tac : unit Proofview.tactic) : unit Proofview.tactic =
    Proofview.tclBIND tac begin fun _ ->
        profiling_end ();
        Tacticals.New.tclIDTAC
    end
;;

    
