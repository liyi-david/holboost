open Yojson.Basic

let sess            : int option ref    = ref None
let server          : string ref        = ref ""
let islocalhost     : bool ref          = ref false
let port            : int ref           = ref 0
let builtin_cached  : bool ref          = ref false


exception SyncFailure


let is_builtin (name:string) : bool =
    let result = String.compare (String.sub name 0 4) "Coq." in
    if result == 0 then true
    else false

let is_cached (name:string) : bool =
    false

let write_to_temp_file (content:string) : string =
    let filename = Filename.temp_file "coq_holboost" ".task" in
    let chan = open_out filename in
    Printf.fprintf chan "%s" content;
    close_out chan;
    filename
    
let raw_post_json ?(_server: string option = None) ?(_port: int option = None) (j:json) : json =
    (* we can put here any common fields in the sent messages *)
    let session = match !sess with
    | Some sid -> `Int sid
    | None -> `Null
    in
    let j = `Assoc [
        ("content", j);
        ("client", `String "coq");
        ("session", session)
    ] in
    let target = match _server, _port with
    | Some _server, Some _port -> Printf.sprintf "%s:%d" _server _port
    | _ -> begin
        match !sess with
        | None -> begin
            Feedback.msg_info Pp.(str "fatal error: failed to initialize connection with holboost server.");
            raise SyncFailure
        end
        | Some _ -> Printf.sprintf "%s:%d" !server !port
    end in
    let s = to_string j in
    let temp_file = write_to_temp_file s in
    Hbprofile.profiling_step "sending request";
    let req_cmd = if !islocalhost then
        Printf.sprintf "curl -s http://%s/%s --data a=b" target temp_file
    else
        Printf.sprintf "curl -s http://%s/%s --data @%s" target temp_file temp_file
    in
    Hbdebug.debug "hbsync" Pp.(str req_cmd);
    let ic = Unix.open_process_in req_cmd in
    let all_input = ref "" in begin
        try
            while true do
                all_input := !all_input ^ "\n" ^ (input_line ic)
            done
        with
            End_of_file ->
                close_in ic
    end;
    Hbprofile.profiling_step "parsing json response";
    let json_resp = from_string !all_input in begin
        let open Yojson.Basic.Util in
        if (json_resp |> member "error" |> to_bool) then begin
            Feedback.msg_info Pp.(str "fatal error: " ++ str (json_resp |> member "msg" |> to_string));
            if String.equal (json_resp |> member "msg" |> to_string) "session lost" then
                sess := None
            else
                ();
            raise SyncFailure
        end
        else
            builtin_cached := (json_resp |> member "builtin_cached" |> to_bool)
    end;
    json_resp

let disconnect () : unit =
    let disconn_msg = `Assoc [
        ("goal", `Null);
        ("constants", `Assoc []);
        ("mutinds", `Assoc []);
        ("variables", `Assoc []);
        ("command", `Assoc [
            ("name", `String "disconnect");
            ("session", match !sess with Some s -> `Int s | None -> `Null)
        ])
    ] in
    try
        let _ = raw_post_json disconn_msg in
        (* currently we do not care the response of disconnecting *)
        Feedback.msg_info Pp.(str "Disconnecting holboost session.")
    with _ ->
        Feedback.msg_info Pp.(str "Disconnecting holboost session failed.")

let try_connect (_server: string) (_port: int) : unit =
    let conn_msg = `Assoc [
        ("goal", `Null);
        ("constants", `Assoc []);
        ("mutinds", `Assoc []);
        ("variables", `Assoc []);
        ("command", `Assoc [
            ("name", `String "connect")
        ])
    ] in
    match !sess with
    | Some _ -> ()
    | None -> begin
        Printf.printf "trying to connect %s: %d ... " _server _port;
        try
            let resp = raw_post_json ~_server:(Some _server) ~_port:(Some _port) conn_msg in
            let json_resp = resp in
            let open Yojson.Basic.Util in
            if (json_resp |> member "error" |> to_bool) then
                Printf.printf "failed because %s.\n" (json_resp |> member "msg" |> to_string)
            else
                sess := Some (json_resp |> member "feedback" |> member "session" |> to_int);
                server := _server;
                port := _port;
                islocalhost := (String.equal _server "localhost") || (String.equal _server "127.0.0.1");
                Printf.printf "successfully connected.\n";
                at_exit disconnect;
        with
            _ -> Printf.printf "failed.\n"
            
    end

let init ?(server: string option = None) ?(port: int option = None) (_: unit): unit =
    match !sess with
    | Some _ -> ()
    | None -> begin
        Feedback.msg_info Pp.(str "Initializing Holboost connection ...");
        match server, port with
        | Some server, Some port -> try_connect server port
        | _ -> try_connect "127.0.0.1" 8081
        (* TODO establish a default remote holboost server *)
    end

let post_json ?(_server: string option = None) ?(_port: int option = None) (j:json) : json =
    init ~server:_server ~port:_port ();
    raw_post_json ~_server:_server ~_port:_port j
