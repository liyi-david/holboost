open Yojson.Basic

let sess : int option ref = ref None
let server : string ref = ref ""
let port : int ref = ref 0
let builtin_cached : bool ref = ref false

exception SyncFailure


let is_builtin (name:string) : bool =
    let result = String.equal (String.sub name 0 4) "Coq." in
    result

let write_to_temp_file (content:string) : string =
    let filename = Filename.temp_file "coq_holboost" ".task" in
    let chan = open_out filename in
    Printf.fprintf chan "%s" content;
    close_out chan;
    filename
    
let raw_post_json ?(_server: string option = None) ?(_port: int option = None) (j:json) : json =
    (* we can put here any common fields in the sent messages *)
    let j = `Assoc [
        ("content", j);
        ("client", `String "coq")
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
    let ic = Unix.open_process_in (Printf.sprintf "curl -s http://%s/coq --data @%s" target temp_file) in
    let all_input = ref "" in begin
        try
            while true do
                all_input := !all_input ^ "\n" ^ (input_line ic)
            done
        with
            End_of_file ->
                close_in ic
    end;
    from_string !all_input

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
        let resp = raw_post_json ~_server:(Some _server) ~_port:(Some _port) conn_msg in
        try
            let json_resp = resp in
            let open Yojson.Basic.Util in
            if (json_resp |> member "error" |> to_bool) then
                Printf.printf "failed because %s.\n" (json_resp |> member "msg" |> to_string)
            else
                sess := Some (json_resp |> member "feedback" |> member "session" |> to_int);
                server := _server;
                port := _port;
                Printf.printf "successfully connected.\n";
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
        | _ -> ()
        ;
        try_connect "localhost" 8081;
        (* TODO establish a default remote holboost server *)
    end

let post_json ?(_server: string option = None) ?(_port: int option = None) (j:json) : json =
    init();
    let open Yojson.Basic.Util in
    let json_resp = raw_post_json ~_server:_server ~_port:_port j in begin
        if not (json_resp |> member "builtin_cached" |> to_bool) then
            builtin_cached := false
        else
            builtin_cached := true
    end;
    json_resp
