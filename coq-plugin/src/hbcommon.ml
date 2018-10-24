open Yojson.Basic

exception SerializingFailure of string
exception DeserializingFailure of string * json
exception Unimplemented of string

let str_contains (main:string) (sub:string) =
    let open Str in
    let pat = regexp_string sub in
    try
        let _ = search_forward pat main 0 in
        true
    with
        Not_found -> false

