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

let get_constants_by_names (names: string list) (env : Environ.env) : Names.Constant.t list =
    let open Pre_env in
    let pre_env = Environ.pre_env env in
    let global = pre_env.env_globals in
    Names.Cmap_env.fold begin fun key const lst ->
        let name = Names.Constant.to_string key in
        if (List.exists begin fun n -> String.equal n name end names) then
            key :: lst
        else
            lst
    end global.env_constants []
;;
