open Yojson.Basic

exception SerializingFailure of string
exception DeserializingFailure of string * json
exception Unimplemented of string

