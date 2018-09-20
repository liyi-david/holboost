open Serialize

exception Unimplemented of string

let mk_template_arity (nparams: int) : Constr.t =
    (* from 2 to Type -> Type -> Type *)
    let rec iterate (nparams: int) : EConstr.t =
        let open EConstr in
        let open Sorts in
        if (nparams == 0) then begin
            mkSort type1
        end else begin
            mkArrow (mkSort Sorts.type1) (iterate (nparams - 1))
        end
    in

    EConstr.Unsafe.to_constr (iterate nparams)

let get_context (context: Context.Rel.t) : string = 
    let open Context in
    let lst_context = Rel.fold_outside begin fun rel lst_context ->
        lst_context
    end context ~init:[] in
    Printf.sprintf "[ %s ]" (String.concat "," lst_context)

let get_ind_arity (arity: Declarations.inductive_arity) : string =
    let open Declarations in
    match arity with
    | RegularArity rarity -> 
            constr2json rarity.mind_user_arity
    | TemplateArity tarity ->
            (* a template arity is a technique to support template universe polymorphism,
             * e.g. Type_0 -> Type_1 -> Type, ...
             * but here we simply use Type -> Type -> ... to simplify all of them
             * *)
            constr2json (mk_template_arity (List.length tarity.template_param_levels))

let get_one_inductive_body (body: Declarations.one_inductive_body) : string (* in json format *) =
    let open Declarations in
    let str_constructors : string list ref = ref [] in

    (* here we prefer loop instead of fold, mainly because the names and types of the constructors are
     * declared in different arrays (mind_consnames and mind_user_lc), but we want to combine them and
     * form a single object for a constructor
     *)
    for i = Array.length body.mind_consnames - 1 downto 0 do
        (* extract all constructors *)
        str_constructors := (
            Printf.sprintf "{ \"constructor_name\" : \"%s\", \"constructor_type\": %s }"
                (Names.Id.to_string (Array.get body.mind_consnames i))
                (constr2json (Array.get body.mind_user_lc i))
        ) :: !str_constructors
    done;
    let str_constructors = Printf.sprintf "[ %s ]" (String.concat ", " !str_constructors) in
    let str_arity_context = get_context body.mind_arity_ctxt in
    let str_arity = get_ind_arity body.mind_arity in
    Printf.sprintf
        "{ \"ind_name\": \"%s\", \"arity\" : %s, \"context\": %s, \"constructors\" : %s  }"
        (Names.Id.to_string body.mind_typename)
        str_arity
        str_arity_context
        str_constructors

let get_mutinds env = 
    let open Pre_env in
    let open Declarations in
    let pre_env = Environ.pre_env env in
    let global = pre_env.env_globals in
    let str_list = Names.Mindmap_env.fold begin fun key mutind str_list ->
        try
            let mind_body, _ = mutind in
            let str_ind_packets =
                String.concat ", " (Array.to_list (Array.map get_one_inductive_body mind_body.mind_packets))
            in
            let str_mind = Printf.sprintf
                "{ \"mutind_name\" : \"%s\", \"inds\" : [ %s ] }"
                (Names.MutInd.to_string key)
                str_ind_packets
            in
            str_mind :: str_list
        with (Unimplemented msg) ->
            Feedback.msg_info Pp.(str "error! " ++ str msg);
            str_list
    end global.env_inductives [] in
    Printf.sprintf "[ %s ]" (String.concat ", " str_list)


