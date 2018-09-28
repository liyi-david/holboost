open Serialize
open Yojson.Basic

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

let get_context (context: Context.Rel.t) : json = 
    let open Context in
    let lst_context : json list = Rel.fold_outside begin fun rel lst_context ->
        (* FIXME *)
        lst_context
    end context ~init:[] in
    `List lst_context

let get_ind_arity (arity: Declarations.inductive_arity) : json =
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

let get_one_inductive_body (body: Declarations.one_inductive_body) : json =
    let open Declarations in
    let json_constructors : json list ref = ref [] in

    (* here we prefer loop instead of fold, mainly because the names and types of the constructors are
     * declared in different arrays (mind_consnames and mind_user_lc), but we want to combine them and
     * form a single object for a constructor
     *)
    for i = Array.length body.mind_consnames - 1 downto 0 do
        (* extract all constructors *)
        json_constructors := (
            `Assoc [
                ("constructor_name", `String (Names.Id.to_string (Array.get body.mind_consnames i)));
                ("constructor_type", (constr2json (Array.get body.mind_user_lc i)))
            ]
        ) :: !json_constructors
    done;
    let json_constructors = `List !json_constructors in
    let json_arity_context = get_context body.mind_arity_ctxt in
    let json_arity = get_ind_arity body.mind_arity in
    `Assoc [
        ("ind_name", `String (Names.Id.to_string body.mind_typename));
        ("arity", json_arity);
        ("context", json_arity_context);
        ("constructors", json_constructors)
    ]

let get_mutinds env : json = 
    let open Pre_env in
    let open Declarations in
    let pre_env = Environ.pre_env env in
    let global = pre_env.env_globals in
    let json_list = Names.Mindmap_env.fold begin fun key mutind json_list ->
        let mutind_name = Names.MutInd.to_string key in
        Declbuf.set mutind_name (Declbuf.MutindDecl key);
        if (Hbsync.is_builtin mutind_name) && !Hbsync.builtin_cached then json_list else begin
            try
                let mind_body, _ = mutind in
                let json_ind_packets = `List (Array.to_list (Array.map get_one_inductive_body mind_body.mind_packets)) in
                let json_mind = `Assoc [
                    ("mutind_name", `String mutind_name);
                    ("inds", json_ind_packets);
                    ("is_builtin", `Bool (Hbsync.is_builtin mutind_name))
                ] in
                json_mind :: json_list
            with (Unimplemented msg) ->
                Feedback.msg_info Pp.(str "error! " ++ str msg);
                json_list
        end
    end global.env_inductives [] in
    `List json_list


