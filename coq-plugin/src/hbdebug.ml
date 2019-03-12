let debug_flag : bool ref = ref false

let debug (m:string) (msg:Pp.std_ppcmds) =
    if !debug_flag then
        Feedback.msg_info Pp.(
            str (Printf.sprintf "Holboost Debug Info [%10s] " m) ++
            msg
        )
    else
        ()

let pr_ugraph (graph:UGraph.t) : Pp.std_ppcmds =
    let raw_ppcmd = UGraph.pr_universes (Univ.Level.pr) graph in
    let raw_lines = Pp.(string_of_ppcmds raw_ppcmd) in
    let raw_lines = String.split_on_char '\n' raw_lines in
    let top_lines = List.filter begin fun line ->
        let line = String.trim line in
        if String.length line < 1 then false
        else
            ((String.get line 0) != '<') && (Hbcommon.str_contains line "Top")
    end raw_lines in
    let open Pp in
    str "universes information: \n\n" ++ (
        List.fold_left begin fun ppcmd line ->
            ppcmd ++ (str line) ++ (str "\n")
        end (str "") top_lines
    )

let pr_ustate (ustate: UState.t) : Pp.std_ppcmds =
    let open Pp in
    let constraints = UState.constraints ustate in
    str "universes information in evar_map:\n\n" ++ 
    Univ.Constraint.fold begin fun uc cmd ->
        let l, opr, r = uc in
        str (Univ.Level.to_string l) ++
        Univ.pr_constraint_type opr ++
        str (Univ.Level.to_string r) ++
        str "\n" ++
        cmd
    end constraints (str "")

let pr_rels (rels: Context.Rel.Declaration.t list) : Pp.std_ppcmds =
    let open Pp in
    str (Printf.sprintf "rel context with %d variables:\n" (List.length rels)) ++
    let cmdassum, cmddef = List.fold_left begin fun cmdpair rdecl ->
        let cmdassum, cmddef = cmdpair in
        let open Context.Rel.Declaration in
        match rdecl with
        | LocalAssum (name, typ) ->
            cmdassum ++ (Names.Name.print name) ++ str ": " ++ (Printer.pr_constr typ), cmddef
        | LocalDef (name, _, typ) ->
            cmdassum, cmddef ++ (Names.Name.print name) ++ str ": " ++ (Printer.pr_constr typ)
    end (str "", str "") rels in
    str "local assumptions: " ++ cmdassum ++ str "\n" ++
    str "local definitions: " ++ cmddef ++ str "\n"

let pr_environ (env:Environ.env) : Pp.std_ppcmds =
    let open Pp in
    str "" ++
    pr_rels (Environ.fold_rel_context begin fun env rel_decl lst -> rel_decl :: lst end env ~init:[]) ++
    pr_ugraph (Environ.universes env)

let pr_current_environ () : Pp.std_ppcmds =
    let env =
        try
            let _, env = Pfedit.get_current_goal_context () in
            env
        with
            _ -> Global.env ()
    in
    pr_environ env

let pr_sigma () : Pp.std_ppcmds =
    let sigma, _ = Pfedit.get_current_goal_context () in
    let open Pp in
    let count = ref 0 in
    let cmd = Evd.fold begin fun evar info cmd ->
        count := !count + 1;
        (
            try
                (str Printf.(sprintf "[%d]" (Evar.repr evar))) ++ (Printer.pr_evar sigma (evar, info)) ++ str "\n"
            with Not_found ->
                str "not_found" ++ str "\n"
        ) ++ cmd
    end sigma (str "") in
    str (Printf.sprintf "evar map contains %d existential variables: \n" (!count)) ++
    cmd
