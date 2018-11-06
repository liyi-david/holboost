(*
 * this file contains a set of local tactics, i.e. which do not require communication with
 * remote python servers
 *)

open Proofview
open Proofview.Notations
open Pre_env
open Genredexpr
open Tacexpr
open Libnames
open Ltac_plugin
open G_tactic

let cbv (pattern: string) : unit tactic =
    let re = Str.regexp pattern in
    tclENV >>=
        fun env ->
            tclEVARMAP >>=
                fun sigma ->
                    let pre_env = Environ.pre_env env in
                    let global = pre_env.env_globals in
                    let matched_or_by_notations = Names.Cmap_env.fold begin fun key const lst ->
                        let name = Names.Constant.to_string key in
                        if Str.string_match re name 0 then
                            try
                                let qualid = qualid_of_string name in
                                let reference = Qualid (None, qualid) in
                                let _ = Feedback.msg_info Pp.(str "matched: " ++ str name) in
                                (Misctypes.AN reference) :: lst
                            with
                                _ -> lst
                        else
                            lst
                    end global.env_constants [] in
                    let gflag = {
                        rBeta = true;
                        (* as suggested by the reference manual, iota reduction is now a shortcut of the following three flags *)
                        rMatch = true;
                        rFix = true;
                        rCofix = true;
                        rZeta = true;
                        rDelta = false; (* refer to definition in genredexpr.ml *)
                        rConst = matched_or_by_notations
                    } in
                    let rexpr_gen : raw_red_expr = Cbv gflag in
                    let raw_tactic : raw_tactic_expr = TacAtom (None, TacReduce (rexpr_gen, G_tactic.all_concl_occs_clause)) in
                    let tactic = Tacinterp.interp raw_tactic in
                    tactic
