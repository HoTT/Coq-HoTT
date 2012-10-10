(* (c) Copyright Microsoft Corporation and Inria. All rights reserved. *)

(* This line is read by the Makefile's dist target: do not remove. *)
let ssrversion = "1.4";;
let ssrAstVersion = 1;;
let () = Mltop.add_known_module "ssreflect";;
let () = 
  if Flags.is_verbose () && not !Flags.batch_mode && 
     (* This is needed when the plugin is statically linked. 
      * Command line args are processed later, thus flags are still unset *)
     not (List.exists (fun x -> x = "-compile" || x = "-where") 
           (Array.to_list Sys.argv))
  then begin
  Printf.printf "\nSmall Scale Reflection version %s loaded.\n" ssrversion;
  Printf.printf "Copyright 2005-2012 Microsoft Corporation and INRIA.\n";
  Printf.printf "Distributed under the terms of the CeCILL-B license.\n\n"
  end
;;
(* Defining grammar rules with "xx" in it automatically declares keywords too *)
let frozen_lexer = Lexer.freeze () ;;

(*i camlp4use: "pa_extend.cmo" i*)
(*i camlp4deps: "parsing/grammar.cma" i*)

open Names
open Pp
open Pcoq
open Genarg
open Term
open Topconstr
open Libnames
open Tactics
open Tacticals
open Termops
open Namegen
open Recordops
open Tacmach
open Coqlib
open Rawterm
open Util
open Evd
open Extend
open Goptions
open Tacexpr
open Tacinterp
open Pretyping.Default
open Constr
open Tactic
open Extraargs
open Ppconstr
open Printer

let inVersion, _ = Libobject.declare_object {
  (Libobject.default_object "SSRASTVERSION") with
  Libobject.load_function = (fun _ (_,v) -> 
    if v <> ssrAstVersion then error "Please recompile your .vo files");
  Libobject.classify_function = (fun v -> Libobject.Keep v);
}

let _ =
  Goptions.declare_bool_option
    { Goptions.optsync  = false;
      Goptions.optname  = "ssreflect version";
      Goptions.optkey   = ["SsrAstVersion"];
      Goptions.optread  = (fun _ -> true);
      Goptions.optwrite = (fun _ -> 
        Lib.add_anonymous_leaf (inVersion ssrAstVersion)) }

let tactic_expr = Tactic.tactic_expr
let gallina_ext = Vernac_.gallina_ext 
let sprintf = Printf.sprintf

(** 0.1 Univalence hacks *)

let build_coq_identity () = (build_coq_identity_data ()).eq
let build_coq_identity_refl () = (build_coq_identity_data ()).refl
let build_coq_identity_sym () = (build_coq_identity_data ()).sym

(** 1. Utilities *)

(* TASSI: 0 cost pp function. Active only if env variable SSRDEBUG is set *)
(* or if SsrDebug is Set                                                  *)
let pp_ref = ref (fun _ -> ())
let ssr_pp s = pperrnl (str"SSR: "++Lazy.force s)
let _ = try ignore(Sys.getenv "SSRDEBUG"); pp_ref := ssr_pp with Not_found -> ()
let _ =
  Goptions.declare_bool_option
    { Goptions.optsync  = false;
      Goptions.optname  = "ssreflect debugging";
      Goptions.optkey   = ["SsrDebug"];
      Goptions.optread  = (fun _ -> !pp_ref == ssr_pp);
      Goptions.optwrite = (fun b -> 
        if b then pp_ref := ssr_pp else pp_ref := fun _ -> ()) }
let pp s = !pp_ref s

let ssroldreworder = ref true
let _ =
  Goptions.declare_bool_option
    { Goptions.optsync  = false;
      Goptions.optname  = "ssreflect 1.3 compatibility flag";
      Goptions.optkey   = ["SsrOldRewriteGoalsOrder"];
      Goptions.optread  = (fun _ -> !ssroldreworder);
      Goptions.optwrite = (fun b -> ssroldreworder := b) }


(** Primitive parsing to avoid syntax conflicts with basic tactics. *)

let accept_before_syms syms strm =
  match Stream.npeek 2 strm with
  | [_; "", sym] when List.mem sym syms -> ()
  | _ -> raise Stream.Failure

let accept_before_syms_or_any_id syms strm =
  match Stream.npeek 2 strm with
  | [_; "", sym] when List.mem sym syms -> ()
  | [_; "IDENT", _] -> ()
  | _ -> raise Stream.Failure

let accept_before_syms_or_ids syms ids strm =
  match Stream.npeek 2 strm with
  | [_; "", sym] when List.mem sym syms -> ()
  | [_; "IDENT", id] when List.mem id ids -> ()
  | _ -> raise Stream.Failure

(** Pretty-printing utilities *)

let pr_id = Ppconstr.pr_id
let pr_name = function Name id -> pr_id id | Anonymous -> str "_"
let pr_spc () = str " "
let pr_bar () = Pp.cut() ++ str "|"
let pr_list = prlist_with_sep

let tacltop = (5,Ppextend.E)

(* More sensible names for constr printers *)

let prl_constr = pr_lconstr
let pr_constr = pr_constr

let prl_rawconstr c = pr_lrawconstr_env (Global.env ()) c
let pr_rawconstr c = pr_rawconstr_env (Global.env ()) c

let prl_constr_expr = pr_lconstr_expr
let pr_constr_expr = pr_constr_expr

let prl_rawconstr_and_expr = function
  | _, Some c -> prl_constr_expr c
  | c, None -> prl_rawconstr c

let pr_rawconstr_and_expr = function
  | _, Some c -> pr_constr_expr c
  | c, None -> pr_rawconstr c

(* Term printing utilities functions for deciding bracketing.  *)

let pr_paren prx x = hov 1 (str "(" ++ prx x ++ str ")")

(* String lexing utilities *)
let skip_wschars s =
  let rec loop i = match s.[i] with '\n'..' ' -> loop (i + 1) | _ -> i in loop

let skip_numchars s =
  let rec loop i = match s.[i] with '0'..'9' -> loop (i + 1) | _ -> i in loop

(* The call 'guard s i' should return true if the contents of s *)
(* starting at i need bracketing to avoid ambiguities.          *)

let pr_guarded guard prc c =
  msg_with Format.str_formatter (prc c);
  let s = Format.flush_str_formatter () ^ "$" in
  if guard s (skip_wschars s 0) then pr_paren prc c else prc c

(** Tactic-level diagnosis *)

let loc_error loc msg = user_err_loc (loc, msg, str msg)

let errorstrm = errorlabstrm "ssreflect"

let pf_pr_constr gl = pr_constr_env (pf_env gl)

let pf_pr_rawconstr gl = pr_rawconstr_env (pf_env gl)

(* debug *)

let pf_msg gl =
   let ppgl = pr_lconstr_env (pf_env gl) (pf_concl gl) in
   msgnl (str "goal is " ++ ppgl)

let msgtac gl = pf_msg gl; tclIDTAC gl

(** Tactic utilities *)

let pf_image gl tac = let gls, _ = tac gl in first_goal gls

let last_goal gls = let sigma, gll = Refiner.unpackage gls in
   Refiner.repackage sigma (List.nth gll (List.length gll - 1))

let pf_image_last gl tac = let gls, _ = tac gl in last_goal gls

let pf_type_id gl t = id_of_string (hdchar (pf_env gl) t)

let not_section_id id = not (is_section_variable id)

let is_pf_var c = isVar c && not_section_id (destVar c)

let pf_ids_of_proof_hyps gl =
  let add_hyp (id, _, _) ids = if not_section_id id then id :: ids else ids in
  Sign.fold_named_context add_hyp (pf_hyps gl) ~init:[]

(* Basic tactics *)

let convert_concl_no_check t = convert_concl_no_check t DEFAULTcast
let convert_concl t = convert_concl t DEFAULTcast
let reduct_in_concl t = reduct_in_concl (t, DEFAULTcast)
let havetac id = pose_proof (Name id)
let settac id c = letin_tac None (Name id) c None
let posetac id cl = settac id cl nowhere

(* we reduce head beta redexes *)
let betared env = 
  Closure.create_clos_infos 
   (Closure.RedFlags.mkflags [Closure.RedFlags.fBETA])
    env
;;
let introid name = tclTHEN (fun gl ->
   let g, env = pf_concl gl, pf_env gl in
   match kind_of_term g with
   | App (hd, _) when isLambda hd -> 
     let g = Closure.whd_val (betared env) (Closure.inject g) in
     convert_concl_no_check g gl
   | _ -> tclIDTAC gl)
  (intro_mustbe_force name)
;;

(** look up a name in the ssreflect internals module *)

let ssrdirpath = make_dirpath [id_of_string "ssreflect"]
let ssrqid name = make_qualid ssrdirpath (id_of_string name) 
let ssrtopqid name = make_short_qualid (id_of_string name) 

let locate_reference qid =
  Smartlocate.global_of_extended_global (Nametab.locate_extended qid)

let mkSsrRef name =
  try locate_reference (ssrqid name) with Not_found ->
  try locate_reference (ssrtopqid name) with Not_found ->
  error "Small scale reflection library not loaded (mkSsrRef)"

let mkSsrRRef name = RRef (dummy_loc, mkSsrRef name)

let mkSsrConst name = constr_of_reference (mkSsrRef name)

(** Ssreflect load check. *)

(* To allow ssrcoq to be fully compatible with the "plain" Coq, we only *)
(* turn on its incompatible features (the new rewrite syntax, and the   *)
(* reserved identifiers) when the theory library (ssreflect.v) has      *)
(* has actually been required, or is being defined. Because this check  *)
(* needs to be done often (for each identifier lookup), we implement    *)
(* some caching, repeating the test only when the environment changes.  *)
(*   We check for protect_term because it is the first constant loaded; *)
(* ssr_have would ultimately be a better choice.                        *)

let ssr_loaded =
  let cache = ref (Global.safe_env (), false) in
  fun () ->
    Lexer.is_keyword "is" &&
    let new_lbl = Global.safe_env () in
    match !cache with
    | lbl, loaded when lbl == new_lbl -> loaded
    | _ ->
       let loaded =
         (try ignore (mkSsrRef "protect_term"); true with _ -> false) in
       cache := new_lbl, loaded; loaded

(** Name generation *)

(* Since Coq now does repeated internal checks of its external lexical *)
(* rules, we now need to carve ssreflect reserved identifiers out of   *)
(* out of the user namespace. We use identifiers of the form _id_ for  *)
(* this purpose, e.g., we "anonymize" an identifier id as _id_, adding *)
(* an extra leading _ if this might clash with an internal identifier. *)
(*    We check for ssreflect identifiers in the ident grammar rule;    *)
(* when the ssreflect Module is present this is normally an error,     *)
(* but we provide a compatibility flag to reduce this to a warning.    *)

let ssr_reserved_ids = ref true

let _ =
  Goptions.declare_bool_option
    { Goptions.optsync  = true;
      Goptions.optname  = "ssreflect identifiers";
      Goptions.optkey   = ["SsrIdents"];
      Goptions.optread  = (fun _ -> !ssr_reserved_ids);
      Goptions.optwrite = (fun b -> ssr_reserved_ids := b)
    }

let is_ssr_reserved s =
  let n = String.length s in n > 2 && s.[0] = '_' && s.[n - 1] = '_'

let internal_names = ref []
let add_internal_name pt = internal_names := pt :: !internal_names
let is_internal_name s = List.exists (fun p -> p s) !internal_names

let ssr_id_of_string loc s =
  if is_ssr_reserved s && ssr_loaded () then begin
    if !ssr_reserved_ids then
      loc_error loc ("The identifier " ^ s ^ " is reserved.")
    else if is_internal_name s then
      warning ("Conflict between " ^ s ^ " and ssreflect internal names.")
    else warning (
     "The name " ^ s ^ " fits the _xxx_ format used for anonymous variables.\n"
  ^ "Scripts with explicit references to anonymous variables are fragile.")
    end; id_of_string s

let ssr_null_entry = Gram.Entry.of_parser "ssr_null" (fun _ -> ())

GEXTEND Gram 
  GLOBAL: Prim.ident;
  Prim.ident: [[ s = IDENT; ssr_null_entry -> ssr_id_of_string loc s ]];
END

let mk_internal_id s =
  let s' = sprintf "_%s_" s in
  for i = 1 to String.length s do if s'.[i] = ' ' then s'.[i] <- '_' done;
  add_internal_name ((=) s'); id_of_string s'

let same_prefix s t n =
  let rec loop i = i = n || s.[i] = t.[i] && loop (i + 1) in loop 0

let skip_digits s =
  let n = String.length s in 
  let rec loop i = if i < n && is_digit s.[i] then loop (i + 1) else i in loop

let mk_tagged_id t i = id_of_string (sprintf "%s%d_" t i)
let is_tagged t s =
  let n = String.length s - 1 and m = String.length t in
  m < n && s.[n] = '_' && same_prefix s t m && skip_digits s m = n

let perm_tag = "_perm_Hyp_"
let _ = add_internal_name (is_tagged perm_tag)
let mk_perm_id =
  let salt = ref 1 in 
  fun () -> salt := !salt mod 10000 + 1; mk_tagged_id perm_tag !salt

let evar_tag = "_evar_"
let _ = add_internal_name (is_tagged evar_tag)
let mk_evar_name n = Name (mk_tagged_id evar_tag n)
let nb_evar_deps = function
  | Name id ->
    let s = string_of_id id in
    if not (is_tagged evar_tag s) then 0 else
    let m = String.length evar_tag in
    (try int_of_string (String.sub s m (String.length s - 1 - m)) with _ -> 0)
  | _ -> 0

let discharged_tag = "_discharged_"
let mk_discharged_id id =
  id_of_string (sprintf "%s%s_" discharged_tag (string_of_id id))
let has_discharged_tag s =
  let m = String.length discharged_tag and n = String.length s - 1 in
  m < n && s.[n] = '_' && same_prefix s discharged_tag m
let _ = add_internal_name has_discharged_tag
let is_discharged_id id = has_discharged_tag (string_of_id id)

let wildcard_tag = "_the_"
let wildcard_post = "_wildcard_"
let mk_wildcard_id i =
  id_of_string (sprintf "%s%s%s" wildcard_tag (ordinal i) wildcard_post)
let has_wildcard_tag s = 
  let n = String.length s in let m = String.length wildcard_tag in
  let m' = String.length wildcard_post in
  n < m + m' + 2 && same_prefix s wildcard_tag m &&
  String.sub s (n - m') m' = wildcard_post &&
  skip_digits s m = n - m' - 2
let _ = add_internal_name has_wildcard_tag

let max_suffix m (t, j0 as tj0) id  =
  let s = string_of_id id in let n = String.length s - 1 in
  let dn = String.length t - 1 - n in let i0 = j0 - dn in
  if not (i0 >= m && s.[n] = '_' && same_prefix s t m) then tj0 else
  let rec loop i =
    if i < i0 && s.[i] = '0' then loop (i + 1) else
    if (if i < i0 then skip_digits s i = n else le_s_t i) then s, i else tj0
  and le_s_t i =
    let ds = s.[i] and dt = t.[i + dn] in
    if ds = dt then i = n || le_s_t (i + 1) else
    dt < ds && skip_digits s i = n in
  loop m

let mk_anon_id t gl =
  let m, si0, id0 =
    let s = ref (sprintf  "_%s_" t) in
    if is_internal_name !s then s := "_" ^ !s;
    let n = String.length !s - 1 in
    let rec loop i j =
      let d = !s.[i] in if not (is_digit d) then i + 1, j else
      loop (i - 1) (if d = '0' then j else i) in
    let m, j = loop (n - 1) n in m, (!s, j), id_of_string !s in
  let gl_ids = pf_ids_of_hyps gl in
  if not (List.mem id0 gl_ids) then id0 else
  let s, i = List.fold_left (max_suffix m) si0 gl_ids in
  let n = String.length s - 1 in
  let rec loop i =
    if s.[i] = '9' then (s.[i] <- '0'; loop (i - 1)) else
    if i < m then (s.[n] <- '0'; s.[m] <- '1'; s ^ "_") else
    (s.[i] <- Char.chr (Char.code s.[i] + 1); s) in
  id_of_string (loop (n - 1))
  
(* We must not anonymize context names discharged by the "in" tactical. *)

let ssr_anon_hyp = "Hyp"

let anontac (x, _, _) gl =
  let id =  match x with
  | Name id ->
    if is_discharged_id id then id else mk_anon_id (string_of_id id) gl
  | _ -> mk_anon_id ssr_anon_hyp gl in
  introid id gl

let rec constr_name c = match kind_of_term c with
  | Var id -> Name id
  | Cast (c', _, _) -> constr_name c'
  | Const cn -> Name (id_of_label (con_label cn))
  | App (c', _) -> constr_name c'
  | _ -> Anonymous

(** Constructors for cast type *)
let dC t = CastConv(DEFAULTcast, t)

(** Constructors for constr_expr *)

let mkCProp loc = CSort (loc, RProp Null)

let mkCType loc = CSort (loc, RType None)

let mkCVar loc id = CRef (Ident (loc, id))
let isCVar = function CRef (Ident _) -> true | _ -> false
let destCVar = function CRef (Ident (_, id)) -> id | _ -> anomaly "not a CRef"

let rec mkCHoles loc n =
  if n <= 0 then [] else CHole (loc, None) :: mkCHoles loc (n - 1)

let mkCHole loc = CHole (loc, None)

let rec isCHoles = function CHole _ :: cl -> isCHoles cl | cl -> cl = []

let mkCExplVar loc id n =
   CAppExpl (loc, (None, Ident (loc, id)), mkCHoles loc n)

let mkCLambda loc name ty t = 
   CLambdaN (loc, [[loc, name], Default Explicit, ty], t)

let mkCLetIn loc name bo t = 
   CLetIn (loc, (loc, name), bo, t)

let mkCArrow loc ty t = CArrow (loc, ty, t)

let mkCCast loc t ty = CCast (loc,t, dC ty)

(** Constructors for rawconstr *)

let mkRHole = RHole (dummy_loc, InternalHole)

let rec mkRHoles n = if n > 0 then mkRHole :: mkRHoles (n - 1) else []

let rec isRHoles = function RHole _ :: cl -> isRHoles cl | cl -> cl = []

let mkRApp f args = if args = [] then f else RApp (dummy_loc, f, args)

let mkRVar id = RRef (dummy_loc, VarRef id)

let mkRltacVar id = RVar (dummy_loc, id)

let mkRCast rc rt =  RCast (dummy_loc, rc, dC rt)

let mkRType =  RSort (dummy_loc, RType None)

let mkRProp =  RSort (dummy_loc, RProp Null)

let mkRArrow rt1 rt2 = RProd (dummy_loc, Anonymous, Explicit, rt1, rt2)

let mkRConstruct c = RRef (dummy_loc, ConstructRef c)

let mkRInd mind = RRef (dummy_loc, IndRef mind)

let mkRLambda n s t = RLambda (dummy_loc, n, Explicit, s, t)

(** Constructors for constr *)

let mkAppRed f c = match kind_of_term f with
| Lambda (_, _, b) -> subst1 c b
| _ -> mkApp (f, [|c|])

let mkProt t c = mkApp (mkSsrConst "protect_term", [|t; c|])

let mkRefl t c = mkApp ((build_coq_identity_data()).refl, [|t; c|])

(* Application to a sequence of n rels (for building eta-expansions). *)
(* The rel indices decrease down to imin (inclusive), unless n < 0,   *)
(* in which case they're incresing (from imin).                       *)
let mkEtaApp c n imin =
  if n = 0 then c else
  let nargs, mkarg =
    if n < 0 then -n, (fun i -> mkRel (imin + i)) else
    let imax = imin + n - 1 in n, (fun i -> mkRel (imax - i)) in
  mkApp (c, Array.init nargs mkarg)

(* Same, but optimizing head beta redexes *)
let rec whdEtaApp c n =
  if n = 0 then c else match kind_of_term c with
  | Lambda (_, _, c') -> whdEtaApp c' (n - 1)
  | _ -> mkEtaApp (lift n c) n 1

let isEvar_k k f =
  match kind_of_term f with Evar (k', _) -> k = k' | _ -> false

let mkSubArg i a = if i = Array.length a then a else Array.sub a 0 i
let mkSubApp f i a = if i = 0 then f else mkApp (f, mkSubArg i a)

let safeDestApp c =
  match kind_of_term c with App (f, a) -> f, a | _ -> c, [| |]
let nb_args c =
  match kind_of_term c with App (_, a) -> Array.length a | _ -> 0

let splay_app ise =
  let rec loop c a = match kind_of_term c with
  | App (f, a') -> loop f (Array.append a' a)
  | Cast (c', _, _) -> loop c' a
  | Evar ex ->
    (try loop (existential_value ise ex) a with _ -> c, a)
  | _ -> c, a in
  fun c -> match kind_of_term c with
  | App (f, a) -> loop f a
  | Cast _ | Evar _ -> loop c [| |]
  | _ -> c, [| |]

(* ssrterm conbinators *)

let combineCG t1 t2 f g = match t1, t2 with
 | (x, (t1, None)), (_, (t2, None)) -> x, (g t1 t2, None)
 | (x, (_, Some t1)), (_, (_, Some t2)) -> x, (mkRHole, Some (f t1 t2))
 | _, (_, (_, None)) -> anomaly "have: mixed C-G constr"
 | _ -> anomaly "have: mixed G-C constr"

let loc_ofCG = function
 | (_, (s, None)) -> Rawterm.loc_of_rawconstr s
 | (_, (_, Some s)) -> Topconstr.constr_loc s

(** Open term to lambda-term coercion *)

(* This operation takes a goal gl and an open term (sigma, t), and   *)
(* returns a term t' where all the new evars in sigma are abstracted *)
(* with the mkAbs argument, i.e., for mkAbs = mkLambda then there is *)
(* some duplicate-free array args of evars of sigma such that the    *)
(* term mkApp (t', args) is convertible to t.                        *)
(* This makes a useful shorthand for local definitions in proofs,    *)
(* i.e., pose succ := _ + 1 means pose succ := fun n : nat => n + 1, *)
(* and, in context of the the 4CT library, pose mid := maps id means *)
(*    pose mid := fun d : detaSet => @maps d d (@id (datum d))       *)
(* Note that this facility does not extend to set, which tries       *)
(* instead to fill holes by matching a goal subterm.                 *)
(* The argument to "have" et al. uses product abstraction, e.g.      *)
(*    have Hmid: forall s, (maps id s) = s.                          *)
(* stands for                                                        *)
(*    have Hmid: forall (d : dataSet) (s : seq d), (maps id s) = s.  *)
(* We also use this feature for rewrite rules, so that, e.g.,        *)
(*   rewrite: (plus_assoc _ 3).                                      *)
(* will execute as                                                   *)
(*   rewrite (fun n => plus_assoc n 3)                               *)
(* i.e., it will rewrite some subterm .. + (3 + ..) to .. + 3 + ...  *)
(* The convention is also used for the argument of the congr tactic, *)
(* e.g., congr (x + _ * 1).                                          *)

let env_size env = List.length (Environ.named_context env)

(* Replace new evars with lambda variables, retaining local dependencies *)
(* but stripping global ones. We use the variable names to encode the    *)
(* the number of dependencies, so that the transformation is reversible. *)

let pf_abs_evars gl (sigma, c0) =
  let sigma0 = project gl in
  let nenv = env_size (pf_env gl) in
  let abs_evar n k =
    let evi = Evd.find sigma k in
    let dc = list_firstn n (evar_filtered_context evi) in
    let abs_dc c = function
    | x, Some b, t -> mkNamedLetIn x b t (mkArrow t c)
    | x, None, t -> mkNamedProd x t c in
    let t = Sign.fold_named_context_reverse abs_dc ~init:evi.evar_concl dc in
    Evarutil.nf_evar sigma t in
  let rec put evlist c = match kind_of_term c with
  | Evar (k, a) ->  
    if List.mem_assoc k evlist || Evd.mem sigma0 k then evlist else
    let n = max 0 (Array.length a - nenv) in
    let t = abs_evar n k in (k, (n, t)) :: put evlist t
  | _ -> fold_constr put evlist c in
  let evlist = put [] c0 in
  if evlist = [] then 0, c0 else
  let rec lookup k i = function
    | [] -> 0, 0
    | (k', (n, _)) :: evl -> if k = k' then i, n else lookup k (i + 1) evl in
  let rec get i c = match kind_of_term c with
  | Evar (ev, a) ->
    let j, n = lookup ev i evlist in
    if j = 0 then map_constr (get i) c else if n = 0 then mkRel j else
    mkApp (mkRel j, Array.init n (fun k -> get i a.(n - 1 - k)))
  | _ -> map_constr_with_binders ((+) 1) get i c in
  let rec loop c i = function
  | (_, (n, t)) :: evl ->
    loop (mkLambda (mk_evar_name n, get (i - 1) t, c)) (i - 1) evl
  | [] -> c in
  List.length evlist, loop (get 1 c0) 1 evlist



(* As before but if (?i : T(?j)) and (?j : P : Prop), then the lambda for i
 * looks like (fun evar_i : (forall pi : P. T(pi))) thanks to "loopP" and all 
 * occurrences of evar_i are replaced by (evar_i evar_j) thanks to "app".
 *
 * If P can be solved by ssrautoprop (that defaults to trivial), then
 * the corresponding lambda looks like (fun evar_i : T(c)) where c is 
 * the solution found by ssrautoprop.
 *)
let ssrautoprop_tac = ref (fun gl -> assert false)

let pf_abs_evars_pirrel gl (sigma, c0) =
  pp(lazy(str"==PF_ABS_EVARS_PIRREL=="));
  pp(lazy(str"c0= " ++ pr_constr c0));
  let sigma0 = project gl in
  let nenv = env_size (pf_env gl) in
  let abs_evar n k =
    let evi = Evd.find sigma k in
    let dc = list_firstn n (evar_filtered_context evi) in
    let abs_dc c = function
    | x, Some b, t -> mkNamedLetIn x b t (mkArrow t c)
    | x, None, t -> mkNamedProd x t c in
    let t = Sign.fold_named_context_reverse abs_dc ~init:evi.evar_concl dc in
    Evarutil.nf_evar sigma t in
  let rec put evlist c = match kind_of_term c with
  | Evar (k, a) ->  
    if List.mem_assoc k evlist || Evd.mem sigma0 k then evlist else
    let n = max 0 (Array.length a - nenv) in
    let k_ty = 
      Retyping.get_sort_family_of 
        (pf_env gl) sigma (Evd.evar_concl (Evd.find sigma k)) in
    let is_prop = k_ty = InProp in
    let t = abs_evar n k in (k, (n, t, is_prop)) :: put evlist t
  | _ -> fold_constr put evlist c in
  let evlist = put [] c0 in
  if evlist = [] then 0, c0 else
  let pr_constr t = pr_constr (Reductionops.nf_beta (project gl) t) in
  let evplist = 
    let depev = List.fold_left (fun evs (_,(_,t,_)) -> 
        Intset.union evs (Evarutil.evars_of_term t)) Intset.empty evlist in
    List.filter (fun i,(_,_,b) -> b && Intset.mem i depev) evlist in
  let evlist, evplist, sigma = 
    if evplist = [] then evlist, [], sigma else
    List.fold_left (fun (ev, evp, sigma) (i, (_,t,_) as p) ->
      try 
        let proof = ref (fun _ -> assert false) in
        let t = Evarutil.nf_evar sigma t in
        let tac gl = 
          let gl, p = !ssrautoprop_tac gl in 
          if sig_it gl = [] then (proof := p; gl, p) else errorstrm (str"XX") in
        ignore(tclTHENS (Tactics.cut t) [tclIDTAC; tac] gl);
        let c, hyps = Refiner.extract_open_proof sigma (!proof []) in
        assert(hyps = []);
        let sigma = Evd.define i c sigma in
        List.filter (fun (j,_) -> j <> i) ev, evp, sigma
      with _ -> ev, p::evp, sigma) (evlist, [], sigma) (List.rev evplist) in
  let c0 = Evarutil.nf_evar sigma c0 in
  let evlist = 
    List.map (fun (x,(y,t,z)) -> x,(y,Evarutil.nf_evar sigma t,z)) evlist in
  let evplist = 
    List.map (fun (x,(y,t,z)) -> x,(y,Evarutil.nf_evar sigma t,z)) evplist in
  pp(lazy(str"c0= " ++ pr_constr c0));
  let rec lookup k i = function
    | [] -> 0, 0
    | (k', (n,_,_)) :: evl -> if k = k' then i,n else lookup k (i + 1) evl in
  let rec get evlist i c = match kind_of_term c with
  | Evar (ev, a) ->
    let j, n = lookup ev i evlist in
    if j = 0 then map_constr (get evlist i) c else if n = 0 then mkRel j else
    mkApp (mkRel j, Array.init n (fun k -> get evlist i a.(n - 1 - k)))
  | _ -> map_constr_with_binders ((+) 1) (get evlist) i c in
  let rec app extra_args i c = match decompose_app c with
  | hd, args when isRel hd && destRel hd = i ->
      let j = destRel hd in
      mkApp (mkRel j, Array.of_list (List.map (lift (i-1)) extra_args @ args))
  | _ -> map_constr_with_binders ((+) 1) (app extra_args) i c in
  let rec loopP evlist c i = function
  | (_, (n, t, _)) :: evl ->
    let t = get evlist (i - 1) t in
    let n = Name (id_of_string (ssr_anon_hyp ^ string_of_int n)) in 
    loopP evlist (mkProd (n, t, c)) (i - 1) evl
  | [] -> c in
  let rec loop c i = function
  | (_, (n, t, _)) :: evl ->
    let evs = Evarutil.evars_of_term t in
    let t_evplist = List.filter (fun (k,_) -> Intset.mem k evs) evplist in
    let t = loopP t_evplist (get t_evplist 1 t) 1 t_evplist in
    let t = get evlist (i - 1) t in
    let extra_args = 
      List.map (fun (k,_) -> mkRel (fst (lookup k i evlist))) 
        (List.rev t_evplist) in
    let c = if extra_args = [] then c else app extra_args 1 c in
    loop (mkLambda (mk_evar_name n, t, c)) (i - 1) evl
  | [] -> c in
  let res = loop (get evlist 1 c0) 1 evlist in
  pp(lazy(str"res= " ++ pr_constr res)); 
  List.length evlist, res

(* A simplified version of the code above, to turn (new) evars into metas *)
let evars_for_FO ~hack env sigma0 (ise0:evar_map) c0 =
  let ise = ref ise0 in
  let sigma = ref ise0 in
  let nenv = env_size env + if hack then 1 else 0 in
  let rec put c = match kind_of_term c with
  | Evar (k, a as ex) ->
    begin try put (existential_value !sigma ex)
    with NotInstantiatedEvar ->
    if Evd.mem sigma0 k then map_constr put c else
    let evi = Evd.find !sigma k in
    let dc = list_firstn (max 0 (Array.length a - nenv)) (evar_filtered_context evi) in
    let abs_dc (d, c) = function
    | x, Some b, t -> d, mkNamedLetIn x (put b) (put t) c
    | x, None, t -> mkVar x :: d, mkNamedProd x (put t) c in
    let a, t =
      Sign.fold_named_context_reverse abs_dc ~init:([], evi.evar_concl) dc in
    let m = Evarutil.new_meta () in
    ise := meta_declare m t !ise;
    sigma := Evd.define k (applist (mkMeta m, List.rev a)) !sigma;
    put (existential_value !sigma ex)
    end
  | _ -> map_constr put c in
  let c1 = put c0 in !ise, c1

(* Strip all non-essential dependencies from an abstracted term, generating *)
(* standard names for the abstracted holes.                                 *)

let pf_abs_cterm gl n c0 =
  if n <= 0 then c0 else
  let noargs = [|0|] in
  let eva = Array.make n noargs in
  let rec strip i c = match kind_of_term c with
  | App (f, a) when isRel f ->
    let j = i - destRel f in
    if j >= n || eva.(j) = noargs then mkApp (f, Array.map (strip i) a) else
    let dp = eva.(j) in
    let nd = Array.length dp - 1 in
    let mkarg k = strip i a.(if k < nd then dp.(k + 1) - j else k + dp.(0)) in
    mkApp (f, Array.init (Array.length a - dp.(0)) mkarg)
  | _ -> map_constr_with_binders ((+) 1) strip i c in
  let rec strip_ndeps j i c = match kind_of_term c with
  | Prod (x, t, c1) when i < j ->
    let dl, c2 = strip_ndeps j (i + 1) c1 in
    if noccurn 1 c2 then dl, lift (-1) c2 else
    i :: dl, mkProd (x, strip i t, c2)
  | LetIn (x, b, t, c1) when i < j ->
    let _, _, c1' = destProd c1 in
    let dl, c2 = strip_ndeps j (i + 1) c1' in
    if noccurn 1 c2 then dl, lift (-1) c2 else
    i :: dl, mkLetIn (x, strip i b, strip i t, c2)
  | _ -> [], strip i c in
  let rec strip_evars i c = match kind_of_term c with
    | Lambda (x, t1, c1) when i < n ->
      let na = nb_evar_deps x in
      let dl, t2 = strip_ndeps (i + na) i t1 in
      let na' = List.length dl in
      eva.(i) <- Array.of_list (na - na' :: dl);
      let x' =
        if na' = 0 then Name (pf_type_id gl t2) else mk_evar_name na' in
      mkLambda (x', t2, strip_evars (i + 1) c1)
(*      if noccurn 1 c2 then lift (-1) c2 else
      mkLambda (Name (pf_type_id gl t2), t2, c2) *)
    | _ -> strip i c in
  strip_evars 0 c0

(* Undo the evar abstractions. Also works for non-evar variables. *)

let pf_unabs_evars gl ise n c0 =
  if n = 0 then c0 else
  let evv = Array.make n mkImplicit in
  let nev = ref 0 in
  let env0 = pf_env gl in
  let nenv0 = env_size env0 in
  let rec unabs i c = match kind_of_term c with
  | Rel j when i - j < !nev -> evv.(i - j)
  | App (f, a0) when isRel f ->
    let a = Array.map (unabs i) a0 in
    let j = i - destRel f in
    if j >= !nev then mkApp (f, a) else
    let ev, eva = destEvar evv.(j) in
    let nd = Array.length eva - nenv0 in
    if nd = 0 then mkApp (evv.(j), a) else
    let evarg k = if k < nd then a.(nd - 1 - k) else eva.(k) in
    let c' = mkEvar (ev, Array.init (nd + nenv0) evarg) in
    let na = Array.length a - nd in
    if na = 0 then c' else mkApp (c', Array.sub a nd na)
  | _ -> map_constr_with_binders ((+) 1) unabs i c in
  let push_rel = Environ.push_rel in
  let rec mk_evar j env i c = match kind_of_term c with
  | Prod (x, t, c1) when i < j ->
    mk_evar j (push_rel (x, None, unabs i t) env) (i + 1) c1
  | LetIn (x, b, t, c1) when i < j ->
    let _, _, c2 = destProd c1 in
    mk_evar j (push_rel (x, Some (unabs i b), unabs i t) env) (i + 1) c2
  | _ -> Evarutil.e_new_evar ise env (unabs i c) in
  let rec unabs_evars c =
    if !nev = n then unabs n c else match kind_of_term c with
  | Lambda (x, t, c1) when !nev < n ->
    let i = !nev in
    evv.(i) <- mk_evar (i + nb_evar_deps x) env0 i t;
    incr nev; unabs_evars c1
  | _ -> unabs !nev c in
  unabs_evars c0

(** Adding a new uninterpreted generic argument type *)

let add_genarg tag pr =
  let wit, globwit, rawwit as wits = create_arg tag in
  let glob _ rarg = in_gen globwit (out_gen rawwit rarg) in
  let interp _ _ garg = in_gen wit (out_gen globwit garg) in
  let subst _ garg = garg in
  add_interp_genarg tag (glob, interp, subst);
  let gen_pr _ _ _ = pr in
  Pptactic.declare_extra_genarg_pprule
    (rawwit, gen_pr) (globwit, gen_pr) (wit, gen_pr);
  wits

(** Tactical extensions. *)

(* The TACTIC EXTEND facility can't be used for defining new user   *)
(* tacticals, because:                                              *)
(*  - the concrete syntax must start with a fixed string            *)
(*  - the lexical Ltac environment is NOT used to interpret tactic  *)
(*    arguments                                                     *)
(* The second limitation means that the extended tacticals will     *)
(* exhibit run-time scope errors if used inside Ltac functions or   *)
(* pattern-matching constructs.                                     *)
(*   We use the following workaround:                               *)
(*  - We use the (unparsable) "(**)"  token for tacticals that      *)
(*    don't start with a token, then redefine the grammar and       *)
(*    printer using GEXTEND and set_pr_ssrtac, respectively.        *)
(*  - We use a global stack and side effects to pass the lexical    *)
(*    Ltac evaluation context to the extended tactical. The context *)
(*    is grabbed by interpreting an (empty) ssrltacctx argument,    *)
(*    which should appear last in the grammar rules; the            *)
(*    get_ltacctx function pops the stack and returns the context.  *)
(*      For additional safety, the push returns an integer key that *)
(*    is checked by the pop; since arguments are interpreted        *)
(*    left-to-right, this checks that only one tactic argument      *)
(*    pushes a context.                                             *)
(* - To avoid a spurrious option type, we don't push the context    *)
(*    for a null tag.                                               *)

type ssrargfmt = ArgSsr of string | ArgCoq of argument_type | ArgSep of string

let set_pr_ssrtac name prec afmt =
  let fmt = List.map (function ArgSep s -> Some s | _ -> None) afmt in
  let rec mk_akey = function
  | ArgSsr s :: afmt' -> ExtraArgType ("ssr" ^ s) :: mk_akey afmt'
  | ArgCoq a :: afmt' -> a :: mk_akey afmt'
  | ArgSep _ :: afmt' -> mk_akey afmt'
  | [] -> [] in
  let tacname = "ssr" ^ name in
  Pptactic.declare_extra_tactic_pprule (tacname, mk_akey afmt, (prec, fmt))

let ssrtac_atom loc name args = TacExtend (loc, "ssr" ^ name, args)
let ssrtac_expr loc name args = TacAtom (loc, ssrtac_atom loc name args)

type ssrltacctx = int

let pr_ssrltacctx _ _ _ _ = mt ()

let ssrltacctxs = ref (1, [])

let interp_ltacctx ist _ n0 =
  if n0 = 0 then 0 else
  let n, s = !ssrltacctxs in
  let n' = if n >= max_int then 1 else n + 1 in
  ssrltacctxs := (n', (n, ist) :: s); n

let noltacctx = 0
let rawltacctx = 1

ARGUMENT EXTEND ssrltacctx TYPED AS int PRINTED BY pr_ssrltacctx
  INTERPRETED BY interp_ltacctx
| [ ] -> [ rawltacctx ]
END

let get_ltacctx i = match !ssrltacctxs with
| _ when i = noltacctx -> Util.anomaly "Missing Ltac context"
| n, (i', ist) :: s when i' = i -> ssrltacctxs := (n, s); ist
| _ -> Util.anomaly "Bad scope in SSR tactical"

let ssrevaltac ist gtac =
  interp_tac_gen ist.lfun [] ist.debug (globTacticIn (fun _ -> gtac))

(* fun gl -> let lfun = [tacarg_id, val_interp ist gl gtac] in
  interp_tac_gen lfun [] ist.debug tacarg_expr gl *)

(** Generic argument-based globbing/typing utilities *)

(* Toplevel constr must be globalized twice ! *)
let glob_constr ist gsigma genv = function
  | _, Some ce ->
    let ltacvars = List.map fst ist.lfun, [] in
    Constrintern.intern_gen false ~ltacvars:ltacvars gsigma genv ce
  | rc, None -> rc

let interp_wit globwit wit ist gl x = 
  let globarg = in_gen globwit x in
  let arg = interp_genarg ist gl globarg in
  out_gen wit arg

let interp_intro_pattern = interp_wit globwit_intro_pattern wit_intro_pattern

let interp_constr = interp_wit globwit_constr wit_constr

let interp_open_constr ist gl gc =
  interp_wit globwit_open_constr wit_open_constr ist gl ((), gc)

let interp_refine ist gl rc =
   let roc = (), (rc, None) in
   interp_wit globwit_casted_open_constr wit_casted_open_constr ist gl roc

let pf_match = pf_apply (fun e s c t -> understand_tcc s e ~expected_type:t c)

(* Estimate a bound on the number of arguments of a raw constr. *)
(* This is not perfect, because the unifier may fail to         *)
(* typecheck the partial application, so we use a minimum of 5. *)
(* Also, we don't handle delayed or iterated coercions to       *)
(* FUNCLASS, which is probably just as well since these can     *)
(* lead to infinite arities.                                    *)

let splay_open_constr gl (sigma, c) =
  let env = pf_env gl in let t = Retyping.get_type_of env sigma c in
  Reductionops.splay_prod env sigma t

let nbargs_open_constr gl oc =
  let pl, _ = splay_open_constr gl oc in List.length pl

let interp_nbargs ist gl rc =
  try
    let rc6 = mkRApp rc (mkRHoles 6) in
    6 + nbargs_open_constr gl (interp_open_constr ist gl (rc6, None))
  with _ -> 5

let pf_nbargs gl c = nbargs_open_constr gl (project gl, c)

let isAppInd gl c =
  try ignore (pf_reduce_to_atomic_ind gl c); true with _ -> false

let interp_view_nbimps ist gl rc =
  try
    let pl, c = splay_open_constr gl (interp_open_constr ist gl (rc, None)) in
    if isAppInd gl c then List.length pl else ~-(List.length pl)
  with _ -> 0


(** 2. Vernacular commands: Prenex Implicits and Search *)

(* This should really be implemented as an extension to the implicit   *)
(* arguments feature, but unfortuately that API is sealed. The current *)
(* workaround uses a combination of notations that works reasonably,   *)
(* with the following caveats:                                         *)
(*  - The pretty-printing always elides prenex implicits, even when    *)
(*    they are obviously needed.                                       *)
(*  - Prenex Implicits are NEVER exported from a module, because this  *)
(*    would lead to faulty pretty-printing and scoping errors.         *)
(*  - The command "Import Prenex Implicits" can be used to reassert    *)
(*    Prenex Implicits for all the visible constants that had been     *)
(*    declared as Prenex Implicits.                                    *)

let declare_one_prenex_implicit locality f =
  let fref =
    try Smartlocate.global_with_alias f 
    with _ -> errorstrm (pr_reference f ++ str " is not declared") in
  let rec loop = function
  | a :: args' when Impargs.is_status_implicit a ->
    (ExplByName (Impargs.name_of_implicit a), (true, true, true)) :: loop args'
  | args' when List.exists Impargs.is_status_implicit args' ->
      errorstrm (str "Expected prenex implicits for " ++ pr_reference f)
  | _ -> [] in
  let impls =
    match Impargs.implicits_of_global fref  with
    | [cond,impls] -> impls
    | [] -> errorstrm (str "Expected some implicits for " ++ pr_reference f)
    | _ -> errorstrm (str "Multiple implicits not supported") in
  match loop impls  with
  | [] ->
    errorstrm (str "Expected some implicits for " ++ pr_reference f)
  | impls ->
    Impargs.declare_manual_implicits locality fref ~enriching:false [impls]

VERNAC COMMAND EXTEND Ssrpreneximplicits
  | [ "Prenex" "Implicits" ne_global_list(fl) ]
  -> [ let locality = Vernacexpr.use_section_locality () in
       List.iter (declare_one_prenex_implicit locality) fl ]
END

(* Vernac grammar visibility patch *)

GEXTEND Gram
  GLOBAL: gallina_ext;
  gallina_ext:
   [ [ IDENT "Import"; IDENT "Prenex"; IDENT "Implicits" ->
      Vernacexpr.VernacUnsetOption (None, ["Printing"; "Implicit"; "Defensive"])
   ] ]
  ;
END

(* Remove the silly restriction that forces coercion classes to be precise *)
(* aliases, e.g., allowing notations that specify some class parameters.   *)

let qualify_ref clref =
  let loc, qid = qualid_of_reference clref in
  try match Nametab.locate_extended qid with
  | TrueGlobal _ -> clref
  | SynDef kn ->
    let rec head_of = function
    |  ARef gref ->
          Qualid (loc, Nametab.shortest_qualid_of_global Idset.empty gref)
    |  AApp (rc, _) -> head_of rc
    |  ACast (rc, _) -> head_of rc
    |  ALetIn (_, _, rc) -> head_of rc
    | rc ->
       user_err_loc (loc, "qualify_ref",
        str "The definition of " ++ Ppconstr.pr_qualid qid
             ++ str " does not have a head constant") in
    head_of (snd (Syntax_def.search_syntactic_definition kn))
  with _ -> clref

let class_rawexpr = G_vernac.class_rawexpr in
GEXTEND Gram
  GLOBAL: class_rawexpr;
  ssrqref: [[ gref = global -> qualify_ref gref ]];
  class_rawexpr: [[ class_ref = ssrqref -> Vernacexpr.RefClass (Genarg.AN class_ref) ]];
END

(** Extend Search to subsume SearchAbout, also adding hidden Type coercions. *)

(* Main prefilter *)

let pr_search_item = function
  | Search.GlobSearchString s -> str s
  | Search.GlobSearchSubPattern p -> pr_constr_pattern p

let wit_ssr_searchitem, globwit_ssr_searchitem, rawwit_ssr_searchitem =
  add_genarg "ssrsearchitem" pr_search_item

let interp_search_notation loc s opt_scope =
  try
    let interp = Notation.interp_notation_as_global_reference loc in
    let ref = interp (fun _ -> true) s opt_scope in
    Search.GlobSearchSubPattern (Pattern.PRef ref)
  with _ ->
    let diagnosis =
      try
        let ntns = Notation.locate_notation pr_rawconstr s opt_scope in
        let ambig = "This string refers to a complex or ambiguous notation." in
        str ambig ++ str "\nTry searching with one of\n" ++ ntns
      with _ -> str "This string is not part of an identifier or notation." in
    user_err_loc (loc, "interp_search_notation", diagnosis)

let pr_ssr_search_item _ _ _ = pr_search_item

(* Workaround the notation API that can only print notations *)

let is_ident s = try Lexer.check_ident s; true with _ -> false

let is_ident_part s = is_ident ("H" ^ s)

let interp_search_notation loc tag okey =
  let err msg = user_err_loc (loc, "interp_search_notation", msg) in
  let mk_pntn s for_key =
    let n = String.length s in
    let s' = String.make (n + 2) ' ' in
    let rec loop i i' =
      if i >= n then s', i' - 2 else if s.[i] = ' ' then loop (i + 1) i' else
      let j = try String.index_from s (i + 1) ' ' with _ -> n in
      let m = j - i in
      if s.[i] = '\'' && i < j - 2 && s.[j - 1] = '\'' then
        (String.blit s (i + 1) s' i' (m - 2); loop (j + 1) (i' + m - 1))
      else if for_key && is_ident (String.sub s i m) then
         (s'.[i'] <- '_'; loop (j + 1) (i' + 2))
      else (String.blit s i s' i' m; loop (j + 1) (i' + m + 1)) in
    loop 0 1 in
  let trim_ntn (pntn, m) = String.sub pntn 1 (max 0 m) in
  let pr_ntn ntn = str "(" ++ str ntn ++ str ")" in
  let pr_and_list pr = function
    | [x] -> pr x
    | x :: lx -> pr_list pr_comma pr lx ++ pr_comma () ++ str "and " ++ pr x
    | [] -> mt () in
  let pr_sc sc = str (if sc = "" then "independently" else sc) in
  let pr_scs = function
    | [""] -> pr_sc ""
    | scs -> str "in " ++ pr_and_list pr_sc scs in
  let generator, pr_tag_sc =
    let ign _ = mt () in match okey with
  | Some key ->
    let sc = Notation.find_delimiters_scope loc key in
    let pr_sc s_in = str s_in ++ spc() ++ str sc ++ pr_comma() in
    Notation.pr_scope ign sc, pr_sc
  | None -> Notation.pr_scopes ign, ign in
  let qtag s_in = pr_tag_sc s_in ++ qstring tag ++ spc()in
  let ptag, ttag =
    let ptag, m = mk_pntn tag false in
    if m <= 0 then err (str "empty notation fragment");
    ptag, trim_ntn (ptag, m) in
  let last = ref "" and last_sc = ref "" in
  let scs = ref [] and ntns = ref [] in
  let push_sc sc = match !scs with
  | "" :: scs' ->  scs := "" :: sc :: scs'
  | scs' -> scs := sc :: scs' in
  let get s _ _ = match !last with
  | "Scope " -> last_sc := s; last := ""
  | "Lonely notation" -> last_sc := ""; last := ""
  | "\"" ->
      let pntn, m = mk_pntn s true in
      if string_string_contains pntn ptag then begin
        let ntn = trim_ntn (pntn, m) in
        match !ntns with
        | [] -> ntns := [ntn]; scs := [!last_sc]
        | ntn' :: _ when ntn' = ntn -> push_sc !last_sc
        | _ when ntn = ttag -> ntns := ntn :: !ntns; scs := [!last_sc]
        | _ :: ntns' when List.mem ntn ntns' -> ()
        | ntn' :: ntns' -> ntns := ntn' :: ntn :: ntns'
      end;
      last := ""
  | _ -> last := s in
  pp_with (Format.make_formatter get (fun _ -> ())) generator;
  let ntn = match !ntns with
  | [] ->
    err (hov 0 (qtag "in" ++ str "does not occur in any notation"))
  | ntn :: ntns' when ntn = ttag ->
    if ntns' <> [] then begin
      let pr_ntns' = pr_and_list pr_ntn ntns' in
      msg_warning (hov 4 (qtag "In" ++ str "also occurs in " ++ pr_ntns'))
    end; ntn
  | [ntn] ->
    msgnl (hov 4 (qtag "In" ++ str "is part of notation " ++ pr_ntn ntn)); ntn
  | ntns' ->
    let e = str "occurs in" ++ spc() ++ pr_and_list pr_ntn ntns' in
    err (hov 4 (str "ambiguous: " ++ qtag "in" ++ e)) in
  let (nvars, body), ((_, pat), osc) = match !scs with
  | [sc] -> Notation.interp_notation loc ntn (None, [sc])
  | scs' ->
    try Notation.interp_notation loc ntn (None, []) with _ ->
    let e = pr_ntn ntn ++ spc() ++ str "is defined " ++ pr_scs scs' in
    err (hov 4 (str "ambiguous: " ++ pr_tag_sc "in" ++ e)) in
  let sc = Option.default "" osc in
  let _ =
    let m_sc =
      if osc <> None then str "In " ++ str sc ++ pr_comma() else mt() in
    let ntn_pat = trim_ntn (mk_pntn pat false) in
    let rbody = rawconstr_of_aconstr loc body in
    let m_body = hov 0 (Constrextern.without_symbols prl_rawconstr rbody) in
    let m = m_sc ++ pr_ntn ntn_pat ++ spc () ++ str "denotes " ++ m_body in
    msgnl (hov 0 m) in
  if List.length !scs > 1 then
    let scs' = list_remove sc !scs in
    let w = pr_ntn ntn ++ str " is also defined " ++ pr_scs scs' in
    msg_warning (hov 4 w)
  else if string_string_contains ntn " .. " then
    err (pr_ntn ntn ++ str " is an n-ary notation");
  let nvars = List.filter (fun (_,(_,typ)) -> typ = NtnTypeConstr) nvars in
  let rec sub () = function
  | AVar x when List.mem_assoc x nvars -> RPatVar (loc, (false, x))
  | c ->
    rawconstr_of_aconstr_with_binders loc (fun _ x -> (), x) sub () c in
  let _, npat = Pattern.pattern_of_rawconstr (sub () body) in
  Search.GlobSearchSubPattern npat

ARGUMENT EXTEND ssr_search_item TYPED AS ssr_searchitem
  PRINTED BY pr_ssr_search_item
  | [ string(s) ] ->
    [ if is_ident_part s then Search.GlobSearchString s else
      interp_search_notation loc s None ]
  | [ string(s) "%" preident(key) ] ->
    [ interp_search_notation loc s (Some key) ]
  | [ constr_pattern(p) ] -> 
    [ try
        let intern = Constrintern.intern_constr_pattern Evd.empty in
        Search.GlobSearchSubPattern (snd (intern (Global.env()) p))
      with e -> raise (Cerrors.process_vernac_interp_error e)
  ]
END

let pr_ssr_search_arg _ _ _ =
  let pr_item (b, p) = str (if b then "-" else "") ++ pr_search_item p in
  pr_list spc pr_item

ARGUMENT EXTEND ssr_search_arg TYPED AS (bool * ssr_searchitem) list
  PRINTED BY pr_ssr_search_arg
  | [ "-" ssr_search_item(p) ssr_search_arg(a) ] -> [ (false, p) :: a ]
  | [ ssr_search_item(p) ssr_search_arg(a) ] -> [ (true, p) :: a ]
  | [ ] -> [ [] ]
END

(* Main type conclusion pattern filter *)

let rec splay_search_pattern na = function 
  | Pattern.PApp (fp, args) -> splay_search_pattern (na + Array.length args) fp
  | Pattern.PLetIn (_, _, bp) -> splay_search_pattern na bp
  | Pattern.PRef hr -> hr, na
  | _ -> error "no head constant in head search pattern"

let coerce_search_pattern_to_sort hpat =
  let env = Global.env () and sigma = Evd.empty in
  let mkPApp fp n_imps args =
    let args' = Array.append (Array.make n_imps (Pattern.PMeta None)) args in
    Pattern.PApp (fp, args') in
  let hr, na = splay_search_pattern 0 hpat in
  let dc, ht = Reductionops.splay_prod env sigma (Global.type_of_global hr) in
  let np = List.length dc in
  if np < na then error "too many arguments in head search pattern" else
  let hpat' = if np = na then hpat else mkPApp hpat (np - na) [||] in
  let warn () =
    msg_warning (str "Listing only lemmas with conclusion matching " ++ 
      pr_constr_pattern hpat') in
  if isSort ht then begin warn (); true, hpat' end else
  let filter_head, coe_path =
    try 
      let _, cp =
        Classops.lookup_path_to_sort_from (push_rels_assum dc env) sigma ht in
      warn ();
      true, cp
    with _ -> false, [] in
  let coerce hp coe_index =
    let coe = Classops.get_coercion_value coe_index in
    try
      let coe_ref = reference_of_constr coe in
      let n_imps = Option.get (Classops.hide_coercion coe_ref) in
      mkPApp (Pattern.PRef coe_ref) n_imps [|hp|]
    with _ ->
    errorstrm (str "need explicit coercion " ++ pr_constr coe ++ spc ()
            ++ str "to interpret head search pattern as type") in
  filter_head, List.fold_left coerce hpat' coe_path

let rec interp_head_pat hpat =
  let filter_head, p = coerce_search_pattern_to_sort hpat in
  let rec loop c = match kind_of_term c with
  | Cast (c', _, _) -> loop c'
  | Prod (_, _, c') -> loop c'
  | LetIn (_, _, _, c') -> loop c'
  | _ -> Matching.is_matching p c in
  filter_head, loop

let all_true _ = true

let interp_search_arg a =
  let hpat, a1 = match a with
  | (_, Search.GlobSearchSubPattern (Pattern.PMeta _)) :: a' -> all_true, a'
  | (true, Search.GlobSearchSubPattern p) :: a' ->
     let filter_head, p = interp_head_pat p in
     if filter_head then p, a' else all_true, a
  | _ -> all_true, a in
  let is_string =
    function (_, Search.GlobSearchString _) -> true | _ -> false in
  let a2, a3 = List.partition is_string a1 in
  hpat, a2 @ a3

(* Module path postfilter *)

let pr_modloc (b, m) = if b then str "-" ++ pr_reference m else pr_reference m

let wit_ssrmodloc, globwit_ssrmodloc, rawwit_ssrmodloc =
  add_genarg "ssrmodloc" pr_modloc

let pr_ssr_modlocs _ _ _ ml =
  if ml = [] then str "" else spc () ++ str "in " ++ pr_list spc pr_modloc ml

ARGUMENT EXTEND ssr_modlocs TYPED AS ssrmodloc list PRINTED BY pr_ssr_modlocs
  | [ ] -> [ [] ]
END

GEXTEND Gram
  GLOBAL: ssr_modlocs;
  modloc: [[ "-"; m = global -> true, m | m = global -> false, m]];
  ssr_modlocs: [[ "in"; ml = LIST1 modloc -> ml ]];
END

let interp_modloc mr =
  let interp_mod (_, mr) =
    let (loc, qid) = qualid_of_reference mr in
    try Nametab.full_name_module qid with Not_found ->
    user_err_loc (loc, "interp_modloc", str "No Module " ++ pr_qualid qid) in
  let mr_out, mr_in = List.partition fst mr in
  let interp_bmod b rmods =
    if rmods = [] then fun _ _ _ -> true else
    Search.filter_by_module_from_list (List.map interp_mod rmods, b) in
  let is_in = interp_bmod false mr_in and is_out = interp_bmod true mr_out in
  fun gr env -> is_in gr env () && is_out gr env ()

(* The unified, extended vernacular "Search" command *)

let ssrdisplaysearch gr env t =
  let pr_res = pr_global gr ++ spc () ++ str " " ++ pr_lconstr_env env t in
  msg (hov 2 pr_res ++ fnl ())

VERNAC COMMAND EXTEND SsrSearchPattern
| [ "Search" ssr_search_arg(a) ssr_modlocs(mr) ] ->
  [ let hpat, a' = interp_search_arg a in
    let in_mod = interp_modloc mr in
    let post_filter gr env typ = in_mod gr env && hpat typ in
    Search.raw_search_about post_filter ssrdisplaysearch a' ]
END

(** 3. Alternative notations for "match" (let or if with pattern). *)

(* Syntax:                                                        *)
(*  if <term> is <pattern> then ... else ...                      *)
(*  if <term> is <pattern> [in ..] return ... then ... else ...   *)
(*  let: <pattern> := <term> in ...                               *)
(*  let: <pattern> [in ...] := <term> return ... in ...           *)
(* The scope of a top-level 'as' in the pattern extends over the  *)
(* 'return' type (dependent if/let).                              *)
(* Note that the optional "in ..." appears next to the <pattern>  *)
(* rather than the <term> in then "let:" syntax. The alternative  *)
(* would lead to ambiguities in, e.g.,                            *)
(* let: p1 := (*v---INNER LET:---v *)                             *)
(*   let: p2 := let: p3 := e3 in k return t in k2 in k1 return t' *)
(* in b       (*^--ALTERNATIVE INNER LET--------^ *)              *)

(* Caveat : There is no pretty-printing support, since this would *)
(* require a modification to the Coq kernel (adding a new match   *)
(* display style -- why aren't these strings?); also, the v8.1    *)
(* pretty-printer only allows extension hooks for printing        *)
(* integer or string literals.                                    *)
(*   Also note that in the v8 grammar "is" needs to be a keyword; *)
(* as this can't be done from an ML extension file, the new       *)
(* syntax will only work when ssreflect.v is imported.            *)


let no_ct = None, None and no_rt = None in 
let aliasvar = function
  | [_, [CPatAlias (loc, _, id)]] -> Some (loc,Name id)
  | _ -> None in
let mk_cnotype mp = aliasvar mp, None in
let mk_ctype mp t = aliasvar mp, Some t in
let mk_rtype t = Some t in
let mk_dthen loc (mp, ct, rt) c = (loc, mp, c), ct, rt in
let mk_let loc rt ct mp c1 =
  CCases (loc, LetPatternStyle, rt, ct, [loc, mp, c1]) in
GEXTEND Gram
  GLOBAL: binder_constr;
  ssr_rtype: [[ "return"; t = operconstr LEVEL "100" -> mk_rtype t ]];
  ssr_mpat: [[ p = pattern -> [loc, [p]] ]];
  ssr_dpat: [
    [ mp = ssr_mpat; "in"; t = lconstr; rt = ssr_rtype -> mp, mk_ctype mp t, rt
    | mp = ssr_mpat; rt = ssr_rtype -> mp, mk_cnotype mp, rt
    | mp = ssr_mpat -> mp, no_ct, no_rt
  ] ];
  ssr_dthen: [[ dp = ssr_dpat; "then"; c = lconstr -> mk_dthen loc dp c ]];
  ssr_elsepat: [[ "else" -> [loc, [CPatAtom (loc, None)]] ]];
  ssr_else: [[ mp = ssr_elsepat; c = lconstr -> loc, mp, c ]];
  binder_constr: [
    [ "if"; c = operconstr LEVEL "200"; "is"; db1 = ssr_dthen; b2 = ssr_else ->
      let b1, ct, rt = db1 in CCases (loc, MatchStyle, rt, [c, ct], [b1; b2])
    | "if"; c = operconstr LEVEL "200";"isn't";db1 = ssr_dthen; b2 = ssr_else ->
      let b1, ct, rt = db1 in
      let b1, b2 = 
        let (l1, p1, r1), (l2, p2, r2) = b1, b2 in (l1, p1, r2), (l2, p2, r1) in
      CCases (loc, MatchStyle, rt, [c, ct], [b1; b2])
    | "let"; ":"; mp = ssr_mpat; ":="; c = lconstr; "in"; c1 = lconstr ->
      mk_let loc no_rt [c, no_ct] mp c1
    | "let"; ":"; mp = ssr_mpat; ":="; c = lconstr;
      rt = ssr_rtype; "in"; c1 = lconstr ->
      mk_let loc rt [c, mk_cnotype mp] mp c1
    | "let"; ":"; mp = ssr_mpat; "in"; t = lconstr; ":="; c = lconstr;
      rt = ssr_rtype; "in"; c1 = lconstr ->
      mk_let loc rt [c, mk_ctype mp t] mp c1
  ] ];
END


(** Alternative syntax for anonymous arguments (for ML-style constructors) *)

GEXTEND Gram
  GLOBAL: closed_binder;
  closed_binder: [
    [ ["of" | "&"]; c = operconstr LEVEL "99" ->
      [LocalRawAssum ([loc, Anonymous], Default Explicit, c)]
  ] ];
END

(** 4. Tacticals (+, -, *, done, by, do, =>, first, and last). *)

(** Bracketing tactical *)

(* The tactic pretty-printer doesn't know that some extended tactics *)
(* are actually tacticals. To prevent it from improperly removing    *)
(* parentheses we override the parsing rule for bracketed tactic     *)
(* expressions so that the pretty-print always reflects the input.   *)
(* (Removing user-specified parentheses is dubious anyway).          *)

GEXTEND Gram
  GLOBAL: tactic_expr;
  ssrparentacarg: [[ "("; tac = tactic_expr; ")" -> Tacexp tac ]];
  tactic_expr: LEVEL "0" [[ arg = ssrparentacarg -> TacArg arg ]];
END

(** The internal "done" and "ssrautoprop" tactics. *)

(* For additional flexibility, "done" and "ssrautoprop" are  *)
(* defined in Ltac.                                          *)
(* Although we provide a default definition in ssreflect,    *)
(* we look up the definition dynamically at each call point, *)
(* to allow for user extensions. "ssrautoprop" defaults to   *)
(* trivial.                                                  *)

let donetac gl =
  let tacname = 
    try Nametab.locate_tactic (qualid_of_ident (id_of_string "done"))
    with Not_found -> try Nametab.locate_tactic (ssrqid "done")
    with Not_found -> Util.error
      "The ssreflect library was not loaded (donetac)" in
  let tacexpr = Tacexpr.Reference (ArgArg (dummy_loc, tacname)) in
  eval_tactic (Tacexpr.TacArg tacexpr) gl

let ssrautoprop gl =
  try 
    let tacname = 
      try Nametab.locate_tactic (qualid_of_ident (id_of_string "ssrautoprop"))
      with Not_found -> Nametab.locate_tactic (ssrqid "ssrautoprop") in
    let tacexpr = Tacexpr.Reference (ArgArg (dummy_loc, tacname)) in
    eval_tactic (Tacexpr.TacArg tacexpr) gl
  with Not_found -> Auto.full_trivial [] gl

let () = ssrautoprop_tac := ssrautoprop

let tclBY tac = tclTHEN tac donetac

(** Tactical arguments. *)

(* We have four kinds: simple tactics, [|]-bracketed lists, hints, and swaps *)
(* The latter two are used in forward-chaining tactics (have, suffice, wlog) *)
(* and subgoal reordering tacticals (; first & ; last), respectively.        *)

(* Force use of the tactic_expr parsing entry, to rule out tick marks. *)
let pr_ssrtacarg _ _ prt = prt tacltop
ARGUMENT EXTEND ssrtacarg TYPED AS tactic PRINTED BY pr_ssrtacarg
| [ "(**)" ] -> [ Util.anomaly "Grammar placeholder match" ]
END
GEXTEND Gram
  GLOBAL: ssrtacarg;
  ssrtacarg: [[ tac = tactic_expr LEVEL "5" -> tac ]];
END

(* Lexically closed tactic for tacticals. *)
let pr_ssrtclarg _ _ prt (tac, _) = prt tacltop tac
ARGUMENT EXTEND ssrtclarg TYPED AS ssrtacarg * ssrltacctx
    PRINTED BY pr_ssrtclarg
| [ ssrtacarg(tac) ] -> [ tac, rawltacctx ]
END
let eval_tclarg (tac, ctx) = ssrevaltac (get_ltacctx ctx) tac

let pr_ortacs prt = 
  let rec pr_rec = function
  | [None]           -> spc() ++ str "|" ++ spc()
  | None :: tacs     -> spc() ++ str "|" ++ pr_rec tacs
  | Some tac :: tacs -> spc() ++ str "| " ++ prt tacltop tac ++  pr_rec tacs
  | []                -> mt() in
  function
  | [None]           -> spc()
  | None :: tacs     -> pr_rec tacs
  | Some tac :: tacs -> prt tacltop tac ++ pr_rec tacs
  | []                -> mt()
let pr_ssrortacs _ _ = pr_ortacs

ARGUMENT EXTEND ssrortacs TYPED AS tactic option list PRINTED BY pr_ssrortacs
| [ ssrtacarg(tac) "|" ssrortacs(tacs) ] -> [ Some tac :: tacs ]
| [ ssrtacarg(tac) "|" ] -> [ [Some tac; None] ]
| [ ssrtacarg(tac) ] -> [ [Some tac] ]
| [ "|" ssrortacs(tacs) ] -> [ None :: tacs ]
| [ "|" ] -> [ [None; None] ]
END

let pr_hintarg prt = function
  | true, tacs -> hv 0 (str "[ " ++ pr_ortacs prt tacs ++ str " ]")
  | false, [Some tac] -> prt tacltop tac
  | _, _ -> mt()

let pr_ssrhintarg _ _ = pr_hintarg

let mk_hint tac = false, [Some tac]
let mk_orhint tacs = true, tacs
let nullhint = true, []
let nohint = false, []

ARGUMENT EXTEND ssrhintarg TYPED AS bool * ssrortacs PRINTED BY pr_ssrhintarg
| [ "[" "]" ] -> [ nullhint ]
| [ "[" ssrortacs(tacs) "]" ] -> [ mk_orhint tacs ]
| [ ssrtacarg(arg) ] -> [ mk_hint arg ]
END

ARGUMENT EXTEND ssrortacarg TYPED AS ssrhintarg PRINTED BY pr_ssrhintarg
| [ "[" ssrortacs(tacs) "]" ] -> [ mk_orhint tacs ]
END

let hinttac ist is_by (is_or, atacs) =
  let dtac = if is_by then donetac else tclIDTAC in
  let mktac = function
  | Some atac -> tclTHEN (ssrevaltac ist atac) dtac
  | _ -> dtac in
  match List.map mktac atacs with
  | [] -> if is_or then dtac else tclIDTAC
  | [tac] -> tac
  | tacs -> tclFIRST tacs

(** The "-"/"+"/"*" tacticals. *)

(* These are just visual cues to flag the beginning of the script for *)
(* new subgoals, when indentation is not appropriate (typically after *)
(* tactics that generate more than two subgoals).                     *)

TACTIC EXTEND ssrtclplus
| [ "(**)" "+" ssrtclarg(arg) ] -> [ eval_tclarg arg ]
END
set_pr_ssrtac "tclplus" 5 [ArgSep "+ "; ArgSsr "tclarg"]

TACTIC EXTEND ssrtclminus
| [ "(**)" "-" ssrtclarg(arg) ] -> [ eval_tclarg arg ]
END
set_pr_ssrtac "tclminus" 5 [ArgSep "- "; ArgSsr "tclarg"]

TACTIC EXTEND ssrtclstar
| [ "(**)" "*" ssrtclarg(arg) ] -> [ eval_tclarg arg ]
END
set_pr_ssrtac "tclstar" 5 [ArgSep "- "; ArgSsr "tclarg"]

let gen_tclarg = in_gen rawwit_ssrtclarg

GEXTEND Gram
  GLOBAL: tactic;
  tactic: [
    [ "+"; tac = ssrtclarg -> ssrtac_expr loc "tclplus" [gen_tclarg tac]
    | "-"; tac = ssrtclarg -> ssrtac_expr loc "tclminus" [gen_tclarg tac]
    | "*"; tac = ssrtclarg -> ssrtac_expr loc "tclstar" [gen_tclarg tac]
    ] ];
END

(** The "by" tactical. *)

let pr_hint prt arg =
  if arg = nohint then mt() else str "by " ++ pr_hintarg prt arg
let pr_ssrhint _ _ = pr_hint

ARGUMENT EXTEND ssrhint TYPED AS ssrhintarg PRINTED BY pr_ssrhint
| [ ]                       -> [ nohint ]
END

TACTIC EXTEND ssrtclby
| [ "(**)" ssrhint(tac) ssrltacctx(ctx)] ->
  [ hinttac (get_ltacctx ctx) true tac ]
END
set_pr_ssrtac "tclby" 0 [ArgSsr "hint"; ArgSsr "ltacctx"]

(* We can't parse "by" in ARGUMENT EXTEND because it will only be made *)
(* into a keyword in ssreflect.v; so we anticipate this in GEXTEND.    *)

GEXTEND Gram
  GLOBAL: ssrhint simple_tactic;
  ssrhint: [[ "by"; arg = ssrhintarg -> arg ]];
  simple_tactic: [
  [ "by"; arg = ssrhintarg ->
    let garg = in_gen rawwit_ssrhint arg in
    let gctx = in_gen rawwit_ssrltacctx rawltacctx in
    ssrtac_atom loc "tclby" [garg; gctx]
  ] ];
END

(** Bound assumption argument *)

(* The Ltac API does have a type for assumptions but it is level-dependent *)
(* and therefore impratical to use for complex arguments, so we substitute *)
(* our own to have a uniform representation. Also, we refuse to intern     *)
(* idents that match global/section constants, since this would lead to    *)
(* fragile Ltac scripts.                                                   *)

type ssrhyp = SsrHyp of loc * identifier

let hyp_id (SsrHyp (_, id)) = id
let pr_hyp (SsrHyp (_, id)) = pr_id id
let pr_ssrhyp _ _ _ = pr_hyp

let wit_ssrhyprep, globwit_ssrhyprep, rawwit_ssrhyprep =
  add_genarg "ssrhyprep" pr_hyp

let hyp_err loc msg id =
  user_err_loc (loc, "ssrhyp", str msg ++ pr_id id)

let intern_hyp ist (SsrHyp (loc, id) as hyp) =
  let _ = intern_genarg ist (in_gen rawwit_var (loc, id)) in
  if not_section_id id then hyp else
  hyp_err loc "Can't clear section hypothesis " id

let interp_hyp ist gl (SsrHyp (loc, id)) =
  let id' = interp_wit globwit_var wit_var ist gl (loc, id) in
  if not_section_id id' then SsrHyp (loc, id') else
  hyp_err loc "Can't clear section hypothesis " id'

ARGUMENT EXTEND ssrhyp TYPED AS ssrhyprep PRINTED BY pr_ssrhyp
                       INTERPRETED BY interp_hyp
                       GLOBALIZED BY intern_hyp
  | [ ident(id) ] -> [ SsrHyp (loc, id) ]
END

type ssrhyps = ssrhyp list

let pr_hyps = pr_list pr_spc pr_hyp
let pr_ssrhyps _ _ _ = pr_hyps
let hyps_ids = List.map hyp_id

let rec check_hyps_uniq ids = function
  | SsrHyp (loc, id) :: _ when List.mem id ids ->
    hyp_err loc "Duplicate assumption " id
  | SsrHyp (_, id) :: hyps -> check_hyps_uniq (id :: ids) hyps
  | [] -> ()

let check_hyp_exists hyps (SsrHyp(_, id)) =
  try ignore(Sign.lookup_named id hyps)
  with Not_found -> errorstrm (str"No assumption is named " ++ pr_id id)

let interp_hyps ist gl ghyps =
  let hyps = List.map (interp_hyp ist gl) ghyps in
  check_hyps_uniq [] hyps; hyps

ARGUMENT EXTEND ssrhyps TYPED AS ssrhyp list PRINTED BY pr_ssrhyps
                        INTERPRETED BY interp_hyps
  | [ ssrhyp_list(hyps) ] -> [ check_hyps_uniq [] hyps; hyps ]
END

(** Term references *)

(* Because we allow wildcards in term references, we need to stage the *)
(* interpretation of terms so that it occurs at the right time during  *)
(* the execution of the tactic (e.g., so that we don't report an error *)
(* for a term that isn't actually used in the execution).              *)
(*   The term representation tracks whether the concrete initial term  *)
(* started with an opening paren, which might avoid a conflict between *)
(* the ssrreflect term syntax and Gallina notation.                    *)

(* kinds of terms *)

type ssrtermkind = char (* print flag *)

let input_ssrtermkind strm = match Stream.npeek 1 strm with
  | ["", "("] -> '('
  | ["", "@"] -> '@'
  | _ -> ' '

let ssrtermkind = Gram.Entry.of_parser "ssrtermkind" input_ssrtermkind

let id_of_Cterm = function
  | _,(_,Some (CRef (Ident (_, x)))) -> x
  | _,(_,Some (CAppExpl (_, (_, Ident (_, x)), []))) -> x
  | _,(_,Some x) -> loc_error (constr_loc x) "Only identifiers are allowed here"
  | _,(RRef (_, VarRef x) ,None) -> x
  | _ -> anomaly "not a cterm nor a GRef(VarRef _)"

let ssrhyp_of_ssrterm = function
  | k, (_, Some c) as o -> SsrHyp (constr_loc c, id_of_Cterm o), String.make 1 k
  | _, (_, None) -> assert false

(* terms *)

type ssrtermrep = char * rawconstr_and_expr

(* We also guard characters that might interfere with the ssreflect   *)
(* tactic syntax.                                                     *)
let guard_term ch1 s i = match s.[i] with
  | '(' -> false
  | '{' | '/' | '=' -> true
  | _ -> ch1 = '('

let mk_term k c = k, (mkRHole, Some c)
let mk_lterm = mk_term ' '

let hole_var = mkVar (id_of_string "_")
let pr_constr_pat c0 =
  let rec wipe_evar c =
    if isEvar c then hole_var else map_constr wipe_evar c in
  pr_constr (wipe_evar c0)

let pat_of_ssrterm n c =
  let rec mkvars i =
    let v = mkVar (id_of_string (sprintf "_pattern_var_%d_" i)) in
    if i = 0 then [v] else v :: mkvars (i - 1) in
  if n <= 0 then c else substl (mkvars n) (snd (decompose_lam_n n c))
let pr_pattern n c = pr_constr (pat_of_ssrterm n c)

let pr_term (k, c) = pr_guarded (guard_term k) pr_rawconstr_and_expr c
let prl_term (k, c) = pr_guarded (guard_term k) prl_rawconstr_and_expr c

let pr_ssrterm _ _ _ = pr_term

let pf_intern_term ist gl (_, c) = glob_constr ist (project gl) (pf_env gl) c
let intern_term ist sigma env (_, c) = glob_constr ist sigma env c

let interp_term ist gl (_, c) = interp_open_constr ist gl c

let force_term ist gl (_, c) = interp_constr ist gl c

let glob_ssrterm gs = function
  | k, (_, Some c) -> k, Tacinterp.intern_constr gs c
  | ct -> ct

let subst_ssrterm s (k, c) = k, Tacinterp.subst_rawconstr_and_expr s c

let interp_ssrterm _ _ t = t

ARGUMENT EXTEND ssrterm
     TYPED AS ssrtermrep PRINTED BY pr_ssrterm
     INTERPRETED BY interp_ssrterm
     GLOBALIZED BY glob_ssrterm SUBSTITUTED BY subst_ssrterm
     RAW_TYPED AS ssrtermrep RAW_PRINTED BY pr_ssrterm
     GLOB_TYPED AS ssrtermrep GLOB_PRINTED BY pr_ssrterm
| [ "(**)" constr(c) ] -> [ mk_lterm c ]
END

GEXTEND Gram
  GLOBAL: ssrterm;
  ssrterm: [[ k = ssrtermkind; c = constr -> mk_term k c ]];
END

(* This piece of code asserts the following notations are reserved *)
(* Reserved Notation "( a 'in' b )"        (at level 0).           *)
(* Reserved Notation "( a 'as' b )"        (at level 0).           *)
(* Reserved Notation "( a 'in' b 'in' c )" (at level 0).           *)
(* Reserved Notation "( a 'as' b 'in' c )" (at level 0).           *)
let glob_ssrpattern gs p =
  pp(lazy(str"globbing pattern: " ++ pr_term p));
  let glob x = snd (glob_ssrterm gs (mk_lterm x)) in
  let encode k s l =
    let name = Name (id_of_string ("_ssrpat_" ^ s)) in
    k, (mkRCast mkRHole (mkRLambda name mkRHole (mkRApp mkRHole l)), None) in
  let bind_in t1 t2 =
    let d = dummy_loc in let n = Name (destCVar t1) in
    fst (glob (mkCCast d (mkCHole d) (mkCLambda d n (mkCHole d) t2))) in
  let check_var t2 = if not (isCVar t2) then
    loc_error (constr_loc t2) "Only identifiers are allowed here" in
  match p with
  | _, (_, None) as x -> x
  | k, (v, Some t) as orig ->
     if k = 'x' then glob_ssrterm gs ('(', (v, Some t)) else
     match t with
     | CNotation(_, "( _ in _ )", ([t1; t2], [], [])) ->
         (try match glob t1, glob t2 with
         | (r1, None), (r2, None) -> encode k "In" [r1;r2]
         | (r1, Some _), (r2, Some _) when isCVar t1 ->
             encode k "In" [r1; r2; bind_in t1 t2]
         | (r1, Some _), (r2, Some _) -> encode k "In" [r1; r2]
         | _ -> anomaly "where are we?"
         with _ when isCVar t1 -> encode k "In" [bind_in t1 t2])
     | CNotation(_, "( _ in _ in _ )", ([t1; t2; t3], [], [])) ->
         check_var t2; encode k "In" [fst (glob t1); bind_in t2 t3]
     | CNotation(_, "( _ as _ )", ([t1; t2], [], [])) ->
         encode k "As" [fst (glob t1); fst (glob t2)]
     | CNotation(_, "( _ as _ in _ )", ([t1; t2; t3], [], [])) ->
         check_var t2; encode k "As" [fst (glob t1); bind_in t2 t3]
     | _ -> glob_ssrterm gs orig
;;

ARGUMENT EXTEND ssrpattern
     TYPED AS ssrtermrep PRINTED BY pr_ssrterm
     INTERPRETED BY interp_ssrterm
     GLOBALIZED BY glob_ssrpattern SUBSTITUTED BY subst_ssrterm
     RAW_TYPED AS ssrtermrep RAW_PRINTED BY pr_ssrterm
     GLOB_TYPED AS ssrtermrep GLOB_PRINTED BY pr_ssrterm
| [ "(**)" constr(c) ] -> [ mk_lterm c ]
END

GEXTEND Gram
  GLOBAL: ssrpattern;
  ssrpattern: [[ k = ssrtermkind; c = constr ->
    let pattern = mk_term k c in
    if loc_ofCG pattern <> loc && k = '(' then mk_term 'x' c else pattern ]];
END

ARGUMENT EXTEND ssrlpattern
     TYPED AS ssrtermrep PRINTED BY pr_ssrterm
     INTERPRETED BY interp_ssrterm
     GLOBALIZED BY glob_ssrpattern SUBSTITUTED BY subst_ssrterm
     RAW_TYPED AS ssrtermrep RAW_PRINTED BY pr_ssrterm
     GLOB_TYPED AS ssrtermrep GLOB_PRINTED BY pr_ssrterm
| [ "(**)" lconstr(c) ] -> [ mk_lterm c ]
END

GEXTEND Gram
  GLOBAL: ssrlpattern;
  ssrlpattern: [[ k = ssrtermkind; c = lconstr ->
    let pattern = mk_term k c in
    if loc_ofCG pattern <> loc && k = '(' then mk_term 'x' c else pattern ]];
END

(** The "in" pseudo-tactical *)

(* We can't make "in" into a general tactical because this would create a  *)
(* crippling conflict with the ltac let .. in construct. Hence, we add     *)
(* explicitly an "in" suffix to all the extended tactics for which it is   *)
(* relevant (including move, case, elim) and to the extended do tactical   *)
(* below, which yields a general-purpose "in" of the form do [...] in ...  *)

(* This tactical needs to come before the intro tactics because the latter *)
(* must take precautions in order not to interfere with the discharged     *)
(* assumptions. This is especially difficult for discharged "let"s, which  *)
(* the default simpl and unfold tactics would erase blindly.               *)

type ssrclseq = InGoal | InHyps
 | InHypsGoal | InHypsSeqGoal | InSeqGoal | InHypsSeq | InAll | InAllHyps

let pr_clseq = function
  | InGoal | InHyps -> mt ()
  | InSeqGoal       -> str "|- *"
  | InHypsSeqGoal   -> str " |- *"
  | InHypsGoal      -> str " *"
  | InAll           -> str "*"
  | InHypsSeq       -> str " |-"
  | InAllHyps       -> str "* |-"

let wit_ssrclseq, globwit_ssrclseq, rawwit_ssrclseq =
  add_genarg "ssrclseq" pr_clseq

(* type ssrahyps = ssrhyp list * string list *)

let ahyps_ids (ids, flags) = List.map hyp_id ids, flags
let check_ahyps_uniq a (b,_) = check_hyps_uniq a b

let pr_ahyp (SsrHyp (_, id), mode) = match mode with 
  | "(" -> str "(" ++ pr_id id ++ str ")"
  | "@" -> str "@" ++ pr_id id
  | " " -> pr_id id
  | _ -> anomaly "pr_ahyp: wrong annotation for ssrhyp"
let pr_ahyps (a,b) = pr_list pr_spc pr_ahyp (List.combine a b)
let pr_ssrahyps _ _ _ = pr_ahyps

let wit_ssrahyps, globwit_ssrahyps, rawwit_ssrahyps =
  add_genarg "ssrahyps" pr_ahyps

ARGUMENT EXTEND ssrclausehyps 
TYPED AS ssrhyps * string list PRINTED BY pr_ssrahyps
| [ ssrterm(hyp) "," ssrclausehyps(hyps) ] ->
  [ let hyp, flag = ssrhyp_of_ssrterm hyp in hyp :: fst hyps, flag :: snd hyps ]
| [ ssrterm(hyp) ssrclausehyps(hyps) ] ->
  [ let hyp, flag = ssrhyp_of_ssrterm hyp in hyp :: fst hyps, flag :: snd hyps ]
| [ ssrterm(hyp) ] -> [ let hyp, flag = ssrhyp_of_ssrterm hyp in [hyp],[flag] ]
END

(* type ssrclauses = ssrahyps * ssrclseq *)

let pr_clauses (hyps, clseq) = 
  if clseq = InGoal then mt () else str "in " ++ pr_ahyps hyps ++ pr_clseq clseq
let pr_ssrclauses _ _ _ = pr_clauses

let mkclause hyps clseq = 
  check_hyps_uniq [] (fst hyps); (hyps, clseq)

ARGUMENT EXTEND ssrclauses TYPED AS (ssrhyps * string list) * ssrclseq
    PRINTED BY pr_ssrclauses
  | [ "in" ssrclausehyps(hyps) "|-" "*" ] -> [ mkclause hyps InHypsSeqGoal ]
  | [ "in" ssrclausehyps(hyps) "|-" ]     -> [ mkclause hyps InHypsSeq ]
  | [ "in" ssrclausehyps(hyps) "*" ]      -> [ mkclause hyps InHypsGoal ]
  | [ "in" ssrclausehyps(hyps) ]          -> [ mkclause hyps InHyps ]
  | [ "in" "|-" "*" ]                     -> [ mkclause ([],[]) InSeqGoal ]
  | [ "in" "*" ]                          -> [ mkclause ([],[]) InAll ]
  | [ "in" "*" "|-" ]                     -> [ mkclause ([],[]) InAllHyps ]
  | [ ]                                   -> [ mkclause ([],[]) InGoal ]
END

let nohide = mkRel 0
let hidden_goal_tag = "the_hidden_goal"

(* Reduction that preserves the Prod/Let spine of the "in" tactical. *)

let inc_safe n = if n = 0 then n else n + 1
let rec safe_depth c = match kind_of_term c with
| LetIn (Name x, _, _, c') when is_discharged_id x -> safe_depth c' + 1
| LetIn (_, _, _, c') | Prod (_, _, c') -> inc_safe (safe_depth c')
| _ -> 0 

let red_safe r e s c0 =
  let rec red_to e c n = match kind_of_term c with
  | Prod (x, t, c') when n > 0 ->
    let t' = r e s t in let e' = Environ.push_rel (x, None, t') e in
    mkProd (x, t', red_to e' c' (n - 1))
  | LetIn (x, b, t, c') when n > 0 ->
    let t' = r e s t in let e' = Environ.push_rel (x, None, t') e in
    mkLetIn (x, r e s b, t', red_to e' c' (n - 1))
  | _ -> r e s c in
  red_to e c0 (safe_depth c0)

let pf_clauseids gl (claids,_ as clahyps) clseq =
  if claids <> [] then (check_ahyps_uniq [] clahyps; ahyps_ids clahyps) else
  if clseq <> InAll && clseq <> InAllHyps then [],[] else
  (*let _ =*) error "assumptions should be named explicitly" (*in*)
(*
  let dep_term var = mkNamedProd_or_LetIn (pf_get_hyp gl var) mkImplicit in
  let rec rem_var var =  function
  | [] -> raise Not_found
  | id :: ids when id <> var -> id :: rem_var var ids
  | _ :: ids -> rem_deps ids (dep_term var)
  and rem_deps ids c =
    try match kind_of_term c with
    | Var id -> rem_var id ids
    | _ -> fold_constr rem_deps ids c
    with Not_found -> ids in
  let ids = pf_ids_of_proof_hyps gl in
  List.rev (if clseq = InAll then ids else rem_deps ids (pf_concl gl))
*)

let hidden_clseq = function InHyps | InHypsSeq | InAllHyps -> true | _ -> false

let hidetacs clseq idhide cl0 =
  if not (hidden_clseq clseq) then  [] else
  [posetac idhide cl0; convert_concl_no_check (mkVar idhide)]

let discharge_hyp (id', (id, mode)) gl =
  let cl' = subst_var id (pf_concl gl) in
  match pf_get_hyp gl id, mode with
  | (_, None, t), _ | (_, Some _, t), "(" -> 
     apply_type (mkProd (Name id', t, cl')) [mkVar id] gl
  | (_, Some v, t), _ -> convert_concl (mkLetIn (Name id', v, t, cl')) gl

let endclausestac id_map clseq gl_id cl0 gl =
  let not_hyp' id = not (List.mem_assoc id id_map) in
  let orig_id id = try fst (List.assoc id id_map) with _ -> id in
  let dc, c = Term.decompose_prod_assum (pf_concl gl) in
  let hide_goal = hidden_clseq clseq in
  let c_hidden = hide_goal && c = mkVar gl_id in
  let rec fits forced = function
  | (id, _) :: ids, (Name id', _, _) :: dc' when id' = id ->
    fits true (ids, dc')
  | ids, dc' ->
    forced && ids = [] && (not hide_goal || dc' = [] && c_hidden) in
  let rec unmark c = match kind_of_term c with
  | Var id when hidden_clseq clseq && id = gl_id -> cl0
  | Prod (Name id, t, c') when List.mem_assoc id id_map ->
    mkProd (Name (orig_id id), unmark t, unmark c')
  | LetIn (Name id, v, t, c') when List.mem_assoc id id_map ->
    mkLetIn (Name (orig_id id), unmark v, unmark t, unmark c')
  | _ -> map_constr unmark c in
  let utac hyp = convert_hyp_no_check (map_named_declaration unmark hyp) in
  let utacs = List.map utac (pf_hyps gl) in
  let ugtac gl' = convert_concl_no_check (unmark (pf_concl gl')) gl' in
  let ctacs = if hide_goal then [clear [gl_id]] else [] in
  let mktac itacs = tclTHENLIST (itacs @ utacs @ ugtac :: ctacs) in
  let itac (_, (id, _)) = introduction id in
  if fits false (id_map, List.rev dc) then mktac (List.map itac id_map) gl else
  let all_ids = ids_of_rel_context dc @ pf_ids_of_hyps gl in
  if List.for_all not_hyp' all_ids && not c_hidden then mktac [] gl else
  Util.error "tampering with discharged assumptions of \"in\" tactical"
    
let tclCLAUSES tac (clahyps, clseq) gl =
  if clseq = InGoal || clseq = InSeqGoal then tac gl else
  let cl_ids = pf_clauseids gl clahyps clseq in
  let id_map = 
    List.map (fun id, mode -> mk_discharged_id id, (id, mode))
      (List.combine (fst cl_ids) (snd cl_ids)) in
  let gl_id = mk_anon_id hidden_goal_tag gl in
  let cl0 = pf_concl gl in
  let dtacs = 
    List.map discharge_hyp (List.rev id_map) @ [clear (fst cl_ids)] in
  let endtac = endclausestac id_map clseq gl_id cl0 in
  tclTHENLIST (hidetacs clseq gl_id cl0 @ dtacs @ [tac; endtac]) gl

(** Clear switch *)

(* This code isn't actually used by the intro patterns below, because the *)
(* Ltac interpretation of the clear switch in an intro pattern is         *)
(* different than in terms: the hyps aren't necessarily in the context at *)
(* the time the argument is interpreted, i.e., they could be introduced   *)
(* earlier in the pattern.                                                *)

type ssrclear = ssrhyps

let pr_clear_ne clr = str "{" ++ pr_hyps clr ++ str "}"
let pr_clear sep clr = if clr = [] then mt () else sep () ++ pr_clear_ne clr

let pr_ssrclear _ _ _ = pr_clear mt

ARGUMENT EXTEND ssrclear_ne TYPED AS ssrhyps PRINTED BY pr_ssrclear
| [ "{" ne_ssrhyp_list(clr) "}" ] -> [ check_hyps_uniq [] clr; clr ]
END

ARGUMENT EXTEND ssrclear TYPED AS ssrclear_ne PRINTED BY pr_ssrclear
| [ ssrclear_ne(clr) ] -> [ clr ]
| [ ] -> [ [] ]
END

let cleartac clr = check_hyps_uniq [] clr; clear (hyps_ids clr)

(** Simpl switch *)

type ssrsimpl = Simpl | Cut | SimplCut | Nop

let pr_simpl = function
  | Simpl -> str "/="
  | Cut -> str "//"
  | SimplCut -> str "//="
  | Nop -> mt ()

let pr_ssrsimpl _ _ _ = pr_simpl

let wit_ssrsimplrep, globwit_ssrsimplrep, rawwit_ssrsimplrep =
  add_genarg "ssrsimplrep" pr_simpl

ARGUMENT EXTEND ssrsimpl_ne TYPED AS ssrsimplrep PRINTED BY pr_ssrsimpl
| [ "/=" ] -> [ Simpl ]
| [ "//" ] -> [ Cut ]
| [ "//=" ] -> [ SimplCut ]
END

ARGUMENT EXTEND ssrsimpl TYPED AS ssrsimplrep PRINTED BY pr_ssrsimpl
| [ ssrsimpl_ne(sim) ] -> [ sim ]
| [ ] -> [ Nop ]
END

(* We must avoid zeta-converting any "let"s created by the "in" tactical. *)

let safe_simpltac gl =
  let cl' = red_safe Tacred.simpl (pf_env gl) (project gl) (pf_concl gl) in
  convert_concl_no_check cl' gl

let simpltac = function
  | Simpl -> safe_simpltac
  | Cut -> tclTRY donetac
  | SimplCut -> tclTHEN safe_simpltac (tclTRY donetac)
  | Nop -> tclIDTAC

(** Rewriting direction *)

type ssrdir = L2R | R2L

let pr_dir = function L2R -> str "->" | R2L -> str "<-"

let pr_rwdir = function L2R -> mt() | R2L -> str "-"

let pr_dir_side = function L2R -> str "LHS" | R2L -> str "RHS"

let inv_dir = function L2R -> R2L | R2L -> L2R

let rewritetac dir c =
  (* Due to the new optional arg ?tac, application shouldn't be too partial *)
  Equality.general_rewrite (dir = L2R) all_occurrences false c

let wit_ssrdir, globwit_ssrdir, rawwit_ssrdir =
  add_genarg "ssrdir" pr_dir

let dir_org = function L2R -> 1 | R2L -> 2

(** Indexes *)

(* Since SSR indexes are always positive numbers, we use the 0 value *)
(* to encode an omitted index. We reuse the in or_var type, but we   *)
(* supply our own interpretation function, which checks for non      *)
(* positive values, and allows the use of constr numerals, so that   *)
(* e.g., "let n := eval compute in (1 + 3) in (do n!clear)" works.   *)

type ssrindex = int or_var

let pr_index = function
  | ArgVar (_, id) -> pr_id id
  | ArgArg n when n > 0 -> pr_int n
  | _ -> mt ()
let pr_ssrindex _ _ _ = pr_index

let noindex = ArgArg 0
let check_index loc i =
  if i > 0 then i else loc_error loc "Index not positive"
let mk_index loc = function ArgArg i -> ArgArg (check_index loc i) | iv -> iv
let get_index = function ArgArg i -> i | _ -> anomaly "Uninterpreted index"

let interp_index ist gl idx =
  match idx with
  | ArgArg _ -> idx
  | ArgVar (loc, id) ->
    let i = try match List.assoc id ist.lfun with
    | VInteger i -> i
    | VConstr ([],c) ->
      let rc = Detyping.detype false [] [] c in
      begin match Notation.uninterp_prim_token rc with
      | _, Numeral bigi -> int_of_string (Bigint.to_string bigi)
      | _ -> raise Not_found
      end
    | _ -> raise Not_found
    with _ -> loc_error loc "Index not a number" in
    ArgArg (check_index loc i)

ARGUMENT EXTEND ssrindex TYPED AS int_or_var PRINTED BY pr_ssrindex
  INTERPRETED BY interp_index
| [ int_or_var(i) ] -> [ mk_index loc i ]
END

(** Occurrence switch *)

(* The standard syntax of complemented occurrence lists involves a single *)
(* initial "-", e.g., {-1 3 5} (the get_occ_indices function handles the  *)
(* conversion to the bool + list form used by the Coq API). An initial    *)
(* "+" may be used to indicate positive occurrences (the default). The    *)
(* "+" is optional, except if the list of occurrences starts with a       *)
(* variable or is empty (to avoid confusion with a clear switch). The     *)
(* empty positive switch "{+}" selects no occurrences, while the empty    *)
(* negative switch "{-}" selects all occurrences explicitly; this is the  *)
(* default, but "{-}" prevents the implicit clear, and can be used to     *)
(* force dependent elimination -- see ndefectelimtac below.               *)

type ssrocc = ssrindex list

let pr_occ = function
  | ArgArg -1 :: occ -> str "{-" ++ pr_list pr_spc pr_index occ ++ str "}"
  | ArgArg 0 :: occ -> str "{+" ++ pr_list pr_spc pr_index occ ++ str "}"
  | occ -> str "{" ++ pr_list pr_spc pr_index occ ++ str "}"

let pr_ssrocc _ _ _ = pr_occ

ARGUMENT EXTEND ssrocc TYPED AS ssrindex list PRINTED BY pr_ssrocc
| [ natural(n) ssrindex_list(occ) ] -> [ ArgArg (check_index loc n) :: occ  ]
| [ "-" ssrindex_list(occ) ]     -> [ ArgArg (-1) :: occ ]
| [ "+" ssrindex_list(occ) ]     -> [ ArgArg 0 :: occ ]
END

let get_occ_indices = function
  | ArgArg -1 :: occ -> occ = [], List.map get_index occ
  | ArgArg 0 :: occ  -> occ != [], List.map get_index occ
  | occ              -> occ != [], List.map get_index occ

let pf_mkprod gl c ?(name=constr_name c) cl =
  let t = pf_type_of gl c in
  if name <> Anonymous || noccurn 1 cl then mkProd (name, t, cl) else
  mkProd (Name (pf_type_id gl t), t, cl)

let pf_abs_prod name gl c cl = pf_mkprod gl c ~name (subst_term c cl)

(** Discharge occ switch (combined occurrence / clear switch *)

type ssrdocc = ssrclear option * ssrocc

let mkocc occ = None, occ
let noclr = mkocc []
let mkclr clr  = Some clr, []
let nodocc = mkclr []

let pr_docc = function
  | None, occ -> pr_occ occ
  | Some clr, _ -> pr_clear mt clr

let pr_ssrdocc _ _ _ = pr_docc

ARGUMENT EXTEND ssrdocc TYPED AS ssrclear option * ssrocc PRINTED BY pr_ssrdocc
| [ "{" ne_ssrhyp_list(clr) "}" ] -> [ mkclr clr ]
| [ "{" ssrocc(occ) "}" ] -> [ mkocc occ ]
END

(** View hint database. *)

(* There are three databases of lemmas used to mediate the application  *)
(* of reflection lemmas: one for forward chaining, one for backward     *)
(* chaining, and one for secondary backward chaining.                   *)

(* View hints *)

let rec isCxHoles = function (CHole _, None) :: ch -> isCxHoles ch | _ -> false

let pr_raw_ssrhintref prc _ _ = function
  | CAppExpl (_, (None, r), args) when isCHoles args ->
    prc (CRef r) ++ str "|" ++ int (List.length args)
  | CApp (_, (_, CRef _), _) as c -> prc c
  | CApp (_, (_, c), args) when isCxHoles args ->
    prc c ++ str "|" ++ int (List.length args)
  | c -> prc c

let pr_rawhintref = function
  | RApp (_, f, args) when isRHoles args ->
    pr_rawconstr f ++ str "|" ++ int (List.length args)
  | c -> pr_rawconstr c

let pr_glob_ssrhintref _ _ _ (c, _) = pr_rawhintref c

let pr_ssrhintref prc _ _ = prc

let mkhintref loc c n = match c with
  | CRef r -> CAppExpl (loc, (None, r), mkCHoles loc n)
  | _ -> mkAppC (c, mkCHoles loc n)

ARGUMENT EXTEND ssrhintref
        TYPED AS constr      PRINTED BY pr_ssrhintref
    RAW_TYPED AS constr  RAW_PRINTED BY pr_raw_ssrhintref
   GLOB_TYPED AS constr GLOB_PRINTED BY pr_glob_ssrhintref
  | [ constr(c) ] -> [ c ]
  | [ constr(c) "|" natural(n) ] -> [ mkhintref loc c n ]
END

(* View purpose *)

let pr_viewpos = function
  | 0 -> str " for move/"
  | 1 -> str " for apply/"
  | 2 -> str " for apply//"
  | _ -> mt ()

let pr_ssrviewpos _ _ _ = pr_viewpos

ARGUMENT EXTEND ssrviewpos TYPED AS int PRINTED BY pr_ssrviewpos
  | [ "for" "move" "/" ] -> [ 0 ]
  | [ "for" "apply" "/" ] -> [ 1 ]
  | [ "for" "apply" "/" "/" ] -> [ 2 ]
  | [ "for" "apply" "//" ] -> [ 2 ]
  | [ ] -> [ 3 ]
END

let pr_ssrviewposspc _ _ _ i = pr_viewpos i ++ spc ()

ARGUMENT EXTEND ssrviewposspc TYPED AS ssrviewpos PRINTED BY pr_ssrviewposspc
  | [ ssrviewpos(i) ] -> [ i ]
END

(* The table and its display command *)

let viewtab : rawconstr list array = Array.make 3 []

let _ =
  let init () = Array.fill viewtab 0 3 [] in
  let freeze () = Array.copy viewtab in
  let unfreeze vt = Array.blit vt 0 viewtab 0 3 in
  Summary.declare_summary "ssrview"
    { Summary.freeze_function   = freeze;
      Summary.unfreeze_function = unfreeze;
      Summary.init_function     = init }

let mapviewpos f n k = if n < 3 then f n else for i = 0 to k - 1 do f i done

let print_view_hints i =
  let pp_viewname = str "Hint View" ++ pr_viewpos i ++ str " " in
  let pp_hints = pr_list spc pr_rawhintref viewtab.(i) in
  ppnl (pp_viewname ++ hov 0 pp_hints ++ Pp.cut ())

VERNAC COMMAND EXTEND PrintView
| [ "Print" "Hint" "View" ssrviewpos(i) ] -> [ mapviewpos print_view_hints i 3 ]
END

(* Populating the table *)

let cache_viewhint (_, (i, lvh)) =
  let mem_raw h = List.exists (Topconstr.eq_rawconstr h) in
  let add_hint h hdb = if mem_raw h hdb then hdb else h :: hdb in
  viewtab.(i) <- List.fold_right add_hint lvh viewtab.(i)

let subst_viewhint ( subst, (i, lvh as ilvh)) =
  let lvh' = list_smartmap (Detyping.subst_rawconstr subst) lvh in
  if lvh' == lvh then ilvh else i, lvh'

let classify_viewhint x = Libobject.Substitute x

let (in_viewhint, out_viewhint)=
  Libobject.declare_object {(Libobject.default_object "VIEW_HINTS") with
       Libobject.open_function = (fun i o -> if i = 1 then cache_viewhint o);
       Libobject.cache_function = cache_viewhint;
       Libobject.subst_function = subst_viewhint;
       Libobject.classify_function = classify_viewhint }

let glob_view_hints lvh =
  List.map (Constrintern.intern_constr Evd.empty (Global.env ())) lvh

let add_view_hints lvh i = Lib.add_anonymous_leaf (in_viewhint (i, lvh))

VERNAC COMMAND EXTEND HintView
  |  [ "Hint" "View" ssrviewposspc(n) ne_ssrhintref_list(lvh) ] ->
     [ mapviewpos (add_view_hints (glob_view_hints lvh)) n 2 ]
END

(** Views *)

(* Views for the "move" and "case" commands are actually open *)
(* terms, but this is handled by interp_view, which is called *)
(* by interp_casearg. We use lists, to support the            *)
(* "double-view" feature of the apply command.                *)

(* type ssrview = ssrterm list *)

let pr_view = pr_list mt (fun c -> str "/" ++ pr_term c)

let pr_ssrview _ _ _ = pr_view

ARGUMENT EXTEND ssrview TYPED AS ssrterm list
   PRINTED BY pr_ssrview
| [ "/" constr(c) ] -> [ [mk_term ' ' c] ]
| [ "/" constr(c) ssrview(w) ] -> [ (mk_term ' ' c) :: w ]
END

(* There are two ways of "applying" a view to term:            *)
(*  1- using a view hint if the view is an instance of some    *)
(*     (reflection) inductive predicate.                       *)
(*  2- applying the view if it coerces to a function, adding   *)
(*     implicit arguments.                                     *)
(* They require guessing the view hints and the number of      *)
(* implicits, respectively, which we do by brute force.        *)

let view_error s gv =
  errorstrm (str ("Cannot " ^ s ^ " view ") ++ pr_term gv)

let interp_view ist si env sigma gv rid =
  match intern_term ist sigma env gv with
  | RApp (loc, RHole _, rargs) ->
    let rv = RApp (loc, rid, rargs) in
    interp_open_constr ist (re_sig si sigma) (rv, None)
  | rv ->
  let interp rc rargs =
    interp_open_constr ist (re_sig si sigma) (mkRApp rc rargs, None) in
  let rec simple_view rargs n =
    if n < 0 then view_error "use" gv else
    try interp rv rargs with _ -> simple_view (mkRHole :: rargs) (n - 1) in
  let view_nbimps = interp_view_nbimps ist (re_sig si sigma) rv in
  let view_args = [mkRApp rv (mkRHoles view_nbimps); rid] in
  let rec view_with = function
  | [] -> simple_view [rid] (interp_nbargs ist (re_sig si sigma) rv)
  | hint :: hints -> try interp hint view_args with _ -> view_with hints in
  view_with (if view_nbimps < 0 then [] else viewtab.(0))

let top_id = mk_internal_id "top assumption"

let with_view ist si env gl0 c name cl prune =
  let c2r ist x = { ist with lfun = (top_id, VConstr ([], x)) :: ist.lfun } in
  let rec loop (sigma, c') = function
  | f :: view ->
      let rid, ist = match kind_of_term c' with
        | Var id -> mkRVar id, ist
        | _ -> mkRltacVar top_id, c2r ist c' in
      loop (interp_view ist si env sigma f rid) view
  | [] ->
      let n, c' = pf_abs_evars gl0 (sigma, c') in
      let c' = if not prune then c' else pf_abs_cterm gl0 n c' in
      pf_abs_prod name gl0 c' (prod_applist cl [c]), c'
  in loop

let pf_with_view ist gl (prune, view) cl c =
  let env, sigma, si = pf_env gl, project gl, sig_it gl in
  with_view ist si env gl c (constr_name c) cl prune (sigma, c) view

(** Extended intro patterns *)

type ssripat =
  | IpatSimpl of ssrclear * ssrsimpl
  | IpatId of identifier
  | IpatWild
  | IpatCase of ssripats list
  | IpatRw of ssrocc * ssrdir
  | IpatAll
  | IpatAnon
  | IpatView of ssrtermrep list
  | IpatNoop
and ssripats = ssripat list

let remove_loc = snd

let rec ipat_of_intro_pattern = function
  | IntroIdentifier id -> IpatId id
  | IntroWildcard -> IpatWild
  | IntroOrAndPattern iorpat ->
    IpatCase 
      (List.map (List.map ipat_of_intro_pattern) 
	 (List.map (List.map remove_loc) iorpat))
  | IntroAnonymous -> IpatAnon
  | IntroRewrite b -> IpatRw ([noindex], if b then L2R else R2L)
  | IntroFresh id -> IpatAnon
  | IntroForthcoming _ -> (* Unable to determine which kind of ipat interp_introid could return [HH] *)
      assert false

let rec pr_ipat = function
  | IpatId id -> pr_id id
  | IpatSimpl (clr, sim) -> pr_clear mt clr ++ pr_simpl sim
  | IpatCase iorpat -> hov 1 (str "[" ++ pr_iorpat iorpat ++ str "]")
  | IpatRw (occ, dir) -> pr_occ occ ++ pr_dir dir
  | IpatAll -> str "*"
  | IpatWild -> str "_"
  | IpatAnon -> str "?"
  | IpatView v -> pr_view v
  | IpatNoop -> str "-"
and pr_iorpat iorpat = pr_list pr_bar pr_ipats iorpat
and pr_ipats ipats = pr_list spc pr_ipat ipats

let wit_ssripatrep, globwit_ssripatrep, rawwit_ssripatrep =
  add_genarg "ssripatrep" pr_ipat

let pr_ssripat _ _ _ = pr_ipat
let pr_ssripats _ _ _ = pr_ipats
let pr_ssriorpat _ _ _ = pr_iorpat

let intern_ipat ist ipat =
  let rec check_pat = function
  | IpatSimpl (clr, _) -> ignore (List.map (intern_hyp ist) clr)
  | IpatCase iorpat -> List.iter (List.iter check_pat) iorpat
  | _ -> () in
  check_pat ipat; ipat

let intern_ipats ist = List.map (intern_ipat ist)

let interp_introid ist gl id =
  try IntroIdentifier (hyp_id (interp_hyp ist gl (SsrHyp (dummy_loc, id))))
  with _ -> snd (interp_intro_pattern ist gl (dummy_loc, IntroIdentifier id))

let rec add_intro_pattern_hyps (loc, ipat) hyps = match ipat with
  | IntroIdentifier id ->
    if not_section_id id then SsrHyp (loc, id) :: hyps else
    hyp_err loc "Can't delete section hypothesis " id
  | IntroWildcard -> hyps
  | IntroOrAndPattern iorpat ->
    List.fold_right (List.fold_right add_intro_pattern_hyps) iorpat hyps
  | IntroAnonymous -> []
  | IntroFresh _ -> []
  | IntroRewrite _ -> hyps
  | IntroForthcoming _ -> 
    (* As in ipat_of_intro_pattern, was unable to determine which kind
      of ipat interp_introid could return [HH] *) assert false

let rec interp_ipat ist gl =
  let ltacvar id = List.mem_assoc id ist.lfun in
  let rec interp = function
  | IpatId id when ltacvar id ->
    ipat_of_intro_pattern (interp_introid ist gl id)
  | IpatSimpl (clr, sim) ->
    let add_hyps (SsrHyp (loc, id) as hyp) hyps =
      if not (ltacvar id) then hyp :: hyps else
      add_intro_pattern_hyps (loc, (interp_introid ist gl id)) hyps in
    let clr' = List.fold_right add_hyps clr [] in
    check_hyps_uniq [] clr'; IpatSimpl (clr', sim)
  | IpatCase iorpat -> IpatCase (List.map (List.map interp) iorpat)
  | ipat -> ipat in
  interp

let interp_ipats ist gl = List.map (interp_ipat ist gl)

let pushIpatRw = function
  | pats :: orpat -> (IpatRw ([noindex], L2R) :: pats) :: orpat
  | [] -> []

let pushIpatNoop = function
  | pats :: orpat -> (IpatNoop :: pats) :: orpat
  | [] -> []

ARGUMENT EXTEND ssripat TYPED AS ssripatrep list PRINTED BY pr_ssripats
  INTERPRETED BY interp_ipats
  GLOBALIZED BY intern_ipats
  | [ "_" ] -> [ [IpatWild] ]
  | [ "*" ] -> [ [IpatAll] ]
  | [ ident(id) ] -> [ [IpatId id] ]
  | [ "?" ] -> [ [IpatAnon] ]
  | [ ssrsimpl_ne(sim) ] -> [ [IpatSimpl ([], sim)] ]
  | [ ssrdocc(occ) "->" ] -> [ match occ with
      | None, occ -> [IpatRw (occ, L2R)]
      | Some clr, _ -> [IpatSimpl (clr, Nop); IpatRw ([noindex], L2R)]]
  | [ ssrdocc(occ) "<-" ] -> [ match occ with
      | None, occ ->  [IpatRw (occ, R2L)]
      | Some clr, _ -> [IpatSimpl (clr, Nop); IpatRw ([noindex], R2L)]]
  | [ ssrdocc(occ) ] -> [ match occ with
      | Some cl, _ -> check_hyps_uniq [] cl; [IpatSimpl (cl, Nop)]
      | _ -> loc_error loc "Only identifiers are allowed here"]
  | [ "->" ] -> [ [IpatRw ([noindex], L2R)] ]
  | [ "<-" ] -> [ [IpatRw ([noindex], R2L)] ]
  | [ "-" ] -> [ [IpatNoop] ]
  | [ "-/" "=" ] -> [ [IpatNoop;IpatSimpl([],Simpl)] ]
  | [ "-/=" ] -> [ [IpatNoop;IpatSimpl([],Simpl)] ]
  | [ "-/" "/" ] -> [ [IpatNoop;IpatSimpl([],Cut)] ]
  | [ "-//" ] -> [ [IpatNoop;IpatSimpl([],Cut)] ]
  | [ "-/" "/=" ] -> [ [IpatNoop;IpatSimpl([],SimplCut)] ]
  | [ "-//" "=" ] -> [ [IpatNoop;IpatSimpl([],SimplCut)] ]
  | [ "-//=" ] -> [ [IpatNoop;IpatSimpl([],SimplCut)] ]
  | [ ssrview(v) ] -> [ [IpatView v] ]
END

ARGUMENT EXTEND ssripats TYPED AS ssripat PRINTED BY pr_ssripats
  | [ ssripat(i) ssripats(tl) ] -> [ i @ tl ]
  | [ ] -> [ [] ]
END

ARGUMENT EXTEND ssriorpat TYPED AS ssripat list PRINTED BY pr_ssriorpat
| [ ssripats(pats) "|" ssriorpat(orpat) ] -> [ pats :: orpat ]
| [ ssripats(pats) "|-" ">" ssriorpat(orpat) ] -> [ pats :: pushIpatRw orpat ]
| [ ssripats(pats) "|-" ssriorpat(orpat) ] -> [ pats :: pushIpatNoop orpat ]
| [ ssripats(pats) "|->" ssriorpat(orpat) ] -> [ pats :: pushIpatRw orpat ]
| [ ssripats(pats) "||" ssriorpat(orpat) ] -> [ pats :: [] :: orpat ]
| [ ssripats(pats) "|||" ssriorpat(orpat) ] -> [ pats :: [] :: [] :: orpat ]
| [ ssripats(pats) "||||" ssriorpat(orpat) ] -> [ [pats; []; []; []] @ orpat ]
| [ ssripats(pats) ] -> [ [pats] ]
END

ARGUMENT EXTEND ssrcpat TYPED AS ssripatrep PRINTED BY pr_ssripat
  | [ "[" ssriorpat(iorpat) "]" ] -> [ IpatCase iorpat ]
END

GEXTEND Gram
  GLOBAL: ssripat;
  ssripat: [[ pat = ssrcpat -> [pat] ]];
END

ARGUMENT EXTEND ssripats_ne TYPED AS ssripat PRINTED BY pr_ssripats
  | [ ssripat(i) ssripats(tl) ] -> [ i @ tl ]
END

(* subsets of patterns *)
let check_ssrhpats loc w_binders ipats =
  let err_loc s = user_err_loc (loc, "ssreflect", s) in
  let clr, ipats =
    let rec aux clr = function
      | IpatSimpl (cl, Nop) :: tl -> aux (clr @ cl) tl
      | IpatSimpl (cl, sim) :: tl -> clr @ cl, IpatSimpl ([], sim) :: tl
      | tl -> clr, tl
    in aux [] ipats in
  let simpl, ipats = 
    match List.rev ipats with
    | IpatSimpl ([],_) as s :: tl -> [s], List.rev tl
    | _ -> [],  ipats in
  if simpl <> [] && not w_binders then
    err_loc (str "No s-item allowed here: " ++ pr_ipats simpl);
  let ipat, binders =
    let rec loop ipat = function
      | [] -> ipat, []
      | ( IpatId _| IpatAnon| IpatCase _| IpatRw _ as i) :: tl -> 
        if w_binders then
          if simpl <> [] && tl <> [] then 
            err_loc(str"binders XOR s-item allowed here: "++pr_ipats(tl@simpl))
          else if not (List.for_all (function IpatId _ -> true | _ -> false) tl)
          then err_loc (str "Only binders allowed here: " ++ pr_ipats tl)
          else ipat @ [i], tl
        else
          if tl = [] then  ipat @ [i], []
          else err_loc (str "No binder or s-item allowed here: " ++ pr_ipats tl)
      | hd :: tl -> loop (ipat @ [hd]) tl
    in loop [] ipats in
  ((clr, ipat), binders), simpl

let single loc =
  function [x] -> x | _ -> loc_error loc "Only one intro pattern is allowed"

let pr_hpats (((clr, ipat), binders), simpl) =
   pr_clear mt clr ++ pr_ipats ipat ++ pr_ipats binders ++ pr_ipats simpl
let pr_ssrhpats _ _ _ = pr_hpats

ARGUMENT EXTEND ssrhpats TYPED AS ((ssrclear * ssripat) * ssripat) * ssripat
PRINTED BY pr_ssrhpats
  | [ ssripats(i) ] -> [ check_ssrhpats loc true i ]
END

ARGUMENT EXTEND ssrhpats_nobs 
TYPED AS ((ssrclear * ssripat) * ssripat) * ssripat PRINTED BY pr_ssrhpats
  | [ ssripats(i) ] -> [ check_ssrhpats loc false i ]
END

ARGUMENT EXTEND ssrrpat TYPED AS ssripatrep PRINTED BY pr_ssripat
  | [ "->" ] -> [ IpatRw ([noindex], L2R) ]
  | [ "<-" ] -> [ IpatRw ([noindex], R2L) ]
END

type ssrintros = ssripats * ssrltacctx

let pr_intros sep (intrs, _) =
  if intrs = [] then mt() else sep () ++ str "=> " ++ pr_ipats intrs
let pr_ssrintros _ _ _ = pr_intros mt

ARGUMENT EXTEND ssrintros_ne TYPED AS ssripat * ssrltacctx
 PRINTED BY pr_ssrintros
  | [ "=>" ssripats_ne(pats) ] -> [ pats, rawltacctx ]
END

ARGUMENT EXTEND ssrintros TYPED AS ssrintros_ne PRINTED BY pr_ssrintros
  | [ ssrintros_ne(intrs) ] -> [ intrs ]
  | [ ] -> [ [], rawltacctx ]
END

let injecteq_id = mk_internal_id "injection equation"

let pf_nb_prod gl = nb_prod (pf_concl gl)

let rev_id = mk_internal_id "rev concl"

let revtoptac n0 gl =
  let n = pf_nb_prod gl - n0 in
  let dc, cl = decompose_prod_n n (pf_concl gl) in
  let dc' = dc @ [Name rev_id, compose_prod (List.rev dc) cl] in
  let f = compose_lam dc' (mkEtaApp (mkRel (n + 1)) (-n) 1) in
  refine (mkApp (f, [|Evarutil.mk_new_meta ()|])) gl

let injectidl2rtac id gl =
  tclTHEN (Equality.inj [] true id) (revtoptac (pf_nb_prod gl)) gl

let injectl2rtac c = match kind_of_term c with
| Var id -> injectidl2rtac (mkVar id, NoBindings)
| _ ->
  let id = injecteq_id in
  tclTHENLIST [havetac id c; injectidl2rtac (mkVar id, NoBindings); clear [id]]

let is_injection_case c gl =
  let mind, _ = pf_reduce_to_quantified_ind gl (pf_type_of gl c) in
  mkInd mind = build_coq_identity ()

let perform_injection c gl =
  let mind, t = pf_reduce_to_quantified_ind gl (pf_type_of gl c) in
  let dc, eqt = decompose_prod t in
  if dc = [] then injectl2rtac c gl else
  if not (closed0 eqt) then error "can't decompose a quantified equality" else
  let cl = pf_concl gl in let n = List.length dc in
  let c_eq = mkEtaApp c n 2 in
  let cl1 = mkLambda (Anonymous, mkArrow eqt cl, mkApp (mkRel 1, [|c_eq|])) in
  let id = injecteq_id in
  let id_with_ebind = (mkVar id, NoBindings) in
  let injtac = tclTHEN (introid id) (injectidl2rtac id_with_ebind) in 
  tclTHENLAST (apply (compose_lam dc cl1)) injtac gl  

let simplest_newcase_ref = ref (fun t gl -> assert false)
let simplest_newcase x gl = !simplest_newcase_ref x gl

let ssrscasetac c gl = 
  if is_injection_case c gl then perform_injection c gl
  else simplest_newcase c gl 

let intro_all gl =
  let dc, _ = Term.decompose_prod_assum (pf_concl gl) in
  tclTHENLIST (List.map anontac (List.rev dc)) gl

let rec intro_anon gl =
  try anontac (List.hd (fst (Term.decompose_prod_n_assum 1 (pf_concl gl)))) gl
  with err0 -> try tclTHEN red_in_concl intro_anon gl with _ -> raise err0
  (* with _ -> error "No product even after reduction" *)

let with_top tac =
  tclTHENLIST [introid top_id; tac (mkVar top_id); clear [top_id]]

let rec mapLR f = function [] -> [] | x :: s -> let y = f x in y :: mapLR f s

let wild_ids = ref []

let new_wild_id () =
  let i = 1 + List.length !wild_ids in
  let id = mk_wildcard_id i in
  wild_ids := id :: !wild_ids;
  id

let clear_wilds wilds gl =
  clear (List.filter (fun id -> List.mem id wilds) (pf_ids_of_hyps gl)) gl

let clear_with_wilds wilds clr0 gl =
  let extend_clr clr (id, _, _ as nd) =
    if List.mem id clr || not (List.mem id wilds) then clr else
    let vars = global_vars_set_of_decl (pf_env gl) nd in
    let occurs id' = Idset.mem id' vars in
    if List.exists occurs clr then id :: clr else clr in
  clear (Sign.fold_named_context_reverse extend_clr ~init:clr0 (pf_hyps gl)) gl

let tclTHENS_nonstrict tac tacl taclname gl =
  let tacres = tac gl in
  let n_gls = List.length (sig_it (fst tacres)) in
  let n_tac = List.length tacl in
  if n_gls = n_tac then tclTHENS (fun _ -> tacres) tacl gl else
  if n_gls = 0 then tacres else
  let pr_only n1 n2 = if n1 < n2 then str "only " else mt () in
  let pr_nb n1 n2 name =
    pr_only n1 n2 ++ int n1 ++ str (" " ^ plural n1 name) in
  errorstrm (pr_nb n_tac n_gls taclname ++ spc ()
             ++ str "for " ++ pr_nb n_gls n_tac "subgoal")


(* Forward reference to extended rewrite *)
let ipat_rewritetac = ref (fun _ -> rewritetac)

let rec is_name_in_ipats name = function
  | IpatSimpl(clr,_) :: tl -> 
      List.exists (function SsrHyp(_,id) -> id = name) clr 
      || is_name_in_ipats name tl
  | IpatId id :: tl -> id = name || is_name_in_ipats name tl
  | IpatCase l :: tl -> is_name_in_ipats name (List.flatten l @ tl)
  | _ :: tl -> is_name_in_ipats name tl
  | [] -> false

let move_top_with_view = ref (fun _ -> assert false)

(* introstac: for "move" and "clear", tclEQINTROS: for "case" and "elim" *)
(* This block hides the spaghetti-code needed to implement the only two  *)
(* tactics that should be used to process intro patters.                 *)
(* The difficulty is that we don't want to always rename, but we can     *)
(* compute needeed renamings only at runtime, so we theread a tree like  *)
(* imperativestructure so that outer renamigs are inherited by inner     *)
(* ipts and that the cler performed at the end of ipatstac clears hyps   *)
(* eventually renamed at runtime.                                        *)
(* TODO: hide wild_ids in this block too *)
let introstac, tclEQINTROS =
  let rec map_acc_k f k = function
    | [] -> (* tricky: we save wilds now, we get to_cler (aka k) later *)
      let clear_ww = clear_with_wilds !wild_ids in           
      [fun gl -> clear_ww (hyps_ids (List.flatten (List.map (!) k))) gl]
    | x :: xs -> let k, x = f k xs x in x :: map_acc_k f k xs in
  let rename force to_clr rest clr gl = 
    let hyps = pf_hyps gl in
    pp(lazy(str"rename " ++ pr_clear spc clr));
    let () = if not force then List.iter (check_hyp_exists hyps) clr in
    if List.exists (fun x -> force || is_name_in_ipats (hyp_id x) rest) clr then
      let ren_clr, ren = 
        List.split (List.map (fun x -> let x = hyp_id x in
          let x' = mk_anon_id (string_of_id x) gl in
          SsrHyp (dummy_loc, x'), (x, x')) clr) in
      let () = to_clr := ren_clr in
      rename_hyp ren gl 
    else
      let () = to_clr := clr in
      tclIDTAC gl in
  let rec ipattac ?ist k rest = function
    | IpatWild -> k, introid (new_wild_id ())
    | IpatCase iorpat -> k, tclIORPAT ?ist k (with_top ssrscasetac) iorpat
    | IpatRw (occ, dir) -> k, with_top (!ipat_rewritetac occ dir)
    | IpatId id -> k, introid id
    | IpatSimpl (clr, sim) ->
      let to_clr = ref [] in
      to_clr :: k, tclTHEN (rename false to_clr rest clr) (simpltac sim)
    | IpatAll -> k, intro_all
    | IpatAnon -> k, intro_anon
    | IpatNoop -> k, tclIDTAC
    | IpatView v -> match ist with
        | None -> anomaly "ipattac with no ist but view"
        | Some ist -> match rest with
            | (IpatCase _ | IpatRw _)::_ -> 
              let to_clr = ref [] in let top_id = ref top_id in
              to_clr :: k, 
              tclTHEN
                (!move_top_with_view false top_id (false,v) ist)
                (fun gl -> 
                  rename true to_clr rest [SsrHyp (dummy_loc, !top_id)]gl)
            | _ -> k, !move_top_with_view true (ref top_id) (true,v) ist
  and tclIORPAT ?ist k tac = function
    | [[]] -> tac
    | orp -> 
       tclTHENS_nonstrict tac (mapLR (ipatstac ?ist k) orp) "intro pattern"
  and ipatstac ?ist k ipats = 
    tclTHENLIST (map_acc_k (ipattac ?ist) k ipats) in
  let introstac ?ist ipats =
    wild_ids := [];
    let tac = ipatstac ?ist [] ipats in
    tclTHENLIST [tac; clear_wilds !wild_ids] in
  let tclEQINTROS ?ist tac eqtac ipats =
    wild_ids := [];
    let rec split_itacs to_clr tac' = function
    | (IpatSimpl _ as spat) :: ipats' -> 
      let to_clr, tac = ipattac ?ist to_clr ipats' spat in
      split_itacs to_clr (tclTHEN tac' tac) ipats'
    | IpatCase iorpat :: ipats' -> 
        to_clr, tclIORPAT ?ist to_clr tac' iorpat, ipats'
    | ipats' -> to_clr, tac', ipats' in
    let to_clr, tac1, ipats' = split_itacs [] tac ipats in
    let tac2 = ipatstac ?ist to_clr ipats' in
    tclTHENLIST [tac1; eqtac; tac2; clear_wilds !wild_ids] in
  introstac, tclEQINTROS
;;

let rec eqmoveipats eqpat = function
  | (IpatSimpl _ as ipat) :: ipats -> ipat :: eqmoveipats eqpat ipats
  | (IpatAll :: _ | []) as ipats -> IpatAnon :: eqpat :: ipats
   | ipat :: ipats -> ipat :: eqpat :: ipats

(* General case *)
let tclINTROS tac (ipats, ctx) = 
  let ist = get_ltacctx ctx in
  tclEQINTROS ~ist (tac ist) tclIDTAC ipats

(** The "=>" tactical *)

let ssrintros_sep =
  let atom_sep = function
    | TacSplit (_,_, [NoBindings]) -> mt
    | TacLeft (_, NoBindings) -> mt
    | TacRight (_, NoBindings) -> mt
    (* | TacExtend (_, "ssrapply", []) -> mt *)
    | _ -> spc in
  function
    | TacId [] -> mt
    | TacArg (Tacexp _) -> mt
    | TacArg (Reference _) -> mt
    | TacAtom (_, atom) -> atom_sep atom
    | _ -> spc

let pr_ssrintrosarg _ _ prt (tac, ipats) =
  prt tacltop tac ++ pr_intros (ssrintros_sep tac) ipats

ARGUMENT EXTEND ssrintrosarg TYPED AS tactic * ssrintros
   PRINTED BY pr_ssrintrosarg
| [ "(**)" ssrtacarg(arg) ssrintros_ne(ipats) ] -> [ arg, ipats ]
END

TACTIC EXTEND ssrtclintros
| [ "(**)" ssrintrosarg(arg) ] ->
  [ let tac, intros = arg in
    tclINTROS (fun ist -> ssrevaltac ist tac) intros ]
END
set_pr_ssrtac "tclintros" 0 [ArgSsr "introsarg"]

let tclintros_expr loc tac ipats =
  let args = [in_gen rawwit_ssrintrosarg (tac, ipats)] in
  ssrtac_expr loc "tclintros" args

GEXTEND Gram
  GLOBAL: tactic_expr;
  tactic_expr: LEVEL "1" [ RIGHTA
    [ tac = tactic_expr; intros = ssrintros_ne -> tclintros_expr loc tac intros
    ] ];
END

(** Multipliers *)

(* modality *)

type ssrmmod = May | Must | Once

let pr_mmod = function May -> str "?" | Must -> str "!" | Once -> mt ()

let wit_ssrmmod, globwit_ssrmmod, rawwit_ssrmmod = add_genarg "ssrmmod" pr_mmod
let ssrmmod = Gram.Entry.create "ssrmmod"
GEXTEND Gram
  GLOBAL: ssrmmod;
  ssrmmod: [[ "!" -> Must | LEFTQMARK -> May | "?" -> May]];
END

(* tactical *)

let tclID tac = tac

let tclDOTRY n tac =
  if n <= 0 then tclIDTAC else
  let rec loop i gl =
    if i = n then tclTRY tac gl else
    tclTRY (tclTHEN tac (loop (i + 1))) gl in
  loop 1

let tclDO n tac =
  let prefix i = str"At iteration " ++ int i ++ str": " in
  let tac_err_at i gl =
    try tac gl
    with 
    | UserError (l, s) -> raise (UserError (l, prefix i ++ s))
    | Compat.Exc_located(loc, UserError (l, s))  -> 
        raise (Compat.Exc_located(loc, UserError (l, prefix i ++ s))) in
  let rec loop i gl =
    if i = n then tac_err_at i gl else
    (tclTHEN (tac_err_at i) (loop (i + 1))) gl in
  loop 1

let tclMULT = function
  | 0, May  -> tclREPEAT
  | 1, May  -> tclTRY
  | n, May  -> tclDOTRY n
  | 0, Must -> tclAT_LEAST_ONCE
  | n, Must when n > 1 -> tclDO n
  | _       -> tclID

(** The "do" tactical. *)

(*
type ssrdoarg = ((ssrindex * ssrmmod) * (ssrhint * ssrltacctx)) * ssrclauses
*)

let pr_ssrdoarg prc _ prt (((n, m), (tac, _)), clauses) =
  pr_index n ++ pr_mmod m ++ pr_hintarg prt tac ++ pr_clauses clauses

ARGUMENT EXTEND ssrdoarg
  TYPED AS ((ssrindex * ssrmmod) * (ssrhintarg * ssrltacctx)) * ssrclauses
  PRINTED BY pr_ssrdoarg
| [ "(**)" ] -> [ anomaly "Grammar placeholder match" ]
END

let ssrdotac (((n, m), (tac, ctx)), clauses) =
  let mul = get_index n, m in
  tclCLAUSES (tclMULT mul (hinttac (get_ltacctx ctx) false tac)) clauses

TACTIC EXTEND ssrtcldo
| [ "(**)" "do" ssrdoarg(arg) ] -> [ ssrdotac arg ]
END
set_pr_ssrtac "tcldo" 3 [ArgSep "do "; ArgSsr "doarg"]

let ssrdotac_expr loc n m tac clauses =
  let arg = ((n, m), (tac, rawltacctx)), clauses in
  ssrtac_expr loc "tcldo" [in_gen rawwit_ssrdoarg arg]

GEXTEND Gram
  GLOBAL: tactic_expr;
  ssrdotac: [
    [ tac = tactic_expr LEVEL "3" -> mk_hint tac
    | tacs = ssrortacarg -> tacs
  ] ];
  tactic_expr: LEVEL "3" [ RIGHTA
    [ IDENT "do"; m = ssrmmod; tac = ssrdotac; clauses = ssrclauses ->
      ssrdotac_expr loc noindex m tac clauses
    | IDENT "do"; tac = ssrortacarg; clauses = ssrclauses ->
      ssrdotac_expr loc noindex Once tac clauses
    | IDENT "do"; n = int_or_var; m = ssrmmod;
                  tac = ssrdotac; clauses = ssrclauses ->
      ssrdotac_expr loc (mk_index loc n) m tac clauses
    ] ];
END

(** The "first" and "last" tacticals. *)

(* type ssrseqarg = ssrindex * (ssrtacarg * ssrtac option) *)

let pr_seqtacarg prt = function
  | (is_first, []), _ -> str (if is_first then "first" else "last")
  | tac, Some dtac ->
    hv 0 (pr_hintarg prt tac ++ spc() ++ str "|| " ++ prt tacltop dtac)
  | tac, _ -> pr_hintarg prt tac

let pr_ssrseqarg _ _ prt = function
  | ArgArg 0, tac -> pr_seqtacarg prt tac
  | i, tac -> pr_index i ++ str " " ++ pr_seqtacarg prt tac

(* We must parse the index separately to resolve the conflict with *)
(* an unindexed tactic.                                            *)
ARGUMENT EXTEND ssrseqarg TYPED AS ssrindex * (ssrhintarg * tactic option)
                          PRINTED BY pr_ssrseqarg
| [ "(**)" ] -> [ anomaly "Grammar placeholder match" ]
END

let sq_brace_tacnames =
   ["first"; "solve"; "do"; "rewrite"; "have"; "suffices"; "wlog"]
   (* "by" is a keyword *)
let accept_ssrseqvar strm =
  match Stream.npeek 1 strm with
  | ["IDENT", id] when not (List.mem id sq_brace_tacnames) ->
     accept_before_syms_or_ids ["["] ["first";"last"] strm
  | _ -> raise Stream.Failure

let test_ssrseqvar = Gram.Entry.of_parser "test_ssrseqvar" accept_ssrseqvar

let swaptacarg (loc, b) = (b, []), Some (TacAtom (loc, TacRevert []))

let check_seqtacarg dir arg = match snd arg, dir with
  | ((true, []), Some (TacAtom (loc, _))), L2R ->
    loc_error loc "expected \"last\""
  | ((false, []), Some (TacAtom (loc, _))), R2L ->
    loc_error loc "expected \"first\""
  | _, _ -> arg

let ssrorelse = Gram.Entry.create "ssrorelse"
GEXTEND Gram
  GLOBAL: ssrorelse ssrseqarg;
  ssrseqidx: [
    [ test_ssrseqvar; id = Prim.ident -> ArgVar (loc, id)
    | n = Prim.natural -> ArgArg (check_index loc n)
    ] ];
  ssrswap: [[ IDENT "first" -> loc, true | IDENT "last" -> loc, false ]];
  ssrorelse: [[ "||"; tac = tactic_expr LEVEL "2" -> tac ]];
  ssrseqarg: [
    [ arg = ssrswap -> noindex, swaptacarg arg
    | i = ssrseqidx; tac = ssrortacarg; def = OPT ssrorelse -> i, (tac, def)
    | i = ssrseqidx; arg = ssrswap -> i, swaptacarg arg
    | tac = tactic_expr LEVEL "3" -> noindex, (mk_hint tac, None)
    ] ];
END

let tclPERM perm tac gls =
  let mkpft n g r =
    {Proof_type.open_subgoals = n; Proof_type.goal = g; Proof_type.ref = r} in
  let mkleaf g = mkpft 0 g None in
  let mkprpft n g pr a = mkpft n g (Some (Proof_type.Prim pr, a)) in
  let mkrpft n g c = mkprpft n g (Proof_type.Refine c) in
  let mkipft n g =
    let mki pft (id, _, _ as d) =
      let g' = {g with evar_concl = mkNamedProd_or_LetIn d g.evar_concl} in
      mkprpft n g' (Proof_type.Intro id) [pft] in
    List.fold_left mki in
  let gl = Refiner.sig_it gls in
  let mkhyp subgl =
    let rec chop_section = function
    | (x, _, _ as d) :: e when not_section_id x -> d :: chop_section e
    | _ -> [] in
    let lhyps = Environ.named_context_of_val subgl.evar_hyps in
    mk_perm_id (), subgl, chop_section lhyps in
  let mkpfvar (hyp, subgl, lhyps) =
    let mkarg args (lhyp, body, _) =
      if body = None then mkVar lhyp :: args else args in
    mkrpft 0 subgl (applist (mkVar hyp, List.fold_left mkarg [] lhyps)) [] in
  let mkpfleaf (_, subgl, lhyps) = mkipft 1 gl (mkleaf subgl) lhyps in
  let mkmeta _ = Evarutil.mk_new_meta () in
  let mkhypdecl (hyp, subgl, lhyps) =
    hyp, None, it_mkNamedProd_or_LetIn subgl.evar_concl lhyps in
  let subgls, v as res0 = tac gls in
  let sigma, subgll = Refiner.unpackage subgls in
  let n = List.length subgll in if n = 0 then res0 else
  let hyps = List.map mkhyp subgll in
  let hyp_decls = List.map mkhypdecl (List.rev (perm hyps)) in
  let c = applist (mkmeta (), List.map mkmeta subgll) in
  let pft0 = mkipft 0 gl (v (List.map mkpfvar hyps)) hyp_decls in
  let pft1 = mkrpft n gl c (pft0 :: List.map mkpfleaf (perm hyps)) in
  let subgll', v' = Refiner.frontier pft1 in
  Refiner.repackage sigma subgll', v'

let tclREV = tclPERM List.rev

let rot_hyps dir i hyps =
  let n = List.length hyps in
  if i = 0 then List.rev hyps else
  if i > n then error "Not enough subgoals" else
  let rec rot i l_hyps = function
    | hyp :: hyps' when i > 0 -> rot (i - 1) (hyp :: l_hyps) hyps'
    | hyps' -> hyps' @ (List.rev l_hyps) in
  rot (match dir with L2R -> i | R2L -> n - i) [] hyps

let tclSEQAT (atac1, ctx) dir (ivar, ((_, atacs2), atac3)) =
  let i = get_index ivar in
  let evtac = ssrevaltac (get_ltacctx ctx) in
  let tac1 = evtac atac1 in
  if atacs2 = [] && atac3 <> None then tclPERM (rot_hyps dir i) tac1  else
  let evotac = function Some atac -> evtac atac | _ -> tclIDTAC in
  let tac3 = evotac atac3 in
  let rec mk_pad n = if n > 0 then tac3 :: mk_pad (n - 1) else [] in
  match dir, mk_pad (i - 1), List.map evotac atacs2 with
  | L2R, [], [tac2] when atac3 = None -> tclTHENFIRST tac1 tac2
  | L2R, [], [tac2] when atac3 = None -> tclTHENLAST tac1 tac2
  | L2R, pad, tacs2 -> tclTHENSFIRSTn tac1 (Array.of_list (pad @ tacs2)) tac3
  | R2L, pad, tacs2 -> tclTHENSLASTn tac1 tac3 (Array.of_list (tacs2 @ pad))

(* We can't actually parse the direction separately because this   *)
(* would introduce conflicts with the basic ltac syntax.           *)
let pr_ssrseqdir _ _ _ = function
  | L2R -> str ";" ++ spc () ++ str "first "
  | R2L -> str ";" ++ spc () ++ str "last "

ARGUMENT EXTEND ssrseqdir TYPED AS ssrdir PRINTED BY pr_ssrseqdir
| [ "(**)" ] -> [ anomaly "Grammar placeholder match" ]
END

TACTIC EXTEND ssrtclseq
| [ "(**)" ssrtclarg(tac) ssrseqdir(dir) ssrseqarg(arg) ] ->
  [ tclSEQAT tac dir arg ]
END
set_pr_ssrtac "tclseq" 5 [ArgSsr "tclarg"; ArgSsr "seqdir"; ArgSsr "seqarg"]

let tclseq_expr loc tac dir arg =
  let arg1 = in_gen rawwit_ssrtclarg (tac, rawltacctx) in
  let arg2 = in_gen rawwit_ssrseqdir dir in
  let arg3 = in_gen rawwit_ssrseqarg (check_seqtacarg dir arg) in
  ssrtac_expr loc "tclseq" [arg1; arg2; arg3]

GEXTEND Gram
  GLOBAL: tactic_expr;
  ssr_first: [
    [ tac = ssr_first; ipats = ssrintros_ne -> tclintros_expr loc tac ipats
    | "["; tacl = LIST0 tactic_expr SEP "|"; "]" -> TacFirst tacl
    ] ];
  ssr_first_else: [
    [ tac1 = ssr_first; tac2 = ssrorelse -> TacOrelse (tac1, tac2)
    | tac = ssr_first -> tac ]];
  tactic_expr: LEVEL "4" [ LEFTA
    [ tac1 = tactic_expr; ";"; IDENT "first"; tac2 = ssr_first_else ->
      TacThen (tac1,[||], tac2,[||])
    | tac = tactic_expr; ";"; IDENT "first"; arg = ssrseqarg ->
      tclseq_expr loc tac L2R arg
    | tac = tactic_expr; ";"; IDENT "last"; arg = ssrseqarg ->
      tclseq_expr loc tac R2L arg
    ] ];
END

(** 5. Bookkeeping tactics (clear, move, case, elim) *)

(* post-interpretation of terms *)

let pf_abs_ssrterm ist gl t =
  let n, c = pf_abs_evars gl (interp_term ist gl t) in pf_abs_cterm gl n c

let pf_interp_ty ist gl ty =
   let n_binders = ref 0 in
   let ty = match ty with
   | a, (t, None) ->
     let rec force_type = function
     | RProd (l, x, k, s, t) -> incr n_binders; RProd (l, x, k, s, force_type t)
     | RLetIn (l, x, v, t) -> incr n_binders; RLetIn (l, x, v, force_type t)
     | ty -> mkRCast ty mkRType in
     a, (force_type t, None)
   | _, (_, Some ty) ->
     let rec force_type = function
     | CProdN (l, abs, t) ->
       n_binders := !n_binders +  List.length (List.flatten (List.map pi1 abs));
       CProdN (l, abs, force_type t)
     | CLetIn (l, n, v, t) -> incr n_binders; CLetIn (l, n, v, force_type t)
     | ty -> mkCCast dummy_loc ty (mkCType dummy_loc) in
     mk_term ' ' (force_type ty) in
   let strip_cast (sigma, t) =
     let rec aux t = match kind_of_type t with
     | CastType (t, ty) when !n_binders = 0 && isSort ty -> t
     | ProdType(n,s,t) -> decr n_binders; mkProd (n, s, aux t)
     | LetInType(n,v,ty,t) -> decr n_binders; mkLetIn (n, v, ty, aux t)
     | _ -> anomaly "pf_interp_ty: ssr Type cast deleted by typecheck" in
     sigma, aux t in
   let ty = strip_cast (interp_term ist gl ty) in
   let n, c = pf_abs_evars gl ty in
   let lam_c = pf_abs_cterm gl n c in
   let ctx, c = decompose_lam_n n lam_c in
   n, compose_prod ctx c, lam_c
;;

let whd_app f args = Reductionops.whd_betaiota Evd.empty (mkApp (f, args))

(** Unification procedures.                                *)

(* To enforce the rigidity of the rooted match we always split  *)
(* top applications, so the unification procedures operate on   *)
(* arrays of patterns and terms.                                *)
(* We perform three kinds of unification:                       *)
(*  EQ: exact conversion check                                  *)
(*  FO: first-order unification of evars, without conversion    *)
(*  HO: higher-order unification with conversion                *)
(* The subterm unification strategy is to find the first FO     *)
(* match, if possible, and the first HO match otherwise, then   *)
(* compute all the occurrences that are EQ matches for the      *)
(* relevant subterm.                                            *)
(*   Additional twists:                                         *)
(*    - If FO/HO fails then we attempt to fill evars using      *)
(*      typeclasses before raising an outright error. We also   *)
(*      fill typeclasses even after a successful match, since   *)
(*      beta-reduction and canonical instances may leave        *)
(*      undefined evars.                                        *)
(*    - We do postchecks to rule out matches that are not       *)
(*      closed or that assign to a global evar; these can be    *)
(*      disabled for rewrite or dependent family matches.       *)
(*    - We do a full FO scan before turning to HO, as the FO    *)
(*      comparison can be much faster than the HO one.          *)

let unif_EQ env sigma p c =
  let evars = existential_opt_value sigma in 
  try let _ = Reduction.conv env p ~evars c in true with _ -> false

let unif_EQ_args env sigma pa a =
  let n = Array.length pa in
  let rec loop i = (i = n) || unif_EQ env sigma pa.(i) a.(i) && loop (i + 1) in
  loop 0

let pr_cargs a =
  str "[" ++ pr_list pr_spc pr_constr (Array.to_list a) ++ str "]"

exception NoMatch
exception NoProgress

let unif_HO env ise p c = Evarconv.the_conv_x env p c ise

let unif_HOtype env ise p c = Evarconv.the_conv_x_leq env p c ise

let unif_HO_args env ise0 pa i ca =
  let n = Array.length pa in
  let rec loop ise j =
    if j = n then ise else loop (unif_HO env ise pa.(j) ca.(i + j)) (j + 1) in
  loop ise0 0

(* FO unification should boil down to calling w_unify with no_delta, but  *)
(* alas things are not so simple: w_unify does partial type-checking,     *)
(* which breaks down when the no-delta flag is on (as the Coq type system *)
(* requires full convertibility. The workaround here is to convert all    *)
(* evars into metas, since 8.2 does not TC metas. This means some lossage *)
(* for HO evars, though hopefully Miller patterns can pick up some of     *)
(* those cases, and HO matching will mop up the rest.                     *)
let flags_FO = {Unification.default_no_delta_unify_flags with 
                Unification.modulo_conv_on_closed_terms = None}

let unif_FO env ise p c =
  Unification.w_unify false env Reduction.CONV ~flags:flags_FO p c ise

(* Perform evar substitution in main term and prune substitution. *)
let nf_open_term sigma0 ise c =
  let s = ise and s' = ref sigma0 in
  let rec nf c' = match kind_of_term c' with
  | Evar ex ->
    begin try nf (existential_value s ex) with _ ->
    let k, a = ex in let a' = Array.map nf a in
    if not (Evd.mem !s' k) then
      s' := Evd.add !s' k (Evarutil.nf_evar_info s (Evd.find s k));
    mkEvar (k, a')
    end
  | _ -> map_constr nf c' in
  let copy_def k evi () =
    if evar_body evi != Evd.Evar_empty then () else
    match Evd.evar_body (Evd.find s k) with
    | Evar_defined c' -> s' := Evd.define k (nf c') !s'
    | _ -> () in
  let c' = nf c in let _ = Evd.fold copy_def sigma0 () in !s', c'

(* We try to work around the fact that evarconv drops secondary unification *)
(* problems; we give up after 10 iterations because Evarutil.solve_refl can *)
(* cause divergence. We also need to recheck type-correctness of all evar   *)
(* assignments because the checks in both evarconv and unification are      *)
(* INCOMPLETE.                                                              *)

(* Workaround for Coq bug #2129. *)
let is_unfiltered evi = List.for_all (fun b -> b) (Evd.evar_filter evi)

let unif_end env sigma0 ise0 pt ok =
  let rec loop sigma ise m =
    if snd (extract_all_conv_pbs ise) != [] then
      if m = 0 then raise NoMatch
      else let ise' = Evarconv.consider_remaining_unif_problems env ise in
	loop sigma ise' (m - 1)
    else
    let sigma' = ise in
    if sigma' != sigma then
      let undefined ev = try not (Evd.is_defined sigma ev) with _ -> true in
      let unif_evtype ev evi ise' = match evi.evar_body with
      | Evar_defined c when undefined ev && is_unfiltered evi ->
        let ev_env = Evd.evar_env evi in
        let t = Retyping.get_type_of ev_env ise' c in
        unif_HOtype ev_env ise' t evi.evar_concl
      | _ -> ise' in
      loop sigma' (Evd.fold unif_evtype sigma' ise) m    
    else
      (* Assume the proof engine ensures that typeclass evar assignments *)
      (* are type-correct. *)
      let s, t = nf_open_term sigma0 ise pt in
      let ise1 = create_evar_defs s in
      let ise2 = Typeclasses.resolve_typeclasses ~fail:true env ise1 in
      if not (ok ise) then raise NoMatch else (* RW progress check *)
      if ise2 == ise1 then (s, t) else nf_open_term sigma0 ise2 t in
   loop sigma0 ise0 10

(* This a version of unif_end without retyping; it should replace the one
   above if/when evarconv and unification get fixed.
let unif_end env sigma0 ise0 pt _ =
  let rec loop ise m =
    if snd (extract_all_conv_pbs ise) = [] then
      let s, t = nf_open_term sigma0 ise pt in
      let ise1 = create_evar_defs s in
      let ise2 = Typeclasses.resolve_typeclasses ~fail:true env ise1 in
      if not (ok ise) then raise NoProgress else
      if ise2 == ise1 then (s, t) else nf_open_term sigma0 ise2 t
    else if m = 0 then raise NoMatch
    else match Evarconv.consider_remaining_unif_problems env ise with
    | ise', true -> loop ise' (m - 1)
    | _ -> raise NoMatch in
  loop ise0 10
*)

let pf_unif_HO gl sigma pt p c =
  let env = pf_env gl in
  let ise = unif_HO env (create_evar_defs sigma) p c in
  unif_end env (project gl) ise pt (fun _ -> true)

(* This is what the definition of iter_constr should be... *)
let iter_constr_LR f c = match kind_of_term c with
  | Evar (k, a) -> Array.iter f a
  | Cast (cc, _, t) -> f cc; f t  
  | Prod (_, t, b) | Lambda (_, t, b)  -> f t; f b
  | LetIn (_, v, t, b) -> f v; f t; f b
  | App (cf, a) -> f cf; Array.iter f a
  | Case (_, p, v, b) -> f v; f p; Array.iter f b
  | Fix (_, (_, t, b)) | CoFix (_, (_, t, b)) ->
    for i = 0 to Array.length t - 1 do f t.(i); f b.(i) done
  | _ -> ()

let pp_term gl t =
  let t = Reductionops.nf_evar (project gl) t in pr_constr t
let pp_concat hd ?(sep=str", ") = function [] -> hd | x :: xs ->
  hd ++ List.fold_left (fun acc x -> acc ++ sep ++ x) x xs

(* The comparison used to determine which subterms matches is KEYED        *)
(* CONVERSION. This looks for convertible terms that either have the same  *)
(* same head constant as pat if pat is an application (after beta-iota),   *)
(* or start with the same constr constructor (esp. for LetIn); this is     *)
(* disregarded if the head term is let x := ... in x, and casts are always *)
(* ignored and removed).                                                   *)
(* Record projections get special treatment: in addition to the projection *)
(* constant itself, ssreflect also recognizes head constants of canonical  *)
(* projections.                                                            *)

type pattern_class =
  | KpatFixed
  | KpatConst
  | KpatEvar of existential_key
  | KpatLet
  | KpatRigid
  | KpatFlex
  | KpatProj of constant

type upattern = {
  up_k : pattern_class;
  up_FO : constr;
  up_f : constr;
  up_a : constr array;
  up_t : constr;                      (* equation proof term or matched term *)
  up_dir : ssrdir;                    (* direction of the rule *)
  up_ok : constr -> evar_map -> bool; (* progess test for rewrite *)
  }

let all_ok _ _ = true

let proj_nparams c =
  try 1 + Recordops.find_projection_nparams (ConstRef c) with _ -> 0

let isFixed c = match kind_of_term c with
  | Var _ | Ind _ | Construct _ | Const _ -> true
  | _ -> false

let isRigid c = match kind_of_term c with
  | Prod _ | Sort _ | Lambda _ | Case _ | Fix _ | CoFix _ -> true
  | _ -> false

exception UndefPat

(* Compile a match pattern from a term; t is the term to fill. *)
(* p_origin can be passed to obtain a better error message     *)
let mk_upat ?(hack=false) env sigma0 ise t ok ?p_origin dir p =
  let k, f, a =
    let f, a = Reductionops.whd_betaiota_stack ise p in
    match kind_of_term f with
    | Const p ->
      let np = proj_nparams p in
      if np = 0 || np > List.length a then KpatConst, f, a else
      let a1, a2 = list_chop np a in KpatProj p, applist(f, a1), a2
    | Var _ | Ind _ | Construct _ -> KpatFixed, f, a
    | Evar (k, _) ->
      if Evd.mem sigma0 k then KpatEvar k, f, a else
      if a <> [] then KpatFlex, f, a else 
      (match p_origin with None -> error "indeterminate pattern"
      | Some (dir, rule) -> errorstrm (str "indeterminate " ++ pr_dir_side dir
          ++ str " in " ++ pr_constr_pat rule))
    | LetIn (_, v, _, b) ->
      if b <> mkRel 1 then KpatLet, f, a else KpatFlex, v, a
    | _ -> KpatRigid, f, a in
  let aa = Array.of_list a in
  let ise', p' = evars_for_FO ~hack env sigma0 ise (mkApp (f, aa)) in
  { up_k = k; up_FO = p'; up_f = f; 
    up_a = aa; up_ok = ok; up_dir = dir; up_t = t}, 
  ise'

(* Specialize a pattern after a successful match: assign a precise head *)
(* kind and arity for Proj and Flex patterns.                           *)
let ungen_upat lhs (sigma, t) u =
  let f, a = safeDestApp lhs in
  let k = match kind_of_term f with
  | Var _ | Ind _ | Construct _ -> KpatFixed
  | Const _ -> KpatConst
  | Evar (k, _) -> if is_defined sigma k then raise NoMatch else KpatEvar k
  | LetIn _ -> KpatLet
  | _ -> KpatRigid in
  sigma, {u with up_k = k; up_FO = lhs; up_f = f; up_a = a; up_t = t}

let nb_cs_proj_args pc f u =
  let na k =
    List.length (lookup_canonical_conversion (ConstRef pc, k)).o_TCOMPS in
  try match kind_of_term f with
  | Prod _ -> na Prod_cs
  | Sort s -> na (Sort_cs (family_of_sort s))
  | Const c' when c' = pc -> Array.length (snd (destApp u.up_f))
  | Var _ | Ind _ | Construct _ | Const _ -> na (Const_cs (global_of_constr f))
  | _ -> -1
  with Not_found -> -1

let filter_upat i0 f n u fpats =
  let na = Array.length u.up_a in
  if n < na then fpats else
  let np = match u.up_k with
  | KpatConst when eq_constr u.up_f f -> na
  | KpatFixed when u.up_f = f -> na 
  | KpatEvar k when isEvar_k k f -> na
  | KpatLet when isLetIn f -> na
  | KpatRigid when isRigid f -> na
  | KpatFlex -> na
  | KpatProj pc ->
    let np = na + nb_cs_proj_args pc f u in if n < np then -1 else np
  | _ -> -1 in
  if np < na then fpats else
  let () = if !i0 < np then i0 := n in (u, np) :: fpats

let filter_upat_FO i0 f n u fpats =
  let np = nb_args u.up_FO in
  if n < np then fpats else
  let ok = match u.up_k with
  | KpatConst -> eq_constr u.up_f f 
  | KpatFixed -> u.up_f = f 
  | KpatEvar k -> isEvar_k k f
  | KpatLet -> isLetIn f
  | KpatRigid -> isRigid f
  | KpatProj pc -> f = mkConst pc
  | KpatFlex -> i0 := n; true in
  if ok then begin if !i0 < np then i0 := np; (u, np) :: fpats end else fpats

exception FoundUnif of (evar_map * upattern)
(* Note: we don't update env as we descend into the term, as the primitive *)
(* unification procedure always rejects subterms with bound variables.     *)

(* We are forced to duplicate code between the FO/HO matching because we    *)
(* have to work around several kludges in unify.ml:                         *)
(*  - w_unify drops into second-order unification when the pattern is an    *)
(*    application whose head is a meta.                                     *)
(*  - w_unify tries to unify types without subsumption when the pattern     *)
(*    head is an evar or meta (e.g., it fails on ?1 = nat when ?1 : Type).  *)
(*  - w_unify expands let-in (zeta conversion) eagerly, whereas we want to  *)
(*    match a head let rigidly.                                             *)
let match_upats_FO upats env sigma0 ise =
  let rec loop c =
    let f, a = splay_app ise c in let i0 = ref (-1) in
    let fpats =
      List.fold_right (filter_upat_FO i0 f (Array.length a)) upats [] in
    while !i0 >= 0 do
      let i = !i0 in i0 := -1;
      let c' = mkSubApp f i a in
      let one_match (u, np) =
         let skip =
           if i <= np then i < np else
           if u.up_k == KpatFlex then begin i0 := i - 1; false end else
           begin if !i0 < np then i0 := np; true end in
         if skip || not (closed0 c') then () else try
           let _ = match u.up_k with
           | KpatFlex ->
             let kludge v = mkLambda (Anonymous, mkImplicit, v) in
             unif_FO env ise (kludge u.up_FO) (kludge c')
           | KpatLet ->
             let kludge vla =
               let vl, a = safeDestApp vla in
               let x, v, t, b = destLetIn vl in
               mkApp (mkLambda (x, t, b), array_cons v a) in
             unif_FO env ise (kludge u.up_FO) (kludge c')
           | _ -> unif_FO env ise u.up_FO c' in
           let ise' = (* Unify again using HO to assign evars *)
             let p = mkApp (u.up_f, u.up_a) in
             try unif_HO env ise p c' with _ -> raise NoMatch in
           let lhs = mkSubApp f i a in
           let pt' = unif_end env sigma0 ise' u.up_t (u.up_ok lhs) in
           raise (FoundUnif (ungen_upat lhs pt' u))
       with FoundUnif _ as sigma_u -> raise sigma_u 
       | Not_found -> anomaly "incomplete ise in match_upats_FO"
       | _ -> () in
    List.iter one_match fpats
  done;
  iter_constr_LR loop f; Array.iter loop a in
  fun c -> try loop c with Invalid_argument _ -> anomaly "IN FO"


let match_upats_HO upats env sigma0 ise c =
 let it_did_match = ref false in
 let rec aux upats env sigma0 ise c =
  let f, a = splay_app ise c in let i0 = ref (-1) in
  let fpats = List.fold_right (filter_upat i0 f (Array.length a)) upats [] in
  while !i0 >= 0 do
    let i = !i0 in i0 := -1;
    let one_match (u, np) =
      let skip =
        if i <= np then i < np else
        if u.up_k == KpatFlex then begin i0 := i - 1; false end else
        begin if !i0 < np then i0 := np; true end in
      if skip then () else try
        let ise' = match u.up_k with
        | KpatFixed | KpatConst -> ise
        | KpatEvar _ ->
          let _, pka = destEvar u.up_f and _, ka = destEvar f in
          unif_HO_args env ise pka 0 ka
        | KpatLet ->
          let x, v, t, b = destLetIn f in
          let _, pv, _, pb = destLetIn u.up_f in
          let ise' = unif_HO env ise pv v in
          unif_HO (Environ.push_rel (x, None, t) env) ise' pb b
        | KpatFlex | KpatProj _ ->
          unif_HO env ise u.up_f (mkSubApp f (i - Array.length u.up_a) a)
        | _ -> unif_HO env ise u.up_f f in
        let ise'' = unif_HO_args env ise' u.up_a (i - Array.length u.up_a) a in
        let lhs = mkSubApp f i a in
        let pt' = unif_end env sigma0 ise'' u.up_t (u.up_ok lhs) in
        raise (FoundUnif (ungen_upat lhs pt' u))
      with FoundUnif _ as sigma_u -> raise sigma_u 
      | NoProgress -> it_did_match := true
      | _ -> () in
    List.iter one_match fpats
  done;
  iter_constr_LR (aux upats env sigma0 ise) f;
  Array.iter (aux upats env sigma0 ise) a
 in
 aux upats env sigma0 ise c;
 if !it_did_match then raise NoProgress


let fixed_upat = function
| {up_k = KpatFlex | KpatEvar _ | KpatProj _} -> false 
| {up_t = t} -> not (occur_existential t)

let do_once r f = match !r with Some _ -> () | None -> r := Some (f ())

let assert_done r = 
  match !r with Some x -> x | None -> anomaly "do_once never called"

(* upats_origin makes a better error message only            *)
let mk_pmatcher ?(raise_NoMatch=false) sigma0 occ ?upats_origin (upats, ise) =
  let nocc = ref 0 and skip_occ = ref false in
  let use_occ, occ_list = match List.map get_index occ with
  | -1 :: ol -> ol = [], ol
  | 0 :: ol | ol -> ol <> [], ol in
  let max_occ = List.fold_right max occ_list 0 in
  let subst_occ =
    let occ_set = Array.make max_occ (not use_occ) in
    let _ = List.iter (fun i -> occ_set.(i - 1) <- use_occ) occ_list in
    let _ = if max_occ = 0 then skip_occ := use_occ in
    fun () -> incr nocc;
    if !nocc = max_occ then skip_occ := use_occ;
    if !nocc <= max_occ then occ_set.(!nocc - 1) else not use_occ in
  let upat_that_matched = ref None in
  let match_EQ env sigma u = 
    match u.up_k with
    | KpatLet ->
      let x, pv, t, pb = destLetIn u.up_f in
      let env' = Environ.push_rel (x, None, t) env in
      let match_let f = match kind_of_term f with
      | LetIn (_, v, _, b) -> unif_EQ env sigma pv v && unif_EQ env' sigma pb b
      | _ -> false in match_let
    | KpatFixed -> (=) u.up_f
    | KpatConst -> eq_constr u.up_f
    | _ -> unif_EQ env sigma u.up_f in
let p2t p = mkApp(p.up_f,p.up_a) in 
let source () = match upats_origin, upats with
  | None, [p] -> 
      (if fixed_upat p then str"term " else str"partial term ") ++ 
      pr_constr_pat (p2t p) ++ spc()
  | Some (dir,rule), [p] -> str"the " ++ pr_dir_side dir ++ str" of " ++ 
      pr_constr_pat rule ++ fnl() ++ ws 4 ++ pr_constr_pat (p2t p) ++ fnl()
  | Some (dir,rule), _ -> str"the " ++ pr_dir_side dir ++ str" of " ++ 
      pr_constr_pat rule ++ spc()
  | _, [] | None, _::_::_ -> anomaly "mk_pmatcher with no upats_origin" in
(fun env c h ~k -> 
  do_once upat_that_matched (fun () -> 
    try
      match_upats_FO upats env sigma0 ise c;
      match_upats_HO upats env sigma0 ise c;
      raise NoMatch
    with FoundUnif sigma_u -> sigma_u
    | NoMatch when (not raise_NoMatch) ->
        errorstrm (source ()++ str "does not match any subterm of the goal")
    | NoProgress when (not raise_NoMatch) ->
        let dir = match upats_origin with Some (d,_) -> d | _ ->
          anomaly "mk_pmatcher with no upats_origin" in      
        errorstrm (str"all matches of "++source()++
          str"are equal to the " ++ pr_dir_side (inv_dir dir))
    | NoProgress -> raise NoMatch);
  let sigma, ({up_f = pf; up_a = pa} as u) = assert_done upat_that_matched in
  if !skip_occ then (ignore(k env u.up_t u.up_t 0); c) else
  let match_EQ = match_EQ env sigma u in
  let pn = Array.length pa in
  let rec subst_loop (env,h as acc) c' = 
    if !skip_occ then c' else
    let f, a = splay_app sigma c' in
    if Array.length a >= pn && match_EQ f && unif_EQ_args env sigma pa a then
      let a1, a2 = array_chop (Array.length pa) a in
      let fa1 = mkApp (f, a1) in
      let f' = if subst_occ () then k env fa1 u.up_t h else fa1 in
      mkApp (f', array_map_left (subst_loop acc) a2)
    else
      (* TASSI: clear letin values to avoid unfolding *)
      let inc_h (n,_,ty) (env,h') = Environ.push_rel (n,None,ty) env, h' + 1 in
      let f' = map_constr_with_binders_left_to_right inc_h subst_loop acc f in
      mkApp (f', array_map_left (subst_loop acc) a) in
  subst_loop (env,h) c),
(fun () ->
  let sigma, ({up_f = pf; up_a = pa} as u) =
    match !upat_that_matched with
    | Some x -> x | None when raise_NoMatch -> raise NoMatch
    | None -> anomaly "companion function never called" in
  let p' = mkApp (pf, pa) in
  if max_occ <= !nocc then p', u.up_dir, (sigma, u.up_t)
  else errorstrm (str"Only " ++ int !nocc ++ str" < " ++ int max_occ ++
        str(plural !nocc " occurence") ++ match upats_origin with
        | None -> str" of" ++ spc() ++ pr_constr_pat p'
        | Some (dir,rule) -> str" of the " ++ pr_dir_side dir ++ fnl() ++
            ws 4 ++ pr_constr_pat p' ++ fnl () ++ 
            str"of " ++ pr_constr_pat rule))

let fake_pmatcher_end () = mkImplicit, L2R, (Evd.empty, mkImplicit)

let pf_fill_occ env concl occ sigma0 p (sigma, t) ok h =
 let ise = create_evar_defs sigma in
 let u, ise = mk_upat env sigma0 ise t ok L2R p in
 let find_U, end_U = mk_pmatcher ~raise_NoMatch:true sigma0 occ ([u], ise) in
 let concl = find_U env concl h (fun _ _ _ -> mkRel) in
 let rdx, _, (sigma, p) = end_U () in
 sigma, p, concl, rdx

let fill_occ_term env cl occ sigma0 (sigma, t) =
  try
    let sigma',t',cl,_ = pf_fill_occ env cl occ sigma0 t (sigma, t) all_ok 1 in
    if sigma' != sigma0 then error "matching impacts evars" else cl, (sigma',t') with NoMatch -> try
    let sigma', t' =
      unif_end env sigma0 (create_evar_defs sigma) t (fun _ -> true) in
    if sigma' != sigma0 then raise NoMatch else cl, (sigma', t')
  with _ ->
    errorstrm (str "partial term " ++ pr_constr_pat t
            ++ str " does not match any subterm of the goal")

let pf_fill_occ_term gl occ t =
  let sigma0 = project gl and env = pf_env gl and concl = pf_concl gl in
  let cl,(_,t) = fill_occ_term env concl occ sigma0 t in
  cl, t

(* TASSI: sound HO unification *)
let unify_HO env sigma0 t1 t2 =
  let sigma = unif_HO env sigma0 t1 t2 in
  let sigma, _ = unif_end env sigma0 sigma t2 (fun _ -> true) in
  sigma

let pf_unify_HO gl t1 t2 =
  let env, sigma0, si = pf_env gl, project gl, sig_it gl in
  let sigma = unify_HO env sigma0 t1 t2 in
  re_sig si sigma

(* TASSI: given (c : ty), generates (c ??? : ty[???/...]) with m evars *)
exception NotEnoughProducts
let saturate ?(beta=false) env sigma c ?(ty=Retyping.get_type_of env sigma c) m 
=
  let rec loop ty args sigma n = 
  if n = 0 then 
    let args = List.rev args in
     (if beta then Reductionops.whd_beta sigma else fun x -> x)
      (mkApp (c, Array.of_list (List.map snd args))), ty, args, sigma 
  else match kind_of_type ty with
  | ProdType (_, src, tgt) ->
      let sigma, x = Evarutil.new_evar (create_evar_defs sigma) env src in
      loop (subst1 x tgt) ((m - n,x) :: args) sigma (n-1)
  | CastType (t, _) -> loop t args sigma n 
  | LetInType (_, v, _, t) -> loop (subst1 v t) args sigma n
  | SortType _ -> assert false
  | AtomicType _ ->
      let ty = Reductionops.whd_betadeltaiota env sigma ty in
      match kind_of_type ty with
      | ProdType _ -> loop ty args sigma n
      | _ -> anomaly "saturate did not find enough products"
  in
   loop ty [] sigma m

let pf_saturate ?beta gl c ?ty m = 
  let env, sigma, si = pf_env gl, project gl, sig_it gl in
  let t, ty, args, sigma = saturate ?beta env sigma c ?ty m in
  t, ty, args, re_sig si sigma 

(** Rewrite redex switch *)

type ('ident, 'term) a_ssrpattern = 
  | T of 'term
  | In_T of 'term
  | X_In_T of 'ident * 'term     
  | In_X_In_T of 'ident * 'term     
  | E_In_X_In_T of 'term * 'ident * 'term     
  | E_As_X_In_T of 'term * 'ident * 'term     
        
let pr_pattern = function
  | T t -> prl_term t
  | In_T t -> str "in " ++ prl_term t
  | X_In_T (x,t) -> prl_term x ++ str " in " ++ prl_term t
  | In_X_In_T (x,t) -> str "in " ++ prl_term x ++ str " in " ++ prl_term t
  | E_In_X_In_T (e,x,t) ->
      prl_term e ++ str " in " ++ prl_term x ++ str " in " ++ prl_term t
  | E_As_X_In_T (e,x,t) ->
      prl_term e ++ str " as " ++ prl_term x ++ str " in " ++ prl_term t

let pr_pattern_w_ids = function
  | T t -> prl_term t
  | In_T t -> str "in " ++ prl_term t
  | X_In_T (x,t) -> pr_id x ++ str " in " ++ prl_term t
  | In_X_In_T (x,t) -> str "in " ++ pr_id x ++ str " in " ++ prl_term t
  | E_In_X_In_T (e,x,t) ->
      prl_term e ++ str " in " ++ pr_id x ++ str " in " ++ prl_term t
  | E_As_X_In_T (e,x,t) ->
      prl_term e ++ str " as " ++ pr_id x ++ str " in " ++ prl_term t

let pr_pattern_aux pr_constr = function
  | T t -> pr_constr t
  | In_T t -> str "in " ++ pr_constr t
  | X_In_T (x,t) -> pr_constr x ++ str " in " ++ pr_constr t
  | In_X_In_T (x,t) -> str "in " ++ pr_constr x ++ str " in " ++ pr_constr t
  | E_In_X_In_T (e,x,t) ->
      pr_constr e ++ str " in " ++ pr_constr x ++ str " in " ++ pr_constr t
  | E_As_X_In_T (e,x,t) ->
      pr_constr e ++ str " as " ++ pr_constr x ++ str " in " ++ pr_constr t
let pp_pattern (sigma, p) =
  pr_pattern_aux (fun t -> pr_constr (Reductionops.nf_evar sigma t)) p

let pr_option f = function None -> mt() | Some x -> f x
let pr_ssrpattern _ _ _ = pr_option pr_pattern
let pr_pattern_squarep = pr_option (fun r -> str "[" ++ pr_pattern r ++ str "]")
let pr_ssrpattern_squarep _ _ _ = pr_pattern_squarep
let pr_pattern_roundp = pr_option (fun r -> str "(" ++ pr_pattern r ++ str ")")
let pr_ssrpattern_roundp  _ _ _ = pr_pattern_roundp

(* type ssrpattern = (ssrtermrep, ssrtermrep) a_ssrpattern *)

let wit_ssrctxpattern, globwit_ssrctxpattern, rawwit_ssrctxpattern =
  add_genarg "ssrctxpattern" pr_pattern

ARGUMENT EXTEND ssrpattern_ne TYPED AS ssrctxpattern option PRINTED BY pr_ssrpattern
  | [ lconstr(c) ] -> [ Some (T (mk_lterm c)) ]
  | [ "in" lconstr(c) ] -> [ Some (In_T (mk_lterm c)) ]
  | [ lconstr(x) "in" lconstr(c) ] -> 
    [ Some (X_In_T (mk_lterm x, mk_lterm c)) ]
  | [ "in" lconstr(x) "in" lconstr(c) ] -> 
    [ Some (In_X_In_T (mk_lterm x, mk_lterm c)) ]
  | [ lconstr(e) "in" lconstr(x) "in" lconstr(c) ] -> 
    [ Some (E_In_X_In_T (mk_lterm e, mk_lterm x, mk_lterm c)) ]
  | [ lconstr(e) "as" lconstr(x) "in" lconstr(c) ] -> 
    [ Some (E_As_X_In_T (mk_lterm e, mk_lterm x, mk_lterm c)) ]
END

ARGUMENT EXTEND ssrpattern_squarep
TYPED AS ssrpattern_ne PRINTED BY pr_ssrpattern_squarep
  | [ "[" ssrpattern_ne(rdx) "]" ] -> [ rdx ]
  | [ ] -> [ None ]
END

ARGUMENT EXTEND ssrpattern_ne_squarep
TYPED AS ssrpattern_ne PRINTED BY pr_ssrpattern_squarep
  | [ "[" ssrpattern_ne(rdx) "]" ] -> [ rdx ]
END


let interp_pattern ist gl red redty =
  pp(lazy(str"interpreting: " ++ pr_pattern red));
  let xInT x y = X_In_T(x,y) and inXInT x y = In_X_In_T(x,y) in
  let inT x = In_T x and eInXInT e x t = E_In_X_In_T(e,x,t) in
  let eAsXInT e x t = E_As_X_In_T(e,x,t) in
  let mkG ?(k=' ') x = k,(x,None) in
  let decode t f g =
    try match (pf_intern_term ist gl t) with
    | RCast(_,RHole _,CastConv(_,RLambda(_,Name x,_,_,c))) -> f x (' ',(c,None))
    | it -> g t with _ -> g t in
  let decodeG t f g = decode (mkG t) f g in
  let bad_enc id _ = anomaly ("bad encoding for pattern " ^ id) in
  let red = match red with
    | T(k,(RCast (_,RHole _,(CastConv(_, RLambda (_,Name id,_,_,t)))),None))
        when let id = string_of_id id in let len = String.length id in
        (len > 8 && String.sub id 0 8 = "_ssrpat_") ->
        let id = string_of_id id in let len = String.length id in
        (match String.sub id 8 (len - 8), t with
        | "In", RApp(_, _, [t]) -> decodeG t xInT (fun x -> T x)
        | "In", RApp(_, _, [e; t]) -> decodeG t (eInXInT (mkG e)) (bad_enc id)
        | "In", RApp(_, _, [e; t; e_in_t]) ->
            decodeG t (eInXInT (mkG e))
              (fun _ -> decodeG e_in_t xInT (fun _ -> assert false))
        | "As", RApp(_, _, [e; t]) -> decodeG t (eAsXInT (mkG e)) (bad_enc id)
        | _ -> bad_enc id ())
    | T t -> decode t xInT (fun x -> T x)
    | In_T t -> decode t inXInT inT
    | X_In_T (e,t) -> decode t (eInXInT e) (fun x -> xInT (id_of_Cterm e) x)
    | In_X_In_T (e,t) -> inXInT (id_of_Cterm e) t
    | E_In_X_In_T (e,x,rp) -> eInXInT e (id_of_Cterm x) rp
    | E_As_X_In_T (e,x,rp) -> eAsXInT e (id_of_Cterm x) rp in
  pp(lazy(str"decoded as: " ++ pr_pattern_w_ids red));
  let red = match redty with None -> red | Some ty -> match red with
  | T t -> T (combineCG t ty (mkCCast (loc_ofCG t)) mkRCast)
  | X_In_T (x,t) ->
      let ty = pf_intern_term ist gl ty in
      E_As_X_In_T (mkG (mkRCast mkRHole ty), x, t)
  | E_In_X_In_T (e,x,t) ->
      let ty = mkG (pf_intern_term ist gl ty) in
      E_In_X_In_T (combineCG e ty (mkCCast (loc_ofCG t)) mkRCast, x, t)
  | E_As_X_In_T (e,x,t) ->
      let ty = mkG (pf_intern_term ist gl ty) in
      E_As_X_In_T (combineCG e ty (mkCCast (loc_ofCG t)) mkRCast, x, t)
  | red -> red in
  pp(lazy(str"typed as: " ++ pr_pattern_w_ids red));
  let mkXLetIn loc x (a,(g,c)) = match c with
  | Some b -> a,(g,Some (mkCLetIn loc x (CHole(loc,None)) b))
  | None -> a,(RLetIn (loc,x,(RHole (loc, BinderType x)), g), None) in
  match red with
  | T t -> let sigma, t = interp_term ist gl t in sigma, T t
  | In_T t -> let sigma, t = interp_term ist gl t in sigma, In_T t
  | X_In_T (x, rp) | In_X_In_T (x, rp) ->
    let mk x p = match red with X_In_T _ -> X_In_T(x,p) | _ -> In_X_In_T(x,p) in
    let rp = mkXLetIn dummy_loc (Name x) rp in
    let sigma, rp = interp_term ist gl rp in
    let _, h, _, rp = destLetIn rp in
    let rp = subst1 h rp in
    sigma, mk h rp
  | E_In_X_In_T(e, x, rp) | E_As_X_In_T (e, x, rp) ->
    let mk e x p =
      match red with E_In_X_In_T _ ->E_In_X_In_T(e,x,p)|_->E_As_X_In_T(e,x,p) in
    let rp = mkXLetIn dummy_loc (Name x) rp in
    let sigma, rp = interp_term ist gl rp in
    let _, h, _, rp = destLetIn rp in
    let rp = subst1 h rp in
    let sigma, e = interp_term ist (re_sig (sig_it gl) sigma) e in
    sigma, mk e h rp
;;

(* calls do_subst on every sub-term identified by (pattern,occ) *)
let eval_pattern ?raise_NoMatch env0 sigma0 concl0 pattern occ do_subst =
  let fs sigma x = Reductionops.nf_evar sigma x in
  let pop_evar sigma e p =
    let { Evd.evar_body = e_body } as e_def = Evd.find sigma e in
    let e_body = match e_body with Evar_defined c -> c
    | _ -> errorstrm (str "Matching the pattern " ++ pr_constr p ++
          str " did not instantiate ?" ++ pr_int e ++ spc () ++
          str "Does the variable bound by the \"in\" construct occur "++
          str "in the pattern?") in
    let sigma = 
      Evd.add (Evd.remove sigma e) e {e_def with Evd.evar_body = Evar_empty} in
    sigma, e_body in
  let ex_value hole =
    match kind_of_term hole with Evar (e,_) -> e | _ -> assert false in
  let mk_upat_for ?hack env sigma0 (sigma, t) ?(p=t) ok =
    let pat, sigma = mk_upat ?hack env sigma0 sigma p ok L2R (fs sigma t) in
    [pat], sigma in
  match pattern with
  | None -> do_subst env0 concl0 1
  | Some (sigma, (T rp | In_T rp)) -> 
    let rp = fs sigma rp in
    let ise = create_evar_defs sigma in
    let occ = match pattern with Some (_, T _) -> occ | _ -> [noindex] in
    let rp = mk_upat_for env0 sigma0 (ise, rp) all_ok in
    let find_T, end_T = mk_pmatcher ?raise_NoMatch sigma0 occ rp in
    let concl = find_T env0 concl0 1 (fun env _ -> do_subst env) in
    let _ = end_T () in
    concl
  | Some (sigma, (X_In_T (hole, p) | In_X_In_T (hole, p))) ->
    let p = fs sigma p in
    let occ = match pattern with Some (_, X_In_T _) -> occ | _ -> [noindex] in
    let ex = ex_value hole in
    let rp = mk_upat_for ~hack:true env0 sigma0 (sigma, p) all_ok in
    let find_T, end_T = mk_pmatcher sigma0 [noindex] rp in
    (* we start from sigma, so hole is considered a rigid head *)
    let holep = mk_upat_for env0 sigma (sigma, hole) all_ok in
    let find_X, end_X = mk_pmatcher ?raise_NoMatch sigma occ holep in
    let concl = find_T env0 concl0 1 (fun env _ c h ->
      let p_sigma = unify_HO env (create_evar_defs sigma) c p in
      let sigma, e_body = pop_evar p_sigma ex p in
      fs p_sigma (find_X env (fs sigma p) h 
        (fun env _ _ -> do_subst env e_body))) in
    let _ = end_X () in let _ = end_T () in 
    concl
  | Some (sigma, E_In_X_In_T (e, hole, p)) ->
    let p, e = fs sigma p, fs sigma e in
    let ex = ex_value hole in
    let rp = mk_upat_for ~hack:true env0 sigma0 (sigma, p) all_ok in
    let find_T, end_T = mk_pmatcher sigma0 [noindex] rp in
    let holep = mk_upat_for env0 sigma (sigma, hole) all_ok in
    let find_X, end_X = mk_pmatcher sigma [noindex] holep in
    let re = mk_upat_for env0 sigma0 (sigma, e) all_ok in
    let find_E, end_E = mk_pmatcher ?raise_NoMatch sigma0 occ re in
    let concl = find_T env0 concl0 1 (fun env _ c h ->
      let p_sigma = unify_HO env (create_evar_defs sigma) c p in
      let sigma, e_body = pop_evar p_sigma ex p in
      fs p_sigma (find_X env (fs sigma p) h (fun env _ c h ->
        find_E env e_body h (fun env _ -> do_subst env)))) in
    let _ = end_E () in let _ = end_X () in let _ = end_T () in
    concl
  | Some (sigma, E_As_X_In_T (e, hole, p)) ->
    let p, e = fs sigma p, fs sigma e in
    let ex = ex_value hole in
    let rp = 
      let e_sigma = unify_HO env0 sigma hole e in
      e_sigma, fs e_sigma p in
    let rp = mk_upat_for ~hack:true env0 sigma0 rp all_ok in
    let find_TE, end_TE = mk_pmatcher sigma0 [noindex] rp in
    let holep = mk_upat_for env0 sigma (sigma, hole) all_ok in
    let find_X, end_X = mk_pmatcher sigma occ holep in
    let concl = find_TE env0 concl0 1 (fun env _ c h ->
      let p_sigma = unify_HO env (create_evar_defs sigma) c p in
      let sigma, e_body = pop_evar p_sigma ex p in
      fs p_sigma (find_X env (fs sigma p) h (fun env _ c h ->
        let e_sigma = unify_HO env sigma e_body e in
        let e_body = fs e_sigma e in
        do_subst env e_body h))) in
    let _ = end_X () in let _ = end_TE () in
    concl
;;

(** Generalization (discharge) item *)

(* An item is a switch + term pair.                                     *)

(* type ssrgen = ssrdocc * ssrterm *)

let pr_gen (docc, dt) = pr_docc docc ++ pr_term dt

let pr_ssrgen _ _ _ = pr_gen

ARGUMENT EXTEND ssrgen TYPED AS ssrdocc * ssrpattern PRINTED BY pr_ssrgen
| [ ssrdocc(docc) ssrpattern(dt) ] -> [ docc, dt ]
| [ ssrpattern(dt) ] -> [ nodocc, dt ]
END

let has_occ ((_, occ), _) = occ <> []
let hyp_of_var v =  SsrHyp (dummy_loc, destVar v)

let interp_clr = function
| Some clr, (k, c) 
  when (k = ' '  || k = '@') && is_pf_var c -> hyp_of_var c :: clr 
| Some clr, _ -> clr
| None, _ -> []

let redex_of_pattern (sigma, p) = let e = match p with
  | In_T _ | In_X_In_T _ -> anomaly "pattern without redex"
  | T e | X_In_T (e, _) | E_As_X_In_T (e, _, _) | E_In_X_In_T (e, _, _) -> e in
  Reductionops.nf_evar sigma e

let fill_occ_pattern ?raise_NoMatch env sigma pat occ h cl =
  let find_R, conclude = let r = ref None in
    (fun env c h' -> do_once r (fun () -> c); mkRel (h'+h-1)),
    (fun _ -> if !r = None then redex_of_pattern pat else assert_done r) in
  let cl = eval_pattern ?raise_NoMatch env sigma cl (Some pat) occ find_R in
  let e = conclude cl in
  e, cl
;;

(* XXX the k of the redex should percolate out *)
let pf_interp_gen_aux ist gl to_ind ((oclr, occ), t) =
  let pat = interp_pattern ist gl (T t) None in (* UGLY API *)
  let c = redex_of_pattern pat in
  let cl, env, sigma = pf_concl gl, pf_env gl, project gl in
  let c, cl = 
    try fill_occ_pattern ~raise_NoMatch:true env sigma pat occ 1 cl
    with NoMatch -> c, cl in
  let clr = interp_clr (oclr, (fst t, c)) in
  if not(occur_existential c) then
    if fst t = '@' then 
      if not (isVar c) then errorstrm (str "@ can be used with variables only")
      else match pf_get_hyp gl (destVar c) with
      | _, None, _ -> errorstrm (str "@ can be used with let-ins only")
      | name, Some bo, ty -> true, pat, mkLetIn (Name name, bo, ty, cl), c, clr
    else false, pat, pf_mkprod gl c cl, c, clr
  else if to_ind && occ = [] then
    let nv, p = pf_abs_evars gl (fst pat, c) in
    if nv = 0 then anomaly "occur_existential but no evars" else
    false, pat, mkProd (constr_name c, pf_type_of gl p, pf_concl gl), p, clr
  else loc_error (loc_ofCG t) "generalized term didn't match"

let genclrtac cl cs clr = tclTHEN (apply_type cl cs) (cleartac clr)

let gentac ist gen gl =
  let conv, _, cl, c, clr = pf_interp_gen_aux ist gl false gen in 
  if conv then tclTHEN (convert_concl cl) (cleartac clr) gl
  else genclrtac cl [c] clr gl

let pf_interp_gen ist gl to_ind gen =
  let _, _, a, b ,c = pf_interp_gen_aux ist gl to_ind gen in a, b ,c

(** Generalization (discharge) sequence *)

(* A discharge sequence is represented as a list of up to two   *)
(* lists of d-items, plus an ident list set (the possibly empty *)
(* final clear switch). The main list is empty iff the command  *)
(* is defective, and has length two if there is a sequence of   *)
(* dependent terms (and in that case it is the first of the two *)
(* lists). Thus, the first of the two lists is never empty.     *)

(* type ssrgens = ssrgen list *)
(* type ssrdgens = ssrgens list * ssrclear *)

let gens_sep = function [], [] -> mt | _ -> spc

let pr_dgens pr_gen (gensl, clr) =
  let prgens s gens = str s ++ pr_list spc pr_gen gens in
  let prdeps deps = prgens ": " deps ++ spc () ++ str "/" in
  match gensl with
  | [deps; []] -> prdeps deps ++ pr_clear pr_spc clr
  | [deps; gens] -> prdeps deps ++ prgens " " gens ++ pr_clear spc clr
  | [gens] -> prgens ": " gens ++ pr_clear spc clr
  | _ -> pr_clear pr_spc clr

let pr_ssrdgens _ _ _ = pr_dgens pr_gen

let cons_gen gen = function
  | gens :: gensl, clr -> (gen :: gens) :: gensl, clr
  | _ -> anomaly "missing gen list"

let cons_dep (gensl, clr) =
  if List.length gensl = 1 then ([] :: gensl, clr) else
  error "multiple dependents switches '/'"

ARGUMENT EXTEND ssrdgens_tl TYPED AS ssrgen list list * ssrclear
                            PRINTED BY pr_ssrdgens
| [ "{" ne_ssrhyp_list(clr) "}" ssrpattern(dt) ssrdgens_tl(dgens) ] ->
  [ cons_gen (mkclr clr, dt) dgens ]
| [ "{" ne_ssrhyp_list(clr) "}" ] ->
  [ [[]], clr ]
| [ "{" ssrocc(occ) "}" ssrpattern(dt) ssrdgens_tl(dgens) ] ->
  [ cons_gen (mkocc occ, dt) dgens ]
| [ "/" ssrdgens_tl(dgens) ] ->
  [ cons_dep dgens ]
| [ ssrpattern(dt) ssrdgens_tl(dgens) ] ->
  [ cons_gen (nodocc, dt) dgens ]
| [ ] ->
  [ [[]], [] ]
END

ARGUMENT EXTEND ssrdgens TYPED AS ssrdgens_tl PRINTED BY pr_ssrdgens
| [ ":" ssrgen(gen) ssrdgens_tl(dgens) ] -> [ cons_gen gen dgens ]
END

let genstac (gens, clr) ist =
  tclTHENLIST (cleartac clr :: List.rev_map (gentac ist) gens)

(* Common code to handle generalization lists along with the defective case *)

let with_defective maintac deps clr ist gl =
  let top_id =
    match kind_of_type (pf_concl gl) with
    | ProdType (Name id, _, _)
      when has_discharged_tag (string_of_id id) -> id
    | _ -> top_id in
  let top_gen = mkclr clr, (' ', (mkRVar top_id, None)) in
  tclTHEN (introid top_id) (maintac deps top_gen ist) gl

let with_dgens (gensl, clr) maintac ist = match gensl with
  | [deps; []] -> with_defective maintac deps clr ist
  | [deps; gen :: gens] ->
    tclTHEN (genstac (gens, clr) ist) (maintac deps gen ist)
  | [gen :: gens] -> tclTHEN (genstac (gens, clr) ist) (maintac [] gen ist)
  | _ -> with_defective maintac [] clr ist

let with_deps deps0 maintac cl0 cs0 clr0 ist gl0 =
  let rec loop gl cl cs clr args clrs = function
  | [] ->
    let n = List.length args in
    maintac (if n > 0 then applist (to_lambda n cl, args) else cl) clrs ist gl0
  | dep :: deps ->
    let gl' = pf_image gl (genclrtac cl cs clr) in
    let cl', c', clr' = pf_interp_gen ist gl' false dep in
    loop gl' cl' [c'] clr' (c' :: args) (clr' :: clrs) deps in
  loop gl0 cl0 cs0 clr0 cs0 [clr0] (List.rev deps0)

(** Equations *)

(* argument *)

type ssreqid = ssripat option

let pr_eqid = function Some pat -> str " " ++ pr_ipat pat | None -> mt ()
let pr_ssreqid _ _ _ = pr_eqid

(* We must use primitive parsing here to avoid conflicts with the  *)
(* basic move, case, and elim tactics.                             *)
ARGUMENT EXTEND ssreqid TYPED AS ssripatrep option PRINTED BY pr_ssreqid
| [ "(**)" ] -> [ Util.anomaly "Grammar placeholder match" ]
END

let accept_ssreqid strm =
  match Stream.npeek 1 strm with
  | ["IDENT", _] -> accept_before_syms [":"] strm
  | ["", ":"] -> ()
  | ["", pat] when List.mem pat ["_"; "?"; "->"; "<-"] ->
                      accept_before_syms [":"] strm
  | _ -> raise Stream.Failure

let test_ssreqid = Gram.Entry.of_parser "test_ssreqid" accept_ssreqid

GEXTEND Gram
  GLOBAL: ssreqid;
  ssreqpat: [
    [ id = Prim.ident -> IpatId id
    | "_" -> IpatWild
    | "?" -> IpatAnon
    | occ = ssrdocc; "->" -> (match occ with
      | None, occ -> IpatRw (occ, L2R)
      | _ -> loc_error loc "Only occurrences are allowed here")
    | occ = ssrdocc; "<-" -> (match occ with
      | None, occ ->  IpatRw (occ, R2L)
      | _ -> loc_error loc "Only occurrences are allowed here")
    | "->" -> IpatRw ([noindex], L2R)
    | "<-" -> IpatRw ([noindex], R2L)
    ]];
  ssreqid: [
    [ test_ssreqid; pat = ssreqpat -> Some pat
    | test_ssreqid -> None
    ]];
END

(* creation *)

let mkEq dir cl c t n =
  let eqargs = [|t; c; c|] in eqargs.(dir_org dir) <- mkRel n;
  mkArrow (mkApp (build_coq_identity(), eqargs)) (lift 1 cl), mkRefl t c

let pushmoveeqtac cl c =
  let x, t, cl1 = destProd cl in
  let cl2, eqc = mkEq R2L cl1 c t 1 in
  apply_type (mkProd (x, t, cl2)) [c; eqc]

let pushcaseeqtac cl gl =
  let cl1, args = destApplication cl in
  let n = Array.length args in
  let dc, cl2 = decompose_lam_n n cl1 in
  let _, t = List.nth dc (n - 1) in
  let cl3, eqc = mkEq R2L cl2 args.(0) t n in
  let cl4 = mkApp (compose_lam dc (mkProt (pf_type_of gl cl) cl3), args) in
  tclTHEN (apply_type cl4 [eqc]) (convert_concl cl4) gl

let pushelimeqtac gl =
  let _, args = destApplication (pf_concl gl) in
  let x, t, _ = destLambda args.(1) in
  let cl1 = mkApp (args.(1), Array.sub args 2 (Array.length args - 2)) in
  let cl2, eqc = mkEq L2R cl1 args.(2) t 1 in
  tclTHEN (apply_type (mkProd (x, t, cl2)) [args.(2); eqc]) intro gl

(** Bookkeeping (discharge-intro) argument *)

(* Since all bookkeeping ssr commands have the same discharge-intro    *)
(* argument format we use a single grammar entry point to parse them.  *)
(* the entry point parses only non-empty arguments to avoid conflicts  *)
(* with the basic Coq tactics.                                         *)

(* type ssrarg = ssrview * (ssreqid * (ssrdgens * ssripats)) *)

let pr_ssrarg _ _ _ (view, (eqid, (dgens, ipats))) =
  let pri = pr_intros (gens_sep dgens) in
  pr_view view ++ pr_eqid eqid ++ pr_dgens pr_gen dgens ++ pri ipats

ARGUMENT EXTEND ssrarg TYPED AS ssrview * (ssreqid * (ssrdgens * ssrintros))
   PRINTED BY pr_ssrarg
| [ ssrview(view) ssreqid(eqid) ssrdgens(dgens) ssrintros(ipats) ] ->
  [ view, (eqid, (dgens, ipats)) ]
| [ ssrview(view) ssrclear(clr) ssrintros(ipats) ] ->
  [ view, (None, (([], clr), ipats)) ]
| [ ssreqid(eqid) ssrdgens(dgens) ssrintros(ipats) ] ->
  [ [], (eqid, (dgens, ipats)) ]
| [ ssrclear_ne(clr) ssrintros(ipats) ] ->
  [ [], (None, (([], clr), ipats)) ]
| [ ssrintros_ne(ipats) ] ->
  [ [], (None, (([], []), ipats)) ]
END

(** The "clear" tactic *)

(* We just add a numeric version that clears the n top assumptions. *)

let poptac ?ist n = introstac ?ist (list_tabulate (fun _ -> IpatWild) n)

TACTIC EXTEND ssrclear
  | [ "clear" natural(n) ssrltacctx(ctx) ] -> [poptac ~ist:(get_ltacctx ctx) n]
END

(** The "move" tactic *)

let rec improper_intros = function
  | IpatSimpl _ :: ipats -> improper_intros ipats
  | (IpatId _ | IpatAnon | IpatCase _ | IpatAll) :: _ -> false
  | _ -> true

let check_movearg = function
  | view, (eqid, _) when view <> [] && eqid <> None ->
    Util.error "incompatible view and equation in move tactic"
  | view, (_, (([gen :: _], _), _)) when view <> [] && has_occ gen ->
    Util.error "incompatible view and occurrence switch in move tactic"
  | _, (_, ((dgens, _), _)) when List.length dgens > 1 ->
    Util.error "dependents switch `/' in move tactic"
  | _, (eqid, (_, (ipats, _))) when eqid <> None && improper_intros ipats ->
    Util.error "no proper intro pattern for equation in move tactic"
  | arg -> arg

ARGUMENT EXTEND ssrmovearg TYPED AS ssrarg PRINTED BY pr_ssrarg
| [ ssrarg(arg) ] -> [ check_movearg arg ]
END

let viewmovetac_aux clear name_ref (_, vl as v) _ gen ist gl =
  let cl, c, clr = pf_interp_gen ist gl false gen in
  let cl, c = if vl = [] then cl, c else pf_with_view ist gl v cl c in
  let clr = if clear then clr else [] in
  name_ref := (match gen with
   | _, (_, (RRef (_, VarRef id), None)) -> id
   | _ -> top_id);
  genclrtac cl [c] clr gl

let () = move_top_with_view := 
   (fun c r v -> with_defective (viewmovetac_aux c r v) [] [])

let viewmovetac v deps gen ist gl = 
  viewmovetac_aux true (ref top_id) v deps gen ist gl

let eqmovetac _ gen ist gl =
  let cl, c, _ = pf_interp_gen ist gl false gen in pushmoveeqtac cl c gl

let movehnftac gl = match kind_of_term (pf_concl gl) with
  | Prod _ | LetIn _ -> tclIDTAC gl
  | _ -> hnf_in_concl gl

let ssrmovetac ist = function
  | _::_ as view, (_, (dgens, (ipats, _))) ->
    let dgentac = with_dgens dgens (viewmovetac (true, view)) ist in
    tclTHEN dgentac (introstac ~ist ipats)
  | _, (Some pat, (dgens, (ipats, _))) ->
    let dgentac = with_dgens dgens eqmovetac ist in
    tclTHEN dgentac (introstac ~ist (eqmoveipats pat ipats))
  | _, (_, (([gens], clr), (ipats, _))) ->
    let gentac = genstac (gens, clr) ist in
    tclTHEN gentac (introstac ~ist ipats)
  | _, (_, ((_, clr), (ipats, _))) ->
    tclTHENLIST [movehnftac; cleartac clr; introstac ~ist ipats]

let ist_of_arg  (_, (_, (_, (_, ctx)))) = get_ltacctx ctx

TACTIC EXTEND ssrmove
| [ "move" ssrmovearg(arg) ssrrpat(pat) ] ->
  [ let ist = ist_of_arg arg in
    tclTHEN (ssrmovetac ist arg) (introstac ~ist [pat]) ]
| [ "move" ssrmovearg(arg) ssrclauses(clauses) ] ->
  [ let ist = ist_of_arg arg in tclCLAUSES (ssrmovetac ist arg) clauses ]
| [ "move" ssrrpat(pat) ssrltacctx(ctx) ] ->
  [ introstac ~ist:(get_ltacctx ctx) [pat] ]
| [ "move" ] -> [ movehnftac ]
END

(* TASSI: given the type of an elimination principle, it finds the higher order
 * argument (index), it computes it's arity and the arity of the eliminator and
 * checks if the eliminator is recursive or not *)
let analyze_eliminator elimty env sigma =
  let rec loop ctx t = match kind_of_type t with
  | AtomicType (hd, args) when isRel hd -> 
    ctx, destRel hd, not (noccurn 1 t), Array.length args
  | CastType (t, _) -> loop ctx t
  | ProdType (x, ty, t) -> loop ((x,None,ty) :: ctx) t
  | LetInType (x,b,ty,t) -> loop ((x,Some b,ty) :: ctx) (subst1 b t)
  | _ ->
    let env' = Environ.push_rel_context ctx env in
    let t' = Reductionops.whd_betadeltaiota env' sigma t in
    if not (eq_constr t t') then loop ctx t' else
      errorstrm (str"The eliminator has the wrong shape."++spc()++
      str"A (applied) bound variable was expected as the conclusion of "++
      str"the eliminator's"++Pp.cut()++str"type:"++spc()++pr_constr elimty) in
  let ctx, pred_id, elim_is_dep, n_pred_args = loop [] elimty in
  let n_elim_args = rel_context_nhyps ctx in
  let is_rec_elim = 
     let count_occurn n term =
       let count = ref 0 in
       let rec occur_rec n c = match kind_of_term c with
         | Rel m -> if m = n then incr count
         | _ -> iter_constr_with_binders succ occur_rec n c
       in
       occur_rec n term; !count in
     let occurr2 n t = count_occurn n t > 1 in
     not (list_for_all_i 
       (fun i (_,rd) -> pred_id <= i || not (occurr2 (pred_id - i) rd))
       1 (assums_of_rel_context ctx))
  in
  n_elim_args - pred_id, n_elim_args, is_rec_elim, elim_is_dep, n_pred_args
  
(* TASSI: This version of unprotects inlines the unfold tactic definition, 
 * since we don't want to wipe out let-ins, and it seems there is no flag
 * to change that behaviour in the standard unfold code *)
let unprotecttac gl =
  let prot = destConst (mkSsrConst "protect_term") in
  onClause (fun idopt ->
    let hyploc = Option.map (fun id -> id, InHyp) idopt in
    reduct_option 
      (Reductionops.clos_norm_flags 
        (Closure.RedFlags.mkflags 
          [Closure.RedFlags.fBETA;
           Closure.RedFlags.fCONST prot;
           Closure.RedFlags.fIOTA]), DEFAULTcast) hyploc)
    allHypsAndConcl gl

let dependent_apply_error =
  try Util.error "Could not fill dependent hole in \"apply\"" with err -> err

(* TASSI: Sometimes Coq's apply fails. According to my experience it may be
 * related to goals that are products and with beta redexes. In that case it
 * guesses the wrong number of implicit arguments for your lemma. What follows
 * is just like apply, but with a user-provided number n of implicits.
 *
 * Refine.refine function that handles type classes and evars but fails to
 * handle "dependently typed higher order evars". 
 *
 * Refiner.refiner that does not handle metas with a non ground type but works
 * with dependently typed higher order metas. *)
let applyn ~with_evars n t gl =
  if with_evars then
    let t, sigma = if n = 0 then t, project gl else
      let t, _, _, gl = pf_saturate gl t n in (* saturate with evars *)
      t, project gl in
    pp(lazy(str"Refine.refine " ++ pr_constr t));
    Refine.refine (sigma, t) gl
  else
    let t, gl = if n = 0 then t, gl else
      let sigma, si = project gl, sig_it gl in
      let rec loop sigma bo args = function (* saturate with metas *)
        | 0 -> mkApp (t, Array.of_list (List.rev args)), re_sig si sigma 
        | n -> match kind_of_term bo with
          | Lambda (_, ty, bo) -> 
              if not (closed0 ty) then raise dependent_apply_error;
              let m = Evarutil.new_meta () in
              loop (meta_declare m ty sigma) bo ((mkMeta m)::args) (n-1)
          | _ -> assert false
      in loop sigma t [] n in
    pp(lazy(str"Refiner.refiner " ++ pr_constr t));
    Refiner.refiner (Proof_type.Prim (Proof_type.Refine t)) gl

let refine_with ?(first_goes_last=false) ?(with_evars=true) oc gl =
  let rec mkRels = function 1 -> [] | n -> mkRel n :: mkRels (n-1) in
  let n, oc = pf_abs_evars_pirrel gl oc in
  let oc = if not first_goes_last || n <= 1 then oc else
    let l, c = decompose_lam oc in
    if not (list_for_all_i (fun i (_,t) -> closedn ~-i t) (1-n) l) then oc else
    compose_lam (let xs,y = list_chop (n-1) l in y @ xs) 
      (mkApp (compose_lam l c, Array.of_list (mkRel 1 :: mkRels n)))
  in
  pp(lazy(str"after: " ++ pr_constr oc));
  try applyn ~with_evars n oc gl with _ -> raise dependent_apply_error

(** The "case" and "elim" tactic *)

(* A case without explicit dependent terms but with both a view and an    *)
(* occurrence switch and/or an equation is treated as dependent, with the *)
(* viewed term as the dependent term (the occurrence switch would be      *)
(* meaningless otherwise). When both a view and explicit dependents are   *)
(* present, it is forbidden to put a (meaningless) occurrence switch on   *)
(* the viewed term.                                                       *)

(* This is both elim and case (defaulting to the former). If ~elim is omitted
 * the standard eliminator is chosen. The code is made of 4 parts:
 * 1. find the eliminator if not given as ~elim and analyze it
 * 2. build the patterns to be matched against the conclusion, looking at
 *    (occ, c), deps and the pattern inferred from the type of the eliminator
 * 3. build the new predicate matching the patterns, and the tactic to 
 *    generalize the equality in case eqid is not None
 * 4. build the tactic handle intructions and clears as required in ipats and
 *    by eqid *)
let ssrelim ?(is_case=false) ?ist deps what ?elim eqid ipats gl =
  (* some sanity checks *)
  let oc, orig_clr, occ, c_gen = match what with
  | `EConstr(_,_,t) when isEvar t -> anomaly "elim called on a constr evar"
  | `EGen _ when ist = None -> anomaly "no ist and non simple elimination"
  | `EGen (_,(_,(_,Some (CHole _)))) when elim = None ->
       errorstrm(str"Indeterminate pattern and no eliminator")
  | `EGen ((Some clr,occ),(_,(_,Some (CHole _)|RHole _,None))) -> 
       None, clr, occ, None
  | `EGen ((None, occ),(_,(_,Some (CHole _)|RHole _,None))) -> None,[],occ,None
  | `EGen ((_, occ), p as gen) ->
       let _, c, clr = pf_interp_gen (Option.get ist) gl true gen in
       Some c, clr, occ, Some p
  | `EConstr (clr, occ, c) -> Some c, clr, occ, None in
  let orig_gl, concl, env = gl, pf_concl gl, pf_env gl in
  pp(lazy(str(if is_case then "==CASE==" else "==ELIM==")));
  (* Utils of local interest only *)
  let iD s ?t gl = let t = match t with None -> pf_concl gl | Some x -> x in
    pp(lazy(str s ++ pr_constr t)); tclIDTAC gl in
  let eq, protectC = build_coq_identity (), mkSsrConst "protect_term" in
  let fire_subst gl t = Reductionops.nf_evar (project gl) t in
  let fire_sigma sigma t = Reductionops.nf_evar sigma t in
  let is_undef_pat = function
  | sigma, T t ->  
      (match kind_of_term (fire_sigma sigma t) with Evar _ -> true | _ -> false)
  | _ -> false in
  let match_pat env p occ h cl = 
    let sigma0 = project orig_gl in
    pp(lazy(str"matching: " ++ pp_pattern p));
    let c, cl = fill_occ_pattern ~raise_NoMatch:true env sigma0 p occ h cl in
    pp(lazy(str"     got: " ++ pr_constr c));
    c, cl in
  let mkTpat gl t = (* takes a term, refreshes it and makes a T pattern *)
    let n, t = pf_abs_evars orig_gl (project gl, fire_subst gl t) in 
    let t, _, _, sigma = saturate ~beta:true env (project gl) t n in
    sigma, T t in
  let unif_redex gl (sigma, r as p) t = (* t is a hint for the redex of p *)
    let n, t = pf_abs_evars orig_gl (project gl, fire_subst gl t) in 
    let t, _, _, sigma = saturate ~beta:true env sigma t n in
    match r with
    | X_In_T (e, p) -> sigma, E_As_X_In_T (t, e, p)
    | _ -> try unify_HO env sigma t (redex_of_pattern p), r with _ -> p in
  (* finds the eliminator applies it to evars and c saturated as needed  *)
  (* obtaining "elim ??? (c ???)". pred is the higher order evar         *)
  let cty, elim, elimty, elim_args, n_elim_args, elim_is_dep, is_rec, pred, gl =
    match elim with
    | Some elim ->
      let elimty = pf_type_of gl elim in
      let pred_id, n_elim_args, is_rec, elim_is_dep, n_pred_args =
        analyze_eliminator elimty env (project gl) in
      let elim, elimty, elim_args, gl =
        pf_saturate ~beta:is_case gl elim ~ty:elimty n_elim_args in
      let pred = List.assoc pred_id elim_args in
      let elimty = Reductionops.whd_betadeltaiota env (project gl) elimty in
      None, elim, elimty, elim_args, n_elim_args, elim_is_dep, is_rec, pred, gl
    | None ->
      let c = Option.get oc in let c_ty = pf_type_of gl c in
      let (kn, i) as ind, unfolded_c_ty = pf_reduce_to_quantified_ind gl c_ty in
      let sort = elimination_sort_of_goal gl in
      let elim = if not is_case then Indrec.lookup_eliminator ind sort
        else pf_apply Indrec.build_case_analysis_scheme gl ind true sort in
      let elimty = pf_type_of gl elim in
      let pred_id,n_elim_args,is_rec,elim_is_dep,n_pred_args =
        analyze_eliminator elimty env (project gl) in
      let rctx = fst (decompose_prod_assum unfolded_c_ty) in
      let n_c_args = rel_context_length rctx in
      let c, c_ty, t_args, gl = pf_saturate gl c ~ty:c_ty n_c_args in
      let elim, elimty, elim_args, gl =
        pf_saturate ~beta:is_case gl elim ~ty:elimty n_elim_args in
      let pred = List.assoc pred_id elim_args in
      let pc = match n_c_args, c_gen with
        | 0, Some p -> interp_pattern (Option.get ist) orig_gl (T p) None 
        | _ -> mkTpat gl c in
      let cty = Some (c, c_ty, pc) in
      let elimty = Reductionops.whd_betadeltaiota env (project gl) elimty in
      cty, elim, elimty, elim_args, n_elim_args, elim_is_dep, is_rec, pred, gl
  in
  pp(lazy(str"elim= "++ pr_constr_pat elim));
  pp(lazy(str"elimty= "++ pr_constr elimty));
  let inf_deps_r = match kind_of_type elimty with
    | AtomicType (_, args) -> List.rev (Array.to_list args)
    | _ -> assert false in
  let saturate_until gl c c_ty f =
    let rec loop n = try
      let c, c_ty, _, gl = pf_saturate gl c ~ty:c_ty n in
      let gl' = f c c_ty gl in
      Some (c, c_ty, gl, gl')
    with NotEnoughProducts -> None | _ -> loop (n+1) in loop 0 in
  let elim_is_dep, gl = match cty with
    | None -> true, gl
    | Some (c, c_ty, _) ->
    let res = 
      if elim_is_dep then None else
      let arg = List.assoc (n_elim_args - 1) elim_args in
      let arg_ty = pf_type_of gl arg in
      match saturate_until gl c c_ty (fun c c_ty gl ->
        pf_unify_HO (pf_unify_HO gl c_ty arg_ty) arg c) with
      | Some (c, _, _, gl) -> Some (false, gl)
      | None -> None in
    match res with
    | Some x -> x
    | None ->
      let inf_arg = List.hd inf_deps_r in
      let inf_arg_ty = pf_type_of gl inf_arg in
      match saturate_until gl c c_ty (fun _ c_ty gl ->
              pf_unify_HO gl c_ty inf_arg_ty) with
      | Some (c, _, _,gl) -> true, gl
      | None -> errorstrm (str"Unable to apply the eliminator to the term"++
      spc()++pr_constr c++spc()++str"or to unify it's type with"++
      pr_constr inf_arg_ty) in
  pp(lazy(str"elim_is_dep= " ++ bool elim_is_dep));
  let predty = pf_type_of gl pred in
  (* Patterns for the inductive types indexes to be bound in pred are computed
   * looking at the ones provided by the user and the inferred ones looking at
   * the type of the elimination principle *)
  let pp_pat (_,p,_,_) = pp_pattern p in
  let pp_inf_pat gl (_,_,t,_) = pr_constr_pat (fire_subst gl t) in
  let patterns, clr, gl =
    let rec loop patterns clr i = function
      | [],[] -> patterns, clr, gl
      | ((oclr, occ), (k ,_ as t)):: deps, inf_t :: inf_deps ->
          let ist = match ist with Some x -> x | None -> assert false in
          let p = interp_pattern ist orig_gl (T t) None in
          let clr_t = interp_clr (oclr, (k, redex_of_pattern p)) in
          (* if we are the index for the equation we do not clear *)
          let clr_t = if deps = [] && eqid <> None then [] else clr_t in
          let p = if is_undef_pat p then mkTpat gl inf_t else p in
          loop (patterns @ [i, p, inf_t, occ]) 
            (clr_t @ clr) (i+1) (deps, inf_deps)
      | [], c :: inf_deps -> 
          pp(lazy(str"adding inferred pattern " ++ pr_constr_pat c));
          loop (patterns @ [i, mkTpat gl c, c, [noindex]]) 
            clr (i+1) ([], inf_deps)
      | _::_, [] -> errorstrm (str "Too many dependent abstractions") in
    let deps, head_p, inf_deps_r = match what, elim_is_dep, cty with
    | `EConstr _, _, None -> anomaly "Simple welim with no term"
    | _, false, _ -> deps, [], inf_deps_r
    | `EGen gen, true, None -> deps @ [gen], [], inf_deps_r
    | _, true, Some (c, _, pc) ->
         let occ = if occ = [] then [noindex] else occ in
         let inf_p, inf_deps_r = List.hd inf_deps_r, List.tl inf_deps_r in
         deps, [1, pc, inf_p, occ], inf_deps_r in
    let patterns, clr, gl = 
      loop [] orig_clr (List.length head_p+1) (List.rev deps, inf_deps_r) in
    head_p @ patterns, Util.list_uniquize clr, gl
  in
  pp(lazy(pp_concat (str"patterns=") (List.map pp_pat patterns)));
  pp(lazy(pp_concat (str"inf. patterns=") (List.map (pp_inf_pat gl) patterns)));
  (* Predicate generation, and (if necessary) tactic to generalize the
   * equation asked by the user *)
  let elim_pred, gen_eq_tac, clr, gl = 
    let error gl t inf_t = errorstrm (str"The given pattern matches the term"++
      spc()++pp_term gl t++spc()++str"while the inferred pattern"++
      spc()++pr_constr_pat (fire_subst gl inf_t)++spc()++ str"doesn't") in
    let match_or_postpone (cl, gl, post) (h, p, inf_t, occ) =
      let p = unif_redex gl p inf_t in
      if is_undef_pat p then
        let () = pp(lazy(str"postponing " ++ pp_pattern p)) in
        cl, gl, post @ [h, p, inf_t, occ]
      else try
        let c, cl =  match_pat env p occ h cl in
        let gl = try pf_unify_HO gl inf_t c with _ -> error gl c inf_t in
        cl, gl, post
      with 
      | NoMatch | NoProgress ->
          let e = redex_of_pattern p in
          let n, e =  pf_abs_evars gl (fst p, e) in
          let e, _, _, gl = pf_saturate ~beta:true gl e n in 
          let gl = try pf_unify_HO gl inf_t e with _ -> error gl e inf_t in
          cl, gl, post
    in        
    let rec match_all concl gl patterns =
      let concl, gl, postponed = 
        List.fold_left match_or_postpone (concl, gl, []) patterns in
      if postponed = [] then concl, gl
      else if List.length postponed = List.length patterns then
        errorstrm (str "Some patterns are undefined even after all"++spc()++
          str"the defined ones matched")
      else match_all concl gl postponed in
    let concl, gl = match_all concl gl patterns in
    let pred_rctx, _ = decompose_prod_assum (fire_subst gl predty) in
    let concl, gen_eq_tac, clr = match eqid with 
    | Some (IpatId _) when not is_rec -> 
        let k = List.length deps in
        let c = fire_subst gl (List.assoc (n_elim_args - k - 1) elim_args) in
        let t = pf_type_of gl c in
        let gen_eq_tac =
          let refl = mkApp (eq, [|t; c; c|]) in
          let new_concl = mkArrow refl (lift 1 (pf_concl orig_gl)) in 
          let new_concl = fire_subst gl new_concl in
          let erefl = fire_subst gl (mkRefl t c) in
          apply_type new_concl [erefl] in
        let rel = k + if elim_is_dep then 1 else 0 in
        let src = mkProt mkImplicit (mkApp (eq,[|t; c; mkRel rel|])) in
        let concl = mkArrow src (lift 1 concl) in
        let clr = if deps <> [] then clr else [] in
        concl, gen_eq_tac, clr
    | _ -> concl, tclIDTAC, clr in
    let mk_lam t r = mkLambda_or_LetIn r t in
    let concl = List.fold_left mk_lam concl pred_rctx in
    let concl = 
      if eqid <> None && is_rec then mkProt (pf_type_of gl concl) concl 
      else concl in
    concl, gen_eq_tac, clr, gl in
  pp(lazy(str"elim_pred=" ++ pp_term gl elim_pred));
  let pty = Typing.type_of env (project gl) elim_pred in
  pp(lazy(str"elim_pred_ty=" ++ pp_term gl pty));
  let gl = pf_unify_HO gl pred elim_pred in
  (* check that the patterns do not contain non instantiated dependent metas *)
  let () = 
    let evars_of_term = Evarutil.evars_of_term in
    let patterns = List.map (fun (_,_,t,_) -> fire_subst gl t) patterns in
    let patterns_ev = List.map evars_of_term patterns in 
    let ev = List.fold_left Intset.union Intset.empty patterns_ev in
    let ty_ev = Intset.fold (fun i e ->
         let ex = Evd.existential_of_int i in  
         let i_ty = Evd.evar_concl (Evd.find (project gl) ex) in
         Intset.union e (evars_of_term i_ty))
      ev Intset.empty in
    let inter = Intset.inter ev ty_ev in
    if not (Intset.is_empty inter) then begin
      let i = Intset.choose inter in
      let pat = List.find (fun t -> Intset.mem i (evars_of_term t)) patterns in
      errorstrm(str"Pattern"++spc()++pr_constr_pat pat++spc()++
        str"was not completely instantiated and one of its variables"++spc()++
        str"occurs in the type of another non instantieted pattern variable");
    end
  in
  (* the elim tactic, with the eliminator and the predicated we computed *)
  let elim = project gl, fire_subst gl elim in 
  let elim_tac gl = 
    tclTHENLIST [refine_with ~with_evars:false elim; cleartac clr] gl in
  (* handling of following intro patterns and equation introduction if any *)
  let elim_intro_tac gl = 
    let intro_eq = 
      match eqid with 
      | Some (IpatId ipat) when not is_rec -> 
          let rec intro_eq gl = match kind_of_type (pf_concl gl) with
          | ProdType (_, src, tgt) -> 
             (match kind_of_type src with
             | AtomicType (hd, _) when eq_constr hd protectC -> 
                tclTHENLIST [unprotecttac; introid ipat] gl
             | _ -> tclTHENLIST [ iD "IA"; introstac [IpatAnon]; intro_eq] gl)
          |_ -> errorstrm (str "Too many names in intro pattern") in
          intro_eq
      | Some (IpatId ipat) -> 
        let name gl = mk_anon_id "K" gl in
        let intro_lhs gl = 
          let elim_name = match orig_clr, what with
            | [SsrHyp(_, x)], _ -> x
            | _, `EConstr(_,_,t) when isVar t -> destVar t
            | _ -> name gl in
          if is_name_in_ipats elim_name ipats then introid (name gl) gl
          else introid elim_name gl
        in
        let rec gen_eq_tac gl =
          let concl = pf_concl gl in
          let ctx, last = decompose_prod_assum concl in
          let args = match kind_of_type last with
          | AtomicType (hd, args) -> assert(eq_constr hd protectC); args
          | _ -> assert false in
          let case = args.(Array.length args-1) in
          if not(closed0 case) then tclTHEN (introstac [IpatAnon]) gen_eq_tac gl
          else
          let case_ty = pf_type_of gl case in 
          let refl = mkApp (eq, [|lift 1 case_ty; mkRel 1; lift 1 case|]) in
          let new_concl = fire_subst gl
            (mkProd (Name (name gl), case_ty, mkArrow refl (lift 2 concl))) in 
          let erefl = fire_subst gl (mkRefl case_ty case) in
          apply_type new_concl [case;erefl] gl in
        tclTHENLIST [gen_eq_tac; intro_lhs; introid ipat]
      | _ -> tclIDTAC in
    let unprot = if eqid <> None && is_rec then unprotecttac else tclIDTAC in
    tclEQINTROS ?ist elim_tac (tclTHENLIST [intro_eq; unprot]) ipats gl
  in
  tclTHENLIST [gen_eq_tac; elim_intro_tac] orig_gl
;;

let simplest_newelim x = ssrelim ~is_case:false [] (`EConstr ([],[],x)) None []
let simplest_newcase x = ssrelim ~is_case:true [] (`EConstr ([],[],x)) None []
let _ = simplest_newcase_ref := simplest_newcase

let check_casearg = function
| view, (_, (([_; gen :: _], _), _)) when view <> [] && has_occ gen ->
  Util.error "incompatible view and occurrence switch in dependent case tactic"
| arg -> arg

ARGUMENT EXTEND ssrcasearg TYPED AS ssrarg PRINTED BY pr_ssrarg
| [ ssrarg(arg) ] -> [ check_casearg arg ]
END

let ssrcasetac (view, (eqid, (dgens, (ipats, ctx)))) =
  let ist = get_ltacctx ctx in
  let ndefectcasetac view eqid ipats deps ((_, occ), _ as gen) ist gl =
    let simple = (eqid = None && deps = [] && occ = []) in
    let cl, c, clr = pf_interp_gen ist gl true gen in
    let vc =
      if view = [] then c else snd(pf_with_view ist gl (false, view) cl c) in
    if simple && is_injection_case vc gl then
      tclTHENLIST [perform_injection vc; cleartac clr; introstac ~ist ipats] gl
    else 
      (* macro for "case/v E: x" ---> "case E: x / (v x)" *)
      let deps, clr, occ = 
        if view <> [] && eqid <> None && deps = [] then [gen], [], []
        else deps, clr, occ in
      ssrelim ~is_case:true ~ist deps (`EConstr (clr,occ, vc)) eqid ipats gl
  in
  with_dgens dgens (ndefectcasetac view eqid ipats) ist

TACTIC EXTEND ssrcase
| [ "case" ssrcasearg(arg) ssrclauses(clauses) ] ->
  [ tclCLAUSES (ssrcasetac arg) clauses ]
| [ "case" ] -> [ with_top ssrscasetac ]
END

(** The "elim" tactic *)

(* Elim views are elimination lemmas, so the eliminated term is not addded *)
(* to the dependent terms as for "case", unless it actually occurs in the  *)
(* goal, the "all occurrences" {+} switch is used, or the equation switch  *)
(* is used and there are no dependents.                                    *)

let ssrelimtac (view, (eqid, (dgens, (ipats, ctx)))) =
  let ist = get_ltacctx ctx in
  let ndefectelimtac view eqid ipats deps gen ist gl =
    let elim = match view with [v] -> Some (force_term ist gl v) | _ -> None in
    ssrelim ~ist deps (`EGen gen) ?elim eqid ipats gl
  in
  with_dgens dgens (ndefectelimtac view eqid ipats) ist 

TACTIC EXTEND ssrelim
| [ "elim" ssrarg(arg) ssrclauses(clauses) ] ->
  [ tclCLAUSES (ssrelimtac arg) clauses ]
| [ "elim" ] -> [ with_top simplest_newelim ]
END

(** 6. Backward chaining tactics: apply, exact, congr. *)

(** The "apply" tactic *)

let pr_agen (docc, dt) = pr_docc docc ++ pr_term dt
let pr_ssragen _ _ _ = pr_agen
let pr_ssragens _ _ _ = pr_dgens pr_agen

ARGUMENT EXTEND ssragen TYPED AS ssrdocc * ssrterm PRINTED BY pr_ssragen
| [ "{" ne_ssrhyp_list(clr) "}" ssrterm(dt) ] -> [ mkclr clr, dt ]
| [ ssrterm(dt) ] -> [ nodocc, dt ]
END

ARGUMENT EXTEND ssragens TYPED AS ssragen list list * ssrclear 
PRINTED BY pr_ssragens
| [ "{" ne_ssrhyp_list(clr) "}" ssrterm(dt) ssragens(agens) ] ->
  [ cons_gen (mkclr clr, dt) agens ]
| [ "{" ne_ssrhyp_list(clr) "}" ] -> [ [[]], clr]
| [ ssrterm(dt) ssragens(agens) ] ->
  [ cons_gen (nodocc, dt) agens ]
| [ ] -> [ [[]], [] ]
END

let mk_applyarg views agens intros = views, (None, (agens, intros))

let pr_ssraarg _ _ _ (view, (eqid, (dgens, ipats))) =
  let pri = pr_intros (gens_sep dgens) in
  pr_view view ++ pr_eqid eqid ++ pr_dgens pr_agen dgens ++ pri ipats

ARGUMENT EXTEND ssrapplyarg 
TYPED AS ssrview * (ssreqid * (ssragens * ssrintros))
PRINTED BY pr_ssraarg
| [ ":" ssragen(gen) ssragens(dgens) ssrintros(intros) ] ->
  [ mk_applyarg [] (cons_gen gen dgens) intros ]
| [ ssrclear_ne(clr) ssrintros(intros) ] ->
  [ mk_applyarg [] ([], clr) intros ]
| [ ssrintros_ne(intros) ] ->
  [ mk_applyarg [] ([], []) intros ]
| [ ssrview(view) ":" ssragen(gen) ssragens(dgens) ssrintros(intros) ] ->
  [ mk_applyarg view (cons_gen gen dgens) intros ]
| [ ssrview(view) ssrclear(clr) ssrintros(intros) ] ->
  [ mk_applyarg view ([], clr) intros ]
END

let interp_agen ist gl ((goclr, _), (k, gc)) (clr, rcs) =
  let rc = glob_constr ist (project gl) (pf_env gl) gc in
  let rcs' = rc :: rcs in
  match goclr with
  | None -> clr, rcs'
  | Some ghyps ->
    let clr' = interp_hyps ist gl ghyps @ clr in
    if k <> ' ' then clr', rcs' else
    match rc with
    | RVar (loc, id) when not_section_id id -> SsrHyp (loc, id) :: clr', rcs'
    | RRef (loc, VarRef id) when not_section_id id ->
        SsrHyp (loc, id) :: clr', rcs'
    | _ -> clr', rcs'

let interp_agens ist gl gagens =
  match List.fold_right (interp_agen ist gl) gagens ([], []) with
  | clr, rlemma :: args ->
    let n = interp_nbargs ist gl rlemma - List.length args in
    let rec loop i =
      if i > n then
         errorstrm (str "Cannot apply lemma " ++ pf_pr_rawconstr gl rlemma)
      else
        try interp_refine ist gl (mkRApp rlemma (mkRHoles i @ args))
        with _ -> loop (i + 1) in
    clr, loop 0
  | _ -> assert false

let apply_rconstr ?ist t gl =
  let n = match ist, t with
    | None, (RVar (_, id) | RRef (_, VarRef id)) -> pf_nbargs gl (mkVar id)
    | Some ist, _ -> interp_nbargs ist gl t
    | _ -> anomaly "apply_rconstr without ist and not RVar" in
  let mkRlemma i = mkRApp t (mkRHoles i) in
  let cl = pf_concl gl in
  let rec loop i =
    if i > n then errorstrm (str"Cannot apply lemma "++pf_pr_rawconstr gl t)
    else try pf_match gl (mkRlemma i) cl with _ -> loop (i + 1) in
  refine_with (loop 0) gl

let mkRAppView ist gl rv gv =
  let nb_view_imps = interp_view_nbimps ist gl rv in
  mkRApp rv (mkRHoles (abs nb_view_imps))

let refine_interp_apply_view i ist gl gv =
  let pair i = List.map (fun x -> i, x) in
  let rv = pf_intern_term ist gl gv in
  let v = mkRAppView ist gl rv gv in
  let interp_with (i, hint) =
    interp_refine ist gl (mkRApp hint (v :: mkRHoles i)) in
  let rec loop = function
  | [] -> (try apply_rconstr ~ist rv gl with _ -> view_error "apply" gv)
  | h :: hs -> (try refine_with (interp_with h) gl with _ -> loop hs) in
  loop (pair i viewtab.(i) @ if i = 2 then pair 1 viewtab.(1) else [])

let apply_top_tac gl =
  tclTHENLIST [introid top_id; apply_rconstr (mkRVar top_id); clear [top_id]] gl

let inner_ssrapplytac gviews ggenl gclr ist gl =
 let clr = interp_hyps ist gl gclr in
 let vtac gv i gl' = refine_interp_apply_view i ist gl' gv in
 let ggenl, tclGENTAC =
   if gviews <> [] && ggenl <> [] then 
     [], tclTHEN (genstac (List.hd ggenl,[]) ist)
   else ggenl, tclTHEN tclIDTAC in
 tclGENTAC (fun gl ->
  match gviews, ggenl with
  | v :: tl, [] ->
    let dbl = if List.length tl = 1 then 2 else 1 in
    tclTHEN
      (List.fold_left (fun acc v -> tclTHENLAST acc (vtac v dbl)) (vtac v 1) tl)
      (cleartac clr) gl
  | [], [agens] ->
    let clr', lemma = interp_agens ist gl agens in
    tclTHENLIST [cleartac clr; refine_with lemma; cleartac clr'] gl
  | _, _ -> tclTHEN apply_top_tac (cleartac clr) gl) gl

let ssrapplytac (views, (_, ((gens, clr), intros))) =
  tclINTROS (inner_ssrapplytac views gens clr) intros

TACTIC EXTEND ssrapply
| [ "apply" ssrapplyarg(arg) ] -> [ ssrapplytac arg ]
| [ "apply" ] -> [ apply_top_tac ]
END

(** The "exact" tactic *)

let mk_exactarg views dgens = mk_applyarg views dgens ([], rawltacctx)

ARGUMENT EXTEND ssrexactarg TYPED AS ssrapplyarg PRINTED BY pr_ssraarg
| [ ":" ssragen(gen) ssragens(dgens) ] ->
  [ mk_exactarg [] (cons_gen gen dgens) ]
| [ ssrview(view) ssrclear(clr) ] ->
  [ mk_exactarg view ([], clr) ]
| [ ssrclear_ne(clr) ] ->
  [ mk_exactarg [] ([], clr) ]
END

let vmexacttac pf gl = exact_no_check (mkCast (pf, VMcast, pf_concl gl)) gl

TACTIC EXTEND ssrexact
| [ "exact" ssrexactarg(arg) ] -> [ tclBY (ssrapplytac arg) ]
| [ "exact" ] -> [ tclORELSE donetac (tclBY apply_top_tac) ]
| [ "exact" "<:" lconstr(pf) ] -> [ vmexacttac pf ]
END

(** The "congr" tactic *)

type ssrcongrarg = open_constr * (int * constr)

let pr_ssrcongrarg _ _ _ (_, ((n, f), dgens)) =
  (if n <= 0 then mt () else str " " ++ pr_int n) ++
  str " " ++ pr_term f ++ pr_dgens pr_gen dgens

ARGUMENT EXTEND ssrcongrarg TYPED AS ssrltacctx * ((int * ssrterm) * ssrdgens)
  PRINTED BY pr_ssrcongrarg
| [ natural(n) constr(c) ssrdgens(dgens) ] ->
  [ rawltacctx, ((n, mk_term ' ' c), dgens) ]
| [ natural(n) constr(c) ] ->
  [ rawltacctx, ((n, mk_term ' ' c),([[]],[])) ]
| [ constr(c) ssrdgens(dgens) ] -> [ rawltacctx, ((0, mk_term ' ' c), dgens) ]
| [ constr(c) ] -> [ rawltacctx, ((0, mk_term ' ' c), ([[]],[])) ]
END

let rec mkRnat n =
  if n <= 0 then RRef (dummy_loc, glob_O) else
  mkRApp (RRef (dummy_loc, glob_S)) [mkRnat (n - 1)]

let interp_congrarg_at ist gl n rf ty m =
  pp(lazy(str"===interp_congrarg_at==="));
  let congrn = mkSsrRRef "nary_congruence" in
  let args1 = mkRnat n :: mkRHoles n @ [ty] in
  let args2 = mkRHoles (3 * n) in
  let rec loop i =
    if i + n > m then None else
    try
      let rt = mkRApp congrn (args1 @  mkRApp rf (mkRHoles i) :: args2) in
      pp(lazy(str"ty=" ++ pr_rawconstr ty));
      pp(lazy(str"rf=" ++ pr_rawconstr rf));
      pp(lazy(str"rt=" ++ pr_rawconstr rt));
      Some (interp_refine ist gl rt)
    with _ -> loop (i + 1) in
  loop 0

let pattern_id = mk_internal_id "pattern value"

let congrtac ((n, t), ty) ist gl =
  pp(lazy(str"===congr==="));
  pp(lazy(str"concl=" ++ pr_constr (pf_concl gl)));
  let _, f = pf_abs_evars gl (interp_term ist gl t) in
  let ist' = {ist with lfun = [pattern_id, VConstr ([],f)]} in
  let rf = mkRltacVar pattern_id in
  let m = pf_nbargs gl f in
  let cf = if n > 0 then
    match interp_congrarg_at ist' gl n rf ty m with
    | Some cf -> cf
    | None -> errorstrm (str "No " ++ pr_int n ++ str "-congruence with "
                         ++ pr_term t)
    else let rec loop i =
      if i > m then errorstrm (str "No congruence with " ++ pr_term t)
      else match interp_congrarg_at ist' gl i rf ty m with
      | Some cf -> cf
      | None -> loop (i + 1) in
      loop 1 in
  tclTHEN (refine_with cf) (tclTRY reflexivity) gl

let newssrcongrtac arg ist gl =
  pp(lazy(str"===newcongr==="));
  pp(lazy(str"concl=" ++ pr_constr (pf_concl gl)));
  (* utils *)
  let fs gl t = Reductionops.nf_evar (project gl) t in
  let tclMATCH_GOAL (c, gl_c) proj t_ok t_fail gl =
    match try Some (pf_unify_HO gl_c (pf_concl gl) c) with _ -> None with  
    | Some gl_c -> tclTHEN (convert_concl (fs gl_c c)) (t_ok (proj gl_c)) gl
    | None -> t_fail () gl in 
  let mk_evar gl ty = 
    let env, sigma, si = pf_env gl, project gl, sig_it gl in
    let sigma, x = Evarutil.new_evar (create_evar_defs sigma) env ty in
    x, re_sig si sigma in
  let ssr_congr lr = mkApp (mkSsrConst "ssr_congr_arrow",lr) in
  (* here thw two cases: simple equality or arrow *)
  let equality, _, eq_args, gl' = pf_saturate gl (build_coq_eq ()) 3 in
  let identity, _, identity_args, gl2 = pf_saturate gl (build_coq_identity ()) 3 in
  tclMATCH_GOAL (equality, gl') (fun gl' -> fs gl' (List.assoc 0 eq_args))
  (fun ty -> congrtac (arg, Detyping.detype false [] [] ty) ist)
  (fun () ->
    tclMATCH_GOAL (identity, gl2) (fun gl2 -> fs gl2 (List.assoc 0 identity_args))
	(fun ty -> congrtac (arg, Detyping.detype false [] [] ty) ist)
	(fun () ->
	  let lhs, gl' = mk_evar gl mkImplicit in let rhs, gl' = mk_evar gl' mkImplicit in
        let arrow = mkArrow lhs (lift 1 rhs) in
	  tclMATCH_GOAL (arrow, gl') (fun gl' -> [|fs gl' lhs;fs gl' rhs|])
	    (fun lr -> tclTHEN (apply (ssr_congr lr)) (congrtac (arg, mkRType) ist))
	    (fun _ _ -> errorstrm (str"Conclusion is not an equality nor an arrow"))))
    gl
;;

TACTIC EXTEND ssrcongr
| [ "congr" ssrcongrarg(arg) ] ->
[ let ctx, (arg, dgens) = arg in
  let ist = get_ltacctx ctx in
  match dgens with
  | [gens], clr -> tclTHEN (genstac (gens,clr) ist) (newssrcongrtac arg ist)
  | _ -> errorstrm (str"Dependent family abstractions not allowed in congr")]
END

(** 7. Rewriting tactics (rewrite, unlock) *)

(** Coq rewrite compatibility flag *)

let ssr_strict_match = ref false

let _ =
  Goptions.declare_bool_option 
    { Goptions.optsync  = true;
      Goptions.optname  = "strict redex matching";
      Goptions.optkey   = ["Match"; "Strict"];
      Goptions.optread  = (fun () -> !ssr_strict_match);
      Goptions.optwrite = (fun b -> ssr_strict_match := b) }

(** Rewrite multiplier *)

type ssrmult = int * ssrmmod

let notimes = 0
let nomult = 1, Once

let pr_mult (n, m) =
  if n > 0 && m <> Once then pr_int n ++ pr_mmod m else pr_mmod m

let pr_ssrmult _ _ _ = pr_mult

ARGUMENT EXTEND ssrmult_ne TYPED AS int * ssrmmod PRINTED BY pr_ssrmult
  | [ natural(n) ssrmmod(m) ] -> [ check_index loc n, m ]
  | [ ssrmmod(m) ]            -> [ notimes, m ]
END

ARGUMENT EXTEND ssrmult TYPED AS ssrmult_ne PRINTED BY pr_ssrmult
  | [ ssrmult_ne(m) ] -> [ m ]
  | [ ] -> [ nomult ]
END

(** Rewrite clear/occ switches *)

let pr_rwocc = function
  | None, [] -> mt ()
  | None, occ -> pr_occ occ
  | Some clr,  _ ->  pr_clear_ne clr

let pr_ssrrwocc _ _ _ = pr_rwocc

ARGUMENT EXTEND ssrrwocc TYPED AS ssrdocc PRINTED BY pr_ssrrwocc
| [ "{" ssrhyp_list(clr) "}" ] -> [ mkclr clr ]
| [ "{" ssrocc(occ) "}" ] -> [ mkocc occ ]
| [ ] -> [ noclr ]
END

(** Rewrite rules *)

type ssrwkind = RWred of ssrsimpl | RWdef | RWeq
(* type ssrrule = ssrwkind * ssrterm *)

let pr_rwkind = function
  | RWred s -> pr_simpl s
  | RWdef -> str "/"
  | RWeq -> mt ()

let wit_ssrrwkind, globwit_ssrrwkind, rawwit_ssrrwkind =
  add_genarg "ssrrwkind" pr_rwkind

let pr_rule = function
  | RWred s, _ -> pr_simpl s
  | RWdef, r-> str "/" ++ pr_term r
  | RWeq, r -> pr_term r

let pr_ssrrule _ _ _ = pr_rule

let noruleterm loc = mk_term ' ' (mkCProp loc)

ARGUMENT EXTEND ssrrule_ne TYPED AS ssrrwkind * ssrterm PRINTED BY pr_ssrrule
  | [ ssrsimpl_ne(s) ] -> [ RWred s, noruleterm loc ]
  | [ "/" ssrterm(t) ] -> [ RWdef, t ] 
  | [ ssrterm(t) ] -> [ RWeq, t ] 
END

ARGUMENT EXTEND ssrrule TYPED AS ssrrule_ne PRINTED BY pr_ssrrule
  | [ ssrrule_ne(r) ] -> [ r ]
  | [ ] -> [ RWred Nop, noruleterm loc ]
END

(** Rewrite arguments *)

(* type ssrrwarg = (ssrdir * ssrmult) * ((ssrdocc * ssrpattern) * ssrrule) *)

let pr_rwarg ((d, m), ((docc, rx), r)) =
  pr_rwdir d ++ pr_mult m ++ pr_rwocc docc ++ pr_pattern_squarep rx ++ pr_rule r

let pr_ssrrwarg _ _ _ = pr_rwarg

let mk_rwarg (d, (n, _ as m)) ((clr, occ as docc), rx) (rt, _ as r) =   
 if rt <> RWeq then begin
   if rt = RWred Nop && not (m = nomult && occ = [] && rx = None)
                     && (clr = None || clr = Some []) then
     anomaly "Improper rewrite clear switch";
   if d = R2L && rt <> RWdef then
     error "Right-to-left switch on simplification";
   if n <> 1 && rt = RWred Cut then
     error "Bad or useless multiplier";
   if occ <> [] && rx = None && rt <> RWdef then
     error "Missing redex for simplification occurrence"
 end; (d, m), ((docc, rx), r)

let norwmult = L2R, nomult
let norwocc = noclr, None

(*
let pattern_ident = Prim.pattern_ident in
GEXTEND Gram
GLOBAL: pattern_ident;
pattern_ident: 
[[c = pattern_ident -> (CRef (Ident (loc,c)), NoBindings)]];
END
*)


ARGUMENT EXTEND ssrrwarg
  TYPED AS (ssrdir * ssrmult) * ((ssrdocc * ssrctxpattern option) * ssrrule)
  PRINTED BY pr_ssrrwarg
  | [ "-" ssrmult(m) ssrrwocc(docc) ssrpattern_squarep(rx) ssrrule_ne(r) ] ->
    [ mk_rwarg (R2L, m) (docc, rx) r ]
  | [ "-/" ssrterm(t) ] ->     (* just in case '-/' should become a token *)
    [ mk_rwarg (R2L, nomult) norwocc (RWdef, t) ]
  | [ ssrmult_ne(m) ssrrwocc(docc) ssrpattern_squarep(rx) ssrrule_ne(r) ] ->
    [ mk_rwarg (L2R, m) (docc, rx) r ]
  | [ "{" ne_ssrhyp_list(clr) "}" ssrpattern_ne_squarep(rx) ssrrule_ne(r) ] ->
    [ mk_rwarg norwmult (mkclr clr, rx) r ]
  | [ "{" ne_ssrhyp_list(clr) "}" ssrrule(r) ] ->
    [ mk_rwarg norwmult (mkclr clr, None) r ]
  | [ "{" ssrocc(occ) "}" ssrpattern_squarep(rx) ssrrule_ne(r) ] ->
    [ mk_rwarg norwmult (mkocc occ, rx) r ]
  | [ "{" "}" ssrpattern_squarep(rx) ssrrule_ne(r) ] ->
    [ mk_rwarg norwmult (nodocc, rx) r ]
  | [ ssrpattern_ne_squarep(rx) ssrrule_ne(r) ] ->
    [ mk_rwarg norwmult (noclr, rx) r ]
  | [ ssrrule_ne(r) ] ->
    [ mk_rwarg norwmult norwocc r ]
END

let simplintac occ rdx sim gl = 
  let simptac gl = 
    let sigma0, concl0, env0 = project gl, pf_concl gl, pf_env gl in
    let simp env c _ = red_safe Tacred.simpl env sigma0 c in
    convert_concl_no_check (eval_pattern env0 sigma0 concl0 rdx occ simp) gl in
  match sim with
  | Simpl -> simptac gl
  | SimplCut -> tclTHEN simptac (tclTRY donetac) gl
  | _ -> simpltac sim gl

let rec get_evalref c =  match kind_of_term c with
  | Var id -> EvalVarRef id
  | Const k -> EvalConstRef k
  | App (c', _) -> get_evalref c'
  | Cast (c', _, _) -> get_evalref c'
  | _ -> errorstrm (str "The term " ++ pr_constr c ++ str " is not unfoldable")

(* Strip a pattern generated by a prenex implicit to its constant. *)
let strip_unfold_term ((sigma, t) as p) kt = match kind_of_term t with
  | App (f, a) when kt = ' ' && array_for_all isEvar a && isConst f -> 
    (sigma, f), true
  | Const _ | Var _ -> p, true
  | _ -> p, false

let unfoldintac occ rdx t (kt,_) gl = 
  let fs sigma x = Reductionops.nf_evar sigma x in
  let sigma0, concl0, env0 = project gl, pf_concl gl, pf_env gl in
  let (sigma, t), const = strip_unfold_term t kt in
  let body env t c = Tacred.unfoldn [(true, [1]), get_evalref t] env sigma0 c in
  let easy = occ = [] && rdx = None in
  let red_flags = if easy then Closure.betaiotazeta else Closure.betaiota in
  let beta env = Reductionops.clos_norm_flags red_flags env sigma0 in
  let unfold, conclude = match rdx with
  | Some (_, (In_T _ | In_X_In_T _)) | None ->
    let ise = create_evar_defs sigma in
    let u, ise = mk_upat env0 sigma0 ise t all_ok L2R t in
    let find_T, end_T = mk_pmatcher ~raise_NoMatch:true sigma0 occ ([u],ise) in
    (fun env c h -> 
      try find_T env c h (fun env _ c _ -> body env t c)
      with NoMatch when easy -> c 
      | NoMatch | NoProgress -> errorstrm (str"No occurrence of "
        ++ pr_constr_pat t ++ spc() ++ str "in " ++ pr_constr c)),
    (fun () -> try end_T () with 
      | NoMatch when easy -> fake_pmatcher_end () 
      | NoMatch -> anomaly "unfoldintac")
  | _ -> 
    (fun env (c as orig_c) h ->
      if const then
          let rec aux c = 
            match kind_of_term c with
            | Const _ when eq_constr c t -> body env t t
            | App (f,a) when eq_constr f t -> mkApp (body env f f,a)
            | _ -> let c = Reductionops.whd_betaiotazeta sigma0 c in
            match kind_of_term c with
            | Const _ when eq_constr c t -> body env t t
            | App (f,a) when eq_constr f t -> mkApp (body env f f,a)
            | Const f -> aux (body env c c)
            | App (f, a) -> aux (mkApp (body env f f, a))
            | _ -> errorstrm (str "The term "++pr_constr orig_c++
                str" contains no " ++ pr_constr t ++ str" even after unfolding")
          in aux c
      else
        try body env t (fs (unify_HO env sigma c t) t)
        with _ -> errorstrm (str "The term " ++
          pr_constr c ++spc()++ str "does not unify with " ++ pr_constr_pat t)),
    fake_pmatcher_end in
  let concl = beta env0 (eval_pattern env0 sigma0 concl0 rdx occ unfold) in
  let _ = conclude () in
  convert_concl concl gl
;;

let foldtac occ rdx ft gl = 
  let fs sigma x = Reductionops.nf_evar sigma x in
  let sigma0, concl0, env0 = project gl, pf_concl gl, pf_env gl in
  let sigma, t = ft in
  let fold, conclude = match rdx with
  | Some (_, (In_T _ | In_X_In_T _)) | None ->
    let ise = create_evar_defs sigma in
    let ut = try Tacred.red_product env0 sigma t with _ -> t in
    let ut, ise = mk_upat env0 sigma0 ise t all_ok L2R ut in
    let find_T,end_T= mk_pmatcher ~raise_NoMatch:true sigma0 occ ([ut],ise) in
    (fun env c h -> try find_T env c h (fun env _ t _ -> t) with NoMatch -> c),
    (fun () -> try end_T () with NoMatch -> fake_pmatcher_end ())
  | _ -> 
    (fun env c h -> try let sigma = unify_HO env sigma c t in fs sigma t
    with _ -> errorstrm (str "fold pattern " ++ pr_constr_pat t ++ spc ()
      ++ str "does not match redex " ++ pr_constr_pat c)), 
    fake_pmatcher_end in
  let concl = eval_pattern env0 sigma0 concl0 rdx occ fold in
  let _ = conclude () in
  convert_concl concl gl
;;

let converse_dir = function L2R -> R2L | R2L -> L2R

let rw_progress rhs lhs ise = not (eq_constr lhs (Evarutil.nf_evar ise rhs))

(* Coq has a more general form of "equation" (any type with a single *)
(* constructor with no arguments with_rect_r elimination lemmas).    *)
(* However there is no clear way of determining the LHS and RHS of   *)
(* such a generic Leibnitz equation -- short of inspecting the type  *)
(* of the elimination lemmas.                                        *)

let rec strip_prod_assum c = match kind_of_term c with
  | Prod (_, _, c') -> strip_prod_assum c'
  | LetIn (_, v, _, c') -> strip_prod_assum (subst1 v c)
  | Cast (c', _, _) -> strip_prod_assum c'
  | _ -> c

let rule_id = mk_internal_id "rewrite rule"

exception PRtype_error
exception PRindetermined_rhs of constr

let pirrel_rewrite pred rdx rdx_ty new_rdx dir (sigma, c) c_ty gl =
  let env = pf_env gl in
  let beta = Reductionops.clos_norm_flags Closure.beta env sigma in
  let sigma, p = 
    let sigma = create_evar_defs sigma in
    Evarutil.new_evar sigma env (beta (subst1 new_rdx pred)) in
  let pred = mkNamedLambda pattern_id rdx_ty pred in
  let elim = 
    let (kn, i) as ind, unfolded_c_ty = pf_reduce_to_quantified_ind gl c_ty in
    let sort = elimination_sort_of_goal gl in
    let elim = Indrec.lookup_eliminator ind sort in
    if dir = R2L then elim else (* taken from Coq's rewrite *)
    let elim = destConst elim in          
    let mp,dp,l = repr_con (constant_of_kn (canonical_con elim)) in
    let l' = label_of_id (Nameops.add_suffix (id_of_label l) "_r")  in 
    let c1' = Global.constant_of_delta (make_con mp dp l') in
    mkConst c1' in
  let proof = mkApp (elim, [| rdx_ty; new_rdx; pred; p; rdx; c |]) in
  let proof_ty =
    try Typing.type_of env sigma proof with _ -> raise PRtype_error in
   pp(lazy(str"pirrel_rewrite proof term of type: " ++ pr_constr proof_ty));
  try refine_with 
    ~first_goes_last:(not !ssroldreworder) ~with_evars:false (sigma, proof) gl
  with _ -> 
    (* we generate a msg like: "Unable to find an instance for the variable" *)
    let c = Reductionops.nf_evar sigma c in
    let hd_ty, miss = match kind_of_term c with
    | App (hd, args) -> 
        let hd_ty = Retyping.get_type_of env sigma hd in
        let names = let rec aux t = function 0 -> [] | n ->
          let t = Reductionops.whd_betadeltaiota env sigma t in
          match kind_of_type t with
          | ProdType (name, _, t) -> name :: aux t (n-1)
          | _ -> assert false in aux hd_ty (Array.length args) in
        hd_ty, Util.list_map_filter (fun (t, name) ->
          let evs = Util.Intset.elements (Evarutil.evars_of_term t) in
          let open_evs = List.filter (fun k ->
            InProp <> Retyping.get_sort_family_of
              env sigma (Evd.evar_concl (Evd.find sigma k)))
            evs in
          if open_evs <> [] then Some name else None)
          (List.combine (Array.to_list args) names)
    | _ -> anomaly "rewrite rule not an application" in
    errorstrm (Himsg.explain_refiner_error (Logic.UnresolvedBindings miss) ++
      (Pp.fnl()++str"Rule's type:" ++ spc() ++ pr_constr hd_ty))
;;

let rwcltac cl rdx dir sr gl =
  let n, r_n = pf_abs_evars gl sr in
  let r_n' = pf_abs_cterm gl n r_n in
  let r' = subst_var pattern_id r_n' in
  let rdxt = Retyping.get_type_of (pf_env gl) (fst sr) rdx in
  let cvtac, rwtac =
    if closed0 r' then 
      let env, sigma, c, c_eq = pf_env gl, fst sr, snd sr, build_coq_eq () in
      let c_ty = Typing.type_of env sigma c in
      match kind_of_type (Reductionops.whd_betadeltaiota env sigma c_ty) with
      | AtomicType(e, a) when eq_constr e c_eq -> 
          let new_rdx = if dir = L2R then a.(2) else a.(1) in
          pirrel_rewrite cl rdx rdxt new_rdx dir sr c_ty, tclIDTAC
      | _ -> 
          let cl' = mkApp (mkNamedLambda pattern_id rdxt cl, [|rdx|]) in
          convert_concl cl', rewritetac dir r'
    else
      let dc, r2 = decompose_lam_n n r' in
      let r3, _, r3t  = 
        try destCast r2 with _ ->
        errorstrm (str "no cast from " ++ pr_constr_pat (snd sr)
                    ++ str " to " ++ pr_constr r2) in
      let cl' = mkNamedProd rule_id (compose_prod dc r3t) (lift 1 cl) in
      let cl'' = mkNamedProd pattern_id rdxt cl' in
      let itacs = [introid pattern_id; introid rule_id] in
      let cltac = clear [pattern_id; rule_id] in
      let rwtacs = [rewritetac dir (mkVar rule_id); cltac] in
      (apply_type cl'' [rdx; compose_lam dc r3], tclTHENLIST (itacs @ rwtacs))
  in
  let cvtac' _ =
    try cvtac gl with
    | PRtype_error ->
      if occur_existential (pf_concl gl)
      then errorstrm (str "Rewriting impacts evars")
      else errorstrm (str "Dependent type error in rewrite of "
        ++ pf_pr_constr gl (mkNamedLambda pattern_id rdxt cl))
    | Util.UserError _ as e -> raise e
    | e -> anomaly ("cvtac's exception: " ^ Printexc.to_string e);
  in
  tclTHEN cvtac' rwtac gl

let lz_coq_prod =
  let prod = lazy (build_prod ()) in fun () -> Lazy.force prod

let lz_setoid_relation =
  let sdir = ["Classes"; "RelationClasses"] in
  let last_srel = ref (Environ.empty_env, None) in
  fun env -> match !last_srel with
  | env', srel when env' == env -> srel
  | _ ->
    let srel =
       try Some (coq_constant "Class_setoid" sdir "RewriteRelation")
       with _ -> None in
    last_srel := (env, srel); srel

let ssr_is_setoid env =
  match lz_setoid_relation env with
  | None -> fun _ _ _ -> false
  | Some srel ->
  fun sigma r args ->
    Rewrite.is_applied_rewrite_relation env 
      sigma [] (mkApp (r, args)) <> None

let closed0_check cl p gl =
  if closed0 cl then errorstrm (str"No occurrence of redex "++pf_pr_constr gl p)

let rwrxtac occ rdx_pat dir rule gl =
  let env = pf_env gl in
  let coq_prod = lz_coq_prod () in
  let is_setoid = ssr_is_setoid env in
  let r_sigma, rules =
    let rec loop d sigma r t0 rs red =
      let t =
        if red = 1 then Tacred.hnf_constr env sigma t0
        else Reductionops.whd_betaiotazeta sigma t0 in
      match kind_of_term t with
      | Prod (_, xt, at) ->
        let ise, x = Evarutil.new_evar (create_evar_defs sigma) env xt in
        loop d ise (mkApp (r, [|x|])) (subst1 x at) rs 0
      | App (pr, a) when pr = coq_prod.Coqlib.typ ->
        let sr = match kind_of_term (Tacred.hnf_constr env sigma r) with
        | App (c, ra) when c = coq_prod.Coqlib.intro -> fun i -> ra.(i + 1)
        | _ -> let ra = Array.append a [|r|] in
          function 1 -> mkApp (coq_prod.Coqlib.proj1, ra)
                | _ ->  mkApp (coq_prod.Coqlib.proj2, ra) in
        if a.(0) = build_coq_I () then
         loop (converse_dir d) sigma (sr 2) a.(1) rs 0
        else
         let sigma2, rs2 = loop d sigma (sr 2) a.(1) rs 0 in
         loop d sigma2 (sr 1) a.(0) rs2 0
      | App (r_eq, a) when Hipattern.match_with_equality_type t != None ->
        let ind = destInd r_eq and rhs = array_last a in
        let np, ndep = Inductiveops.inductive_nargs env ind in
        let ind_ct = Inductiveops.type_of_constructors env ind in
        let lhs0 = last_arg (strip_prod_assum ind_ct.(0)) in
        let rdesc = match kind_of_term lhs0 with
        | Rel i ->
          let lhs = a.(np - i) in
          let lhs, rhs = if d = L2R then lhs, rhs else rhs, lhs in
(* msgnl (str "RW: " ++ pr_rwdir d ++ str " " ++ pr_constr_pat r ++ str " : "
            ++ pr_constr_pat lhs ++ str " ~> " ++ pr_constr_pat rhs); *)
          d, r, lhs, rhs
(*
          let l_i, r_i = if d = L2R then i, 1 - ndep else 1 - ndep, i in
          let lhs = a.(np - l_i) and rhs = a.(np - r_i) in
          let a' = Array.copy a in let _ = a'.(np - l_i) <- mkVar pattern_id in
          let r' = mkCast (r, DEFAULTcast, mkApp (r_eq, a')) in
          (d, r', lhs, rhs)
*)
        | _ ->
          let lhs = substl (array_list_of_tl (Array.sub a 0 np)) lhs0 in
          let lhs, rhs = if d = R2L then lhs, rhs else rhs, lhs in
          let d' = if Array.length a = 1 then d else converse_dir d in
          d', r, lhs, rhs in
        sigma, rdesc :: rs
      | App (s_eq, a) when is_setoid sigma s_eq a ->
        let np = Array.length a and i = 3 - dir_org d in
        let lhs = a.(np - i) and rhs = a.(np + i - 3) in
        let a' = Array.copy a in let _ = a'.(np - i) <- mkVar pattern_id in
        let r' = mkCast (r, DEFAULTcast, mkApp (s_eq, a')) in
        sigma, (d, r', lhs, rhs) :: rs
      | _ ->
        if red = 0 then loop d sigma r t rs 1
        else errorstrm (str "not a rewritable relation: " ++ pr_constr_pat t
                        ++ spc() ++ str "in rule " ++ pr_constr_pat (snd rule))
        in
    let sigma, r = rule in
    let t = Retyping.get_type_of env sigma r in
    loop dir sigma r t [] 0 in
  let find_rule rdx =
    let rec rwtac = function
      | [] ->
        errorstrm (str "pattern " ++ pr_constr_pat rdx ++
                   str " does not match " ++ pr_dir_side dir ++
                   str " of " ++ pr_constr_pat (snd rule))
      | (d, r, lhs, rhs) :: rs ->
        try
          let ise = unif_HO env (create_evar_defs r_sigma) lhs rdx in
          let sr' = unif_end env (project gl) ise r (rw_progress rhs rdx) in
          d, sr'
        with _ -> rwtac rs in
     rwtac rules in
  let sigma0, env0, concl0 = project gl, pf_env gl, pf_concl gl in
  let find_R, conclude = match rdx_pat with
  | Some (_, (In_T _ | In_X_In_T _)) | None ->
      let upats_origin = dir, snd rule in
      let rpat env sigma0 (pats, sigma) (d, r, lhs, rhs) =
        let pat, sigma = mk_upat env sigma0 sigma r (rw_progress rhs) d lhs in
        pats @ [pat], sigma in
      let rpats = List.fold_left (rpat env0 sigma0) ([], r_sigma) rules in
      let find_R, end_R = mk_pmatcher sigma0 occ ~upats_origin rpats in
      find_R ~k:(fun _ _ _ h -> mkRel h), 
      fun cl -> let rdx,d,r = end_R () in closed0_check cl rdx gl; (d,r),rdx
  | Some(_, (T e | X_In_T (_,e) | E_As_X_In_T (e,_,_) | E_In_X_In_T (e,_,_))) ->
      let r = ref None in
      (fun env c h -> do_once r (fun () -> find_rule c, c); mkRel h),
      (fun concl -> closed0_check concl e gl; assert_done r) in
  let concl = eval_pattern env0 sigma0 concl0 rdx_pat occ find_R in
  let (d, r), rdx = conclude concl in
  rwcltac concl rdx d r gl
;;

(* Resolve forward reference *)
let _ = 
  ipat_rewritetac := fun occ dir c gl -> rwrxtac occ None dir (project gl, c) gl

let rwargtac ist ((dir, mult), (((oclr, occ), grx), (kind, gt))) gl =
  let fail = ref false in
  let interp_pattern ist gl gc =
    try interp_pattern ist gl gc None
    with _ when snd mult = May -> fail := true; project gl, T mkImplicit in
  let interp gc =
    try interp_term ist gl gc
    with _ when snd mult = May -> fail := true; (project gl, mkImplicit) in
  let rx = Option.map (interp_pattern ist gl) grx in
  let t = interp gt in
  let rwtac = match kind with
  | RWred sim -> simplintac occ rx sim
  | RWdef -> if dir = R2L then foldtac occ rx t else unfoldintac occ rx t gt
  | RWeq -> rwrxtac occ rx dir t in
  let ctac = cleartac (interp_clr (oclr, (fst gt, snd t))) in
  if !fail then ctac gl else tclTHEN (tclMULT mult rwtac) ctac gl

(** Rewrite argument sequence *)

(* type ssrrwargs = ssrrwarg list * ssrltacctx *)

let pr_ssrrwargs _ _ _ (rwargs, _) = pr_list spc pr_rwarg rwargs

ARGUMENT EXTEND ssrrwargs TYPED AS ssrrwarg list * ssrltacctx
                          PRINTED BY pr_ssrrwargs
  | [ "(**)" ] -> [ anomaly "Grammar placeholder match" ]
END

let ssr_rw_syntax = ref true

let _ =
  Goptions.declare_bool_option
    { Goptions.optsync  = true;
      Goptions.optname  = "ssreflect rewrite";
      Goptions.optkey   = ["SsrRewrite"];
      Goptions.optread  = (fun _ -> !ssr_rw_syntax);
      Goptions.optwrite = (fun b -> ssr_rw_syntax := b) }

let test_ssr_rw_syntax =
  let test strm  =
    if not !ssr_rw_syntax then raise Stream.Failure else
    if ssr_loaded () then () else
    match Stream.npeek 1 strm with
    | ["", key] when List.mem key.[0] ['{'; '['; '/'] -> ()
    | _ -> raise Stream.Failure in
  Gram.Entry.of_parser "test_ssr_rw_syntax" test

GEXTEND Gram
  GLOBAL: ssrrwargs;
  ssrrwargs: [[ test_ssr_rw_syntax; a = LIST1 ssrrwarg -> a, rawltacctx ]];
END

(** The "rewrite" tactic *)

let ssrrewritetac (rwargs, ctx) =
  tclTHENLIST (List.map (rwargtac (get_ltacctx ctx)) rwargs)

TACTIC EXTEND ssrrewrite
  | [ "rewrite" ssrrwargs(args) ssrclauses(clauses) ] ->
    [ tclCLAUSES (ssrrewritetac args) clauses ]
END

(** The "unlock" tactic *)

let pr_unlockarg (occ, t) = pr_occ occ ++ pr_term t
let pr_ssrunlockarg _ _ _ = pr_unlockarg

ARGUMENT EXTEND ssrunlockarg TYPED AS ssrocc * ssrterm
  PRINTED BY pr_ssrunlockarg
  | [  "{" ssrocc(occ) "}" ssrterm(t) ] -> [ occ, t ]
  | [  ssrterm(t) ] -> [ [], t ]
END

let pr_ssrunlockargs _ _ _ (args, _) = pr_list spc pr_unlockarg args

ARGUMENT EXTEND ssrunlockargs TYPED AS ssrunlockarg list * ssrltacctx
  PRINTED BY pr_ssrunlockargs
  | [  ssrunlockarg_list(args) ] -> [ args, rawltacctx ]
END

let unfoldtac occ ko t kt gl =
  let cl, c = pf_fill_occ_term gl occ (fst (strip_unfold_term t kt)) in
  let cl' = subst1 (pf_unfoldn [(true, [1]), get_evalref c] gl c) cl in
  let f = if ko = [] then Closure.betaiotazeta else Closure.betaiota in
  convert_concl (pf_reduce (Reductionops.clos_norm_flags f) gl cl') gl

let unlocktac (args, ctx) =
  let ist = get_ltacctx ctx in
  let utac (occ, gt) gl =
    unfoldtac occ occ (interp_term ist gl gt) (fst gt) gl in
  let locked = mkSsrConst "locked" in
  let key = mkSsrConst "master_key" in
  let ktacs = [
    (fun gl -> unfoldtac [] [] (project gl,locked) '(' gl); 
    simplest_newcase key ] in
  tclTHENLIST (List.map utac args @ ktacs)

TACTIC EXTEND ssrunlock
  | [ "unlock" ssrunlockargs(args) ssrclauses(clauses) ] ->
    [  tclCLAUSES (unlocktac args) clauses ]
END

(** 8. Forward chaining tactics (pose, set, have, suffice, wlog) *)

(** Defined identifier *)

type ssrfwdid = identifier

let pr_ssrfwdid _ _ _ id = pr_spc () ++ pr_id id

(* We use a primitive parser for the head identifier of forward *)
(* tactis to avoid syntactic conflicts with basic Coq tactics. *)
ARGUMENT EXTEND ssrfwdid TYPED AS ident PRINTED BY pr_ssrfwdid
  | [ "(**)" ] -> [ Util.anomaly "Grammar placeholder match" ]
END

let accept_ssrfwdid strm =
  match Stream.npeek 1 strm with
  | ["IDENT", id] -> accept_before_syms_or_any_id [":"; ":="; "("] strm
  | _ -> raise Stream.Failure


let test_ssrfwdid = Gram.Entry.of_parser "test_ssrfwdid" accept_ssrfwdid

GEXTEND Gram
  GLOBAL: ssrfwdid;
  ssrfwdid: [[ test_ssrfwdid; id = Prim.ident -> id ]];
  END



(** Definition value formatting *)

(* We use an intermediate structure to correctly render the binder list  *)
(* abbreviations. We use a list of hints to extract the binders and      *)
(* base term from a term, for the two first levels of representation of  *)
(* of constr terms.                                                      *)

type 'term ssrbind =
  | Bvar of name
  | Bdecl of name list * 'term
  | Bdef of name * 'term option * 'term
  | Bstruct of name
  | Bcast of 'term

let pr_binder prl = function
  | Bvar x ->
    pr_name x
  | Bdecl (xs, t) ->
    str "(" ++ pr_list pr_spc pr_name xs ++ str " : " ++ prl t ++ str ")"
  | Bdef (x, None, v) ->
    str "(" ++ pr_name x ++ str " := " ++ prl v ++ str ")"
  | Bdef (x, Some t, v) ->
    str "(" ++ pr_name x ++ str " : " ++ prl t ++
                            str " := " ++ prl v ++ str ")"
  | Bstruct x ->
    str "{struct " ++ pr_name x ++ str "}"
  | Bcast t ->
    str ": " ++ prl t

type 'term ssrbindval = 'term ssrbind list * 'term

type ssrbindfmt =
  | BFvar
  | BFdecl of int        (* #xs *)
  | BFcast               (* final cast *)
  | BFdef of bool        (* has cast? *)
  | BFrec of bool * bool (* has struct? * has cast? *)

let rec mkBstruct i = function
  | Bvar x :: b ->
    if i = 0 then [Bstruct x] else mkBstruct (i - 1) b
  | Bdecl (xs, _) :: b ->
    let i' = i - List.length xs in
    if i' < 0 then [Bstruct (List.nth xs i)] else mkBstruct i' b
  | _ :: b -> mkBstruct i b
  | [] -> []

let rec format_local_binders h0 bl0 = match h0, bl0 with
  | BFvar :: h, LocalRawAssum ([_, x], _,  _) :: bl ->
    Bvar x :: format_local_binders h bl
  | BFdecl _ :: h, LocalRawAssum (lxs, _, t) :: bl ->
    Bdecl (List.map snd lxs, t) :: format_local_binders h bl
  | BFdef false :: h, LocalRawDef ((_, x), v) :: bl ->
    Bdef (x, None, v) :: format_local_binders h bl
  | BFdef true :: h,
      LocalRawDef ((_, x), CCast (_, v, CastConv (_, t))) :: bl ->
    Bdef (x, Some t, v) :: format_local_binders h bl
  | _ -> []
  
let rec format_constr_expr h0 c0 = match h0, c0 with
  | BFvar :: h, CLambdaN (_, [[_, x], _, _], c) ->
    let bs, c' = format_constr_expr h c in
    Bvar x :: bs, c'
  | BFdecl _:: h, CLambdaN (_, [lxs, _, t], c) ->
    let bs, c' = format_constr_expr h c in
    Bdecl (List.map snd lxs, t) :: bs, c'
  | BFdef false :: h, CLetIn(_, (_, x), v, c) ->
    let bs, c' = format_constr_expr h c in
    Bdef (x, None, v) :: bs, c'
  | BFdef true :: h, CLetIn(_, (_, x), CCast (_, v, CastConv (_, t)), c) ->
    let bs, c' = format_constr_expr h c in
    Bdef (x, Some t, v) :: bs, c'
  | [BFcast], CCast (_, c, CastConv (_, t)) ->
    [Bcast t], c
  | BFrec (has_str, has_cast) :: h, 
    CFix (_, _, [_, (Some locn, CStructRec), bl, t, c]) ->
    let bs = format_local_binders h bl in
    let bstr = if has_str then [Bstruct (Name (snd locn))] else [] in
    bs @ bstr @ (if has_cast then [Bcast t] else []), c 
  | BFrec (_, has_cast) :: h, CCoFix (_, _, [_, bl, t, c]) ->
    format_local_binders h bl @ (if has_cast then [Bcast t] else []), c
  | _, c ->
    [], c

let rec format_rawdecl h0 d0 = match h0, d0 with
  | BFvar :: h, (x, _, None, _) :: d ->
    Bvar x :: format_rawdecl h d
  | BFdecl 1 :: h,  (x, _, None, t) :: d ->
    Bdecl ([x], t) :: format_rawdecl h d
  | BFdecl n :: h, (x, _, None, t) :: d when n > 1 ->
    begin match format_rawdecl (BFdecl (n - 1) :: h) d with
    | Bdecl (xs, _) :: bs -> Bdecl (x :: xs, t) :: bs
    | bs -> Bdecl ([x], t) :: bs
    end
  | BFdef false :: h, (x, _, Some v, _)  :: d ->
    Bdef (x, None, v) :: format_rawdecl h d
  | BFdef true:: h, (x, _, Some (RCast (_, v, CastConv (_, t))), _) :: d ->
    Bdef (x, Some t, v) :: format_rawdecl h d
  | _, (x, _, None, t) :: d ->
    Bdecl ([x], t) :: format_rawdecl [] d
  | _, (x, _, Some v, _) :: d ->
     Bdef (x, None, v) :: format_rawdecl [] d
  | _, [] -> []

let rec format_rawconstr h0 c0 = match h0, c0 with
  | BFvar :: h, RLambda (_, x, _, _, c) ->
    let bs, c' = format_rawconstr h c in
    Bvar x :: bs, c'
  | BFdecl 1 :: h,  RLambda (_, x, _, t, c) ->
    let bs, c' = format_rawconstr h c in
    Bdecl ([x], t) :: bs, c'
  | BFdecl n :: h,  RLambda (_, x, _, t, c) when n > 1 ->
    begin match format_rawconstr (BFdecl (n - 1) :: h) c with
    | Bdecl (xs, _) :: bs, c' -> Bdecl (x :: xs, t) :: bs, c'
    | _ -> [Bdecl ([x], t)], c
    end
  | BFdef false :: h, RLetIn(_, x, v, c) ->
    let bs, c' = format_rawconstr h c in
    Bdef (x, None, v) :: bs, c'
  | BFdef true :: h, RLetIn(_, x, RCast (_, v, CastConv (_, t)), c) ->
    let bs, c' = format_rawconstr h c in
    Bdef (x, Some t, v) :: bs, c'
  | [BFcast], RCast (_, c, CastConv(_, t)) ->
    [Bcast t], c
  | BFrec (has_str, has_cast) :: h, RRec (_, f, _, bl, t, c)
      when Array.length c = 1 ->
    let bs = format_rawdecl h bl.(0) in
    let bstr = match has_str, f with
    | true, RFix ([|Some i, RStructRec|], _) -> mkBstruct i bs
    | _ -> [] in
    bs @ bstr @ (if has_cast then [Bcast t.(0)] else []), c.(0)
  | _, c ->
    [], c

(** Forward chaining argument *)

(* There are three kinds of forward definitions:           *)
(*   - Hint: type only, cast to Type, may have proof hint. *)
(*   - Have: type option + value, no space before type     *)
(*   - Pose: binders + value, space before binders.        *)

type ssrfwdkind = FwdHint of string | FwdHave | FwdPose

type ssrfwdfmt = ssrfwdkind * ssrbindfmt list

let pr_fwdkind = function FwdHint s -> str (s ^ " ") | _ -> str " :=" ++ spc ()
let pr_fwdfmt (fk, _ : ssrfwdfmt) = pr_fwdkind fk

let wit_ssrfwdfmt, globwit_ssrfwdfmt, rawwit_ssrfwdfmt =
  add_genarg "ssrfwdfmt" pr_fwdfmt

(* type ssrfwd = ssrfwdfmt * ssrterm *)

let mkFwdVal fk c = ((fk, []), mk_term ' ' c), rawltacctx
let mkssrFwdVal fk c = ((fk, []), (c,None)), rawltacctx

let mkFwdCast fk loc t c =
  ((fk, [BFcast]), mk_term ' ' (CCast (loc, c, dC t))), rawltacctx
let mkssrFwdCast fk loc t c = ((fk, [BFcast]), (c, Some t)), rawltacctx

let mkFwdHint s t =
  let loc = constr_loc t in mkFwdCast (FwdHint s) loc t (CHole (loc, None))

let pr_gen_fwd prval prc prlc fk (bs, c) =
  let prc s = str s ++ spc () ++ prval prc prlc c in
  match fk, bs with
  | FwdHint s, [Bcast t] -> str s ++ spc () ++ prlc t
  | FwdHint s, _ ->  prc (s ^ "(* typeof *)")
  | FwdHave, [Bcast t] -> str ":" ++ spc () ++ prlc t ++ prc " :="
  | _, [] -> prc " :="
  | _, _ -> spc () ++ pr_list spc (pr_binder prlc) bs ++ prc " :="

let pr_fwd_guarded prval prval' = function
| ((fk, h), (_, (_, Some c))), _ ->
  pr_gen_fwd prval pr_constr_expr prl_constr_expr fk (format_constr_expr h c)
| ((fk, h), (_, (c, None))), _ ->
  pr_gen_fwd prval' pr_rawconstr prl_rawconstr fk (format_rawconstr h c)

let pr_unguarded prc prlc = prlc

let pr_fwd = pr_fwd_guarded pr_unguarded pr_unguarded
let pr_ssrfwd _ _ _ = pr_fwd
 
ARGUMENT EXTEND ssrfwd TYPED AS (ssrfwdfmt * ssrterm) * ssrltacctx
                       PRINTED BY pr_ssrfwd
  | [ ":=" lconstr(c) ] -> [ mkFwdVal FwdPose c ]
  | [ ":" lconstr (t) ":=" lconstr(c) ] -> [ mkFwdCast FwdPose loc t c ]
END

(** Independent parsing for binders *)

(* The pose, pose fix, and pose cofix tactics use these internally to  *)
(* parse argument fragments.                                           *)

let pr_ssrbvar prc _ _ v = prc v

ARGUMENT EXTEND ssrbvar TYPED AS constr PRINTED BY pr_ssrbvar
| [ ident(id) ] -> [ mkCVar loc id ]
| [ "_" ] -> [ CHole (loc, None) ]
END

let bvar_lname = function
  | CRef (Ident (loc, id)) -> loc, Name id
  | c -> constr_loc c, Anonymous

let pr_ssrbinder prc _ _ (_, c) = prc c

ARGUMENT EXTEND ssrbinder TYPED AS ssrfwdfmt * constr PRINTED BY pr_ssrbinder
 | [ ssrbvar(bv) ] ->
   [ let xloc, _ as x = bvar_lname bv in
     (FwdPose, [BFvar]),
     CLambdaN (loc,[[x],Default Explicit,CHole (xloc,None)],CHole (loc,None)) ]
 | [ "(" ssrbvar(bv) ")" ] ->
   [ let xloc, _ as x = bvar_lname bv in
     (FwdPose, [BFvar]),
     CLambdaN (loc,[[x],Default Explicit,CHole (xloc,None)],CHole (loc,None)) ]
 | [ "(" ssrbvar(bv) ":" lconstr(t) ")" ] ->
   [ let x = bvar_lname bv in
     (FwdPose, [BFdecl 1]),
     CLambdaN (loc, [[x], Default Explicit, t], CHole (loc, None)) ]
 | [ "(" ssrbvar(bv) ne_ssrbvar_list(bvs) ":" lconstr(t) ")" ] ->
   [ let xs = List.map bvar_lname (bv :: bvs) in
     let n = List.length xs in
     (FwdPose, [BFdecl n]),
     CLambdaN (loc, [xs, Default Explicit, t], CHole (loc, None)) ]
 | [ "(" ssrbvar(id) ":" lconstr(t) ":=" lconstr(v) ")" ] ->
   [ let loc' = Util.join_loc (constr_loc t) (constr_loc v) in
     let v' = CCast (loc', v, dC t) in
     (FwdPose,[BFdef true]), CLetIn (loc,bvar_lname id, v',CHole (loc,None)) ]
 | [ "(" ssrbvar(id) ":=" lconstr(v) ")" ] ->
   [ (FwdPose,[BFdef false]), CLetIn (loc,bvar_lname id, v,CHole (loc,None)) ]
END

GEXTEND Gram
  GLOBAL: ssrbinder;
  ssrbinder: [
  [  ["of" | "&"]; c = operconstr LEVEL "99" ->
     (FwdPose, [BFvar]),
     CLambdaN (loc,[[loc,Anonymous],Default Explicit,c],CHole (loc,None)) ]
  ];
END

let rec binders_fmts = function
  | ((_, h), _) :: bs -> h @ binders_fmts bs
  | _ -> []

let push_binders c2 bs =
  let loc2 = constr_loc c2 in let mkloc loc1 = Util.join_loc loc1 loc2 in
  let rec loop ty c = function
  | (_, CLambdaN (loc1, b, _)) :: bs when ty ->
      CProdN (mkloc loc1, b, loop ty c bs)
  | (_, CLambdaN (loc1, b, _)) :: bs ->
      CLambdaN (mkloc loc1, b, loop ty c bs)
  | (_, CLetIn (loc1, x, v, _)) :: bs ->
      CLetIn (mkloc loc1, x, v, loop ty c bs)
  | [] -> c
  | _ -> anomaly "binder not a lambda nor a let in" in
  match c2 with
  | CCast (x, ct, CastConv (y, cty)) ->
      (CCast (x, loop false ct bs, CastConv (y, loop true cty bs)))
  | ct -> loop false ct bs

let rec fix_binders = function
  | (_, CLambdaN (_, [xs, _, t], _)) :: bs ->
      LocalRawAssum (xs, Default Explicit, t) :: fix_binders bs
  | (_, CLetIn (_, x, v, _)) :: bs ->
    LocalRawDef (x, v) :: fix_binders bs
  | _ -> []

let pr_ssrstruct _ _ _ = function
  | Some id -> str "{struct " ++ pr_id id ++ str "}"
  | None -> mt ()

ARGUMENT EXTEND ssrstruct TYPED AS ident option PRINTED BY pr_ssrstruct
| [ "{" "struct" ident(id) "}" ] -> [ Some id ]
| [ ] -> [ None ]
END

(** The "pose" tactic *)

(* The plain pose form. *)

let bind_fwd bs = function
  | ((fk, h), (ck, (rc, Some c))), ctx ->
    ((fk,binders_fmts bs @ h), (ck,(rc,Some (push_binders c bs)))), ctx
  | fwd -> fwd

ARGUMENT EXTEND ssrposefwd TYPED AS ssrfwd PRINTED BY pr_ssrfwd
  | [ ssrbinder_list(bs) ssrfwd(fwd) ] -> [ bind_fwd bs fwd ]
END

(* The pose fix form. *)

let pr_ssrfixfwd _ _ _ (id, fwd) = str " fix " ++ pr_id id ++ pr_fwd fwd

let bvar_locid = function
  | CRef (Ident (loc, id)) -> loc, id
  | _ -> Util.error "Missing identifier after \"(co)fix\""


ARGUMENT EXTEND ssrfixfwd TYPED AS ident * ssrfwd PRINTED BY pr_ssrfixfwd
  | [ "fix" ssrbvar(bv) ssrbinder_list(bs) ssrstruct(sid) ssrfwd(fwd) ] ->
    [ let (_, id) as lid = bvar_locid bv in
      let ((fk, h), (ck, (rc, oc))), ctx = fwd in
      let c = Option.get oc in
      let has_cast, t', c' = match format_constr_expr h c with
      | [Bcast t'], c' -> true, t', c'
      | _ -> false, CHole (constr_loc c, None), c in
      let lb = fix_binders bs in
      let has_struct, i =
        let rec loop = function
          (l', Name id') :: _ when sid = Some id' -> true, (l', id')
          | [l', Name id'] when sid = None -> false, (l', id')
          | _ :: bn -> loop bn
          | [] -> Util.error "Bad structural argument" in
        loop (names_of_local_assums lb) in
      let h' = BFrec (has_struct, has_cast) :: binders_fmts bs in
      let fix = CFix (loc, lid, [lid, (Some i, CStructRec), lb, t', c']) in
      id, (((fk, h'), (ck, (rc, Some fix))), ctx) ]
END


(* The pose cofix form. *)

let pr_ssrcofixfwd _ _ _ (id, fwd) = str " cofix " ++ pr_id id ++ pr_fwd fwd

ARGUMENT EXTEND ssrcofixfwd TYPED AS ssrfixfwd PRINTED BY pr_ssrcofixfwd
  | [ "cofix" ssrbvar(bv) ssrbinder_list(bs) ssrfwd(fwd) ] ->
    [ let _, id as lid = bvar_locid bv in
      let ((fk, h), (ck, (rc, oc))), ctx = fwd in
      let c = Option.get oc in
      let has_cast, t', c' = match format_constr_expr h c with
      | [Bcast t'], c' -> true, t', c'
      | _ -> false, CHole (constr_loc c, None), c in
      let h' = BFrec (false, has_cast) :: binders_fmts bs in
      let cofix = CCoFix (loc, lid, [lid, fix_binders bs, t', c']) in
      id, (((fk, h'), (ck, (rc, Some cofix))), ctx)
    ]
END

let ssrposetac (id, ((_, t), ctx)) gl =
  posetac id (pf_abs_ssrterm (get_ltacctx ctx) gl t) gl
  
TACTIC EXTEND ssrpose
| [ "pose" ssrfixfwd(ffwd) ] -> [ ssrposetac ffwd ]
| [ "pose" ssrcofixfwd(ffwd) ] -> [ ssrposetac ffwd ]
| [ "pose" ssrfwdid(id) ssrposefwd(fwd) ] -> [ ssrposetac (id, fwd) ]
END

(** The "set" tactic *)

(* type ssrsetfwd = ssrfwd * ssrdocc *)

let guard_setrhs s i = s.[i] = '{'

let pr_setrhs occ prc prlc c =
  if occ = nodocc then pr_guarded guard_setrhs prlc c else pr_docc occ ++ prc c

let pr_ssrsetfwd _ _ _ (((fmt,(t,ty)),ctx), docc) =
  let fwd = match ty with
  | Some ty -> (fmt, combineCG t ty (mkCCast dummy_loc) mkRCast), ctx
  | None -> (fmt, t), ctx in
  pr_fwd_guarded (pr_setrhs docc) (pr_setrhs docc) fwd

ARGUMENT EXTEND ssrsetfwd
TYPED AS ((ssrfwdfmt * (ssrpattern * ssrterm option)) * ssrltacctx) * ssrdocc
PRINTED BY pr_ssrsetfwd
| [ ":" lconstr(t) ":=" "{" ssrocc(occ) "}" ssrpattern(c) ] ->
  [ mkssrFwdCast FwdPose loc (mk_lterm t) c, mkocc occ ]
| [ ":" lconstr(t) ":=" ssrlpattern(c) ] ->
  [ mkssrFwdCast FwdPose loc (mk_lterm t) c, nodocc ]
| [ ":=" "{" ssrocc(occ) "}" ssrpattern(c) ] ->
  [ mkssrFwdVal FwdPose c, mkocc occ ]
| [ ":=" ssrlpattern(c) ] -> [ mkssrFwdVal FwdPose c, nodocc ]
END

let ssrsettac id (((_, (pat, pty)), ctx), (_, occ)) gl =
  let ist = get_ltacctx ctx in
  let pat = interp_pattern ist gl (T pat) pty in
  let cl, sigma, env = pf_concl gl, project gl, pf_env gl in
  let c, cl = 
    try fill_occ_pattern ~raise_NoMatch:true env sigma pat occ 1 cl
    with NoMatch -> redex_of_pattern pat, cl in
  if occur_existential c then errorstrm(str"The pattern"++spc()++
    pr_constr_pat c++spc()++str"did not match and has holes."++spc()++
    str"Did you mean pose?") else
  let c, cty =  match kind_of_term c with
  | Cast(t, DEFAULTcast, ty) -> t, ty
  | _ -> c, pf_type_of gl c in
  let cl' = mkLetIn (Name id, c, cty, cl) in
  tclTHEN (convert_concl cl') (introid id) gl

TACTIC EXTEND ssrset
| [ "set" ssrfwdid(id) ssrsetfwd(fwd) ssrclauses(clauses) ] ->
  [ tclCLAUSES (ssrsettac id fwd) clauses ]
END

(** The "have" tactic *)

(* type ssrhavefwd = ssrfwd * ssrhint *)

let pr_ssrhavefwd _ _ prt (fwd, hint) = pr_fwd fwd ++ pr_hint prt hint

ARGUMENT EXTEND ssrhavefwd TYPED AS ssrfwd * ssrhint PRINTED BY pr_ssrhavefwd
| [ ":" lconstr(t) ssrhint(hint) ] -> [ mkFwdHint ":" t, hint ]
| [ ":" lconstr(t) ":=" lconstr(c) ] -> [ mkFwdCast FwdHave loc t c, nohint ]
| [ ":=" lconstr(c) ] -> [ mkFwdVal FwdHave c, nohint ]
END

let intro_id_to_binder = List.map (function 
  | IpatId id ->
      let xloc, _ as x = bvar_lname (mkCVar dummy_loc id) in
      (FwdPose, [BFvar]),
        CLambdaN (dummy_loc, [[x], Default Explicit, CHole (xloc, None)],
          CHole (dummy_loc, None))
  | _ -> anomaly "non-id accepted as binder")

let binder_to_intro_id = List.map (function
  | (FwdPose, [BFvar]), CLambdaN (_,[ids,_,_],_)
  | (FwdPose, [BFdecl _]), CLambdaN (_,[ids,_,_],_) ->
      List.map (function (_, Name id) -> IpatId id | _ -> IpatAnon) ids
  | (FwdPose, [BFdef _]), CLetIn (_,(_,Name id),_,_) -> [IpatId id]
  | (FwdPose, [BFdef _]), CLetIn (_,(_,Anonymous),_,_) -> [IpatAnon]
  | _ -> anomaly "ssrbinder is not a binder")

let pr_ssrhavefwdwbinders _ _ prt (hpats, (fwd, hint)) =
  pr_hpats hpats ++ pr_fwd fwd ++ pr_hint prt hint

ARGUMENT EXTEND ssrhavefwdwbinders
  TYPED AS ssrhpats * (ssrfwd * ssrhint) PRINTED BY pr_ssrhavefwdwbinders
| [ ssrhpats(pats) ssrbinder_list(bs) ssrhavefwd(fwd) ] ->
  [ let ((clr, pats), binders), simpl = pats in
    let allbs = intro_id_to_binder binders @ bs in
    let allbinders = binders @ List.flatten (binder_to_intro_id bs) in
    (((clr, pats), allbinders), simpl), (bind_fwd allbs (fst fwd), snd fwd) ]
END

(* Tactic. *)

let basecuttac name c = apply (mkApp (mkSsrConst name, [|c|]))

let havegentac ist t gl =
  let c = pf_abs_ssrterm ist gl t in
  apply_type (mkArrow (pf_type_of gl c) (pf_concl gl)) [c] gl

let havetac ((((clr, pats), binders), simpl), ((((fk, _), t), ctx), hint))
      suff namefst gl 
=
 (* honour automatic introduction flag *)
 let binders = if Flags.is_auto_intros () then binders else [] in
 let ist, concl = get_ltacctx ctx, pf_concl gl in
 let itac_c = introstac ~ist (IpatSimpl(clr,Nop) :: pats) in
 let itac, id, clr = introstac ~ist pats, tclIDTAC, cleartac clr in
 let binderstac n =
   let rec aux = function 0 -> [] | n -> IpatAnon :: aux (n-1) in
   tclTHEN (if binders <> [] then introstac ~ist (aux n) else tclIDTAC)
     (introstac ~ist binders) in
 let simpltac = introstac ~ist simpl in
 let hint = hinttac ist true hint in
 let cuttac t gl = basecuttac "ssr_have" t gl in
 let mkt t = mk_term ' ' t in
 let mkl t = (' ', (t, None)) in
 let interp t = pf_abs_ssrterm ist gl t in
 let interp_ty t = let a,b,_ = pf_interp_ty ist gl t in a, b in
 let ct, cty, hole, loc = match t with
   | _, (_, Some (CCast (loc, ct, CastConv (_, cty)))) ->
     mkt ct, mkt cty, mkt (mkCHole dummy_loc), loc
   | _, (_, Some ct) ->
     mkt ct, mkt (mkCHole dummy_loc), mkt (mkCHole dummy_loc), dummy_loc
   | _, (RCast (loc, ct, CastConv (_, cty)), None) ->
     mkl ct, mkl cty, mkl mkRHole, loc
   | _, (t, None) -> mkl t, mkl mkRHole, mkl mkRHole, dummy_loc in
 let cut, sol, itac1, itac2 =
   match fk, namefst, suff with
   | FwdHave, true, true ->
     errorstrm (str"Suff have does not accept a proof term")
   | FwdHave, false, true ->
     let cty = combineCG cty hole (mkCArrow loc) mkRArrow in
     let t = interp (combineCG ct cty (mkCCast loc) mkRCast) in
     let ty = pf_type_of gl t in
     let ctx, _ = decompose_prod_n 1 ty in
     let assert_is_conv gl =
       try convert_concl (compose_prod ctx concl) gl
       with _ -> errorstrm (str "Given proof term is not of type " ++
         pr_constr (mkArrow (mkVar (id_of_string "_")) concl)) in
     ty, tclTHEN assert_is_conv (apply t), id, itac_c
   | FwdHave, false, false ->
     let t = interp (combineCG ct cty (mkCCast loc) mkRCast) in
     pf_type_of gl t, apply t, id, tclTHEN itac_c simpltac
   | _, true, true   -> mkArrow (snd (interp_ty cty)) concl, hint, itac, clr
   | _, false, true  -> mkArrow (snd (interp_ty cty)) concl, hint, id, itac_c
   | _, false, false -> 
     let n, cty = interp_ty cty in
     cty, tclTHEN (binderstac n) hint, id, tclTHEN itac_c simpltac
   | _, true, false -> assert false in
 tclTHENS (cuttac cut) [ tclTHEN sol itac1; itac2 ] gl

TACTIC EXTEND ssrhave
| [ "have" ssrhavefwdwbinders(fwd) ] ->
  [ havetac fwd false false ]
END

TACTIC EXTEND ssrhavesuff
| [ "have" "suff" ssrhpats_nobs(pats) ssrhavefwd(fwd) ] ->
  [ havetac (pats, fwd) true false ]
END

TACTIC EXTEND ssrhavesuffices
| [ "have" "suffices" ssrhpats_nobs(pats) ssrhavefwd(fwd) ] ->
  [ havetac (pats, fwd) true false ]
END

TACTIC EXTEND ssrsuffhave
| [ "suff" "have" ssrhpats_nobs(pats) ssrhavefwd(fwd) ] ->
  [ havetac (pats, fwd) true true ]
END

TACTIC EXTEND ssrsufficeshave
| [ "suffices" "have" ssrhpats_nobs(pats) ssrhavefwd(fwd) ] ->
  [ havetac (pats, fwd) true true ]
END

(** The "suffice" tactic *)

ARGUMENT EXTEND ssrsufffwd
  TYPED AS ssrhpats * (ssrfwd * ssrhint) PRINTED BY pr_ssrhavefwdwbinders
| [ ssrhpats(pats) ssrbinder_list(bs)  ":" lconstr(t) ssrhint(hint) ] ->
  [ let ((clr, pats), binders), simpl = pats in
    let allbs = intro_id_to_binder binders @ bs in
    let allbinders = binders @ List.flatten (binder_to_intro_id bs) in
    let fwd = mkFwdHint ":" t in
    (((clr, pats), allbinders), simpl), (bind_fwd allbs fwd, hint) ]
END

let sufftac ((((clr, pats),binders),simpl), (((_, c), ctx), hint)) =
  (* honour automatic introduction flag *)
  let binders = if Flags.is_auto_intros () then binders else [] in
  let ist = get_ltacctx ctx in
  let htac = tclTHEN (introstac ~ist pats) (hinttac ist true hint) in
  let c = match c with
  | (a, (b, Some (CCast (_, _, CastConv (_, cty))))) -> a, (b, Some cty)
  | (a, (RCast (_, _, CastConv (_, cty)), None)) -> a, (cty, None)
  | _ -> anomaly "suff: ssr cast hole deleted by typecheck" in
  let ctac gl = basecuttac "ssr_suff" (pi2 (pf_interp_ty ist gl c)) gl in
  tclTHENS ctac [htac; tclTHEN (cleartac clr) (introstac ~ist (binders@simpl))]

TACTIC EXTEND ssrsuff
| [ "suff" ssrsufffwd(fwd) ] -> [ sufftac fwd ]
END

TACTIC EXTEND ssrsuffices
| [ "suffices" ssrsufffwd(fwd) ] -> [ sufftac fwd ]
END

(** The "wlog" (Without Loss Of Generality) tactic *)

(* type ssrwgen = ssrclear * ssrhyp * string *)

let pr_wgen = function 
  | (clr, Some (SsrHyp (loc, c), guard)) ->
     spc () ++ pr_clear mt clr ++
       pr_term (mk_term guard.[0] (CRef (Ident (loc, c))))
  | (clr, None) -> spc () ++ pr_clear mt clr
let pr_ssrwgen _ _ _ = pr_wgen

(* no globwith for char *)
ARGUMENT EXTEND ssrwgen
  TYPED AS ssrclear * (ssrhyp * string) option PRINTED BY pr_ssrwgen
| [ ssrclear_ne(clr) ] -> [ clr, None ]
| [ ssrterm(id) ] -> [ [], Some (ssrhyp_of_ssrterm id) ]
END

(* type ssrwlogfwd = ssrwgen list * ssrfwd *)

let pr_ssrwlogfwd _ _ _ (gens, t) =
  str ":" ++ pr_list mt pr_wgen gens ++ spc() ++ pr_fwd t

ARGUMENT EXTEND ssrwlogfwd TYPED AS ssrwgen list * ssrfwd
                         PRINTED BY pr_ssrwlogfwd
| [ ":" ssrwgen_list(gens) "/" lconstr(t) ] -> [ gens, mkFwdHint "/" t]
END

let wlogtac (((clr0, pats),_),_) (gens, ((_, ct), ctx)) hint suff gl =
  let ist = get_ltacctx ctx in
  let mkabs = function 
    | (_, (Some (SsrHyp (_, x), mode))) -> (match mode with
      | "@" -> mkNamedProd_or_LetIn (pf_get_hyp gl x)
      | _ -> mkNamedProd x (pf_get_hyp_typ gl x))
    | _, None -> fun x -> x
  in
  let mkclr = function 
   | (clr, Some (x, _)) -> fun clrs -> cleartac clr :: cleartac [x] :: clrs
   | (clr, None) -> fun clrs -> cleartac clr :: clrs in
  let mkpats = function
   | (_, Some (SsrHyp (_, x), _)) -> fun pats -> IpatId x :: pats
   | _ -> fun x -> x in
  let ct = match ct with
  | (a, (b, Some (CCast (_, _, CastConv (_, cty))))) -> a, (b, Some cty)
  | (a, (RCast (_, _, CastConv (_, cty)), None)) -> a, (cty, None)
  | _ -> anomaly "wlog: ssr cast hole deleted by typecheck" in
  let cl0 = mkArrow (pi2 (pf_interp_ty ist gl ct)) (pf_concl gl) in
  let cl0 = if not suff then cl0 else let _,t,_ = destProd cl0 in t in
  let c = List.fold_right mkabs gens cl0 in
  let tacipat = introstac ~ist pats in
  let tacigens = 
    tclTHEN (tclTHENLIST (List.rev(List.fold_right mkclr gens [cleartac clr0])))
      (introstac ~ist (List.fold_right mkpats gens [])) in
  let hinttac = hinttac ist true hint in
  tclTHENS (basecuttac "ssr_wlog" c)
    (if suff then [tclTHEN hinttac tacipat; tacigens]
     else [hinttac; tclTHEN tacigens tacipat]) gl

TACTIC EXTEND ssrwlog
| [ "wlog" ssrhpats_nobs(pats) ssrwlogfwd(fwd) ssrhint(hint) ] ->
  [ wlogtac pats fwd hint false ]
END

TACTIC EXTEND ssrwlogs
| [ "wlog" "suff" ssrhpats_nobs(pats) ssrwlogfwd(fwd) ssrhint(hint) ] ->
  [ wlogtac pats fwd hint true ]
END

TACTIC EXTEND ssrwlogss
| [ "wlog" "suffices" ssrhpats_nobs(pats) ssrwlogfwd(fwd) ssrhint(hint) ]->
  [ wlogtac pats fwd hint true ]
END

TACTIC EXTEND ssrwithoutloss
| [ "without" "loss" ssrhpats_nobs(pats) ssrwlogfwd(fwd) ssrhint(hint) ] ->
  [ wlogtac pats fwd hint false ]
END

TACTIC EXTEND ssrwithoutlosss
| [ "without" "loss" "suff" 
    ssrhpats_nobs(pats) ssrwlogfwd(fwd) ssrhint(hint) ] ->
  [ wlogtac pats fwd hint true ]
END

TACTIC EXTEND ssrwithoutlossss
| [ "without" "loss" "suffices" 
    ssrhpats_nobs(pats) ssrwlogfwd(fwd) ssrhint(hint) ]->
  [ wlogtac pats fwd hint true ]
END

(** Canonical Structure alias *)

let def_body : Vernacexpr.definition_expr Gram.Entry.e = Obj.magic
   (Grammar.Entry.find (Obj.magic gallina_ext) "vernac:def_body") in

GEXTEND Gram
  GLOBAL: gallina_ext;

  gallina_ext:
      (* Canonical structure *)
     [[ IDENT "Canonical"; qid = Constr.global ->
	  Vernacexpr.VernacCanonical (AN qid)
      | IDENT "Canonical"; ntn = Prim.by_notation ->
	  Vernacexpr.VernacCanonical (ByNotation ntn)
      | IDENT "Canonical"; qid = Constr.global;
          d = def_body ->
          let s = coerce_reference_to_id qid in
	  Vernacexpr.VernacDefinition
	    ((Decl_kinds.Global,false,Decl_kinds.CanonicalStructure),
             (dummy_loc,s),(d  ),
             (fun _ -> Recordops.declare_canonical_structure))
(*It seems there is not need for these:
      (* Canonical structure *)
      | IDENT "Canonical"; IDENT "Structure"; qid = Constr.global ->
	  Vernacexpr.VernacCanonical (AN qid)
      | IDENT "Canonical"; IDENT "Structure"; ntn = Prim.by_notation ->
	  Vernacexpr.VernacCanonical (ByNotation ntn)
      | IDENT "Canonical"; IDENT "Structure"; qid = Constr.global;
          d = def_body ->
          let s = coerce_reference_to_id qid in
	  Vernacexpr.VernacDefinition
	    ((Decl_kinds.Global,false,Decl_kinds.CanonicalStructure),
             (dummy_loc,s),(d  ),
             (fun _ -> Recordops.declare_canonical_structure))
*)
  ]];
END

(** 9. Keyword compatibility fixes. *)

(* Coq v8.1 notation uses "by" and "of" quasi-keywords, i.e., reserved *)
(* identifiers used as keywords. This is incompatible with ssreflect.v *)
(* which makes "by" and "of" true keywords, because of technicalities  *)
(* in the internal lexer-parser API of Coq. We patch this here by      *)
(* adding new parsing rules that recognize the new keywords.           *)
(*   To make matters worse, the Coq grammar for tactics fails to       *)
(* export the non-terminals we need to patch. Fortunately, the CamlP5  *)
(* API provides a backdoor access (with loads of Obj.magic trickery).  *)

(* Coq v8.3 defines "by" as a keyword, some hacks are not needed any   *)
(* longer and thus comment out. Such comments are marked with v8.3     *)

let tac_ent = List.fold_left Grammar.Entry.find (Obj.magic simple_tactic) in
let hypident_ent =
  tac_ent ["clause_dft_all"; "in_clause"; "hypident_occ"; "hypident"] in
let id_or_meta : Obj.t Gram.Entry.e = Obj.magic
   (Grammar.Entry.find hypident_ent "id_or_meta") in
(*v8.3
let by_tactic : raw_tactic_expr Gram.Entry.e = Obj.magic
  (tac_ent ["by_tactic"]) in
let opt_by_tactic : raw_tactic_expr option Gram.Entry.e = Obj.magic
  (tac_ent ["opt_by_tactic"]) in
*)
let hypident : (Obj.t * hyp_location_flag) Gram.Entry.e =
   Obj.magic hypident_ent in
GEXTEND Gram
  GLOBAL: (*v8.3 opt_by_tactic by_tactic*) hypident;
(*v8.3
opt_by_tactic: [
  [ "by"; tac = tactic_expr LEVEL "3" -> Some tac ] ];
by_tactic: [
  [ "by"; tac = tactic_expr LEVEL "3" -> TacComplete tac ] ];
*)
hypident: [
  [ "("; IDENT "type"; "of"; id = id_or_meta; ")" -> id, InHypTypeOnly
  | "("; IDENT "value"; "of"; id = id_or_meta; ")" -> id, InHypValueOnly
  ] ];
END

GEXTEND Gram
  GLOBAL: hloc (*v8.3 by_arg_tac*);
hloc: [
  [ "in"; "("; "Type"; "of"; id = ident; ")" -> 
    HypLocation ((Util.dummy_loc,id), InHypTypeOnly)
  | "in"; "("; IDENT "Value"; "of"; id = ident; ")" -> 
    HypLocation ((Util.dummy_loc,id), InHypValueOnly)
  ] ];
(*v8.3
by_arg_tac: [
  [ "by"; tac = tactic_expr LEVEL "3" -> Some tac ] ];
*)
END

(*v8.3
open Rewrite
 
let pr_ssrrelattr prc _ _ (a, c) = pr_id a ++ str " proved by " ++ prc c

ARGUMENT EXTEND ssrrelattr TYPED AS ident * constr PRINTED BY pr_ssrrelattr
  [ ident(a) "proved" "by" constr(c) ] -> [ a, c ]
END

GEXTEND Gram
  GLOBAL: ssrrelattr;
  ssrrelattr: [[ a = ident; IDENT "proved"; "by"; c = constr -> a, c ]];
END

let rec ssr_add_relation n d b deq pf_refl pf_sym pf_trans = function
  | [] ->
    Rewrite.declare_relation ~binders:b d deq n pf_refl pf_sym pf_trans
  | (aid, c) :: al -> match string_of_id aid with
  | "reflexivity" when pf_refl = None ->
    ssr_add_relation n d b deq (Some c) pf_sym pf_trans al
  | "symmetry" when pf_sym = None ->
    ssr_add_relation n d b deq pf_refl (Some c) pf_trans al
  | "transitivity" when pf_trans = None ->
    ssr_add_relation n d b deq pf_refl pf_sym (Some c) al
  | a -> Util.error ("bad attribute \"" ^ a ^ "\" in Add Relation")

VERNAC COMMAND EXTEND SsrAddRelation
 [ "Add" "Relation" constr(d) constr(deq) ssrrelattr_list(al) "as" ident(n) ]
 -> [ ssr_add_relation n d [] deq None None None al ]
END

VERNAC COMMAND EXTEND SsrAddParametricRelation
 [ "Add" "Parametric" "Relation" binders_let(b) ":"
         constr(d) constr(deq) ssrrelattr_list(al) "as" ident(n) ]
 -> [ ssr_add_relation n d b deq None None None al ]
END
*)


(* We wipe out all the keywords generated by the grammar rules we defined. *)
(* The user is supposed to Require Import ssreflect or Require ssreflect   *)
(* and Import ssreflectSsrSyntax to obtain these keywords and as a         *)
(* consequence the extended ssreflect grammar.                             *)
let () = Lexer.unfreeze frozen_lexer ;;

