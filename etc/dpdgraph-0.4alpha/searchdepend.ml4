(*~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~*)
(*            This file is part of the DpdGraph tools.                        *)
(*   Copyright (C) 2009-2013 Anne Pacalet (Anne.Pacalet@free.fr)              *)
(*                  and Yves Bertot (Yves.Bertot@inria.fr)                    *)
(*             ~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~                                *)
(*        This file is distributed under the terms of the                     *)
(*         GNU Lesser General Public License Version 2.1                      *)
(*        (see the enclosed LICENSE file for mode details)                    *)
(*~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~*)


open Pp

module Data = struct
  type t = int Globnames.Refmap.t

  let empty = Globnames.Refmap.empty

  let add gref d =
    let n = try  Globnames.Refmap.find gref d with Not_found -> 0 in
    Globnames.Refmap.add gref (n+1) d

      (* [f gref n acc] *)
  let fold f d acc = Globnames.Refmap.fold f d acc
end

let add_identifier (x:Names.identifier)(d:Data.t) =
  failwith
    ("SearchDep does not expect to find plain identifiers :" ^
     Names.string_of_id x)

let add_sort (s:Term.sorts)(d:Data.t) = d

let add_constant (cst:Names.constant)(d:Data.t) =
  Data.add (Globnames.ConstRef cst) d

let add_inductive ((k,i):Names.inductive)(d:Data.t) =
  Data.add (Globnames.IndRef (k, i)) d

let add_constructor(((k,i),j):Names.constructor)(d:Data.t) =
  Data.add (Globnames.ConstructRef ((k,i),j)) d

let collect_long_names (c:Term.constr) (acc:Data.t) =
  let rec add c acc =
    match Term.kind_of_term c with
        Term.Rel _ -> acc
      | Term.Var x -> add_identifier x acc
      | Term.Meta _ -> assert false
      | Term.Evar _ -> assert false
      | Term.Sort s -> add_sort s acc
      | Term.Cast(c,_,t) -> add c (add t acc)
      | Term.Prod(n,t,c) -> add t (add c acc)
      | Term.Lambda(n,t,c) -> add t (add c acc)
      | Term.LetIn(_,v,t,c) -> add v (add t (add c acc))
      | Term.App(c,ca) -> add c (Array.fold_right add ca acc)
      | Term.Const (cst,univ) -> add_constant cst acc (* abstraction-barrier-breaking hack! *)
      | Term.Ind (i,univ) -> add_inductive i acc (* abstraction-barrier-breaking hack! *)
      | Term.Construct (cnst,univ) -> add_constructor cnst acc (* abstraction-barrier-breaking hack! *)
      | Term.Case({Term.ci_ind=i},c,t,ca) ->
          add_inductive i (add c (add t (Array.fold_right add ca acc)))
      | Term.Fix(_,(_,ca,ca')) ->
          Array.fold_right add ca (Array.fold_right add ca' acc)
      | Term.CoFix(_,(_,ca,ca')) ->
          Array.fold_right add ca (Array.fold_right add ca' acc)
  in add c acc

exception NoDef of Globnames.global_reference

let collect_dependance gref =
  match gref with
  | Globnames.VarRef _ -> assert false
  | Globnames.ConstRef cst ->
      let cb = Environ.lookup_constant cst (Global.env()) in
      let c = match cb.Declarations.const_body with
        | Declarations.Def c -> Lazyconstr.force c
        | Declarations.OpaqueDef c -> Lazyconstr.force_opaque c
        | Declarations.Undef _ -> raise (NoDef gref)
      in
      collect_long_names c Data.empty
  | Globnames.IndRef i | Globnames.ConstructRef (i,_) ->
      let _, indbody = Global.lookup_inductive i in
      let ca = indbody.Declarations.mind_user_lc in
        Array.fold_right collect_long_names ca Data.empty

let display_dependance gref =
  let display d =
    let pp gr n s =
      [< Printer.pr_global gr ++ str "(" ++ int n ++ str ")" ++ spc() ++s >]
    in
      Pp.msgnl [< str"[" ++ ((Data.fold pp) d (str "]")) >]
  in try let data = collect_dependance gref in display data
  with NoDef gref ->
    Pp.msgerrnl [< Printer.pr_global gref ++ str " has no value" >]

VERNAC COMMAND EXTEND Searchdepend
   ["SearchDepend" global(ref) ] -> [ display_dependance (Nametab.global ref) ]
END
