
type __ = Obj.t

val negb : bool -> bool

type ('a, 'b) sum =
| Inl of 'a
| Inr of 'b

val fst : ('a1*'a2) -> 'a1

val snd : ('a1*'a2) -> 'a2

val app : 'a1 list -> 'a1 list -> 'a1 list

val id : __ -> __

type 'a sig0 = 'a
  (* singleton inductive, whose constructor was exist *)

type 'a sig2 = 'a
  (* singleton inductive, whose constructor was exist2 *)

type ('a, 'p) sigT =
| ExistT of 'a * 'p



type ('a, 'b) arrow = 'a -> 'b

type ('a, 'b) iffT = ('a -> 'b)*('b -> 'a)

type ('a, 'r) symmetric = 'a -> 'a -> 'r -> 'r

val symmetry : ('a1, 'a2) symmetric -> 'a1 -> 'a1 -> 'a2 -> 'a2

type ('a, 'r) transitive = 'a -> 'a -> 'a -> 'r -> 'r -> 'r

val transitivity :
  ('a1, 'a2) transitive -> 'a1 -> 'a1 -> 'a1 -> 'a2 -> 'a2 -> 'a2

type ('a, 'r, 'x) subrelation = 'a -> 'a -> 'r -> 'x

val iffT_Symmetric : (__, __) iffT -> (__, __) iffT

val iffT_Transitive : (__, __) iffT -> (__, __) iffT -> (__, __) iffT

val iffT_arrow_subrelation : (__, __) iffT -> (__, __) arrow

val iffT_flip_arrow_subrelation : (__, __) iffT -> (__, __) arrow

val trans_co_eq_inv_arrow_morphism_obligation_1 :
  ('a1, 'a2) transitive -> 'a1 -> 'a1 -> 'a2 -> 'a1 -> 'a1 -> (__, __) arrow

val trans_co_eq_inv_arrow_morphism :
  ('a1, 'a2) transitive -> 'a1 -> 'a1 -> 'a2 -> 'a1 -> 'a1 -> (__, __) arrow

val flip2 : ('a1, 'a2, 'a3) subrelation -> ('a1, 'a2, 'a3) subrelation

val in_dec : ('a1 -> 'a1 -> bool) -> 'a1 -> 'a1 list -> bool

val remove : ('a1 -> 'a1 -> bool) -> 'a1 -> 'a1 list -> 'a1 list

val list_eq_dec : ('a1 -> 'a1 -> bool) -> 'a1 list -> 'a1 list -> bool

val map : ('a1 -> 'a2) -> 'a1 list -> 'a2 list

val fold_right : ('a2 -> 'a1 -> 'a1) -> 'a1 -> 'a2 list -> 'a1

type 'a eq_dec = 'a -> 'a -> bool

type ('a, 'b) iffT0 = ('a -> 'b)*('b -> 'a)

type 'a eqDec =
  'a -> 'a -> bool
  (* singleton inductive, whose constructor was Build_EqDec *)

val eqdec : 'a1 eqDec -> 'a1 -> 'a1 -> bool

val eqDec_list : 'a1 eqDec -> 'a1 list eqDec

val eqDec_prod : 'a1 eqDec -> 'a2 eqDec -> ('a1*'a2) eqDec

val eqDec_string : string eqDec

val comp : ('a2 -> 'a3) -> ('a1 -> 'a2) -> 'a1 -> 'a3

val list_biind :
  'a3 -> ('a1 -> 'a1 list -> 'a2 -> 'a2 list -> 'a3 -> 'a3) -> 'a1 list ->
  'a2 list -> 'a3

val in_some_dec :
  'a2 eqDec -> 'a2 -> 'a1 list -> ('a1 -> 'a2 list) -> 'a1 sig2 option

val eq_dec_in_list :
  ('a1 -> 'a1 -> bool) -> 'a1 -> 'a1 list -> 'a1 -> (__ -> 'a2) -> (__ ->
  'a2) -> 'a2

val nxorb : bool -> bool -> bool

val zip : ('a1 -> 'a2 -> 'a3) -> 'a1 list -> 'a2 list -> 'a3 list

val list_2_elems_dec : 'a1 list -> ('a1, ('a1, __) sigT) sigT option

val in_map_inv_sig : 'a1 eqDec -> ('a2 -> 'a1) -> 'a2 list -> 'a1 -> 'a2

val list_union : 'a1 list -> ('a1 -> 'a2 list) -> 'a2 list

type ('a, 'p) forallT =
| ForallT_nil
| ForallT_cons of 'a * 'a list * 'p * ('a, 'p) forallT

val forallT_inv : 'a1 -> 'a1 list -> ('a1, 'a2) forallT -> 'a2

val forallT_inv_tail :
  'a1 -> 'a1 list -> ('a1, 'a2) forallT -> ('a1, 'a2) forallT

val forallT_forall :
  'a1 eqDec -> 'a1 list -> (('a1, 'a2) forallT, 'a1 -> __ -> 'a2) iffT0

val forallT_mp :
  'a1 list -> ('a1, 'a2) forallT -> ('a1, 'a2 -> 'a3) forallT -> ('a1, 'a3)
  forallT

val forallT_act :
  'a1 list -> ('a1 -> 'a2 -> 'a3) -> ('a1, 'a2) forallT -> ('a1, 'a3) forallT

val forallT_act_iff :
  'a1 list -> ('a1 -> ('a2, 'a3) iffT0) -> (('a1, 'a2) forallT, ('a1, 'a3)
  forallT) iffT0

val forallT_sig_elim : 'a1 list -> ('a1, 'a2) forallT -> 'a2 list

val forall_ForallT : 'a1 eqDec -> 'a1 list -> (__, ('a1, __) forallT) iffT0

type ('a, 'p) existsT =
| ExistsT_cons_hd of 'a * 'a list * 'p
| Exists_cons_tl of 'a * 'a list * ('a, 'p) existsT

val in_zip_pair_23_sig_1 :
  'a2 eqDec -> 'a3 eqDec -> 'a1 list -> 'a2 list -> 'a3 list -> 'a2 -> 'a3 ->
  'a1

val forallT_dec_E_sumbool :
  'a1 list -> ('a1, bool) forallT -> (('a1, __) existsT, ('a1, __) forallT)
  sum

val forallT_map :
  ('a1 -> 'a2) -> 'a1 list -> (('a2, 'a3) forallT, ('a1, 'a3) forallT) iffT0

type 'expr fLANG = { ipse : ('expr -> 'expr list);
                     ipse_rect : (__ -> ('expr -> ('expr -> __ -> __) -> __)
                                 -> 'expr -> __);
                     conn : ('expr -> 'expr list -> 'expr) }

val ipse_rect :
  'a1 eqDec -> 'a1 fLANG -> ('a1 -> ('a1 -> __ -> 'a2) -> 'a2) -> 'a1 -> 'a2

type ('expr, 'ix) iXEXP =
  'expr -> 'ix option
  (* singleton inductive, whose constructor was Build_IXEXP *)

val var_dec :
  'a1 eqDec -> 'a1 fLANG -> ('a2 -> 'a1) -> ('a1, 'a2) iXEXP -> 'a1 -> 'a2
  option

type 'formula lOGLANG = { atm : (string -> 'formula);
                          fV : (string -> 'formula);
                          aTMVAR : ('formula, string) iXEXP;
                          fVVAR : ('formula, string) iXEXP }

type aSubst = string -> string

type 'formula fSubst = string -> 'formula

type 'formula afSubst = aSubst*'formula fSubst

val allVars :
  'a1 eqDec -> 'a1 fLANG -> ('a2 -> 'a1) -> ('a1, 'a2) iXEXP -> 'a1 -> 'a2
  list

val fmlAtms : 'a1 eqDec -> 'a1 fLANG -> 'a1 lOGLANG -> 'a1 -> string list

val fmlFVs : 'a1 eqDec -> 'a1 fLANG -> 'a1 lOGLANG -> 'a1 -> string list

val fmlSubst :
  'a1 eqDec -> 'a1 fLANG -> 'a1 lOGLANG -> 'a1 afSubst -> 'a1 -> 'a1

val i_a : aSubst

val i_f : 'a1 eqDec -> 'a1 fLANG -> 'a1 lOGLANG -> 'a1 fSubst

val fml_matchsub_Atm :
  'a1 eqDec -> 'a1 fLANG -> 'a1 lOGLANG -> 'a1 -> 'a1 -> aSubst

val fml_matchsub_FV :
  'a1 eqDec -> 'a1 fLANG -> 'a1 lOGLANG -> 'a1 -> 'a1 -> 'a1 fSubst

type ('formula, 'structr) sTRLANG = { sV : (string -> 'structr);
                                      fS : ('formula -> 'structr);
                                      sVVAR : ('structr, string) iXEXP;
                                      fSVAR : ('structr, 'formula) iXEXP;
                                      sgnips : ('structr -> bool list) }

type ('formula, 'structr) sequent =
| Sequent of 'structr * 'structr

type ('formula, 'structr) rule =
  ('formula, 'structr) sequent list*('formula, 'structr) sequent

type ('formula, 'structr) dISPCALC = ('formula, 'structr) rule list

val antec :
  'a1 eqDec -> 'a1 fLANG -> 'a1 lOGLANG -> 'a2 eqDec -> 'a2 fLANG -> ('a1,
  'a2) sTRLANG -> ('a1, 'a2) sequent -> 'a2

val succ :
  'a1 eqDec -> 'a1 fLANG -> 'a1 lOGLANG -> 'a2 eqDec -> 'a2 fLANG -> ('a1,
  'a2) sTRLANG -> ('a1, 'a2) sequent -> 'a2

val conclRule :
  'a1 eqDec -> 'a1 fLANG -> 'a1 lOGLANG -> 'a2 eqDec -> 'a2 fLANG -> ('a1,
  'a2) sTRLANG -> ('a1, 'a2) rule -> ('a1, 'a2) sequent

val premsRule :
  'a1 eqDec -> 'a1 fLANG -> 'a1 lOGLANG -> 'a2 eqDec -> 'a2 fLANG -> ('a1,
  'a2) sTRLANG -> ('a1, 'a2) rule -> ('a1, 'a2) sequent list

val sequent_eq_dec :
  'a1 eqDec -> 'a1 fLANG -> 'a1 lOGLANG -> 'a2 eqDec -> 'a2 fLANG -> ('a1,
  'a2) sTRLANG -> ('a1, 'a2) sequent -> ('a1, 'a2) sequent -> bool

val eqDec_sequent :
  'a1 eqDec -> 'a1 fLANG -> 'a1 lOGLANG -> 'a2 eqDec -> 'a2 fLANG -> ('a1,
  'a2) sTRLANG -> ('a1, 'a2) sequent eqDec

val rule_eq_dec :
  'a1 eqDec -> 'a1 fLANG -> 'a1 lOGLANG -> 'a2 eqDec -> 'a2 fLANG -> ('a1,
  'a2) sTRLANG -> ('a1, 'a2) rule -> ('a1, 'a2) rule -> bool

val eqDec_rule :
  'a1 eqDec -> 'a1 fLANG -> 'a1 lOGLANG -> 'a2 eqDec -> 'a2 fLANG -> ('a1,
  'a2) sTRLANG -> ('a1, 'a2) rule eqDec

val strIsFml_sig :
  'a1 eqDec -> 'a1 fLANG -> 'a1 lOGLANG -> 'a2 eqDec -> 'a2 fLANG -> ('a1,
  'a2) sTRLANG -> 'a2 -> 'a1

val strIsFml_dec :
  'a1 eqDec -> 'a1 fLANG -> 'a1 lOGLANG -> 'a2 eqDec -> 'a2 fLANG -> ('a1,
  'a2) sTRLANG -> 'a2 -> bool

val strCtnsFml_dec :
  'a1 eqDec -> 'a1 fLANG -> 'a1 lOGLANG -> 'a2 eqDec -> 'a2 fLANG -> ('a1,
  'a2) sTRLANG -> 'a2 -> bool

val strAtms :
  'a1 eqDec -> 'a1 fLANG -> 'a1 lOGLANG -> 'a2 eqDec -> 'a2 fLANG -> ('a1,
  'a2) sTRLANG -> 'a2 -> string list

val strFVs :
  'a1 eqDec -> 'a1 fLANG -> 'a1 lOGLANG -> 'a2 eqDec -> 'a2 fLANG -> ('a1,
  'a2) sTRLANG -> 'a2 -> string list

val strSVs :
  'a1 eqDec -> 'a1 fLANG -> 'a1 lOGLANG -> 'a2 eqDec -> 'a2 fLANG -> ('a1,
  'a2) sTRLANG -> 'a2 -> string list

val seqAtms :
  'a1 eqDec -> 'a1 fLANG -> 'a1 lOGLANG -> 'a2 eqDec -> 'a2 fLANG -> ('a1,
  'a2) sTRLANG -> ('a1, 'a2) sequent -> string list

val seqFVs :
  'a1 eqDec -> 'a1 fLANG -> 'a1 lOGLANG -> 'a2 eqDec -> 'a2 fLANG -> ('a1,
  'a2) sTRLANG -> ('a1, 'a2) sequent -> string list

val seqSVs :
  'a1 eqDec -> 'a1 fLANG -> 'a1 lOGLANG -> 'a2 eqDec -> 'a2 fLANG -> ('a1,
  'a2) sTRLANG -> ('a1, 'a2) sequent -> string list

type 'structr sSubst = string -> 'structr

type ('formula, 'structr) afsSubst = 'formula afSubst*'structr sSubst

val strSubst :
  'a1 eqDec -> 'a1 fLANG -> 'a1 lOGLANG -> 'a2 eqDec -> 'a2 fLANG -> ('a1,
  'a2) sTRLANG -> ('a1, 'a2) afsSubst -> 'a2 -> 'a2

val seqSubst :
  'a1 eqDec -> 'a1 fLANG -> 'a1 lOGLANG -> 'a2 eqDec -> 'a2 fLANG -> ('a1,
  'a2) sTRLANG -> ('a1, 'a2) afsSubst -> ('a1, 'a2) sequent -> ('a1, 'a2)
  sequent

val ruleSubst :
  'a1 eqDec -> 'a1 fLANG -> 'a1 lOGLANG -> 'a2 eqDec -> 'a2 fLANG -> ('a1,
  'a2) sTRLANG -> ('a1, 'a2) afsSubst -> ('a1, 'a2) rule -> ('a1, 'a2) rule

val i_s :
  'a1 eqDec -> 'a1 fLANG -> 'a1 lOGLANG -> 'a2 eqDec -> 'a2 fLANG -> ('a1,
  'a2) sTRLANG -> 'a2 sSubst

val str_matchsub_Atm :
  'a1 eqDec -> 'a1 fLANG -> 'a1 lOGLANG -> 'a2 eqDec -> 'a2 fLANG -> ('a1,
  'a2) sTRLANG -> 'a2 -> 'a2 -> aSubst

val str_matchsub_FV :
  'a1 eqDec -> 'a1 fLANG -> 'a1 lOGLANG -> 'a2 eqDec -> 'a2 fLANG -> ('a1,
  'a2) sTRLANG -> 'a2 -> 'a2 -> 'a1 fSubst

val str_matchsub_SV :
  'a1 eqDec -> 'a1 fLANG -> 'a1 lOGLANG -> 'a2 eqDec -> 'a2 fLANG -> ('a1,
  'a2) sTRLANG -> 'a2 -> 'a2 -> 'a2 sSubst

val seq_matchsub_Atm :
  'a1 eqDec -> 'a1 fLANG -> 'a1 lOGLANG -> 'a2 eqDec -> 'a2 fLANG -> ('a1,
  'a2) sTRLANG -> ('a1, 'a2) sequent -> ('a1, 'a2) sequent -> aSubst

val seq_matchsub_FV :
  'a1 eqDec -> 'a1 fLANG -> 'a1 lOGLANG -> 'a2 eqDec -> 'a2 fLANG -> ('a1,
  'a2) sTRLANG -> ('a1, 'a2) sequent -> ('a1, 'a2) sequent -> 'a1 fSubst

val seq_matchsub_SV :
  'a1 eqDec -> 'a1 fLANG -> 'a1 lOGLANG -> 'a2 eqDec -> 'a2 fLANG -> ('a1,
  'a2) sTRLANG -> ('a1, 'a2) sequent -> ('a1, 'a2) sequent -> 'a2 sSubst

val seq_matchsub :
  'a1 eqDec -> 'a1 fLANG -> 'a1 lOGLANG -> 'a2 eqDec -> 'a2 fLANG -> ('a1,
  'a2) sTRLANG -> ('a1, 'a2) sequent -> ('a1, 'a2) sequent -> ('a1, 'a2)
  afsSubst

val listseq_matchsub_Atm :
  'a1 eqDec -> 'a1 fLANG -> 'a1 lOGLANG -> 'a2 eqDec -> 'a2 fLANG -> ('a1,
  'a2) sTRLANG -> ('a1, 'a2) sequent list -> ('a1, 'a2) sequent list -> aSubst

val listseq_matchsub_FV :
  'a1 eqDec -> 'a1 fLANG -> 'a1 lOGLANG -> 'a2 eqDec -> 'a2 fLANG -> ('a1,
  'a2) sTRLANG -> ('a1, 'a2) sequent list -> ('a1, 'a2) sequent list -> 'a1
  fSubst

val listseq_matchsub_SV :
  'a1 eqDec -> 'a1 fLANG -> 'a1 lOGLANG -> 'a2 eqDec -> 'a2 fLANG -> ('a1,
  'a2) sTRLANG -> ('a1, 'a2) sequent list -> ('a1, 'a2) sequent list -> 'a2
  sSubst

val listseq_matchsub :
  'a1 eqDec -> 'a1 fLANG -> 'a1 lOGLANG -> 'a2 eqDec -> 'a2 fLANG -> ('a1,
  'a2) sTRLANG -> ('a1, 'a2) sequent list -> ('a1, 'a2) sequent list -> ('a1,
  'a2) afsSubst

val listseqSubst_dec :
  'a1 eqDec -> 'a1 fLANG -> 'a1 lOGLANG -> 'a2 eqDec -> 'a2 fLANG -> ('a1,
  'a2) sTRLANG -> ('a1, 'a2) sequent list -> ('a1, 'a2) sequent list -> ('a1,
  'a2) afsSubst option

val ruleSubst_dec :
  'a1 eqDec -> 'a1 fLANG -> 'a1 lOGLANG -> 'a2 eqDec -> 'a2 fLANG -> ('a1,
  'a2) sTRLANG -> ('a1, 'a2) rule -> ('a1, 'a2) rule -> ('a1, 'a2) afsSubst
  option

val ruleInst_ruleSubst :
  'a1 eqDec -> 'a1 fLANG -> 'a1 lOGLANG -> 'a2 eqDec -> 'a2 fLANG -> ('a1,
  'a2) sTRLANG -> ('a1, 'a2) rule -> ('a1, 'a2) rule -> ('a1, 'a2) afsSubst

val a_spec : (string*string) list -> aSubst

val f_spec :
  'a1 eqDec -> 'a1 fLANG -> 'a1 lOGLANG -> (string*'a1) list -> 'a1 fSubst

val s_spec :
  'a1 eqDec -> 'a1 fLANG -> 'a1 lOGLANG -> 'a2 eqDec -> 'a2 fLANG -> ('a1,
  'a2) sTRLANG -> (string*'a2) list -> 'a2 sSubst

val af_spec :
  'a1 eqDec -> 'a1 fLANG -> 'a1 lOGLANG -> (string*string) list ->
  (string*'a1) list -> 'a1 afSubst

val afs_spec :
  'a1 eqDec -> 'a1 fLANG -> 'a1 lOGLANG -> 'a2 eqDec -> 'a2 fLANG -> ('a1,
  'a2) sTRLANG -> (string*string) list -> (string*'a1) list -> (string*'a2)
  list -> ('a1, 'a2) afsSubst

type ('formula, 'structr) dertree =
| Unf of ('formula, 'structr) sequent
| Der of ('formula, 'structr) sequent * ('formula, 'structr) rule
   * ('formula, 'structr) dertree list

val dertree_rect_gen :
  'a1 eqDec -> 'a1 fLANG -> 'a1 lOGLANG -> 'a2 eqDec -> 'a2 fLANG -> ('a1,
  'a2) sTRLANG -> 'a4 -> (('a1, 'a2) dertree -> ('a1, 'a2) dertree list ->
  'a3 -> 'a4 -> 'a4) -> (('a1, 'a2) sequent -> 'a3) -> (('a1, 'a2) sequent ->
  ('a1, 'a2) rule -> ('a1, 'a2) dertree list -> 'a4 -> 'a3) -> ('a1, 'a2)
  dertree -> 'a3

val dertree_eq_dec :
  'a1 eqDec -> 'a1 fLANG -> 'a1 lOGLANG -> 'a2 eqDec -> 'a2 fLANG -> ('a1,
  'a2) sTRLANG -> ('a1, 'a2) dertree -> ('a1, 'a2) dertree -> bool

val eqDec_dertree :
  'a1 eqDec -> 'a1 fLANG -> 'a1 lOGLANG -> 'a2 eqDec -> 'a2 fLANG -> ('a1,
  'a2) sTRLANG -> ('a1, 'a2) dertree eqDec

val nextUp :
  'a1 eqDec -> 'a1 fLANG -> 'a1 lOGLANG -> 'a2 eqDec -> 'a2 fLANG -> ('a1,
  'a2) sTRLANG -> ('a1, 'a2) dertree -> ('a1, 'a2) dertree list

val conclDT :
  'a1 eqDec -> 'a1 fLANG -> 'a1 lOGLANG -> 'a2 eqDec -> 'a2 fLANG -> ('a1,
  'a2) sTRLANG -> ('a1, 'a2) dertree -> ('a1, 'a2) sequent

val premsDT :
  'a1 eqDec -> 'a1 fLANG -> 'a1 lOGLANG -> 'a2 eqDec -> 'a2 fLANG -> ('a1,
  'a2) sTRLANG -> ('a1, 'a2) dertree -> ('a1, 'a2) sequent list

type ('formula, 'structr) deriv_prseq =
| Deriv_prseq_prem of ('formula, 'structr) sequent
| Deriv_prseq_ext of ('formula, 'structr) sequent list
   * ('formula, 'structr) sequent * ('formula, 'structr) rule
   * ('formula, 'structr) deriv_prseqs
and ('formula, 'structr) deriv_prseqs =
| Deriv_prseqs_nil
| Deriv_prseqs_cons of ('formula, 'structr) sequent
   * ('formula, 'structr) sequent list * ('formula, 'structr) deriv_prseq
   * ('formula, 'structr) deriv_prseqs

type ('formula, 'structr) deriv_rule = __

val deriv_prseqs_mut_rect :
  'a1 eqDec -> 'a1 fLANG -> 'a1 lOGLANG -> 'a2 eqDec -> 'a2 fLANG -> ('a1,
  'a2) sTRLANG -> ('a1, 'a2) dISPCALC -> ('a1, 'a2) sequent list -> (('a1,
  'a2) sequent -> __ -> 'a3) -> (('a1, 'a2) sequent list -> ('a1, 'a2)
  sequent -> ('a1, 'a2) rule -> __ -> __ -> ('a1, 'a2) deriv_prseqs -> 'a4 ->
  'a3) -> 'a4 -> (('a1, 'a2) sequent -> ('a1, 'a2) sequent list -> ('a1, 'a2)
  deriv_prseq -> 'a3 -> ('a1, 'a2) deriv_prseqs -> 'a4 -> 'a4) -> ('a1, 'a2)
  sequent list -> ('a1, 'a2) deriv_prseqs -> 'a4

val deriv_prseq_mut_rect :
  'a1 eqDec -> 'a1 fLANG -> 'a1 lOGLANG -> 'a2 eqDec -> 'a2 fLANG -> ('a1,
  'a2) sTRLANG -> ('a1, 'a2) dISPCALC -> ('a1, 'a2) sequent list -> (('a1,
  'a2) sequent -> __ -> 'a3) -> (('a1, 'a2) sequent list -> ('a1, 'a2)
  sequent -> ('a1, 'a2) rule -> __ -> __ -> ('a1, 'a2) deriv_prseqs -> 'a4 ->
  'a3) -> 'a4 -> (('a1, 'a2) sequent -> ('a1, 'a2) sequent list -> ('a1, 'a2)
  deriv_prseq -> 'a3 -> ('a1, 'a2) deriv_prseqs -> 'a4 -> 'a4) -> ('a1, 'a2)
  sequent -> ('a1, 'a2) deriv_prseq -> 'a3

val forallT_deriv_prseqs :
  'a1 eqDec -> 'a1 fLANG -> 'a1 lOGLANG -> 'a2 eqDec -> 'a2 fLANG -> ('a1,
  'a2) sTRLANG -> ('a1, 'a2) dISPCALC -> ('a1, 'a2) sequent list -> ('a1,
  'a2) sequent list -> (('a1, 'a2) sequent, ('a1, 'a2) deriv_prseq) forallT
  -> ('a1, 'a2) deriv_prseqs

val forallT_deriv_prseqs_iff :
  'a1 eqDec -> 'a1 fLANG -> 'a1 lOGLANG -> 'a2 eqDec -> 'a2 fLANG -> ('a1,
  'a2) sTRLANG -> ('a1, 'a2) dISPCALC -> ('a1, 'a2) sequent list -> ('a1,
  'a2) sequent list -> ((('a1, 'a2) sequent, ('a1, 'a2) deriv_prseq) forallT,
  ('a1, 'a2) deriv_prseqs) iffT0

val deriv_prseq_weak :
  'a1 eqDec -> 'a1 fLANG -> 'a1 lOGLANG -> 'a2 eqDec -> 'a2 fLANG -> ('a1,
  'a2) sTRLANG -> ('a1, 'a2) dISPCALC -> ('a1, 'a2) sequent list -> ('a1,
  'a2) sequent list -> ('a1, 'a2) sequent -> ('a1, 'a2) deriv_prseq -> ('a1,
  'a2) deriv_prseq

val deriv_prseq_tran :
  'a1 eqDec -> 'a1 fLANG -> 'a1 lOGLANG -> 'a2 eqDec -> 'a2 fLANG -> ('a1,
  'a2) sTRLANG -> ('a1, 'a2) dISPCALC -> ('a1, 'a2) sequent list -> ('a1,
  'a2) sequent list -> ('a1, 'a2) sequent -> ('a1, 'a2) deriv_prseqs -> ('a1,
  'a2) deriv_prseq -> ('a1, 'a2) deriv_prseq

val deriv_prseq_tran_afs :
  'a1 eqDec -> 'a1 fLANG -> 'a1 lOGLANG -> 'a2 eqDec -> 'a2 fLANG -> ('a1,
  'a2) sTRLANG -> ('a1, 'a2) dISPCALC -> ('a1, 'a2) sequent list -> ('a1,
  'a2) sequent list -> ('a1, 'a2) sequent -> ('a1, 'a2) afsSubst -> ('a1,
  'a2) deriv_prseqs -> ('a1, 'a2) deriv_prseq -> ('a1, 'a2) deriv_prseq

val deriv_rule_Inst :
  'a1 eqDec -> 'a1 fLANG -> 'a1 lOGLANG -> 'a2 eqDec -> 'a2 fLANG -> ('a1,
  'a2) sTRLANG -> ('a1, 'a2) dISPCALC -> ('a1, 'a2) rule -> ('a1, 'a2) rule
  -> ('a1, 'a2) deriv_rule -> ('a1, 'a2) deriv_rule

val deriv_rule_replace :
  'a1 eqDec -> 'a1 fLANG -> 'a1 lOGLANG -> 'a2 eqDec -> 'a2 fLANG -> ('a1,
  'a2) sTRLANG -> ('a1, 'a2) dISPCALC -> ('a1, 'a2) dISPCALC -> ('a1, 'a2)
  rule -> (('a1, 'a2) rule, ('a1, 'a2) deriv_rule) forallT -> ('a1, 'a2)
  deriv_rule -> ('a1, 'a2) deriv_rule

val cUT :
  'a1 eqDec -> 'a1 fLANG -> 'a1 lOGLANG -> 'a2 eqDec -> 'a2 fLANG -> ('a1,
  'a2) sTRLANG -> ('a1, 'a2) rule

val cUT_spec :
  'a1 eqDec -> 'a1 fLANG -> 'a1 lOGLANG -> 'a2 eqDec -> 'a2 fLANG -> ('a1,
  'a2) sTRLANG -> 'a1 -> 'a2 -> 'a2 -> ('a1, 'a2) afsSubst

val remove_rule :
  'a1 eqDec -> 'a1 fLANG -> 'a1 lOGLANG -> 'a2 eqDec -> 'a2 fLANG -> ('a1,
  'a2) sTRLANG -> ('a1, 'a2) rule -> ('a1, 'a2) rule list -> ('a1, 'a2) rule
  list

val lP_dec :
  'a1 eqDec -> 'a1 fLANG -> 'a1 lOGLANG -> 'a2 eqDec -> 'a2 fLANG -> ('a1,
  'a2) sTRLANG -> ('a1, 'a2) dertree list -> 'a1 -> ('a2, (('a1, 'a2) rule,
  (('a1, 'a2) dertree list, ('a1, 'a2) dertree) sigT) sigT) sigT option

val rP_dec :
  'a1 eqDec -> 'a1 fLANG -> 'a1 lOGLANG -> 'a2 eqDec -> 'a2 fLANG -> ('a1,
  'a2) sTRLANG -> ('a1, 'a2) dertree list -> 'a1 -> ('a2, (('a1, 'a2)
  dertree, (('a1, 'a2) rule, ('a1, 'a2) dertree list) sigT) sigT) sigT option

val right_cut_dec :
  'a1 eqDec -> 'a1 fLANG -> 'a1 lOGLANG -> 'a2 eqDec -> 'a2 fLANG -> ('a1,
  'a2) sTRLANG -> ('a1, 'a2) dertree list -> (('a1, 'a2) dertree, (('a1, 'a2)
  dertree, ('a2, 'a1) sigT) sigT) sigT option

type ('formula, 'structr) deriv_cofseq =
| Deriv_cofseq_ext of ('formula, 'structr) sequent list
   * ('formula, 'structr) sequent * ('formula, 'structr) rule
   * ('formula, 'structr) deriv_cofseqs
and ('formula, 'structr) deriv_cofseqs =
| Deriv_cofseqs_nil
| Deriv_cofseqs_cons of ('formula, 'structr) sequent
   * ('formula, 'structr) sequent list * ('formula, 'structr) deriv_cofseq
   * ('formula, 'structr) deriv_cofseqs

type ('formula, 'structr) deriv_cofprseq =
| Deriv_cofprseq_prem of ('formula, 'structr) sequent
| Deriv_cofprseq_ext of ('formula, 'structr) sequent list
   * ('formula, 'structr) sequent * ('formula, 'structr) rule
   * ('formula, 'structr) deriv_cofprseqs
and ('formula, 'structr) deriv_cofprseqs =
| Deriv_cofprseqs_nil
| Deriv_cofprseqs_cons of ('formula, 'structr) sequent
   * ('formula, 'structr) sequent list * ('formula, 'structr) deriv_cofprseq
   * ('formula, 'structr) deriv_cofprseqs

val deriv_cofseqs_mut_rect :
  'a1 eqDec -> 'a1 fLANG -> 'a1 lOGLANG -> 'a2 eqDec -> 'a2 fLANG -> ('a1,
  'a2) sTRLANG -> ('a1, 'a2) dISPCALC -> (('a1, 'a2) sequent list -> ('a1,
  'a2) sequent -> ('a1, 'a2) rule -> __ -> __ -> __ -> ('a1, 'a2)
  deriv_cofseqs -> 'a4 -> 'a3) -> 'a4 -> (('a1, 'a2) sequent -> ('a1, 'a2)
  sequent list -> ('a1, 'a2) deriv_cofseq -> 'a3 -> ('a1, 'a2) deriv_cofseqs
  -> 'a4 -> 'a4) -> ('a1, 'a2) sequent list -> ('a1, 'a2) deriv_cofseqs -> 'a4

val deriv_cofseq_mut_rect :
  'a1 eqDec -> 'a1 fLANG -> 'a1 lOGLANG -> 'a2 eqDec -> 'a2 fLANG -> ('a1,
  'a2) sTRLANG -> ('a1, 'a2) dISPCALC -> (('a1, 'a2) sequent list -> ('a1,
  'a2) sequent -> ('a1, 'a2) rule -> __ -> __ -> __ -> ('a1, 'a2)
  deriv_cofseqs -> 'a4 -> 'a3) -> 'a4 -> (('a1, 'a2) sequent -> ('a1, 'a2)
  sequent list -> ('a1, 'a2) deriv_cofseq -> 'a3 -> ('a1, 'a2) deriv_cofseqs
  -> 'a4 -> 'a4) -> ('a1, 'a2) sequent -> ('a1, 'a2) deriv_cofseq -> 'a3

val deriv_cofprseq_mut_rect :
  'a1 eqDec -> 'a1 fLANG -> 'a1 lOGLANG -> 'a2 eqDec -> 'a2 fLANG -> ('a1,
  'a2) sTRLANG -> ('a1, 'a2) dISPCALC -> ('a1, 'a2) sequent list -> (('a1,
  'a2) sequent -> __ -> 'a3) -> (('a1, 'a2) sequent list -> ('a1, 'a2)
  sequent -> ('a1, 'a2) rule -> __ -> __ -> __ -> ('a1, 'a2) deriv_cofprseqs
  -> 'a4 -> 'a3) -> 'a4 -> (('a1, 'a2) sequent -> ('a1, 'a2) sequent list ->
  ('a1, 'a2) deriv_cofprseq -> 'a3 -> ('a1, 'a2) deriv_cofprseqs -> 'a4 ->
  'a4) -> ('a1, 'a2) sequent -> ('a1, 'a2) deriv_cofprseq -> 'a3

type ('formula, 'structr) deriv_ncprseq = ('formula, 'structr) deriv_cofprseq

val forallT_deriv_cofseqs :
  'a1 eqDec -> 'a1 fLANG -> 'a1 lOGLANG -> 'a2 eqDec -> 'a2 fLANG -> ('a1,
  'a2) sTRLANG -> ('a1, 'a2) dISPCALC -> ('a1, 'a2) sequent list -> (('a1,
  'a2) sequent, ('a1, 'a2) deriv_cofseq) forallT -> ('a1, 'a2) deriv_cofseqs

val forallT_deriv_cofseqs_iff :
  'a1 eqDec -> 'a1 fLANG -> 'a1 lOGLANG -> 'a2 eqDec -> 'a2 fLANG -> ('a1,
  'a2) sTRLANG -> ('a1, 'a2) dISPCALC -> ('a1, 'a2) sequent list -> ((('a1,
  'a2) sequent, ('a1, 'a2) deriv_cofseq) forallT, ('a1, 'a2) deriv_cofseqs)
  iffT0

val forallT_deriv_cofprseqs :
  'a1 eqDec -> 'a1 fLANG -> 'a1 lOGLANG -> 'a2 eqDec -> 'a2 fLANG -> ('a1,
  'a2) sTRLANG -> ('a1, 'a2) dISPCALC -> ('a1, 'a2) sequent list -> ('a1,
  'a2) sequent list -> (('a1, 'a2) sequent, ('a1, 'a2) deriv_cofprseq)
  forallT -> ('a1, 'a2) deriv_cofprseqs

val deriv_cofseq_iff :
  'a1 eqDec -> 'a1 fLANG -> 'a1 lOGLANG -> 'a2 eqDec -> 'a2 fLANG -> ('a1,
  'a2) sTRLANG -> ('a1, 'a2) dISPCALC -> ('a1, 'a2) sequent -> (('a1, 'a2)
  deriv_cofseq, ('a1, 'a2) dertree) iffT0

val deriv_cofseqs_iff :
  'a1 eqDec -> 'a1 fLANG -> 'a1 lOGLANG -> 'a2 eqDec -> 'a2 fLANG -> ('a1,
  'a2) sTRLANG -> ('a1, 'a2) dISPCALC -> ('a1, 'a2) sequent list -> (('a1,
  'a2) deriv_cofseqs, ('a1, 'a2) dertree list) iffT0

val deriv_cofprseq_weak :
  'a1 eqDec -> 'a1 fLANG -> 'a1 lOGLANG -> 'a2 eqDec -> 'a2 fLANG -> ('a1,
  'a2) sTRLANG -> ('a1, 'a2) dISPCALC -> ('a1, 'a2) sequent list -> ('a1,
  'a2) sequent list -> ('a1, 'a2) sequent -> ('a1, 'a2) deriv_cofprseq ->
  ('a1, 'a2) deriv_cofprseq

val deriv_cofseq_tran_afs :
  'a1 eqDec -> 'a1 fLANG -> 'a1 lOGLANG -> 'a2 eqDec -> 'a2 fLANG -> ('a1,
  'a2) sTRLANG -> ('a1, 'a2) dISPCALC -> ('a1, 'a2) sequent list -> ('a1,
  'a2) sequent -> ('a1, 'a2) afsSubst -> ('a1, 'a2) deriv_ncprseq -> ('a1,
  'a2) deriv_cofseqs -> ('a1, 'a2) deriv_cofseq

type ('formula, 'structr) c8 =
  'formula -> ('formula, 'structr) dertree -> __ -> __ -> __ -> ('formula,
  'structr) dertree

val defSubs : string list -> 'a1 sSubst -> 'a1 sSubst -> 'a1 sSubst

type ('formula, 'structr) sSubstfor = 'structr sSubst

val stepSub :
  'a1 eqDec -> 'a1 fLANG -> 'a1 lOGLANG -> 'a2 eqDec -> 'a2 fLANG -> ('a1,
  'a2) sTRLANG -> ('a1, 'a2) afsSubst -> ('a1, 'a2) sequent -> ('a1, 'a2)
  sequent -> ('a1, 'a2) sSubstfor -> ('a1, 'a2) afsSubst

val comSubn :
  'a1 eqDec -> 'a1 fLANG -> 'a1 lOGLANG -> 'a2 eqDec -> 'a2 fLANG -> ('a1,
  'a2) sTRLANG -> ('a2*'a2) list -> 'a2 sSubst list -> 'a1 afSubst -> 'a2
  sSubst

val sF_str_sub :
  'a1 eqDec -> 'a1 fLANG -> 'a1 lOGLANG -> 'a2 eqDec -> 'a2 fLANG -> ('a1,
  'a2) sTRLANG -> 'a1 -> 'a2 -> 'a2 -> 'a1 afSubst -> 'a2 sSubst -> bool ->
  'a2 -> 'a2 sSubst

val exSub :
  'a1 eqDec -> 'a1 fLANG -> 'a1 lOGLANG -> 'a2 eqDec -> 'a2 fLANG -> ('a1,
  'a2) sTRLANG -> 'a1 -> 'a2 -> 'a2 -> 'a2 -> 'a2 -> 'a1 afSubst -> 'a2
  sSubst -> bool -> 'a2 sSubst

val seqExSub1 :
  'a1 eqDec -> 'a1 fLANG -> 'a1 lOGLANG -> 'a2 eqDec -> 'a2 fLANG -> ('a1,
  'a2) sTRLANG -> ('a1, 'a2) sequent -> ('a1, 'a2) sequent -> ('a1, 'a2)
  sequent -> 'a1 afSubst -> 'a2 sSubst -> bool -> 'a1 -> 'a2 -> ('a1, 'a2)
  sSubstfor

val seqExSub2 :
  'a1 eqDec -> 'a1 fLANG -> 'a1 lOGLANG -> 'a2 eqDec -> 'a2 fLANG -> ('a1,
  'a2) sTRLANG -> 'a2 -> 'a2 -> 'a2 -> 'a2 -> 'a2 -> 'a2 -> ('a1, 'a2)
  sequent -> ('a1, 'a2) sequent -> ('a1, 'a2) sequent -> 'a1 afSubst -> 'a2
  sSubst -> 'a1 -> 'a2 -> bool -> ('a1, 'a2) sSubstfor

type ('formula, 'structr) bELNAP =
  ('formula, 'structr) c8
  (* singleton inductive, whose constructor was Build_BELNAP *)

val c8_holds :
  'a1 eqDec -> 'a1 fLANG -> 'a1 lOGLANG -> 'a2 eqDec -> 'a2 fLANG -> ('a1,
  'a2) sTRLANG -> ('a1, 'a2) dISPCALC -> ('a1, 'a2) bELNAP -> 'a1 -> ('a1,
  'a2) dertree -> ('a1, 'a2) dertree

type ('formula, 'structr) derivRule =
  ('formula, 'structr) dertree
  (* singleton inductive, whose constructor was Build_DerivRule *)

val derr_dt :
  'a1 eqDec -> 'a1 fLANG -> 'a1 lOGLANG -> 'a2 eqDec -> 'a2 fLANG -> ('a1,
  'a2) sTRLANG -> ('a1, 'a2) dISPCALC -> ('a1, 'a2) rule -> ('a1, 'a2)
  derivRule -> ('a1, 'a2) dertree

type ('formula, 'structr) derivRuleNC =
  ('formula, 'structr) derivRule
  (* singleton inductive, whose constructor was Build_DerivRuleNC *)

val derrnc_derr :
  'a1 eqDec -> 'a1 fLANG -> 'a1 lOGLANG -> 'a2 eqDec -> 'a2 fLANG -> ('a1,
  'a2) sTRLANG -> ('a1, 'a2) dISPCALC -> ('a1, 'a2) rule -> ('a1, 'a2)
  derivRuleNC -> ('a1, 'a2) derivRule

type ('formula, 'structr) derivDC =
  ('formula, 'structr) rule -> __ -> ('formula, 'structr) derivRule

val derr_rules :
  'a1 eqDec -> 'a1 fLANG -> 'a1 lOGLANG -> 'a2 eqDec -> 'a2 fLANG -> ('a1,
  'a2) sTRLANG -> ('a1, 'a2) dISPCALC -> ('a1, 'a2) rule -> ('a1, 'a2)
  derivRule

val forallT_DerivRule_sig :
  'a1 eqDec -> 'a1 fLANG -> 'a1 lOGLANG -> 'a2 eqDec -> 'a2 fLANG -> ('a1,
  'a2) sTRLANG -> ('a1, 'a2) dISPCALC -> ('a1, 'a2) sequent list -> ('a1,
  'a2) sequent list -> (('a1, 'a2) sequent, ('a1, 'a2) derivRule) forallT ->
  ('a1, 'a2) dertree list

val forallT_DerivRuleNC_sig :
  'a1 eqDec -> 'a1 fLANG -> 'a1 lOGLANG -> 'a2 eqDec -> 'a2 fLANG -> ('a1,
  'a2) sTRLANG -> ('a1, 'a2) dISPCALC -> ('a1, 'a2) sequent list -> ('a1,
  'a2) sequent list -> (('a1, 'a2) sequent, ('a1, 'a2) derivRuleNC) forallT
  -> ('a1, 'a2) dertree list

val derivRule_iff_deriv_rule :
  'a1 eqDec -> 'a1 fLANG -> 'a1 lOGLANG -> 'a2 eqDec -> 'a2 fLANG -> ('a1,
  'a2) sTRLANG -> ('a1, 'a2) dISPCALC -> ('a1, 'a2) rule -> (('a1, 'a2)
  derivRule, ('a1, 'a2) deriv_rule) iffT0

val forallT_DerivRule_iff_deriv_rule :
  'a1 eqDec -> 'a1 fLANG -> 'a1 lOGLANG -> 'a2 eqDec -> 'a2 fLANG -> ('a1,
  'a2) sTRLANG -> ('a1, 'a2) dISPCALC -> ('a1, 'a2) rule list -> ((('a1, 'a2)
  rule, ('a1, 'a2) derivRule) forallT, (('a1, 'a2) rule, ('a1, 'a2)
  deriv_rule) forallT) iffT0

val derivRule_iff_deriv_prseq :
  'a1 eqDec -> 'a1 fLANG -> 'a1 lOGLANG -> 'a2 eqDec -> 'a2 fLANG -> ('a1,
  'a2) sTRLANG -> ('a1, 'a2) dISPCALC -> ('a1, 'a2) sequent list -> ('a1,
  'a2) sequent -> (('a1, 'a2) derivRule, ('a1, 'a2) deriv_prseq) iffT0

val derivDC_iff_ForallT_DerivRule :
  'a1 eqDec -> 'a1 fLANG -> 'a1 lOGLANG -> 'a2 eqDec -> 'a2 fLANG -> ('a1,
  'a2) sTRLANG -> ('a1, 'a2) dISPCALC -> ('a1, 'a2) dISPCALC -> (('a1, 'a2)
  derivDC, (('a1, 'a2) rule, ('a1, 'a2) derivRule) forallT) iffT0

val derivDC_iff_ForallT_deriv_rule :
  'a1 eqDec -> 'a1 fLANG -> 'a1 lOGLANG -> 'a2 eqDec -> 'a2 fLANG -> ('a1,
  'a2) sTRLANG -> ('a1, 'a2) dISPCALC -> ('a1, 'a2) dISPCALC -> (('a1, 'a2)
  derivDC, (('a1, 'a2) rule, ('a1, 'a2) deriv_rule) forallT) iffT0

val derivRuleNC_iff_deriv_ncprseq :
  'a1 eqDec -> 'a1 fLANG -> 'a1 lOGLANG -> 'a2 eqDec -> 'a2 fLANG -> ('a1,
  'a2) sTRLANG -> ('a1, 'a2) dISPCALC -> ('a1, 'a2) sequent list -> ('a1,
  'a2) sequent -> (('a1, 'a2) derivRuleNC, ('a1, 'a2) deriv_ncprseq) iffT0

val dernc_derremcut :
  'a1 eqDec -> 'a1 fLANG -> 'a1 lOGLANG -> 'a2 eqDec -> 'a2 fLANG -> ('a1,
  'a2) sTRLANG -> ('a1, 'a2) dISPCALC -> ('a1, 'a2) rule -> ('a1, 'a2)
  derivRuleNC -> ('a1, 'a2) derivRule

val derremcut_dernc :
  'a1 eqDec -> 'a1 fLANG -> 'a1 lOGLANG -> 'a2 eqDec -> 'a2 fLANG -> ('a1,
  'a2) sTRLANG -> ('a1, 'a2) dISPCALC -> ('a1, 'a2) rule -> ('a1, 'a2)
  derivRule -> ('a1, 'a2) derivRuleNC

val dernc_derremcut_iff :
  'a1 eqDec -> 'a1 fLANG -> 'a1 lOGLANG -> 'a2 eqDec -> 'a2 fLANG -> ('a1,
  'a2) sTRLANG -> ('a1, 'a2) dISPCALC -> ('a1, 'a2) rule -> (('a1, 'a2)
  derivRuleNC, ('a1, 'a2) derivRule) iffT0

val derivRule_rule_bw_Inst_expl :
  'a1 eqDec -> 'a1 fLANG -> 'a1 lOGLANG -> 'a2 eqDec -> 'a2 fLANG -> ('a1,
  'a2) sTRLANG -> ('a1, 'a2) dISPCALC -> ('a1, 'a2) sequent list -> ('a1,
  'a2) sequent list -> ('a1, 'a2) sequent -> ('a1, 'a2) afsSubst -> ('a1,
  'a2) derivRule -> (('a1, 'a2) sequent, ('a1, 'a2) derivRule) forallT ->
  ('a1, 'a2) derivRule

val derivRule_rule_bw_inDC :
  'a1 eqDec -> 'a1 fLANG -> 'a1 lOGLANG -> 'a2 eqDec -> 'a2 fLANG -> ('a1,
  'a2) sTRLANG -> ('a1, 'a2) dISPCALC -> ('a1, 'a2) sequent list -> ('a1,
  'a2) sequent list -> ('a1, 'a2) sequent -> ('a1, 'a2) afsSubst -> (('a1,
  'a2) sequent, ('a1, 'a2) derivRule) forallT -> ('a1, 'a2) derivRule

val deriv_cofseq_rule_bw_inDC :
  'a1 eqDec -> 'a1 fLANG -> 'a1 lOGLANG -> 'a2 eqDec -> 'a2 fLANG -> ('a1,
  'a2) sTRLANG -> ('a1, 'a2) dISPCALC -> ('a1, 'a2) sequent list -> ('a1,
  'a2) sequent -> ('a1, 'a2) afsSubst -> ('a1, 'a2) deriv_cofseqs -> ('a1,
  'a2) deriv_cofseq

val deriv_cofseq_rule_bw_InstNC :
  'a1 eqDec -> 'a1 fLANG -> 'a1 lOGLANG -> 'a2 eqDec -> 'a2 fLANG -> ('a1,
  'a2) sTRLANG -> ('a1, 'a2) dISPCALC -> ('a1, 'a2) sequent list -> ('a1,
  'a2) sequent -> ('a1, 'a2) afsSubst -> ('a1, 'a2) derivRuleNC -> (('a1,
  'a2) sequent, ('a1, 'a2) deriv_cofseq) forallT -> ('a1, 'a2) deriv_cofseq

val derivRuleNC_rule_bw_inDC :
  'a1 eqDec -> 'a1 fLANG -> 'a1 lOGLANG -> 'a2 eqDec -> 'a2 fLANG -> ('a1,
  'a2) sTRLANG -> ('a1, 'a2) dISPCALC -> ('a1, 'a2) sequent list -> ('a1,
  'a2) sequent list -> ('a1, 'a2) sequent -> ('a1, 'a2) afsSubst -> (('a1,
  'a2) sequent, ('a1, 'a2) derivRuleNC) forallT -> ('a1, 'a2) derivRuleNC

type ('formula, 'structr) subDer =
  ('formula, 'structr) rule -> ('formula, 'structr) derivRule -> ('formula,
  'structr) derivRule

val derivDC_refl :
  'a1 eqDec -> 'a1 fLANG -> 'a1 lOGLANG -> 'a2 eqDec -> 'a2 fLANG -> ('a1,
  'a2) sTRLANG -> ('a1, 'a2) dISPCALC -> ('a1, 'a2) rule -> ('a1, 'a2)
  derivRule

val derivDC_app :
  'a1 eqDec -> 'a1 fLANG -> 'a1 lOGLANG -> 'a2 eqDec -> 'a2 fLANG -> ('a1,
  'a2) sTRLANG -> ('a1, 'a2) dISPCALC -> ('a1, 'a2) dISPCALC -> ('a1, 'a2)
  dISPCALC -> ('a1, 'a2) derivDC -> ('a1, 'a2) derivDC -> ('a1, 'a2) rule ->
  ('a1, 'a2) derivRule

val derivDC_SubDer :
  'a1 eqDec -> 'a1 fLANG -> 'a1 lOGLANG -> 'a2 eqDec -> 'a2 fLANG -> ('a1,
  'a2) sTRLANG -> ('a1, 'a2) dISPCALC -> ('a1, 'a2) dISPCALC -> ('a1, 'a2)
  derivDC -> ('a1, 'a2) subDer

val extend_DerivDC :
  'a1 eqDec -> 'a1 fLANG -> 'a1 lOGLANG -> 'a2 eqDec -> 'a2 fLANG -> ('a1,
  'a2) sTRLANG -> ('a1, 'a2) dISPCALC -> ('a1, 'a2) dISPCALC -> ('a1, 'a2)
  derivDC -> ('a1, 'a2) subDer

val derivDC_one :
  'a1 eqDec -> 'a1 fLANG -> 'a1 lOGLANG -> 'a2 eqDec -> 'a2 fLANG -> ('a1,
  'a2) sTRLANG -> ('a1, 'a2) dISPCALC -> ('a1, 'a2) rule -> ('a1, 'a2)
  derivRule -> ('a1, 'a2) rule -> ('a1, 'a2) derivRule

val extend_DerivRule_expl :
  'a1 eqDec -> 'a1 fLANG -> 'a1 lOGLANG -> 'a2 eqDec -> 'a2 fLANG -> ('a1,
  'a2) sTRLANG -> ('a1, 'a2) dISPCALC -> ('a1, 'a2) rule -> ('a1, 'a2)
  derivRule -> ('a1, 'a2) subDer

val extSub2_fs :
  'a1 eqDec -> 'a1 fLANG -> 'a1 lOGLANG -> 'a2 eqDec -> 'a2 fLANG -> ('a1,
  'a2) sTRLANG -> ('a1, 'a2) rule -> ('a1, 'a2) rule -> ('a1, 'a2) sequent ->
  'a2 -> 'a2 -> 'a2 -> 'a2 -> 'a2 -> 'a2 -> 'a1 -> 'a2 -> bool -> ('a1, 'a2)
  afsSubst

val seqreps_map_concl :
  'a1 eqDec -> 'a1 fLANG -> 'a1 lOGLANG -> 'a2 eqDec -> 'a2 fLANG -> ('a1,
  'a2) sTRLANG -> bool -> 'a2 -> 'a2 -> ('a1, 'a2) sequent list -> ('a1, 'a2)
  sequent list -> (('a1, 'a2) sequent, ('a1, 'a2) sequent -> __ -> ('a1, 'a2)
  dertree) forallT -> ('a1, 'a2) dertree list

val makeCutLP :
  'a1 eqDec -> 'a1 fLANG -> 'a1 lOGLANG -> 'a2 eqDec -> 'a2 fLANG -> ('a1,
  'a2) sTRLANG -> ('a1, 'a2) dISPCALC -> ('a1, 'a2) bELNAP -> ('a1, 'a2)
  dertree -> ('a1, 'a2) dertree -> 'a1 -> 'a2 -> ('a1, 'a2) sequent -> ('a1,
  'a2) dertree

val allLP :
  'a1 eqDec -> 'a1 fLANG -> 'a1 lOGLANG -> 'a2 eqDec -> 'a2 fLANG -> ('a1,
  'a2) sTRLANG -> ('a1, 'a2) dISPCALC -> ('a1, 'a2) bELNAP -> ('a1, 'a2)
  dertree -> 'a1 -> ('a1, 'a2) dertree

val makeCutLRP :
  'a1 eqDec -> 'a1 fLANG -> 'a1 lOGLANG -> 'a2 eqDec -> 'a2 fLANG -> ('a1,
  'a2) sTRLANG -> ('a1, 'a2) dISPCALC -> ('a1, 'a2) bELNAP -> ('a1, 'a2)
  dertree -> ('a1, 'a2) dertree -> 'a1 -> 'a2 -> ('a1, 'a2) sequent -> ('a1,
  'a2) dertree

val allLRP :
  'a1 eqDec -> 'a1 fLANG -> 'a1 lOGLANG -> 'a2 eqDec -> 'a2 fLANG -> ('a1,
  'a2) sTRLANG -> ('a1, 'a2) dISPCALC -> ('a1, 'a2) bELNAP -> ('a1, 'a2)
  dertree -> 'a1 -> ('a1, 'a2) dertree

type ('formula, 'structr) canElim =
  ('formula, 'structr) dertree -> __ -> __ -> __ -> ('formula, 'structr)
  dertree

type ('formula, 'structr) canElimAll =
  ('formula, 'structr) dertree -> __ -> __ -> ('formula, 'structr) dertree

val canElim_canElimAll :
  'a1 eqDec -> 'a1 fLANG -> 'a1 lOGLANG -> 'a2 eqDec -> 'a2 fLANG -> ('a1,
  'a2) sTRLANG -> ('a1, 'a2) dISPCALC -> ('a1, 'a2) canElim -> ('a1, 'a2)
  dertree -> ('a1, 'a2) dertree

val elimFmls :
  'a1 eqDec -> 'a1 fLANG -> 'a1 lOGLANG -> 'a2 eqDec -> 'a2 fLANG -> ('a1,
  'a2) sTRLANG -> ('a1, 'a2) dISPCALC -> ('a1, 'a2) canElim -> ('a1, 'a2)
  dertree -> ('a1, 'a2) dertree

type ('formula, 'structr) canElimRaw =
  ('formula, 'structr) dertree -> __ -> __ -> ('formula, 'structr) dertree

type ('formula, 'structr) canElimAllRaw =
  ('formula, 'structr) dertree -> __ -> ('formula, 'structr) dertree

val canElim_cutOnFull_iff :
  'a1 eqDec -> 'a1 fLANG -> 'a1 lOGLANG -> 'a2 eqDec -> 'a2 fLANG -> ('a1,
  'a2) sTRLANG -> ('a1, 'a2) dISPCALC -> (('a1, 'a2) canElimRaw, ('a1, 'a2)
  canElim) iffT0

val canElimAll_cutOnFull_iff :
  'a1 eqDec -> 'a1 fLANG -> 'a1 lOGLANG -> 'a2 eqDec -> 'a2 fLANG -> ('a1,
  'a2) sTRLANG -> ('a1, 'a2) dISPCALC -> (('a1, 'a2) canElimAllRaw, ('a1,
  'a2) canElimAll) iffT0

val canElim_ex :
  'a1 eqDec -> 'a1 fLANG -> 'a1 lOGLANG -> 'a2 eqDec -> 'a2 fLANG -> ('a1,
  'a2) sTRLANG -> ('a1, 'a2) dISPCALC -> ('a3 -> ('a1, 'a2) canElim) -> ('a1,
  'a2) dertree -> 'a3 -> ('a1, 'a2) dertree

val cutOnFmls_Full :
  'a1 eqDec -> 'a1 fLANG -> 'a1 lOGLANG -> 'a2 eqDec -> 'a2 fLANG -> ('a1,
  'a2) sTRLANG -> ('a1, 'a2) dertree -> 'a1

val allElim :
  'a1 eqDec -> 'a1 fLANG -> 'a1 lOGLANG -> 'a2 eqDec -> 'a2 fLANG -> ('a1,
  'a2) sTRLANG -> ('a1, 'a2) dISPCALC -> ('a1 -> __ -> ('a1, 'a2) canElim) ->
  ('a1, 'a2) dertree -> ('a1, 'a2) dertree

val elimLP :
  'a1 eqDec -> 'a1 fLANG -> 'a1 lOGLANG -> 'a2 eqDec -> 'a2 fLANG -> ('a1,
  'a2) sTRLANG -> ('a1, 'a2) dISPCALC -> 'a1 -> ('a1, 'a2) canElim -> ('a1,
  'a2) dertree -> ('a1, 'a2) dertree

val elimLRP :
  'a1 eqDec -> 'a1 fLANG -> 'a1 lOGLANG -> 'a2 eqDec -> 'a2 fLANG -> ('a1,
  'a2) sTRLANG -> ('a1, 'a2) dISPCALC -> 'a1 -> ('a1, 'a2) canElim -> ('a1,
  'a2) dertree -> ('a1, 'a2) dertree

val allLP' :
  'a1 eqDec -> 'a1 fLANG -> 'a1 lOGLANG -> 'a2 eqDec -> 'a2 fLANG -> ('a1,
  'a2) sTRLANG -> ('a1, 'a2) dISPCALC -> ('a1, 'a2) bELNAP -> 'a1 -> ('a1,
  'a2) canElimAll -> ('a1, 'a2) dertree -> ('a1, 'a2) dertree

val allLRP' :
  'a1 eqDec -> 'a1 fLANG -> 'a1 lOGLANG -> 'a2 eqDec -> 'a2 fLANG -> ('a1,
  'a2) sTRLANG -> ('a1, 'a2) dISPCALC -> ('a1, 'a2) bELNAP -> 'a1 -> ('a1,
  'a2) canElimAll -> ('a1, 'a2) dertree -> ('a1, 'a2) dertree

val th8 :
  'a1 eqDec -> 'a1 fLANG -> 'a1 lOGLANG -> 'a2 eqDec -> 'a2 fLANG -> ('a1,
  'a2) sTRLANG -> ('a1, 'a2) dISPCALC -> ('a1, 'a2) bELNAP -> 'a1 -> ('a1,
  'a2) canElim -> ('a1, 'a2) dertree -> ('a1, 'a2) dertree

val allch :
  'a1 eqDec -> 'a1 fLANG -> 'a1 lOGLANG -> 'a2 eqDec -> 'a2 fLANG -> ('a1,
  'a2) sTRLANG -> ('a1, 'a2) dISPCALC -> ('a1, 'a2) bELNAP -> 'a1 -> ('a1,
  'a2) canElimAll -> ('a1, 'a2) dertree -> ('a1, 'a2) dertree

val th8ch' :
  'a1 eqDec -> 'a1 fLANG -> 'a1 lOGLANG -> 'a2 eqDec -> 'a2 fLANG -> ('a1,
  'a2) sTRLANG -> ('a1, 'a2) dISPCALC -> ('a1, 'a2) bELNAP -> 'a1 -> ('a1 ->
  __ -> ('a1, 'a2) canElim) -> ('a1, 'a2) dertree -> ('a1, 'a2) dertree

val canElimFml :
  'a1 eqDec -> 'a1 fLANG -> 'a1 lOGLANG -> 'a2 eqDec -> 'a2 fLANG -> ('a1,
  'a2) sTRLANG -> ('a1, 'a2) dISPCALC -> ('a1, 'a2) bELNAP -> 'a1 -> ('a1,
  'a2) dertree -> ('a1, 'a2) dertree

val c3458_canElimRaw :
  'a1 eqDec -> 'a1 fLANG -> 'a1 lOGLANG -> 'a2 eqDec -> 'a2 fLANG -> ('a1,
  'a2) sTRLANG -> ('a1, 'a2) dISPCALC -> ('a1, 'a2) bELNAP -> ('a1, 'a2)
  dertree -> ('a1, 'a2) dertree

val cav :
  'a1 eqDec -> 'a1 fLANG -> 'a1 lOGLANG -> 'a2 eqDec -> 'a2 fLANG -> ('a1,
  'a2) sTRLANG -> ('a1, 'a2) dISPCALC -> ('a1, 'a2) bELNAP -> ('a1, 'a2)
  dertree -> ('a1, 'a2) dertree

val cutElim :
  'a1 eqDec -> 'a1 fLANG -> 'a1 lOGLANG -> 'a2 eqDec -> 'a2 fLANG -> ('a1,
  'a2) sTRLANG -> ('a1, 'a2) dISPCALC -> ('a1, 'a2) bELNAP -> ('a1, 'a2)
  dertree -> ('a1, 'a2) dertree

val atrefl :
  'a1 eqDec -> 'a1 fLANG -> 'a1 lOGLANG -> 'a2 eqDec -> 'a2 fLANG -> ('a1,
  'a2) sTRLANG -> ('a1, 'a2) rule

val frefl :
  'a1 eqDec -> 'a1 fLANG -> 'a1 lOGLANG -> 'a2 eqDec -> 'a2 fLANG -> ('a1,
  'a2) sTRLANG -> 'a1 -> ('a1, 'a2) rule

module Kt :
 sig
  type formula =
  | Atf of string
  | FVf of string
  | Top
  | Bot
  | Neg of formula
  | Imp of formula * formula
  | Dis of formula * formula
  | Con of formula * formula
  | Boxn of formula
  | Dian of formula
  | Boxp of formula
  | Diap of formula

  val formula_rect :
    (string -> 'a1) -> (string -> 'a1) -> 'a1 -> 'a1 -> (formula -> 'a1 ->
    'a1) -> (formula -> 'a1 -> formula -> 'a1 -> 'a1) -> (formula -> 'a1 ->
    formula -> 'a1 -> 'a1) -> (formula -> 'a1 -> formula -> 'a1 -> 'a1) ->
    (formula -> 'a1 -> 'a1) -> (formula -> 'a1 -> 'a1) -> (formula -> 'a1 ->
    'a1) -> (formula -> 'a1 -> 'a1) -> formula -> 'a1

  val formula_rec :
    (string -> 'a1) -> (string -> 'a1) -> 'a1 -> 'a1 -> (formula -> 'a1 ->
    'a1) -> (formula -> 'a1 -> formula -> 'a1 -> 'a1) -> (formula -> 'a1 ->
    formula -> 'a1 -> 'a1) -> (formula -> 'a1 -> formula -> 'a1 -> 'a1) ->
    (formula -> 'a1 -> 'a1) -> (formula -> 'a1 -> 'a1) -> (formula -> 'a1 ->
    'a1) -> (formula -> 'a1 -> 'a1) -> formula -> 'a1

  type structr =
  | SVf of string
  | FSf of formula
  | I
  | Star of structr
  | Comma of structr * structr
  | BCirc of structr

  val structr_rect :
    (string -> 'a1) -> (formula -> 'a1) -> 'a1 -> (structr -> 'a1 -> 'a1) ->
    (structr -> 'a1 -> structr -> 'a1 -> 'a1) -> (structr -> 'a1 -> 'a1) ->
    structr -> 'a1

  val structr_rec :
    (string -> 'a1) -> (formula -> 'a1) -> 'a1 -> (structr -> 'a1 -> 'a1) ->
    (structr -> 'a1 -> structr -> 'a1 -> 'a1) -> (structr -> 'a1 -> 'a1) ->
    structr -> 'a1
 end

module Kt_LOG :
 sig
  val fml_eq_dec : Kt.formula eq_dec

  val ipse : Kt.formula -> Kt.formula list

  val ipse_rect :
    (Kt.formula -> (Kt.formula -> __ -> 'a1) -> 'a1) -> Kt.formula -> 'a1

  val fml_df : Kt.formula

  val conn : Kt.formula -> Kt.formula list -> Kt.formula

  val coq_Atm_dec : Kt.formula -> string option

  val coq_FV_dec : Kt.formula -> string option
 end

val eqDec_formula : Kt.formula eqDec

val f_Kt_log : Kt.formula fLANG

val kt_Atm : (Kt.formula, string) iXEXP

val kt_FV : (Kt.formula, string) iXEXP

val kt_log : Kt.formula lOGLANG

module Kt_STR :
 sig
  val str_eq_dec : Kt.structr eq_dec

  val ipse : Kt.structr -> Kt.structr list

  val ipse_rect :
    (Kt.structr -> (Kt.structr -> __ -> 'a1) -> 'a1) -> Kt.structr -> 'a1

  val str_df : Kt.structr

  val conn : Kt.structr -> Kt.structr list -> Kt.structr

  val coq_SV_dec : Kt.structr -> string option

  val coq_FS_dec : Kt.structr -> Kt.formula option

  val sgnips : Kt.structr -> bool list
 end

val eqDec_structr : Kt.structr eqDec

val f_Kt : Kt.structr fLANG

val kt_SV : (Kt.structr, string) iXEXP

val kt_FS : (Kt.structr, Kt.formula) iXEXP

val kt_str : (Kt.formula, Kt.structr) sTRLANG

module KtRules :
 sig
  val coq_Topl : (Kt.formula, Kt.structr) rule

  val coq_Topr : (Kt.formula, Kt.structr) rule

  val coq_Botl : (Kt.formula, Kt.structr) rule

  val coq_Botr : (Kt.formula, Kt.structr) rule

  val coq_Negl : (Kt.formula, Kt.structr) rule

  val coq_Negr : (Kt.formula, Kt.structr) rule

  val coq_Conl : (Kt.formula, Kt.structr) rule

  val coq_Conr : (Kt.formula, Kt.structr) rule

  val coq_Disl : (Kt.formula, Kt.structr) rule

  val coq_Disr : (Kt.formula, Kt.structr) rule

  val coq_Impl : (Kt.formula, Kt.structr) rule

  val coq_Impr : (Kt.formula, Kt.structr) rule

  val coq_Boxnl : (Kt.formula, Kt.structr) rule

  val coq_Boxnr : (Kt.formula, Kt.structr) rule

  val coq_Dianl : (Kt.formula, Kt.structr) rule

  val coq_Dianr : (Kt.formula, Kt.structr) rule

  val coq_Boxpl : (Kt.formula, Kt.structr) rule

  val coq_Boxpr : (Kt.formula, Kt.structr) rule

  val coq_Diapl : (Kt.formula, Kt.structr) rule

  val coq_Diapr : (Kt.formula, Kt.structr) rule

  val coq_Iaddl : (Kt.formula, Kt.structr) rule

  val coq_Idell : (Kt.formula, Kt.structr) rule

  val coq_Iaddr : (Kt.formula, Kt.structr) rule

  val coq_Idelr : (Kt.formula, Kt.structr) rule

  val coq_Isl : (Kt.formula, Kt.structr) rule

  val coq_Iul : (Kt.formula, Kt.structr) rule

  val coq_Isr : (Kt.formula, Kt.structr) rule

  val coq_Iur : (Kt.formula, Kt.structr) rule

  val coq_Wkl : (Kt.formula, Kt.structr) rule

  val coq_Wkr : (Kt.formula, Kt.structr) rule

  val coq_Assol : (Kt.formula, Kt.structr) rule

  val coq_Assolinv : (Kt.formula, Kt.structr) rule

  val coq_Assor : (Kt.formula, Kt.structr) rule

  val coq_Assorinv : (Kt.formula, Kt.structr) rule

  val coq_Comml : (Kt.formula, Kt.structr) rule

  val coq_Commr : (Kt.formula, Kt.structr) rule

  val coq_Contl : (Kt.formula, Kt.structr) rule

  val coq_Contr : (Kt.formula, Kt.structr) rule

  val coq_Icl : (Kt.formula, Kt.structr) rule

  val coq_Icr : (Kt.formula, Kt.structr) rule

  val coq_Mlrn : (Kt.formula, Kt.structr) rule

  val coq_Mrrs : (Kt.formula, Kt.structr) rule

  val coq_Mlln : (Kt.formula, Kt.structr) rule

  val coq_Mrls : (Kt.formula, Kt.structr) rule

  val coq_Mrrn : (Kt.formula, Kt.structr) rule

  val coq_Mlrs : (Kt.formula, Kt.structr) rule

  val coq_Mrln : (Kt.formula, Kt.structr) rule

  val coq_Mlls : (Kt.formula, Kt.structr) rule

  val coq_Ssn : (Kt.formula, Kt.structr) rule

  val coq_Sns : (Kt.formula, Kt.structr) rule

  val coq_DSEl : (Kt.formula, Kt.structr) rule

  val coq_DSIl : (Kt.formula, Kt.structr) rule

  val coq_DSEr : (Kt.formula, Kt.structr) rule

  val coq_DSIr : (Kt.formula, Kt.structr) rule

  val coq_Scl : (Kt.formula, Kt.structr) rule

  val coq_Scr : (Kt.formula, Kt.structr) rule

  val coq_Sss : (Kt.formula, Kt.structr) rule
 end

type ('formula, 'structr) c8_case_alt =
  ('formula, 'structr) deriv_cofseqs -> ('formula, 'structr) deriv_cofseq

val c8_case_alt_imp_C8_case :
  'a1 eqDec -> 'a1 fLANG -> 'a1 lOGLANG -> 'a2 eqDec -> 'a2 fLANG -> ('a1,
  'a2) sTRLANG -> ('a1, 'a2) dISPCALC -> 'a2 -> 'a2 -> ('a1, 'a2) sequent
  list -> ('a1, 'a2) c8_case_alt -> ('a1, 'a2) dertree list -> ('a1, 'a2)
  dertree

val lP_exhibit :
  'a1 eqDec -> 'a1 fLANG -> 'a1 lOGLANG -> 'a2 eqDec -> 'a2 fLANG -> ('a1,
  'a2) sTRLANG -> 'a1 -> ('a1, 'a2) sequent -> ('a1, 'a2) rule -> ('a1, 'a2)
  dertree list -> ('a2, (('a1, 'a2) rule, (('a1, 'a2) dertree list, ('a1,
  'a2) dertree) sigT) sigT) sigT

val rP_exhibit :
  'a1 eqDec -> 'a1 fLANG -> 'a1 lOGLANG -> 'a2 eqDec -> 'a2 fLANG -> ('a1,
  'a2) sTRLANG -> 'a1 -> ('a1, 'a2) sequent -> ('a1, 'a2) rule -> ('a1, 'a2)
  dertree list -> ('a2, (('a1, 'a2) dertree, (('a1, 'a2) rule, ('a1, 'a2)
  dertree list) sigT) sigT) sigT

val reduce_C8 :
  'a1 eqDec -> 'a1 fLANG -> 'a1 lOGLANG -> 'a2 eqDec -> 'a2 fLANG -> ('a1,
  'a2) sTRLANG -> ('a1, 'a2) dISPCALC -> ('a1 -> ('a1, 'a2) dertree list ->
  'a2 -> 'a2 -> ('a1, 'a2) rule -> ('a1, 'a2) dertree list -> ('a1, 'a2) rule
  -> ('a1, 'a2) dertree list -> ('a1, 'a2) afsSubst -> __ -> __ -> __ -> __
  -> __ -> __ -> __ -> ('a1, 'a2) dertree) -> 'a1 -> ('a1, 'a2) dertree ->
  ('a1, 'a2) dertree

val kt_DC : (Kt.formula, Kt.structr) dISPCALC

module KtDeriv :
 sig
  val dernc_Sss : (Kt.formula, Kt.structr) derivRuleNC

  val dernc_frefl : Kt.formula -> (Kt.formula, Kt.structr) derivRuleNC
 end

module KtBelnap :
 sig
  val coq_C8_Neg :
    Kt.structr -> Kt.structr -> Kt.formula -> (Kt.formula, Kt.structr)
    dertree list -> (Kt.formula, Kt.structr) dertree

  val coq_C8_Con :
    Kt.structr -> Kt.structr -> Kt.structr -> Kt.formula -> Kt.formula ->
    (Kt.formula, Kt.structr) dertree list -> (Kt.formula, Kt.structr) dertree

  val coq_C8_Dis :
    Kt.structr -> Kt.structr -> Kt.structr -> Kt.formula -> Kt.formula ->
    (Kt.formula, Kt.structr) dertree list -> (Kt.formula, Kt.structr) dertree

  val coq_C8_Imp :
    Kt.structr -> Kt.structr -> Kt.structr -> Kt.formula -> Kt.formula ->
    (Kt.formula, Kt.structr) dertree list -> (Kt.formula, Kt.structr) dertree

  val coq_C8_Boxn :
    Kt.structr -> Kt.structr -> Kt.formula -> (Kt.formula, Kt.structr)
    dertree list -> (Kt.formula, Kt.structr) dertree

  val coq_C8_Dian :
    Kt.structr -> Kt.structr -> Kt.formula -> (Kt.formula, Kt.structr)
    dertree list -> (Kt.formula, Kt.structr) dertree

  val coq_C8_Boxp :
    Kt.structr -> Kt.structr -> Kt.formula -> (Kt.formula, Kt.structr)
    dertree list -> (Kt.formula, Kt.structr) dertree

  val coq_C8_Diap :
    Kt.structr -> Kt.structr -> Kt.formula -> (Kt.formula, Kt.structr)
    dertree list -> (Kt.formula, Kt.structr) dertree

  val coq_C8_holds :
    Kt.formula -> (Kt.formula, Kt.structr) dertree -> (Kt.formula,
    Kt.structr) dertree
 end

val kt_DCBel : (Kt.formula, Kt.structr) bELNAP

val kt_cutElim :
  (Kt.formula, Kt.structr) dertree -> (Kt.formula, Kt.structr) dertree

val box_con_dis : (Kt.formula, Kt.structr) rule

val derr_box_con_dis : (Kt.formula, Kt.structr) derivRule
