
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

type ('a, 'r, 'x) subrelation = 'a -> 'a -> 'r -> 'x

val iffT_arrow_subrelation : (__, __) iffT -> (__, __) arrow

val iffT_flip_arrow_subrelation : (__, __) iffT -> (__, __) arrow

val flip2 : ('a1, 'a2, 'a3) subrelation -> ('a1, 'a2, 'a3) subrelation

val in_dec : ('a1 -> 'a1 -> bool) -> 'a1 -> 'a1 list -> bool

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

val conclDT :
  'a1 eqDec -> 'a1 fLANG -> 'a1 lOGLANG -> 'a2 eqDec -> 'a2 fLANG -> ('a1,
  'a2) sTRLANG -> ('a1, 'a2) dertree -> ('a1, 'a2) sequent

val cUT :
  'a1 eqDec -> 'a1 fLANG -> 'a1 lOGLANG -> 'a2 eqDec -> 'a2 fLANG -> ('a1,
  'a2) sTRLANG -> ('a1, 'a2) rule

val cUT_spec :
  'a1 eqDec -> 'a1 fLANG -> 'a1 lOGLANG -> 'a2 eqDec -> 'a2 fLANG -> ('a1,
  'a2) sTRLANG -> 'a1 -> 'a2 -> 'a2 -> ('a1, 'a2) afsSubst

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

val forallT_deriv_cofseqs :
  'a1 eqDec -> 'a1 fLANG -> 'a1 lOGLANG -> 'a2 eqDec -> 'a2 fLANG -> ('a1,
  'a2) sTRLANG -> ('a1, 'a2) dISPCALC -> ('a1, 'a2) sequent list -> (('a1,
  'a2) sequent, ('a1, 'a2) deriv_cofseq) forallT -> ('a1, 'a2) deriv_cofseqs

val forallT_deriv_cofseqs_iff :
  'a1 eqDec -> 'a1 fLANG -> 'a1 lOGLANG -> 'a2 eqDec -> 'a2 fLANG -> ('a1,
  'a2) sTRLANG -> ('a1, 'a2) dISPCALC -> ('a1, 'a2) sequent list -> ((('a1,
  'a2) sequent, ('a1, 'a2) deriv_cofseq) forallT, ('a1, 'a2) deriv_cofseqs)
  iffT0

val deriv_cofseq_iff :
  'a1 eqDec -> 'a1 fLANG -> 'a1 lOGLANG -> 'a2 eqDec -> 'a2 fLANG -> ('a1,
  'a2) sTRLANG -> ('a1, 'a2) dISPCALC -> ('a1, 'a2) sequent -> (('a1, 'a2)
  deriv_cofseq, ('a1, 'a2) dertree) iffT0

val deriv_cofseqs_iff :
  'a1 eqDec -> 'a1 fLANG -> 'a1 lOGLANG -> 'a2 eqDec -> 'a2 fLANG -> ('a1,
  'a2) sTRLANG -> ('a1, 'a2) dISPCALC -> ('a1, 'a2) sequent list -> (('a1,
  'a2) deriv_cofseqs, ('a1, 'a2) dertree list) iffT0

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

val deriv_cofseq_rule_bw_inDC :
  'a1 eqDec -> 'a1 fLANG -> 'a1 lOGLANG -> 'a2 eqDec -> 'a2 fLANG -> ('a1,
  'a2) sTRLANG -> ('a1, 'a2) dISPCALC -> ('a1, 'a2) sequent list -> ('a1,
  'a2) sequent -> ('a1, 'a2) afsSubst -> ('a1, 'a2) deriv_cofseqs -> ('a1,
  'a2) deriv_cofseq

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

module Lambek :
 sig
  type formula =
  | Atf of string
  | FVf of string
  | Top
  | Bot
  | Dis of formula * formula
  | Con of formula * formula
  | One
  | Fus of formula * formula
  | Und of formula * formula
  | Ove of formula * formula

  val formula_rect :
    (string -> 'a1) -> (string -> 'a1) -> 'a1 -> 'a1 -> (formula -> 'a1 ->
    formula -> 'a1 -> 'a1) -> (formula -> 'a1 -> formula -> 'a1 -> 'a1) ->
    'a1 -> (formula -> 'a1 -> formula -> 'a1 -> 'a1) -> (formula -> 'a1 ->
    formula -> 'a1 -> 'a1) -> (formula -> 'a1 -> formula -> 'a1 -> 'a1) ->
    formula -> 'a1

  val formula_rec :
    (string -> 'a1) -> (string -> 'a1) -> 'a1 -> 'a1 -> (formula -> 'a1 ->
    formula -> 'a1 -> 'a1) -> (formula -> 'a1 -> formula -> 'a1 -> 'a1) ->
    'a1 -> (formula -> 'a1 -> formula -> 'a1 -> 'a1) -> (formula -> 'a1 ->
    formula -> 'a1 -> 'a1) -> (formula -> 'a1 -> formula -> 'a1 -> 'a1) ->
    formula -> 'a1

  type structr =
  | SVf of string
  | FSf of formula
  | I
  | Coq__UU03a6_
  | Smc of structr * structr
  | Gre of structr * structr
  | Les of structr * structr

  val structr_rect :
    (string -> 'a1) -> (formula -> 'a1) -> 'a1 -> 'a1 -> (structr -> 'a1 ->
    structr -> 'a1 -> 'a1) -> (structr -> 'a1 -> structr -> 'a1 -> 'a1) ->
    (structr -> 'a1 -> structr -> 'a1 -> 'a1) -> structr -> 'a1

  val structr_rec :
    (string -> 'a1) -> (formula -> 'a1) -> 'a1 -> 'a1 -> (structr -> 'a1 ->
    structr -> 'a1 -> 'a1) -> (structr -> 'a1 -> structr -> 'a1 -> 'a1) ->
    (structr -> 'a1 -> structr -> 'a1 -> 'a1) -> structr -> 'a1
 end

module Lambek_LOG :
 sig
  val fml_eq_dec : Lambek.formula eq_dec

  val ipse : Lambek.formula -> Lambek.formula list

  val ipse_rect :
    (Lambek.formula -> (Lambek.formula -> __ -> 'a1) -> 'a1) ->
    Lambek.formula -> 'a1

  val fml_df : Lambek.formula

  val conn : Lambek.formula -> Lambek.formula list -> Lambek.formula

  val coq_Atm_dec : Lambek.formula -> string option

  val coq_FV_dec : Lambek.formula -> string option
 end

val eqDec_formula : Lambek.formula eqDec

val f_Lambek_log : Lambek.formula fLANG

val lambek_Atm : (Lambek.formula, string) iXEXP

val lambek_FV : (Lambek.formula, string) iXEXP

val lambek_log : Lambek.formula lOGLANG

module Lambek_STR :
 sig
  val str_eq_dec : Lambek.structr eq_dec

  val ipse : Lambek.structr -> Lambek.structr list

  val ipse_rect :
    (Lambek.structr -> (Lambek.structr -> __ -> 'a1) -> 'a1) ->
    Lambek.structr -> 'a1

  val str_df : Lambek.structr

  val conn : Lambek.structr -> Lambek.structr list -> Lambek.structr

  val coq_SV_dec : Lambek.structr -> string option

  val coq_FS_dec : Lambek.structr -> Lambek.formula option

  val sgnips : Lambek.structr -> bool list
 end

val eqDec_structr : Lambek.structr eqDec

val f_Lambek : Lambek.structr fLANG

val lambek_SV : (Lambek.structr, string) iXEXP

val lambek_FS : (Lambek.structr, Lambek.formula) iXEXP

val lambek_str : (Lambek.formula, Lambek.structr) sTRLANG

module LambekRules :
 sig
  val coq_Topl : (Lambek.formula, Lambek.structr) rule

  val coq_Topr : (Lambek.formula, Lambek.structr) rule

  val coq_Botl : (Lambek.formula, Lambek.structr) rule

  val coq_Botr : (Lambek.formula, Lambek.structr) rule

  val coq_Conll : (Lambek.formula, Lambek.structr) rule

  val coq_Conlr : (Lambek.formula, Lambek.structr) rule

  val coq_Conr : (Lambek.formula, Lambek.structr) rule

  val coq_Disl : (Lambek.formula, Lambek.structr) rule

  val coq_Disrl : (Lambek.formula, Lambek.structr) rule

  val coq_Disrr : (Lambek.formula, Lambek.structr) rule

  val coq_Onel : (Lambek.formula, Lambek.structr) rule

  val coq_Oner : (Lambek.formula, Lambek.structr) rule

  val coq_Fusl : (Lambek.formula, Lambek.structr) rule

  val coq_Fusr : (Lambek.formula, Lambek.structr) rule

  val coq_Undl : (Lambek.formula, Lambek.structr) rule

  val coq_Undr : (Lambek.formula, Lambek.structr) rule

  val coq_Ovel : (Lambek.formula, Lambek.structr) rule

  val coq_Over : (Lambek.formula, Lambek.structr) rule

  val coq_Iwl : (Lambek.formula, Lambek.structr) rule

  val coq_Iwr : (Lambek.formula, Lambek.structr) rule

  val _UU03a6_addll : (Lambek.formula, Lambek.structr) rule

  val _UU03a6_addlr : (Lambek.formula, Lambek.structr) rule

  val _UU03a6_addrl : (Lambek.formula, Lambek.structr) rule

  val _UU03a6_addrr : (Lambek.formula, Lambek.structr) rule

  val _UU03a6_delll : (Lambek.formula, Lambek.structr) rule

  val _UU03a6_dellr : (Lambek.formula, Lambek.structr) rule

  val _UU03a6_delrl : (Lambek.formula, Lambek.structr) rule

  val _UU03a6_delrr : (Lambek.formula, Lambek.structr) rule

  val coq_Rlesmr : (Lambek.formula, Lambek.structr) rule

  val coq_Rsmgel : (Lambek.formula, Lambek.structr) rule

  val coq_Rgesmr : (Lambek.formula, Lambek.structr) rule

  val coq_Rsmlel : (Lambek.formula, Lambek.structr) rule

  val coq_Rlesml : (Lambek.formula, Lambek.structr) rule

  val coq_Rsmger : (Lambek.formula, Lambek.structr) rule

  val coq_Rgesml : (Lambek.formula, Lambek.structr) rule

  val coq_Rsmler : (Lambek.formula, Lambek.structr) rule
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

val lambek_DC : (Lambek.formula, Lambek.structr) dISPCALC

module LambekBelnap :
 sig
  val coq_C8_Con_l :
    Lambek.structr -> Lambek.structr -> Lambek.formula -> Lambek.formula ->
    (Lambek.formula, Lambek.structr) dertree list -> (Lambek.formula,
    Lambek.structr) dertree

  val coq_C8_Con_r :
    Lambek.structr -> Lambek.structr -> Lambek.formula -> Lambek.formula ->
    (Lambek.formula, Lambek.structr) dertree list -> (Lambek.formula,
    Lambek.structr) dertree

  val coq_C8_Dis_l :
    Lambek.structr -> Lambek.structr -> Lambek.formula -> Lambek.formula ->
    (Lambek.formula, Lambek.structr) dertree list -> (Lambek.formula,
    Lambek.structr) dertree

  val coq_C8_Dis_r :
    Lambek.structr -> Lambek.structr -> Lambek.formula -> Lambek.formula ->
    (Lambek.formula, Lambek.structr) dertree list -> (Lambek.formula,
    Lambek.structr) dertree

  val coq_C8_Fus :
    Lambek.structr -> Lambek.structr -> Lambek.structr -> Lambek.formula ->
    Lambek.formula -> (Lambek.formula, Lambek.structr) dertree list ->
    (Lambek.formula, Lambek.structr) dertree

  val coq_C8_Und :
    Lambek.structr -> Lambek.structr -> Lambek.structr -> Lambek.formula ->
    Lambek.formula -> (Lambek.formula, Lambek.structr) dertree list ->
    (Lambek.formula, Lambek.structr) dertree

  val coq_C8_Ove :
    Lambek.structr -> Lambek.structr -> Lambek.structr -> Lambek.formula ->
    Lambek.formula -> (Lambek.formula, Lambek.structr) dertree list ->
    (Lambek.formula, Lambek.structr) dertree

  val coq_C8_holds :
    Lambek.formula -> (Lambek.formula, Lambek.structr) dertree ->
    (Lambek.formula, Lambek.structr) dertree
 end

val lambek_DCBel : (Lambek.formula, Lambek.structr) bELNAP

val lambek_cutElim :
  (Lambek.formula, Lambek.structr) dertree -> (Lambek.formula,
  Lambek.structr) dertree

val derr_ex_rule : (Lambek.formula, Lambek.structr) derivRule
