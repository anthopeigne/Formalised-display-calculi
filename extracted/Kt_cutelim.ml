
type __ = Obj.t
let __ = let rec f _ = Obj.repr f in Obj.repr f

(** val negb : bool -> bool **)

let negb = function
| true -> false
| false -> true

type ('a, 'b) sum =
| Inl of 'a
| Inr of 'b

(** val fst : ('a1*'a2) -> 'a1 **)

let fst = function
| x,_ -> x

(** val snd : ('a1*'a2) -> 'a2 **)

let snd = function
| _,y -> y

(** val app : 'a1 list -> 'a1 list -> 'a1 list **)

let rec app l m =
  match l with
  | [] -> m
  | a::l1 -> a::(app l1 m)

(** val id : __ -> __ **)

let id x =
  x

type 'a sig0 = 'a
  (* singleton inductive, whose constructor was exist *)

type 'a sig2 = 'a
  (* singleton inductive, whose constructor was exist2 *)

type ('a, 'p) sigT =
| ExistT of 'a * 'p



type ('a, 'b) arrow = 'a -> 'b

type ('a, 'b) iffT = ('a -> 'b)*('b -> 'a)

type ('a, 'r) symmetric = 'a -> 'a -> 'r -> 'r

(** val symmetry : ('a1, 'a2) symmetric -> 'a1 -> 'a1 -> 'a2 -> 'a2 **)

let symmetry symmetric0 =
  symmetric0

type ('a, 'r) transitive = 'a -> 'a -> 'a -> 'r -> 'r -> 'r

(** val transitivity :
    ('a1, 'a2) transitive -> 'a1 -> 'a1 -> 'a1 -> 'a2 -> 'a2 -> 'a2 **)

let transitivity transitive0 =
  transitive0

type ('a, 'r, 'x) subrelation = 'a -> 'a -> 'r -> 'x

(** val iffT_Symmetric : (__, __) iffT -> (__, __) iffT **)

let iffT_Symmetric = function
| a,b -> b,a

(** val iffT_Transitive : (__, __) iffT -> (__, __) iffT -> (__, __) iffT **)

let iffT_Transitive x = function
| a,b ->
  let a0,b0 = x in
  (fun x1 -> let x2 = a0 x1 in a x2),(fun x1 -> let x2 = b x1 in b0 x2)

(** val iffT_arrow_subrelation : (__, __) iffT -> (__, __) arrow **)

let iffT_arrow_subrelation x x0 =
  let a,_ = x in a x0

(** val iffT_flip_arrow_subrelation : (__, __) iffT -> (__, __) arrow **)

let iffT_flip_arrow_subrelation x x0 =
  let _,b = x in b x0

(** val trans_co_eq_inv_arrow_morphism_obligation_1 :
    ('a1, 'a2) transitive -> 'a1 -> 'a1 -> 'a2 -> 'a1 -> 'a1 -> (__, __) arrow **)

let trans_co_eq_inv_arrow_morphism_obligation_1 h x y x0 y0 _ x1 =
  transitivity (Obj.magic h) x y y0 (Obj.magic x0) x1

(** val trans_co_eq_inv_arrow_morphism :
    ('a1, 'a2) transitive -> 'a1 -> 'a1 -> 'a2 -> 'a1 -> 'a1 -> (__, __) arrow **)

let trans_co_eq_inv_arrow_morphism =
  trans_co_eq_inv_arrow_morphism_obligation_1

(** val flip2 : ('a1, 'a2, 'a3) subrelation -> ('a1, 'a2, 'a3) subrelation **)

let flip2 h =
  h

(** val in_dec : ('a1 -> 'a1 -> bool) -> 'a1 -> 'a1 list -> bool **)

let rec in_dec h a = function
| [] -> false
| y::l0 -> let s = h y a in if s then true else in_dec h a l0

(** val remove : ('a1 -> 'a1 -> bool) -> 'a1 -> 'a1 list -> 'a1 list **)

let rec remove eq_dec0 x = function
| [] -> []
| y::tl ->
  if eq_dec0 x y then remove eq_dec0 x tl else y::(remove eq_dec0 x tl)

(** val list_eq_dec : ('a1 -> 'a1 -> bool) -> 'a1 list -> 'a1 list -> bool **)

let rec list_eq_dec eq_dec0 l l' =
  match l with
  | [] -> (match l' with
           | [] -> true
           | _::_ -> false)
  | y::l0 ->
    (match l' with
     | [] -> false
     | a::l1 -> if eq_dec0 y a then list_eq_dec eq_dec0 l0 l1 else false)

(** val map : ('a1 -> 'a2) -> 'a1 list -> 'a2 list **)

let rec map f = function
| [] -> []
| a::t -> (f a)::(map f t)

(** val fold_right : ('a2 -> 'a1 -> 'a1) -> 'a1 -> 'a2 list -> 'a1 **)

let rec fold_right f a0 = function
| [] -> a0
| b::t -> f b (fold_right f a0 t)

type 'a eq_dec = 'a -> 'a -> bool

type ('a, 'b) iffT0 = ('a -> 'b)*('b -> 'a)

type 'a eqDec =
  'a -> 'a -> bool
  (* singleton inductive, whose constructor was Build_EqDec *)

(** val eqdec : 'a1 eqDec -> 'a1 -> 'a1 -> bool **)

let eqdec eqDec0 =
  eqDec0

(** val eqDec_list : 'a1 eqDec -> 'a1 list eqDec **)

let eqDec_list aED =
  list_eq_dec (eqdec aED)

(** val eqDec_prod : 'a1 eqDec -> 'a2 eqDec -> ('a1*'a2) eqDec **)

let eqDec_prod aED bED x y =
  let a,b = x in
  let a0,b0 = y in if eqdec aED a a0 then eqdec bED b b0 else false

(** val eqDec_string : string eqDec **)

let eqDec_string =
  (=)

(** val comp : ('a2 -> 'a3) -> ('a1 -> 'a2) -> 'a1 -> 'a3 **)

let comp g f x =
  g (f x)

(** val list_biind :
    'a3 -> ('a1 -> 'a1 list -> 'a2 -> 'a2 list -> 'a3 -> 'a3) -> 'a1 list ->
    'a2 list -> 'a3 **)

let rec list_biind bC iH l1 l2 =
  match l1 with
  | [] -> bC
  | y::l ->
    (match l2 with
     | [] -> assert false (* absurd case *)
     | b::l0 -> iH y l b l0 (list_biind bC iH l l0))

(** val in_some_dec :
    'a2 eqDec -> 'a2 -> 'a1 list -> ('a1 -> 'a2 list) -> 'a1 sig2 option **)

let rec in_some_dec eDB b l f =
  match l with
  | [] -> None
  | y::l0 ->
    (match in_some_dec eDB b l0 f with
     | Some s -> Some s
     | None ->
       let s = in_dec (eqdec eDB) b (f y) in if s then Some y else None)

(** val eq_dec_in_list :
    ('a1 -> 'a1 -> bool) -> 'a1 -> 'a1 list -> 'a1 -> (__ -> 'a2) -> (__ ->
    'a2) -> 'a2 **)

let eq_dec_in_list aeq_dec y _ x hy hys =
  let s = aeq_dec x y in if s then hy __ else hys __

(** val nxorb : bool -> bool -> bool **)

let nxorb b1 b2 =
  if b1 then b2 else negb b2

(** val zip : ('a1 -> 'a2 -> 'a3) -> 'a1 list -> 'a2 list -> 'a3 list **)

let rec zip f lA lB =
  match lA with
  | [] -> []
  | a::tA -> (match lB with
              | [] -> []
              | b::tB -> (f a b)::(zip f tA tB))

(** val list_2_elems_dec : 'a1 list -> ('a1, ('a1, __) sigT) sigT option **)

let list_2_elems_dec = function
| [] -> None
| a::l0 ->
  (match l0 with
   | [] -> None
   | a0::l1 ->
     (match l1 with
      | [] -> Some (ExistT (a, (ExistT (a0, __))))
      | _::_ -> None))

(** val in_map_inv_sig :
    'a1 eqDec -> ('a2 -> 'a1) -> 'a2 list -> 'a1 -> 'a2 **)

let rec in_map_inv_sig aED f l y =
  match l with
  | [] -> assert false (* absurd case *)
  | y0::l0 ->
    let s = eqdec aED (f y0) y in
    if s
    then y0
    else let s0 = in_dec (eqdec aED) y (map f l0) in
         if s0
         then in_map_inv_sig aED f l0 y
         else assert false (* absurd case *)

(** val list_union : 'a1 list -> ('a1 -> 'a2 list) -> 'a2 list **)

let list_union l f =
  fold_right (fun x -> app (f x)) [] l

type ('a, 'p) forallT =
| ForallT_nil
| ForallT_cons of 'a * 'a list * 'p * ('a, 'p) forallT

(** val forallT_inv : 'a1 -> 'a1 list -> ('a1, 'a2) forallT -> 'a2 **)

let forallT_inv _ _ = function
| ForallT_nil -> assert false (* absurd case *)
| ForallT_cons (_, _, x, _) -> x

(** val forallT_inv_tail :
    'a1 -> 'a1 list -> ('a1, 'a2) forallT -> ('a1, 'a2) forallT **)

let forallT_inv_tail _ _ = function
| ForallT_nil -> assert false (* absurd case *)
| ForallT_cons (_, _, _, x) -> x

(** val forallT_forall :
    'a1 eqDec -> 'a1 list -> (('a1, 'a2) forallT, 'a1 -> __ -> 'a2) iffT0 **)

let forallT_forall aED l =
  (fun h x _ ->
    let rec f l0 h0 x0 =
      match l0 with
      | [] -> assert false (* absurd case *)
      | y::l1 ->
        (match h0 with
         | ForallT_nil -> assert false (* absurd case *)
         | ForallT_cons (_, _, x1, x2) ->
           let s = eqdec aED y x0 in
           if s
           then x1
           else let s0 = in_dec (eqdec aED) x0 l1 in
                if s0 then f l1 x2 x0 else assert false (* absurd case *))
    in f l h x),(fun h ->
    let rec f l0 h0 =
      match l0 with
      | [] -> ForallT_nil
      | y::l1 -> ForallT_cons (y, l1, (h0 y __), (f l1 (fun x _ -> h0 x __)))
    in f l h)

(** val forallT_mp :
    'a1 list -> ('a1, 'a2) forallT -> ('a1, 'a2 -> 'a3) forallT -> ('a1, 'a3)
    forallT **)

let rec forallT_mp l hP hPQ =
  match l with
  | [] -> ForallT_nil
  | y::l0 ->
    (match hP with
     | ForallT_nil -> assert false (* absurd case *)
     | ForallT_cons (_, _, x, x0) ->
       (match hPQ with
        | ForallT_nil -> assert false (* absurd case *)
        | ForallT_cons (_, _, x1, x2) ->
          ForallT_cons (y, l0, (x1 x), (forallT_mp l0 x0 x2))))

(** val forallT_act :
    'a1 list -> ('a1 -> 'a2 -> 'a3) -> ('a1, 'a2) forallT -> ('a1, 'a3)
    forallT **)

let forallT_act l f h =
  forallT_mp l h
    (let rec f0 l0 h0 =
       match l0 with
       | [] -> ForallT_nil
       | y::l1 ->
         ForallT_cons (y, l1, (f y),
           (match h0 with
            | ForallT_nil -> assert false (* absurd case *)
            | ForallT_cons (_, _, _, x) -> f0 l1 x))
     in f0 l h)

(** val forallT_act_iff :
    'a1 list -> ('a1 -> ('a2, 'a3) iffT0) -> (('a1, 'a2) forallT, ('a1, 'a3)
    forallT) iffT0 **)

let forallT_act_iff l h =
  (forallT_act l (fun x -> let x0,_ = h x in x0)),(forallT_act l (fun x ->
                                                    let _,x0 = h x in x0))

(** val forallT_sig_elim : 'a1 list -> ('a1, 'a2) forallT -> 'a2 list **)

let rec forallT_sig_elim l h =
  match l with
  | [] -> []
  | _::l0 ->
    (match h with
     | ForallT_nil -> assert false (* absurd case *)
     | ForallT_cons (_, _, x, x0) -> let s = forallT_sig_elim l0 x0 in x::s)

(** val forall_ForallT :
    'a1 eqDec -> 'a1 list -> (__, ('a1, __) forallT) iffT0 **)

let forall_ForallT aED l =
  (fun _ ->
    let _,x = forallT_forall aED l in let x0 = Obj.magic x in Obj.magic x0 __),
    (Obj.magic __)

type ('a, 'p) existsT =
| ExistsT_cons_hd of 'a * 'a list * 'p
| Exists_cons_tl of 'a * 'a list * ('a, 'p) existsT

(** val in_zip_pair_23_sig_1 :
    'a2 eqDec -> 'a3 eqDec -> 'a1 list -> 'a2 list -> 'a3 list -> 'a2 -> 'a3
    -> 'a1 **)

let rec in_zip_pair_23_sig_1 bED cED lA lB lC b c =
  match lB with
  | [] -> assert false (* absurd case *)
  | y::l ->
    (match lA with
     | [] -> assert false (* absurd case *)
     | a::l0 ->
       (match lC with
        | [] -> assert false (* absurd case *)
        | c0::l1 ->
          let s = eqdec (eqDec_prod bED cED) (y,c0) (b,c) in
          if s
          then a
          else let s0 =
                 in_dec (eqdec (eqDec_prod bED cED)) (b,c)
                   (zip (fun x x0 -> x,x0) l l1)
               in
               if s0
               then in_zip_pair_23_sig_1 bED cED l0 l l1 b c
               else assert false (* absurd case *)))

(** val forallT_dec_E_sumbool :
    'a1 list -> ('a1, bool) forallT -> (('a1, __) existsT, ('a1, __) forallT)
    sum **)

let rec forallT_dec_E_sumbool l hdec =
  match l with
  | [] -> Inr ForallT_nil
  | y::l0 ->
    let hdeca = forallT_inv y l0 hdec in
    let hdecl = forallT_inv_tail y l0 hdec in
    let iHl = forallT_dec_E_sumbool l0 hdecl in
    if hdeca
    then Inl (ExistsT_cons_hd (y, l0, __))
    else (match iHl with
          | Inl e -> Inl (Exists_cons_tl (y, l0, e))
          | Inr f -> Inr (ForallT_cons (y, l0, __, f)))

(** val forallT_map :
    ('a1 -> 'a2) -> 'a1 list -> (('a2, 'a3) forallT, ('a1, 'a3) forallT) iffT0 **)

let forallT_map f l =
  (fun h ->
    let rec f0 l0 h0 =
      match l0 with
      | [] -> ForallT_nil
      | y::l1 ->
        ForallT_cons (y, l1,
          (match h0 with
           | ForallT_nil -> assert false (* absurd case *)
           | ForallT_cons (_, _, x, _) -> x),
          (match h0 with
           | ForallT_nil -> assert false (* absurd case *)
           | ForallT_cons (_, _, _, x) -> f0 l1 x))
    in f0 l h),(fun h ->
    let rec f0 _ = function
    | ForallT_nil -> ForallT_nil
    | ForallT_cons (x, l0, y, f2) ->
      ForallT_cons ((f x),
        (let rec map0 = function
         | [] -> []
         | a::t -> (f a)::(map0 t)
         in map0 l0), y, (f0 l0 f2))
    in f0 l h)

type 'expr fLANG = { ipse : ('expr -> 'expr list);
                     ipse_rect : (__ -> ('expr -> ('expr -> __ -> __) -> __)
                                 -> 'expr -> __);
                     conn : ('expr -> 'expr list -> 'expr) }

(** val ipse_rect :
    'a1 eqDec -> 'a1 fLANG -> ('a1 -> ('a1 -> __ -> 'a2) -> 'a2) -> 'a1 -> 'a2 **)

let ipse_rect _ fLANG0 x a =
  Obj.magic fLANG0.ipse_rect __ x a

type ('expr, 'ix) iXEXP =
  'expr -> 'ix option
  (* singleton inductive, whose constructor was Build_IXEXP *)

(** val var_dec :
    'a1 eqDec -> 'a1 fLANG -> ('a2 -> 'a1) -> ('a1, 'a2) iXEXP -> 'a1 -> 'a2
    option **)

let var_dec _ _ _ iXEXP0 =
  iXEXP0

type 'formula lOGLANG = { atm : (string -> 'formula);
                          fV : (string -> 'formula);
                          aTMVAR : ('formula, string) iXEXP;
                          fVVAR : ('formula, string) iXEXP }

type aSubst = string -> string

type 'formula fSubst = string -> 'formula

type 'formula afSubst = aSubst*'formula fSubst

(** val allVars :
    'a1 eqDec -> 'a1 fLANG -> ('a2 -> 'a1) -> ('a1, 'a2) iXEXP -> 'a1 -> 'a2
    list **)

let allVars eD l var sVAR =
  ipse_rect eD l (fun a iH ->
    match var_dec eD l var sVAR a with
    | Some s -> s::[]
    | None ->
      list_union (l.ipse a) (fun b ->
        if in_dec (eqdec eD) b (l.ipse a) then iH b __ else []))

(** val fmlAtms :
    'a1 eqDec -> 'a1 fLANG -> 'a1 lOGLANG -> 'a1 -> string list **)

let fmlAtms eDf lf lL =
  allVars eDf lf lL.atm lL.aTMVAR

(** val fmlFVs :
    'a1 eqDec -> 'a1 fLANG -> 'a1 lOGLANG -> 'a1 -> string list **)

let fmlFVs eDf lf lL =
  allVars eDf lf lL.fV lL.fVVAR

(** val fmlSubst :
    'a1 eqDec -> 'a1 fLANG -> 'a1 lOGLANG -> 'a1 afSubst -> 'a1 -> 'a1 **)

let fmlSubst eDf lf lL af =
  ipse_rect eDf lf (fun a iH ->
    match var_dec eDf lf lL.atm lL.aTMVAR a with
    | Some s -> lL.atm (fst af s)
    | None ->
      (match var_dec eDf lf lL.fV lL.fVVAR a with
       | Some s -> snd af s
       | None ->
         lf.conn a
           (list_union (lf.ipse a) (fun b ->
             if in_dec (eqdec eDf) b (lf.ipse a) then (iH b __)::[] else []))))

(** val i_a : aSubst **)

let i_a =
  Obj.magic id

(** val i_f : 'a1 eqDec -> 'a1 fLANG -> 'a1 lOGLANG -> 'a1 fSubst **)

let i_f _ _ lL f =
  lL.fV f

(** val fml_matchsub_Atm :
    'a1 eqDec -> 'a1 fLANG -> 'a1 lOGLANG -> 'a1 -> 'a1 -> aSubst **)

let fml_matchsub_Atm eDf lf lL =
  ipse_rect eDf lf (fun a iH b x ->
    match var_dec eDf lf lL.atm lL.aTMVAR a with
    | Some _ ->
      (match var_dec eDf lf lL.atm lL.aTMVAR b with
       | Some s0 -> s0
       | None ->
         (match in_some_dec eqDec_string x
                  (zip (fun x0 x1 -> x0,x1) (lf.ipse a) (lf.ipse b))
                  (comp (fmlAtms eDf lf lL) fst) with
          | Some s -> iH (fst s) __ (snd s) x
          | None -> x))
    | None ->
      (match in_some_dec eqDec_string x
               (zip (fun x0 x1 -> x0,x1) (lf.ipse a) (lf.ipse b))
               (comp (fmlAtms eDf lf lL) fst) with
       | Some s -> iH (fst s) __ (snd s) x
       | None -> x))

(** val fml_matchsub_FV :
    'a1 eqDec -> 'a1 fLANG -> 'a1 lOGLANG -> 'a1 -> 'a1 -> 'a1 fSubst **)

let fml_matchsub_FV eDf lf lL =
  ipse_rect eDf lf (fun a iH b x ->
    match var_dec eDf lf lL.fV lL.fVVAR a with
    | Some _ -> b
    | None ->
      (match in_some_dec eqDec_string x
               (zip (fun x0 x1 -> x0,x1) (lf.ipse a) (lf.ipse b))
               (comp (fmlFVs eDf lf lL) fst) with
       | Some s -> iH (fst s) __ (snd s) x
       | None -> lL.fV x))

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

(** val antec :
    'a1 eqDec -> 'a1 fLANG -> 'a1 lOGLANG -> 'a2 eqDec -> 'a2 fLANG -> ('a1,
    'a2) sTRLANG -> ('a1, 'a2) sequent -> 'a2 **)

let antec _ _ _ _ _ _ = function
| Sequent (x, _) -> x

(** val succ :
    'a1 eqDec -> 'a1 fLANG -> 'a1 lOGLANG -> 'a2 eqDec -> 'a2 fLANG -> ('a1,
    'a2) sTRLANG -> ('a1, 'a2) sequent -> 'a2 **)

let succ _ _ _ _ _ _ = function
| Sequent (_, y) -> y

(** val conclRule :
    'a1 eqDec -> 'a1 fLANG -> 'a1 lOGLANG -> 'a2 eqDec -> 'a2 fLANG -> ('a1,
    'a2) sTRLANG -> ('a1, 'a2) rule -> ('a1, 'a2) sequent **)

let conclRule _ _ _ _ _ _ =
  snd

(** val premsRule :
    'a1 eqDec -> 'a1 fLANG -> 'a1 lOGLANG -> 'a2 eqDec -> 'a2 fLANG -> ('a1,
    'a2) sTRLANG -> ('a1, 'a2) rule -> ('a1, 'a2) sequent list **)

let premsRule _ _ _ _ _ _ =
  fst

(** val sequent_eq_dec :
    'a1 eqDec -> 'a1 fLANG -> 'a1 lOGLANG -> 'a2 eqDec -> 'a2 fLANG -> ('a1,
    'a2) sTRLANG -> ('a1, 'a2) sequent -> ('a1, 'a2) sequent -> bool **)

let sequent_eq_dec _ _ _ eDs _ _ s1 s2 =
  let Sequent (x, y) = s1 in
  let Sequent (x0, y0) = s2 in
  if eqdec eDs x x0 then eqdec eDs y y0 else false

(** val eqDec_sequent :
    'a1 eqDec -> 'a1 fLANG -> 'a1 lOGLANG -> 'a2 eqDec -> 'a2 fLANG -> ('a1,
    'a2) sTRLANG -> ('a1, 'a2) sequent eqDec **)

let eqDec_sequent =
  sequent_eq_dec

(** val rule_eq_dec :
    'a1 eqDec -> 'a1 fLANG -> 'a1 lOGLANG -> 'a2 eqDec -> 'a2 fLANG -> ('a1,
    'a2) sTRLANG -> ('a1, 'a2) rule -> ('a1, 'a2) rule -> bool **)

let rule_eq_dec eDf lf lL eDs ls sL r1 r2 =
  let a,b = r1 in
  let l,s = r2 in
  if eqdec (eqDec_list (eqDec_sequent eDf lf lL eDs ls sL)) a l
  then eqdec (eqDec_sequent eDf lf lL eDs ls sL) b s
  else false

(** val eqDec_rule :
    'a1 eqDec -> 'a1 fLANG -> 'a1 lOGLANG -> 'a2 eqDec -> 'a2 fLANG -> ('a1,
    'a2) sTRLANG -> ('a1, 'a2) rule eqDec **)

let eqDec_rule =
  rule_eq_dec

(** val strIsFml_sig :
    'a1 eqDec -> 'a1 fLANG -> 'a1 lOGLANG -> 'a2 eqDec -> 'a2 fLANG -> ('a1,
    'a2) sTRLANG -> 'a2 -> 'a1 **)

let strIsFml_sig _ _ _ eDs ls sL x =
  let s = var_dec eDs ls sL.fS sL.fSVAR x in
  (match s with
   | Some s0 -> s0
   | None -> assert false (* absurd case *))

(** val strIsFml_dec :
    'a1 eqDec -> 'a1 fLANG -> 'a1 lOGLANG -> 'a2 eqDec -> 'a2 fLANG -> ('a1,
    'a2) sTRLANG -> 'a2 -> bool **)

let strIsFml_dec _ _ _ eDs ls sL x =
  let s = var_dec eDs ls sL.fS sL.fSVAR x in
  (match s with
   | Some _ -> true
   | None -> false)

(** val strCtnsFml_dec :
    'a1 eqDec -> 'a1 fLANG -> 'a1 lOGLANG -> 'a2 eqDec -> 'a2 fLANG -> ('a1,
    'a2) sTRLANG -> 'a2 -> bool **)

let strCtnsFml_dec _ _ _ eDs ls sL =
  ipse_rect eDs ls (fun x iHX ->
    let s = var_dec eDs ls sL.fS sL.fSVAR x in
    (match s with
     | Some _ -> true
     | None ->
       let x0 = fun l -> let _,x0 = forallT_forall eDs l in x0 in
       let iHX0 = x0 (ls.ipse x) iHX in
       let iHX1 = forallT_dec_E_sumbool (ls.ipse x) iHX0 in
       (match iHX1 with
        | Inl _ -> true
        | Inr _ -> false)))

(** val strAtms :
    'a1 eqDec -> 'a1 fLANG -> 'a1 lOGLANG -> 'a2 eqDec -> 'a2 fLANG -> ('a1,
    'a2) sTRLANG -> 'a2 -> string list **)

let strAtms eDf lf lL eDs ls sL =
  ipse_rect eDs ls (fun x iH ->
    match var_dec eDs ls sL.fS sL.fSVAR x with
    | Some s -> fmlAtms eDf lf lL s
    | None ->
      list_union (ls.ipse x) (fun x' ->
        if in_dec (eqdec eDs) x' (ls.ipse x) then iH x' __ else []))

(** val strFVs :
    'a1 eqDec -> 'a1 fLANG -> 'a1 lOGLANG -> 'a2 eqDec -> 'a2 fLANG -> ('a1,
    'a2) sTRLANG -> 'a2 -> string list **)

let strFVs eDf lf lL eDs ls sL =
  ipse_rect eDs ls (fun x iH ->
    match var_dec eDs ls sL.fS sL.fSVAR x with
    | Some s -> fmlFVs eDf lf lL s
    | None ->
      list_union (ls.ipse x) (fun x' ->
        if in_dec (eqdec eDs) x' (ls.ipse x) then iH x' __ else []))

(** val strSVs :
    'a1 eqDec -> 'a1 fLANG -> 'a1 lOGLANG -> 'a2 eqDec -> 'a2 fLANG -> ('a1,
    'a2) sTRLANG -> 'a2 -> string list **)

let strSVs _ _ _ eDs ls sL =
  allVars eDs ls sL.sV sL.sVVAR

(** val seqAtms :
    'a1 eqDec -> 'a1 fLANG -> 'a1 lOGLANG -> 'a2 eqDec -> 'a2 fLANG -> ('a1,
    'a2) sTRLANG -> ('a1, 'a2) sequent -> string list **)

let seqAtms eDf lf lL eDs ls sL seq =
  app (strAtms eDf lf lL eDs ls sL (antec eDf lf lL eDs ls sL seq))
    (strAtms eDf lf lL eDs ls sL (succ eDf lf lL eDs ls sL seq))

(** val seqFVs :
    'a1 eqDec -> 'a1 fLANG -> 'a1 lOGLANG -> 'a2 eqDec -> 'a2 fLANG -> ('a1,
    'a2) sTRLANG -> ('a1, 'a2) sequent -> string list **)

let seqFVs eDf lf lL eDs ls sL seq =
  app (strFVs eDf lf lL eDs ls sL (antec eDf lf lL eDs ls sL seq))
    (strFVs eDf lf lL eDs ls sL (succ eDf lf lL eDs ls sL seq))

(** val seqSVs :
    'a1 eqDec -> 'a1 fLANG -> 'a1 lOGLANG -> 'a2 eqDec -> 'a2 fLANG -> ('a1,
    'a2) sTRLANG -> ('a1, 'a2) sequent -> string list **)

let seqSVs eDf lf lL eDs ls sL seq =
  app (strSVs eDf lf lL eDs ls sL (antec eDf lf lL eDs ls sL seq))
    (strSVs eDf lf lL eDs ls sL (succ eDf lf lL eDs ls sL seq))

type 'structr sSubst = string -> 'structr

type ('formula, 'structr) afsSubst = 'formula afSubst*'structr sSubst

(** val strSubst :
    'a1 eqDec -> 'a1 fLANG -> 'a1 lOGLANG -> 'a2 eqDec -> 'a2 fLANG -> ('a1,
    'a2) sTRLANG -> ('a1, 'a2) afsSubst -> 'a2 -> 'a2 **)

let strSubst eDf lf lL eDs ls sL afs =
  ipse_rect eDs ls (fun x iH ->
    match var_dec eDs ls sL.sV sL.sVVAR x with
    | Some s -> snd afs s
    | None ->
      (match var_dec eDs ls sL.fS sL.fSVAR x with
       | Some s -> sL.fS (fmlSubst eDf lf lL (fst afs) s)
       | None ->
         ls.conn x
           (list_union (ls.ipse x) (fun x' ->
             if in_dec (eqdec eDs) x' (ls.ipse x) then (iH x' __)::[] else []))))

(** val seqSubst :
    'a1 eqDec -> 'a1 fLANG -> 'a1 lOGLANG -> 'a2 eqDec -> 'a2 fLANG -> ('a1,
    'a2) sTRLANG -> ('a1, 'a2) afsSubst -> ('a1, 'a2) sequent -> ('a1, 'a2)
    sequent **)

let seqSubst eDf lf lL eDs ls sL afs = function
| Sequent (x, y) ->
  Sequent ((strSubst eDf lf lL eDs ls sL afs x),
    (strSubst eDf lf lL eDs ls sL afs y))

(** val ruleSubst :
    'a1 eqDec -> 'a1 fLANG -> 'a1 lOGLANG -> 'a2 eqDec -> 'a2 fLANG -> ('a1,
    'a2) sTRLANG -> ('a1, 'a2) afsSubst -> ('a1, 'a2) rule -> ('a1, 'a2) rule **)

let ruleSubst eDf lf lL eDs ls sL afs = function
| ps,c ->
  (map (seqSubst eDf lf lL eDs ls sL afs) ps),(seqSubst eDf lf lL eDs ls sL
                                                afs c)

(** val i_s :
    'a1 eqDec -> 'a1 fLANG -> 'a1 lOGLANG -> 'a2 eqDec -> 'a2 fLANG -> ('a1,
    'a2) sTRLANG -> 'a2 sSubst **)

let i_s _ _ _ _ _ sL x =
  sL.sV x

(** val str_matchsub_Atm :
    'a1 eqDec -> 'a1 fLANG -> 'a1 lOGLANG -> 'a2 eqDec -> 'a2 fLANG -> ('a1,
    'a2) sTRLANG -> 'a2 -> 'a2 -> aSubst **)

let str_matchsub_Atm eDf lf lL eDs ls sL =
  ipse_rect eDs ls (fun x iH y ->
    match var_dec eDs ls sL.fS sL.fSVAR x with
    | Some s ->
      (match var_dec eDs ls sL.fS sL.fSVAR y with
       | Some s0 -> fml_matchsub_Atm eDf lf lL s s0
       | None ->
         (fun p ->
           match in_some_dec eqDec_string p
                   (zip (fun x0 x1 -> x0,x1) (ls.ipse x) (ls.ipse y))
                   (comp (strAtms eDf lf lL eDs ls sL) fst) with
           | Some s0 -> iH (fst s0) __ (snd s0) p
           | None -> p))
    | None ->
      (fun p ->
        match in_some_dec eqDec_string p
                (zip (fun x0 x1 -> x0,x1) (ls.ipse x) (ls.ipse y))
                (comp (strAtms eDf lf lL eDs ls sL) fst) with
        | Some s -> iH (fst s) __ (snd s) p
        | None -> p))

(** val str_matchsub_FV :
    'a1 eqDec -> 'a1 fLANG -> 'a1 lOGLANG -> 'a2 eqDec -> 'a2 fLANG -> ('a1,
    'a2) sTRLANG -> 'a2 -> 'a2 -> 'a1 fSubst **)

let str_matchsub_FV eDf lf lL eDs ls sL =
  ipse_rect eDs ls (fun x iH y ->
    match var_dec eDs ls sL.fS sL.fSVAR x with
    | Some s ->
      (match var_dec eDs ls sL.fS sL.fSVAR y with
       | Some s0 -> fml_matchsub_FV eDf lf lL s s0
       | None ->
         (fun v ->
           match in_some_dec eqDec_string v
                   (zip (fun x0 x1 -> x0,x1) (ls.ipse x) (ls.ipse y))
                   (comp (strFVs eDf lf lL eDs ls sL) fst) with
           | Some s0 -> iH (fst s0) __ (snd s0) v
           | None -> lL.fV v))
    | None ->
      (fun v ->
        match in_some_dec eqDec_string v
                (zip (fun x0 x1 -> x0,x1) (ls.ipse x) (ls.ipse y))
                (comp (strFVs eDf lf lL eDs ls sL) fst) with
        | Some s -> iH (fst s) __ (snd s) v
        | None -> lL.fV v))

(** val str_matchsub_SV :
    'a1 eqDec -> 'a1 fLANG -> 'a1 lOGLANG -> 'a2 eqDec -> 'a2 fLANG -> ('a1,
    'a2) sTRLANG -> 'a2 -> 'a2 -> 'a2 sSubst **)

let str_matchsub_SV eDf lf lL eDs ls sL =
  ipse_rect eDs ls (fun x iH y x0 ->
    match var_dec eDs ls sL.sV sL.sVVAR x with
    | Some _ -> y
    | None ->
      (match in_some_dec eqDec_string x0
               (zip (fun x1 x2 -> x1,x2) (ls.ipse x) (ls.ipse y))
               (comp (strSVs eDf lf lL eDs ls sL) fst) with
       | Some s -> iH (fst s) __ (snd s) x0
       | None -> sL.sV x0))

(** val seq_matchsub_Atm :
    'a1 eqDec -> 'a1 fLANG -> 'a1 lOGLANG -> 'a2 eqDec -> 'a2 fLANG -> ('a1,
    'a2) sTRLANG -> ('a1, 'a2) sequent -> ('a1, 'a2) sequent -> aSubst **)

let seq_matchsub_Atm eDf lf lL eDs ls sL s t p =
  let Sequent (x1, y1) = s in
  let Sequent (x2, y2) = t in
  if in_dec (eqdec eqDec_string) p (strAtms eDf lf lL eDs ls sL x1)
  then str_matchsub_Atm eDf lf lL eDs ls sL x1 x2 p
  else if in_dec (eqdec eqDec_string) p (strAtms eDf lf lL eDs ls sL y1)
       then str_matchsub_Atm eDf lf lL eDs ls sL y1 y2 p
       else p

(** val seq_matchsub_FV :
    'a1 eqDec -> 'a1 fLANG -> 'a1 lOGLANG -> 'a2 eqDec -> 'a2 fLANG -> ('a1,
    'a2) sTRLANG -> ('a1, 'a2) sequent -> ('a1, 'a2) sequent -> 'a1 fSubst **)

let seq_matchsub_FV eDf lf lL eDs ls sL s t v =
  let Sequent (x1, y1) = s in
  let Sequent (x2, y2) = t in
  if in_dec (eqdec eqDec_string) v (strFVs eDf lf lL eDs ls sL x1)
  then str_matchsub_FV eDf lf lL eDs ls sL x1 x2 v
  else if in_dec (eqdec eqDec_string) v (strFVs eDf lf lL eDs ls sL y1)
       then str_matchsub_FV eDf lf lL eDs ls sL y1 y2 v
       else lL.fV v

(** val seq_matchsub_SV :
    'a1 eqDec -> 'a1 fLANG -> 'a1 lOGLANG -> 'a2 eqDec -> 'a2 fLANG -> ('a1,
    'a2) sTRLANG -> ('a1, 'a2) sequent -> ('a1, 'a2) sequent -> 'a2 sSubst **)

let seq_matchsub_SV eDf lf lL eDs ls sL s t v =
  let Sequent (x1, y1) = s in
  let Sequent (x2, y2) = t in
  if in_dec (eqdec eqDec_string) v (strSVs eDf lf lL eDs ls sL x1)
  then str_matchsub_SV eDf lf lL eDs ls sL x1 x2 v
  else if in_dec (eqdec eqDec_string) v (strSVs eDf lf lL eDs ls sL y1)
       then str_matchsub_SV eDf lf lL eDs ls sL y1 y2 v
       else sL.sV v

(** val seq_matchsub :
    'a1 eqDec -> 'a1 fLANG -> 'a1 lOGLANG -> 'a2 eqDec -> 'a2 fLANG -> ('a1,
    'a2) sTRLANG -> ('a1, 'a2) sequent -> ('a1, 'a2) sequent -> ('a1, 'a2)
    afsSubst **)

let seq_matchsub eDf lf lL eDs ls sL s t =
  ((seq_matchsub_Atm eDf lf lL eDs ls sL s t),(seq_matchsub_FV eDf lf lL eDs
                                                ls sL s t)),(seq_matchsub_SV
                                                              eDf lf lL eDs
                                                              ls sL s t)

(** val listseq_matchsub_Atm :
    'a1 eqDec -> 'a1 fLANG -> 'a1 lOGLANG -> 'a2 eqDec -> 'a2 fLANG -> ('a1,
    'a2) sTRLANG -> ('a1, 'a2) sequent list -> ('a1, 'a2) sequent list ->
    aSubst **)

let listseq_matchsub_Atm eDf lf lL eDs ls sL ls0 lt p =
  match in_some_dec eqDec_string p (zip (fun x x0 -> x,x0) ls0 lt)
          (comp (seqAtms eDf lf lL eDs ls sL) fst) with
  | Some s0 -> let s,t = s0 in seq_matchsub_Atm eDf lf lL eDs ls sL s t p
  | None -> p

(** val listseq_matchsub_FV :
    'a1 eqDec -> 'a1 fLANG -> 'a1 lOGLANG -> 'a2 eqDec -> 'a2 fLANG -> ('a1,
    'a2) sTRLANG -> ('a1, 'a2) sequent list -> ('a1, 'a2) sequent list -> 'a1
    fSubst **)

let listseq_matchsub_FV eDf lf lL eDs ls sL ls0 lt v =
  match in_some_dec eqDec_string v (zip (fun x x0 -> x,x0) ls0 lt)
          (comp (seqFVs eDf lf lL eDs ls sL) fst) with
  | Some s0 -> let s,t = s0 in seq_matchsub_FV eDf lf lL eDs ls sL s t v
  | None -> lL.fV v

(** val listseq_matchsub_SV :
    'a1 eqDec -> 'a1 fLANG -> 'a1 lOGLANG -> 'a2 eqDec -> 'a2 fLANG -> ('a1,
    'a2) sTRLANG -> ('a1, 'a2) sequent list -> ('a1, 'a2) sequent list -> 'a2
    sSubst **)

let listseq_matchsub_SV eDf lf lL eDs ls sL ls0 lt v =
  match in_some_dec eqDec_string v (zip (fun x x0 -> x,x0) ls0 lt)
          (comp (seqSVs eDf lf lL eDs ls sL) fst) with
  | Some s0 -> let s,t = s0 in seq_matchsub_SV eDf lf lL eDs ls sL s t v
  | None -> sL.sV v

(** val listseq_matchsub :
    'a1 eqDec -> 'a1 fLANG -> 'a1 lOGLANG -> 'a2 eqDec -> 'a2 fLANG -> ('a1,
    'a2) sTRLANG -> ('a1, 'a2) sequent list -> ('a1, 'a2) sequent list ->
    ('a1, 'a2) afsSubst **)

let listseq_matchsub eDf lf lL eDs ls sL ls0 lt =
  ((listseq_matchsub_Atm eDf lf lL eDs ls sL ls0 lt),(listseq_matchsub_FV eDf
                                                       lf lL eDs ls sL ls0 lt)),
    (listseq_matchsub_SV eDf lf lL eDs ls sL ls0 lt)

(** val listseqSubst_dec :
    'a1 eqDec -> 'a1 fLANG -> 'a1 lOGLANG -> 'a2 eqDec -> 'a2 fLANG -> ('a1,
    'a2) sTRLANG -> ('a1, 'a2) sequent list -> ('a1, 'a2) sequent list ->
    ('a1, 'a2) afsSubst option **)

let listseqSubst_dec eDf lf lL eDs ls sL ls0 lt =
  let s =
    eqdec (eqDec_list (eqDec_sequent eDf lf lL eDs ls sL))
      (map
        (seqSubst eDf lf lL eDs ls sL
          (listseq_matchsub eDf lf lL eDs ls sL ls0 lt)) ls0) lt
  in
  if s then Some (listseq_matchsub eDf lf lL eDs ls sL ls0 lt) else None

(** val ruleSubst_dec :
    'a1 eqDec -> 'a1 fLANG -> 'a1 lOGLANG -> 'a2 eqDec -> 'a2 fLANG -> ('a1,
    'a2) sTRLANG -> ('a1, 'a2) rule -> ('a1, 'a2) rule -> ('a1, 'a2) afsSubst
    option **)

let ruleSubst_dec eDf lf lL eDs ls sL r r' =
  let l,s = r in
  let l0,s0 = r' in listseqSubst_dec eDf lf lL eDs ls sL (s::l) (s0::l0)

(** val ruleInst_ruleSubst :
    'a1 eqDec -> 'a1 fLANG -> 'a1 lOGLANG -> 'a2 eqDec -> 'a2 fLANG -> ('a1,
    'a2) sTRLANG -> ('a1, 'a2) rule -> ('a1, 'a2) rule -> ('a1, 'a2) afsSubst **)

let ruleInst_ruleSubst eDf lf lL eDs ls sL r r' =
  let s = ruleSubst_dec eDf lf lL eDs ls sL r r' in
  (match s with
   | Some s0 -> s0
   | None -> assert false (* absurd case *))

(** val a_spec : (string*string) list -> aSubst **)

let rec a_spec = function
| [] -> i_a
| p::l' -> (fun x -> let s,t = p in if (=) x s then t else a_spec l' x)

(** val f_spec :
    'a1 eqDec -> 'a1 fLANG -> 'a1 lOGLANG -> (string*'a1) list -> 'a1 fSubst **)

let rec f_spec eDf lf lL = function
| [] -> i_f eDf lf lL
| p::l' ->
  (fun x -> let s,a = p in if (=) x s then a else f_spec eDf lf lL l' x)

(** val s_spec :
    'a1 eqDec -> 'a1 fLANG -> 'a1 lOGLANG -> 'a2 eqDec -> 'a2 fLANG -> ('a1,
    'a2) sTRLANG -> (string*'a2) list -> 'a2 sSubst **)

let rec s_spec eDf lf lL eDs ls sL = function
| [] -> i_s eDf lf lL eDs ls sL
| p::l' ->
  (fun x ->
    let s,x0 = p in if (=) x s then x0 else s_spec eDf lf lL eDs ls sL l' x)

(** val af_spec :
    'a1 eqDec -> 'a1 fLANG -> 'a1 lOGLANG -> (string*string) list ->
    (string*'a1) list -> 'a1 afSubst **)

let af_spec eDf lf lL lp lf0 =
  (a_spec lp),(f_spec eDf lf lL lf0)

(** val afs_spec :
    'a1 eqDec -> 'a1 fLANG -> 'a1 lOGLANG -> 'a2 eqDec -> 'a2 fLANG -> ('a1,
    'a2) sTRLANG -> (string*string) list -> (string*'a1) list -> (string*'a2)
    list -> ('a1, 'a2) afsSubst **)

let afs_spec eDf lf lL eDs ls sL lp lf0 ls0 =
  (af_spec eDf lf lL lp lf0),(s_spec eDf lf lL eDs ls sL ls0)

type ('formula, 'structr) dertree =
| Unf of ('formula, 'structr) sequent
| Der of ('formula, 'structr) sequent * ('formula, 'structr) rule
   * ('formula, 'structr) dertree list

(** val dertree_rect_gen :
    'a1 eqDec -> 'a1 fLANG -> 'a1 lOGLANG -> 'a2 eqDec -> 'a2 fLANG -> ('a1,
    'a2) sTRLANG -> 'a4 -> (('a1, 'a2) dertree -> ('a1, 'a2) dertree list ->
    'a3 -> 'a4 -> 'a4) -> (('a1, 'a2) sequent -> 'a3) -> (('a1, 'a2) sequent
    -> ('a1, 'a2) rule -> ('a1, 'a2) dertree list -> 'a4 -> 'a3) -> ('a1,
    'a2) dertree -> 'a3 **)

let rec dertree_rect_gen eDf lf lL eDs ls sL p_nil p_cons p_Unf p_Der dt =
  let go_list =
    let rec go_list = function
    | [] -> p_nil
    | t::l0 ->
      p_cons t l0
        (dertree_rect_gen eDf lf lL eDs ls sL p_nil p_cons p_Unf p_Der t)
        (go_list l0)
    in go_list
  in
  (match dt with
   | Unf s -> p_Unf s
   | Der (s, r, l) -> p_Der s r l (go_list l))

(** val dertree_eq_dec :
    'a1 eqDec -> 'a1 fLANG -> 'a1 lOGLANG -> 'a2 eqDec -> 'a2 fLANG -> ('a1,
    'a2) sTRLANG -> ('a1, 'a2) dertree -> ('a1, 'a2) dertree -> bool **)

let dertree_eq_dec eDf lf lL eDs ls sL =
  dertree_rect_gen eDf lf lL eDs ls sL (fun l2 ->
    match l2 with
    | [] -> true
    | _::_ -> false) (fun _ _ hd hl l2 ->
    match l2 with
    | [] -> false
    | d::l -> let s = hd d in if s then hl l else false) (fun s d2 ->
    match d2 with
    | Unf s0 -> sequent_eq_dec eDf lf lL eDs ls sL s s0
    | Der (_, _, _) -> false) (fun s1 r1 _ iH d2 ->
    match d2 with
    | Unf _ -> false
    | Der (s, r, l) ->
      let s0 = sequent_eq_dec eDf lf lL eDs ls sL s1 s in
      if s0
      then let s2 = rule_eq_dec eDf lf lL eDs ls sL r1 r in
           if s2 then iH l else false
      else false)

(** val eqDec_dertree :
    'a1 eqDec -> 'a1 fLANG -> 'a1 lOGLANG -> 'a2 eqDec -> 'a2 fLANG -> ('a1,
    'a2) sTRLANG -> ('a1, 'a2) dertree eqDec **)

let eqDec_dertree =
  dertree_eq_dec

(** val nextUp :
    'a1 eqDec -> 'a1 fLANG -> 'a1 lOGLANG -> 'a2 eqDec -> 'a2 fLANG -> ('a1,
    'a2) sTRLANG -> ('a1, 'a2) dertree -> ('a1, 'a2) dertree list **)

let nextUp _ _ _ _ _ _ = function
| Unf _ -> []
| Der (_, _, l) -> l

(** val conclDT :
    'a1 eqDec -> 'a1 fLANG -> 'a1 lOGLANG -> 'a2 eqDec -> 'a2 fLANG -> ('a1,
    'a2) sTRLANG -> ('a1, 'a2) dertree -> ('a1, 'a2) sequent **)

let conclDT _ _ _ _ _ _ = function
| Unf s -> s
| Der (s, _, _) -> s

(** val premsDT :
    'a1 eqDec -> 'a1 fLANG -> 'a1 lOGLANG -> 'a2 eqDec -> 'a2 fLANG -> ('a1,
    'a2) sTRLANG -> ('a1, 'a2) dertree -> ('a1, 'a2) sequent list **)

let rec premsDT eDf lf lL eDs ls sL = function
| Unf s -> s::[]
| Der (_, _, l) ->
  fold_right (fun dt' -> app (premsDT eDf lf lL eDs ls sL dt')) [] l

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

(** val deriv_prseqs_mut_rect :
    'a1 eqDec -> 'a1 fLANG -> 'a1 lOGLANG -> 'a2 eqDec -> 'a2 fLANG -> ('a1,
    'a2) sTRLANG -> ('a1, 'a2) dISPCALC -> ('a1, 'a2) sequent list -> (('a1,
    'a2) sequent -> __ -> 'a3) -> (('a1, 'a2) sequent list -> ('a1, 'a2)
    sequent -> ('a1, 'a2) rule -> __ -> __ -> ('a1, 'a2) deriv_prseqs -> 'a4
    -> 'a3) -> 'a4 -> (('a1, 'a2) sequent -> ('a1, 'a2) sequent list -> ('a1,
    'a2) deriv_prseq -> 'a3 -> ('a1, 'a2) deriv_prseqs -> 'a4 -> 'a4) ->
    ('a1, 'a2) sequent list -> ('a1, 'a2) deriv_prseqs -> 'a4 **)

let deriv_prseqs_mut_rect _ _ _ _ _ _ _ _ f f0 f1 f2 =
  let rec f3 _ = function
  | Deriv_prseq_prem c -> f c __
  | Deriv_prseq_ext (ps, c, r, d0) -> f0 ps c r __ __ d0 (f4 ps d0)
  and f4 _ = function
  | Deriv_prseqs_nil -> f1
  | Deriv_prseqs_cons (c, cs, d0, d1) -> f2 c cs d0 (f3 c d0) d1 (f4 cs d1)
  in f4

(** val deriv_prseq_mut_rect :
    'a1 eqDec -> 'a1 fLANG -> 'a1 lOGLANG -> 'a2 eqDec -> 'a2 fLANG -> ('a1,
    'a2) sTRLANG -> ('a1, 'a2) dISPCALC -> ('a1, 'a2) sequent list -> (('a1,
    'a2) sequent -> __ -> 'a3) -> (('a1, 'a2) sequent list -> ('a1, 'a2)
    sequent -> ('a1, 'a2) rule -> __ -> __ -> ('a1, 'a2) deriv_prseqs -> 'a4
    -> 'a3) -> 'a4 -> (('a1, 'a2) sequent -> ('a1, 'a2) sequent list -> ('a1,
    'a2) deriv_prseq -> 'a3 -> ('a1, 'a2) deriv_prseqs -> 'a4 -> 'a4) ->
    ('a1, 'a2) sequent -> ('a1, 'a2) deriv_prseq -> 'a3 **)

let deriv_prseq_mut_rect _ _ _ _ _ _ _ _ f f0 f1 f2 =
  let rec f3 _ = function
  | Deriv_prseq_prem c -> f c __
  | Deriv_prseq_ext (ps, c, r, d0) -> f0 ps c r __ __ d0 (f4 ps d0)
  and f4 _ = function
  | Deriv_prseqs_nil -> f1
  | Deriv_prseqs_cons (c, cs, d0, d1) -> f2 c cs d0 (f3 c d0) d1 (f4 cs d1)
  in f3

(** val forallT_deriv_prseqs :
    'a1 eqDec -> 'a1 fLANG -> 'a1 lOGLANG -> 'a2 eqDec -> 'a2 fLANG -> ('a1,
    'a2) sTRLANG -> ('a1, 'a2) dISPCALC -> ('a1, 'a2) sequent list -> ('a1,
    'a2) sequent list -> (('a1, 'a2) sequent, ('a1, 'a2) deriv_prseq) forallT
    -> ('a1, 'a2) deriv_prseqs **)

let rec forallT_deriv_prseqs eDf lf lL eDs ls sL dC ps cs hall =
  match cs with
  | [] -> Deriv_prseqs_nil
  | y::l ->
    Deriv_prseqs_cons (y, l, (forallT_inv y l hall),
      (forallT_deriv_prseqs eDf lf lL eDs ls sL dC ps l
        (forallT_inv_tail y l hall)))

(** val forallT_deriv_prseqs_iff :
    'a1 eqDec -> 'a1 fLANG -> 'a1 lOGLANG -> 'a2 eqDec -> 'a2 fLANG -> ('a1,
    'a2) sTRLANG -> ('a1, 'a2) dISPCALC -> ('a1, 'a2) sequent list -> ('a1,
    'a2) sequent list -> ((('a1, 'a2) sequent, ('a1, 'a2) deriv_prseq)
    forallT, ('a1, 'a2) deriv_prseqs) iffT0 **)

let forallT_deriv_prseqs_iff eDf lf lL eDs ls sL dC ps cs =
  (forallT_deriv_prseqs eDf lf lL eDs ls sL dC ps cs),(deriv_prseqs_mut_rect
                                                        eDf lf lL eDs ls sL
                                                        dC ps (fun x _ ->
                                                        Deriv_prseq_prem x)
                                                        (fun ss c r _ _ hders _ ->
                                                        Deriv_prseq_ext (ss,
                                                        c, r, hders))
                                                        ForallT_nil
                                                        (fun c cs0 hder _ _ hallders ->
                                                        ForallT_cons (c, cs0,
                                                        hder, hallders)) cs)

(** val deriv_prseq_weak :
    'a1 eqDec -> 'a1 fLANG -> 'a1 lOGLANG -> 'a2 eqDec -> 'a2 fLANG -> ('a1,
    'a2) sTRLANG -> ('a1, 'a2) dISPCALC -> ('a1, 'a2) sequent list -> ('a1,
    'a2) sequent list -> ('a1, 'a2) sequent -> ('a1, 'a2) deriv_prseq ->
    ('a1, 'a2) deriv_prseq **)

let deriv_prseq_weak eDf lf lL eDs ls sL dC ps _ c =
  deriv_prseq_mut_rect eDf lf lL eDs ls sL dC ps (fun c0 _ ->
    Deriv_prseq_prem c0) (fun cs c0 r _ _ _ hders' -> Deriv_prseq_ext (cs,
    c0, r, hders')) Deriv_prseqs_nil (fun c0 cs _ hder' _ hders' ->
    Deriv_prseqs_cons (c0, cs, hder', hders')) c

(** val deriv_prseq_tran :
    'a1 eqDec -> 'a1 fLANG -> 'a1 lOGLANG -> 'a2 eqDec -> 'a2 fLANG -> ('a1,
    'a2) sTRLANG -> ('a1, 'a2) dISPCALC -> ('a1, 'a2) sequent list -> ('a1,
    'a2) sequent list -> ('a1, 'a2) sequent -> ('a1, 'a2) deriv_prseqs ->
    ('a1, 'a2) deriv_prseq -> ('a1, 'a2) deriv_prseq **)

let deriv_prseq_tran eDf lf lL eDs ls sL dC ps ss c hders hder =
  deriv_prseq_mut_rect eDf lf lL eDs ls sL dC ss (fun c0 _ ->
    let x = fun ps0 cs ->
      let _,x = forallT_deriv_prseqs_iff eDf lf lL eDs ls sL dC ps0 cs in x
    in
    let hders0 = x ps ss hders in
    let hders1 =
      let lemma = forallT_forall (eqDec_sequent eDf lf lL eDs ls sL) ss in
      iffT_arrow_subrelation (Obj.magic lemma) (Obj.magic hders0)
    in
    Obj.magic hders1 c0 __) (fun ts c0 r _ _ _ hpsders -> Deriv_prseq_ext
    (ts, c0, r, hpsders)) Deriv_prseqs_nil (fun c0 cs _ hpsder _ hpsders ->
    Deriv_prseqs_cons (c0, cs, hpsder, hpsders)) c hder

(** val deriv_prseq_tran_afs :
    'a1 eqDec -> 'a1 fLANG -> 'a1 lOGLANG -> 'a2 eqDec -> 'a2 fLANG -> ('a1,
    'a2) sTRLANG -> ('a1, 'a2) dISPCALC -> ('a1, 'a2) sequent list -> ('a1,
    'a2) sequent list -> ('a1, 'a2) sequent -> ('a1, 'a2) afsSubst -> ('a1,
    'a2) deriv_prseqs -> ('a1, 'a2) deriv_prseq -> ('a1, 'a2) deriv_prseq **)

let deriv_prseq_tran_afs eDf lf lL eDs ls sL dC ps ss c afs hders hder =
  deriv_prseq_mut_rect eDf lf lL eDs ls sL dC ss (fun c0 _ ->
    let x = fun ps0 cs ->
      let _,x = forallT_deriv_prseqs_iff eDf lf lL eDs ls sL dC ps0 cs in x
    in
    let hders0 = x ps (map (seqSubst eDf lf lL eDs ls sL afs) ss) hders in
    let hders1 =
      let lemma =
        forallT_forall (eqDec_sequent eDf lf lL eDs ls sL)
          (map (seqSubst eDf lf lL eDs ls sL afs) ss)
      in
      iffT_arrow_subrelation (Obj.magic lemma) (Obj.magic hders0)
    in
    Obj.magic hders1 (seqSubst eDf lf lL eDs ls sL afs c0) __)
    (fun ts c0 r _ _ _ hpsders -> Deriv_prseq_ext
    ((map (seqSubst eDf lf lL eDs ls sL afs) ts),
    (seqSubst eDf lf lL eDs ls sL afs c0), r, hpsders)) Deriv_prseqs_nil
    (fun c0 cs _ hpsder _ hpsders -> Deriv_prseqs_cons
    ((seqSubst eDf lf lL eDs ls sL afs c0),
    (let rec map0 = function
     | [] -> []
     | a::t -> (seqSubst eDf lf lL eDs ls sL afs a)::(map0 t)
     in map0 cs), hpsder, hpsders)) c hder

(** val deriv_rule_Inst :
    'a1 eqDec -> 'a1 fLANG -> 'a1 lOGLANG -> 'a2 eqDec -> 'a2 fLANG -> ('a1,
    'a2) sTRLANG -> ('a1, 'a2) dISPCALC -> ('a1, 'a2) rule -> ('a1, 'a2) rule
    -> ('a1, 'a2) deriv_rule -> ('a1, 'a2) deriv_rule **)

let deriv_rule_Inst eDf lf lL eDs ls sL dC r r' =
  let hins = ruleInst_ruleSubst eDf lf lL eDs ls sL r r' in
  let l,s = r in
  Obj.magic deriv_prseq_mut_rect eDf lf lL eDs ls sL dC l (fun c _ ->
    Deriv_prseq_prem (seqSubst eDf lf lL eDs ls sL hins c))
    (fun ss c r0 _ _ _ hders' -> Deriv_prseq_ext
    ((map (seqSubst eDf lf lL eDs ls sL hins) ss),
    (seqSubst eDf lf lL eDs ls sL hins c), r0, hders')) Deriv_prseqs_nil
    (fun c cs _ hder' _ hders' -> Deriv_prseqs_cons
    ((seqSubst eDf lf lL eDs ls sL hins c),
    (let rec map0 = function
     | [] -> []
     | a::t -> (seqSubst eDf lf lL eDs ls sL hins a)::(map0 t)
     in map0 cs), hder', hders')) s

(** val deriv_rule_replace :
    'a1 eqDec -> 'a1 fLANG -> 'a1 lOGLANG -> 'a2 eqDec -> 'a2 fLANG -> ('a1,
    'a2) sTRLANG -> ('a1, 'a2) dISPCALC -> ('a1, 'a2) dISPCALC -> ('a1, 'a2)
    rule -> (('a1, 'a2) rule, ('a1, 'a2) deriv_rule) forallT -> ('a1, 'a2)
    deriv_rule -> ('a1, 'a2) deriv_rule **)

let deriv_rule_replace eDf lf lL eDs ls sL dC1 dC2 r hderDC =
  let l,s = r in
  Obj.magic deriv_prseq_mut_rect eDf lf lL eDs ls sL dC1 l (fun x _ ->
    Deriv_prseq_prem x) (fun ss c r0 _ _ _ hders2 ->
    deriv_prseq_tran eDf lf lL eDs ls sL dC2 l ss c hders2
      (Obj.magic deriv_rule_Inst eDf lf lL eDs ls sL dC2 r0 (ss,c)
        (let hderDC0 =
           let lemma = forallT_forall (eqDec_rule eDf lf lL eDs ls sL) dC1 in
           iffT_arrow_subrelation (Obj.magic lemma) (Obj.magic hderDC)
         in
         Obj.magic hderDC0 r0 __))) Deriv_prseqs_nil
    (fun c cs _ hder2 _ hders2 -> Deriv_prseqs_cons (c, cs, hder2, hders2)) s

(** val cUT :
    'a1 eqDec -> 'a1 fLANG -> 'a1 lOGLANG -> 'a2 eqDec -> 'a2 fLANG -> ('a1,
    'a2) sTRLANG -> ('a1, 'a2) rule **)

let cUT _ _ lL _ _ sL =
  ((Sequent ((sL.sV "X"), (sL.fS (lL.fV "A"))))::((Sequent
    ((sL.fS (lL.fV "A")), (sL.sV "Y")))::[])),(Sequent ((sL.sV "X"),
    (sL.sV "Y")))

(** val cUT_spec :
    'a1 eqDec -> 'a1 fLANG -> 'a1 lOGLANG -> 'a2 eqDec -> 'a2 fLANG -> ('a1,
    'a2) sTRLANG -> 'a1 -> 'a2 -> 'a2 -> ('a1, 'a2) afsSubst **)

let cUT_spec eDf lf lL eDs ls sL a x y =
  afs_spec eDf lf lL eDs ls sL [] (("A",a)::[]) (("X",x)::(("Y",y)::[]))

(** val remove_rule :
    'a1 eqDec -> 'a1 fLANG -> 'a1 lOGLANG -> 'a2 eqDec -> 'a2 fLANG -> ('a1,
    'a2) sTRLANG -> ('a1, 'a2) rule -> ('a1, 'a2) rule list -> ('a1, 'a2)
    rule list **)

let remove_rule eDf lf lL eDs ls sL =
  remove (rule_eq_dec eDf lf lL eDs ls sL)

(** val lP_dec :
    'a1 eqDec -> 'a1 fLANG -> 'a1 lOGLANG -> 'a2 eqDec -> 'a2 fLANG -> ('a1,
    'a2) sTRLANG -> ('a1, 'a2) dertree list -> 'a1 -> ('a2, (('a1, 'a2) rule,
    (('a1, 'a2) dertree list, ('a1, 'a2) dertree) sigT) sigT) sigT option **)

let lP_dec eDf lf lL eDs ls sL l a =
  let s = list_2_elems_dec l in
  (match s with
   | Some s0 ->
     let ExistT (x, s1) = s0 in
     let ExistT (x0, _) = s1 in
     (match x with
      | Unf _ -> None
      | Der (s2, r, l0) ->
        let Sequent (x1, y) = s2 in
        let s3 = eqdec eDs y (sL.fS a) in
        if s3
        then let s4 =
               strIsFml_dec eDf lf lL eDs ls sL
                 (succ eDf lf lL eDs ls sL (conclRule eDf lf lL eDs ls sL r))
             in
             if s4
             then Some (ExistT (x1, (ExistT (r, (ExistT (l0, x0))))))
             else None
        else None)
   | None -> None)

(** val rP_dec :
    'a1 eqDec -> 'a1 fLANG -> 'a1 lOGLANG -> 'a2 eqDec -> 'a2 fLANG -> ('a1,
    'a2) sTRLANG -> ('a1, 'a2) dertree list -> 'a1 -> ('a2, (('a1, 'a2)
    dertree, (('a1, 'a2) rule, ('a1, 'a2) dertree list) sigT) sigT) sigT
    option **)

let rP_dec eDf lf lL eDs ls sL l a =
  let s = list_2_elems_dec l in
  (match s with
   | Some s0 ->
     let ExistT (x, s1) = s0 in
     let ExistT (x0, _) = s1 in
     (match x0 with
      | Unf _ -> None
      | Der (s2, r, l0) ->
        let Sequent (x1, y) = s2 in
        let s3 = eqdec eDs x1 (sL.fS a) in
        if s3
        then let s4 =
               strIsFml_dec eDf lf lL eDs ls sL
                 (antec eDf lf lL eDs ls sL (conclRule eDf lf lL eDs ls sL r))
             in
             if s4
             then Some (ExistT (y, (ExistT (x, (ExistT (r, l0))))))
             else None
        else None)
   | None -> None)

(** val right_cut_dec :
    'a1 eqDec -> 'a1 fLANG -> 'a1 lOGLANG -> 'a2 eqDec -> 'a2 fLANG -> ('a1,
    'a2) sTRLANG -> ('a1, 'a2) dertree list -> (('a1, 'a2) dertree, (('a1,
    'a2) dertree, ('a2, 'a1) sigT) sigT) sigT option **)

let right_cut_dec eDf lf lL eDs ls sL l =
  let s = list_2_elems_dec l in
  (match s with
   | Some s0 ->
     let ExistT (x, s1) = s0 in
     let ExistT (x0, _) = s1 in
     let s2 = conclDT eDf lf lL eDs ls sL x0 in
     let Sequent (x1, y) = s2 in
     let s3 = strIsFml_dec eDf lf lL eDs ls sL x1 in
     if s3
     then Some
            (let s4 = strIsFml_sig eDf lf lL eDs ls sL x1 in
             ExistT (x, (ExistT (x0, (ExistT (y, s4))))))
     else None
   | None -> None)

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

(** val deriv_cofseqs_mut_rect :
    'a1 eqDec -> 'a1 fLANG -> 'a1 lOGLANG -> 'a2 eqDec -> 'a2 fLANG -> ('a1,
    'a2) sTRLANG -> ('a1, 'a2) dISPCALC -> (('a1, 'a2) sequent list -> ('a1,
    'a2) sequent -> ('a1, 'a2) rule -> __ -> __ -> __ -> ('a1, 'a2)
    deriv_cofseqs -> 'a4 -> 'a3) -> 'a4 -> (('a1, 'a2) sequent -> ('a1, 'a2)
    sequent list -> ('a1, 'a2) deriv_cofseq -> 'a3 -> ('a1, 'a2)
    deriv_cofseqs -> 'a4 -> 'a4) -> ('a1, 'a2) sequent list -> ('a1, 'a2)
    deriv_cofseqs -> 'a4 **)

let deriv_cofseqs_mut_rect _ _ _ _ _ _ _ f f0 f1 =
  let rec f2 _ = function
  | Deriv_cofseq_ext (ps, c, r, d0) -> f ps c r __ __ __ d0 (f3 ps d0)
  and f3 _ = function
  | Deriv_cofseqs_nil -> f0
  | Deriv_cofseqs_cons (c, cs, d0, d1) -> f1 c cs d0 (f2 c d0) d1 (f3 cs d1)
  in f3

(** val deriv_cofseq_mut_rect :
    'a1 eqDec -> 'a1 fLANG -> 'a1 lOGLANG -> 'a2 eqDec -> 'a2 fLANG -> ('a1,
    'a2) sTRLANG -> ('a1, 'a2) dISPCALC -> (('a1, 'a2) sequent list -> ('a1,
    'a2) sequent -> ('a1, 'a2) rule -> __ -> __ -> __ -> ('a1, 'a2)
    deriv_cofseqs -> 'a4 -> 'a3) -> 'a4 -> (('a1, 'a2) sequent -> ('a1, 'a2)
    sequent list -> ('a1, 'a2) deriv_cofseq -> 'a3 -> ('a1, 'a2)
    deriv_cofseqs -> 'a4 -> 'a4) -> ('a1, 'a2) sequent -> ('a1, 'a2)
    deriv_cofseq -> 'a3 **)

let deriv_cofseq_mut_rect _ _ _ _ _ _ _ f f0 f1 =
  let rec f2 _ = function
  | Deriv_cofseq_ext (ps, c, r, d0) -> f ps c r __ __ __ d0 (f3 ps d0)
  and f3 _ = function
  | Deriv_cofseqs_nil -> f0
  | Deriv_cofseqs_cons (c, cs, d0, d1) -> f1 c cs d0 (f2 c d0) d1 (f3 cs d1)
  in f2

(** val deriv_cofprseq_mut_rect :
    'a1 eqDec -> 'a1 fLANG -> 'a1 lOGLANG -> 'a2 eqDec -> 'a2 fLANG -> ('a1,
    'a2) sTRLANG -> ('a1, 'a2) dISPCALC -> ('a1, 'a2) sequent list -> (('a1,
    'a2) sequent -> __ -> 'a3) -> (('a1, 'a2) sequent list -> ('a1, 'a2)
    sequent -> ('a1, 'a2) rule -> __ -> __ -> __ -> ('a1, 'a2)
    deriv_cofprseqs -> 'a4 -> 'a3) -> 'a4 -> (('a1, 'a2) sequent -> ('a1,
    'a2) sequent list -> ('a1, 'a2) deriv_cofprseq -> 'a3 -> ('a1, 'a2)
    deriv_cofprseqs -> 'a4 -> 'a4) -> ('a1, 'a2) sequent -> ('a1, 'a2)
    deriv_cofprseq -> 'a3 **)

let deriv_cofprseq_mut_rect _ _ _ _ _ _ _ _ f f0 f1 f2 =
  let rec f3 _ = function
  | Deriv_cofprseq_prem c -> f c __
  | Deriv_cofprseq_ext (ps, c, r, d0) -> f0 ps c r __ __ __ d0 (f4 ps d0)
  and f4 _ = function
  | Deriv_cofprseqs_nil -> f1
  | Deriv_cofprseqs_cons (c, cs, d0, d1) -> f2 c cs d0 (f3 c d0) d1 (f4 cs d1)
  in f3

type ('formula, 'structr) deriv_ncprseq = ('formula, 'structr) deriv_cofprseq

(** val forallT_deriv_cofseqs :
    'a1 eqDec -> 'a1 fLANG -> 'a1 lOGLANG -> 'a2 eqDec -> 'a2 fLANG -> ('a1,
    'a2) sTRLANG -> ('a1, 'a2) dISPCALC -> ('a1, 'a2) sequent list -> (('a1,
    'a2) sequent, ('a1, 'a2) deriv_cofseq) forallT -> ('a1, 'a2) deriv_cofseqs **)

let rec forallT_deriv_cofseqs eDf lf lL eDs ls sL dC cs hall =
  match cs with
  | [] -> Deriv_cofseqs_nil
  | y::l ->
    Deriv_cofseqs_cons (y, l, (forallT_inv y l hall),
      (forallT_deriv_cofseqs eDf lf lL eDs ls sL dC l
        (forallT_inv_tail y l hall)))

(** val forallT_deriv_cofseqs_iff :
    'a1 eqDec -> 'a1 fLANG -> 'a1 lOGLANG -> 'a2 eqDec -> 'a2 fLANG -> ('a1,
    'a2) sTRLANG -> ('a1, 'a2) dISPCALC -> ('a1, 'a2) sequent list -> ((('a1,
    'a2) sequent, ('a1, 'a2) deriv_cofseq) forallT, ('a1, 'a2) deriv_cofseqs)
    iffT0 **)

let forallT_deriv_cofseqs_iff eDf lf lL eDs ls sL dC cs =
  (forallT_deriv_cofseqs eDf lf lL eDs ls sL dC cs),(deriv_cofseqs_mut_rect
                                                      eDf lf lL eDs ls sL dC
                                                      (fun ps c r _ _ _ hders _ ->
                                                      Deriv_cofseq_ext (ps,
                                                      c, r, hders))
                                                      ForallT_nil
                                                      (fun c cs0 hder _ _ hallders ->
                                                      ForallT_cons (c, cs0,
                                                      hder, hallders)) cs)

(** val forallT_deriv_cofprseqs :
    'a1 eqDec -> 'a1 fLANG -> 'a1 lOGLANG -> 'a2 eqDec -> 'a2 fLANG -> ('a1,
    'a2) sTRLANG -> ('a1, 'a2) dISPCALC -> ('a1, 'a2) sequent list -> ('a1,
    'a2) sequent list -> (('a1, 'a2) sequent, ('a1, 'a2) deriv_cofprseq)
    forallT -> ('a1, 'a2) deriv_cofprseqs **)

let rec forallT_deriv_cofprseqs eDf lf lL eDs ls sL dC ps cs hall =
  match cs with
  | [] -> Deriv_cofprseqs_nil
  | y::l ->
    Deriv_cofprseqs_cons (y, l, (forallT_inv y l hall),
      (forallT_deriv_cofprseqs eDf lf lL eDs ls sL dC ps l
        (forallT_inv_tail y l hall)))

(** val deriv_cofseq_iff :
    'a1 eqDec -> 'a1 fLANG -> 'a1 lOGLANG -> 'a2 eqDec -> 'a2 fLANG -> ('a1,
    'a2) sTRLANG -> ('a1, 'a2) dISPCALC -> ('a1, 'a2) sequent -> (('a1, 'a2)
    deriv_cofseq, ('a1, 'a2) dertree) iffT0 **)

let deriv_cofseq_iff eDf lf lL eDs ls sL dC s =
  (deriv_cofseq_mut_rect eDf lf lL eDs ls sL dC (fun _ c r _ _ _ _ x -> Der
    (c, r, x)) [] (fun _ _ _ x _ x0 -> x::x0) s),(fun x ->
    dertree_rect_gen eDf lf lL eDs ls sL ForallT_nil (fun t l pt pl ->
      ForallT_cons (t, l, pt, pl)) (fun _ _ _ -> assert false
      (* absurd case *)) (fun s0 r l iH _ _ ->
      let x0 = fun l0 ->
        let x0,_ = forall_ForallT (eqDec_dertree eDf lf lL eDs ls sL) l0 in
        Obj.magic x0
      in
      let hprol = x0 l __ in
      let x1 = fun l0 ->
        let x1,_ = forall_ForallT (eqDec_dertree eDf lf lL eDs ls sL) l0 in
        Obj.magic x1
      in
      let hcofl = x1 l __ in
      let iH0 = forallT_mp l hprol iH in
      let iH1 = forallT_mp l hcofl iH0 in
      let x2 = fun f l0 -> let _,x2 = forallT_map f l0 in x2 in
      let iH2 = x2 (conclDT eDf lf lL eDs ls sL) l iH1 in
      let iH3 =
        forallT_deriv_cofseqs eDf lf lL eDs ls sL dC
          (map (conclDT eDf lf lL eDs ls sL) l) iH2
      in
      Deriv_cofseq_ext ((map (conclDT eDf lf lL eDs ls sL) l), s0, r, iH3)) x
      __ __)

(** val deriv_cofseqs_iff :
    'a1 eqDec -> 'a1 fLANG -> 'a1 lOGLANG -> 'a2 eqDec -> 'a2 fLANG -> ('a1,
    'a2) sTRLANG -> ('a1, 'a2) dISPCALC -> ('a1, 'a2) sequent list -> (('a1,
    'a2) deriv_cofseqs, ('a1, 'a2) dertree list) iffT0 **)

let deriv_cofseqs_iff eDf lf lL eDs ls sL dC ls0 =
  (deriv_cofseqs_mut_rect eDf lf lL eDs ls sL dC (fun _ c r _ _ _ _ x -> Der
    (c, r, x)) [] (fun _ _ _ x _ x0 -> x::x0) ls0),(fun x ->
    let x0,_ = forallT_deriv_cofseqs_iff eDf lf lL eDs ls sL dC ls0 in
    x0
      (forallT_act ls0 (fun s ->
        let _,x1 = deriv_cofseq_iff eDf lf lL eDs ls sL dC s in x1)
        (let _,x1 = forallT_forall (eqDec_sequent eDf lf lL eDs ls sL) ls0 in
         x1 (fun s _ ->
           in_map_inv_sig (eqDec_sequent eDf lf lL eDs ls sL)
             (conclDT eDf lf lL eDs ls sL) x s))))

(** val deriv_cofprseq_weak :
    'a1 eqDec -> 'a1 fLANG -> 'a1 lOGLANG -> 'a2 eqDec -> 'a2 fLANG -> ('a1,
    'a2) sTRLANG -> ('a1, 'a2) dISPCALC -> ('a1, 'a2) sequent list -> ('a1,
    'a2) sequent list -> ('a1, 'a2) sequent -> ('a1, 'a2) deriv_cofprseq ->
    ('a1, 'a2) deriv_cofprseq **)

let deriv_cofprseq_weak eDf lf lL eDs ls sL dC ps _ c =
  deriv_cofprseq_mut_rect eDf lf lL eDs ls sL dC ps (fun c0 _ ->
    Deriv_cofprseq_prem c0) (fun cs c0 r _ _ _ _ hders' -> Deriv_cofprseq_ext
    (cs, c0, r, hders')) Deriv_cofprseqs_nil (fun c0 cs _ hder' _ hders' ->
    Deriv_cofprseqs_cons (c0, cs, hder', hders')) c

(** val deriv_cofseq_tran_afs :
    'a1 eqDec -> 'a1 fLANG -> 'a1 lOGLANG -> 'a2 eqDec -> 'a2 fLANG -> ('a1,
    'a2) sTRLANG -> ('a1, 'a2) dISPCALC -> ('a1, 'a2) sequent list -> ('a1,
    'a2) sequent -> ('a1, 'a2) afsSubst -> ('a1, 'a2) deriv_ncprseq -> ('a1,
    'a2) deriv_cofseqs -> ('a1, 'a2) deriv_cofseq **)

let deriv_cofseq_tran_afs eDf lf lL eDs ls sL dC ps c afs hder hders =
  deriv_cofprseq_mut_rect eDf lf lL eDs ls sL dC ps (fun c0 _ ->
    let x = fun dC0 cs ->
      let _,x = forallT_deriv_cofseqs_iff eDf lf lL eDs ls sL dC0 cs in x
    in
    let hders0 = x dC (map (seqSubst eDf lf lL eDs ls sL afs) ps) hders in
    let hders1 =
      let lemma =
        forallT_forall (eqDec_sequent eDf lf lL eDs ls sL)
          (map (seqSubst eDf lf lL eDs ls sL afs) ps)
      in
      iffT_arrow_subrelation (Obj.magic lemma) (Obj.magic hders0)
    in
    Obj.magic hders1 (seqSubst eDf lf lL eDs ls sL afs c0) __)
    (fun ss c0 r _ _ _ _ hssders -> Deriv_cofseq_ext
    ((map (seqSubst eDf lf lL eDs ls sL afs) ss),
    (seqSubst eDf lf lL eDs ls sL afs c0), r, hssders)) Deriv_cofseqs_nil
    (fun c0 cs _ x _ x0 -> Deriv_cofseqs_cons
    ((seqSubst eDf lf lL eDs ls sL afs c0),
    (let rec map0 = function
     | [] -> []
     | a::t -> (seqSubst eDf lf lL eDs ls sL afs a)::(map0 t)
     in map0 cs), x, x0)) c hder

type ('formula, 'structr) c8 =
  'formula -> ('formula, 'structr) dertree -> __ -> __ -> __ -> ('formula,
  'structr) dertree

(** val defSubs : string list -> 'a1 sSubst -> 'a1 sSubst -> 'a1 sSubst **)

let defSubs ls sub1 sub2 s =
  if in_dec (=) s ls then sub1 s else sub2 s

type ('formula, 'structr) sSubstfor = 'structr sSubst

(** val stepSub :
    'a1 eqDec -> 'a1 fLANG -> 'a1 lOGLANG -> 'a2 eqDec -> 'a2 fLANG -> ('a1,
    'a2) sTRLANG -> ('a1, 'a2) afsSubst -> ('a1, 'a2) sequent -> ('a1, 'a2)
    sequent -> ('a1, 'a2) sSubstfor -> ('a1, 'a2) afsSubst **)

let stepSub eDf lf lL eDs ls sL afs concl _ ssub =
  let af,suba = afs in
  af,(defSubs (seqSVs eDf lf lL eDs ls sL concl) ssub suba)

(** val comSubn :
    'a1 eqDec -> 'a1 fLANG -> 'a1 lOGLANG -> 'a2 eqDec -> 'a2 fLANG -> ('a1,
    'a2) sTRLANG -> ('a2*'a2) list -> 'a2 sSubst list -> 'a1 afSubst -> 'a2
    sSubst **)

let rec comSubn eDf lf lL eDs ls sL lXY ls0 af =
  match lXY with
  | [] -> (fun _ -> sL.sV "")
  | _::l ->
    (match ls0 with
     | [] -> assert false (* absurd case *)
     | s::l0 ->
       let s0 = comSubn eDf lf lL eDs ls sL l l0 af in
       (fun x ->
       if in_dec (eqdec eqDec_string) x
            (list_union l (comp (strSVs eDf lf lL eDs ls sL) fst))
       then s0 x
       else s x))

(** val sF_str_sub :
    'a1 eqDec -> 'a1 fLANG -> 'a1 lOGLANG -> 'a2 eqDec -> 'a2 fLANG -> ('a1,
    'a2) sTRLANG -> 'a1 -> 'a2 -> 'a2 -> 'a1 afSubst -> 'a2 sSubst -> bool ->
    'a2 -> 'a2 sSubst **)

let sF_str_sub eDf lf lL eDs ls sL a x y af s b z =
  ipse_rect eDs ls (fun x0 iH _ _ b0 z0 _ ->
    let s0 = eqdec eDs (strSubst eDf lf lL eDs ls sL (af,s) x0) z0 in
    if s0
    then s
    else let s1 =
           eqdec (eqDec_prod eDs eDs)
             ((strSubst eDf lf lL eDs ls sL (af,s) x0),z0) ((sL.fS a),y)
         in
         if s1
         then let s2 = var_dec eDs ls sL.sV sL.sVVAR x0 in
              (fun _ ->
              match s2 with
              | Some _ -> z0
              | None -> assert false (* absurd case *))
         else let s2 = var_dec eDs ls sL.sV sL.sVVAR x0 in
              (match s2 with
               | Some _ -> (fun _ -> z0)
               | None ->
                 let s3 = var_dec eDs ls sL.fS sL.fSVAR x0 in
                 (match s3 with
                  | Some _ -> assert false (* absurd case *)
                  | None ->
                    let hall =
                      let l =
                        zip (fun x1 x2 -> x1,x2) (ls.ipse x0) (ls.ipse z0)
                      in
                      let _,x1 = forallT_forall (eqDec_prod eDs eDs) l in
                      x1 (fun x2 _ ->
                        let s4,s5 = x2 in
                        let hinX'Z' =
                          in_zip_pair_23_sig_1 eDs eDs (sL.sgnips x0)
                            (map (strSubst eDf lf lL eDs ls sL (af,s))
                              (ls.ipse x0)) (ls.ipse z0)
                            (strSubst eDf lf lL eDs ls sL (af,s) s4) s5
                        in
                        iH s4 __ __ __ (nxorb b0 hinX'Z') s5 __)
                    in
                    let hall0 =
                      forallT_sig_elim
                        (zip (fun x1 x2 -> x1,x2) (ls.ipse x0) (ls.ipse z0))
                        hall
                    in
                    comSubn eDf lf lL eDs ls sL
                      (zip (fun x1 x2 -> x1,x2) (ls.ipse x0) (ls.ipse z0))
                      hall0 af))) x __ __ b z __

(** val exSub :
    'a1 eqDec -> 'a1 fLANG -> 'a1 lOGLANG -> 'a2 eqDec -> 'a2 fLANG -> ('a1,
    'a2) sTRLANG -> 'a1 -> 'a2 -> 'a2 -> 'a2 -> 'a2 -> 'a1 afSubst -> 'a2
    sSubst -> bool -> 'a2 sSubst **)

let exSub eDf lf lL eDs ls sL a pat y _ stry af suba pn =
  sF_str_sub eDf lf lL eDs ls sL a pat y af suba pn stry

(** val seqExSub1 :
    'a1 eqDec -> 'a1 fLANG -> 'a1 lOGLANG -> 'a2 eqDec -> 'a2 fLANG -> ('a1,
    'a2) sTRLANG -> ('a1, 'a2) sequent -> ('a1, 'a2) sequent -> ('a1, 'a2)
    sequent -> 'a1 afSubst -> 'a2 sSubst -> bool -> 'a1 -> 'a2 -> ('a1, 'a2)
    sSubstfor **)

let seqExSub1 eDf lf lL eDs ls sL pat seqa seqy af suba pn a y =
  let Sequent (x, y0) = pat in
  let Sequent (x0, y1) = seqa in
  let Sequent (x1, y2) = seqy in
  let s = exSub eDf lf lL eDs ls sL a x y x0 x1 af suba (negb pn) in
  let s0 = exSub eDf lf lL eDs ls sL a y0 y y1 y2 af suba pn in
  defSubs (strSVs eDf lf lL eDs ls sL x) s s0

(** val seqExSub2 :
    'a1 eqDec -> 'a1 fLANG -> 'a1 lOGLANG -> 'a2 eqDec -> 'a2 fLANG -> ('a1,
    'a2) sTRLANG -> 'a2 -> 'a2 -> 'a2 -> 'a2 -> 'a2 -> 'a2 -> ('a1, 'a2)
    sequent -> ('a1, 'a2) sequent -> ('a1, 'a2) sequent -> 'a1 afSubst -> 'a2
    sSubst -> 'a1 -> 'a2 -> bool -> ('a1, 'a2) sSubstfor **)

let seqExSub2 eDf lf lL eDs ls sL pant psuc aant asuc yant ysuc pat seqa seqy af suba a y pn =
  let s = strCtnsFml_dec eDf lf lL eDs ls sL pant in
  if s
  then let s0 = strCtnsFml_dec eDf lf lL eDs ls sL psuc in
       if s0
       then suba
       else exSub eDf lf lL eDs ls sL a psuc y asuc ysuc af suba pn
  else let s0 = strCtnsFml_dec eDf lf lL eDs ls sL psuc in
       if s0
       then exSub eDf lf lL eDs ls sL a pant y aant yant af suba (negb pn)
       else seqExSub1 eDf lf lL eDs ls sL pat seqa seqy af suba pn a y

type ('formula, 'structr) bELNAP =
  ('formula, 'structr) c8
  (* singleton inductive, whose constructor was Build_BELNAP *)

(** val c8_holds :
    'a1 eqDec -> 'a1 fLANG -> 'a1 lOGLANG -> 'a2 eqDec -> 'a2 fLANG -> ('a1,
    'a2) sTRLANG -> ('a1, 'a2) dISPCALC -> ('a1, 'a2) bELNAP -> 'a1 -> ('a1,
    'a2) dertree -> ('a1, 'a2) dertree **)

let c8_holds _ _ _ _ _ _ _ bELNAP0 m dt =
  bELNAP0 m dt __ __ __

type ('formula, 'structr) derivRule =
  ('formula, 'structr) dertree
  (* singleton inductive, whose constructor was Build_DerivRule *)

(** val derr_dt :
    'a1 eqDec -> 'a1 fLANG -> 'a1 lOGLANG -> 'a2 eqDec -> 'a2 fLANG -> ('a1,
    'a2) sTRLANG -> ('a1, 'a2) dISPCALC -> ('a1, 'a2) rule -> ('a1, 'a2)
    derivRule -> ('a1, 'a2) dertree **)

let derr_dt _ _ _ _ _ _ _ _ derivRule0 =
  derivRule0

type ('formula, 'structr) derivRuleNC =
  ('formula, 'structr) derivRule
  (* singleton inductive, whose constructor was Build_DerivRuleNC *)

(** val derrnc_derr :
    'a1 eqDec -> 'a1 fLANG -> 'a1 lOGLANG -> 'a2 eqDec -> 'a2 fLANG -> ('a1,
    'a2) sTRLANG -> ('a1, 'a2) dISPCALC -> ('a1, 'a2) rule -> ('a1, 'a2)
    derivRuleNC -> ('a1, 'a2) derivRule **)

let derrnc_derr _ _ _ _ _ _ _ _ derivRuleNC0 =
  derivRuleNC0

type ('formula, 'structr) derivDC =
  ('formula, 'structr) rule -> __ -> ('formula, 'structr) derivRule

(** val derr_rules :
    'a1 eqDec -> 'a1 fLANG -> 'a1 lOGLANG -> 'a2 eqDec -> 'a2 fLANG -> ('a1,
    'a2) sTRLANG -> ('a1, 'a2) dISPCALC -> ('a1, 'a2) rule -> ('a1, 'a2)
    derivRule **)

let derr_rules eDf lf lL eDs ls sL _ r =
  Der ((conclRule eDf lf lL eDs ls sL r), r,
    (map (fun x -> Unf x) (premsRule eDf lf lL eDs ls sL r)))

(** val forallT_DerivRule_sig :
    'a1 eqDec -> 'a1 fLANG -> 'a1 lOGLANG -> 'a2 eqDec -> 'a2 fLANG -> ('a1,
    'a2) sTRLANG -> ('a1, 'a2) dISPCALC -> ('a1, 'a2) sequent list -> ('a1,
    'a2) sequent list -> (('a1, 'a2) sequent, ('a1, 'a2) derivRule) forallT
    -> ('a1, 'a2) dertree list **)

let rec forallT_DerivRule_sig eDf lf lL eDs ls sL dC prems ls0 hder =
  match ls0 with
  | [] -> []
  | y::l ->
    let hders = forallT_inv y l hder in
    let hderls = forallT_inv_tail y l hder in
    let iHls = forallT_DerivRule_sig eDf lf lL eDs ls sL dC prems l hderls in
    hders::iHls

(** val forallT_DerivRuleNC_sig :
    'a1 eqDec -> 'a1 fLANG -> 'a1 lOGLANG -> 'a2 eqDec -> 'a2 fLANG -> ('a1,
    'a2) sTRLANG -> ('a1, 'a2) dISPCALC -> ('a1, 'a2) sequent list -> ('a1,
    'a2) sequent list -> (('a1, 'a2) sequent, ('a1, 'a2) derivRuleNC) forallT
    -> ('a1, 'a2) dertree list **)

let rec forallT_DerivRuleNC_sig eDf lf lL eDs ls sL dC prems ls0 hder =
  match ls0 with
  | [] -> []
  | y::l ->
    let hders = forallT_inv y l hder in
    let hderls = forallT_inv_tail y l hder in
    let iHls = forallT_DerivRuleNC_sig eDf lf lL eDs ls sL dC prems l hderls
    in
    hders::iHls

(** val derivRule_iff_deriv_rule :
    'a1 eqDec -> 'a1 fLANG -> 'a1 lOGLANG -> 'a2 eqDec -> 'a2 fLANG -> ('a1,
    'a2) sTRLANG -> ('a1, 'a2) dISPCALC -> ('a1, 'a2) rule -> (('a1, 'a2)
    derivRule, ('a1, 'a2) deriv_rule) iffT0 **)

let derivRule_iff_deriv_rule eDf lf lL eDs ls sL dC = function
| l,s ->
  (fun x ->
    Obj.magic deriv_prseq_weak eDf lf lL eDs ls sL dC
      (premsDT eDf lf lL eDs ls sL x) l s
      (dertree_rect_gen eDf lf lL eDs ls sL ForallT_nil (fun t l0 pt pl ->
        ForallT_cons (t, l0, pt, pl)) (fun s0 _ -> Deriv_prseq_prem
        (conclDT eDf lf lL eDs ls sL (Unf s0))) (fun s0 r0 l0 iH _ ->
        let x0 = fun l1 ->
          let x0,_ = forall_ForallT (eqDec_dertree eDf lf lL eDs ls sL) l1 in
          Obj.magic x0
        in
        let hspup = x0 (nextUp eDf lf lL eDs ls sL (Der (s0, r0, l0))) __ in
        let iH0 =
          forallT_mp (nextUp eDf lf lL eDs ls sL (Der (s0, r0, l0))) hspup iH
        in
        Deriv_prseq_ext ((map (conclDT eDf lf lL eDs ls sL) l0), s0, r0,
        (forallT_deriv_prseqs eDf lf lL eDs ls sL dC
          (premsDT eDf lf lL eDs ls sL (Der (s0, r0, l0)))
          (map (conclDT eDf lf lL eDs ls sL) l0)
          (let f = conclDT eDf lf lL eDs ls sL in
           let _,x1 = forallT_map f l0 in
           x1
             (let iH1 =
                let lemma =
                  forallT_forall (eqDec_dertree eDf lf lL eDs ls sL)
                    (nextUp eDf lf lL eDs ls sL (Der (s0, r0, l0)))
                in
                iffT_arrow_subrelation (Obj.magic lemma) (Obj.magic iH0)
              in
              let _,x2 = forallT_forall (eqDec_dertree eDf lf lL eDs ls sL) l0
              in
              x2 (fun dt _ ->
                let iH2 = Obj.magic iH1 dt __ in
                deriv_prseq_weak eDf lf lL eDs ls sL dC
                  (premsDT eDf lf lL eDs ls sL dt)
                  (premsDT eDf lf lL eDs ls sL (Der (s0, r0, l0)))
                  (conclDT eDf lf lL eDs ls sL dt) iH2)))))) x __)),(Obj.magic
                                                                    deriv_prseq_mut_rect
                                                                    eDf lf lL
                                                                    eDs ls sL
                                                                    dC l
                                                                    (fun c _ ->
                                                                    Unf c)
                                                                    (fun cs c r0 _ _ _ hDers ->
                                                                    let hDers0 =
                                                                    forallT_DerivRule_sig
                                                                    eDf lf lL
                                                                    eDs ls sL
                                                                    dC l cs
                                                                    hDers
                                                                    in
                                                                    Der (c,
                                                                    r0,
                                                                    hDers0))
                                                                    ForallT_nil
                                                                    (fun c cs _ hDer _ hDers ->
                                                                    ForallT_cons
                                                                    (c, cs,
                                                                    hDer,
                                                                    hDers)) s)

(** val forallT_DerivRule_iff_deriv_rule :
    'a1 eqDec -> 'a1 fLANG -> 'a1 lOGLANG -> 'a2 eqDec -> 'a2 fLANG -> ('a1,
    'a2) sTRLANG -> ('a1, 'a2) dISPCALC -> ('a1, 'a2) rule list -> ((('a1,
    'a2) rule, ('a1, 'a2) derivRule) forallT, (('a1, 'a2) rule, ('a1, 'a2)
    deriv_rule) forallT) iffT0 **)

let forallT_DerivRule_iff_deriv_rule eDf lf lL eDs ls sL dC lr =
  forallT_act_iff lr (fun s ->
    derivRule_iff_deriv_rule eDf lf lL eDs ls sL dC s)

(** val derivRule_iff_deriv_prseq :
    'a1 eqDec -> 'a1 fLANG -> 'a1 lOGLANG -> 'a2 eqDec -> 'a2 fLANG -> ('a1,
    'a2) sTRLANG -> ('a1, 'a2) dISPCALC -> ('a1, 'a2) sequent list -> ('a1,
    'a2) sequent -> (('a1, 'a2) derivRule, ('a1, 'a2) deriv_prseq) iffT0 **)

let derivRule_iff_deriv_prseq eDf lf lL eDs ls sL dC ps c =
  Obj.magic derivRule_iff_deriv_rule eDf lf lL eDs ls sL dC (ps,c)

(** val derivDC_iff_ForallT_DerivRule :
    'a1 eqDec -> 'a1 fLANG -> 'a1 lOGLANG -> 'a2 eqDec -> 'a2 fLANG -> ('a1,
    'a2) sTRLANG -> ('a1, 'a2) dISPCALC -> ('a1, 'a2) dISPCALC -> (('a1, 'a2)
    derivDC, (('a1, 'a2) rule, ('a1, 'a2) derivRule) forallT) iffT0 **)

let derivDC_iff_ForallT_DerivRule eDf lf lL eDs ls sL _ dC' =
  (let _,x = forallT_forall (eqDec_rule eDf lf lL eDs ls sL) dC' in x),
    (let x,_ = forallT_forall (eqDec_rule eDf lf lL eDs ls sL) dC' in x)

(** val derivDC_iff_ForallT_deriv_rule :
    'a1 eqDec -> 'a1 fLANG -> 'a1 lOGLANG -> 'a2 eqDec -> 'a2 fLANG -> ('a1,
    'a2) sTRLANG -> ('a1, 'a2) dISPCALC -> ('a1, 'a2) dISPCALC -> (('a1, 'a2)
    derivDC, (('a1, 'a2) rule, ('a1, 'a2) deriv_rule) forallT) iffT0 **)

let derivDC_iff_ForallT_deriv_rule eDf lf lL eDs ls sL dC dC' =
  let lemma = derivDC_iff_ForallT_DerivRule eDf lf lL eDs ls sL dC dC' in
  Obj.magic trans_co_eq_inv_arrow_morphism (fun _ _ _ -> iffT_Transitive) __
    __ lemma __ __
    (forallT_DerivRule_iff_deriv_rule eDf lf lL eDs ls sL dC dC')

(** val derivRuleNC_iff_deriv_ncprseq :
    'a1 eqDec -> 'a1 fLANG -> 'a1 lOGLANG -> 'a2 eqDec -> 'a2 fLANG -> ('a1,
    'a2) sTRLANG -> ('a1, 'a2) dISPCALC -> ('a1, 'a2) sequent list -> ('a1,
    'a2) sequent -> (('a1, 'a2) derivRuleNC, ('a1, 'a2) deriv_ncprseq) iffT0 **)

let derivRuleNC_iff_deriv_ncprseq eDf lf lL eDs ls sL dC ps c =
  (fun x ->
    deriv_cofprseq_weak eDf lf lL eDs ls sL dC
      (premsDT eDf lf lL eDs ls sL x) ps c
      (dertree_rect_gen eDf lf lL eDs ls sL ForallT_nil (fun t l pt pl ->
        ForallT_cons (t, l, pt, pl)) (fun s _ _ -> Deriv_cofprseq_prem
        (conclDT eDf lf lL eDs ls sL (Unf s))) (fun s r l iH _ _ ->
        let x0 = fun l0 ->
          let x0,_ = forall_ForallT (eqDec_dertree eDf lf lL eDs ls sL) l0 in
          Obj.magic x0
        in
        let hspup = x0 (nextUp eDf lf lL eDs ls sL (Der (s, r, l))) __ in
        let x1 = fun l0 ->
          let x1,_ = forall_ForallT (eqDec_dertree eDf lf lL eDs ls sL) l0 in
          Obj.magic x1
        in
        let hncup = x1 (nextUp eDf lf lL eDs ls sL (Der (s, r, l))) __ in
        let iH0 =
          forallT_mp (nextUp eDf lf lL eDs ls sL (Der (s, r, l))) hspup iH
        in
        let iH1 =
          forallT_mp (nextUp eDf lf lL eDs ls sL (Der (s, r, l))) hncup iH0
        in
        Deriv_cofprseq_ext ((map (conclDT eDf lf lL eDs ls sL) l), s, r,
        (forallT_deriv_cofprseqs eDf lf lL eDs ls sL dC
          (premsDT eDf lf lL eDs ls sL (Der (s, r, l)))
          (map (conclDT eDf lf lL eDs ls sL) l)
          (let f = conclDT eDf lf lL eDs ls sL in
           let _,x2 = forallT_map f l in
           x2
             (let iH2 =
                let lemma =
                  forallT_forall (eqDec_dertree eDf lf lL eDs ls sL)
                    (nextUp eDf lf lL eDs ls sL (Der (s, r, l)))
                in
                iffT_arrow_subrelation (Obj.magic lemma) (Obj.magic iH1)
              in
              let _,x3 = forallT_forall (eqDec_dertree eDf lf lL eDs ls sL) l
              in
              x3 (fun dt _ ->
                let iH3 = Obj.magic iH2 dt __ in
                deriv_cofprseq_weak eDf lf lL eDs ls sL dC
                  (premsDT eDf lf lL eDs ls sL dt)
                  (premsDT eDf lf lL eDs ls sL (Der (s, r, l)))
                  (conclDT eDf lf lL eDs ls sL dt) iH3)))))) x __ __)),
    (deriv_cofprseq_mut_rect eDf lf lL eDs ls sL dC ps (fun c0 _ -> Unf c0)
      (fun cs c0 r _ _ _ _ hDers ->
      let hDers0 = forallT_DerivRuleNC_sig eDf lf lL eDs ls sL dC ps cs hDers
      in
      Der (c0, r, hDers0)) ForallT_nil (fun c0 cs _ hDer _ hDers ->
      ForallT_cons (c0, cs, hDer, hDers)) c)

(** val dernc_derremcut :
    'a1 eqDec -> 'a1 fLANG -> 'a1 lOGLANG -> 'a2 eqDec -> 'a2 fLANG -> ('a1,
    'a2) sTRLANG -> ('a1, 'a2) dISPCALC -> ('a1, 'a2) rule -> ('a1, 'a2)
    derivRuleNC -> ('a1, 'a2) derivRule **)

let dernc_derremcut eDf lf lL eDs ls sL dC r h =
  derr_dt eDf lf lL eDs ls sL dC r (derrnc_derr eDf lf lL eDs ls sL dC r h)

(** val derremcut_dernc :
    'a1 eqDec -> 'a1 fLANG -> 'a1 lOGLANG -> 'a2 eqDec -> 'a2 fLANG -> ('a1,
    'a2) sTRLANG -> ('a1, 'a2) dISPCALC -> ('a1, 'a2) rule -> ('a1, 'a2)
    derivRule -> ('a1, 'a2) derivRuleNC **)

let derremcut_dernc eDf lf lL eDs ls sL dC r h =
  derr_dt eDf lf lL eDs ls sL
    (remove_rule eDf lf lL eDs ls sL (cUT eDf lf lL eDs ls sL) dC) r h

(** val dernc_derremcut_iff :
    'a1 eqDec -> 'a1 fLANG -> 'a1 lOGLANG -> 'a2 eqDec -> 'a2 fLANG -> ('a1,
    'a2) sTRLANG -> ('a1, 'a2) dISPCALC -> ('a1, 'a2) rule -> (('a1, 'a2)
    derivRuleNC, ('a1, 'a2) derivRule) iffT0 **)

let dernc_derremcut_iff eDf lf lL eDs ls sL dC r =
  (dernc_derremcut eDf lf lL eDs ls sL dC r),(derremcut_dernc eDf lf lL eDs
                                               ls sL dC r)

(** val derivRule_rule_bw_Inst_expl :
    'a1 eqDec -> 'a1 fLANG -> 'a1 lOGLANG -> 'a2 eqDec -> 'a2 fLANG -> ('a1,
    'a2) sTRLANG -> ('a1, 'a2) dISPCALC -> ('a1, 'a2) sequent list -> ('a1,
    'a2) sequent list -> ('a1, 'a2) sequent -> ('a1, 'a2) afsSubst -> ('a1,
    'a2) derivRule -> (('a1, 'a2) sequent, ('a1, 'a2) derivRule) forallT ->
    ('a1, 'a2) derivRule **)

let derivRule_rule_bw_Inst_expl eDf lf lL eDs ls sL dC ps ss c afs hDer hDers =
  let x = fun dC0 ps0 c0 ->
    let x,_ = derivRule_iff_deriv_prseq eDf lf lL eDs ls sL dC0 ps0 c0 in x
  in
  let hDer0 = x dC ss c hDer in
  let c0 = seqSubst eDf lf lL eDs ls sL afs c in
  let _,x0 = derivRule_iff_deriv_prseq eDf lf lL eDs ls sL dC ps c0 in
  x0
    (deriv_prseq_tran_afs eDf lf lL eDs ls sL dC ps ss c afs
      (let cs = map (seqSubst eDf lf lL eDs ls sL afs) ss in
       let x1,_ = forallT_deriv_prseqs_iff eDf lf lL eDs ls sL dC ps cs in
       x1
         (let f = seqSubst eDf lf lL eDs ls sL afs in
          let _,x2 = forallT_map f ss in
          x2
            (let _,x3 = forallT_forall (eqDec_sequent eDf lf lL eDs ls sL) ss
             in
             x3 (fun s _ ->
               let hDers0 =
                 let lemma =
                   forallT_forall (eqDec_sequent eDf lf lL eDs ls sL) ss
                 in
                 iffT_arrow_subrelation (Obj.magic lemma) (Obj.magic hDers)
               in
               let lemma =
                 derivRule_iff_deriv_prseq eDf lf lL eDs ls sL dC ps
                   (seqSubst eDf lf lL eDs ls sL afs s)
               in
               flip2 (Obj.magic (fun _ _ -> iffT_flip_arrow_subrelation)) __
                 __
                 (symmetry (Obj.magic (fun _ _ -> iffT_Symmetric)) __ __
                   lemma) (Obj.magic hDers0 s __))))) hDer0)

(** val derivRule_rule_bw_inDC :
    'a1 eqDec -> 'a1 fLANG -> 'a1 lOGLANG -> 'a2 eqDec -> 'a2 fLANG -> ('a1,
    'a2) sTRLANG -> ('a1, 'a2) dISPCALC -> ('a1, 'a2) sequent list -> ('a1,
    'a2) sequent list -> ('a1, 'a2) sequent -> ('a1, 'a2) afsSubst -> (('a1,
    'a2) sequent, ('a1, 'a2) derivRule) forallT -> ('a1, 'a2) derivRule **)

let derivRule_rule_bw_inDC eDf lf lL eDs ls sL dC ps ss c afs =
  derivRule_rule_bw_Inst_expl eDf lf lL eDs ls sL dC ps ss c afs
    (derr_rules eDf lf lL eDs ls sL dC (ss,c))

(** val deriv_cofseq_rule_bw_inDC :
    'a1 eqDec -> 'a1 fLANG -> 'a1 lOGLANG -> 'a2 eqDec -> 'a2 fLANG -> ('a1,
    'a2) sTRLANG -> ('a1, 'a2) dISPCALC -> ('a1, 'a2) sequent list -> ('a1,
    'a2) sequent -> ('a1, 'a2) afsSubst -> ('a1, 'a2) deriv_cofseqs -> ('a1,
    'a2) deriv_cofseq **)

let deriv_cofseq_rule_bw_inDC eDf lf lL eDs ls sL _ ss c afs hders =
  Deriv_cofseq_ext ((map (seqSubst eDf lf lL eDs ls sL afs) ss),
    (seqSubst eDf lf lL eDs ls sL afs c), (ss,c), hders)

(** val deriv_cofseq_rule_bw_InstNC :
    'a1 eqDec -> 'a1 fLANG -> 'a1 lOGLANG -> 'a2 eqDec -> 'a2 fLANG -> ('a1,
    'a2) sTRLANG -> ('a1, 'a2) dISPCALC -> ('a1, 'a2) sequent list -> ('a1,
    'a2) sequent -> ('a1, 'a2) afsSubst -> ('a1, 'a2) derivRuleNC -> (('a1,
    'a2) sequent, ('a1, 'a2) deriv_cofseq) forallT -> ('a1, 'a2) deriv_cofseq **)

let deriv_cofseq_rule_bw_InstNC eDf lf lL eDs ls sL dC ss c afs hDer hders =
  let hders0 =
    forallT_deriv_cofseqs eDf lf lL eDs ls sL dC
      (map (seqSubst eDf lf lL eDs ls sL afs) ss) hders
  in
  deriv_cofseq_tran_afs eDf lf lL eDs ls sL dC ss c afs
    (let x,_ = derivRuleNC_iff_deriv_ncprseq eDf lf lL eDs ls sL dC ss c in
     x hDer) hders0

(** val derivRuleNC_rule_bw_inDC :
    'a1 eqDec -> 'a1 fLANG -> 'a1 lOGLANG -> 'a2 eqDec -> 'a2 fLANG -> ('a1,
    'a2) sTRLANG -> ('a1, 'a2) dISPCALC -> ('a1, 'a2) sequent list -> ('a1,
    'a2) sequent list -> ('a1, 'a2) sequent -> ('a1, 'a2) afsSubst -> (('a1,
    'a2) sequent, ('a1, 'a2) derivRuleNC) forallT -> ('a1, 'a2) derivRuleNC **)

let derivRuleNC_rule_bw_inDC eDf lf lL eDs ls sL dC ps ss c afs hDers =
  let r = ps,(seqSubst eDf lf lL eDs ls sL afs c) in
  let _,x = dernc_derremcut_iff eDf lf lL eDs ls sL dC r in
  x
    (let x0 = fun x0 -> let _,x1 = forallT_act_iff ss x0 in x1 in
     let hDers0 =
       x0 (fun s ->
         (derremcut_dernc eDf lf lL eDs ls sL dC
           (ps,(seqSubst eDf lf lL eDs ls sL afs s))),(dernc_derremcut eDf lf
                                                        lL eDs ls sL dC
                                                        (ps,(seqSubst eDf lf
                                                              lL eDs ls sL
                                                              afs s)))) hDers
     in
     derivRule_rule_bw_inDC eDf lf lL eDs ls sL
       (remove_rule eDf lf lL eDs ls sL (cUT eDf lf lL eDs ls sL) dC) ps ss c
       afs hDers0)

type ('formula, 'structr) subDer =
  ('formula, 'structr) rule -> ('formula, 'structr) derivRule -> ('formula,
  'structr) derivRule

(** val derivDC_refl :
    'a1 eqDec -> 'a1 fLANG -> 'a1 lOGLANG -> 'a2 eqDec -> 'a2 fLANG -> ('a1,
    'a2) sTRLANG -> ('a1, 'a2) dISPCALC -> ('a1, 'a2) rule -> ('a1, 'a2)
    derivRule **)

let derivDC_refl =
  derr_rules

(** val derivDC_app :
    'a1 eqDec -> 'a1 fLANG -> 'a1 lOGLANG -> 'a2 eqDec -> 'a2 fLANG -> ('a1,
    'a2) sTRLANG -> ('a1, 'a2) dISPCALC -> ('a1, 'a2) dISPCALC -> ('a1, 'a2)
    dISPCALC -> ('a1, 'a2) derivDC -> ('a1, 'a2) derivDC -> ('a1, 'a2) rule
    -> ('a1, 'a2) derivRule **)

let derivDC_app eDf lf lL eDs ls sL dC1 dC2 _ h1 h2 r =
  let s = in_dec (rule_eq_dec eDf lf lL eDs ls sL) r dC1 in
  if s
  then h1 r __
  else let s0 = in_dec (rule_eq_dec eDf lf lL eDs ls sL) r dC2 in
       if s0 then h2 r __ else assert false (* absurd case *)

(** val derivDC_SubDer :
    'a1 eqDec -> 'a1 fLANG -> 'a1 lOGLANG -> 'a2 eqDec -> 'a2 fLANG -> ('a1,
    'a2) sTRLANG -> ('a1, 'a2) dISPCALC -> ('a1, 'a2) dISPCALC -> ('a1, 'a2)
    derivDC -> ('a1, 'a2) subDer **)

let derivDC_SubDer eDf lf lL eDs ls sL dC1 dC2 hdDC r hr =
  let x = fun dC dC' ->
    let x,_ = derivDC_iff_ForallT_deriv_rule eDf lf lL eDs ls sL dC dC' in x
  in
  let hdDC0 = x dC2 dC1 hdDC in
  let x0 = fun dC r0 ->
    let x0,_ = derivRule_iff_deriv_rule eDf lf lL eDs ls sL dC r0 in x0
  in
  let hr0 = x0 dC1 r hr in
  let _,x1 = derivRule_iff_deriv_rule eDf lf lL eDs ls sL dC2 r in
  x1 (deriv_rule_replace eDf lf lL eDs ls sL dC1 dC2 r hdDC0 hr0)

(** val extend_DerivDC :
    'a1 eqDec -> 'a1 fLANG -> 'a1 lOGLANG -> 'a2 eqDec -> 'a2 fLANG -> ('a1,
    'a2) sTRLANG -> ('a1, 'a2) dISPCALC -> ('a1, 'a2) dISPCALC -> ('a1, 'a2)
    derivDC -> ('a1, 'a2) subDer **)

let extend_DerivDC eDf lf lL eDs ls sL dC1 dC2 h =
  derivDC_SubDer eDf lf lL eDs ls sL (app dC1 dC2) dC1 (fun x _ ->
    derivDC_app eDf lf lL eDs ls sL dC1 dC2 dC1 (fun x0 _ ->
      derivDC_refl eDf lf lL eDs ls sL dC1 x0) h x)

(** val derivDC_one :
    'a1 eqDec -> 'a1 fLANG -> 'a1 lOGLANG -> 'a2 eqDec -> 'a2 fLANG -> ('a1,
    'a2) sTRLANG -> ('a1, 'a2) dISPCALC -> ('a1, 'a2) rule -> ('a1, 'a2)
    derivRule -> ('a1, 'a2) rule -> ('a1, 'a2) derivRule **)

let derivDC_one eDf lf lL eDs ls sL _ r h x =
  eq_dec_in_list (rule_eq_dec eDf lf lL eDs ls sL) r [] x (fun _ -> h)
    (fun _ -> assert false (* absurd case *))

(** val extend_DerivRule_expl :
    'a1 eqDec -> 'a1 fLANG -> 'a1 lOGLANG -> 'a2 eqDec -> 'a2 fLANG -> ('a1,
    'a2) sTRLANG -> ('a1, 'a2) dISPCALC -> ('a1, 'a2) rule -> ('a1, 'a2)
    derivRule -> ('a1, 'a2) subDer **)

let extend_DerivRule_expl eDf lf lL eDs ls sL dC r dr =
  extend_DerivDC eDf lf lL eDs ls sL dC (r::[]) (fun x _ ->
    derivDC_one eDf lf lL eDs ls sL dC r dr x)

(** val extSub2_fs :
    'a1 eqDec -> 'a1 fLANG -> 'a1 lOGLANG -> 'a2 eqDec -> 'a2 fLANG -> ('a1,
    'a2) sTRLANG -> ('a1, 'a2) rule -> ('a1, 'a2) rule -> ('a1, 'a2) sequent
    -> 'a2 -> 'a2 -> 'a2 -> 'a2 -> 'a2 -> 'a2 -> 'a1 -> 'a2 -> bool -> ('a1,
    'a2) afsSubst **)

let extSub2_fs eDf lf lL eDs ls sL r rA conclY pant psuc aant asuc yant ysuc a y pn =
  let s = ruleInst_ruleSubst eDf lf lL eDs ls sL r rA in
  let a0,s0 = s in
  stepSub eDf lf lL eDs ls sL (a0,s0) (conclRule eDf lf lL eDs ls sL r)
    conclY
    (seqExSub2 eDf lf lL eDs ls sL pant psuc aant asuc yant ysuc
      (conclRule eDf lf lL eDs ls sL r) (conclRule eDf lf lL eDs ls sL rA)
      conclY a0 s0 a y pn)

(** val seqreps_map_concl :
    'a1 eqDec -> 'a1 fLANG -> 'a1 lOGLANG -> 'a2 eqDec -> 'a2 fLANG -> ('a1,
    'a2) sTRLANG -> bool -> 'a2 -> 'a2 -> ('a1, 'a2) sequent list -> ('a1,
    'a2) sequent list -> (('a1, 'a2) sequent, ('a1, 'a2) sequent -> __ ->
    ('a1, 'a2) dertree) forallT -> ('a1, 'a2) dertree list **)

let seqreps_map_concl _ _ _ _ _ _ _ _ _ lX lY =
  list_biind (fun _ _ -> []) (fun _ _ v _ iH _ hall ->
    let s =
      iH __
        (match hall with
         | ForallT_nil -> assert false (* absurd case *)
         | ForallT_cons (_, _, _, x) -> x)
    in
    (match hall with
     | ForallT_nil -> assert false (* absurd case *)
     | ForallT_cons (_, _, x, _) -> let s0 = x v __ in s0::s)) lX lY __

(** val makeCutLP :
    'a1 eqDec -> 'a1 fLANG -> 'a1 lOGLANG -> 'a2 eqDec -> 'a2 fLANG -> ('a1,
    'a2) sTRLANG -> ('a1, 'a2) dISPCALC -> ('a1, 'a2) bELNAP -> ('a1, 'a2)
    dertree -> ('a1, 'a2) dertree -> 'a1 -> 'a2 -> ('a1, 'a2) sequent ->
    ('a1, 'a2) dertree **)

let makeCutLP eDf lf lL eDs ls sL _ _ dtAY dtA a y seqY =
  dertree_rect_gen eDf lf lL eDs ls sL ForallT_nil (fun t l pt pl ->
    ForallT_cons (t, l, pt, pl)) (fun _ _ _ -> assert false
    (* absurd case *)) (fun s r l iH _ _ seqY0 _ ->
    let _,s0 = r in
    let Sequent (x, y0) = s0 in
    let Sequent (x0, y1) = seqY0 in
    let Sequent (x1, y2) = s in
    let psA = map (conclDT eDf lf lL eDs ls sL) l in
    let rA = psA,s in
    let h =
      let s1 = strIsFml_dec eDf lf lL eDs ls sL y0 in
      if s1
      then let s2 = eqdec eDs y2 (sL.fS a) in
           if s2
           then let s3 = eqdec eDs y2 y1 in if s3 then false else true
           else false
      else false
    in
    if h
    then let seqYl = Sequent (x0, (sL.fS a)) in
         let s1 =
           extSub2_fs eDf lf lL eDs ls sL r rA seqYl x y0 x1 y2 x0 (sL.fS a)
             a y true
         in
         let s2 =
           seqreps_map_concl eDf lf lL eDs ls sL true (sL.fS a) y
             (premsRule eDf lf lL eDs ls sL rA)
             (premsRule eDf lf lL eDs ls sL
               (ruleSubst eDf lf lL eDs ls sL s1 r))
             (let f = conclDT eDf lf lL eDs ls sL in
              let _,x2 = forallT_map f l in
              x2
                (let lemma =
                   forallT_forall (eqDec_dertree eDf lf lL eDs ls sL) l
                 in
                 flip2 (Obj.magic (fun _ _ -> iffT_flip_arrow_subrelation))
                   __ __ lemma
                   (let iH0 =
                      let lemma0 =
                        forallT_forall (eqDec_dertree eDf lf lL eDs ls sL) l
                      in
                      iffT_arrow_subrelation (Obj.magic lemma0) (Obj.magic iH)
                    in
                    fun x3 _ t _ -> Obj.magic iH0 x3 __ __ __ t __)))
         in
         Der (seqY0, (cUT eDf lf lL eDs ls sL), ((Der (seqYl, r,
         s2))::(dtAY::[])))
    else let s1 =
           extSub2_fs eDf lf lL eDs ls sL r rA seqY0 x y0 x1 y2 x0 y1 a y true
         in
         let rsubY = ruleSubst eDf lf lL eDs ls sL s1 r in
         let s2 =
           seqreps_map_concl eDf lf lL eDs ls sL true (sL.fS a) y
             (premsRule eDf lf lL eDs ls sL rA)
             (premsRule eDf lf lL eDs ls sL rsubY)
             (let f = conclDT eDf lf lL eDs ls sL in
              let _,x2 = forallT_map f l in
              x2
                (let lemma =
                   forallT_forall (eqDec_dertree eDf lf lL eDs ls sL) l
                 in
                 flip2 (Obj.magic (fun _ _ -> iffT_flip_arrow_subrelation))
                   __ __ lemma
                   (let iH0 =
                      let lemma0 =
                        forallT_forall (eqDec_dertree eDf lf lL eDs ls sL) l
                      in
                      iffT_arrow_subrelation (Obj.magic lemma0) (Obj.magic iH)
                    in
                    fun x3 _ t _ -> Obj.magic iH0 x3 __ __ __ t __)))
         in
         Der (seqY0, r, s2)) dtA __ __ seqY __

(** val allLP :
    'a1 eqDec -> 'a1 fLANG -> 'a1 lOGLANG -> 'a2 eqDec -> 'a2 fLANG -> ('a1,
    'a2) sTRLANG -> ('a1, 'a2) dISPCALC -> ('a1, 'a2) bELNAP -> ('a1, 'a2)
    dertree -> 'a1 -> ('a1, 'a2) dertree **)

let allLP eDf lf lL eDs ls sL dC bP dt a =
  match dt with
  | Unf _ -> dt
  | Der (s, r, l) ->
    let s0 = rule_eq_dec eDf lf lL eDs ls sL r (cUT eDf lf lL eDs ls sL) in
    if s0
    then let s1 =
           ruleInst_ruleSubst eDf lf lL eDs ls sL r
             ((map (conclDT eDf lf lL eDs ls sL) l),s)
         in
         let _,s2 = s1 in
         (match l with
          | [] -> assert false (* absurd case *)
          | d::l0 ->
            (match l0 with
             | [] -> assert false (* absurd case *)
             | d0::l1 ->
               (match l1 with
                | [] ->
                  let y = s2 "Y" in
                  makeCutLP eDf lf lL eDs ls sL dC bP d0 d a y
                    (conclDT eDf lf lL eDs ls sL (Der (s, r, (d::(d0::[])))))
                | _::_ -> assert false (* absurd case *))))
    else dt

(** val makeCutLRP :
    'a1 eqDec -> 'a1 fLANG -> 'a1 lOGLANG -> 'a2 eqDec -> 'a2 fLANG -> ('a1,
    'a2) sTRLANG -> ('a1, 'a2) dISPCALC -> ('a1, 'a2) bELNAP -> ('a1, 'a2)
    dertree -> ('a1, 'a2) dertree -> 'a1 -> 'a2 -> ('a1, 'a2) sequent ->
    ('a1, 'a2) dertree **)

let makeCutLRP eDf lf lL eDs ls sL _ _ dtAY dtA a y seqY =
  dertree_rect_gen eDf lf lL eDs ls sL ForallT_nil (fun t l pt pl ->
    ForallT_cons (t, l, pt, pl)) (fun _ _ _ -> assert false
    (* absurd case *)) (fun s r l iH _ _ seqY0 _ ->
    let _,s0 = r in
    let Sequent (x, y0) = s0 in
    let Sequent (x0, y1) = seqY0 in
    let Sequent (x1, y2) = s in
    let psA = map (conclDT eDf lf lL eDs ls sL) l in
    let rA = psA,s in
    let h =
      let s1 = strIsFml_dec eDf lf lL eDs ls sL x in
      if s1
      then let s2 = eqdec eDs x1 (sL.fS a) in
           if s2
           then let s3 = eqdec eDs x1 x0 in if s3 then false else true
           else false
      else false
    in
    if h
    then let seqYr = Sequent ((sL.fS a), y1) in
         let s1 =
           extSub2_fs eDf lf lL eDs ls sL r rA seqYr x y0 x1 y2 (sL.fS a) y1
             a y false
         in
         let s2 =
           seqreps_map_concl eDf lf lL eDs ls sL false (sL.fS a) y
             (premsRule eDf lf lL eDs ls sL rA)
             (premsRule eDf lf lL eDs ls sL
               (ruleSubst eDf lf lL eDs ls sL s1 r))
             (let f = conclDT eDf lf lL eDs ls sL in
              let _,x2 = forallT_map f l in
              x2
                (let lemma =
                   forallT_forall (eqDec_dertree eDf lf lL eDs ls sL) l
                 in
                 flip2 (Obj.magic (fun _ _ -> iffT_flip_arrow_subrelation))
                   __ __ lemma
                   (let iH0 =
                      let lemma0 =
                        forallT_forall (eqDec_dertree eDf lf lL eDs ls sL) l
                      in
                      iffT_arrow_subrelation (Obj.magic lemma0) (Obj.magic iH)
                    in
                    fun x3 _ t _ -> Obj.magic iH0 x3 __ __ __ t __)))
         in
         Der (seqY0, (cUT eDf lf lL eDs ls sL), (dtAY::((Der (seqYr, r,
         s2))::[])))
    else let s1 =
           extSub2_fs eDf lf lL eDs ls sL r rA seqY0 x y0 x1 y2 x0 y1 a y
             false
         in
         let rsubY = ruleSubst eDf lf lL eDs ls sL s1 r in
         let s2 =
           seqreps_map_concl eDf lf lL eDs ls sL false (sL.fS a) y
             (premsRule eDf lf lL eDs ls sL rA)
             (premsRule eDf lf lL eDs ls sL rsubY)
             (let f = conclDT eDf lf lL eDs ls sL in
              let _,x2 = forallT_map f l in
              x2
                (let lemma =
                   forallT_forall (eqDec_dertree eDf lf lL eDs ls sL) l
                 in
                 flip2 (Obj.magic (fun _ _ -> iffT_flip_arrow_subrelation))
                   __ __ lemma
                   (let iH0 =
                      let lemma0 =
                        forallT_forall (eqDec_dertree eDf lf lL eDs ls sL) l
                      in
                      iffT_arrow_subrelation (Obj.magic lemma0) (Obj.magic iH)
                    in
                    fun x3 _ t _ -> Obj.magic iH0 x3 __ __ __ t __)))
         in
         Der (seqY0, r, s2)) dtA __ __ seqY __

(** val allLRP :
    'a1 eqDec -> 'a1 fLANG -> 'a1 lOGLANG -> 'a2 eqDec -> 'a2 fLANG -> ('a1,
    'a2) sTRLANG -> ('a1, 'a2) dISPCALC -> ('a1, 'a2) bELNAP -> ('a1, 'a2)
    dertree -> 'a1 -> ('a1, 'a2) dertree **)

let allLRP eDf lf lL eDs ls sL dC bP dt a =
  match dt with
  | Unf _ -> dt
  | Der (s, r, l) ->
    let s0 = rule_eq_dec eDf lf lL eDs ls sL r (cUT eDf lf lL eDs ls sL) in
    if s0
    then let s1 =
           ruleInst_ruleSubst eDf lf lL eDs ls sL r
             ((map (conclDT eDf lf lL eDs ls sL) l),s)
         in
         let _,s2 = s1 in
         (match l with
          | [] -> assert false (* absurd case *)
          | d::l0 ->
            (match l0 with
             | [] -> assert false (* absurd case *)
             | d0::l1 ->
               (match l1 with
                | [] ->
                  let x = s2 "X" in
                  makeCutLRP eDf lf lL eDs ls sL dC bP d d0 a x
                    (conclDT eDf lf lL eDs ls sL (Der (s, r, (d::(d0::[])))))
                | _::_ -> assert false (* absurd case *))))
    else dt

type ('formula, 'structr) canElim =
  ('formula, 'structr) dertree -> __ -> __ -> __ -> ('formula, 'structr)
  dertree

type ('formula, 'structr) canElimAll =
  ('formula, 'structr) dertree -> __ -> __ -> ('formula, 'structr) dertree

(** val canElim_canElimAll :
    'a1 eqDec -> 'a1 fLANG -> 'a1 lOGLANG -> 'a2 eqDec -> 'a2 fLANG -> ('a1,
    'a2) sTRLANG -> ('a1, 'a2) dISPCALC -> ('a1, 'a2) canElim -> ('a1, 'a2)
    dertree -> ('a1, 'a2) dertree **)

let canElim_canElimAll eDf lf lL eDs ls sL _ helim dt =
  dertree_rect_gen eDf lf lL eDs ls sL ForallT_nil (fun t l pt pl ->
    ForallT_cons (t, l, pt, pl)) (fun _ _ -> assert false (* absurd case *))
    (fun s r l iH _ _ ->
    let x = fun l0 ->
      let x,_ = forall_ForallT (eqDec_dertree eDf lf lL eDs ls sL) l0 in
      Obj.magic x
    in
    let hvalup = x l __ in
    let x0 = fun l0 ->
      let x0,_ = forall_ForallT (eqDec_dertree eDf lf lL eDs ls sL) l0 in
      Obj.magic x0
    in
    let hPup = x0 l __ in
    let iH0 = forallT_mp l hvalup iH in
    let iH1 = forallT_mp l hPup iH0 in
    let iH2 = forallT_sig_elim l iH1 in
    let s0 = rule_eq_dec eDf lf lL eDs ls sL r (cUT eDf lf lL eDs ls sL) in
    if s0
    then helim (Der (s, (cUT eDf lf lL eDs ls sL), iH2)) __ __ __
    else Der (s, r, iH2)) dt __ __

(** val elimFmls :
    'a1 eqDec -> 'a1 fLANG -> 'a1 lOGLANG -> 'a2 eqDec -> 'a2 fLANG -> ('a1,
    'a2) sTRLANG -> ('a1, 'a2) dISPCALC -> ('a1, 'a2) canElim -> ('a1, 'a2)
    dertree -> ('a1, 'a2) dertree **)

let elimFmls =
  canElim_canElimAll

type ('formula, 'structr) canElimRaw =
  ('formula, 'structr) dertree -> __ -> __ -> ('formula, 'structr) dertree

type ('formula, 'structr) canElimAllRaw =
  ('formula, 'structr) dertree -> __ -> ('formula, 'structr) dertree

(** val canElim_cutOnFull_iff :
    'a1 eqDec -> 'a1 fLANG -> 'a1 lOGLANG -> 'a2 eqDec -> 'a2 fLANG -> ('a1,
    'a2) sTRLANG -> ('a1, 'a2) dISPCALC -> (('a1, 'a2) canElimRaw, ('a1, 'a2)
    canElim) iffT0 **)

let canElim_cutOnFull_iff _ _ _ _ _ _ _ =
  (fun h dt _ _ _ -> h dt __ __),(fun h dt _ _ -> h dt __ __ __)

(** val canElimAll_cutOnFull_iff :
    'a1 eqDec -> 'a1 fLANG -> 'a1 lOGLANG -> 'a2 eqDec -> 'a2 fLANG -> ('a1,
    'a2) sTRLANG -> ('a1, 'a2) dISPCALC -> (('a1, 'a2) canElimAllRaw, ('a1,
    'a2) canElimAll) iffT0 **)

let canElimAll_cutOnFull_iff _ _ _ _ _ _ _ =
  (fun h dt _ _ -> h dt __),(fun h dt _ -> h dt __ __)

(** val canElim_ex :
    'a1 eqDec -> 'a1 fLANG -> 'a1 lOGLANG -> 'a2 eqDec -> 'a2 fLANG -> ('a1,
    'a2) sTRLANG -> ('a1, 'a2) dISPCALC -> ('a3 -> ('a1, 'a2) canElim) ->
    ('a1, 'a2) dertree -> 'a3 -> ('a1, 'a2) dertree **)

let canElim_ex _ _ _ _ _ _ _ helim dt x =
  helim x dt __ __ __

(** val cutOnFmls_Full :
    'a1 eqDec -> 'a1 fLANG -> 'a1 lOGLANG -> 'a2 eqDec -> 'a2 fLANG -> ('a1,
    'a2) sTRLANG -> ('a1, 'a2) dertree -> 'a1 **)

let cutOnFmls_Full eDf lf lL eDs ls sL = function
| Unf _ -> lL.atm "p"
| Der (_, r, l) ->
  let s0 = rule_eq_dec eDf lf lL eDs ls sL r (cUT eDf lf lL eDs ls sL) in
  if s0
  then let s1 = right_cut_dec eDf lf lL eDs ls sL l in
       (match s1 with
        | Some s ->
          let ExistT (_, s2) = s in
          let ExistT (_, s3) = s2 in let ExistT (_, s4) = s3 in s4
        | None -> assert false (* absurd case *))
  else lL.atm "p"

(** val allElim :
    'a1 eqDec -> 'a1 fLANG -> 'a1 lOGLANG -> 'a2 eqDec -> 'a2 fLANG -> ('a1,
    'a2) sTRLANG -> ('a1, 'a2) dISPCALC -> ('a1 -> __ -> ('a1, 'a2) canElim)
    -> ('a1, 'a2) dertree -> ('a1, 'a2) dertree **)

let allElim eDf lf lL eDs ls sL _ h = function
| Unf _ -> assert false (* absurd case *)
| Der (s, r, l) ->
  let s0 = rule_eq_dec eDf lf lL eDs ls sL r (cUT eDf lf lL eDs ls sL) in
  if s0
  then let hwfb =
         ruleInst_ruleSubst eDf lf lL eDs ls sL r
           ((map (conclDT eDf lf lL eDs ls sL) l),s)
       in
       (match l with
        | [] -> assert false (* absurd case *)
        | d::l0 ->
          (match l0 with
           | [] -> assert false (* absurd case *)
           | d0::l1 ->
             (match l1 with
              | [] ->
                let a = fmlSubst eDf lf lL (fst hwfb) (lL.fV "A") in
                h a __ (Der (s, r, (d::(d0::[])))) __ __ __
              | _::_ -> assert false (* absurd case *))))
  else Der (s, r, l)

(** val elimLP :
    'a1 eqDec -> 'a1 fLANG -> 'a1 lOGLANG -> 'a2 eqDec -> 'a2 fLANG -> ('a1,
    'a2) sTRLANG -> ('a1, 'a2) dISPCALC -> 'a1 -> ('a1, 'a2) canElim -> ('a1,
    'a2) dertree -> ('a1, 'a2) dertree **)

let elimLP eDf lf lL eDs ls sL dC _ x dt =
  canElim_canElimAll eDf lf lL eDs ls sL dC x dt

(** val elimLRP :
    'a1 eqDec -> 'a1 fLANG -> 'a1 lOGLANG -> 'a2 eqDec -> 'a2 fLANG -> ('a1,
    'a2) sTRLANG -> ('a1, 'a2) dISPCALC -> 'a1 -> ('a1, 'a2) canElim -> ('a1,
    'a2) dertree -> ('a1, 'a2) dertree **)

let elimLRP eDf lf lL eDs ls sL dC _ x dt =
  canElim_canElimAll eDf lf lL eDs ls sL dC x dt

(** val allLP' :
    'a1 eqDec -> 'a1 fLANG -> 'a1 lOGLANG -> 'a2 eqDec -> 'a2 fLANG -> ('a1,
    'a2) sTRLANG -> ('a1, 'a2) dISPCALC -> ('a1, 'a2) bELNAP -> 'a1 -> ('a1,
    'a2) canElimAll -> ('a1, 'a2) dertree -> ('a1, 'a2) dertree **)

let allLP' eDf lf lL eDs ls sL dC bP a helim dt =
  let s = allLP eDf lf lL eDs ls sL dC bP dt a in helim s __ __

(** val allLRP' :
    'a1 eqDec -> 'a1 fLANG -> 'a1 lOGLANG -> 'a2 eqDec -> 'a2 fLANG -> ('a1,
    'a2) sTRLANG -> ('a1, 'a2) dISPCALC -> ('a1, 'a2) bELNAP -> 'a1 -> ('a1,
    'a2) canElimAll -> ('a1, 'a2) dertree -> ('a1, 'a2) dertree **)

let allLRP' eDf lf lL eDs ls sL dC bP a helim dt =
  let s = allLRP eDf lf lL eDs ls sL dC bP dt a in helim s __ __

(** val th8 :
    'a1 eqDec -> 'a1 fLANG -> 'a1 lOGLANG -> 'a2 eqDec -> 'a2 fLANG -> ('a1,
    'a2) sTRLANG -> ('a1, 'a2) dISPCALC -> ('a1, 'a2) bELNAP -> 'a1 -> ('a1,
    'a2) canElim -> ('a1, 'a2) dertree -> ('a1, 'a2) dertree **)

let th8 eDf lf lL eDs ls sL dC bP a h dt =
  allLP' eDf lf lL eDs ls sL dC bP a (fun x _ _ ->
    elimLP eDf lf lL eDs ls sL dC a (fun x0 _ _ _ ->
      allLRP' eDf lf lL eDs ls sL dC bP a (fun x1 _ _ ->
        elimLRP eDf lf lL eDs ls sL dC a h x1) x0) x) dt

(** val allch :
    'a1 eqDec -> 'a1 fLANG -> 'a1 lOGLANG -> 'a2 eqDec -> 'a2 fLANG -> ('a1,
    'a2) sTRLANG -> ('a1, 'a2) dISPCALC -> ('a1, 'a2) bELNAP -> 'a1 -> ('a1,
    'a2) canElimAll -> ('a1, 'a2) dertree -> ('a1, 'a2) dertree **)

let allch eDf lf lL eDs ls sL dC bP a helim dt =
  let s = c8_holds eDf lf lL eDs ls sL dC bP a dt in helim s __ __

(** val th8ch' :
    'a1 eqDec -> 'a1 fLANG -> 'a1 lOGLANG -> 'a2 eqDec -> 'a2 fLANG -> ('a1,
    'a2) sTRLANG -> ('a1, 'a2) dISPCALC -> ('a1, 'a2) bELNAP -> 'a1 -> ('a1
    -> __ -> ('a1, 'a2) canElim) -> ('a1, 'a2) dertree -> ('a1, 'a2) dertree **)

let th8ch' eDf lf lL eDs ls sL dC bP a h dt =
  th8 eDf lf lL eDs ls sL dC bP a (fun x _ _ _ ->
    allch eDf lf lL eDs ls sL dC bP a (fun x0 _ _ ->
      elimFmls eDf lf lL eDs ls sL dC (fun x1 _ _ _ ->
        allElim eDf lf lL eDs ls sL dC h x1) x0) x) dt

(** val canElimFml :
    'a1 eqDec -> 'a1 fLANG -> 'a1 lOGLANG -> 'a2 eqDec -> 'a2 fLANG -> ('a1,
    'a2) sTRLANG -> ('a1, 'a2) dISPCALC -> ('a1, 'a2) bELNAP -> 'a1 -> ('a1,
    'a2) dertree -> ('a1, 'a2) dertree **)

let canElimFml eDf lf lL eDs ls sL dC bP a dt =
  ipse_rect eDf lf (fun a0 x x0 _ _ _ ->
    th8ch' eDf lf lL eDs ls sL dC bP a0 x x0) a dt __ __ __

(** val c3458_canElimRaw :
    'a1 eqDec -> 'a1 fLANG -> 'a1 lOGLANG -> 'a2 eqDec -> 'a2 fLANG -> ('a1,
    'a2) sTRLANG -> ('a1, 'a2) dISPCALC -> ('a1, 'a2) bELNAP -> ('a1, 'a2)
    dertree -> ('a1, 'a2) dertree **)

let c3458_canElimRaw eDf lf lL eDs ls sL dC bP dt =
  let _,x = canElim_cutOnFull_iff eDf lf lL eDs ls sL dC in
  x (fun dt0 _ _ ->
    let hdt0 = cutOnFmls_Full eDf lf lL eDs ls sL dt0 in
    (fun _ ->
    canElim_ex eDf lf lL eDs ls sL dC (fun phi x0 _ _ _ ->
      canElimFml eDf lf lL eDs ls sL dC bP phi x0) dt0 hdt0)) dt __ __

(** val cav :
    'a1 eqDec -> 'a1 fLANG -> 'a1 lOGLANG -> 'a2 eqDec -> 'a2 fLANG -> ('a1,
    'a2) sTRLANG -> ('a1, 'a2) dISPCALC -> ('a1, 'a2) bELNAP -> ('a1, 'a2)
    dertree -> ('a1, 'a2) dertree **)

let cav eDf lf lL eDs ls sL dC bP dt =
  let x = fun x ->
    elimFmls eDf lf lL eDs ls sL dC
      (fst (canElim_cutOnFull_iff eDf lf lL eDs ls sL dC) (fun x0 _ _ ->
        c3458_canElimRaw eDf lf lL eDs ls sL dC bP x0)) x
  in
  let _,x0 = canElimAll_cutOnFull_iff eDf lf lL eDs ls sL dC in
  x0 (fun x1 _ _ -> x x1) dt __

(** val cutElim :
    'a1 eqDec -> 'a1 fLANG -> 'a1 lOGLANG -> 'a2 eqDec -> 'a2 fLANG -> ('a1,
    'a2) sTRLANG -> ('a1, 'a2) dISPCALC -> ('a1, 'a2) bELNAP -> ('a1, 'a2)
    dertree -> ('a1, 'a2) dertree **)

let cutElim =
  cav

(** val atrefl :
    'a1 eqDec -> 'a1 fLANG -> 'a1 lOGLANG -> 'a2 eqDec -> 'a2 fLANG -> ('a1,
    'a2) sTRLANG -> ('a1, 'a2) rule **)

let atrefl _ _ lL _ _ sL =
  [],(Sequent ((sL.fS (lL.atm "p")), (sL.fS (lL.atm "p"))))

(** val frefl :
    'a1 eqDec -> 'a1 fLANG -> 'a1 lOGLANG -> 'a2 eqDec -> 'a2 fLANG -> ('a1,
    'a2) sTRLANG -> 'a1 -> ('a1, 'a2) rule **)

let frefl _ _ _ _ _ sL a =
  [],(Sequent ((sL.fS a), (sL.fS a)))

module Kt =
 struct
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

  (** val formula_rect :
      (string -> 'a1) -> (string -> 'a1) -> 'a1 -> 'a1 -> (formula -> 'a1 ->
      'a1) -> (formula -> 'a1 -> formula -> 'a1 -> 'a1) -> (formula -> 'a1 ->
      formula -> 'a1 -> 'a1) -> (formula -> 'a1 -> formula -> 'a1 -> 'a1) ->
      (formula -> 'a1 -> 'a1) -> (formula -> 'a1 -> 'a1) -> (formula -> 'a1
      -> 'a1) -> (formula -> 'a1 -> 'a1) -> formula -> 'a1 **)

  let rec formula_rect f f0 f1 f2 f3 f4 f5 f6 f7 f8 f9 f10 = function
  | Atf p -> f p
  | FVf a -> f0 a
  | Top -> f1
  | Bot -> f2
  | Neg phi -> f3 phi (formula_rect f f0 f1 f2 f3 f4 f5 f6 f7 f8 f9 f10 phi)
  | Imp (phi, psi) ->
    f4 phi (formula_rect f f0 f1 f2 f3 f4 f5 f6 f7 f8 f9 f10 phi) psi
      (formula_rect f f0 f1 f2 f3 f4 f5 f6 f7 f8 f9 f10 psi)
  | Dis (phi, psi) ->
    f5 phi (formula_rect f f0 f1 f2 f3 f4 f5 f6 f7 f8 f9 f10 phi) psi
      (formula_rect f f0 f1 f2 f3 f4 f5 f6 f7 f8 f9 f10 psi)
  | Con (phi, psi) ->
    f6 phi (formula_rect f f0 f1 f2 f3 f4 f5 f6 f7 f8 f9 f10 phi) psi
      (formula_rect f f0 f1 f2 f3 f4 f5 f6 f7 f8 f9 f10 psi)
  | Boxn phi -> f7 phi (formula_rect f f0 f1 f2 f3 f4 f5 f6 f7 f8 f9 f10 phi)
  | Dian phi -> f8 phi (formula_rect f f0 f1 f2 f3 f4 f5 f6 f7 f8 f9 f10 phi)
  | Boxp phi -> f9 phi (formula_rect f f0 f1 f2 f3 f4 f5 f6 f7 f8 f9 f10 phi)
  | Diap phi -> f10 phi (formula_rect f f0 f1 f2 f3 f4 f5 f6 f7 f8 f9 f10 phi)

  (** val formula_rec :
      (string -> 'a1) -> (string -> 'a1) -> 'a1 -> 'a1 -> (formula -> 'a1 ->
      'a1) -> (formula -> 'a1 -> formula -> 'a1 -> 'a1) -> (formula -> 'a1 ->
      formula -> 'a1 -> 'a1) -> (formula -> 'a1 -> formula -> 'a1 -> 'a1) ->
      (formula -> 'a1 -> 'a1) -> (formula -> 'a1 -> 'a1) -> (formula -> 'a1
      -> 'a1) -> (formula -> 'a1 -> 'a1) -> formula -> 'a1 **)

  let rec formula_rec f f0 f1 f2 f3 f4 f5 f6 f7 f8 f9 f10 = function
  | Atf p -> f p
  | FVf a -> f0 a
  | Top -> f1
  | Bot -> f2
  | Neg phi -> f3 phi (formula_rec f f0 f1 f2 f3 f4 f5 f6 f7 f8 f9 f10 phi)
  | Imp (phi, psi) ->
    f4 phi (formula_rec f f0 f1 f2 f3 f4 f5 f6 f7 f8 f9 f10 phi) psi
      (formula_rec f f0 f1 f2 f3 f4 f5 f6 f7 f8 f9 f10 psi)
  | Dis (phi, psi) ->
    f5 phi (formula_rec f f0 f1 f2 f3 f4 f5 f6 f7 f8 f9 f10 phi) psi
      (formula_rec f f0 f1 f2 f3 f4 f5 f6 f7 f8 f9 f10 psi)
  | Con (phi, psi) ->
    f6 phi (formula_rec f f0 f1 f2 f3 f4 f5 f6 f7 f8 f9 f10 phi) psi
      (formula_rec f f0 f1 f2 f3 f4 f5 f6 f7 f8 f9 f10 psi)
  | Boxn phi -> f7 phi (formula_rec f f0 f1 f2 f3 f4 f5 f6 f7 f8 f9 f10 phi)
  | Dian phi -> f8 phi (formula_rec f f0 f1 f2 f3 f4 f5 f6 f7 f8 f9 f10 phi)
  | Boxp phi -> f9 phi (formula_rec f f0 f1 f2 f3 f4 f5 f6 f7 f8 f9 f10 phi)
  | Diap phi -> f10 phi (formula_rec f f0 f1 f2 f3 f4 f5 f6 f7 f8 f9 f10 phi)

  type structr =
  | SVf of string
  | FSf of formula
  | I
  | Star of structr
  | Comma of structr * structr
  | BCirc of structr

  (** val structr_rect :
      (string -> 'a1) -> (formula -> 'a1) -> 'a1 -> (structr -> 'a1 -> 'a1)
      -> (structr -> 'a1 -> structr -> 'a1 -> 'a1) -> (structr -> 'a1 -> 'a1)
      -> structr -> 'a1 **)

  let rec structr_rect f f0 f1 f2 f3 f4 = function
  | SVf x -> f x
  | FSf a -> f0 a
  | I -> f1
  | Star x -> f2 x (structr_rect f f0 f1 f2 f3 f4 x)
  | Comma (x, y) ->
    f3 x (structr_rect f f0 f1 f2 f3 f4 x) y (structr_rect f f0 f1 f2 f3 f4 y)
  | BCirc x -> f4 x (structr_rect f f0 f1 f2 f3 f4 x)

  (** val structr_rec :
      (string -> 'a1) -> (formula -> 'a1) -> 'a1 -> (structr -> 'a1 -> 'a1)
      -> (structr -> 'a1 -> structr -> 'a1 -> 'a1) -> (structr -> 'a1 -> 'a1)
      -> structr -> 'a1 **)

  let rec structr_rec f f0 f1 f2 f3 f4 = function
  | SVf x -> f x
  | FSf a -> f0 a
  | I -> f1
  | Star x -> f2 x (structr_rec f f0 f1 f2 f3 f4 x)
  | Comma (x, y) ->
    f3 x (structr_rec f f0 f1 f2 f3 f4 x) y (structr_rec f f0 f1 f2 f3 f4 y)
  | BCirc x -> f4 x (structr_rec f f0 f1 f2 f3 f4 x)
 end

module Kt_LOG =
 struct
  (** val fml_eq_dec : Kt.formula eq_dec **)

  let rec fml_eq_dec f x0 =
    match f with
    | Kt.Atf p -> (match x0 with
                   | Kt.Atf p0 -> (=) p p0
                   | _ -> false)
    | Kt.FVf a -> (match x0 with
                   | Kt.FVf a0 -> (=) a a0
                   | _ -> false)
    | Kt.Top -> (match x0 with
                 | Kt.Top -> true
                 | _ -> false)
    | Kt.Bot -> (match x0 with
                 | Kt.Bot -> true
                 | _ -> false)
    | Kt.Neg phi ->
      (match x0 with
       | Kt.Neg phi0 -> fml_eq_dec phi phi0
       | _ -> false)
    | Kt.Imp (phi, psi) ->
      (match x0 with
       | Kt.Imp (phi0, psi0) ->
         if fml_eq_dec phi phi0 then fml_eq_dec psi psi0 else false
       | _ -> false)
    | Kt.Dis (phi, psi) ->
      (match x0 with
       | Kt.Dis (phi0, psi0) ->
         if fml_eq_dec phi phi0 then fml_eq_dec psi psi0 else false
       | _ -> false)
    | Kt.Con (phi, psi) ->
      (match x0 with
       | Kt.Con (phi0, psi0) ->
         if fml_eq_dec phi phi0 then fml_eq_dec psi psi0 else false
       | _ -> false)
    | Kt.Boxn phi ->
      (match x0 with
       | Kt.Boxn phi0 -> fml_eq_dec phi phi0
       | _ -> false)
    | Kt.Dian phi ->
      (match x0 with
       | Kt.Dian phi0 -> fml_eq_dec phi phi0
       | _ -> false)
    | Kt.Boxp phi ->
      (match x0 with
       | Kt.Boxp phi0 -> fml_eq_dec phi phi0
       | _ -> false)
    | Kt.Diap phi ->
      (match x0 with
       | Kt.Diap phi0 -> fml_eq_dec phi phi0
       | _ -> false)

  (** val ipse : Kt.formula -> Kt.formula list **)

  let ipse = function
  | Kt.Neg a0 -> a0::[]
  | Kt.Imp (a1, a2) -> a1::(a2::[])
  | Kt.Dis (a1, a2) -> a1::(a2::[])
  | Kt.Con (a1, a2) -> a1::(a2::[])
  | Kt.Boxn a0 -> a0::[]
  | Kt.Dian a0 -> a0::[]
  | Kt.Boxp a0 -> a0::[]
  | Kt.Diap a0 -> a0::[]
  | _ -> []

  (** val ipse_rect :
      (Kt.formula -> (Kt.formula -> __ -> 'a1) -> 'a1) -> Kt.formula -> 'a1 **)

  let rec ipse_rect h = function
  | Kt.Neg phi ->
    h (Kt.Neg phi) (fun b _ ->
      let s = fml_eq_dec b phi in
      if s then ipse_rect h phi else assert false (* absurd case *))
  | Kt.Imp (phi, psi) ->
    h (Kt.Imp (phi, psi)) (fun b _ ->
      let s = fml_eq_dec b phi in
      if s
      then ipse_rect h phi
      else let s0 = fml_eq_dec b psi in
           if s0 then ipse_rect h psi else assert false (* absurd case *))
  | Kt.Dis (phi, psi) ->
    h (Kt.Dis (phi, psi)) (fun b _ ->
      let s = fml_eq_dec b phi in
      if s
      then ipse_rect h phi
      else let s0 = fml_eq_dec b psi in
           if s0 then ipse_rect h psi else assert false (* absurd case *))
  | Kt.Con (phi, psi) ->
    h (Kt.Con (phi, psi)) (fun b _ ->
      let s = fml_eq_dec b phi in
      if s
      then ipse_rect h phi
      else let s0 = fml_eq_dec b psi in
           if s0 then ipse_rect h psi else assert false (* absurd case *))
  | Kt.Boxn phi ->
    h (Kt.Boxn phi) (fun b _ ->
      let s = fml_eq_dec b phi in
      if s then ipse_rect h phi else assert false (* absurd case *))
  | Kt.Dian phi ->
    h (Kt.Dian phi) (fun b _ ->
      let s = fml_eq_dec b phi in
      if s then ipse_rect h phi else assert false (* absurd case *))
  | Kt.Boxp phi ->
    h (Kt.Boxp phi) (fun b _ ->
      let s = fml_eq_dec b phi in
      if s then ipse_rect h phi else assert false (* absurd case *))
  | Kt.Diap phi ->
    h (Kt.Diap phi) (fun b _ ->
      let s = fml_eq_dec b phi in
      if s then ipse_rect h phi else assert false (* absurd case *))
  | x -> h x (fun _ _ -> assert false (* absurd case *))

  (** val fml_df : Kt.formula **)

  let fml_df =
    Kt.Atf ""

  (** val conn : Kt.formula -> Kt.formula list -> Kt.formula **)

  let conn a x =
    match a with
    | Kt.Neg _ -> (match x with
                   | [] -> fml_df
                   | b0::_ -> Kt.Neg b0)
    | Kt.Imp (_, _) ->
      (match x with
       | [] -> fml_df
       | b1::l0 -> (match l0 with
                    | [] -> fml_df
                    | b2::_ -> Kt.Imp (b1, b2)))
    | Kt.Dis (_, _) ->
      (match x with
       | [] -> fml_df
       | b1::l0 -> (match l0 with
                    | [] -> fml_df
                    | b2::_ -> Kt.Dis (b1, b2)))
    | Kt.Con (_, _) ->
      (match x with
       | [] -> fml_df
       | b1::l0 -> (match l0 with
                    | [] -> fml_df
                    | b2::_ -> Kt.Con (b1, b2)))
    | Kt.Boxn _ -> (match x with
                    | [] -> fml_df
                    | b0::_ -> Kt.Boxn b0)
    | Kt.Dian _ -> (match x with
                    | [] -> fml_df
                    | b0::_ -> Kt.Dian b0)
    | Kt.Boxp _ -> (match x with
                    | [] -> fml_df
                    | b0::_ -> Kt.Boxp b0)
    | Kt.Diap _ -> (match x with
                    | [] -> fml_df
                    | b0::_ -> Kt.Diap b0)
    | _ -> a

  (** val coq_Atm_dec : Kt.formula -> string option **)

  let coq_Atm_dec = function
  | Kt.Atf p -> Some p
  | _ -> None

  (** val coq_FV_dec : Kt.formula -> string option **)

  let coq_FV_dec = function
  | Kt.FVf a0 -> Some a0
  | _ -> None
 end

(** val eqDec_formula : Kt.formula eqDec **)

let eqDec_formula =
  Kt_LOG.fml_eq_dec

(** val f_Kt_log : Kt.formula fLANG **)

let f_Kt_log =
  { ipse = Kt_LOG.ipse; ipse_rect = (fun _ -> Kt_LOG.ipse_rect); conn =
    Kt_LOG.conn }

(** val kt_Atm : (Kt.formula, string) iXEXP **)

let kt_Atm =
  Kt_LOG.coq_Atm_dec

(** val kt_FV : (Kt.formula, string) iXEXP **)

let kt_FV =
  Kt_LOG.coq_FV_dec

(** val kt_log : Kt.formula lOGLANG **)

let kt_log =
  { atm = (fun x -> Kt.Atf x); fV = (fun x -> Kt.FVf x); aTMVAR = kt_Atm;
    fVVAR = kt_FV }

module Kt_STR =
 struct
  (** val str_eq_dec : Kt.structr eq_dec **)

  let rec str_eq_dec s x0 =
    match s with
    | Kt.SVf x ->
      (match x0 with
       | Kt.SVf x1 -> eqdec eqDec_string x x1
       | _ -> false)
    | Kt.FSf a ->
      (match x0 with
       | Kt.FSf a0 -> eqdec eqDec_formula a a0
       | _ -> false)
    | Kt.I -> (match x0 with
               | Kt.I -> true
               | _ -> false)
    | Kt.Star x -> (match x0 with
                    | Kt.Star x1 -> str_eq_dec x x1
                    | _ -> false)
    | Kt.Comma (x, y) ->
      (match x0 with
       | Kt.Comma (x1, y0) ->
         if str_eq_dec x x1 then str_eq_dec y y0 else false
       | _ -> false)
    | Kt.BCirc x ->
      (match x0 with
       | Kt.BCirc x1 -> str_eq_dec x x1
       | _ -> false)

  (** val ipse : Kt.structr -> Kt.structr list **)

  let ipse = function
  | Kt.Star x0 -> x0::[]
  | Kt.Comma (x1, x2) -> x1::(x2::[])
  | Kt.BCirc x0 -> x0::[]
  | _ -> []

  (** val ipse_rect :
      (Kt.structr -> (Kt.structr -> __ -> 'a1) -> 'a1) -> Kt.structr -> 'a1 **)

  let rec ipse_rect h = function
  | Kt.Star x ->
    h (Kt.Star x) (fun b _ ->
      let s = str_eq_dec b x in
      if s then ipse_rect h x else assert false (* absurd case *))
  | Kt.Comma (x, y) ->
    h (Kt.Comma (x, y)) (fun b _ ->
      let s = str_eq_dec b x in
      if s
      then ipse_rect h x
      else let s0 = str_eq_dec b y in
           if s0 then ipse_rect h y else assert false (* absurd case *))
  | Kt.BCirc x ->
    h (Kt.BCirc x) (fun b _ ->
      let s = str_eq_dec b x in
      if s then ipse_rect h x else assert false (* absurd case *))
  | x -> h x (fun _ _ -> assert false (* absurd case *))

  (** val str_df : Kt.structr **)

  let str_df =
    Kt.SVf ""

  (** val conn : Kt.structr -> Kt.structr list -> Kt.structr **)

  let conn x x0 =
    match x with
    | Kt.Star _ -> (match x0 with
                    | [] -> str_df
                    | y0::_ -> Kt.Star y0)
    | Kt.Comma (_, _) ->
      (match x0 with
       | [] -> str_df
       | y1::l0 -> (match l0 with
                    | [] -> str_df
                    | y2::_ -> Kt.Comma (y1, y2)))
    | Kt.BCirc _ -> (match x0 with
                     | [] -> str_df
                     | y0::_ -> Kt.BCirc y0)
    | _ -> x

  (** val coq_SV_dec : Kt.structr -> string option **)

  let coq_SV_dec = function
  | Kt.SVf x0 -> Some x0
  | _ -> None

  (** val coq_FS_dec : Kt.structr -> Kt.formula option **)

  let coq_FS_dec = function
  | Kt.FSf a -> Some a
  | _ -> None

  (** val sgnips : Kt.structr -> bool list **)

  let sgnips = function
  | Kt.Star _ -> false::[]
  | Kt.Comma (_, _) -> true::(true::[])
  | Kt.BCirc _ -> true::[]
  | _ -> []
 end

(** val eqDec_structr : Kt.structr eqDec **)

let eqDec_structr =
  Kt_STR.str_eq_dec

(** val f_Kt : Kt.structr fLANG **)

let f_Kt =
  { ipse = Kt_STR.ipse; ipse_rect = (fun _ -> Kt_STR.ipse_rect); conn =
    Kt_STR.conn }

(** val kt_SV : (Kt.structr, string) iXEXP **)

let kt_SV =
  Kt_STR.coq_SV_dec

(** val kt_FS : (Kt.structr, Kt.formula) iXEXP **)

let kt_FS =
  Kt_STR.coq_FS_dec

(** val kt_str : (Kt.formula, Kt.structr) sTRLANG **)

let kt_str =
  { sV = (fun x -> Kt.SVf x); fS = (fun x -> Kt.FSf x); sVVAR = kt_SV;
    fSVAR = kt_FS; sgnips = Kt_STR.sgnips }

module KtRules =
 struct
  (** val coq_Topl : (Kt.formula, Kt.structr) rule **)

  let coq_Topl =
    ((Sequent (Kt.I, (Kt.SVf "X")))::[]),(Sequent ((Kt.FSf Kt.Top), (Kt.SVf
      "X")))

  (** val coq_Topr : (Kt.formula, Kt.structr) rule **)

  let coq_Topr =
    [],(Sequent (Kt.I, (Kt.FSf Kt.Top)))

  (** val coq_Botl : (Kt.formula, Kt.structr) rule **)

  let coq_Botl =
    [],(Sequent ((Kt.FSf Kt.Bot), Kt.I))

  (** val coq_Botr : (Kt.formula, Kt.structr) rule **)

  let coq_Botr =
    ((Sequent ((Kt.SVf "X"), Kt.I))::[]),(Sequent ((Kt.SVf "X"), (Kt.FSf
      Kt.Bot)))

  (** val coq_Negl : (Kt.formula, Kt.structr) rule **)

  let coq_Negl =
    ((Sequent ((Kt.Star (Kt.FSf (Kt.FVf "A"))), (Kt.SVf "X")))::[]),(Sequent
      ((Kt.FSf (Kt.Neg (Kt.FVf "A"))), (Kt.SVf "X")))

  (** val coq_Negr : (Kt.formula, Kt.structr) rule **)

  let coq_Negr =
    ((Sequent ((Kt.SVf "X"), (Kt.Star (Kt.FSf (Kt.FVf "A")))))::[]),(Sequent
      ((Kt.SVf "X"), (Kt.FSf (Kt.Neg (Kt.FVf "A")))))

  (** val coq_Conl : (Kt.formula, Kt.structr) rule **)

  let coq_Conl =
    ((Sequent ((Kt.Comma ((Kt.FSf (Kt.FVf "A")), (Kt.FSf (Kt.FVf "B")))),
      (Kt.SVf "X")))::[]),(Sequent ((Kt.FSf (Kt.Con ((Kt.FVf "A"), (Kt.FVf
      "B")))), (Kt.SVf "X")))

  (** val coq_Conr : (Kt.formula, Kt.structr) rule **)

  let coq_Conr =
    ((Sequent ((Kt.SVf "X"), (Kt.FSf (Kt.FVf "A"))))::((Sequent ((Kt.SVf
      "Y"), (Kt.FSf (Kt.FVf "B"))))::[])),(Sequent ((Kt.Comma ((Kt.SVf "X"),
      (Kt.SVf "Y"))), (Kt.FSf (Kt.Con ((Kt.FVf "A"), (Kt.FVf "B"))))))

  (** val coq_Disl : (Kt.formula, Kt.structr) rule **)

  let coq_Disl =
    ((Sequent ((Kt.FSf (Kt.FVf "A")), (Kt.SVf "X")))::((Sequent ((Kt.FSf
      (Kt.FVf "B")), (Kt.SVf "Y")))::[])),(Sequent ((Kt.FSf (Kt.Dis ((Kt.FVf
      "A"), (Kt.FVf "B")))), (Kt.Comma ((Kt.SVf "X"), (Kt.SVf "Y")))))

  (** val coq_Disr : (Kt.formula, Kt.structr) rule **)

  let coq_Disr =
    ((Sequent ((Kt.SVf "X"), (Kt.Comma ((Kt.FSf (Kt.FVf "A")), (Kt.FSf
      (Kt.FVf "B"))))))::[]),(Sequent ((Kt.SVf "X"), (Kt.FSf (Kt.Dis ((Kt.FVf
      "A"), (Kt.FVf "B"))))))

  (** val coq_Impl : (Kt.formula, Kt.structr) rule **)

  let coq_Impl =
    ((Sequent ((Kt.SVf "X"), (Kt.FSf (Kt.FVf "A"))))::((Sequent ((Kt.FSf
      (Kt.FVf "B")), (Kt.SVf "Y")))::[])),(Sequent ((Kt.FSf (Kt.Imp ((Kt.FVf
      "A"), (Kt.FVf "B")))), (Kt.Comma ((Kt.Star (Kt.SVf "X")), (Kt.SVf
      "Y")))))

  (** val coq_Impr : (Kt.formula, Kt.structr) rule **)

  let coq_Impr =
    ((Sequent ((Kt.Comma ((Kt.SVf "X"), (Kt.FSf (Kt.FVf "A")))), (Kt.FSf
      (Kt.FVf "B"))))::[]),(Sequent ((Kt.SVf "X"), (Kt.FSf (Kt.Imp ((Kt.FVf
      "A"), (Kt.FVf "B"))))))

  (** val coq_Boxnl : (Kt.formula, Kt.structr) rule **)

  let coq_Boxnl =
    ((Sequent ((Kt.FSf (Kt.FVf "A")), (Kt.SVf "X")))::[]),(Sequent ((Kt.FSf
      (Kt.Boxn (Kt.FVf "A"))), (Kt.BCirc (Kt.SVf "X"))))

  (** val coq_Boxnr : (Kt.formula, Kt.structr) rule **)

  let coq_Boxnr =
    ((Sequent ((Kt.BCirc (Kt.SVf "X")), (Kt.FSf (Kt.FVf "A"))))::[]),(Sequent
      ((Kt.SVf "X"), (Kt.FSf (Kt.Boxn (Kt.FVf "A")))))

  (** val coq_Dianl : (Kt.formula, Kt.structr) rule **)

  let coq_Dianl =
    ((Sequent ((Kt.Star (Kt.BCirc (Kt.Star (Kt.FSf (Kt.FVf "A"))))), (Kt.SVf
      "X")))::[]),(Sequent ((Kt.FSf (Kt.Dian (Kt.FVf "A"))), (Kt.SVf "X")))

  (** val coq_Dianr : (Kt.formula, Kt.structr) rule **)

  let coq_Dianr =
    ((Sequent ((Kt.SVf "X"), (Kt.FSf (Kt.FVf "A"))))::[]),(Sequent ((Kt.Star
      (Kt.BCirc (Kt.Star (Kt.SVf "X")))), (Kt.FSf (Kt.Dian (Kt.FVf "A")))))

  (** val coq_Boxpl : (Kt.formula, Kt.structr) rule **)

  let coq_Boxpl =
    ((Sequent ((Kt.FSf (Kt.FVf "A")), (Kt.SVf "X")))::[]),(Sequent ((Kt.FSf
      (Kt.Boxp (Kt.FVf "A"))), (Kt.Star (Kt.BCirc (Kt.Star (Kt.SVf "X"))))))

  (** val coq_Boxpr : (Kt.formula, Kt.structr) rule **)

  let coq_Boxpr =
    ((Sequent ((Kt.SVf "X"), (Kt.Star (Kt.BCirc (Kt.Star (Kt.FSf (Kt.FVf
      "A")))))))::[]),(Sequent ((Kt.SVf "X"), (Kt.FSf (Kt.Boxp (Kt.FVf
      "A")))))

  (** val coq_Diapl : (Kt.formula, Kt.structr) rule **)

  let coq_Diapl =
    ((Sequent ((Kt.FSf (Kt.FVf "A")), (Kt.BCirc (Kt.SVf "X"))))::[]),(Sequent
      ((Kt.FSf (Kt.Diap (Kt.FVf "A"))), (Kt.SVf "X")))

  (** val coq_Diapr : (Kt.formula, Kt.structr) rule **)

  let coq_Diapr =
    ((Sequent ((Kt.SVf "X"), (Kt.FSf (Kt.FVf "A"))))::[]),(Sequent ((Kt.BCirc
      (Kt.SVf "X")), (Kt.FSf (Kt.Diap (Kt.FVf "A")))))

  (** val coq_Iaddl : (Kt.formula, Kt.structr) rule **)

  let coq_Iaddl =
    ((Sequent ((Kt.SVf "X"), (Kt.SVf "Y")))::[]),(Sequent ((Kt.Comma (Kt.I,
      (Kt.SVf "X"))), (Kt.SVf "Y")))

  (** val coq_Idell : (Kt.formula, Kt.structr) rule **)

  let coq_Idell =
    ((Sequent ((Kt.Comma (Kt.I, (Kt.SVf "X"))), (Kt.SVf "Y")))::[]),(Sequent
      ((Kt.SVf "X"), (Kt.SVf "Y")))

  (** val coq_Iaddr : (Kt.formula, Kt.structr) rule **)

  let coq_Iaddr =
    ((Sequent ((Kt.SVf "X"), (Kt.SVf "Y")))::[]),(Sequent ((Kt.SVf "X"),
      (Kt.Comma (Kt.I, (Kt.SVf "Y")))))

  (** val coq_Idelr : (Kt.formula, Kt.structr) rule **)

  let coq_Idelr =
    ((Sequent ((Kt.SVf "X"), (Kt.Comma (Kt.I, (Kt.SVf "Y")))))::[]),(Sequent
      ((Kt.SVf "X"), (Kt.SVf "Y")))

  (** val coq_Isl : (Kt.formula, Kt.structr) rule **)

  let coq_Isl =
    ((Sequent (Kt.I, (Kt.SVf "Y")))::[]),(Sequent ((Kt.Star Kt.I), (Kt.SVf
      "Y")))

  (** val coq_Iul : (Kt.formula, Kt.structr) rule **)

  let coq_Iul =
    ((Sequent ((Kt.Star Kt.I), (Kt.SVf "Y")))::[]),(Sequent (Kt.I, (Kt.SVf
      "Y")))

  (** val coq_Isr : (Kt.formula, Kt.structr) rule **)

  let coq_Isr =
    ((Sequent ((Kt.SVf "Y"), Kt.I))::[]),(Sequent ((Kt.SVf "Y"), (Kt.Star
      Kt.I)))

  (** val coq_Iur : (Kt.formula, Kt.structr) rule **)

  let coq_Iur =
    ((Sequent ((Kt.SVf "Y"), (Kt.Star Kt.I)))::[]),(Sequent ((Kt.SVf "Y"),
      Kt.I))

  (** val coq_Wkl : (Kt.formula, Kt.structr) rule **)

  let coq_Wkl =
    ((Sequent ((Kt.SVf "X"), (Kt.SVf "Y")))::[]),(Sequent ((Kt.Comma ((Kt.SVf
      "Z"), (Kt.SVf "X"))), (Kt.SVf "Y")))

  (** val coq_Wkr : (Kt.formula, Kt.structr) rule **)

  let coq_Wkr =
    ((Sequent ((Kt.SVf "X"), (Kt.SVf "Y")))::[]),(Sequent ((Kt.SVf "X"),
      (Kt.Comma ((Kt.SVf "Y"), (Kt.SVf "Z")))))

  (** val coq_Assol : (Kt.formula, Kt.structr) rule **)

  let coq_Assol =
    ((Sequent ((Kt.Comma ((Kt.SVf "X"), (Kt.Comma ((Kt.SVf "Y"), (Kt.SVf
      "Z"))))), (Kt.SVf "W")))::[]),(Sequent ((Kt.Comma ((Kt.Comma ((Kt.SVf
      "X"), (Kt.SVf "Y"))), (Kt.SVf "Z"))), (Kt.SVf "W")))

  (** val coq_Assolinv : (Kt.formula, Kt.structr) rule **)

  let coq_Assolinv =
    ((Sequent ((Kt.Comma ((Kt.Comma ((Kt.SVf "X"), (Kt.SVf "Y"))), (Kt.SVf
      "Z"))), (Kt.SVf "W")))::[]),(Sequent ((Kt.Comma ((Kt.SVf "X"),
      (Kt.Comma ((Kt.SVf "Y"), (Kt.SVf "Z"))))), (Kt.SVf "W")))

  (** val coq_Assor : (Kt.formula, Kt.structr) rule **)

  let coq_Assor =
    ((Sequent ((Kt.SVf "X"), (Kt.Comma ((Kt.SVf "Y"), (Kt.Comma ((Kt.SVf
      "Z"), (Kt.SVf "W")))))))::[]),(Sequent ((Kt.SVf "X"), (Kt.Comma
      ((Kt.Comma ((Kt.SVf "Y"), (Kt.SVf "Z"))), (Kt.SVf "W")))))

  (** val coq_Assorinv : (Kt.formula, Kt.structr) rule **)

  let coq_Assorinv =
    ((Sequent ((Kt.SVf "X"), (Kt.Comma ((Kt.Comma ((Kt.SVf "Y"), (Kt.SVf
      "Z"))), (Kt.SVf "W")))))::[]),(Sequent ((Kt.SVf "X"), (Kt.Comma
      ((Kt.SVf "Y"), (Kt.Comma ((Kt.SVf "Z"), (Kt.SVf "W")))))))

  (** val coq_Comml : (Kt.formula, Kt.structr) rule **)

  let coq_Comml =
    ((Sequent ((Kt.Comma ((Kt.SVf "X"), (Kt.SVf "Y"))), (Kt.SVf
      "Z")))::[]),(Sequent ((Kt.Comma ((Kt.SVf "Y"), (Kt.SVf "X"))), (Kt.SVf
      "Z")))

  (** val coq_Commr : (Kt.formula, Kt.structr) rule **)

  let coq_Commr =
    ((Sequent ((Kt.SVf "X"), (Kt.Comma ((Kt.SVf "Y"), (Kt.SVf
      "Z")))))::[]),(Sequent ((Kt.SVf "X"), (Kt.Comma ((Kt.SVf "Z"), (Kt.SVf
      "Y")))))

  (** val coq_Contl : (Kt.formula, Kt.structr) rule **)

  let coq_Contl =
    ((Sequent ((Kt.Comma ((Kt.SVf "X"), (Kt.SVf "X"))), (Kt.SVf
      "Y")))::[]),(Sequent ((Kt.SVf "X"), (Kt.SVf "Y")))

  (** val coq_Contr : (Kt.formula, Kt.structr) rule **)

  let coq_Contr =
    ((Sequent ((Kt.SVf "X"), (Kt.Comma ((Kt.SVf "Y"), (Kt.SVf
      "Y")))))::[]),(Sequent ((Kt.SVf "X"), (Kt.SVf "Y")))

  (** val coq_Icl : (Kt.formula, Kt.structr) rule **)

  let coq_Icl =
    ((Sequent (Kt.I, (Kt.SVf "Y")))::[]),(Sequent ((Kt.BCirc Kt.I), (Kt.SVf
      "Y")))

  (** val coq_Icr : (Kt.formula, Kt.structr) rule **)

  let coq_Icr =
    ((Sequent ((Kt.SVf "X"), Kt.I))::[]),(Sequent ((Kt.SVf "X"), (Kt.BCirc
      Kt.I)))

  (** val coq_Mlrn : (Kt.formula, Kt.structr) rule **)

  let coq_Mlrn =
    ((Sequent ((Kt.Comma ((Kt.SVf "X"), (Kt.SVf "Y"))), (Kt.SVf
      "Z")))::[]),(Sequent ((Kt.SVf "X"), (Kt.Comma ((Kt.SVf "Z"), (Kt.Star
      (Kt.SVf "Y"))))))

  (** val coq_Mrrs : (Kt.formula, Kt.structr) rule **)

  let coq_Mrrs =
    ((Sequent ((Kt.SVf "X"), (Kt.Comma ((Kt.SVf "Y"), (Kt.Star (Kt.SVf
      "Z"))))))::[]),(Sequent ((Kt.Comma ((Kt.SVf "X"), (Kt.SVf "Z"))),
      (Kt.SVf "Y")))

  (** val coq_Mlln : (Kt.formula, Kt.structr) rule **)

  let coq_Mlln =
    ((Sequent ((Kt.Comma ((Kt.SVf "X"), (Kt.SVf "Y"))), (Kt.SVf
      "Z")))::[]),(Sequent ((Kt.SVf "Y"), (Kt.Comma ((Kt.Star (Kt.SVf "X")),
      (Kt.SVf "Z")))))

  (** val coq_Mrls : (Kt.formula, Kt.structr) rule **)

  let coq_Mrls =
    ((Sequent ((Kt.SVf "X"), (Kt.Comma ((Kt.Star (Kt.SVf "Y")), (Kt.SVf
      "Z")))))::[]),(Sequent ((Kt.Comma ((Kt.SVf "Y"), (Kt.SVf "X"))),
      (Kt.SVf "Z")))

  (** val coq_Mrrn : (Kt.formula, Kt.structr) rule **)

  let coq_Mrrn =
    ((Sequent ((Kt.SVf "X"), (Kt.Comma ((Kt.SVf "Y"), (Kt.SVf
      "Z")))))::[]),(Sequent ((Kt.Comma ((Kt.SVf "X"), (Kt.Star (Kt.SVf
      "Z")))), (Kt.SVf "Y")))

  (** val coq_Mlrs : (Kt.formula, Kt.structr) rule **)

  let coq_Mlrs =
    ((Sequent ((Kt.Comma ((Kt.SVf "X"), (Kt.Star (Kt.SVf "Y")))), (Kt.SVf
      "Z")))::[]),(Sequent ((Kt.SVf "X"), (Kt.Comma ((Kt.SVf "Z"), (Kt.SVf
      "Y")))))

  (** val coq_Mrln : (Kt.formula, Kt.structr) rule **)

  let coq_Mrln =
    ((Sequent ((Kt.SVf "X"), (Kt.Comma ((Kt.SVf "Y"), (Kt.SVf
      "Z")))))::[]),(Sequent ((Kt.Comma ((Kt.Star (Kt.SVf "Y")), (Kt.SVf
      "X"))), (Kt.SVf "Z")))

  (** val coq_Mlls : (Kt.formula, Kt.structr) rule **)

  let coq_Mlls =
    ((Sequent ((Kt.Comma ((Kt.Star (Kt.SVf "X")), (Kt.SVf "Y"))), (Kt.SVf
      "Z")))::[]),(Sequent ((Kt.SVf "Y"), (Kt.Comma ((Kt.SVf "X"), (Kt.SVf
      "Z")))))

  (** val coq_Ssn : (Kt.formula, Kt.structr) rule **)

  let coq_Ssn =
    ((Sequent ((Kt.Star (Kt.SVf "X")), (Kt.SVf "Y")))::[]),(Sequent ((Kt.Star
      (Kt.SVf "Y")), (Kt.SVf "X")))

  (** val coq_Sns : (Kt.formula, Kt.structr) rule **)

  let coq_Sns =
    ((Sequent ((Kt.SVf "X"), (Kt.Star (Kt.SVf "Y"))))::[]),(Sequent ((Kt.SVf
      "Y"), (Kt.Star (Kt.SVf "X"))))

  (** val coq_DSEl : (Kt.formula, Kt.structr) rule **)

  let coq_DSEl =
    ((Sequent ((Kt.Star (Kt.Star (Kt.SVf "X"))), (Kt.SVf "Y")))::[]),(Sequent
      ((Kt.SVf "X"), (Kt.SVf "Y")))

  (** val coq_DSIl : (Kt.formula, Kt.structr) rule **)

  let coq_DSIl =
    ((Sequent ((Kt.SVf "X"), (Kt.SVf "Y")))::[]),(Sequent ((Kt.Star (Kt.Star
      (Kt.SVf "X"))), (Kt.SVf "Y")))

  (** val coq_DSEr : (Kt.formula, Kt.structr) rule **)

  let coq_DSEr =
    ((Sequent ((Kt.SVf "X"), (Kt.Star (Kt.Star (Kt.SVf "Y")))))::[]),(Sequent
      ((Kt.SVf "X"), (Kt.SVf "Y")))

  (** val coq_DSIr : (Kt.formula, Kt.structr) rule **)

  let coq_DSIr =
    ((Sequent ((Kt.SVf "X"), (Kt.SVf "Y")))::[]),(Sequent ((Kt.SVf "X"),
      (Kt.Star (Kt.Star (Kt.SVf "Y")))))

  (** val coq_Scl : (Kt.formula, Kt.structr) rule **)

  let coq_Scl =
    ((Sequent ((Kt.BCirc (Kt.SVf "X")), (Kt.SVf "Y")))::[]),(Sequent ((Kt.SVf
      "X"), (Kt.BCirc (Kt.SVf "Y"))))

  (** val coq_Scr : (Kt.formula, Kt.structr) rule **)

  let coq_Scr =
    ((Sequent ((Kt.SVf "X"), (Kt.BCirc (Kt.SVf "Y"))))::[]),(Sequent
      ((Kt.BCirc (Kt.SVf "X")), (Kt.SVf "Y")))

  (** val coq_Sss : (Kt.formula, Kt.structr) rule **)

  let coq_Sss =
    ((Sequent ((Kt.Star (Kt.SVf "X")), (Kt.Star (Kt.SVf "Y"))))::[]),(Sequent
      ((Kt.SVf "Y"), (Kt.SVf "X")))
 end

type ('formula, 'structr) c8_case_alt =
  ('formula, 'structr) deriv_cofseqs -> ('formula, 'structr) deriv_cofseq

(** val c8_case_alt_imp_C8_case :
    'a1 eqDec -> 'a1 fLANG -> 'a1 lOGLANG -> 'a2 eqDec -> 'a2 fLANG -> ('a1,
    'a2) sTRLANG -> ('a1, 'a2) dISPCALC -> 'a2 -> 'a2 -> ('a1, 'a2) sequent
    list -> ('a1, 'a2) c8_case_alt -> ('a1, 'a2) dertree list -> ('a1, 'a2)
    dertree **)

let c8_case_alt_imp_C8_case eDf lf lL eDs ls sL dC x y ls0 halt ld =
  let s = Sequent (x, y) in
  let x0,_ = deriv_cofseq_iff eDf lf lL eDs ls sL dC s in
  x0 (halt (let _,x1 = deriv_cofseqs_iff eDf lf lL eDs ls sL dC ls0 in x1 ld))

(** val lP_exhibit :
    'a1 eqDec -> 'a1 fLANG -> 'a1 lOGLANG -> 'a2 eqDec -> 'a2 fLANG -> ('a1,
    'a2) sTRLANG -> 'a1 -> ('a1, 'a2) sequent -> ('a1, 'a2) rule -> ('a1,
    'a2) dertree list -> ('a2, (('a1, 'a2) rule, (('a1, 'a2) dertree list,
    ('a1, 'a2) dertree) sigT) sigT) sigT **)

let lP_exhibit eDf lf lL eDs ls sL a _ _ l =
  let s0 = lP_dec eDf lf lL eDs ls sL l a in
  (match s0 with
   | Some s -> s
   | None -> assert false (* absurd case *))

(** val rP_exhibit :
    'a1 eqDec -> 'a1 fLANG -> 'a1 lOGLANG -> 'a2 eqDec -> 'a2 fLANG -> ('a1,
    'a2) sTRLANG -> 'a1 -> ('a1, 'a2) sequent -> ('a1, 'a2) rule -> ('a1,
    'a2) dertree list -> ('a2, (('a1, 'a2) dertree, (('a1, 'a2) rule, ('a1,
    'a2) dertree list) sigT) sigT) sigT **)

let rP_exhibit eDf lf lL eDs ls sL a _ _ l =
  let s0 = rP_dec eDf lf lL eDs ls sL l a in
  (match s0 with
   | Some s -> s
   | None -> assert false (* absurd case *))

(** val reduce_C8 :
    'a1 eqDec -> 'a1 fLANG -> 'a1 lOGLANG -> 'a2 eqDec -> 'a2 fLANG -> ('a1,
    'a2) sTRLANG -> ('a1, 'a2) dISPCALC -> ('a1 -> ('a1, 'a2) dertree list ->
    'a2 -> 'a2 -> ('a1, 'a2) rule -> ('a1, 'a2) dertree list -> ('a1, 'a2)
    rule -> ('a1, 'a2) dertree list -> ('a1, 'a2) afsSubst -> __ -> __ -> __
    -> __ -> __ -> __ -> __ -> ('a1, 'a2) dertree) -> 'a1 -> ('a1, 'a2)
    dertree -> ('a1, 'a2) dertree **)

let reduce_C8 eDf lf lL eDs ls sL _ hred a = function
| Unf _ -> assert false (* absurd case *)
| Der (s, r, l) ->
  let s0 = rule_eq_dec eDf lf lL eDs ls sL r (cUT eDf lf lL eDs ls sL) in
  if s0
  then let hLP = lP_exhibit eDf lf lL eDs ls sL a s r l in
       let hRP = rP_exhibit eDf lf lL eDs ls sL a s r l in
       let ExistT (x, s1) = hLP in
       let ExistT (x0, s2) = s1 in
       let ExistT (x1, _) = s2 in
       let ExistT (x2, s3) = hRP in
       let ExistT (_, s4) = s3 in
       let ExistT (x3, s5) = s4 in
       let hwfr =
         ruleInst_ruleSubst eDf lf lL eDs ls sL (cUT eDf lf lL eDs ls sL)
           ((map (conclDT eDf lf lL eDs ls sL) ((Der ((Sequent (x,
              (sL.fS a))), x0, x1))::((Der ((Sequent ((sL.fS a), x2)), x3,
              s5))::[]))),s)
       in
       hred a l x x2 x0 x1 x3 s5 hwfr __ __ __ __ __ __ __
  else Der (s, r, l)

(** val kt_DC : (Kt.formula, Kt.structr) dISPCALC **)

let kt_DC =
  (atrefl eqDec_formula f_Kt_log kt_log eqDec_structr f_Kt kt_str)::(
    (cUT eqDec_formula f_Kt_log kt_log eqDec_structr f_Kt kt_str)::(KtRules.coq_Topl::(KtRules.coq_Topr::(KtRules.coq_Botl::(KtRules.coq_Botr::(KtRules.coq_Negl::(KtRules.coq_Negr::(KtRules.coq_Conl::(KtRules.coq_Conr::(KtRules.coq_Disl::(KtRules.coq_Disr::(KtRules.coq_Impl::(KtRules.coq_Impr::(KtRules.coq_Boxnl::(KtRules.coq_Boxnr::(KtRules.coq_Dianl::(KtRules.coq_Dianr::(KtRules.coq_Boxpl::(KtRules.coq_Boxpr::(KtRules.coq_Diapl::(KtRules.coq_Diapr::(KtRules.coq_Iaddl::(KtRules.coq_Idell::(KtRules.coq_Iaddr::(KtRules.coq_Idelr::(KtRules.coq_Isl::(KtRules.coq_Iul::(KtRules.coq_Isr::(KtRules.coq_Iur::(KtRules.coq_Wkl::(KtRules.coq_Wkr::(KtRules.coq_Assol::(KtRules.coq_Assolinv::(KtRules.coq_Assor::(KtRules.coq_Assorinv::(KtRules.coq_Comml::(KtRules.coq_Commr::(KtRules.coq_Contl::(KtRules.coq_Contr::(KtRules.coq_Icl::(KtRules.coq_Icr::(KtRules.coq_Mlrn::(KtRules.coq_Mrrs::(KtRules.coq_Mlln::(KtRules.coq_Mrls::(KtRules.coq_Mrrn::(KtRules.coq_Mlrs::(KtRules.coq_Mrln::(KtRules.coq_Mlls::(KtRules.coq_Ssn::(KtRules.coq_Sns::(KtRules.coq_DSEl::(KtRules.coq_DSIl::(KtRules.coq_DSEr::(KtRules.coq_DSIr::(KtRules.coq_Scl::(KtRules.coq_Scr::[])))))))))))))))))))))))))))))))))))))))))))))))))))))))))

module KtDeriv =
 struct
  (** val dernc_Sss : (Kt.formula, Kt.structr) derivRuleNC **)

  let dernc_Sss =
    let x = Kt.SVf "X" in
    let y = Kt.SVf "Y" in
    Der ((Sequent (y, x)), KtRules.coq_DSEl, ((Der ((Sequent ((Kt.Star
    (Kt.Star y)), x)), KtRules.coq_Ssn, ((Unf (Sequent ((Kt.Star x), (Kt.Star
    y))))::[])))::[]))

  (** val dernc_frefl : Kt.formula -> (Kt.formula, Kt.structr) derivRuleNC **)

  let rec dernc_frefl = function
  | Kt.Atf p ->
    Der ((Sequent ((Kt.FSf (Kt.Atf p)), (Kt.FSf (Kt.Atf p)))),
      (atrefl eqDec_formula f_Kt_log kt_log eqDec_structr f_Kt kt_str), [])
  | Kt.FVf _ -> assert false (* absurd case *)
  | Kt.Top ->
    Der ((Sequent ((Kt.FSf Kt.Top), (Kt.FSf Kt.Top))), KtRules.coq_Topl,
      ((Der ((Sequent (Kt.I, (Kt.FSf Kt.Top))), KtRules.coq_Topr, []))::[]))
  | Kt.Bot ->
    Der ((Sequent ((Kt.FSf Kt.Bot), (Kt.FSf Kt.Bot))), KtRules.coq_Botr,
      ((Der ((Sequent ((Kt.FSf Kt.Bot), Kt.I)), KtRules.coq_Botl, []))::[]))
  | Kt.Neg phi ->
    let iHA = dernc_frefl phi in
    derivRuleNC_rule_bw_inDC eqDec_formula f_Kt_log kt_log eqDec_structr f_Kt
      kt_str kt_DC []
      (premsRule eqDec_formula f_Kt_log kt_log eqDec_structr f_Kt kt_str
        KtRules.coq_Negr)
      (conclRule eqDec_formula f_Kt_log kt_log eqDec_structr f_Kt kt_str
        KtRules.coq_Negr)
      (seq_matchsub eqDec_formula f_Kt_log kt_log eqDec_structr f_Kt kt_str
        (conclRule eqDec_formula f_Kt_log kt_log eqDec_structr f_Kt kt_str
          KtRules.coq_Negr) (Sequent ((kt_str.fS (Kt.Neg phi)),
        (kt_str.fS (Kt.Neg phi))))) (ForallT_cons ((Sequent ((Kt.SVf "X"),
      (Kt.Star (Kt.FSf (Kt.FVf "A"))))), [],
      (derivRuleNC_rule_bw_inDC eqDec_formula f_Kt_log kt_log eqDec_structr
        f_Kt kt_str kt_DC []
        (premsRule eqDec_formula f_Kt_log kt_log eqDec_structr f_Kt kt_str
          KtRules.coq_Negl)
        (conclRule eqDec_formula f_Kt_log kt_log eqDec_structr f_Kt kt_str
          KtRules.coq_Negl)
        (seq_matchsub eqDec_formula f_Kt_log kt_log eqDec_structr f_Kt kt_str
          (conclRule eqDec_formula f_Kt_log kt_log eqDec_structr f_Kt kt_str
            KtRules.coq_Negl) (Sequent ((Kt.FSf (Kt.Neg phi)), (Kt.Star
          (Kt.FSf phi))))) (ForallT_cons ((Sequent ((Kt.Star (Kt.FSf (Kt.FVf
        "A"))), (Kt.SVf "X"))), [],
        (derivRuleNC_rule_bw_inDC eqDec_formula f_Kt_log kt_log eqDec_structr
          f_Kt kt_str kt_DC []
          (premsRule eqDec_formula f_Kt_log kt_log eqDec_structr f_Kt kt_str
            KtRules.coq_Ssn)
          (conclRule eqDec_formula f_Kt_log kt_log eqDec_structr f_Kt kt_str
            KtRules.coq_Ssn)
          (seq_matchsub eqDec_formula f_Kt_log kt_log eqDec_structr f_Kt
            kt_str
            (conclRule eqDec_formula f_Kt_log kt_log eqDec_structr f_Kt
              kt_str KtRules.coq_Ssn) (Sequent ((Kt.Star (Kt.FSf phi)),
            (Kt.Star (Kt.FSf phi))))) (ForallT_cons ((Sequent ((Kt.Star
          (Kt.SVf "X")), (Kt.SVf "Y"))), [],
          (derivRuleNC_rule_bw_inDC eqDec_formula f_Kt_log kt_log
            eqDec_structr f_Kt kt_str kt_DC []
            (premsRule eqDec_formula f_Kt_log kt_log eqDec_structr f_Kt
              kt_str KtRules.coq_DSIl)
            (conclRule eqDec_formula f_Kt_log kt_log eqDec_structr f_Kt
              kt_str KtRules.coq_DSIl)
            (seq_matchsub eqDec_formula f_Kt_log kt_log eqDec_structr f_Kt
              kt_str
              (conclRule eqDec_formula f_Kt_log kt_log eqDec_structr f_Kt
                kt_str KtRules.coq_DSIl) (Sequent ((Kt.Star (Kt.Star (Kt.FSf
              phi))), (Kt.FSf phi)))) (ForallT_cons ((Sequent ((Kt.SVf "X"),
            (Kt.SVf "Y"))), [], iHA, ForallT_nil))), ForallT_nil))),
        ForallT_nil))), ForallT_nil))
  | Kt.Imp (phi, psi) ->
    let iHA1 = dernc_frefl phi in
    let iHA2 = dernc_frefl psi in
    derivRuleNC_rule_bw_inDC eqDec_formula f_Kt_log kt_log eqDec_structr f_Kt
      kt_str kt_DC []
      (premsRule eqDec_formula f_Kt_log kt_log eqDec_structr f_Kt kt_str
        KtRules.coq_Impr)
      (conclRule eqDec_formula f_Kt_log kt_log eqDec_structr f_Kt kt_str
        KtRules.coq_Impr)
      (seq_matchsub eqDec_formula f_Kt_log kt_log eqDec_structr f_Kt kt_str
        (conclRule eqDec_formula f_Kt_log kt_log eqDec_structr f_Kt kt_str
          KtRules.coq_Impr) (Sequent ((kt_str.fS (Kt.Imp (phi, psi))),
        (kt_str.fS (Kt.Imp (phi, psi)))))) (ForallT_cons ((Sequent ((Kt.Comma
      ((Kt.SVf "X"), (Kt.FSf (Kt.FVf "A")))), (Kt.FSf (Kt.FVf "B")))), [],
      (derivRuleNC_rule_bw_inDC eqDec_formula f_Kt_log kt_log eqDec_structr
        f_Kt kt_str kt_DC []
        (premsRule eqDec_formula f_Kt_log kt_log eqDec_structr f_Kt kt_str
          KtRules.coq_Comml)
        (conclRule eqDec_formula f_Kt_log kt_log eqDec_structr f_Kt kt_str
          KtRules.coq_Comml)
        (seq_matchsub eqDec_formula f_Kt_log kt_log eqDec_structr f_Kt kt_str
          (conclRule eqDec_formula f_Kt_log kt_log eqDec_structr f_Kt kt_str
            KtRules.coq_Comml) (Sequent ((Kt.Comma ((Kt.FSf (Kt.Imp (phi,
          psi))), (Kt.FSf phi))), (Kt.FSf psi)))) (ForallT_cons ((Sequent
        ((Kt.Comma ((Kt.SVf "X"), (Kt.SVf "Y"))), (Kt.SVf "Z"))), [],
        (derivRuleNC_rule_bw_inDC eqDec_formula f_Kt_log kt_log eqDec_structr
          f_Kt kt_str kt_DC []
          (premsRule eqDec_formula f_Kt_log kt_log eqDec_structr f_Kt kt_str
            KtRules.coq_Mrls)
          (conclRule eqDec_formula f_Kt_log kt_log eqDec_structr f_Kt kt_str
            KtRules.coq_Mrls)
          (seq_matchsub eqDec_formula f_Kt_log kt_log eqDec_structr f_Kt
            kt_str
            (conclRule eqDec_formula f_Kt_log kt_log eqDec_structr f_Kt
              kt_str KtRules.coq_Mrls) (Sequent ((Kt.Comma ((Kt.FSf phi),
            (Kt.FSf (Kt.Imp (phi, psi))))), (Kt.FSf psi)))) (ForallT_cons
          ((Sequent ((Kt.SVf "X"), (Kt.Comma ((Kt.Star (Kt.SVf "Y")), (Kt.SVf
          "Z"))))), [],
          (derivRuleNC_rule_bw_inDC eqDec_formula f_Kt_log kt_log
            eqDec_structr f_Kt kt_str kt_DC []
            (premsRule eqDec_formula f_Kt_log kt_log eqDec_structr f_Kt
              kt_str KtRules.coq_Impl)
            (conclRule eqDec_formula f_Kt_log kt_log eqDec_structr f_Kt
              kt_str KtRules.coq_Impl)
            (seq_matchsub eqDec_formula f_Kt_log kt_log eqDec_structr f_Kt
              kt_str
              (conclRule eqDec_formula f_Kt_log kt_log eqDec_structr f_Kt
                kt_str KtRules.coq_Impl) (Sequent ((Kt.FSf (Kt.Imp (phi,
              psi))), (Kt.Comma ((Kt.Star (Kt.FSf phi)), (Kt.FSf psi))))))
            (ForallT_cons ((Sequent ((Kt.SVf "X"), (Kt.FSf (Kt.FVf "A")))),
            ((Sequent ((Kt.FSf (Kt.FVf "B")), (Kt.SVf "Y")))::[]), iHA1,
            (ForallT_cons ((Sequent ((Kt.FSf (Kt.FVf "B")), (Kt.SVf "Y"))),
            [], iHA2, ForallT_nil))))), ForallT_nil))), ForallT_nil))),
      ForallT_nil))
  | Kt.Dis (phi, psi) ->
    let iHA1 = dernc_frefl phi in
    let iHA2 = dernc_frefl psi in
    derivRuleNC_rule_bw_inDC eqDec_formula f_Kt_log kt_log eqDec_structr f_Kt
      kt_str kt_DC []
      (premsRule eqDec_formula f_Kt_log kt_log eqDec_structr f_Kt kt_str
        KtRules.coq_Disr)
      (conclRule eqDec_formula f_Kt_log kt_log eqDec_structr f_Kt kt_str
        KtRules.coq_Disr)
      (seq_matchsub eqDec_formula f_Kt_log kt_log eqDec_structr f_Kt kt_str
        (conclRule eqDec_formula f_Kt_log kt_log eqDec_structr f_Kt kt_str
          KtRules.coq_Disr) (Sequent ((kt_str.fS (Kt.Dis (phi, psi))),
        (kt_str.fS (Kt.Dis (phi, psi)))))) (ForallT_cons ((Sequent ((Kt.SVf
      "X"), (Kt.Comma ((Kt.FSf (Kt.FVf "A")), (Kt.FSf (Kt.FVf "B")))))), [],
      (derivRuleNC_rule_bw_inDC eqDec_formula f_Kt_log kt_log eqDec_structr
        f_Kt kt_str kt_DC []
        (premsRule eqDec_formula f_Kt_log kt_log eqDec_structr f_Kt kt_str
          KtRules.coq_Disl)
        (conclRule eqDec_formula f_Kt_log kt_log eqDec_structr f_Kt kt_str
          KtRules.coq_Disl)
        (seq_matchsub eqDec_formula f_Kt_log kt_log eqDec_structr f_Kt kt_str
          (conclRule eqDec_formula f_Kt_log kt_log eqDec_structr f_Kt kt_str
            KtRules.coq_Disl) (Sequent ((Kt.FSf (Kt.Dis (phi, psi))),
          (Kt.Comma ((Kt.FSf phi), (Kt.FSf psi)))))) (ForallT_cons ((Sequent
        ((Kt.FSf (Kt.FVf "A")), (Kt.SVf "X"))), ((Sequent ((Kt.FSf (Kt.FVf
        "B")), (Kt.SVf "Y")))::[]), iHA1, (ForallT_cons ((Sequent ((Kt.FSf
        (Kt.FVf "B")), (Kt.SVf "Y"))), [], iHA2, ForallT_nil))))),
      ForallT_nil))
  | Kt.Con (phi, psi) ->
    let iHA1 = dernc_frefl phi in
    let iHA2 = dernc_frefl psi in
    derivRuleNC_rule_bw_inDC eqDec_formula f_Kt_log kt_log eqDec_structr f_Kt
      kt_str kt_DC []
      (premsRule eqDec_formula f_Kt_log kt_log eqDec_structr f_Kt kt_str
        KtRules.coq_Conl)
      (conclRule eqDec_formula f_Kt_log kt_log eqDec_structr f_Kt kt_str
        KtRules.coq_Conl)
      (seq_matchsub eqDec_formula f_Kt_log kt_log eqDec_structr f_Kt kt_str
        (conclRule eqDec_formula f_Kt_log kt_log eqDec_structr f_Kt kt_str
          KtRules.coq_Conl) (Sequent ((kt_str.fS (Kt.Con (phi, psi))),
        (kt_str.fS (Kt.Con (phi, psi)))))) (ForallT_cons ((Sequent ((Kt.Comma
      ((Kt.FSf (Kt.FVf "A")), (Kt.FSf (Kt.FVf "B")))), (Kt.SVf "X"))), [],
      (derivRuleNC_rule_bw_inDC eqDec_formula f_Kt_log kt_log eqDec_structr
        f_Kt kt_str kt_DC []
        (premsRule eqDec_formula f_Kt_log kt_log eqDec_structr f_Kt kt_str
          KtRules.coq_Conr)
        (conclRule eqDec_formula f_Kt_log kt_log eqDec_structr f_Kt kt_str
          KtRules.coq_Conr)
        (seq_matchsub eqDec_formula f_Kt_log kt_log eqDec_structr f_Kt kt_str
          (conclRule eqDec_formula f_Kt_log kt_log eqDec_structr f_Kt kt_str
            KtRules.coq_Conr) (Sequent ((Kt.Comma ((Kt.FSf phi), (Kt.FSf
          psi))), (Kt.FSf (Kt.Con (phi, psi)))))) (ForallT_cons ((Sequent
        ((Kt.SVf "X"), (Kt.FSf (Kt.FVf "A")))), ((Sequent ((Kt.SVf "Y"),
        (Kt.FSf (Kt.FVf "B"))))::[]), iHA1, (ForallT_cons ((Sequent ((Kt.SVf
        "Y"), (Kt.FSf (Kt.FVf "B")))), [], iHA2, ForallT_nil))))),
      ForallT_nil))
  | Kt.Boxn phi ->
    let iHA = dernc_frefl phi in
    derivRuleNC_rule_bw_inDC eqDec_formula f_Kt_log kt_log eqDec_structr f_Kt
      kt_str kt_DC []
      (premsRule eqDec_formula f_Kt_log kt_log eqDec_structr f_Kt kt_str
        KtRules.coq_Boxnr)
      (conclRule eqDec_formula f_Kt_log kt_log eqDec_structr f_Kt kt_str
        KtRules.coq_Boxnr)
      (seq_matchsub eqDec_formula f_Kt_log kt_log eqDec_structr f_Kt kt_str
        (conclRule eqDec_formula f_Kt_log kt_log eqDec_structr f_Kt kt_str
          KtRules.coq_Boxnr) (Sequent ((kt_str.fS (Kt.Boxn phi)),
        (kt_str.fS (Kt.Boxn phi))))) (ForallT_cons ((Sequent ((Kt.BCirc
      (Kt.SVf "X")), (Kt.FSf (Kt.FVf "A")))), [],
      (derivRuleNC_rule_bw_inDC eqDec_formula f_Kt_log kt_log eqDec_structr
        f_Kt kt_str kt_DC []
        (premsRule eqDec_formula f_Kt_log kt_log eqDec_structr f_Kt kt_str
          KtRules.coq_Scr)
        (conclRule eqDec_formula f_Kt_log kt_log eqDec_structr f_Kt kt_str
          KtRules.coq_Scr)
        (seq_matchsub eqDec_formula f_Kt_log kt_log eqDec_structr f_Kt kt_str
          (conclRule eqDec_formula f_Kt_log kt_log eqDec_structr f_Kt kt_str
            KtRules.coq_Scr) (Sequent ((Kt.BCirc (Kt.FSf (Kt.Boxn phi))),
          (Kt.FSf phi)))) (ForallT_cons ((Sequent ((Kt.SVf "X"), (Kt.BCirc
        (Kt.SVf "Y")))), [],
        (derivRuleNC_rule_bw_inDC eqDec_formula f_Kt_log kt_log eqDec_structr
          f_Kt kt_str kt_DC []
          (premsRule eqDec_formula f_Kt_log kt_log eqDec_structr f_Kt kt_str
            KtRules.coq_Boxnl)
          (conclRule eqDec_formula f_Kt_log kt_log eqDec_structr f_Kt kt_str
            KtRules.coq_Boxnl)
          (seq_matchsub eqDec_formula f_Kt_log kt_log eqDec_structr f_Kt
            kt_str
            (conclRule eqDec_formula f_Kt_log kt_log eqDec_structr f_Kt
              kt_str KtRules.coq_Boxnl) (Sequent ((Kt.FSf (Kt.Boxn phi)),
            (Kt.BCirc (Kt.FSf phi))))) (ForallT_cons ((Sequent ((Kt.FSf
          (Kt.FVf "A")), (Kt.SVf "X"))), [], iHA, ForallT_nil))),
        ForallT_nil))), ForallT_nil))
  | Kt.Dian phi ->
    let iHA = dernc_frefl phi in
    derivRuleNC_rule_bw_inDC eqDec_formula f_Kt_log kt_log eqDec_structr f_Kt
      kt_str kt_DC []
      (premsRule eqDec_formula f_Kt_log kt_log eqDec_structr f_Kt kt_str
        KtRules.coq_Dianl)
      (conclRule eqDec_formula f_Kt_log kt_log eqDec_structr f_Kt kt_str
        KtRules.coq_Dianl)
      (seq_matchsub eqDec_formula f_Kt_log kt_log eqDec_structr f_Kt kt_str
        (conclRule eqDec_formula f_Kt_log kt_log eqDec_structr f_Kt kt_str
          KtRules.coq_Dianl) (Sequent ((kt_str.fS (Kt.Dian phi)),
        (kt_str.fS (Kt.Dian phi))))) (ForallT_cons ((Sequent ((Kt.Star
      (Kt.BCirc (Kt.Star (Kt.FSf (Kt.FVf "A"))))), (Kt.SVf "X"))), [],
      (derivRuleNC_rule_bw_inDC eqDec_formula f_Kt_log kt_log eqDec_structr
        f_Kt kt_str kt_DC []
        (premsRule eqDec_formula f_Kt_log kt_log eqDec_structr f_Kt kt_str
          KtRules.coq_Dianr)
        (conclRule eqDec_formula f_Kt_log kt_log eqDec_structr f_Kt kt_str
          KtRules.coq_Dianr)
        (seq_matchsub eqDec_formula f_Kt_log kt_log eqDec_structr f_Kt kt_str
          (conclRule eqDec_formula f_Kt_log kt_log eqDec_structr f_Kt kt_str
            KtRules.coq_Dianr) (Sequent ((Kt.Star (Kt.BCirc (Kt.Star (Kt.FSf
          phi)))), (Kt.FSf (Kt.Dian phi))))) (ForallT_cons ((Sequent ((Kt.SVf
        "X"), (Kt.FSf (Kt.FVf "A")))), [], iHA, ForallT_nil))), ForallT_nil))
  | Kt.Boxp phi ->
    let iHA = dernc_frefl phi in
    derivRuleNC_rule_bw_inDC eqDec_formula f_Kt_log kt_log eqDec_structr f_Kt
      kt_str kt_DC []
      (premsRule eqDec_formula f_Kt_log kt_log eqDec_structr f_Kt kt_str
        KtRules.coq_Boxpr)
      (conclRule eqDec_formula f_Kt_log kt_log eqDec_structr f_Kt kt_str
        KtRules.coq_Boxpr)
      (seq_matchsub eqDec_formula f_Kt_log kt_log eqDec_structr f_Kt kt_str
        (conclRule eqDec_formula f_Kt_log kt_log eqDec_structr f_Kt kt_str
          KtRules.coq_Boxpr) (Sequent ((kt_str.fS (Kt.Boxp phi)),
        (kt_str.fS (Kt.Boxp phi))))) (ForallT_cons ((Sequent ((Kt.SVf "X"),
      (Kt.Star (Kt.BCirc (Kt.Star (Kt.FSf (Kt.FVf "A"))))))), [],
      (derivRuleNC_rule_bw_inDC eqDec_formula f_Kt_log kt_log eqDec_structr
        f_Kt kt_str kt_DC []
        (premsRule eqDec_formula f_Kt_log kt_log eqDec_structr f_Kt kt_str
          KtRules.coq_Boxpl)
        (conclRule eqDec_formula f_Kt_log kt_log eqDec_structr f_Kt kt_str
          KtRules.coq_Boxpl)
        (seq_matchsub eqDec_formula f_Kt_log kt_log eqDec_structr f_Kt kt_str
          (conclRule eqDec_formula f_Kt_log kt_log eqDec_structr f_Kt kt_str
            KtRules.coq_Boxpl) (Sequent ((Kt.FSf (Kt.Boxp phi)), (Kt.Star
          (Kt.BCirc (Kt.Star (Kt.FSf phi))))))) (ForallT_cons ((Sequent
        ((Kt.FSf (Kt.FVf "A")), (Kt.SVf "X"))), [], iHA, ForallT_nil))),
      ForallT_nil))
  | Kt.Diap phi ->
    let iHA = dernc_frefl phi in
    derivRuleNC_rule_bw_inDC eqDec_formula f_Kt_log kt_log eqDec_structr f_Kt
      kt_str kt_DC []
      (premsRule eqDec_formula f_Kt_log kt_log eqDec_structr f_Kt kt_str
        KtRules.coq_Diapl)
      (conclRule eqDec_formula f_Kt_log kt_log eqDec_structr f_Kt kt_str
        KtRules.coq_Diapl)
      (seq_matchsub eqDec_formula f_Kt_log kt_log eqDec_structr f_Kt kt_str
        (conclRule eqDec_formula f_Kt_log kt_log eqDec_structr f_Kt kt_str
          KtRules.coq_Diapl) (Sequent ((kt_str.fS (Kt.Diap phi)),
        (kt_str.fS (Kt.Diap phi))))) (ForallT_cons ((Sequent ((Kt.FSf (Kt.FVf
      "A")), (Kt.BCirc (Kt.SVf "X")))), [],
      (derivRuleNC_rule_bw_inDC eqDec_formula f_Kt_log kt_log eqDec_structr
        f_Kt kt_str kt_DC []
        (premsRule eqDec_formula f_Kt_log kt_log eqDec_structr f_Kt kt_str
          KtRules.coq_Scl)
        (conclRule eqDec_formula f_Kt_log kt_log eqDec_structr f_Kt kt_str
          KtRules.coq_Scl)
        (seq_matchsub eqDec_formula f_Kt_log kt_log eqDec_structr f_Kt kt_str
          (conclRule eqDec_formula f_Kt_log kt_log eqDec_structr f_Kt kt_str
            KtRules.coq_Scl) (Sequent ((Kt.FSf phi), (Kt.BCirc (Kt.FSf
          (Kt.Diap phi)))))) (ForallT_cons ((Sequent ((Kt.BCirc (Kt.SVf
        "X")), (Kt.SVf "Y"))), [],
        (derivRuleNC_rule_bw_inDC eqDec_formula f_Kt_log kt_log eqDec_structr
          f_Kt kt_str kt_DC []
          (premsRule eqDec_formula f_Kt_log kt_log eqDec_structr f_Kt kt_str
            KtRules.coq_Diapr)
          (conclRule eqDec_formula f_Kt_log kt_log eqDec_structr f_Kt kt_str
            KtRules.coq_Diapr)
          (seq_matchsub eqDec_formula f_Kt_log kt_log eqDec_structr f_Kt
            kt_str
            (conclRule eqDec_formula f_Kt_log kt_log eqDec_structr f_Kt
              kt_str KtRules.coq_Diapr) (Sequent ((Kt.BCirc (Kt.FSf phi)),
            (Kt.FSf (Kt.Diap phi))))) (ForallT_cons ((Sequent ((Kt.SVf "X"),
          (Kt.FSf (Kt.FVf "A")))), [], iHA, ForallT_nil))), ForallT_nil))),
      ForallT_nil))
 end

module KtBelnap =
 struct
  (** val coq_C8_Neg :
      Kt.structr -> Kt.structr -> Kt.formula -> (Kt.formula, Kt.structr)
      dertree list -> (Kt.formula, Kt.structr) dertree **)

  let coq_C8_Neg x y a ld =
    c8_case_alt_imp_C8_case eqDec_formula f_Kt_log kt_log eqDec_structr f_Kt
      kt_str kt_DC x y ((Sequent (x, (Kt.Star (Kt.FSf a))))::((Sequent
      ((Kt.Star (Kt.FSf a)), y))::[])) (fun hders ->
      let x0 = fun dC cs ->
        let _,x0 =
          forallT_deriv_cofseqs_iff eqDec_formula f_Kt_log kt_log
            eqDec_structr f_Kt kt_str dC cs
        in
        x0
      in
      let hders0 =
        x0 kt_DC ((Sequent (x, (Kt.Star (Kt.FSf a))))::((Sequent ((Kt.Star
          (Kt.FSf a)), y))::[])) hders
      in
      let hders1 =
        forallT_inv (Sequent (x, (Kt.Star (Kt.FSf a)))) ((Sequent ((Kt.Star
          (Kt.FSf a)), y))::[]) hders0
      in
      let hders2 =
        forallT_inv_tail (Sequent (x, (Kt.Star (Kt.FSf a)))) ((Sequent
          ((Kt.Star (Kt.FSf a)), y))::[]) hders0
      in
      let hders3 = forallT_inv (Sequent ((Kt.Star (Kt.FSf a)), y)) [] hders2
      in
      deriv_cofseq_rule_bw_InstNC eqDec_formula f_Kt_log kt_log eqDec_structr
        f_Kt kt_str kt_DC
        (premsRule eqDec_formula f_Kt_log kt_log eqDec_structr f_Kt kt_str
          KtRules.coq_Sss)
        (conclRule eqDec_formula f_Kt_log kt_log eqDec_structr f_Kt kt_str
          KtRules.coq_Sss)
        (seq_matchsub eqDec_formula f_Kt_log kt_log eqDec_structr f_Kt kt_str
          (conclRule eqDec_formula f_Kt_log kt_log eqDec_structr f_Kt kt_str
            KtRules.coq_Sss) (Sequent (x, y))) KtDeriv.dernc_Sss
        (ForallT_cons
        ((seqSubst eqDec_formula f_Kt_log kt_log eqDec_structr f_Kt kt_str
           (seq_matchsub eqDec_formula f_Kt_log kt_log eqDec_structr f_Kt
             kt_str
             (conclRule eqDec_formula f_Kt_log kt_log eqDec_structr f_Kt
               kt_str KtRules.coq_Sss) (Sequent (x, y))) (Sequent ((Kt.Star
           (Kt.SVf "X")), (Kt.Star (Kt.SVf "Y"))))), [],
        (deriv_cofseq_rule_bw_inDC eqDec_formula f_Kt_log kt_log
          eqDec_structr f_Kt kt_str kt_DC
          (premsRule eqDec_formula f_Kt_log kt_log eqDec_structr f_Kt kt_str
            (cUT eqDec_formula f_Kt_log kt_log eqDec_structr f_Kt kt_str))
          (conclRule eqDec_formula f_Kt_log kt_log eqDec_structr f_Kt kt_str
            (cUT eqDec_formula f_Kt_log kt_log eqDec_structr f_Kt kt_str))
          (cUT_spec eqDec_formula f_Kt_log kt_log eqDec_structr f_Kt kt_str a
            (Kt.Star y) (Kt.Star x))
          (forallT_deriv_cofseqs eqDec_formula f_Kt_log kt_log eqDec_structr
            f_Kt kt_str kt_DC ((Sequent ((Kt.Star y), (Kt.FSf a)))::((Sequent
            ((Kt.FSf a), (Kt.Star x)))::[])) (ForallT_cons ((Sequent
            ((Kt.Star y), (Kt.FSf a))), ((Sequent ((Kt.FSf a), (Kt.Star
            x)))::[]),
            (deriv_cofseq_rule_bw_inDC eqDec_formula f_Kt_log kt_log
              eqDec_structr f_Kt kt_str kt_DC
              (premsRule eqDec_formula f_Kt_log kt_log eqDec_structr f_Kt
                kt_str KtRules.coq_Ssn)
              (conclRule eqDec_formula f_Kt_log kt_log eqDec_structr f_Kt
                kt_str KtRules.coq_Ssn)
              (seq_matchsub eqDec_formula f_Kt_log kt_log eqDec_structr f_Kt
                kt_str
                (conclRule eqDec_formula f_Kt_log kt_log eqDec_structr f_Kt
                  kt_str KtRules.coq_Ssn) (Sequent ((Kt.Star y), (Kt.FSf a))))
              (forallT_deriv_cofseqs eqDec_formula f_Kt_log kt_log
                eqDec_structr f_Kt kt_str kt_DC
                (map
                  (seqSubst eqDec_formula f_Kt_log kt_log eqDec_structr f_Kt
                    kt_str
                    (seq_matchsub eqDec_formula f_Kt_log kt_log eqDec_structr
                      f_Kt kt_str
                      (conclRule eqDec_formula f_Kt_log kt_log eqDec_structr
                        f_Kt kt_str KtRules.coq_Ssn) (Sequent ((Kt.Star y),
                      (Kt.FSf a)))))
                  (premsRule eqDec_formula f_Kt_log kt_log eqDec_structr f_Kt
                    kt_str KtRules.coq_Ssn)) (ForallT_cons
                ((seqSubst eqDec_formula f_Kt_log kt_log eqDec_structr f_Kt
                   kt_str
                   (seq_matchsub eqDec_formula f_Kt_log kt_log eqDec_structr
                     f_Kt kt_str
                     (conclRule eqDec_formula f_Kt_log kt_log eqDec_structr
                       f_Kt kt_str KtRules.coq_Ssn) (Sequent ((Kt.Star y),
                     (Kt.FSf a)))) (Sequent ((Kt.Star (Kt.SVf "X")), (Kt.SVf
                   "Y")))), [], hders3, ForallT_nil)))), (ForallT_cons
            ((Sequent ((Kt.FSf a), (Kt.Star x))), [],
            (deriv_cofseq_rule_bw_inDC eqDec_formula f_Kt_log kt_log
              eqDec_structr f_Kt kt_str kt_DC
              (premsRule eqDec_formula f_Kt_log kt_log eqDec_structr f_Kt
                kt_str KtRules.coq_Sns)
              (conclRule eqDec_formula f_Kt_log kt_log eqDec_structr f_Kt
                kt_str KtRules.coq_Sns)
              (seq_matchsub eqDec_formula f_Kt_log kt_log eqDec_structr f_Kt
                kt_str
                (conclRule eqDec_formula f_Kt_log kt_log eqDec_structr f_Kt
                  kt_str KtRules.coq_Sns) (Sequent ((Kt.FSf a), (Kt.Star x))))
              (forallT_deriv_cofseqs eqDec_formula f_Kt_log kt_log
                eqDec_structr f_Kt kt_str kt_DC
                (map
                  (seqSubst eqDec_formula f_Kt_log kt_log eqDec_structr f_Kt
                    kt_str
                    (seq_matchsub eqDec_formula f_Kt_log kt_log eqDec_structr
                      f_Kt kt_str
                      (conclRule eqDec_formula f_Kt_log kt_log eqDec_structr
                        f_Kt kt_str KtRules.coq_Sns) (Sequent ((Kt.FSf a),
                      (Kt.Star x)))))
                  (premsRule eqDec_formula f_Kt_log kt_log eqDec_structr f_Kt
                    kt_str KtRules.coq_Sns)) (ForallT_cons
                ((seqSubst eqDec_formula f_Kt_log kt_log eqDec_structr f_Kt
                   kt_str
                   (seq_matchsub eqDec_formula f_Kt_log kt_log eqDec_structr
                     f_Kt kt_str
                     (conclRule eqDec_formula f_Kt_log kt_log eqDec_structr
                       f_Kt kt_str KtRules.coq_Sns) (Sequent ((Kt.FSf a),
                     (Kt.Star x)))) (Sequent ((Kt.SVf "X"), (Kt.Star (Kt.SVf
                   "Y"))))), [], hders1, ForallT_nil)))), ForallT_nil)))))),
        ForallT_nil))) ld

  (** val coq_C8_Con :
      Kt.structr -> Kt.structr -> Kt.structr -> Kt.formula -> Kt.formula ->
      (Kt.formula, Kt.structr) dertree list -> (Kt.formula, Kt.structr)
      dertree **)

  let coq_C8_Con x y z a b ld =
    c8_case_alt_imp_C8_case eqDec_formula f_Kt_log kt_log eqDec_structr f_Kt
      kt_str kt_DC (Kt.Comma (x, y)) z ((Sequent (x, (Kt.FSf a)))::((Sequent
      (y, (Kt.FSf b)))::((Sequent ((Kt.Comma ((Kt.FSf a), (Kt.FSf b))),
      z))::[]))) (fun hders ->
      let x0 = fun dC cs ->
        let _,x0 =
          forallT_deriv_cofseqs_iff eqDec_formula f_Kt_log kt_log
            eqDec_structr f_Kt kt_str dC cs
        in
        x0
      in
      let hders0 =
        x0 kt_DC ((Sequent (x, (Kt.FSf a)))::((Sequent (y, (Kt.FSf
          b)))::((Sequent ((Kt.Comma ((Kt.FSf a), (Kt.FSf b))), z))::[])))
          hders
      in
      let hders1 =
        forallT_inv (Sequent (x, (Kt.FSf a))) ((Sequent (y, (Kt.FSf
          b)))::((Sequent ((Kt.Comma ((Kt.FSf a), (Kt.FSf b))), z))::[]))
          hders0
      in
      let hders2 =
        forallT_inv_tail (Sequent (x, (Kt.FSf a))) ((Sequent (y, (Kt.FSf
          b)))::((Sequent ((Kt.Comma ((Kt.FSf a), (Kt.FSf b))), z))::[]))
          hders0
      in
      let hders3 =
        forallT_inv (Sequent (y, (Kt.FSf b))) ((Sequent ((Kt.Comma ((Kt.FSf
          a), (Kt.FSf b))), z))::[]) hders2
      in
      let hders4 =
        forallT_inv_tail (Sequent (y, (Kt.FSf b))) ((Sequent ((Kt.Comma
          ((Kt.FSf a), (Kt.FSf b))), z))::[]) hders2
      in
      let hders5 =
        forallT_inv (Sequent ((Kt.Comma ((Kt.FSf a), (Kt.FSf b))), z)) []
          hders4
      in
      deriv_cofseq_rule_bw_inDC eqDec_formula f_Kt_log kt_log eqDec_structr
        f_Kt kt_str kt_DC
        (premsRule eqDec_formula f_Kt_log kt_log eqDec_structr f_Kt kt_str
          KtRules.coq_Mrrs)
        (conclRule eqDec_formula f_Kt_log kt_log eqDec_structr f_Kt kt_str
          KtRules.coq_Mrrs)
        (seq_matchsub eqDec_formula f_Kt_log kt_log eqDec_structr f_Kt kt_str
          (conclRule eqDec_formula f_Kt_log kt_log eqDec_structr f_Kt kt_str
            KtRules.coq_Mrrs) (Sequent ((Kt.Comma (x, y)), z)))
        (forallT_deriv_cofseqs eqDec_formula f_Kt_log kt_log eqDec_structr
          f_Kt kt_str kt_DC
          (map
            (seqSubst eqDec_formula f_Kt_log kt_log eqDec_structr f_Kt kt_str
              (seq_matchsub eqDec_formula f_Kt_log kt_log eqDec_structr f_Kt
                kt_str
                (conclRule eqDec_formula f_Kt_log kt_log eqDec_structr f_Kt
                  kt_str KtRules.coq_Mrrs) (Sequent ((Kt.Comma (x, y)), z))))
            (premsRule eqDec_formula f_Kt_log kt_log eqDec_structr f_Kt
              kt_str KtRules.coq_Mrrs)) (ForallT_cons
          ((seqSubst eqDec_formula f_Kt_log kt_log eqDec_structr f_Kt kt_str
             (seq_matchsub eqDec_formula f_Kt_log kt_log eqDec_structr f_Kt
               kt_str
               (conclRule eqDec_formula f_Kt_log kt_log eqDec_structr f_Kt
                 kt_str KtRules.coq_Mrrs) (Sequent ((Kt.Comma (x, y)), z)))
             (Sequent ((Kt.SVf "X"), (Kt.Comma ((Kt.SVf "Y"), (Kt.Star
             (Kt.SVf "Z"))))))), [],
          (deriv_cofseq_rule_bw_inDC eqDec_formula f_Kt_log kt_log
            eqDec_structr f_Kt kt_str kt_DC
            (premsRule eqDec_formula f_Kt_log kt_log eqDec_structr f_Kt
              kt_str
              (cUT eqDec_formula f_Kt_log kt_log eqDec_structr f_Kt kt_str))
            (conclRule eqDec_formula f_Kt_log kt_log eqDec_structr f_Kt
              kt_str
              (cUT eqDec_formula f_Kt_log kt_log eqDec_structr f_Kt kt_str))
            (cUT_spec eqDec_formula f_Kt_log kt_log eqDec_structr f_Kt kt_str
              a x (Kt.Comma (z, (Kt.Star y))))
            (forallT_deriv_cofseqs eqDec_formula f_Kt_log kt_log
              eqDec_structr f_Kt kt_str kt_DC ((Sequent (x, (Kt.FSf
              a)))::((Sequent ((Kt.FSf a), (Kt.Comma (z, (Kt.Star
              y)))))::[])) (ForallT_cons ((Sequent (x, (Kt.FSf a))),
              ((Sequent ((Kt.FSf a), (Kt.Comma (z, (Kt.Star y)))))::[]),
              hders1, (ForallT_cons ((Sequent ((Kt.FSf a), (Kt.Comma (z,
              (Kt.Star y))))), [],
              (deriv_cofseq_rule_bw_inDC eqDec_formula f_Kt_log kt_log
                eqDec_structr f_Kt kt_str kt_DC
                (premsRule eqDec_formula f_Kt_log kt_log eqDec_structr f_Kt
                  kt_str KtRules.coq_Mlrn)
                (conclRule eqDec_formula f_Kt_log kt_log eqDec_structr f_Kt
                  kt_str KtRules.coq_Mlrn)
                (seq_matchsub eqDec_formula f_Kt_log kt_log eqDec_structr
                  f_Kt kt_str
                  (conclRule eqDec_formula f_Kt_log kt_log eqDec_structr f_Kt
                    kt_str KtRules.coq_Mlrn) (Sequent ((Kt.FSf a), (Kt.Comma
                  (z, (Kt.Star y))))))
                (forallT_deriv_cofseqs eqDec_formula f_Kt_log kt_log
                  eqDec_structr f_Kt kt_str kt_DC
                  (map
                    (seqSubst eqDec_formula f_Kt_log kt_log eqDec_structr
                      f_Kt kt_str
                      (seq_matchsub eqDec_formula f_Kt_log kt_log
                        eqDec_structr f_Kt kt_str
                        (conclRule eqDec_formula f_Kt_log kt_log
                          eqDec_structr f_Kt kt_str KtRules.coq_Mlrn)
                        (Sequent ((Kt.FSf a), (Kt.Comma (z, (Kt.Star y)))))))
                    (premsRule eqDec_formula f_Kt_log kt_log eqDec_structr
                      f_Kt kt_str KtRules.coq_Mlrn)) (ForallT_cons
                  ((seqSubst eqDec_formula f_Kt_log kt_log eqDec_structr f_Kt
                     kt_str
                     (seq_matchsub eqDec_formula f_Kt_log kt_log
                       eqDec_structr f_Kt kt_str
                       (conclRule eqDec_formula f_Kt_log kt_log eqDec_structr
                         f_Kt kt_str KtRules.coq_Mlrn) (Sequent ((Kt.FSf a),
                       (Kt.Comma (z, (Kt.Star y)))))) (Sequent ((Kt.Comma
                     ((Kt.SVf "X"), (Kt.SVf "Y"))), (Kt.SVf "Z")))), [],
                  (deriv_cofseq_rule_bw_inDC eqDec_formula f_Kt_log kt_log
                    eqDec_structr f_Kt kt_str kt_DC
                    (premsRule eqDec_formula f_Kt_log kt_log eqDec_structr
                      f_Kt kt_str KtRules.coq_Mrls)
                    (conclRule eqDec_formula f_Kt_log kt_log eqDec_structr
                      f_Kt kt_str KtRules.coq_Mrls)
                    (seq_matchsub eqDec_formula f_Kt_log kt_log eqDec_structr
                      f_Kt kt_str
                      (conclRule eqDec_formula f_Kt_log kt_log eqDec_structr
                        f_Kt kt_str KtRules.coq_Mrls) (Sequent ((Kt.Comma
                      ((Kt.FSf a), y)), z)))
                    (forallT_deriv_cofseqs eqDec_formula f_Kt_log kt_log
                      eqDec_structr f_Kt kt_str kt_DC
                      (map
                        (seqSubst eqDec_formula f_Kt_log kt_log eqDec_structr
                          f_Kt kt_str
                          (seq_matchsub eqDec_formula f_Kt_log kt_log
                            eqDec_structr f_Kt kt_str
                            (conclRule eqDec_formula f_Kt_log kt_log
                              eqDec_structr f_Kt kt_str KtRules.coq_Mrls)
                            (Sequent ((Kt.Comma ((Kt.FSf a), y)), z))))
                        (premsRule eqDec_formula f_Kt_log kt_log
                          eqDec_structr f_Kt kt_str KtRules.coq_Mrls))
                      (ForallT_cons
                      ((seqSubst eqDec_formula f_Kt_log kt_log eqDec_structr
                         f_Kt kt_str
                         (seq_matchsub eqDec_formula f_Kt_log kt_log
                           eqDec_structr f_Kt kt_str
                           (conclRule eqDec_formula f_Kt_log kt_log
                             eqDec_structr f_Kt kt_str KtRules.coq_Mrls)
                           (Sequent ((Kt.Comma ((Kt.FSf a), y)), z)))
                         (Sequent ((Kt.SVf "X"), (Kt.Comma ((Kt.Star (Kt.SVf
                         "Y")), (Kt.SVf "Z")))))), [],
                      (deriv_cofseq_rule_bw_inDC eqDec_formula f_Kt_log
                        kt_log eqDec_structr f_Kt kt_str kt_DC
                        (premsRule eqDec_formula f_Kt_log kt_log
                          eqDec_structr f_Kt kt_str
                          (cUT eqDec_formula f_Kt_log kt_log eqDec_structr
                            f_Kt kt_str))
                        (conclRule eqDec_formula f_Kt_log kt_log
                          eqDec_structr f_Kt kt_str
                          (cUT eqDec_formula f_Kt_log kt_log eqDec_structr
                            f_Kt kt_str))
                        (cUT_spec eqDec_formula f_Kt_log kt_log eqDec_structr
                          f_Kt kt_str b y (Kt.Comma ((Kt.Star (Kt.FSf a)),
                          z)))
                        (forallT_deriv_cofseqs eqDec_formula f_Kt_log kt_log
                          eqDec_structr f_Kt kt_str kt_DC ((Sequent (y,
                          (Kt.FSf b)))::((Sequent ((Kt.FSf b), (Kt.Comma
                          ((Kt.Star (Kt.FSf a)), z))))::[])) (ForallT_cons
                          ((Sequent (y, (Kt.FSf b))), ((Sequent ((Kt.FSf b),
                          (Kt.Comma ((Kt.Star (Kt.FSf a)), z))))::[]),
                          hders3, (ForallT_cons ((Sequent ((Kt.FSf b),
                          (Kt.Comma ((Kt.Star (Kt.FSf a)), z)))), [],
                          (deriv_cofseq_rule_bw_inDC eqDec_formula f_Kt_log
                            kt_log eqDec_structr f_Kt kt_str kt_DC
                            (premsRule eqDec_formula f_Kt_log kt_log
                              eqDec_structr f_Kt kt_str KtRules.coq_Mlln)
                            (conclRule eqDec_formula f_Kt_log kt_log
                              eqDec_structr f_Kt kt_str KtRules.coq_Mlln)
                            (seq_matchsub eqDec_formula f_Kt_log kt_log
                              eqDec_structr f_Kt kt_str
                              (conclRule eqDec_formula f_Kt_log kt_log
                                eqDec_structr f_Kt kt_str KtRules.coq_Mlln)
                              (Sequent ((Kt.FSf b), (Kt.Comma ((Kt.Star
                              (Kt.FSf a)), z)))))
                            (forallT_deriv_cofseqs eqDec_formula f_Kt_log
                              kt_log eqDec_structr f_Kt kt_str kt_DC
                              (map
                                (seqSubst eqDec_formula f_Kt_log kt_log
                                  eqDec_structr f_Kt kt_str
                                  (seq_matchsub eqDec_formula f_Kt_log kt_log
                                    eqDec_structr f_Kt kt_str
                                    (conclRule eqDec_formula f_Kt_log kt_log
                                      eqDec_structr f_Kt kt_str
                                      KtRules.coq_Mlln) (Sequent ((Kt.FSf b),
                                    (Kt.Comma ((Kt.Star (Kt.FSf a)), z))))))
                                (premsRule eqDec_formula f_Kt_log kt_log
                                  eqDec_structr f_Kt kt_str KtRules.coq_Mlln))
                              (ForallT_cons
                              ((seqSubst eqDec_formula f_Kt_log kt_log
                                 eqDec_structr f_Kt kt_str
                                 (seq_matchsub eqDec_formula f_Kt_log kt_log
                                   eqDec_structr f_Kt kt_str
                                   (conclRule eqDec_formula f_Kt_log kt_log
                                     eqDec_structr f_Kt kt_str
                                     KtRules.coq_Mlln) (Sequent ((Kt.FSf b),
                                   (Kt.Comma ((Kt.Star (Kt.FSf a)), z)))))
                                 (Sequent ((Kt.Comma ((Kt.SVf "X"), (Kt.SVf
                                 "Y"))), (Kt.SVf "Z")))), [], hders5,
                              ForallT_nil)))), ForallT_nil)))))),
                      ForallT_nil)))), ForallT_nil)))), ForallT_nil)))))),
          ForallT_nil)))) ld

  (** val coq_C8_Dis :
      Kt.structr -> Kt.structr -> Kt.structr -> Kt.formula -> Kt.formula ->
      (Kt.formula, Kt.structr) dertree list -> (Kt.formula, Kt.structr)
      dertree **)

  let coq_C8_Dis x y z a b ld =
    c8_case_alt_imp_C8_case eqDec_formula f_Kt_log kt_log eqDec_structr f_Kt
      kt_str kt_DC x (Kt.Comma (y, z)) ((Sequent (x, (Kt.Comma ((Kt.FSf a),
      (Kt.FSf b)))))::((Sequent ((Kt.FSf a), y))::((Sequent ((Kt.FSf b),
      z))::[]))) (fun hders ->
      let x0 = fun dC cs ->
        let _,x0 =
          forallT_deriv_cofseqs_iff eqDec_formula f_Kt_log kt_log
            eqDec_structr f_Kt kt_str dC cs
        in
        x0
      in
      let hders0 =
        x0 kt_DC ((Sequent (x, (Kt.Comma ((Kt.FSf a), (Kt.FSf
          b)))))::((Sequent ((Kt.FSf a), y))::((Sequent ((Kt.FSf b),
          z))::[]))) hders
      in
      let hders1 =
        forallT_inv (Sequent (x, (Kt.Comma ((Kt.FSf a), (Kt.FSf b)))))
          ((Sequent ((Kt.FSf a), y))::((Sequent ((Kt.FSf b), z))::[])) hders0
      in
      let hders2 =
        forallT_inv_tail (Sequent (x, (Kt.Comma ((Kt.FSf a), (Kt.FSf b)))))
          ((Sequent ((Kt.FSf a), y))::((Sequent ((Kt.FSf b), z))::[])) hders0
      in
      let hders3 =
        forallT_inv (Sequent ((Kt.FSf a), y)) ((Sequent ((Kt.FSf b), z))::[])
          hders2
      in
      let hders4 =
        forallT_inv_tail (Sequent ((Kt.FSf a), y)) ((Sequent ((Kt.FSf b),
          z))::[]) hders2
      in
      let hders5 = forallT_inv (Sequent ((Kt.FSf b), z)) [] hders4 in
      deriv_cofseq_rule_bw_inDC eqDec_formula f_Kt_log kt_log eqDec_structr
        f_Kt kt_str kt_DC
        (premsRule eqDec_formula f_Kt_log kt_log eqDec_structr f_Kt kt_str
          KtRules.coq_Mlls)
        (conclRule eqDec_formula f_Kt_log kt_log eqDec_structr f_Kt kt_str
          KtRules.coq_Mlls)
        (seq_matchsub eqDec_formula f_Kt_log kt_log eqDec_structr f_Kt kt_str
          (conclRule eqDec_formula f_Kt_log kt_log eqDec_structr f_Kt kt_str
            KtRules.coq_Mlls) (Sequent (x, (Kt.Comma (y, z)))))
        (forallT_deriv_cofseqs eqDec_formula f_Kt_log kt_log eqDec_structr
          f_Kt kt_str kt_DC
          (map
            (seqSubst eqDec_formula f_Kt_log kt_log eqDec_structr f_Kt kt_str
              (seq_matchsub eqDec_formula f_Kt_log kt_log eqDec_structr f_Kt
                kt_str
                (conclRule eqDec_formula f_Kt_log kt_log eqDec_structr f_Kt
                  kt_str KtRules.coq_Mlls) (Sequent (x, (Kt.Comma (y, z))))))
            (premsRule eqDec_formula f_Kt_log kt_log eqDec_structr f_Kt
              kt_str KtRules.coq_Mlls)) (ForallT_cons
          ((seqSubst eqDec_formula f_Kt_log kt_log eqDec_structr f_Kt kt_str
             (seq_matchsub eqDec_formula f_Kt_log kt_log eqDec_structr f_Kt
               kt_str
               (conclRule eqDec_formula f_Kt_log kt_log eqDec_structr f_Kt
                 kt_str KtRules.coq_Mlls) (Sequent (x, (Kt.Comma (y, z)))))
             (Sequent ((Kt.Comma ((Kt.Star (Kt.SVf "X")), (Kt.SVf "Y"))),
             (Kt.SVf "Z")))), [],
          (deriv_cofseq_rule_bw_inDC eqDec_formula f_Kt_log kt_log
            eqDec_structr f_Kt kt_str kt_DC
            (premsRule eqDec_formula f_Kt_log kt_log eqDec_structr f_Kt
              kt_str
              (cUT eqDec_formula f_Kt_log kt_log eqDec_structr f_Kt kt_str))
            (conclRule eqDec_formula f_Kt_log kt_log eqDec_structr f_Kt
              kt_str
              (cUT eqDec_formula f_Kt_log kt_log eqDec_structr f_Kt kt_str))
            (cUT_spec eqDec_formula f_Kt_log kt_log eqDec_structr f_Kt kt_str
              b (Kt.Comma ((Kt.Star y), x)) z)
            (forallT_deriv_cofseqs eqDec_formula f_Kt_log kt_log
              eqDec_structr f_Kt kt_str kt_DC ((Sequent ((Kt.Comma ((Kt.Star
              y), x)), (Kt.FSf b)))::((Sequent ((Kt.FSf b), z))::[]))
              (ForallT_cons ((Sequent ((Kt.Comma ((Kt.Star y), x)), (Kt.FSf
              b))), ((Sequent ((Kt.FSf b), z))::[]),
              (deriv_cofseq_rule_bw_inDC eqDec_formula f_Kt_log kt_log
                eqDec_structr f_Kt kt_str kt_DC
                (premsRule eqDec_formula f_Kt_log kt_log eqDec_structr f_Kt
                  kt_str KtRules.coq_Mrln)
                (conclRule eqDec_formula f_Kt_log kt_log eqDec_structr f_Kt
                  kt_str KtRules.coq_Mrln)
                (seq_matchsub eqDec_formula f_Kt_log kt_log eqDec_structr
                  f_Kt kt_str
                  (conclRule eqDec_formula f_Kt_log kt_log eqDec_structr f_Kt
                    kt_str KtRules.coq_Mrln) (Sequent ((Kt.Comma ((Kt.Star
                  y), x)), (Kt.FSf b))))
                (forallT_deriv_cofseqs eqDec_formula f_Kt_log kt_log
                  eqDec_structr f_Kt kt_str kt_DC
                  (map
                    (seqSubst eqDec_formula f_Kt_log kt_log eqDec_structr
                      f_Kt kt_str
                      (seq_matchsub eqDec_formula f_Kt_log kt_log
                        eqDec_structr f_Kt kt_str
                        (conclRule eqDec_formula f_Kt_log kt_log
                          eqDec_structr f_Kt kt_str KtRules.coq_Mrln)
                        (Sequent ((Kt.Comma ((Kt.Star y), x)), (Kt.FSf b)))))
                    (premsRule eqDec_formula f_Kt_log kt_log eqDec_structr
                      f_Kt kt_str KtRules.coq_Mrln)) (ForallT_cons
                  ((seqSubst eqDec_formula f_Kt_log kt_log eqDec_structr f_Kt
                     kt_str
                     (seq_matchsub eqDec_formula f_Kt_log kt_log
                       eqDec_structr f_Kt kt_str
                       (conclRule eqDec_formula f_Kt_log kt_log eqDec_structr
                         f_Kt kt_str KtRules.coq_Mrln) (Sequent ((Kt.Comma
                       ((Kt.Star y), x)), (Kt.FSf b)))) (Sequent ((Kt.SVf
                     "X"), (Kt.Comma ((Kt.SVf "Y"), (Kt.SVf "Z")))))), [],
                  (deriv_cofseq_rule_bw_inDC eqDec_formula f_Kt_log kt_log
                    eqDec_structr f_Kt kt_str kt_DC
                    (premsRule eqDec_formula f_Kt_log kt_log eqDec_structr
                      f_Kt kt_str KtRules.coq_Mlrs)
                    (conclRule eqDec_formula f_Kt_log kt_log eqDec_structr
                      f_Kt kt_str KtRules.coq_Mlrs)
                    (seq_matchsub eqDec_formula f_Kt_log kt_log eqDec_structr
                      f_Kt kt_str
                      (conclRule eqDec_formula f_Kt_log kt_log eqDec_structr
                        f_Kt kt_str KtRules.coq_Mlrs) (Sequent (x, (Kt.Comma
                      (y, (Kt.FSf b))))))
                    (forallT_deriv_cofseqs eqDec_formula f_Kt_log kt_log
                      eqDec_structr f_Kt kt_str kt_DC
                      (map
                        (seqSubst eqDec_formula f_Kt_log kt_log eqDec_structr
                          f_Kt kt_str
                          (seq_matchsub eqDec_formula f_Kt_log kt_log
                            eqDec_structr f_Kt kt_str
                            (conclRule eqDec_formula f_Kt_log kt_log
                              eqDec_structr f_Kt kt_str KtRules.coq_Mlrs)
                            (Sequent (x, (Kt.Comma (y, (Kt.FSf b)))))))
                        (premsRule eqDec_formula f_Kt_log kt_log
                          eqDec_structr f_Kt kt_str KtRules.coq_Mlrs))
                      (ForallT_cons
                      ((seqSubst eqDec_formula f_Kt_log kt_log eqDec_structr
                         f_Kt kt_str
                         (seq_matchsub eqDec_formula f_Kt_log kt_log
                           eqDec_structr f_Kt kt_str
                           (conclRule eqDec_formula f_Kt_log kt_log
                             eqDec_structr f_Kt kt_str KtRules.coq_Mlrs)
                           (Sequent (x, (Kt.Comma (y, (Kt.FSf b))))))
                         (Sequent ((Kt.Comma ((Kt.SVf "X"), (Kt.Star (Kt.SVf
                         "Y")))), (Kt.SVf "Z")))), [],
                      (deriv_cofseq_rule_bw_inDC eqDec_formula f_Kt_log
                        kt_log eqDec_structr f_Kt kt_str kt_DC
                        (premsRule eqDec_formula f_Kt_log kt_log
                          eqDec_structr f_Kt kt_str
                          (cUT eqDec_formula f_Kt_log kt_log eqDec_structr
                            f_Kt kt_str))
                        (conclRule eqDec_formula f_Kt_log kt_log
                          eqDec_structr f_Kt kt_str
                          (cUT eqDec_formula f_Kt_log kt_log eqDec_structr
                            f_Kt kt_str))
                        (cUT_spec eqDec_formula f_Kt_log kt_log eqDec_structr
                          f_Kt kt_str a (Kt.Comma (x, (Kt.Star (Kt.FSf b))))
                          y)
                        (forallT_deriv_cofseqs eqDec_formula f_Kt_log kt_log
                          eqDec_structr f_Kt kt_str kt_DC ((Sequent
                          ((Kt.Comma (x, (Kt.Star (Kt.FSf b)))), (Kt.FSf
                          a)))::((Sequent ((Kt.FSf a), y))::[]))
                          (ForallT_cons ((Sequent ((Kt.Comma (x, (Kt.Star
                          (Kt.FSf b)))), (Kt.FSf a))), ((Sequent ((Kt.FSf a),
                          y))::[]),
                          (deriv_cofseq_rule_bw_inDC eqDec_formula f_Kt_log
                            kt_log eqDec_structr f_Kt kt_str kt_DC
                            (premsRule eqDec_formula f_Kt_log kt_log
                              eqDec_structr f_Kt kt_str KtRules.coq_Mrrn)
                            (conclRule eqDec_formula f_Kt_log kt_log
                              eqDec_structr f_Kt kt_str KtRules.coq_Mrrn)
                            (seq_matchsub eqDec_formula f_Kt_log kt_log
                              eqDec_structr f_Kt kt_str
                              (conclRule eqDec_formula f_Kt_log kt_log
                                eqDec_structr f_Kt kt_str KtRules.coq_Mrrn)
                              (Sequent ((Kt.Comma (x, (Kt.Star (Kt.FSf b)))),
                              (Kt.FSf a))))
                            (forallT_deriv_cofseqs eqDec_formula f_Kt_log
                              kt_log eqDec_structr f_Kt kt_str kt_DC
                              (map
                                (seqSubst eqDec_formula f_Kt_log kt_log
                                  eqDec_structr f_Kt kt_str
                                  (seq_matchsub eqDec_formula f_Kt_log kt_log
                                    eqDec_structr f_Kt kt_str
                                    (conclRule eqDec_formula f_Kt_log kt_log
                                      eqDec_structr f_Kt kt_str
                                      KtRules.coq_Mrrn) (Sequent ((Kt.Comma
                                    (x, (Kt.Star (Kt.FSf b)))), (Kt.FSf a)))))
                                (premsRule eqDec_formula f_Kt_log kt_log
                                  eqDec_structr f_Kt kt_str KtRules.coq_Mrrn))
                              (ForallT_cons
                              ((seqSubst eqDec_formula f_Kt_log kt_log
                                 eqDec_structr f_Kt kt_str
                                 (seq_matchsub eqDec_formula f_Kt_log kt_log
                                   eqDec_structr f_Kt kt_str
                                   (conclRule eqDec_formula f_Kt_log kt_log
                                     eqDec_structr f_Kt kt_str
                                     KtRules.coq_Mrrn) (Sequent ((Kt.Comma
                                   (x, (Kt.Star (Kt.FSf b)))), (Kt.FSf a))))
                                 (Sequent ((Kt.SVf "X"), (Kt.Comma ((Kt.SVf
                                 "Y"), (Kt.SVf "Z")))))), [], hders1,
                              ForallT_nil)))), (ForallT_cons ((Sequent
                          ((Kt.FSf a), y)), [], hders3, ForallT_nil)))))),
                      ForallT_nil)))), ForallT_nil)))), (ForallT_cons
              ((Sequent ((Kt.FSf b), z)), [], hders5, ForallT_nil)))))),
          ForallT_nil)))) ld

  (** val coq_C8_Imp :
      Kt.structr -> Kt.structr -> Kt.structr -> Kt.formula -> Kt.formula ->
      (Kt.formula, Kt.structr) dertree list -> (Kt.formula, Kt.structr)
      dertree **)

  let coq_C8_Imp x y z a b ld =
    c8_case_alt_imp_C8_case eqDec_formula f_Kt_log kt_log eqDec_structr f_Kt
      kt_str kt_DC x (Kt.Comma ((Kt.Star y), z)) ((Sequent (y, (Kt.FSf
      a)))::((Sequent ((Kt.Comma (x, (Kt.FSf a))), (Kt.FSf b)))::((Sequent
      ((Kt.FSf b), z))::[]))) (fun hders ->
      let x0 = fun dC cs ->
        let _,x0 =
          forallT_deriv_cofseqs_iff eqDec_formula f_Kt_log kt_log
            eqDec_structr f_Kt kt_str dC cs
        in
        x0
      in
      let hders0 =
        x0 kt_DC ((Sequent (y, (Kt.FSf a)))::((Sequent ((Kt.Comma (x, (Kt.FSf
          a))), (Kt.FSf b)))::((Sequent ((Kt.FSf b), z))::[]))) hders
      in
      let hders1 =
        forallT_inv (Sequent (y, (Kt.FSf a))) ((Sequent ((Kt.Comma (x,
          (Kt.FSf a))), (Kt.FSf b)))::((Sequent ((Kt.FSf b), z))::[])) hders0
      in
      let hders2 =
        forallT_inv_tail (Sequent (y, (Kt.FSf a))) ((Sequent ((Kt.Comma (x,
          (Kt.FSf a))), (Kt.FSf b)))::((Sequent ((Kt.FSf b), z))::[])) hders0
      in
      let hders3 =
        forallT_inv (Sequent ((Kt.Comma (x, (Kt.FSf a))), (Kt.FSf b)))
          ((Sequent ((Kt.FSf b), z))::[]) hders2
      in
      let hders4 =
        forallT_inv_tail (Sequent ((Kt.Comma (x, (Kt.FSf a))), (Kt.FSf b)))
          ((Sequent ((Kt.FSf b), z))::[]) hders2
      in
      let hders5 = forallT_inv (Sequent ((Kt.FSf b), z)) [] hders4 in
      deriv_cofseq_rule_bw_inDC eqDec_formula f_Kt_log kt_log eqDec_structr
        f_Kt kt_str kt_DC
        (premsRule eqDec_formula f_Kt_log kt_log eqDec_structr f_Kt kt_str
          KtRules.coq_Mlln)
        (conclRule eqDec_formula f_Kt_log kt_log eqDec_structr f_Kt kt_str
          KtRules.coq_Mlln)
        (seq_matchsub eqDec_formula f_Kt_log kt_log eqDec_structr f_Kt kt_str
          (conclRule eqDec_formula f_Kt_log kt_log eqDec_structr f_Kt kt_str
            KtRules.coq_Mlln) (Sequent (x, (Kt.Comma ((Kt.Star y), z)))))
        (forallT_deriv_cofseqs eqDec_formula f_Kt_log kt_log eqDec_structr
          f_Kt kt_str kt_DC
          (map
            (seqSubst eqDec_formula f_Kt_log kt_log eqDec_structr f_Kt kt_str
              (seq_matchsub eqDec_formula f_Kt_log kt_log eqDec_structr f_Kt
                kt_str
                (conclRule eqDec_formula f_Kt_log kt_log eqDec_structr f_Kt
                  kt_str KtRules.coq_Mlln) (Sequent (x, (Kt.Comma ((Kt.Star
                y), z))))))
            (premsRule eqDec_formula f_Kt_log kt_log eqDec_structr f_Kt
              kt_str KtRules.coq_Mlln)) (ForallT_cons
          ((seqSubst eqDec_formula f_Kt_log kt_log eqDec_structr f_Kt kt_str
             (seq_matchsub eqDec_formula f_Kt_log kt_log eqDec_structr f_Kt
               kt_str
               (conclRule eqDec_formula f_Kt_log kt_log eqDec_structr f_Kt
                 kt_str KtRules.coq_Mlln) (Sequent (x, (Kt.Comma ((Kt.Star
               y), z))))) (Sequent ((Kt.Comma ((Kt.SVf "X"), (Kt.SVf "Y"))),
             (Kt.SVf "Z")))), [],
          (deriv_cofseq_rule_bw_inDC eqDec_formula f_Kt_log kt_log
            eqDec_structr f_Kt kt_str kt_DC
            (premsRule eqDec_formula f_Kt_log kt_log eqDec_structr f_Kt
              kt_str
              (cUT eqDec_formula f_Kt_log kt_log eqDec_structr f_Kt kt_str))
            (conclRule eqDec_formula f_Kt_log kt_log eqDec_structr f_Kt
              kt_str
              (cUT eqDec_formula f_Kt_log kt_log eqDec_structr f_Kt kt_str))
            (cUT_spec eqDec_formula f_Kt_log kt_log eqDec_structr f_Kt kt_str
              b (Kt.Comma (y, x)) z)
            (forallT_deriv_cofseqs eqDec_formula f_Kt_log kt_log
              eqDec_structr f_Kt kt_str kt_DC ((Sequent ((Kt.Comma (y, x)),
              (Kt.FSf b)))::((Sequent ((Kt.FSf b), z))::[])) (ForallT_cons
              ((Sequent ((Kt.Comma (y, x)), (Kt.FSf b))), ((Sequent ((Kt.FSf
              b), z))::[]),
              (deriv_cofseq_rule_bw_inDC eqDec_formula f_Kt_log kt_log
                eqDec_structr f_Kt kt_str kt_DC
                (premsRule eqDec_formula f_Kt_log kt_log eqDec_structr f_Kt
                  kt_str KtRules.coq_Mrrs)
                (conclRule eqDec_formula f_Kt_log kt_log eqDec_structr f_Kt
                  kt_str KtRules.coq_Mrrs)
                (seq_matchsub eqDec_formula f_Kt_log kt_log eqDec_structr
                  f_Kt kt_str
                  (conclRule eqDec_formula f_Kt_log kt_log eqDec_structr f_Kt
                    kt_str KtRules.coq_Mrrs) (Sequent ((Kt.Comma (y, x)),
                  (Kt.FSf b))))
                (forallT_deriv_cofseqs eqDec_formula f_Kt_log kt_log
                  eqDec_structr f_Kt kt_str kt_DC
                  (map
                    (seqSubst eqDec_formula f_Kt_log kt_log eqDec_structr
                      f_Kt kt_str
                      (seq_matchsub eqDec_formula f_Kt_log kt_log
                        eqDec_structr f_Kt kt_str
                        (conclRule eqDec_formula f_Kt_log kt_log
                          eqDec_structr f_Kt kt_str KtRules.coq_Mrrs)
                        (Sequent ((Kt.Comma (y, x)), (Kt.FSf b)))))
                    (premsRule eqDec_formula f_Kt_log kt_log eqDec_structr
                      f_Kt kt_str KtRules.coq_Mrrs)) (ForallT_cons
                  ((seqSubst eqDec_formula f_Kt_log kt_log eqDec_structr f_Kt
                     kt_str
                     (seq_matchsub eqDec_formula f_Kt_log kt_log
                       eqDec_structr f_Kt kt_str
                       (conclRule eqDec_formula f_Kt_log kt_log eqDec_structr
                         f_Kt kt_str KtRules.coq_Mrrs) (Sequent ((Kt.Comma
                       (y, x)), (Kt.FSf b)))) (Sequent ((Kt.SVf "X"),
                     (Kt.Comma ((Kt.SVf "Y"), (Kt.Star (Kt.SVf "Z"))))))),
                  [],
                  (deriv_cofseq_rule_bw_inDC eqDec_formula f_Kt_log kt_log
                    eqDec_structr f_Kt kt_str kt_DC
                    (premsRule eqDec_formula f_Kt_log kt_log eqDec_structr
                      f_Kt kt_str
                      (cUT eqDec_formula f_Kt_log kt_log eqDec_structr f_Kt
                        kt_str))
                    (conclRule eqDec_formula f_Kt_log kt_log eqDec_structr
                      f_Kt kt_str
                      (cUT eqDec_formula f_Kt_log kt_log eqDec_structr f_Kt
                        kt_str))
                    (cUT_spec eqDec_formula f_Kt_log kt_log eqDec_structr
                      f_Kt kt_str a y (Kt.Comma ((Kt.FSf b), (Kt.Star x))))
                    (forallT_deriv_cofseqs eqDec_formula f_Kt_log kt_log
                      eqDec_structr f_Kt kt_str kt_DC ((Sequent (y, (Kt.FSf
                      a)))::((Sequent ((Kt.FSf a), (Kt.Comma ((Kt.FSf b),
                      (Kt.Star x)))))::[])) (ForallT_cons ((Sequent (y,
                      (Kt.FSf a))), ((Sequent ((Kt.FSf a), (Kt.Comma ((Kt.FSf
                      b), (Kt.Star x)))))::[]), hders1, (ForallT_cons
                      ((Sequent ((Kt.FSf a), (Kt.Comma ((Kt.FSf b), (Kt.Star
                      x))))), [],
                      (deriv_cofseq_rule_bw_inDC eqDec_formula f_Kt_log
                        kt_log eqDec_structr f_Kt kt_str kt_DC
                        (premsRule eqDec_formula f_Kt_log kt_log
                          eqDec_structr f_Kt kt_str KtRules.coq_Mlrn)
                        (conclRule eqDec_formula f_Kt_log kt_log
                          eqDec_structr f_Kt kt_str KtRules.coq_Mlrn)
                        (seq_matchsub eqDec_formula f_Kt_log kt_log
                          eqDec_structr f_Kt kt_str
                          (conclRule eqDec_formula f_Kt_log kt_log
                            eqDec_structr f_Kt kt_str KtRules.coq_Mlrn)
                          (Sequent ((Kt.FSf a), (Kt.Comma ((Kt.FSf b),
                          (Kt.Star x))))))
                        (forallT_deriv_cofseqs eqDec_formula f_Kt_log kt_log
                          eqDec_structr f_Kt kt_str kt_DC
                          (map
                            (seqSubst eqDec_formula f_Kt_log kt_log
                              eqDec_structr f_Kt kt_str
                              (seq_matchsub eqDec_formula f_Kt_log kt_log
                                eqDec_structr f_Kt kt_str
                                (conclRule eqDec_formula f_Kt_log kt_log
                                  eqDec_structr f_Kt kt_str KtRules.coq_Mlrn)
                                (Sequent ((Kt.FSf a), (Kt.Comma ((Kt.FSf b),
                                (Kt.Star x)))))))
                            (premsRule eqDec_formula f_Kt_log kt_log
                              eqDec_structr f_Kt kt_str KtRules.coq_Mlrn))
                          (ForallT_cons
                          ((seqSubst eqDec_formula f_Kt_log kt_log
                             eqDec_structr f_Kt kt_str
                             (seq_matchsub eqDec_formula f_Kt_log kt_log
                               eqDec_structr f_Kt kt_str
                               (conclRule eqDec_formula f_Kt_log kt_log
                                 eqDec_structr f_Kt kt_str KtRules.coq_Mlrn)
                               (Sequent ((Kt.FSf a), (Kt.Comma ((Kt.FSf b),
                               (Kt.Star x)))))) (Sequent ((Kt.Comma ((Kt.SVf
                             "X"), (Kt.SVf "Y"))), (Kt.SVf "Z")))), [],
                          (deriv_cofseq_rule_bw_inDC eqDec_formula f_Kt_log
                            kt_log eqDec_structr f_Kt kt_str kt_DC
                            (premsRule eqDec_formula f_Kt_log kt_log
                              eqDec_structr f_Kt kt_str KtRules.coq_Comml)
                            (conclRule eqDec_formula f_Kt_log kt_log
                              eqDec_structr f_Kt kt_str KtRules.coq_Comml)
                            (seq_matchsub eqDec_formula f_Kt_log kt_log
                              eqDec_structr f_Kt kt_str
                              (conclRule eqDec_formula f_Kt_log kt_log
                                eqDec_structr f_Kt kt_str KtRules.coq_Comml)
                              (Sequent ((Kt.Comma ((Kt.FSf a), x)), (Kt.FSf
                              b))))
                            (forallT_deriv_cofseqs eqDec_formula f_Kt_log
                              kt_log eqDec_structr f_Kt kt_str kt_DC
                              (map
                                (seqSubst eqDec_formula f_Kt_log kt_log
                                  eqDec_structr f_Kt kt_str
                                  (seq_matchsub eqDec_formula f_Kt_log kt_log
                                    eqDec_structr f_Kt kt_str
                                    (conclRule eqDec_formula f_Kt_log kt_log
                                      eqDec_structr f_Kt kt_str
                                      KtRules.coq_Comml) (Sequent ((Kt.Comma
                                    ((Kt.FSf a), x)), (Kt.FSf b)))))
                                (premsRule eqDec_formula f_Kt_log kt_log
                                  eqDec_structr f_Kt kt_str KtRules.coq_Comml))
                              (ForallT_cons
                              ((seqSubst eqDec_formula f_Kt_log kt_log
                                 eqDec_structr f_Kt kt_str
                                 (seq_matchsub eqDec_formula f_Kt_log kt_log
                                   eqDec_structr f_Kt kt_str
                                   (conclRule eqDec_formula f_Kt_log kt_log
                                     eqDec_structr f_Kt kt_str
                                     KtRules.coq_Comml) (Sequent ((Kt.Comma
                                   ((Kt.FSf a), x)), (Kt.FSf b)))) (Sequent
                                 ((Kt.Comma ((Kt.SVf "X"), (Kt.SVf "Y"))),
                                 (Kt.SVf "Z")))), [], hders3, ForallT_nil)))),
                          ForallT_nil)))), ForallT_nil)))))), ForallT_nil)))),
              (ForallT_cons ((Sequent ((Kt.FSf b), z)), [], hders5,
              ForallT_nil)))))), ForallT_nil)))) ld

  (** val coq_C8_Boxn :
      Kt.structr -> Kt.structr -> Kt.formula -> (Kt.formula, Kt.structr)
      dertree list -> (Kt.formula, Kt.structr) dertree **)

  let coq_C8_Boxn x y a ld =
    c8_case_alt_imp_C8_case eqDec_formula f_Kt_log kt_log eqDec_structr f_Kt
      kt_str kt_DC x (Kt.BCirc y) ((Sequent ((Kt.BCirc x), (Kt.FSf
      a)))::((Sequent ((Kt.FSf a), y))::[])) (fun hders ->
      let x0 = fun dC cs ->
        let _,x0 =
          forallT_deriv_cofseqs_iff eqDec_formula f_Kt_log kt_log
            eqDec_structr f_Kt kt_str dC cs
        in
        x0
      in
      let hders0 =
        x0 kt_DC ((Sequent ((Kt.BCirc x), (Kt.FSf a)))::((Sequent ((Kt.FSf
          a), y))::[])) hders
      in
      let hders1 =
        forallT_inv (Sequent ((Kt.BCirc x), (Kt.FSf a))) ((Sequent ((Kt.FSf
          a), y))::[]) hders0
      in
      let hders2 =
        forallT_inv_tail (Sequent ((Kt.BCirc x), (Kt.FSf a))) ((Sequent
          ((Kt.FSf a), y))::[]) hders0
      in
      let hders3 = forallT_inv (Sequent ((Kt.FSf a), y)) [] hders2 in
      deriv_cofseq_rule_bw_inDC eqDec_formula f_Kt_log kt_log eqDec_structr
        f_Kt kt_str kt_DC
        (premsRule eqDec_formula f_Kt_log kt_log eqDec_structr f_Kt kt_str
          KtRules.coq_Scl)
        (conclRule eqDec_formula f_Kt_log kt_log eqDec_structr f_Kt kt_str
          KtRules.coq_Scl)
        (seq_matchsub eqDec_formula f_Kt_log kt_log eqDec_structr f_Kt kt_str
          (conclRule eqDec_formula f_Kt_log kt_log eqDec_structr f_Kt kt_str
            KtRules.coq_Scl) (Sequent (x, (Kt.BCirc y))))
        (forallT_deriv_cofseqs eqDec_formula f_Kt_log kt_log eqDec_structr
          f_Kt kt_str kt_DC
          (map
            (seqSubst eqDec_formula f_Kt_log kt_log eqDec_structr f_Kt kt_str
              (seq_matchsub eqDec_formula f_Kt_log kt_log eqDec_structr f_Kt
                kt_str
                (conclRule eqDec_formula f_Kt_log kt_log eqDec_structr f_Kt
                  kt_str KtRules.coq_Scl) (Sequent (x, (Kt.BCirc y)))))
            (premsRule eqDec_formula f_Kt_log kt_log eqDec_structr f_Kt
              kt_str KtRules.coq_Scl)) (ForallT_cons
          ((seqSubst eqDec_formula f_Kt_log kt_log eqDec_structr f_Kt kt_str
             (seq_matchsub eqDec_formula f_Kt_log kt_log eqDec_structr f_Kt
               kt_str
               (conclRule eqDec_formula f_Kt_log kt_log eqDec_structr f_Kt
                 kt_str KtRules.coq_Scl) (Sequent (x, (Kt.BCirc y))))
             (Sequent ((Kt.BCirc (Kt.SVf "X")), (Kt.SVf "Y")))), [],
          (deriv_cofseq_rule_bw_inDC eqDec_formula f_Kt_log kt_log
            eqDec_structr f_Kt kt_str kt_DC
            (premsRule eqDec_formula f_Kt_log kt_log eqDec_structr f_Kt
              kt_str
              (cUT eqDec_formula f_Kt_log kt_log eqDec_structr f_Kt kt_str))
            (conclRule eqDec_formula f_Kt_log kt_log eqDec_structr f_Kt
              kt_str
              (cUT eqDec_formula f_Kt_log kt_log eqDec_structr f_Kt kt_str))
            (cUT_spec eqDec_formula f_Kt_log kt_log eqDec_structr f_Kt kt_str
              a (Kt.BCirc x) y)
            (forallT_deriv_cofseqs eqDec_formula f_Kt_log kt_log
              eqDec_structr f_Kt kt_str kt_DC ((Sequent ((Kt.BCirc x),
              (Kt.FSf a)))::((Sequent ((Kt.FSf a), y))::[])) (ForallT_cons
              ((Sequent ((Kt.BCirc x), (Kt.FSf a))), ((Sequent ((Kt.FSf a),
              y))::[]), hders1, (ForallT_cons ((Sequent ((Kt.FSf a), y)), [],
              hders3, ForallT_nil)))))), ForallT_nil)))) ld

  (** val coq_C8_Dian :
      Kt.structr -> Kt.structr -> Kt.formula -> (Kt.formula, Kt.structr)
      dertree list -> (Kt.formula, Kt.structr) dertree **)

  let coq_C8_Dian x y a ld =
    c8_case_alt_imp_C8_case eqDec_formula f_Kt_log kt_log eqDec_structr f_Kt
      kt_str kt_DC (Kt.Star (Kt.BCirc (Kt.Star x))) y ((Sequent (x, (Kt.FSf
      a)))::((Sequent ((Kt.Star (Kt.BCirc (Kt.Star (Kt.FSf a)))), y))::[]))
      (fun hders ->
      let x0 = fun dC cs ->
        let _,x0 =
          forallT_deriv_cofseqs_iff eqDec_formula f_Kt_log kt_log
            eqDec_structr f_Kt kt_str dC cs
        in
        x0
      in
      let hders0 =
        x0 kt_DC ((Sequent (x, (Kt.FSf a)))::((Sequent ((Kt.Star (Kt.BCirc
          (Kt.Star (Kt.FSf a)))), y))::[])) hders
      in
      let hders1 =
        forallT_inv (Sequent (x, (Kt.FSf a))) ((Sequent ((Kt.Star (Kt.BCirc
          (Kt.Star (Kt.FSf a)))), y))::[]) hders0
      in
      let hders2 =
        forallT_inv_tail (Sequent (x, (Kt.FSf a))) ((Sequent ((Kt.Star
          (Kt.BCirc (Kt.Star (Kt.FSf a)))), y))::[]) hders0
      in
      let hders3 =
        forallT_inv (Sequent ((Kt.Star (Kt.BCirc (Kt.Star (Kt.FSf a)))), y))
          [] hders2
      in
      deriv_cofseq_rule_bw_inDC eqDec_formula f_Kt_log kt_log eqDec_structr
        f_Kt kt_str kt_DC
        (premsRule eqDec_formula f_Kt_log kt_log eqDec_structr f_Kt kt_str
          KtRules.coq_Ssn)
        (conclRule eqDec_formula f_Kt_log kt_log eqDec_structr f_Kt kt_str
          KtRules.coq_Ssn)
        (seq_matchsub eqDec_formula f_Kt_log kt_log eqDec_structr f_Kt kt_str
          (conclRule eqDec_formula f_Kt_log kt_log eqDec_structr f_Kt kt_str
            KtRules.coq_Ssn) (Sequent ((Kt.Star (Kt.BCirc (Kt.Star x))), y)))
        (forallT_deriv_cofseqs eqDec_formula f_Kt_log kt_log eqDec_structr
          f_Kt kt_str kt_DC
          (map
            (seqSubst eqDec_formula f_Kt_log kt_log eqDec_structr f_Kt kt_str
              (seq_matchsub eqDec_formula f_Kt_log kt_log eqDec_structr f_Kt
                kt_str
                (conclRule eqDec_formula f_Kt_log kt_log eqDec_structr f_Kt
                  kt_str KtRules.coq_Ssn) (Sequent ((Kt.Star (Kt.BCirc
                (Kt.Star x))), y))))
            (premsRule eqDec_formula f_Kt_log kt_log eqDec_structr f_Kt
              kt_str KtRules.coq_Ssn)) (ForallT_cons
          ((seqSubst eqDec_formula f_Kt_log kt_log eqDec_structr f_Kt kt_str
             (seq_matchsub eqDec_formula f_Kt_log kt_log eqDec_structr f_Kt
               kt_str
               (conclRule eqDec_formula f_Kt_log kt_log eqDec_structr f_Kt
                 kt_str KtRules.coq_Ssn) (Sequent ((Kt.Star (Kt.BCirc
               (Kt.Star x))), y))) (Sequent ((Kt.Star (Kt.SVf "X")), (Kt.SVf
             "Y")))), [],
          (deriv_cofseq_rule_bw_inDC eqDec_formula f_Kt_log kt_log
            eqDec_structr f_Kt kt_str kt_DC
            (premsRule eqDec_formula f_Kt_log kt_log eqDec_structr f_Kt
              kt_str KtRules.coq_Scl)
            (conclRule eqDec_formula f_Kt_log kt_log eqDec_structr f_Kt
              kt_str KtRules.coq_Scl)
            (seq_matchsub eqDec_formula f_Kt_log kt_log eqDec_structr f_Kt
              kt_str
              (conclRule eqDec_formula f_Kt_log kt_log eqDec_structr f_Kt
                kt_str KtRules.coq_Scl) (Sequent ((Kt.Star y), (Kt.BCirc
              (Kt.Star x)))))
            (forallT_deriv_cofseqs eqDec_formula f_Kt_log kt_log
              eqDec_structr f_Kt kt_str kt_DC
              (map
                (seqSubst eqDec_formula f_Kt_log kt_log eqDec_structr f_Kt
                  kt_str
                  (seq_matchsub eqDec_formula f_Kt_log kt_log eqDec_structr
                    f_Kt kt_str
                    (conclRule eqDec_formula f_Kt_log kt_log eqDec_structr
                      f_Kt kt_str KtRules.coq_Scl) (Sequent ((Kt.Star y),
                    (Kt.BCirc (Kt.Star x))))))
                (premsRule eqDec_formula f_Kt_log kt_log eqDec_structr f_Kt
                  kt_str KtRules.coq_Scl)) (ForallT_cons
              ((seqSubst eqDec_formula f_Kt_log kt_log eqDec_structr f_Kt
                 kt_str
                 (seq_matchsub eqDec_formula f_Kt_log kt_log eqDec_structr
                   f_Kt kt_str
                   (conclRule eqDec_formula f_Kt_log kt_log eqDec_structr
                     f_Kt kt_str KtRules.coq_Scl) (Sequent ((Kt.Star y),
                   (Kt.BCirc (Kt.Star x))))) (Sequent ((Kt.BCirc (Kt.SVf
                 "X")), (Kt.SVf "Y")))), [],
              (deriv_cofseq_rule_bw_inDC eqDec_formula f_Kt_log kt_log
                eqDec_structr f_Kt kt_str kt_DC
                (premsRule eqDec_formula f_Kt_log kt_log eqDec_structr f_Kt
                  kt_str KtRules.coq_Sns)
                (conclRule eqDec_formula f_Kt_log kt_log eqDec_structr f_Kt
                  kt_str KtRules.coq_Sns)
                (seq_matchsub eqDec_formula f_Kt_log kt_log eqDec_structr
                  f_Kt kt_str
                  (conclRule eqDec_formula f_Kt_log kt_log eqDec_structr f_Kt
                    kt_str KtRules.coq_Sns) (Sequent ((Kt.BCirc (Kt.Star y)),
                  (Kt.Star x))))
                (forallT_deriv_cofseqs eqDec_formula f_Kt_log kt_log
                  eqDec_structr f_Kt kt_str kt_DC
                  (map
                    (seqSubst eqDec_formula f_Kt_log kt_log eqDec_structr
                      f_Kt kt_str
                      (seq_matchsub eqDec_formula f_Kt_log kt_log
                        eqDec_structr f_Kt kt_str
                        (conclRule eqDec_formula f_Kt_log kt_log
                          eqDec_structr f_Kt kt_str KtRules.coq_Sns) (Sequent
                        ((Kt.BCirc (Kt.Star y)), (Kt.Star x)))))
                    (premsRule eqDec_formula f_Kt_log kt_log eqDec_structr
                      f_Kt kt_str KtRules.coq_Sns)) (ForallT_cons
                  ((seqSubst eqDec_formula f_Kt_log kt_log eqDec_structr f_Kt
                     kt_str
                     (seq_matchsub eqDec_formula f_Kt_log kt_log
                       eqDec_structr f_Kt kt_str
                       (conclRule eqDec_formula f_Kt_log kt_log eqDec_structr
                         f_Kt kt_str KtRules.coq_Sns) (Sequent ((Kt.BCirc
                       (Kt.Star y)), (Kt.Star x)))) (Sequent ((Kt.SVf "X"),
                     (Kt.Star (Kt.SVf "Y"))))), [],
                  (deriv_cofseq_rule_bw_inDC eqDec_formula f_Kt_log kt_log
                    eqDec_structr f_Kt kt_str kt_DC
                    (premsRule eqDec_formula f_Kt_log kt_log eqDec_structr
                      f_Kt kt_str
                      (cUT eqDec_formula f_Kt_log kt_log eqDec_structr f_Kt
                        kt_str))
                    (conclRule eqDec_formula f_Kt_log kt_log eqDec_structr
                      f_Kt kt_str
                      (cUT eqDec_formula f_Kt_log kt_log eqDec_structr f_Kt
                        kt_str))
                    (cUT_spec eqDec_formula f_Kt_log kt_log eqDec_structr
                      f_Kt kt_str a x (Kt.Star (Kt.BCirc (Kt.Star y))))
                    (forallT_deriv_cofseqs eqDec_formula f_Kt_log kt_log
                      eqDec_structr f_Kt kt_str kt_DC ((Sequent (x, (Kt.FSf
                      a)))::((Sequent ((Kt.FSf a), (Kt.Star (Kt.BCirc
                      (Kt.Star y)))))::[])) (ForallT_cons ((Sequent (x,
                      (Kt.FSf a))), ((Sequent ((Kt.FSf a), (Kt.Star (Kt.BCirc
                      (Kt.Star y)))))::[]), hders1, (ForallT_cons ((Sequent
                      ((Kt.FSf a), (Kt.Star (Kt.BCirc (Kt.Star y))))), [],
                      (deriv_cofseq_rule_bw_inDC eqDec_formula f_Kt_log
                        kt_log eqDec_structr f_Kt kt_str kt_DC
                        (premsRule eqDec_formula f_Kt_log kt_log
                          eqDec_structr f_Kt kt_str KtRules.coq_Sns)
                        (conclRule eqDec_formula f_Kt_log kt_log
                          eqDec_structr f_Kt kt_str KtRules.coq_Sns)
                        (seq_matchsub eqDec_formula f_Kt_log kt_log
                          eqDec_structr f_Kt kt_str
                          (conclRule eqDec_formula f_Kt_log kt_log
                            eqDec_structr f_Kt kt_str KtRules.coq_Sns)
                          (Sequent ((Kt.FSf a), (Kt.Star (Kt.BCirc (Kt.Star
                          y))))))
                        (forallT_deriv_cofseqs eqDec_formula f_Kt_log kt_log
                          eqDec_structr f_Kt kt_str kt_DC
                          (map
                            (seqSubst eqDec_formula f_Kt_log kt_log
                              eqDec_structr f_Kt kt_str
                              (seq_matchsub eqDec_formula f_Kt_log kt_log
                                eqDec_structr f_Kt kt_str
                                (conclRule eqDec_formula f_Kt_log kt_log
                                  eqDec_structr f_Kt kt_str KtRules.coq_Sns)
                                (Sequent ((Kt.FSf a), (Kt.Star (Kt.BCirc
                                (Kt.Star y)))))))
                            (premsRule eqDec_formula f_Kt_log kt_log
                              eqDec_structr f_Kt kt_str KtRules.coq_Sns))
                          (ForallT_cons
                          ((seqSubst eqDec_formula f_Kt_log kt_log
                             eqDec_structr f_Kt kt_str
                             (seq_matchsub eqDec_formula f_Kt_log kt_log
                               eqDec_structr f_Kt kt_str
                               (conclRule eqDec_formula f_Kt_log kt_log
                                 eqDec_structr f_Kt kt_str KtRules.coq_Sns)
                               (Sequent ((Kt.FSf a), (Kt.Star (Kt.BCirc
                               (Kt.Star y)))))) (Sequent ((Kt.SVf "X"),
                             (Kt.Star (Kt.SVf "Y"))))), [],
                          (deriv_cofseq_rule_bw_inDC eqDec_formula f_Kt_log
                            kt_log eqDec_structr f_Kt kt_str kt_DC
                            (premsRule eqDec_formula f_Kt_log kt_log
                              eqDec_structr f_Kt kt_str KtRules.coq_Scr)
                            (conclRule eqDec_formula f_Kt_log kt_log
                              eqDec_structr f_Kt kt_str KtRules.coq_Scr)
                            (seq_matchsub eqDec_formula f_Kt_log kt_log
                              eqDec_structr f_Kt kt_str
                              (conclRule eqDec_formula f_Kt_log kt_log
                                eqDec_structr f_Kt kt_str KtRules.coq_Scr)
                              (Sequent ((Kt.BCirc (Kt.Star y)), (Kt.Star
                              (Kt.FSf a)))))
                            (forallT_deriv_cofseqs eqDec_formula f_Kt_log
                              kt_log eqDec_structr f_Kt kt_str kt_DC
                              (map
                                (seqSubst eqDec_formula f_Kt_log kt_log
                                  eqDec_structr f_Kt kt_str
                                  (seq_matchsub eqDec_formula f_Kt_log kt_log
                                    eqDec_structr f_Kt kt_str
                                    (conclRule eqDec_formula f_Kt_log kt_log
                                      eqDec_structr f_Kt kt_str
                                      KtRules.coq_Scr) (Sequent ((Kt.BCirc
                                    (Kt.Star y)), (Kt.Star (Kt.FSf a))))))
                                (premsRule eqDec_formula f_Kt_log kt_log
                                  eqDec_structr f_Kt kt_str KtRules.coq_Scr))
                              (ForallT_cons
                              ((seqSubst eqDec_formula f_Kt_log kt_log
                                 eqDec_structr f_Kt kt_str
                                 (seq_matchsub eqDec_formula f_Kt_log kt_log
                                   eqDec_structr f_Kt kt_str
                                   (conclRule eqDec_formula f_Kt_log kt_log
                                     eqDec_structr f_Kt kt_str
                                     KtRules.coq_Scr) (Sequent ((Kt.BCirc
                                   (Kt.Star y)), (Kt.Star (Kt.FSf a)))))
                                 (Sequent ((Kt.SVf "X"), (Kt.BCirc (Kt.SVf
                                 "Y"))))), [],
                              (deriv_cofseq_rule_bw_inDC eqDec_formula
                                f_Kt_log kt_log eqDec_structr f_Kt kt_str
                                kt_DC
                                (premsRule eqDec_formula f_Kt_log kt_log
                                  eqDec_structr f_Kt kt_str KtRules.coq_Ssn)
                                (conclRule eqDec_formula f_Kt_log kt_log
                                  eqDec_structr f_Kt kt_str KtRules.coq_Ssn)
                                (seq_matchsub eqDec_formula f_Kt_log kt_log
                                  eqDec_structr f_Kt kt_str
                                  (conclRule eqDec_formula f_Kt_log kt_log
                                    eqDec_structr f_Kt kt_str KtRules.coq_Ssn)
                                  (Sequent ((Kt.Star y), (Kt.BCirc (Kt.Star
                                  (Kt.FSf a))))))
                                (forallT_deriv_cofseqs eqDec_formula f_Kt_log
                                  kt_log eqDec_structr f_Kt kt_str kt_DC
                                  (map
                                    (seqSubst eqDec_formula f_Kt_log kt_log
                                      eqDec_structr f_Kt kt_str
                                      (seq_matchsub eqDec_formula f_Kt_log
                                        kt_log eqDec_structr f_Kt kt_str
                                        (conclRule eqDec_formula f_Kt_log
                                          kt_log eqDec_structr f_Kt kt_str
                                          KtRules.coq_Ssn) (Sequent ((Kt.Star
                                        y), (Kt.BCirc (Kt.Star (Kt.FSf a)))))))
                                    (premsRule eqDec_formula f_Kt_log kt_log
                                      eqDec_structr f_Kt kt_str
                                      KtRules.coq_Ssn)) (ForallT_cons
                                  ((seqSubst eqDec_formula f_Kt_log kt_log
                                     eqDec_structr f_Kt kt_str
                                     (seq_matchsub eqDec_formula f_Kt_log
                                       kt_log eqDec_structr f_Kt kt_str
                                       (conclRule eqDec_formula f_Kt_log
                                         kt_log eqDec_structr f_Kt kt_str
                                         KtRules.coq_Ssn) (Sequent ((Kt.Star
                                       y), (Kt.BCirc (Kt.Star (Kt.FSf a))))))
                                     (Sequent ((Kt.Star (Kt.SVf "X")),
                                     (Kt.SVf "Y")))), [], hders3,
                                  ForallT_nil)))), ForallT_nil)))),
                          ForallT_nil)))), ForallT_nil)))))), ForallT_nil)))),
              ForallT_nil)))), ForallT_nil)))) ld

  (** val coq_C8_Boxp :
      Kt.structr -> Kt.structr -> Kt.formula -> (Kt.formula, Kt.structr)
      dertree list -> (Kt.formula, Kt.structr) dertree **)

  let coq_C8_Boxp x y a ld =
    c8_case_alt_imp_C8_case eqDec_formula f_Kt_log kt_log eqDec_structr f_Kt
      kt_str kt_DC x (Kt.Star (Kt.BCirc (Kt.Star y))) ((Sequent (x, (Kt.Star
      (Kt.BCirc (Kt.Star (Kt.FSf a))))))::((Sequent ((Kt.FSf a), y))::[]))
      (fun hders ->
      let x0 = fun dC cs ->
        let _,x0 =
          forallT_deriv_cofseqs_iff eqDec_formula f_Kt_log kt_log
            eqDec_structr f_Kt kt_str dC cs
        in
        x0
      in
      let hders0 =
        x0 kt_DC ((Sequent (x, (Kt.Star (Kt.BCirc (Kt.Star (Kt.FSf
          a))))))::((Sequent ((Kt.FSf a), y))::[])) hders
      in
      let hders1 =
        forallT_inv (Sequent (x, (Kt.Star (Kt.BCirc (Kt.Star (Kt.FSf a))))))
          ((Sequent ((Kt.FSf a), y))::[]) hders0
      in
      let hders2 =
        forallT_inv_tail (Sequent (x, (Kt.Star (Kt.BCirc (Kt.Star (Kt.FSf
          a)))))) ((Sequent ((Kt.FSf a), y))::[]) hders0
      in
      let hders3 = forallT_inv (Sequent ((Kt.FSf a), y)) [] hders2 in
      deriv_cofseq_rule_bw_inDC eqDec_formula f_Kt_log kt_log eqDec_structr
        f_Kt kt_str kt_DC
        (premsRule eqDec_formula f_Kt_log kt_log eqDec_structr f_Kt kt_str
          KtRules.coq_Sns)
        (conclRule eqDec_formula f_Kt_log kt_log eqDec_structr f_Kt kt_str
          KtRules.coq_Sns)
        (seq_matchsub eqDec_formula f_Kt_log kt_log eqDec_structr f_Kt kt_str
          (conclRule eqDec_formula f_Kt_log kt_log eqDec_structr f_Kt kt_str
            KtRules.coq_Sns) (Sequent (x, (Kt.Star (Kt.BCirc (Kt.Star y))))))
        (forallT_deriv_cofseqs eqDec_formula f_Kt_log kt_log eqDec_structr
          f_Kt kt_str kt_DC
          (map
            (seqSubst eqDec_formula f_Kt_log kt_log eqDec_structr f_Kt kt_str
              (seq_matchsub eqDec_formula f_Kt_log kt_log eqDec_structr f_Kt
                kt_str
                (conclRule eqDec_formula f_Kt_log kt_log eqDec_structr f_Kt
                  kt_str KtRules.coq_Sns) (Sequent (x, (Kt.Star (Kt.BCirc
                (Kt.Star y)))))))
            (premsRule eqDec_formula f_Kt_log kt_log eqDec_structr f_Kt
              kt_str KtRules.coq_Sns)) (ForallT_cons
          ((seqSubst eqDec_formula f_Kt_log kt_log eqDec_structr f_Kt kt_str
             (seq_matchsub eqDec_formula f_Kt_log kt_log eqDec_structr f_Kt
               kt_str
               (conclRule eqDec_formula f_Kt_log kt_log eqDec_structr f_Kt
                 kt_str KtRules.coq_Sns) (Sequent (x, (Kt.Star (Kt.BCirc
               (Kt.Star y)))))) (Sequent ((Kt.SVf "X"), (Kt.Star (Kt.SVf
             "Y"))))), [],
          (deriv_cofseq_rule_bw_inDC eqDec_formula f_Kt_log kt_log
            eqDec_structr f_Kt kt_str kt_DC
            (premsRule eqDec_formula f_Kt_log kt_log eqDec_structr f_Kt
              kt_str KtRules.coq_Scr)
            (conclRule eqDec_formula f_Kt_log kt_log eqDec_structr f_Kt
              kt_str KtRules.coq_Scr)
            (seq_matchsub eqDec_formula f_Kt_log kt_log eqDec_structr f_Kt
              kt_str
              (conclRule eqDec_formula f_Kt_log kt_log eqDec_structr f_Kt
                kt_str KtRules.coq_Scr) (Sequent ((Kt.BCirc (Kt.Star y)),
              (Kt.Star x))))
            (forallT_deriv_cofseqs eqDec_formula f_Kt_log kt_log
              eqDec_structr f_Kt kt_str kt_DC
              (map
                (seqSubst eqDec_formula f_Kt_log kt_log eqDec_structr f_Kt
                  kt_str
                  (seq_matchsub eqDec_formula f_Kt_log kt_log eqDec_structr
                    f_Kt kt_str
                    (conclRule eqDec_formula f_Kt_log kt_log eqDec_structr
                      f_Kt kt_str KtRules.coq_Scr) (Sequent ((Kt.BCirc
                    (Kt.Star y)), (Kt.Star x)))))
                (premsRule eqDec_formula f_Kt_log kt_log eqDec_structr f_Kt
                  kt_str KtRules.coq_Scr)) (ForallT_cons
              ((seqSubst eqDec_formula f_Kt_log kt_log eqDec_structr f_Kt
                 kt_str
                 (seq_matchsub eqDec_formula f_Kt_log kt_log eqDec_structr
                   f_Kt kt_str
                   (conclRule eqDec_formula f_Kt_log kt_log eqDec_structr
                     f_Kt kt_str KtRules.coq_Scr) (Sequent ((Kt.BCirc
                   (Kt.Star y)), (Kt.Star x)))) (Sequent ((Kt.SVf "X"),
                 (Kt.BCirc (Kt.SVf "Y"))))), [],
              (deriv_cofseq_rule_bw_inDC eqDec_formula f_Kt_log kt_log
                eqDec_structr f_Kt kt_str kt_DC
                (premsRule eqDec_formula f_Kt_log kt_log eqDec_structr f_Kt
                  kt_str KtRules.coq_Ssn)
                (conclRule eqDec_formula f_Kt_log kt_log eqDec_structr f_Kt
                  kt_str KtRules.coq_Ssn)
                (seq_matchsub eqDec_formula f_Kt_log kt_log eqDec_structr
                  f_Kt kt_str
                  (conclRule eqDec_formula f_Kt_log kt_log eqDec_structr f_Kt
                    kt_str KtRules.coq_Ssn) (Sequent ((Kt.Star y), (Kt.BCirc
                  (Kt.Star x)))))
                (forallT_deriv_cofseqs eqDec_formula f_Kt_log kt_log
                  eqDec_structr f_Kt kt_str kt_DC
                  (map
                    (seqSubst eqDec_formula f_Kt_log kt_log eqDec_structr
                      f_Kt kt_str
                      (seq_matchsub eqDec_formula f_Kt_log kt_log
                        eqDec_structr f_Kt kt_str
                        (conclRule eqDec_formula f_Kt_log kt_log
                          eqDec_structr f_Kt kt_str KtRules.coq_Ssn) (Sequent
                        ((Kt.Star y), (Kt.BCirc (Kt.Star x))))))
                    (premsRule eqDec_formula f_Kt_log kt_log eqDec_structr
                      f_Kt kt_str KtRules.coq_Ssn)) (ForallT_cons
                  ((seqSubst eqDec_formula f_Kt_log kt_log eqDec_structr f_Kt
                     kt_str
                     (seq_matchsub eqDec_formula f_Kt_log kt_log
                       eqDec_structr f_Kt kt_str
                       (conclRule eqDec_formula f_Kt_log kt_log eqDec_structr
                         f_Kt kt_str KtRules.coq_Ssn) (Sequent ((Kt.Star y),
                       (Kt.BCirc (Kt.Star x))))) (Sequent ((Kt.Star (Kt.SVf
                     "X")), (Kt.SVf "Y")))), [],
                  (deriv_cofseq_rule_bw_inDC eqDec_formula f_Kt_log kt_log
                    eqDec_structr f_Kt kt_str kt_DC
                    (premsRule eqDec_formula f_Kt_log kt_log eqDec_structr
                      f_Kt kt_str
                      (cUT eqDec_formula f_Kt_log kt_log eqDec_structr f_Kt
                        kt_str))
                    (conclRule eqDec_formula f_Kt_log kt_log eqDec_structr
                      f_Kt kt_str
                      (cUT eqDec_formula f_Kt_log kt_log eqDec_structr f_Kt
                        kt_str))
                    (cUT_spec eqDec_formula f_Kt_log kt_log eqDec_structr
                      f_Kt kt_str a (Kt.Star (Kt.BCirc (Kt.Star x))) y)
                    (forallT_deriv_cofseqs eqDec_formula f_Kt_log kt_log
                      eqDec_structr f_Kt kt_str kt_DC ((Sequent ((Kt.Star
                      (Kt.BCirc (Kt.Star x))), (Kt.FSf a)))::((Sequent
                      ((Kt.FSf a), y))::[])) (ForallT_cons ((Sequent
                      ((Kt.Star (Kt.BCirc (Kt.Star x))), (Kt.FSf a))),
                      ((Sequent ((Kt.FSf a), y))::[]),
                      (deriv_cofseq_rule_bw_inDC eqDec_formula f_Kt_log
                        kt_log eqDec_structr f_Kt kt_str kt_DC
                        (premsRule eqDec_formula f_Kt_log kt_log
                          eqDec_structr f_Kt kt_str KtRules.coq_Ssn)
                        (conclRule eqDec_formula f_Kt_log kt_log
                          eqDec_structr f_Kt kt_str KtRules.coq_Ssn)
                        (seq_matchsub eqDec_formula f_Kt_log kt_log
                          eqDec_structr f_Kt kt_str
                          (conclRule eqDec_formula f_Kt_log kt_log
                            eqDec_structr f_Kt kt_str KtRules.coq_Ssn)
                          (Sequent ((Kt.Star (Kt.BCirc (Kt.Star x))), (Kt.FSf
                          a))))
                        (forallT_deriv_cofseqs eqDec_formula f_Kt_log kt_log
                          eqDec_structr f_Kt kt_str kt_DC
                          (map
                            (seqSubst eqDec_formula f_Kt_log kt_log
                              eqDec_structr f_Kt kt_str
                              (seq_matchsub eqDec_formula f_Kt_log kt_log
                                eqDec_structr f_Kt kt_str
                                (conclRule eqDec_formula f_Kt_log kt_log
                                  eqDec_structr f_Kt kt_str KtRules.coq_Ssn)
                                (Sequent ((Kt.Star (Kt.BCirc (Kt.Star x))),
                                (Kt.FSf a)))))
                            (premsRule eqDec_formula f_Kt_log kt_log
                              eqDec_structr f_Kt kt_str KtRules.coq_Ssn))
                          (ForallT_cons
                          ((seqSubst eqDec_formula f_Kt_log kt_log
                             eqDec_structr f_Kt kt_str
                             (seq_matchsub eqDec_formula f_Kt_log kt_log
                               eqDec_structr f_Kt kt_str
                               (conclRule eqDec_formula f_Kt_log kt_log
                                 eqDec_structr f_Kt kt_str KtRules.coq_Ssn)
                               (Sequent ((Kt.Star (Kt.BCirc (Kt.Star x))),
                               (Kt.FSf a)))) (Sequent ((Kt.Star (Kt.SVf
                             "X")), (Kt.SVf "Y")))), [],
                          (deriv_cofseq_rule_bw_inDC eqDec_formula f_Kt_log
                            kt_log eqDec_structr f_Kt kt_str kt_DC
                            (premsRule eqDec_formula f_Kt_log kt_log
                              eqDec_structr f_Kt kt_str KtRules.coq_Scl)
                            (conclRule eqDec_formula f_Kt_log kt_log
                              eqDec_structr f_Kt kt_str KtRules.coq_Scl)
                            (seq_matchsub eqDec_formula f_Kt_log kt_log
                              eqDec_structr f_Kt kt_str
                              (conclRule eqDec_formula f_Kt_log kt_log
                                eqDec_structr f_Kt kt_str KtRules.coq_Scl)
                              (Sequent ((Kt.Star (Kt.FSf a)), (Kt.BCirc
                              (Kt.Star x)))))
                            (forallT_deriv_cofseqs eqDec_formula f_Kt_log
                              kt_log eqDec_structr f_Kt kt_str kt_DC
                              (map
                                (seqSubst eqDec_formula f_Kt_log kt_log
                                  eqDec_structr f_Kt kt_str
                                  (seq_matchsub eqDec_formula f_Kt_log kt_log
                                    eqDec_structr f_Kt kt_str
                                    (conclRule eqDec_formula f_Kt_log kt_log
                                      eqDec_structr f_Kt kt_str
                                      KtRules.coq_Scl) (Sequent ((Kt.Star
                                    (Kt.FSf a)), (Kt.BCirc (Kt.Star x))))))
                                (premsRule eqDec_formula f_Kt_log kt_log
                                  eqDec_structr f_Kt kt_str KtRules.coq_Scl))
                              (ForallT_cons
                              ((seqSubst eqDec_formula f_Kt_log kt_log
                                 eqDec_structr f_Kt kt_str
                                 (seq_matchsub eqDec_formula f_Kt_log kt_log
                                   eqDec_structr f_Kt kt_str
                                   (conclRule eqDec_formula f_Kt_log kt_log
                                     eqDec_structr f_Kt kt_str
                                     KtRules.coq_Scl) (Sequent ((Kt.Star
                                   (Kt.FSf a)), (Kt.BCirc (Kt.Star x)))))
                                 (Sequent ((Kt.BCirc (Kt.SVf "X")), (Kt.SVf
                                 "Y")))), [],
                              (deriv_cofseq_rule_bw_inDC eqDec_formula
                                f_Kt_log kt_log eqDec_structr f_Kt kt_str
                                kt_DC
                                (premsRule eqDec_formula f_Kt_log kt_log
                                  eqDec_structr f_Kt kt_str KtRules.coq_Sns)
                                (conclRule eqDec_formula f_Kt_log kt_log
                                  eqDec_structr f_Kt kt_str KtRules.coq_Sns)
                                (seq_matchsub eqDec_formula f_Kt_log kt_log
                                  eqDec_structr f_Kt kt_str
                                  (conclRule eqDec_formula f_Kt_log kt_log
                                    eqDec_structr f_Kt kt_str KtRules.coq_Sns)
                                  (Sequent ((Kt.BCirc (Kt.Star (Kt.FSf a))),
                                  (Kt.Star x))))
                                (forallT_deriv_cofseqs eqDec_formula f_Kt_log
                                  kt_log eqDec_structr f_Kt kt_str kt_DC
                                  (map
                                    (seqSubst eqDec_formula f_Kt_log kt_log
                                      eqDec_structr f_Kt kt_str
                                      (seq_matchsub eqDec_formula f_Kt_log
                                        kt_log eqDec_structr f_Kt kt_str
                                        (conclRule eqDec_formula f_Kt_log
                                          kt_log eqDec_structr f_Kt kt_str
                                          KtRules.coq_Sns) (Sequent
                                        ((Kt.BCirc (Kt.Star (Kt.FSf a))),
                                        (Kt.Star x)))))
                                    (premsRule eqDec_formula f_Kt_log kt_log
                                      eqDec_structr f_Kt kt_str
                                      KtRules.coq_Sns)) (ForallT_cons
                                  ((seqSubst eqDec_formula f_Kt_log kt_log
                                     eqDec_structr f_Kt kt_str
                                     (seq_matchsub eqDec_formula f_Kt_log
                                       kt_log eqDec_structr f_Kt kt_str
                                       (conclRule eqDec_formula f_Kt_log
                                         kt_log eqDec_structr f_Kt kt_str
                                         KtRules.coq_Sns) (Sequent ((Kt.BCirc
                                       (Kt.Star (Kt.FSf a))), (Kt.Star x))))
                                     (Sequent ((Kt.SVf "X"), (Kt.Star (Kt.SVf
                                     "Y"))))), [], hders1, ForallT_nil)))),
                              ForallT_nil)))), ForallT_nil)))), (ForallT_cons
                      ((Sequent ((Kt.FSf a), y)), [], hders3, ForallT_nil)))))),
                  ForallT_nil)))), ForallT_nil)))), ForallT_nil)))) ld

  (** val coq_C8_Diap :
      Kt.structr -> Kt.structr -> Kt.formula -> (Kt.formula, Kt.structr)
      dertree list -> (Kt.formula, Kt.structr) dertree **)

  let coq_C8_Diap x y a ld =
    c8_case_alt_imp_C8_case eqDec_formula f_Kt_log kt_log eqDec_structr f_Kt
      kt_str kt_DC (Kt.BCirc x) y ((Sequent (x, (Kt.FSf a)))::((Sequent
      ((Kt.FSf a), (Kt.BCirc y)))::[])) (fun hders ->
      let x0 = fun dC cs ->
        let _,x0 =
          forallT_deriv_cofseqs_iff eqDec_formula f_Kt_log kt_log
            eqDec_structr f_Kt kt_str dC cs
        in
        x0
      in
      let hders0 =
        x0 kt_DC ((Sequent (x, (Kt.FSf a)))::((Sequent ((Kt.FSf a), (Kt.BCirc
          y)))::[])) hders
      in
      let hders1 =
        forallT_inv (Sequent (x, (Kt.FSf a))) ((Sequent ((Kt.FSf a),
          (Kt.BCirc y)))::[]) hders0
      in
      let hders2 =
        forallT_inv_tail (Sequent (x, (Kt.FSf a))) ((Sequent ((Kt.FSf a),
          (Kt.BCirc y)))::[]) hders0
      in
      let hders3 = forallT_inv (Sequent ((Kt.FSf a), (Kt.BCirc y))) [] hders2
      in
      deriv_cofseq_rule_bw_inDC eqDec_formula f_Kt_log kt_log eqDec_structr
        f_Kt kt_str kt_DC
        (premsRule eqDec_formula f_Kt_log kt_log eqDec_structr f_Kt kt_str
          KtRules.coq_Scr)
        (conclRule eqDec_formula f_Kt_log kt_log eqDec_structr f_Kt kt_str
          KtRules.coq_Scr)
        (seq_matchsub eqDec_formula f_Kt_log kt_log eqDec_structr f_Kt kt_str
          (conclRule eqDec_formula f_Kt_log kt_log eqDec_structr f_Kt kt_str
            KtRules.coq_Scr) (Sequent ((Kt.BCirc x), y)))
        (forallT_deriv_cofseqs eqDec_formula f_Kt_log kt_log eqDec_structr
          f_Kt kt_str kt_DC
          (map
            (seqSubst eqDec_formula f_Kt_log kt_log eqDec_structr f_Kt kt_str
              (seq_matchsub eqDec_formula f_Kt_log kt_log eqDec_structr f_Kt
                kt_str
                (conclRule eqDec_formula f_Kt_log kt_log eqDec_structr f_Kt
                  kt_str KtRules.coq_Scr) (Sequent ((Kt.BCirc x), y))))
            (premsRule eqDec_formula f_Kt_log kt_log eqDec_structr f_Kt
              kt_str KtRules.coq_Scr)) (ForallT_cons
          ((seqSubst eqDec_formula f_Kt_log kt_log eqDec_structr f_Kt kt_str
             (seq_matchsub eqDec_formula f_Kt_log kt_log eqDec_structr f_Kt
               kt_str
               (conclRule eqDec_formula f_Kt_log kt_log eqDec_structr f_Kt
                 kt_str KtRules.coq_Scr) (Sequent ((Kt.BCirc x), y)))
             (Sequent ((Kt.SVf "X"), (Kt.BCirc (Kt.SVf "Y"))))), [],
          (deriv_cofseq_rule_bw_inDC eqDec_formula f_Kt_log kt_log
            eqDec_structr f_Kt kt_str kt_DC
            (premsRule eqDec_formula f_Kt_log kt_log eqDec_structr f_Kt
              kt_str
              (cUT eqDec_formula f_Kt_log kt_log eqDec_structr f_Kt kt_str))
            (conclRule eqDec_formula f_Kt_log kt_log eqDec_structr f_Kt
              kt_str
              (cUT eqDec_formula f_Kt_log kt_log eqDec_structr f_Kt kt_str))
            (cUT_spec eqDec_formula f_Kt_log kt_log eqDec_structr f_Kt kt_str
              a x (Kt.BCirc y))
            (forallT_deriv_cofseqs eqDec_formula f_Kt_log kt_log
              eqDec_structr f_Kt kt_str kt_DC ((Sequent (x, (Kt.FSf
              a)))::((Sequent ((Kt.FSf a), (Kt.BCirc y)))::[])) (ForallT_cons
              ((Sequent (x, (Kt.FSf a))), ((Sequent ((Kt.FSf a), (Kt.BCirc
              y)))::[]), hders1, (ForallT_cons ((Sequent ((Kt.FSf a),
              (Kt.BCirc y))), [], hders3, ForallT_nil)))))), ForallT_nil))))
      ld

  (** val coq_C8_holds :
      Kt.formula -> (Kt.formula, Kt.structr) dertree -> (Kt.formula,
      Kt.structr) dertree **)

  let coq_C8_holds m dt =
    reduce_C8 eqDec_formula f_Kt_log kt_log eqDec_structr f_Kt kt_str kt_DC
      (fun a _ x y rL lL rR lR _ _ _ _ _ _ _ _ ->
      eq_dec_in_list
        (eqdec
          (eqDec_rule eqDec_formula f_Kt_log kt_log eqDec_structr f_Kt kt_str))
        (atrefl eqDec_formula f_Kt_log kt_log eqDec_structr f_Kt kt_str)
        (KtRules.coq_Topr::(KtRules.coq_Botr::(KtRules.coq_Negr::(KtRules.coq_Conr::(KtRules.coq_Disr::(KtRules.coq_Impr::(KtRules.coq_Boxnr::(KtRules.coq_Dianr::(KtRules.coq_Boxpr::(KtRules.coq_Diapr::[]))))))))))
        rL (fun _ ->
        eq_dec_in_list
          (eqdec
            (eqDec_rule eqDec_formula f_Kt_log kt_log eqDec_structr f_Kt
              kt_str))
          (atrefl eqDec_formula f_Kt_log kt_log eqDec_structr f_Kt kt_str)
          (KtRules.coq_Topl::(KtRules.coq_Botl::(KtRules.coq_Negl::(KtRules.coq_Conl::(KtRules.coq_Disl::(KtRules.coq_Impl::(KtRules.coq_Boxnl::(KtRules.coq_Dianl::(KtRules.coq_Boxpl::(KtRules.coq_Diapl::[]))))))))))
          rR (fun _ ->
          let hwfrR =
            ruleInst_ruleSubst eqDec_formula f_Kt_log kt_log eqDec_structr
              f_Kt kt_str rR
              ((map
                 (conclDT eqDec_formula f_Kt_log kt_log eqDec_structr f_Kt
                   kt_str) lR),(Sequent ((kt_str.fS a), y)))
          in
          (match lL with
           | [] ->
             (match lR with
              | [] ->
                let p = fst (fst hwfrR) "p" in
                Der ((Sequent ((Kt.FSf (Kt.Atf p)), (Kt.FSf (Kt.Atf p)))),
                (atrefl eqDec_formula f_Kt_log kt_log eqDec_structr f_Kt
                  kt_str), [])
              | _::_ -> assert false (* absurd case *))
           | _::_ -> assert false (* absurd case *))) (fun _ ->
          eq_dec_in_list
            (eqdec
              (eqDec_rule eqDec_formula f_Kt_log kt_log eqDec_structr f_Kt
                kt_str)) KtRules.coq_Topl
            (KtRules.coq_Botl::(KtRules.coq_Negl::(KtRules.coq_Conl::(KtRules.coq_Disl::(KtRules.coq_Impl::(KtRules.coq_Boxnl::(KtRules.coq_Dianl::(KtRules.coq_Boxpl::(KtRules.coq_Diapl::[])))))))))
            rR (fun _ -> assert false (* absurd case *)) (fun _ ->
            eq_dec_in_list
              (eqdec
                (eqDec_rule eqDec_formula f_Kt_log kt_log eqDec_structr f_Kt
                  kt_str)) KtRules.coq_Botl
              (KtRules.coq_Negl::(KtRules.coq_Conl::(KtRules.coq_Disl::(KtRules.coq_Impl::(KtRules.coq_Boxnl::(KtRules.coq_Dianl::(KtRules.coq_Boxpl::(KtRules.coq_Diapl::[]))))))))
              rR (fun _ -> assert false (* absurd case *)) (fun _ ->
              eq_dec_in_list
                (eqdec
                  (eqDec_rule eqDec_formula f_Kt_log kt_log eqDec_structr
                    f_Kt kt_str)) KtRules.coq_Negl
                (KtRules.coq_Conl::(KtRules.coq_Disl::(KtRules.coq_Impl::(KtRules.coq_Boxnl::(KtRules.coq_Dianl::(KtRules.coq_Boxpl::(KtRules.coq_Diapl::[])))))))
                rR (fun _ -> assert false (* absurd case *)) (fun _ ->
                eq_dec_in_list
                  (eqdec
                    (eqDec_rule eqDec_formula f_Kt_log kt_log eqDec_structr
                      f_Kt kt_str)) KtRules.coq_Conl
                  (KtRules.coq_Disl::(KtRules.coq_Impl::(KtRules.coq_Boxnl::(KtRules.coq_Dianl::(KtRules.coq_Boxpl::(KtRules.coq_Diapl::[]))))))
                  rR (fun _ -> assert false (* absurd case *)) (fun _ ->
                  eq_dec_in_list
                    (eqdec
                      (eqDec_rule eqDec_formula f_Kt_log kt_log eqDec_structr
                        f_Kt kt_str)) KtRules.coq_Disl
                    (KtRules.coq_Impl::(KtRules.coq_Boxnl::(KtRules.coq_Dianl::(KtRules.coq_Boxpl::(KtRules.coq_Diapl::[])))))
                    rR (fun _ -> assert false (* absurd case *)) (fun _ ->
                    eq_dec_in_list
                      (eqdec
                        (eqDec_rule eqDec_formula f_Kt_log kt_log
                          eqDec_structr f_Kt kt_str)) KtRules.coq_Impl
                      (KtRules.coq_Boxnl::(KtRules.coq_Dianl::(KtRules.coq_Boxpl::(KtRules.coq_Diapl::[]))))
                      rR (fun _ -> assert false (* absurd case *)) (fun _ ->
                      eq_dec_in_list
                        (eqdec
                          (eqDec_rule eqDec_formula f_Kt_log kt_log
                            eqDec_structr f_Kt kt_str)) KtRules.coq_Boxnl
                        (KtRules.coq_Dianl::(KtRules.coq_Boxpl::(KtRules.coq_Diapl::[])))
                        rR (fun _ -> assert false (* absurd case *))
                        (fun _ ->
                        eq_dec_in_list
                          (eqdec
                            (eqDec_rule eqDec_formula f_Kt_log kt_log
                              eqDec_structr f_Kt kt_str)) KtRules.coq_Dianl
                          (KtRules.coq_Boxpl::(KtRules.coq_Diapl::[])) rR
                          (fun _ -> assert false (* absurd case *)) (fun _ ->
                          eq_dec_in_list
                            (eqdec
                              (eqDec_rule eqDec_formula f_Kt_log kt_log
                                eqDec_structr f_Kt kt_str)) KtRules.coq_Boxpl
                            (KtRules.coq_Diapl::[]) rR (fun _ -> assert false
                            (* absurd case *)) (fun _ ->
                            eq_dec_in_list
                              (eqdec
                                (eqDec_rule eqDec_formula f_Kt_log kt_log
                                  eqDec_structr f_Kt kt_str))
                              KtRules.coq_Diapl [] rR (fun _ -> assert false
                              (* absurd case *)) (fun _ -> assert false
                              (* absurd case *))))))))))))) (fun _ ->
        eq_dec_in_list
          (eqdec
            (eqDec_rule eqDec_formula f_Kt_log kt_log eqDec_structr f_Kt
              kt_str)) KtRules.coq_Topr
          (KtRules.coq_Botr::(KtRules.coq_Negr::(KtRules.coq_Conr::(KtRules.coq_Disr::(KtRules.coq_Impr::(KtRules.coq_Boxnr::(KtRules.coq_Dianr::(KtRules.coq_Boxpr::(KtRules.coq_Diapr::[])))))))))
          rL (fun _ ->
          eq_dec_in_list
            (eqdec
              (eqDec_rule eqDec_formula f_Kt_log kt_log eqDec_structr f_Kt
                kt_str))
            (atrefl eqDec_formula f_Kt_log kt_log eqDec_structr f_Kt kt_str)
            (KtRules.coq_Topl::(KtRules.coq_Botl::(KtRules.coq_Negl::(KtRules.coq_Conl::(KtRules.coq_Disl::(KtRules.coq_Impl::(KtRules.coq_Boxnl::(KtRules.coq_Dianl::(KtRules.coq_Boxpl::(KtRules.coq_Diapl::[]))))))))))
            rR (fun _ -> assert false (* absurd case *)) (fun _ ->
            eq_dec_in_list
              (eqdec
                (eqDec_rule eqDec_formula f_Kt_log kt_log eqDec_structr f_Kt
                  kt_str)) KtRules.coq_Topl
              (KtRules.coq_Botl::(KtRules.coq_Negl::(KtRules.coq_Conl::(KtRules.coq_Disl::(KtRules.coq_Impl::(KtRules.coq_Boxnl::(KtRules.coq_Dianl::(KtRules.coq_Boxpl::(KtRules.coq_Diapl::[])))))))))
              rR (fun _ ->
              match lL with
              | [] ->
                (match lR with
                 | [] -> assert false (* absurd case *)
                 | d::l ->
                   (match l with
                    | [] -> d
                    | _::_ -> assert false (* absurd case *)))
              | _::_ -> assert false (* absurd case *)) (fun _ ->
              eq_dec_in_list
                (eqdec
                  (eqDec_rule eqDec_formula f_Kt_log kt_log eqDec_structr
                    f_Kt kt_str)) KtRules.coq_Botl
                (KtRules.coq_Negl::(KtRules.coq_Conl::(KtRules.coq_Disl::(KtRules.coq_Impl::(KtRules.coq_Boxnl::(KtRules.coq_Dianl::(KtRules.coq_Boxpl::(KtRules.coq_Diapl::[]))))))))
                rR (fun _ -> assert false (* absurd case *)) (fun _ ->
                eq_dec_in_list
                  (eqdec
                    (eqDec_rule eqDec_formula f_Kt_log kt_log eqDec_structr
                      f_Kt kt_str)) KtRules.coq_Negl
                  (KtRules.coq_Conl::(KtRules.coq_Disl::(KtRules.coq_Impl::(KtRules.coq_Boxnl::(KtRules.coq_Dianl::(KtRules.coq_Boxpl::(KtRules.coq_Diapl::[])))))))
                  rR (fun _ -> assert false (* absurd case *)) (fun _ ->
                  eq_dec_in_list
                    (eqdec
                      (eqDec_rule eqDec_formula f_Kt_log kt_log eqDec_structr
                        f_Kt kt_str)) KtRules.coq_Conl
                    (KtRules.coq_Disl::(KtRules.coq_Impl::(KtRules.coq_Boxnl::(KtRules.coq_Dianl::(KtRules.coq_Boxpl::(KtRules.coq_Diapl::[]))))))
                    rR (fun _ -> assert false (* absurd case *)) (fun _ ->
                    eq_dec_in_list
                      (eqdec
                        (eqDec_rule eqDec_formula f_Kt_log kt_log
                          eqDec_structr f_Kt kt_str)) KtRules.coq_Disl
                      (KtRules.coq_Impl::(KtRules.coq_Boxnl::(KtRules.coq_Dianl::(KtRules.coq_Boxpl::(KtRules.coq_Diapl::[])))))
                      rR (fun _ -> assert false (* absurd case *)) (fun _ ->
                      eq_dec_in_list
                        (eqdec
                          (eqDec_rule eqDec_formula f_Kt_log kt_log
                            eqDec_structr f_Kt kt_str)) KtRules.coq_Impl
                        (KtRules.coq_Boxnl::(KtRules.coq_Dianl::(KtRules.coq_Boxpl::(KtRules.coq_Diapl::[]))))
                        rR (fun _ -> assert false (* absurd case *))
                        (fun _ ->
                        eq_dec_in_list
                          (eqdec
                            (eqDec_rule eqDec_formula f_Kt_log kt_log
                              eqDec_structr f_Kt kt_str)) KtRules.coq_Boxnl
                          (KtRules.coq_Dianl::(KtRules.coq_Boxpl::(KtRules.coq_Diapl::[])))
                          rR (fun _ -> assert false (* absurd case *))
                          (fun _ ->
                          eq_dec_in_list
                            (eqdec
                              (eqDec_rule eqDec_formula f_Kt_log kt_log
                                eqDec_structr f_Kt kt_str)) KtRules.coq_Dianl
                            (KtRules.coq_Boxpl::(KtRules.coq_Diapl::[])) rR
                            (fun _ -> assert false (* absurd case *))
                            (fun _ ->
                            eq_dec_in_list
                              (eqdec
                                (eqDec_rule eqDec_formula f_Kt_log kt_log
                                  eqDec_structr f_Kt kt_str))
                              KtRules.coq_Boxpl (KtRules.coq_Diapl::[]) rR
                              (fun _ -> assert false (* absurd case *))
                              (fun _ ->
                              eq_dec_in_list
                                (eqdec
                                  (eqDec_rule eqDec_formula f_Kt_log kt_log
                                    eqDec_structr f_Kt kt_str))
                                KtRules.coq_Diapl [] rR (fun _ ->
                                assert false (* absurd case *)) (fun _ ->
                                assert false (* absurd case *)))))))))))))
          (fun _ ->
          eq_dec_in_list
            (eqdec
              (eqDec_rule eqDec_formula f_Kt_log kt_log eqDec_structr f_Kt
                kt_str)) KtRules.coq_Botr
            (KtRules.coq_Negr::(KtRules.coq_Conr::(KtRules.coq_Disr::(KtRules.coq_Impr::(KtRules.coq_Boxnr::(KtRules.coq_Dianr::(KtRules.coq_Boxpr::(KtRules.coq_Diapr::[]))))))))
            rL (fun _ ->
            eq_dec_in_list
              (eqdec
                (eqDec_rule eqDec_formula f_Kt_log kt_log eqDec_structr f_Kt
                  kt_str))
              (atrefl eqDec_formula f_Kt_log kt_log eqDec_structr f_Kt kt_str)
              (KtRules.coq_Topl::(KtRules.coq_Botl::(KtRules.coq_Negl::(KtRules.coq_Conl::(KtRules.coq_Disl::(KtRules.coq_Impl::(KtRules.coq_Boxnl::(KtRules.coq_Dianl::(KtRules.coq_Boxpl::(KtRules.coq_Diapl::[]))))))))))
              rR (fun _ -> assert false (* absurd case *)) (fun _ ->
              eq_dec_in_list
                (eqdec
                  (eqDec_rule eqDec_formula f_Kt_log kt_log eqDec_structr
                    f_Kt kt_str)) KtRules.coq_Topl
                (KtRules.coq_Botl::(KtRules.coq_Negl::(KtRules.coq_Conl::(KtRules.coq_Disl::(KtRules.coq_Impl::(KtRules.coq_Boxnl::(KtRules.coq_Dianl::(KtRules.coq_Boxpl::(KtRules.coq_Diapl::[])))))))))
                rR (fun _ -> assert false (* absurd case *)) (fun _ ->
                eq_dec_in_list
                  (eqdec
                    (eqDec_rule eqDec_formula f_Kt_log kt_log eqDec_structr
                      f_Kt kt_str)) KtRules.coq_Botl
                  (KtRules.coq_Negl::(KtRules.coq_Conl::(KtRules.coq_Disl::(KtRules.coq_Impl::(KtRules.coq_Boxnl::(KtRules.coq_Dianl::(KtRules.coq_Boxpl::(KtRules.coq_Diapl::[]))))))))
                  rR (fun _ ->
                  match lL with
                  | [] -> assert false (* absurd case *)
                  | d::l ->
                    (match l with
                     | [] ->
                       (match lR with
                        | [] -> d
                        | _::_ -> assert false (* absurd case *))
                     | _::_ -> assert false (* absurd case *))) (fun _ ->
                  eq_dec_in_list
                    (eqdec
                      (eqDec_rule eqDec_formula f_Kt_log kt_log eqDec_structr
                        f_Kt kt_str)) KtRules.coq_Negl
                    (KtRules.coq_Conl::(KtRules.coq_Disl::(KtRules.coq_Impl::(KtRules.coq_Boxnl::(KtRules.coq_Dianl::(KtRules.coq_Boxpl::(KtRules.coq_Diapl::[])))))))
                    rR (fun _ -> assert false (* absurd case *)) (fun _ ->
                    eq_dec_in_list
                      (eqdec
                        (eqDec_rule eqDec_formula f_Kt_log kt_log
                          eqDec_structr f_Kt kt_str)) KtRules.coq_Conl
                      (KtRules.coq_Disl::(KtRules.coq_Impl::(KtRules.coq_Boxnl::(KtRules.coq_Dianl::(KtRules.coq_Boxpl::(KtRules.coq_Diapl::[]))))))
                      rR (fun _ -> assert false (* absurd case *)) (fun _ ->
                      eq_dec_in_list
                        (eqdec
                          (eqDec_rule eqDec_formula f_Kt_log kt_log
                            eqDec_structr f_Kt kt_str)) KtRules.coq_Disl
                        (KtRules.coq_Impl::(KtRules.coq_Boxnl::(KtRules.coq_Dianl::(KtRules.coq_Boxpl::(KtRules.coq_Diapl::[])))))
                        rR (fun _ -> assert false (* absurd case *))
                        (fun _ ->
                        eq_dec_in_list
                          (eqdec
                            (eqDec_rule eqDec_formula f_Kt_log kt_log
                              eqDec_structr f_Kt kt_str)) KtRules.coq_Impl
                          (KtRules.coq_Boxnl::(KtRules.coq_Dianl::(KtRules.coq_Boxpl::(KtRules.coq_Diapl::[]))))
                          rR (fun _ -> assert false (* absurd case *))
                          (fun _ ->
                          eq_dec_in_list
                            (eqdec
                              (eqDec_rule eqDec_formula f_Kt_log kt_log
                                eqDec_structr f_Kt kt_str)) KtRules.coq_Boxnl
                            (KtRules.coq_Dianl::(KtRules.coq_Boxpl::(KtRules.coq_Diapl::[])))
                            rR (fun _ -> assert false (* absurd case *))
                            (fun _ ->
                            eq_dec_in_list
                              (eqdec
                                (eqDec_rule eqDec_formula f_Kt_log kt_log
                                  eqDec_structr f_Kt kt_str))
                              KtRules.coq_Dianl
                              (KtRules.coq_Boxpl::(KtRules.coq_Diapl::[])) rR
                              (fun _ -> assert false (* absurd case *))
                              (fun _ ->
                              eq_dec_in_list
                                (eqdec
                                  (eqDec_rule eqDec_formula f_Kt_log kt_log
                                    eqDec_structr f_Kt kt_str))
                                KtRules.coq_Boxpl (KtRules.coq_Diapl::[]) rR
                                (fun _ -> assert false (* absurd case *))
                                (fun _ ->
                                eq_dec_in_list
                                  (eqdec
                                    (eqDec_rule eqDec_formula f_Kt_log kt_log
                                      eqDec_structr f_Kt kt_str))
                                  KtRules.coq_Diapl [] rR (fun _ ->
                                  assert false (* absurd case *)) (fun _ ->
                                  assert false (* absurd case *)))))))))))))
            (fun _ ->
            eq_dec_in_list
              (eqdec
                (eqDec_rule eqDec_formula f_Kt_log kt_log eqDec_structr f_Kt
                  kt_str)) KtRules.coq_Negr
              (KtRules.coq_Conr::(KtRules.coq_Disr::(KtRules.coq_Impr::(KtRules.coq_Boxnr::(KtRules.coq_Dianr::(KtRules.coq_Boxpr::(KtRules.coq_Diapr::[])))))))
              rL (fun _ ->
              eq_dec_in_list
                (eqdec
                  (eqDec_rule eqDec_formula f_Kt_log kt_log eqDec_structr
                    f_Kt kt_str))
                (atrefl eqDec_formula f_Kt_log kt_log eqDec_structr f_Kt
                  kt_str)
                (KtRules.coq_Topl::(KtRules.coq_Botl::(KtRules.coq_Negl::(KtRules.coq_Conl::(KtRules.coq_Disl::(KtRules.coq_Impl::(KtRules.coq_Boxnl::(KtRules.coq_Dianl::(KtRules.coq_Boxpl::(KtRules.coq_Diapl::[]))))))))))
                rR (fun _ -> assert false (* absurd case *)) (fun _ ->
                eq_dec_in_list
                  (eqdec
                    (eqDec_rule eqDec_formula f_Kt_log kt_log eqDec_structr
                      f_Kt kt_str)) KtRules.coq_Topl
                  (KtRules.coq_Botl::(KtRules.coq_Negl::(KtRules.coq_Conl::(KtRules.coq_Disl::(KtRules.coq_Impl::(KtRules.coq_Boxnl::(KtRules.coq_Dianl::(KtRules.coq_Boxpl::(KtRules.coq_Diapl::[])))))))))
                  rR (fun _ -> assert false (* absurd case *)) (fun _ ->
                  eq_dec_in_list
                    (eqdec
                      (eqDec_rule eqDec_formula f_Kt_log kt_log eqDec_structr
                        f_Kt kt_str)) KtRules.coq_Botl
                    (KtRules.coq_Negl::(KtRules.coq_Conl::(KtRules.coq_Disl::(KtRules.coq_Impl::(KtRules.coq_Boxnl::(KtRules.coq_Dianl::(KtRules.coq_Boxpl::(KtRules.coq_Diapl::[]))))))))
                    rR (fun _ -> assert false (* absurd case *)) (fun _ ->
                    eq_dec_in_list
                      (eqdec
                        (eqDec_rule eqDec_formula f_Kt_log kt_log
                          eqDec_structr f_Kt kt_str)) KtRules.coq_Negl
                      (KtRules.coq_Conl::(KtRules.coq_Disl::(KtRules.coq_Impl::(KtRules.coq_Boxnl::(KtRules.coq_Dianl::(KtRules.coq_Boxpl::(KtRules.coq_Diapl::[])))))))
                      rR (fun _ ->
                      let hwfrL =
                        ruleInst_ruleSubst eqDec_formula f_Kt_log kt_log
                          eqDec_structr f_Kt kt_str rL
                          ((map
                             (conclDT eqDec_formula f_Kt_log kt_log
                               eqDec_structr f_Kt kt_str) lL),(Sequent (x,
                          (kt_str.fS a))))
                      in
                      let hwfrR =
                        ruleInst_ruleSubst eqDec_formula f_Kt_log kt_log
                          eqDec_structr f_Kt kt_str rR
                          ((map
                             (conclDT eqDec_formula f_Kt_log kt_log
                               eqDec_structr f_Kt kt_str) lR),(Sequent
                          ((kt_str.fS a), y)))
                      in
                      (match lL with
                       | [] -> assert false (* absurd case *)
                       | d::l ->
                         (match l with
                          | [] ->
                            (match lR with
                             | [] -> assert false (* absurd case *)
                             | d0::l0 ->
                               (match l0 with
                                | [] ->
                                  coq_C8_Neg (snd hwfrL "X") (snd hwfrR "X")
                                    (snd (fst hwfrR) "A") (d::(d0::[]))
                                | _::_ -> assert false (* absurd case *)))
                          | _::_ -> assert false (* absurd case *))))
                      (fun _ ->
                      eq_dec_in_list
                        (eqdec
                          (eqDec_rule eqDec_formula f_Kt_log kt_log
                            eqDec_structr f_Kt kt_str)) KtRules.coq_Conl
                        (KtRules.coq_Disl::(KtRules.coq_Impl::(KtRules.coq_Boxnl::(KtRules.coq_Dianl::(KtRules.coq_Boxpl::(KtRules.coq_Diapl::[]))))))
                        rR (fun _ -> assert false (* absurd case *))
                        (fun _ ->
                        eq_dec_in_list
                          (eqdec
                            (eqDec_rule eqDec_formula f_Kt_log kt_log
                              eqDec_structr f_Kt kt_str)) KtRules.coq_Disl
                          (KtRules.coq_Impl::(KtRules.coq_Boxnl::(KtRules.coq_Dianl::(KtRules.coq_Boxpl::(KtRules.coq_Diapl::[])))))
                          rR (fun _ -> assert false (* absurd case *))
                          (fun _ ->
                          eq_dec_in_list
                            (eqdec
                              (eqDec_rule eqDec_formula f_Kt_log kt_log
                                eqDec_structr f_Kt kt_str)) KtRules.coq_Impl
                            (KtRules.coq_Boxnl::(KtRules.coq_Dianl::(KtRules.coq_Boxpl::(KtRules.coq_Diapl::[]))))
                            rR (fun _ -> assert false (* absurd case *))
                            (fun _ ->
                            eq_dec_in_list
                              (eqdec
                                (eqDec_rule eqDec_formula f_Kt_log kt_log
                                  eqDec_structr f_Kt kt_str))
                              KtRules.coq_Boxnl
                              (KtRules.coq_Dianl::(KtRules.coq_Boxpl::(KtRules.coq_Diapl::[])))
                              rR (fun _ -> assert false (* absurd case *))
                              (fun _ ->
                              eq_dec_in_list
                                (eqdec
                                  (eqDec_rule eqDec_formula f_Kt_log kt_log
                                    eqDec_structr f_Kt kt_str))
                                KtRules.coq_Dianl
                                (KtRules.coq_Boxpl::(KtRules.coq_Diapl::[]))
                                rR (fun _ -> assert false (* absurd case *))
                                (fun _ ->
                                eq_dec_in_list
                                  (eqdec
                                    (eqDec_rule eqDec_formula f_Kt_log kt_log
                                      eqDec_structr f_Kt kt_str))
                                  KtRules.coq_Boxpl (KtRules.coq_Diapl::[])
                                  rR (fun _ -> assert false
                                  (* absurd case *)) (fun _ ->
                                  eq_dec_in_list
                                    (eqdec
                                      (eqDec_rule eqDec_formula f_Kt_log
                                        kt_log eqDec_structr f_Kt kt_str))
                                    KtRules.coq_Diapl [] rR (fun _ ->
                                    assert false (* absurd case *)) (fun _ ->
                                    assert false (* absurd case *)))))))))))))
              (fun _ ->
              eq_dec_in_list
                (eqdec
                  (eqDec_rule eqDec_formula f_Kt_log kt_log eqDec_structr
                    f_Kt kt_str)) KtRules.coq_Conr
                (KtRules.coq_Disr::(KtRules.coq_Impr::(KtRules.coq_Boxnr::(KtRules.coq_Dianr::(KtRules.coq_Boxpr::(KtRules.coq_Diapr::[]))))))
                rL (fun _ ->
                eq_dec_in_list
                  (eqdec
                    (eqDec_rule eqDec_formula f_Kt_log kt_log eqDec_structr
                      f_Kt kt_str))
                  (atrefl eqDec_formula f_Kt_log kt_log eqDec_structr f_Kt
                    kt_str)
                  (KtRules.coq_Topl::(KtRules.coq_Botl::(KtRules.coq_Negl::(KtRules.coq_Conl::(KtRules.coq_Disl::(KtRules.coq_Impl::(KtRules.coq_Boxnl::(KtRules.coq_Dianl::(KtRules.coq_Boxpl::(KtRules.coq_Diapl::[]))))))))))
                  rR (fun _ -> assert false (* absurd case *)) (fun _ ->
                  eq_dec_in_list
                    (eqdec
                      (eqDec_rule eqDec_formula f_Kt_log kt_log eqDec_structr
                        f_Kt kt_str)) KtRules.coq_Topl
                    (KtRules.coq_Botl::(KtRules.coq_Negl::(KtRules.coq_Conl::(KtRules.coq_Disl::(KtRules.coq_Impl::(KtRules.coq_Boxnl::(KtRules.coq_Dianl::(KtRules.coq_Boxpl::(KtRules.coq_Diapl::[])))))))))
                    rR (fun _ -> assert false (* absurd case *)) (fun _ ->
                    eq_dec_in_list
                      (eqdec
                        (eqDec_rule eqDec_formula f_Kt_log kt_log
                          eqDec_structr f_Kt kt_str)) KtRules.coq_Botl
                      (KtRules.coq_Negl::(KtRules.coq_Conl::(KtRules.coq_Disl::(KtRules.coq_Impl::(KtRules.coq_Boxnl::(KtRules.coq_Dianl::(KtRules.coq_Boxpl::(KtRules.coq_Diapl::[]))))))))
                      rR (fun _ -> assert false (* absurd case *)) (fun _ ->
                      eq_dec_in_list
                        (eqdec
                          (eqDec_rule eqDec_formula f_Kt_log kt_log
                            eqDec_structr f_Kt kt_str)) KtRules.coq_Negl
                        (KtRules.coq_Conl::(KtRules.coq_Disl::(KtRules.coq_Impl::(KtRules.coq_Boxnl::(KtRules.coq_Dianl::(KtRules.coq_Boxpl::(KtRules.coq_Diapl::[])))))))
                        rR (fun _ -> assert false (* absurd case *))
                        (fun _ ->
                        eq_dec_in_list
                          (eqdec
                            (eqDec_rule eqDec_formula f_Kt_log kt_log
                              eqDec_structr f_Kt kt_str)) KtRules.coq_Conl
                          (KtRules.coq_Disl::(KtRules.coq_Impl::(KtRules.coq_Boxnl::(KtRules.coq_Dianl::(KtRules.coq_Boxpl::(KtRules.coq_Diapl::[]))))))
                          rR (fun _ ->
                          let hwfrL =
                            ruleInst_ruleSubst eqDec_formula f_Kt_log kt_log
                              eqDec_structr f_Kt kt_str rL
                              ((map
                                 (conclDT eqDec_formula f_Kt_log kt_log
                                   eqDec_structr f_Kt kt_str) lL),(Sequent
                              (x, (kt_str.fS a))))
                          in
                          let hwfrR =
                            ruleInst_ruleSubst eqDec_formula f_Kt_log kt_log
                              eqDec_structr f_Kt kt_str rR
                              ((map
                                 (conclDT eqDec_formula f_Kt_log kt_log
                                   eqDec_structr f_Kt kt_str) lR),(Sequent
                              ((kt_str.fS a), y)))
                          in
                          (match lL with
                           | [] -> assert false (* absurd case *)
                           | d::l ->
                             (match l with
                              | [] -> assert false (* absurd case *)
                              | d0::l0 ->
                                (match l0 with
                                 | [] ->
                                   (match lR with
                                    | [] -> assert false (* absurd case *)
                                    | d1::l1 ->
                                      (match l1 with
                                       | [] ->
                                         coq_C8_Con (snd hwfrL "X")
                                           (snd hwfrL "Y") (snd hwfrR "X")
                                           (snd (fst hwfrR) "A")
                                           (snd (fst hwfrR) "B")
                                           (d::(d0::(d1::[])))
                                       | _::_ ->
                                         assert false (* absurd case *)))
                                 | _::_ -> assert false (* absurd case *)))))
                          (fun _ ->
                          eq_dec_in_list
                            (eqdec
                              (eqDec_rule eqDec_formula f_Kt_log kt_log
                                eqDec_structr f_Kt kt_str)) KtRules.coq_Disl
                            (KtRules.coq_Impl::(KtRules.coq_Boxnl::(KtRules.coq_Dianl::(KtRules.coq_Boxpl::(KtRules.coq_Diapl::[])))))
                            rR (fun _ -> assert false (* absurd case *))
                            (fun _ ->
                            eq_dec_in_list
                              (eqdec
                                (eqDec_rule eqDec_formula f_Kt_log kt_log
                                  eqDec_structr f_Kt kt_str))
                              KtRules.coq_Impl
                              (KtRules.coq_Boxnl::(KtRules.coq_Dianl::(KtRules.coq_Boxpl::(KtRules.coq_Diapl::[]))))
                              rR (fun _ -> assert false (* absurd case *))
                              (fun _ ->
                              eq_dec_in_list
                                (eqdec
                                  (eqDec_rule eqDec_formula f_Kt_log kt_log
                                    eqDec_structr f_Kt kt_str))
                                KtRules.coq_Boxnl
                                (KtRules.coq_Dianl::(KtRules.coq_Boxpl::(KtRules.coq_Diapl::[])))
                                rR (fun _ -> assert false (* absurd case *))
                                (fun _ ->
                                eq_dec_in_list
                                  (eqdec
                                    (eqDec_rule eqDec_formula f_Kt_log kt_log
                                      eqDec_structr f_Kt kt_str))
                                  KtRules.coq_Dianl
                                  (KtRules.coq_Boxpl::(KtRules.coq_Diapl::[]))
                                  rR (fun _ -> assert false
                                  (* absurd case *)) (fun _ ->
                                  eq_dec_in_list
                                    (eqdec
                                      (eqDec_rule eqDec_formula f_Kt_log
                                        kt_log eqDec_structr f_Kt kt_str))
                                    KtRules.coq_Boxpl (KtRules.coq_Diapl::[])
                                    rR (fun _ -> assert false
                                    (* absurd case *)) (fun _ ->
                                    eq_dec_in_list
                                      (eqdec
                                        (eqDec_rule eqDec_formula f_Kt_log
                                          kt_log eqDec_structr f_Kt kt_str))
                                      KtRules.coq_Diapl [] rR (fun _ ->
                                      assert false (* absurd case *))
                                      (fun _ -> assert false
                                      (* absurd case *))))))))))))) (fun _ ->
                eq_dec_in_list
                  (eqdec
                    (eqDec_rule eqDec_formula f_Kt_log kt_log eqDec_structr
                      f_Kt kt_str)) KtRules.coq_Disr
                  (KtRules.coq_Impr::(KtRules.coq_Boxnr::(KtRules.coq_Dianr::(KtRules.coq_Boxpr::(KtRules.coq_Diapr::[])))))
                  rL (fun _ ->
                  eq_dec_in_list
                    (eqdec
                      (eqDec_rule eqDec_formula f_Kt_log kt_log eqDec_structr
                        f_Kt kt_str))
                    (atrefl eqDec_formula f_Kt_log kt_log eqDec_structr f_Kt
                      kt_str)
                    (KtRules.coq_Topl::(KtRules.coq_Botl::(KtRules.coq_Negl::(KtRules.coq_Conl::(KtRules.coq_Disl::(KtRules.coq_Impl::(KtRules.coq_Boxnl::(KtRules.coq_Dianl::(KtRules.coq_Boxpl::(KtRules.coq_Diapl::[]))))))))))
                    rR (fun _ -> assert false (* absurd case *)) (fun _ ->
                    eq_dec_in_list
                      (eqdec
                        (eqDec_rule eqDec_formula f_Kt_log kt_log
                          eqDec_structr f_Kt kt_str)) KtRules.coq_Topl
                      (KtRules.coq_Botl::(KtRules.coq_Negl::(KtRules.coq_Conl::(KtRules.coq_Disl::(KtRules.coq_Impl::(KtRules.coq_Boxnl::(KtRules.coq_Dianl::(KtRules.coq_Boxpl::(KtRules.coq_Diapl::[])))))))))
                      rR (fun _ -> assert false (* absurd case *)) (fun _ ->
                      eq_dec_in_list
                        (eqdec
                          (eqDec_rule eqDec_formula f_Kt_log kt_log
                            eqDec_structr f_Kt kt_str)) KtRules.coq_Botl
                        (KtRules.coq_Negl::(KtRules.coq_Conl::(KtRules.coq_Disl::(KtRules.coq_Impl::(KtRules.coq_Boxnl::(KtRules.coq_Dianl::(KtRules.coq_Boxpl::(KtRules.coq_Diapl::[]))))))))
                        rR (fun _ -> assert false (* absurd case *))
                        (fun _ ->
                        eq_dec_in_list
                          (eqdec
                            (eqDec_rule eqDec_formula f_Kt_log kt_log
                              eqDec_structr f_Kt kt_str)) KtRules.coq_Negl
                          (KtRules.coq_Conl::(KtRules.coq_Disl::(KtRules.coq_Impl::(KtRules.coq_Boxnl::(KtRules.coq_Dianl::(KtRules.coq_Boxpl::(KtRules.coq_Diapl::[])))))))
                          rR (fun _ -> assert false (* absurd case *))
                          (fun _ ->
                          eq_dec_in_list
                            (eqdec
                              (eqDec_rule eqDec_formula f_Kt_log kt_log
                                eqDec_structr f_Kt kt_str)) KtRules.coq_Conl
                            (KtRules.coq_Disl::(KtRules.coq_Impl::(KtRules.coq_Boxnl::(KtRules.coq_Dianl::(KtRules.coq_Boxpl::(KtRules.coq_Diapl::[]))))))
                            rR (fun _ -> assert false (* absurd case *))
                            (fun _ ->
                            eq_dec_in_list
                              (eqdec
                                (eqDec_rule eqDec_formula f_Kt_log kt_log
                                  eqDec_structr f_Kt kt_str))
                              KtRules.coq_Disl
                              (KtRules.coq_Impl::(KtRules.coq_Boxnl::(KtRules.coq_Dianl::(KtRules.coq_Boxpl::(KtRules.coq_Diapl::[])))))
                              rR (fun _ ->
                              let hwfrL =
                                ruleInst_ruleSubst eqDec_formula f_Kt_log
                                  kt_log eqDec_structr f_Kt kt_str rL
                                  ((map
                                     (conclDT eqDec_formula f_Kt_log kt_log
                                       eqDec_structr f_Kt kt_str) lL),(Sequent
                                  (x, (kt_str.fS a))))
                              in
                              let hwfrR =
                                ruleInst_ruleSubst eqDec_formula f_Kt_log
                                  kt_log eqDec_structr f_Kt kt_str rR
                                  ((map
                                     (conclDT eqDec_formula f_Kt_log kt_log
                                       eqDec_structr f_Kt kt_str) lR),(Sequent
                                  ((kt_str.fS a), y)))
                              in
                              (match lL with
                               | [] -> assert false (* absurd case *)
                               | d::l ->
                                 (match l with
                                  | [] ->
                                    (match lR with
                                     | [] -> assert false (* absurd case *)
                                     | d0::l0 ->
                                       (match l0 with
                                        | [] -> assert false (* absurd case *)
                                        | d1::l1 ->
                                          (match l1 with
                                           | [] ->
                                             coq_C8_Dis (snd hwfrL "X")
                                               (snd hwfrR "X")
                                               (snd hwfrR "Y")
                                               (snd (fst hwfrR) "A")
                                               (snd (fst hwfrR) "B")
                                               (d::(d0::(d1::[])))
                                           | _::_ ->
                                             assert false (* absurd case *))))
                                  | _::_ -> assert false (* absurd case *))))
                              (fun _ ->
                              eq_dec_in_list
                                (eqdec
                                  (eqDec_rule eqDec_formula f_Kt_log kt_log
                                    eqDec_structr f_Kt kt_str))
                                KtRules.coq_Impl
                                (KtRules.coq_Boxnl::(KtRules.coq_Dianl::(KtRules.coq_Boxpl::(KtRules.coq_Diapl::[]))))
                                rR (fun _ -> assert false (* absurd case *))
                                (fun _ ->
                                eq_dec_in_list
                                  (eqdec
                                    (eqDec_rule eqDec_formula f_Kt_log kt_log
                                      eqDec_structr f_Kt kt_str))
                                  KtRules.coq_Boxnl
                                  (KtRules.coq_Dianl::(KtRules.coq_Boxpl::(KtRules.coq_Diapl::[])))
                                  rR (fun _ -> assert false
                                  (* absurd case *)) (fun _ ->
                                  eq_dec_in_list
                                    (eqdec
                                      (eqDec_rule eqDec_formula f_Kt_log
                                        kt_log eqDec_structr f_Kt kt_str))
                                    KtRules.coq_Dianl
                                    (KtRules.coq_Boxpl::(KtRules.coq_Diapl::[]))
                                    rR (fun _ -> assert false
                                    (* absurd case *)) (fun _ ->
                                    eq_dec_in_list
                                      (eqdec
                                        (eqDec_rule eqDec_formula f_Kt_log
                                          kt_log eqDec_structr f_Kt kt_str))
                                      KtRules.coq_Boxpl
                                      (KtRules.coq_Diapl::[]) rR (fun _ ->
                                      assert false (* absurd case *))
                                      (fun _ ->
                                      eq_dec_in_list
                                        (eqdec
                                          (eqDec_rule eqDec_formula f_Kt_log
                                            kt_log eqDec_structr f_Kt kt_str))
                                        KtRules.coq_Diapl [] rR (fun _ ->
                                        assert false (* absurd case *))
                                        (fun _ -> assert false
                                        (* absurd case *)))))))))))))
                  (fun _ ->
                  eq_dec_in_list
                    (eqdec
                      (eqDec_rule eqDec_formula f_Kt_log kt_log eqDec_structr
                        f_Kt kt_str)) KtRules.coq_Impr
                    (KtRules.coq_Boxnr::(KtRules.coq_Dianr::(KtRules.coq_Boxpr::(KtRules.coq_Diapr::[]))))
                    rL (fun _ ->
                    eq_dec_in_list
                      (eqdec
                        (eqDec_rule eqDec_formula f_Kt_log kt_log
                          eqDec_structr f_Kt kt_str))
                      (atrefl eqDec_formula f_Kt_log kt_log eqDec_structr
                        f_Kt kt_str)
                      (KtRules.coq_Topl::(KtRules.coq_Botl::(KtRules.coq_Negl::(KtRules.coq_Conl::(KtRules.coq_Disl::(KtRules.coq_Impl::(KtRules.coq_Boxnl::(KtRules.coq_Dianl::(KtRules.coq_Boxpl::(KtRules.coq_Diapl::[]))))))))))
                      rR (fun _ -> assert false (* absurd case *)) (fun _ ->
                      eq_dec_in_list
                        (eqdec
                          (eqDec_rule eqDec_formula f_Kt_log kt_log
                            eqDec_structr f_Kt kt_str)) KtRules.coq_Topl
                        (KtRules.coq_Botl::(KtRules.coq_Negl::(KtRules.coq_Conl::(KtRules.coq_Disl::(KtRules.coq_Impl::(KtRules.coq_Boxnl::(KtRules.coq_Dianl::(KtRules.coq_Boxpl::(KtRules.coq_Diapl::[])))))))))
                        rR (fun _ -> assert false (* absurd case *))
                        (fun _ ->
                        eq_dec_in_list
                          (eqdec
                            (eqDec_rule eqDec_formula f_Kt_log kt_log
                              eqDec_structr f_Kt kt_str)) KtRules.coq_Botl
                          (KtRules.coq_Negl::(KtRules.coq_Conl::(KtRules.coq_Disl::(KtRules.coq_Impl::(KtRules.coq_Boxnl::(KtRules.coq_Dianl::(KtRules.coq_Boxpl::(KtRules.coq_Diapl::[]))))))))
                          rR (fun _ -> assert false (* absurd case *))
                          (fun _ ->
                          eq_dec_in_list
                            (eqdec
                              (eqDec_rule eqDec_formula f_Kt_log kt_log
                                eqDec_structr f_Kt kt_str)) KtRules.coq_Negl
                            (KtRules.coq_Conl::(KtRules.coq_Disl::(KtRules.coq_Impl::(KtRules.coq_Boxnl::(KtRules.coq_Dianl::(KtRules.coq_Boxpl::(KtRules.coq_Diapl::[])))))))
                            rR (fun _ -> assert false (* absurd case *))
                            (fun _ ->
                            eq_dec_in_list
                              (eqdec
                                (eqDec_rule eqDec_formula f_Kt_log kt_log
                                  eqDec_structr f_Kt kt_str))
                              KtRules.coq_Conl
                              (KtRules.coq_Disl::(KtRules.coq_Impl::(KtRules.coq_Boxnl::(KtRules.coq_Dianl::(KtRules.coq_Boxpl::(KtRules.coq_Diapl::[]))))))
                              rR (fun _ -> assert false (* absurd case *))
                              (fun _ ->
                              eq_dec_in_list
                                (eqdec
                                  (eqDec_rule eqDec_formula f_Kt_log kt_log
                                    eqDec_structr f_Kt kt_str))
                                KtRules.coq_Disl
                                (KtRules.coq_Impl::(KtRules.coq_Boxnl::(KtRules.coq_Dianl::(KtRules.coq_Boxpl::(KtRules.coq_Diapl::[])))))
                                rR (fun _ -> assert false (* absurd case *))
                                (fun _ ->
                                eq_dec_in_list
                                  (eqdec
                                    (eqDec_rule eqDec_formula f_Kt_log kt_log
                                      eqDec_structr f_Kt kt_str))
                                  KtRules.coq_Impl
                                  (KtRules.coq_Boxnl::(KtRules.coq_Dianl::(KtRules.coq_Boxpl::(KtRules.coq_Diapl::[]))))
                                  rR (fun _ ->
                                  let hwfrL =
                                    ruleInst_ruleSubst eqDec_formula f_Kt_log
                                      kt_log eqDec_structr f_Kt kt_str rL
                                      ((map
                                         (conclDT eqDec_formula f_Kt_log
                                           kt_log eqDec_structr f_Kt kt_str)
                                         lL),(Sequent (x, (kt_str.fS a))))
                                  in
                                  let hwfrR =
                                    ruleInst_ruleSubst eqDec_formula f_Kt_log
                                      kt_log eqDec_structr f_Kt kt_str rR
                                      ((map
                                         (conclDT eqDec_formula f_Kt_log
                                           kt_log eqDec_structr f_Kt kt_str)
                                         lR),(Sequent ((kt_str.fS a), y)))
                                  in
                                  (match lL with
                                   | [] -> assert false (* absurd case *)
                                   | d::l ->
                                     (match l with
                                      | [] ->
                                        (match lR with
                                         | [] ->
                                           assert false (* absurd case *)
                                         | d0::l0 ->
                                           (match l0 with
                                            | [] ->
                                              assert false (* absurd case *)
                                            | d1::l1 ->
                                              (match l1 with
                                               | [] ->
                                                 coq_C8_Imp (snd hwfrL "X")
                                                   (snd hwfrR "X")
                                                   (snd hwfrR "Y")
                                                   (snd (fst hwfrR) "A")
                                                   (snd (fst hwfrR) "B")
                                                   (d0::(d::(d1::[])))
                                               | _::_ ->
                                                 assert false
                                                   (* absurd case *))))
                                      | _::_ -> assert false (* absurd case *))))
                                  (fun _ ->
                                  eq_dec_in_list
                                    (eqdec
                                      (eqDec_rule eqDec_formula f_Kt_log
                                        kt_log eqDec_structr f_Kt kt_str))
                                    KtRules.coq_Boxnl
                                    (KtRules.coq_Dianl::(KtRules.coq_Boxpl::(KtRules.coq_Diapl::[])))
                                    rR (fun _ -> assert false
                                    (* absurd case *)) (fun _ ->
                                    eq_dec_in_list
                                      (eqdec
                                        (eqDec_rule eqDec_formula f_Kt_log
                                          kt_log eqDec_structr f_Kt kt_str))
                                      KtRules.coq_Dianl
                                      (KtRules.coq_Boxpl::(KtRules.coq_Diapl::[]))
                                      rR (fun _ -> assert false
                                      (* absurd case *)) (fun _ ->
                                      eq_dec_in_list
                                        (eqdec
                                          (eqDec_rule eqDec_formula f_Kt_log
                                            kt_log eqDec_structr f_Kt kt_str))
                                        KtRules.coq_Boxpl
                                        (KtRules.coq_Diapl::[]) rR (fun _ ->
                                        assert false (* absurd case *))
                                        (fun _ ->
                                        eq_dec_in_list
                                          (eqdec
                                            (eqDec_rule eqDec_formula
                                              f_Kt_log kt_log eqDec_structr
                                              f_Kt kt_str)) KtRules.coq_Diapl
                                          [] rR (fun _ -> assert false
                                          (* absurd case *)) (fun _ ->
                                          assert false (* absurd case *)))))))))))))
                    (fun _ ->
                    eq_dec_in_list
                      (eqdec
                        (eqDec_rule eqDec_formula f_Kt_log kt_log
                          eqDec_structr f_Kt kt_str)) KtRules.coq_Boxnr
                      (KtRules.coq_Dianr::(KtRules.coq_Boxpr::(KtRules.coq_Diapr::[])))
                      rL (fun _ ->
                      eq_dec_in_list
                        (eqdec
                          (eqDec_rule eqDec_formula f_Kt_log kt_log
                            eqDec_structr f_Kt kt_str))
                        (atrefl eqDec_formula f_Kt_log kt_log eqDec_structr
                          f_Kt kt_str)
                        (KtRules.coq_Topl::(KtRules.coq_Botl::(KtRules.coq_Negl::(KtRules.coq_Conl::(KtRules.coq_Disl::(KtRules.coq_Impl::(KtRules.coq_Boxnl::(KtRules.coq_Dianl::(KtRules.coq_Boxpl::(KtRules.coq_Diapl::[]))))))))))
                        rR (fun _ -> assert false (* absurd case *))
                        (fun _ ->
                        eq_dec_in_list
                          (eqdec
                            (eqDec_rule eqDec_formula f_Kt_log kt_log
                              eqDec_structr f_Kt kt_str)) KtRules.coq_Topl
                          (KtRules.coq_Botl::(KtRules.coq_Negl::(KtRules.coq_Conl::(KtRules.coq_Disl::(KtRules.coq_Impl::(KtRules.coq_Boxnl::(KtRules.coq_Dianl::(KtRules.coq_Boxpl::(KtRules.coq_Diapl::[])))))))))
                          rR (fun _ -> assert false (* absurd case *))
                          (fun _ ->
                          eq_dec_in_list
                            (eqdec
                              (eqDec_rule eqDec_formula f_Kt_log kt_log
                                eqDec_structr f_Kt kt_str)) KtRules.coq_Botl
                            (KtRules.coq_Negl::(KtRules.coq_Conl::(KtRules.coq_Disl::(KtRules.coq_Impl::(KtRules.coq_Boxnl::(KtRules.coq_Dianl::(KtRules.coq_Boxpl::(KtRules.coq_Diapl::[]))))))))
                            rR (fun _ -> assert false (* absurd case *))
                            (fun _ ->
                            eq_dec_in_list
                              (eqdec
                                (eqDec_rule eqDec_formula f_Kt_log kt_log
                                  eqDec_structr f_Kt kt_str))
                              KtRules.coq_Negl
                              (KtRules.coq_Conl::(KtRules.coq_Disl::(KtRules.coq_Impl::(KtRules.coq_Boxnl::(KtRules.coq_Dianl::(KtRules.coq_Boxpl::(KtRules.coq_Diapl::[])))))))
                              rR (fun _ -> assert false (* absurd case *))
                              (fun _ ->
                              eq_dec_in_list
                                (eqdec
                                  (eqDec_rule eqDec_formula f_Kt_log kt_log
                                    eqDec_structr f_Kt kt_str))
                                KtRules.coq_Conl
                                (KtRules.coq_Disl::(KtRules.coq_Impl::(KtRules.coq_Boxnl::(KtRules.coq_Dianl::(KtRules.coq_Boxpl::(KtRules.coq_Diapl::[]))))))
                                rR (fun _ -> assert false (* absurd case *))
                                (fun _ ->
                                eq_dec_in_list
                                  (eqdec
                                    (eqDec_rule eqDec_formula f_Kt_log kt_log
                                      eqDec_structr f_Kt kt_str))
                                  KtRules.coq_Disl
                                  (KtRules.coq_Impl::(KtRules.coq_Boxnl::(KtRules.coq_Dianl::(KtRules.coq_Boxpl::(KtRules.coq_Diapl::[])))))
                                  rR (fun _ -> assert false
                                  (* absurd case *)) (fun _ ->
                                  eq_dec_in_list
                                    (eqdec
                                      (eqDec_rule eqDec_formula f_Kt_log
                                        kt_log eqDec_structr f_Kt kt_str))
                                    KtRules.coq_Impl
                                    (KtRules.coq_Boxnl::(KtRules.coq_Dianl::(KtRules.coq_Boxpl::(KtRules.coq_Diapl::[]))))
                                    rR (fun _ -> assert false
                                    (* absurd case *)) (fun _ ->
                                    eq_dec_in_list
                                      (eqdec
                                        (eqDec_rule eqDec_formula f_Kt_log
                                          kt_log eqDec_structr f_Kt kt_str))
                                      KtRules.coq_Boxnl
                                      (KtRules.coq_Dianl::(KtRules.coq_Boxpl::(KtRules.coq_Diapl::[])))
                                      rR (fun _ ->
                                      let hwfrL =
                                        ruleInst_ruleSubst eqDec_formula
                                          f_Kt_log kt_log eqDec_structr f_Kt
                                          kt_str rL
                                          ((map
                                             (conclDT eqDec_formula f_Kt_log
                                               kt_log eqDec_structr f_Kt
                                               kt_str) lL),(Sequent (x,
                                          (kt_str.fS a))))
                                      in
                                      let hwfrR =
                                        ruleInst_ruleSubst eqDec_formula
                                          f_Kt_log kt_log eqDec_structr f_Kt
                                          kt_str rR
                                          ((map
                                             (conclDT eqDec_formula f_Kt_log
                                               kt_log eqDec_structr f_Kt
                                               kt_str) lR),(Sequent
                                          ((kt_str.fS a), y)))
                                      in
                                      (match lL with
                                       | [] -> assert false (* absurd case *)
                                       | d::l ->
                                         (match l with
                                          | [] ->
                                            (match lR with
                                             | [] ->
                                               assert false (* absurd case *)
                                             | d0::l0 ->
                                               (match l0 with
                                                | [] ->
                                                  coq_C8_Boxn (snd hwfrL "X")
                                                    (snd hwfrR "X")
                                                    (snd (fst hwfrR) "A")
                                                    (d::(d0::[]))
                                                | _::_ ->
                                                  assert false
                                                    (* absurd case *)))
                                          | _::_ ->
                                            assert false (* absurd case *))))
                                      (fun _ ->
                                      eq_dec_in_list
                                        (eqdec
                                          (eqDec_rule eqDec_formula f_Kt_log
                                            kt_log eqDec_structr f_Kt kt_str))
                                        KtRules.coq_Dianl
                                        (KtRules.coq_Boxpl::(KtRules.coq_Diapl::[]))
                                        rR (fun _ -> assert false
                                        (* absurd case *)) (fun _ ->
                                        eq_dec_in_list
                                          (eqdec
                                            (eqDec_rule eqDec_formula
                                              f_Kt_log kt_log eqDec_structr
                                              f_Kt kt_str)) KtRules.coq_Boxpl
                                          (KtRules.coq_Diapl::[]) rR
                                          (fun _ -> assert false
                                          (* absurd case *)) (fun _ ->
                                          eq_dec_in_list
                                            (eqdec
                                              (eqDec_rule eqDec_formula
                                                f_Kt_log kt_log eqDec_structr
                                                f_Kt kt_str))
                                            KtRules.coq_Diapl [] rR (fun _ ->
                                            assert false (* absurd case *))
                                            (fun _ -> assert false
                                            (* absurd case *)))))))))))))
                      (fun _ ->
                      eq_dec_in_list
                        (eqdec
                          (eqDec_rule eqDec_formula f_Kt_log kt_log
                            eqDec_structr f_Kt kt_str)) KtRules.coq_Dianr
                        (KtRules.coq_Boxpr::(KtRules.coq_Diapr::[])) rL
                        (fun _ ->
                        eq_dec_in_list
                          (eqdec
                            (eqDec_rule eqDec_formula f_Kt_log kt_log
                              eqDec_structr f_Kt kt_str))
                          (atrefl eqDec_formula f_Kt_log kt_log eqDec_structr
                            f_Kt kt_str)
                          (KtRules.coq_Topl::(KtRules.coq_Botl::(KtRules.coq_Negl::(KtRules.coq_Conl::(KtRules.coq_Disl::(KtRules.coq_Impl::(KtRules.coq_Boxnl::(KtRules.coq_Dianl::(KtRules.coq_Boxpl::(KtRules.coq_Diapl::[]))))))))))
                          rR (fun _ -> assert false (* absurd case *))
                          (fun _ ->
                          eq_dec_in_list
                            (eqdec
                              (eqDec_rule eqDec_formula f_Kt_log kt_log
                                eqDec_structr f_Kt kt_str)) KtRules.coq_Topl
                            (KtRules.coq_Botl::(KtRules.coq_Negl::(KtRules.coq_Conl::(KtRules.coq_Disl::(KtRules.coq_Impl::(KtRules.coq_Boxnl::(KtRules.coq_Dianl::(KtRules.coq_Boxpl::(KtRules.coq_Diapl::[])))))))))
                            rR (fun _ -> assert false (* absurd case *))
                            (fun _ ->
                            eq_dec_in_list
                              (eqdec
                                (eqDec_rule eqDec_formula f_Kt_log kt_log
                                  eqDec_structr f_Kt kt_str))
                              KtRules.coq_Botl
                              (KtRules.coq_Negl::(KtRules.coq_Conl::(KtRules.coq_Disl::(KtRules.coq_Impl::(KtRules.coq_Boxnl::(KtRules.coq_Dianl::(KtRules.coq_Boxpl::(KtRules.coq_Diapl::[]))))))))
                              rR (fun _ -> assert false (* absurd case *))
                              (fun _ ->
                              eq_dec_in_list
                                (eqdec
                                  (eqDec_rule eqDec_formula f_Kt_log kt_log
                                    eqDec_structr f_Kt kt_str))
                                KtRules.coq_Negl
                                (KtRules.coq_Conl::(KtRules.coq_Disl::(KtRules.coq_Impl::(KtRules.coq_Boxnl::(KtRules.coq_Dianl::(KtRules.coq_Boxpl::(KtRules.coq_Diapl::[])))))))
                                rR (fun _ -> assert false (* absurd case *))
                                (fun _ ->
                                eq_dec_in_list
                                  (eqdec
                                    (eqDec_rule eqDec_formula f_Kt_log kt_log
                                      eqDec_structr f_Kt kt_str))
                                  KtRules.coq_Conl
                                  (KtRules.coq_Disl::(KtRules.coq_Impl::(KtRules.coq_Boxnl::(KtRules.coq_Dianl::(KtRules.coq_Boxpl::(KtRules.coq_Diapl::[]))))))
                                  rR (fun _ -> assert false
                                  (* absurd case *)) (fun _ ->
                                  eq_dec_in_list
                                    (eqdec
                                      (eqDec_rule eqDec_formula f_Kt_log
                                        kt_log eqDec_structr f_Kt kt_str))
                                    KtRules.coq_Disl
                                    (KtRules.coq_Impl::(KtRules.coq_Boxnl::(KtRules.coq_Dianl::(KtRules.coq_Boxpl::(KtRules.coq_Diapl::[])))))
                                    rR (fun _ -> assert false
                                    (* absurd case *)) (fun _ ->
                                    eq_dec_in_list
                                      (eqdec
                                        (eqDec_rule eqDec_formula f_Kt_log
                                          kt_log eqDec_structr f_Kt kt_str))
                                      KtRules.coq_Impl
                                      (KtRules.coq_Boxnl::(KtRules.coq_Dianl::(KtRules.coq_Boxpl::(KtRules.coq_Diapl::[]))))
                                      rR (fun _ -> assert false
                                      (* absurd case *)) (fun _ ->
                                      eq_dec_in_list
                                        (eqdec
                                          (eqDec_rule eqDec_formula f_Kt_log
                                            kt_log eqDec_structr f_Kt kt_str))
                                        KtRules.coq_Boxnl
                                        (KtRules.coq_Dianl::(KtRules.coq_Boxpl::(KtRules.coq_Diapl::[])))
                                        rR (fun _ -> assert false
                                        (* absurd case *)) (fun _ ->
                                        eq_dec_in_list
                                          (eqdec
                                            (eqDec_rule eqDec_formula
                                              f_Kt_log kt_log eqDec_structr
                                              f_Kt kt_str)) KtRules.coq_Dianl
                                          (KtRules.coq_Boxpl::(KtRules.coq_Diapl::[]))
                                          rR (fun _ ->
                                          let hwfrL =
                                            ruleInst_ruleSubst eqDec_formula
                                              f_Kt_log kt_log eqDec_structr
                                              f_Kt kt_str rL
                                              ((map
                                                 (conclDT eqDec_formula
                                                   f_Kt_log kt_log
                                                   eqDec_structr f_Kt kt_str)
                                                 lL),(Sequent (x,
                                              (kt_str.fS a))))
                                          in
                                          let hwfrR =
                                            ruleInst_ruleSubst eqDec_formula
                                              f_Kt_log kt_log eqDec_structr
                                              f_Kt kt_str rR
                                              ((map
                                                 (conclDT eqDec_formula
                                                   f_Kt_log kt_log
                                                   eqDec_structr f_Kt kt_str)
                                                 lR),(Sequent ((kt_str.fS a),
                                              y)))
                                          in
                                          (match lL with
                                           | [] ->
                                             assert false (* absurd case *)
                                           | d::l ->
                                             (match l with
                                              | [] ->
                                                (match lR with
                                                 | [] ->
                                                   assert false
                                                     (* absurd case *)
                                                 | d0::l0 ->
                                                   (match l0 with
                                                    | [] ->
                                                      coq_C8_Dian
                                                        (snd hwfrL "X")
                                                        (snd hwfrR "X")
                                                        (snd (fst hwfrR) "A")
                                                        (d::(d0::[]))
                                                    | _::_ ->
                                                      assert false
                                                        (* absurd case *)))
                                              | _::_ ->
                                                assert false (* absurd case *))))
                                          (fun _ ->
                                          eq_dec_in_list
                                            (eqdec
                                              (eqDec_rule eqDec_formula
                                                f_Kt_log kt_log eqDec_structr
                                                f_Kt kt_str))
                                            KtRules.coq_Boxpl
                                            (KtRules.coq_Diapl::[]) rR
                                            (fun _ -> assert false
                                            (* absurd case *)) (fun _ ->
                                            eq_dec_in_list
                                              (eqdec
                                                (eqDec_rule eqDec_formula
                                                  f_Kt_log kt_log
                                                  eqDec_structr f_Kt kt_str))
                                              KtRules.coq_Diapl [] rR
                                              (fun _ -> assert false
                                              (* absurd case *)) (fun _ ->
                                              assert false (* absurd case *)))))))))))))
                        (fun _ ->
                        eq_dec_in_list
                          (eqdec
                            (eqDec_rule eqDec_formula f_Kt_log kt_log
                              eqDec_structr f_Kt kt_str)) KtRules.coq_Boxpr
                          (KtRules.coq_Diapr::[]) rL (fun _ ->
                          eq_dec_in_list
                            (eqdec
                              (eqDec_rule eqDec_formula f_Kt_log kt_log
                                eqDec_structr f_Kt kt_str))
                            (atrefl eqDec_formula f_Kt_log kt_log
                              eqDec_structr f_Kt kt_str)
                            (KtRules.coq_Topl::(KtRules.coq_Botl::(KtRules.coq_Negl::(KtRules.coq_Conl::(KtRules.coq_Disl::(KtRules.coq_Impl::(KtRules.coq_Boxnl::(KtRules.coq_Dianl::(KtRules.coq_Boxpl::(KtRules.coq_Diapl::[]))))))))))
                            rR (fun _ -> assert false (* absurd case *))
                            (fun _ ->
                            eq_dec_in_list
                              (eqdec
                                (eqDec_rule eqDec_formula f_Kt_log kt_log
                                  eqDec_structr f_Kt kt_str))
                              KtRules.coq_Topl
                              (KtRules.coq_Botl::(KtRules.coq_Negl::(KtRules.coq_Conl::(KtRules.coq_Disl::(KtRules.coq_Impl::(KtRules.coq_Boxnl::(KtRules.coq_Dianl::(KtRules.coq_Boxpl::(KtRules.coq_Diapl::[])))))))))
                              rR (fun _ -> assert false (* absurd case *))
                              (fun _ ->
                              eq_dec_in_list
                                (eqdec
                                  (eqDec_rule eqDec_formula f_Kt_log kt_log
                                    eqDec_structr f_Kt kt_str))
                                KtRules.coq_Botl
                                (KtRules.coq_Negl::(KtRules.coq_Conl::(KtRules.coq_Disl::(KtRules.coq_Impl::(KtRules.coq_Boxnl::(KtRules.coq_Dianl::(KtRules.coq_Boxpl::(KtRules.coq_Diapl::[]))))))))
                                rR (fun _ -> assert false (* absurd case *))
                                (fun _ ->
                                eq_dec_in_list
                                  (eqdec
                                    (eqDec_rule eqDec_formula f_Kt_log kt_log
                                      eqDec_structr f_Kt kt_str))
                                  KtRules.coq_Negl
                                  (KtRules.coq_Conl::(KtRules.coq_Disl::(KtRules.coq_Impl::(KtRules.coq_Boxnl::(KtRules.coq_Dianl::(KtRules.coq_Boxpl::(KtRules.coq_Diapl::[])))))))
                                  rR (fun _ -> assert false
                                  (* absurd case *)) (fun _ ->
                                  eq_dec_in_list
                                    (eqdec
                                      (eqDec_rule eqDec_formula f_Kt_log
                                        kt_log eqDec_structr f_Kt kt_str))
                                    KtRules.coq_Conl
                                    (KtRules.coq_Disl::(KtRules.coq_Impl::(KtRules.coq_Boxnl::(KtRules.coq_Dianl::(KtRules.coq_Boxpl::(KtRules.coq_Diapl::[]))))))
                                    rR (fun _ -> assert false
                                    (* absurd case *)) (fun _ ->
                                    eq_dec_in_list
                                      (eqdec
                                        (eqDec_rule eqDec_formula f_Kt_log
                                          kt_log eqDec_structr f_Kt kt_str))
                                      KtRules.coq_Disl
                                      (KtRules.coq_Impl::(KtRules.coq_Boxnl::(KtRules.coq_Dianl::(KtRules.coq_Boxpl::(KtRules.coq_Diapl::[])))))
                                      rR (fun _ -> assert false
                                      (* absurd case *)) (fun _ ->
                                      eq_dec_in_list
                                        (eqdec
                                          (eqDec_rule eqDec_formula f_Kt_log
                                            kt_log eqDec_structr f_Kt kt_str))
                                        KtRules.coq_Impl
                                        (KtRules.coq_Boxnl::(KtRules.coq_Dianl::(KtRules.coq_Boxpl::(KtRules.coq_Diapl::[]))))
                                        rR (fun _ -> assert false
                                        (* absurd case *)) (fun _ ->
                                        eq_dec_in_list
                                          (eqdec
                                            (eqDec_rule eqDec_formula
                                              f_Kt_log kt_log eqDec_structr
                                              f_Kt kt_str)) KtRules.coq_Boxnl
                                          (KtRules.coq_Dianl::(KtRules.coq_Boxpl::(KtRules.coq_Diapl::[])))
                                          rR (fun _ -> assert false
                                          (* absurd case *)) (fun _ ->
                                          eq_dec_in_list
                                            (eqdec
                                              (eqDec_rule eqDec_formula
                                                f_Kt_log kt_log eqDec_structr
                                                f_Kt kt_str))
                                            KtRules.coq_Dianl
                                            (KtRules.coq_Boxpl::(KtRules.coq_Diapl::[]))
                                            rR (fun _ -> assert false
                                            (* absurd case *)) (fun _ ->
                                            eq_dec_in_list
                                              (eqdec
                                                (eqDec_rule eqDec_formula
                                                  f_Kt_log kt_log
                                                  eqDec_structr f_Kt kt_str))
                                              KtRules.coq_Boxpl
                                              (KtRules.coq_Diapl::[]) rR
                                              (fun _ ->
                                              let hwfrL =
                                                ruleInst_ruleSubst
                                                  eqDec_formula f_Kt_log
                                                  kt_log eqDec_structr f_Kt
                                                  kt_str rL
                                                  ((map
                                                     (conclDT eqDec_formula
                                                       f_Kt_log kt_log
                                                       eqDec_structr f_Kt
                                                       kt_str) lL),(Sequent
                                                  (x, (kt_str.fS a))))
                                              in
                                              let hwfrR =
                                                ruleInst_ruleSubst
                                                  eqDec_formula f_Kt_log
                                                  kt_log eqDec_structr f_Kt
                                                  kt_str rR
                                                  ((map
                                                     (conclDT eqDec_formula
                                                       f_Kt_log kt_log
                                                       eqDec_structr f_Kt
                                                       kt_str) lR),(Sequent
                                                  ((kt_str.fS a), y)))
                                              in
                                              (match lL with
                                               | [] ->
                                                 assert false
                                                   (* absurd case *)
                                               | d::l ->
                                                 (match l with
                                                  | [] ->
                                                    (match lR with
                                                     | [] ->
                                                       assert false
                                                         (* absurd case *)
                                                     | d0::l0 ->
                                                       (match l0 with
                                                        | [] ->
                                                          coq_C8_Boxp
                                                            (snd hwfrL "X")
                                                            (snd hwfrR "X")
                                                            (snd (fst hwfrR)
                                                              "A")
                                                            (d::(d0::[]))
                                                        | _::_ ->
                                                          assert false
                                                            (* absurd case *)))
                                                  | _::_ ->
                                                    assert false
                                                      (* absurd case *))))
                                              (fun _ ->
                                              eq_dec_in_list
                                                (eqdec
                                                  (eqDec_rule eqDec_formula
                                                    f_Kt_log kt_log
                                                    eqDec_structr f_Kt kt_str))
                                                KtRules.coq_Diapl [] rR
                                                (fun _ -> assert false
                                                (* absurd case *)) (fun _ ->
                                                assert false
                                                (* absurd case *)))))))))))))
                          (fun _ ->
                          eq_dec_in_list
                            (eqdec
                              (eqDec_rule eqDec_formula f_Kt_log kt_log
                                eqDec_structr f_Kt kt_str)) KtRules.coq_Diapr
                            [] rL (fun _ ->
                            eq_dec_in_list
                              (eqdec
                                (eqDec_rule eqDec_formula f_Kt_log kt_log
                                  eqDec_structr f_Kt kt_str))
                              (atrefl eqDec_formula f_Kt_log kt_log
                                eqDec_structr f_Kt kt_str)
                              (KtRules.coq_Topl::(KtRules.coq_Botl::(KtRules.coq_Negl::(KtRules.coq_Conl::(KtRules.coq_Disl::(KtRules.coq_Impl::(KtRules.coq_Boxnl::(KtRules.coq_Dianl::(KtRules.coq_Boxpl::(KtRules.coq_Diapl::[]))))))))))
                              rR (fun _ -> assert false (* absurd case *))
                              (fun _ ->
                              eq_dec_in_list
                                (eqdec
                                  (eqDec_rule eqDec_formula f_Kt_log kt_log
                                    eqDec_structr f_Kt kt_str))
                                KtRules.coq_Topl
                                (KtRules.coq_Botl::(KtRules.coq_Negl::(KtRules.coq_Conl::(KtRules.coq_Disl::(KtRules.coq_Impl::(KtRules.coq_Boxnl::(KtRules.coq_Dianl::(KtRules.coq_Boxpl::(KtRules.coq_Diapl::[])))))))))
                                rR (fun _ -> assert false (* absurd case *))
                                (fun _ ->
                                eq_dec_in_list
                                  (eqdec
                                    (eqDec_rule eqDec_formula f_Kt_log kt_log
                                      eqDec_structr f_Kt kt_str))
                                  KtRules.coq_Botl
                                  (KtRules.coq_Negl::(KtRules.coq_Conl::(KtRules.coq_Disl::(KtRules.coq_Impl::(KtRules.coq_Boxnl::(KtRules.coq_Dianl::(KtRules.coq_Boxpl::(KtRules.coq_Diapl::[]))))))))
                                  rR (fun _ -> assert false
                                  (* absurd case *)) (fun _ ->
                                  eq_dec_in_list
                                    (eqdec
                                      (eqDec_rule eqDec_formula f_Kt_log
                                        kt_log eqDec_structr f_Kt kt_str))
                                    KtRules.coq_Negl
                                    (KtRules.coq_Conl::(KtRules.coq_Disl::(KtRules.coq_Impl::(KtRules.coq_Boxnl::(KtRules.coq_Dianl::(KtRules.coq_Boxpl::(KtRules.coq_Diapl::[])))))))
                                    rR (fun _ -> assert false
                                    (* absurd case *)) (fun _ ->
                                    eq_dec_in_list
                                      (eqdec
                                        (eqDec_rule eqDec_formula f_Kt_log
                                          kt_log eqDec_structr f_Kt kt_str))
                                      KtRules.coq_Conl
                                      (KtRules.coq_Disl::(KtRules.coq_Impl::(KtRules.coq_Boxnl::(KtRules.coq_Dianl::(KtRules.coq_Boxpl::(KtRules.coq_Diapl::[]))))))
                                      rR (fun _ -> assert false
                                      (* absurd case *)) (fun _ ->
                                      eq_dec_in_list
                                        (eqdec
                                          (eqDec_rule eqDec_formula f_Kt_log
                                            kt_log eqDec_structr f_Kt kt_str))
                                        KtRules.coq_Disl
                                        (KtRules.coq_Impl::(KtRules.coq_Boxnl::(KtRules.coq_Dianl::(KtRules.coq_Boxpl::(KtRules.coq_Diapl::[])))))
                                        rR (fun _ -> assert false
                                        (* absurd case *)) (fun _ ->
                                        eq_dec_in_list
                                          (eqdec
                                            (eqDec_rule eqDec_formula
                                              f_Kt_log kt_log eqDec_structr
                                              f_Kt kt_str)) KtRules.coq_Impl
                                          (KtRules.coq_Boxnl::(KtRules.coq_Dianl::(KtRules.coq_Boxpl::(KtRules.coq_Diapl::[]))))
                                          rR (fun _ -> assert false
                                          (* absurd case *)) (fun _ ->
                                          eq_dec_in_list
                                            (eqdec
                                              (eqDec_rule eqDec_formula
                                                f_Kt_log kt_log eqDec_structr
                                                f_Kt kt_str))
                                            KtRules.coq_Boxnl
                                            (KtRules.coq_Dianl::(KtRules.coq_Boxpl::(KtRules.coq_Diapl::[])))
                                            rR (fun _ -> assert false
                                            (* absurd case *)) (fun _ ->
                                            eq_dec_in_list
                                              (eqdec
                                                (eqDec_rule eqDec_formula
                                                  f_Kt_log kt_log
                                                  eqDec_structr f_Kt kt_str))
                                              KtRules.coq_Dianl
                                              (KtRules.coq_Boxpl::(KtRules.coq_Diapl::[]))
                                              rR (fun _ -> assert false
                                              (* absurd case *)) (fun _ ->
                                              eq_dec_in_list
                                                (eqdec
                                                  (eqDec_rule eqDec_formula
                                                    f_Kt_log kt_log
                                                    eqDec_structr f_Kt kt_str))
                                                KtRules.coq_Boxpl
                                                (KtRules.coq_Diapl::[]) rR
                                                (fun _ -> assert false
                                                (* absurd case *)) (fun _ ->
                                                eq_dec_in_list
                                                  (eqdec
                                                    (eqDec_rule eqDec_formula
                                                      f_Kt_log kt_log
                                                      eqDec_structr f_Kt
                                                      kt_str))
                                                  KtRules.coq_Diapl [] rR
                                                  (fun _ ->
                                                  let hwfrL =
                                                    ruleInst_ruleSubst
                                                      eqDec_formula f_Kt_log
                                                      kt_log eqDec_structr
                                                      f_Kt kt_str rL
                                                      ((map
                                                         (conclDT
                                                           eqDec_formula
                                                           f_Kt_log kt_log
                                                           eqDec_structr f_Kt
                                                           kt_str) lL),(Sequent
                                                      (x, (kt_str.fS a))))
                                                  in
                                                  let hwfrR =
                                                    ruleInst_ruleSubst
                                                      eqDec_formula f_Kt_log
                                                      kt_log eqDec_structr
                                                      f_Kt kt_str rR
                                                      ((map
                                                         (conclDT
                                                           eqDec_formula
                                                           f_Kt_log kt_log
                                                           eqDec_structr f_Kt
                                                           kt_str) lR),(Sequent
                                                      ((kt_str.fS a), y)))
                                                  in
                                                  (match lL with
                                                   | [] ->
                                                     assert false
                                                       (* absurd case *)
                                                   | d::l ->
                                                     (match l with
                                                      | [] ->
                                                        (match lR with
                                                         | [] ->
                                                           assert false
                                                             (* absurd case *)
                                                         | d0::l0 ->
                                                           (match l0 with
                                                            | [] ->
                                                              coq_C8_Diap
                                                                (snd hwfrL
                                                                  "X")
                                                                (snd hwfrR
                                                                  "X")
                                                                (snd
                                                                  (fst hwfrR)
                                                                  "A")
                                                                (d::(d0::[]))
                                                            | _::_ ->
                                                              assert false
                                                                (* absurd case *)))
                                                      | _::_ ->
                                                        assert false
                                                          (* absurd case *))))
                                                  (fun _ -> assert false
                                                  (* absurd case *)))))))))))))
                            (fun _ -> assert false (* absurd case *)))))))))))))
      m dt
 end

(** val kt_DCBel : (Kt.formula, Kt.structr) bELNAP **)

let kt_DCBel x x0 _ _ _ =
  KtBelnap.coq_C8_holds x x0

(** val kt_cutElim :
    (Kt.formula, Kt.structr) dertree -> (Kt.formula, Kt.structr) dertree **)

let kt_cutElim dt =
  cutElim eqDec_formula f_Kt_log kt_log eqDec_structr f_Kt kt_str kt_DC
    kt_DCBel dt

(** val box_con_dis : (Kt.formula, Kt.structr) rule **)

let box_con_dis =
  [],(Sequent ((Kt.FSf (Kt.Boxn (Kt.Con ((Kt.Atf "p"), (Kt.Atf "q"))))),
    (Kt.FSf (Kt.Dis ((Kt.Boxn (Kt.Atf "p")), (Kt.Boxn (Kt.Atf "q")))))))

(** val derr_box_con_dis : (Kt.formula, Kt.structr) derivRule **)

let derr_box_con_dis =
  let p = Kt.Atf "p" in
  let q = Kt.Atf "q" in
  extend_DerivRule_expl eqDec_formula f_Kt_log kt_log eqDec_structr f_Kt
    kt_str kt_DC
    (frefl eqDec_formula f_Kt_log kt_log eqDec_structr f_Kt kt_str (Kt.Boxn
      p))
    (let a = Kt.Boxn p in
     derrnc_derr eqDec_formula f_Kt_log kt_log eqDec_structr f_Kt kt_str
       kt_DC
       (frefl eqDec_formula f_Kt_log kt_log eqDec_structr f_Kt kt_str a)
       (KtDeriv.dernc_frefl a)) box_con_dis (Der ((Sequent ((Kt.FSf (Kt.Boxn
    (Kt.Con (p, q)))), (Kt.FSf (Kt.Dis ((Kt.Boxn p), (Kt.Boxn q)))))),
    (cUT eqDec_formula f_Kt_log kt_log eqDec_structr f_Kt kt_str), ((Der
    ((Sequent ((Kt.FSf (Kt.Boxn (Kt.Con (p, q)))), (Kt.FSf (Kt.Boxn p)))),
    KtRules.coq_Boxnr, ((Der ((Sequent ((Kt.BCirc (Kt.FSf (Kt.Boxn (Kt.Con
    (p, q))))), (Kt.FSf p))), KtRules.coq_Scr, ((Der ((Sequent ((Kt.FSf
    (Kt.Boxn (Kt.Con (p, q)))), (Kt.BCirc (Kt.FSf p)))), KtRules.coq_Boxnl,
    ((Der ((Sequent ((Kt.FSf (Kt.Con (p, q))), (Kt.FSf p))),
    KtRules.coq_Conl, ((Der ((Sequent ((Kt.Comma ((Kt.FSf p), (Kt.FSf q))),
    (Kt.FSf p))), KtRules.coq_Comml, ((Der ((Sequent ((Kt.Comma ((Kt.FSf q),
    (Kt.FSf p))), (Kt.FSf p))), KtRules.coq_Wkl, ((Der ((Sequent ((Kt.FSf p),
    (Kt.FSf p))),
    (atrefl eqDec_formula f_Kt_log kt_log eqDec_structr f_Kt kt_str),
    []))::[])))::[])))::[])))::[])))::[])))::[])))::((Der ((Sequent ((Kt.FSf
    (Kt.Boxn p)), (Kt.FSf (Kt.Dis ((Kt.Boxn p), (Kt.Boxn q)))))),
    KtRules.coq_Disr, ((Der ((Sequent ((Kt.FSf (Kt.Boxn p)), (Kt.Comma
    ((Kt.FSf (Kt.Boxn p)), (Kt.FSf (Kt.Boxn q)))))), KtRules.coq_Wkr, ((Der
    ((Sequent ((Kt.FSf (Kt.Boxn p)), (Kt.FSf (Kt.Boxn p)))),
    (frefl eqDec_formula f_Kt_log kt_log eqDec_structr f_Kt kt_str (Kt.Boxn
      p)), []))::[])))::[])))::[]))))
