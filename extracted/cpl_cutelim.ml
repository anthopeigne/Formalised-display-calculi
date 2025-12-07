
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

(** val alr_DerivRule :
    'a1 eqDec -> 'a1 fLANG -> 'a1 lOGLANG -> 'a2 eqDec -> 'a2 fLANG -> ('a1,
    'a2) sTRLANG -> ('a1, 'a2) dISPCALC -> ('a1, 'a2) rule -> ('a1, 'a2)
    derivRule -> ('a1, 'a2) derivRule **)

let alr_DerivRule _ _ _ _ _ _ _ _ dr =
  dr

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

(** val derivRuleNC_refl :
    'a1 eqDec -> 'a1 fLANG -> 'a1 lOGLANG -> 'a2 eqDec -> 'a2 fLANG -> ('a1,
    'a2) sTRLANG -> ('a1, 'a2) dISPCALC -> ('a1, 'a2) sequent -> ('a1, 'a2)
    derivRuleNC **)

let derivRuleNC_refl _ _ _ _ _ _ _ c =
  Unf c

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

type ('formula, 'structr) subDerNC =
  ('formula, 'structr) rule -> ('formula, 'structr) derivRuleNC -> ('formula,
  'structr) derivRuleNC

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

(** val subDC_SubDer :
    'a1 eqDec -> 'a1 fLANG -> 'a1 lOGLANG -> 'a2 eqDec -> 'a2 fLANG -> ('a1,
    'a2) sTRLANG -> ('a1, 'a2) dISPCALC -> ('a1, 'a2) dISPCALC -> ('a1, 'a2)
    subDer **)

let subDC_SubDer eDf lf lL eDs ls sL dC1 _ r hderncr =
  derr_dt eDf lf lL eDs ls sL dC1 r hderncr

(** val subDC_DerivRule :
    'a1 eqDec -> 'a1 fLANG -> 'a1 lOGLANG -> 'a2 eqDec -> 'a2 fLANG -> ('a1,
    'a2) sTRLANG -> ('a1, 'a2) dISPCALC -> ('a1, 'a2) dISPCALC -> ('a1, 'a2)
    rule -> ('a1, 'a2) derivRule -> ('a1, 'a2) derivRule **)

let subDC_DerivRule =
  subDC_SubDer

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

(** val extend_DerivRule :
    'a1 eqDec -> 'a1 fLANG -> 'a1 lOGLANG -> 'a2 eqDec -> 'a2 fLANG -> ('a1,
    'a2) sTRLANG -> ('a1, 'a2) dISPCALC -> ('a1, 'a2) rule -> ('a1, 'a2)
    derivRule -> ('a1, 'a2) subDer **)

let extend_DerivRule eDf lf lL eDs ls sL dC r dr =
  extend_DerivDC eDf lf lL eDs ls sL dC (r::[]) (fun x _ ->
    derivDC_one eDf lf lL eDs ls sL dC r dr x)

(** val extend_DerivRule_expl :
    'a1 eqDec -> 'a1 fLANG -> 'a1 lOGLANG -> 'a2 eqDec -> 'a2 fLANG -> ('a1,
    'a2) sTRLANG -> ('a1, 'a2) dISPCALC -> ('a1, 'a2) rule -> ('a1, 'a2)
    derivRule -> ('a1, 'a2) subDer **)

let extend_DerivRule_expl eDf lf lL eDs ls sL dC r dr =
  extend_DerivDC eDf lf lL eDs ls sL dC (r::[]) (fun x _ ->
    derivDC_one eDf lf lL eDs ls sL dC r dr x)

(** val extend_DerivRuleNC :
    'a1 eqDec -> 'a1 fLANG -> 'a1 lOGLANG -> 'a2 eqDec -> 'a2 fLANG -> ('a1,
    'a2) sTRLANG -> ('a1, 'a2) dISPCALC -> ('a1, 'a2) rule -> ('a1, 'a2)
    derivRuleNC -> ('a1, 'a2) subDerNC **)

let extend_DerivRuleNC eDf lf lL eDs ls sL dC r dr rho hder =
  let x = fun dC0 r0 ->
    let x,_ = dernc_derremcut_iff eDf lf lL eDs ls sL dC0 r0 in x
  in
  let dr0 = x dC r dr in
  let x0 = fun dC0 r0 ->
    let x0,_ = dernc_derremcut_iff eDf lf lL eDs ls sL dC0 r0 in x0
  in
  let hder0 = x0 (app dC (r::[])) rho hder in
  let _,x1 = dernc_derremcut_iff eDf lf lL eDs ls sL dC rho in
  x1
    (let s = rule_eq_dec eDf lf lL eDs ls sL (cUT eDf lf lL eDs ls sL) r in
     if s
     then hder0
     else extend_DerivRule eDf lf lL eDs ls sL
            (remove_rule eDf lf lL eDs ls sL (cUT eDf lf lL eDs ls sL) dC) r
            dr0 rho hder0)

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

module PL =
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

  (** val formula_rect :
      (string -> 'a1) -> (string -> 'a1) -> 'a1 -> 'a1 -> (formula -> 'a1 ->
      'a1) -> (formula -> 'a1 -> formula -> 'a1 -> 'a1) -> (formula -> 'a1 ->
      formula -> 'a1 -> 'a1) -> (formula -> 'a1 -> formula -> 'a1 -> 'a1) ->
      formula -> 'a1 **)

  let rec formula_rect f f0 f1 f2 f3 f4 f5 f6 = function
  | Atf p -> f p
  | FVf a -> f0 a
  | Top -> f1
  | Bot -> f2
  | Neg phi -> f3 phi (formula_rect f f0 f1 f2 f3 f4 f5 f6 phi)
  | Imp (phi, psi) ->
    f4 phi (formula_rect f f0 f1 f2 f3 f4 f5 f6 phi) psi
      (formula_rect f f0 f1 f2 f3 f4 f5 f6 psi)
  | Dis (phi, psi) ->
    f5 phi (formula_rect f f0 f1 f2 f3 f4 f5 f6 phi) psi
      (formula_rect f f0 f1 f2 f3 f4 f5 f6 psi)
  | Con (phi, psi) ->
    f6 phi (formula_rect f f0 f1 f2 f3 f4 f5 f6 phi) psi
      (formula_rect f f0 f1 f2 f3 f4 f5 f6 psi)

  (** val formula_rec :
      (string -> 'a1) -> (string -> 'a1) -> 'a1 -> 'a1 -> (formula -> 'a1 ->
      'a1) -> (formula -> 'a1 -> formula -> 'a1 -> 'a1) -> (formula -> 'a1 ->
      formula -> 'a1 -> 'a1) -> (formula -> 'a1 -> formula -> 'a1 -> 'a1) ->
      formula -> 'a1 **)

  let rec formula_rec f f0 f1 f2 f3 f4 f5 f6 = function
  | Atf p -> f p
  | FVf a -> f0 a
  | Top -> f1
  | Bot -> f2
  | Neg phi -> f3 phi (formula_rec f f0 f1 f2 f3 f4 f5 f6 phi)
  | Imp (phi, psi) ->
    f4 phi (formula_rec f f0 f1 f2 f3 f4 f5 f6 phi) psi
      (formula_rec f f0 f1 f2 f3 f4 f5 f6 psi)
  | Dis (phi, psi) ->
    f5 phi (formula_rec f f0 f1 f2 f3 f4 f5 f6 phi) psi
      (formula_rec f f0 f1 f2 f3 f4 f5 f6 psi)
  | Con (phi, psi) ->
    f6 phi (formula_rec f f0 f1 f2 f3 f4 f5 f6 phi) psi
      (formula_rec f f0 f1 f2 f3 f4 f5 f6 psi)
 end

module PL_LOG =
 struct
  (** val fml_eq_dec : PL.formula eq_dec **)

  let rec fml_eq_dec f x0 =
    match f with
    | PL.Atf p -> (match x0 with
                   | PL.Atf p0 -> (=) p p0
                   | _ -> false)
    | PL.FVf a -> (match x0 with
                   | PL.FVf a0 -> (=) a a0
                   | _ -> false)
    | PL.Top -> (match x0 with
                 | PL.Top -> true
                 | _ -> false)
    | PL.Bot -> (match x0 with
                 | PL.Bot -> true
                 | _ -> false)
    | PL.Neg phi ->
      (match x0 with
       | PL.Neg phi0 -> fml_eq_dec phi phi0
       | _ -> false)
    | PL.Imp (phi, psi) ->
      (match x0 with
       | PL.Imp (phi0, psi0) ->
         if fml_eq_dec phi phi0 then fml_eq_dec psi psi0 else false
       | _ -> false)
    | PL.Dis (phi, psi) ->
      (match x0 with
       | PL.Dis (phi0, psi0) ->
         if fml_eq_dec phi phi0 then fml_eq_dec psi psi0 else false
       | _ -> false)
    | PL.Con (phi, psi) ->
      (match x0 with
       | PL.Con (phi0, psi0) ->
         if fml_eq_dec phi phi0 then fml_eq_dec psi psi0 else false
       | _ -> false)

  (** val ipse : PL.formula -> PL.formula list **)

  let ipse = function
  | PL.Neg a0 -> a0::[]
  | PL.Imp (a1, a2) -> a1::(a2::[])
  | PL.Dis (a1, a2) -> a1::(a2::[])
  | PL.Con (a1, a2) -> a1::(a2::[])
  | _ -> []

  (** val ipse_rect :
      (PL.formula -> (PL.formula -> __ -> 'a1) -> 'a1) -> PL.formula -> 'a1 **)

  let rec ipse_rect h = function
  | PL.Neg phi ->
    h (PL.Neg phi) (fun b _ ->
      let s = fml_eq_dec b phi in
      if s then ipse_rect h phi else assert false (* absurd case *))
  | PL.Imp (phi, psi) ->
    h (PL.Imp (phi, psi)) (fun b _ ->
      let s = fml_eq_dec b phi in
      if s
      then ipse_rect h phi
      else let s0 = fml_eq_dec b psi in
           if s0 then ipse_rect h psi else assert false (* absurd case *))
  | PL.Dis (phi, psi) ->
    h (PL.Dis (phi, psi)) (fun b _ ->
      let s = fml_eq_dec b phi in
      if s
      then ipse_rect h phi
      else let s0 = fml_eq_dec b psi in
           if s0 then ipse_rect h psi else assert false (* absurd case *))
  | PL.Con (phi, psi) ->
    h (PL.Con (phi, psi)) (fun b _ ->
      let s = fml_eq_dec b phi in
      if s
      then ipse_rect h phi
      else let s0 = fml_eq_dec b psi in
           if s0 then ipse_rect h psi else assert false (* absurd case *))
  | x -> h x (fun _ _ -> assert false (* absurd case *))

  (** val fml_df : PL.formula **)

  let fml_df =
    PL.Atf ""

  (** val conn : PL.formula -> PL.formula list -> PL.formula **)

  let conn a x =
    match a with
    | PL.Neg _ -> (match x with
                   | [] -> fml_df
                   | b0::_ -> PL.Neg b0)
    | PL.Imp (_, _) ->
      (match x with
       | [] -> fml_df
       | b1::l0 -> (match l0 with
                    | [] -> fml_df
                    | b2::_ -> PL.Imp (b1, b2)))
    | PL.Dis (_, _) ->
      (match x with
       | [] -> fml_df
       | b1::l0 -> (match l0 with
                    | [] -> fml_df
                    | b2::_ -> PL.Dis (b1, b2)))
    | PL.Con (_, _) ->
      (match x with
       | [] -> fml_df
       | b1::l0 -> (match l0 with
                    | [] -> fml_df
                    | b2::_ -> PL.Con (b1, b2)))
    | _ -> a

  (** val coq_Atm_dec : PL.formula -> string option **)

  let coq_Atm_dec = function
  | PL.Atf p -> Some p
  | _ -> None

  (** val coq_FV_dec : PL.formula -> string option **)

  let coq_FV_dec = function
  | PL.FVf a0 -> Some a0
  | _ -> None
 end

(** val eqDec_formula : PL.formula eqDec **)

let eqDec_formula =
  PL_LOG.fml_eq_dec

(** val f_PL : PL.formula fLANG **)

let f_PL =
  { ipse = PL_LOG.ipse; ipse_rect = (fun _ -> PL_LOG.ipse_rect); conn =
    PL_LOG.conn }

(** val pL_Atm : (PL.formula, string) iXEXP **)

let pL_Atm =
  PL_LOG.coq_Atm_dec

(** val pL_FV : (PL.formula, string) iXEXP **)

let pL_FV =
  PL_LOG.coq_FV_dec

(** val pL_LANG : PL.formula lOGLANG **)

let pL_LANG =
  { atm = (fun x -> PL.Atf x); fV = (fun x -> PL.FVf x); aTMVAR = pL_Atm;
    fVVAR = pL_FV }

module CPL =
 struct
  type structr =
  | SVf of string
  | FSf of PL.formula
  | I
  | Star of structr
  | Comma of structr * structr

  (** val structr_rect :
      (string -> 'a1) -> (PL.formula -> 'a1) -> 'a1 -> (structr -> 'a1 ->
      'a1) -> (structr -> 'a1 -> structr -> 'a1 -> 'a1) -> structr -> 'a1 **)

  let rec structr_rect f f0 f1 f2 f3 = function
  | SVf x -> f x
  | FSf a -> f0 a
  | I -> f1
  | Star x -> f2 x (structr_rect f f0 f1 f2 f3 x)
  | Comma (phi, psi) ->
    f3 phi (structr_rect f f0 f1 f2 f3 phi) psi
      (structr_rect f f0 f1 f2 f3 psi)

  (** val structr_rec :
      (string -> 'a1) -> (PL.formula -> 'a1) -> 'a1 -> (structr -> 'a1 ->
      'a1) -> (structr -> 'a1 -> structr -> 'a1 -> 'a1) -> structr -> 'a1 **)

  let rec structr_rec f f0 f1 f2 f3 = function
  | SVf x -> f x
  | FSf a -> f0 a
  | I -> f1
  | Star x -> f2 x (structr_rec f f0 f1 f2 f3 x)
  | Comma (phi, psi) ->
    f3 phi (structr_rec f f0 f1 f2 f3 phi) psi (structr_rec f f0 f1 f2 f3 psi)
 end

module CPL_STR =
 struct
  (** val str_eq_dec : CPL.structr eq_dec **)

  let rec str_eq_dec s x0 =
    match s with
    | CPL.SVf x ->
      (match x0 with
       | CPL.SVf x1 -> eqdec eqDec_string x x1
       | _ -> false)
    | CPL.FSf a ->
      (match x0 with
       | CPL.FSf a0 -> eqdec eqDec_formula a a0
       | _ -> false)
    | CPL.I -> (match x0 with
                | CPL.I -> true
                | _ -> false)
    | CPL.Star x ->
      (match x0 with
       | CPL.Star x1 -> str_eq_dec x x1
       | _ -> false)
    | CPL.Comma (phi, psi) ->
      (match x0 with
       | CPL.Comma (phi0, psi0) ->
         if str_eq_dec phi phi0 then str_eq_dec psi psi0 else false
       | _ -> false)

  (** val ipse : CPL.structr -> CPL.structr list **)

  let ipse = function
  | CPL.Star x0 -> x0::[]
  | CPL.Comma (x1, x2) -> x1::(x2::[])
  | _ -> []

  (** val ipse_rect :
      (CPL.structr -> (CPL.structr -> __ -> 'a1) -> 'a1) -> CPL.structr -> 'a1 **)

  let rec ipse_rect h = function
  | CPL.Star x ->
    h (CPL.Star x) (fun b _ ->
      let s = str_eq_dec b x in
      if s then ipse_rect h x else assert false (* absurd case *))
  | CPL.Comma (phi, psi) ->
    h (CPL.Comma (phi, psi)) (fun b _ ->
      let s = str_eq_dec b phi in
      if s
      then ipse_rect h phi
      else let s0 = str_eq_dec b psi in
           if s0 then ipse_rect h psi else assert false (* absurd case *))
  | x -> h x (fun _ _ -> assert false (* absurd case *))

  (** val str_df : CPL.structr **)

  let str_df =
    CPL.SVf ""

  (** val conn : CPL.structr -> CPL.structr list -> CPL.structr **)

  let conn x x0 =
    match x with
    | CPL.Star _ -> (match x0 with
                     | [] -> str_df
                     | y0::_ -> CPL.Star y0)
    | CPL.Comma (_, _) ->
      (match x0 with
       | [] -> str_df
       | y1::l0 -> (match l0 with
                    | [] -> str_df
                    | y2::_ -> CPL.Comma (y1, y2)))
    | _ -> x

  (** val coq_SV_dec : CPL.structr -> string option **)

  let coq_SV_dec = function
  | CPL.SVf x0 -> Some x0
  | _ -> None

  (** val coq_FS_dec : CPL.structr -> PL.formula option **)

  let coq_FS_dec = function
  | CPL.FSf a -> Some a
  | _ -> None

  (** val sgnips : CPL.structr -> bool list **)

  let sgnips = function
  | CPL.Star _ -> false::[]
  | CPL.Comma (_, _) -> true::(true::[])
  | _ -> []
 end

(** val eqDec_structr : CPL.structr eqDec **)

let eqDec_structr =
  CPL_STR.str_eq_dec

(** val f_CPL : CPL.structr fLANG **)

let f_CPL =
  { ipse = CPL_STR.ipse; ipse_rect = (fun _ -> CPL_STR.ipse_rect); conn =
    CPL_STR.conn }

(** val cPL_SV : (CPL.structr, string) iXEXP **)

let cPL_SV =
  CPL_STR.coq_SV_dec

(** val cPL_FS : (CPL.structr, PL.formula) iXEXP **)

let cPL_FS =
  CPL_STR.coq_FS_dec

(** val cPL_LANG : (PL.formula, CPL.structr) sTRLANG **)

let cPL_LANG =
  { sV = (fun x -> CPL.SVf x); fS = (fun x -> CPL.FSf x); sVVAR = cPL_SV;
    fSVAR = cPL_FS; sgnips = CPL_STR.sgnips }

module CPLRules =
 struct
  (** val coq_Topl : (PL.formula, CPL.structr) rule **)

  let coq_Topl =
    ((Sequent (CPL.I, (CPL.SVf "X")))::[]),(Sequent ((CPL.FSf PL.Top),
      (CPL.SVf "X")))

  (** val coq_Topr : (PL.formula, CPL.structr) rule **)

  let coq_Topr =
    [],(Sequent (CPL.I, (CPL.FSf PL.Top)))

  (** val coq_Botl : (PL.formula, CPL.structr) rule **)

  let coq_Botl =
    [],(Sequent ((CPL.FSf PL.Bot), CPL.I))

  (** val coq_Botr : (PL.formula, CPL.structr) rule **)

  let coq_Botr =
    ((Sequent ((CPL.SVf "X"), CPL.I))::[]),(Sequent ((CPL.SVf "X"), (CPL.FSf
      PL.Bot)))

  (** val coq_Negl : (PL.formula, CPL.structr) rule **)

  let coq_Negl =
    ((Sequent ((CPL.Star (CPL.FSf (PL.FVf "A"))), (CPL.SVf
      "X")))::[]),(Sequent ((CPL.FSf (PL.Neg (PL.FVf "A"))), (CPL.SVf "X")))

  (** val coq_Negr : (PL.formula, CPL.structr) rule **)

  let coq_Negr =
    ((Sequent ((CPL.SVf "X"), (CPL.Star (CPL.FSf (PL.FVf
      "A")))))::[]),(Sequent ((CPL.SVf "X"), (CPL.FSf (PL.Neg (PL.FVf "A")))))

  (** val coq_Conl : (PL.formula, CPL.structr) rule **)

  let coq_Conl =
    ((Sequent ((CPL.Comma ((CPL.FSf (PL.FVf "A")), (CPL.FSf (PL.FVf "B")))),
      (CPL.SVf "X")))::[]),(Sequent ((CPL.FSf (PL.Con ((PL.FVf "A"), (PL.FVf
      "B")))), (CPL.SVf "X")))

  (** val coq_Conr : (PL.formula, CPL.structr) rule **)

  let coq_Conr =
    ((Sequent ((CPL.SVf "X"), (CPL.FSf (PL.FVf "A"))))::((Sequent ((CPL.SVf
      "Y"), (CPL.FSf (PL.FVf "B"))))::[])),(Sequent ((CPL.Comma ((CPL.SVf
      "X"), (CPL.SVf "Y"))), (CPL.FSf (PL.Con ((PL.FVf "A"), (PL.FVf "B"))))))

  (** val coq_Disl : (PL.formula, CPL.structr) rule **)

  let coq_Disl =
    ((Sequent ((CPL.FSf (PL.FVf "A")), (CPL.SVf "X")))::((Sequent ((CPL.FSf
      (PL.FVf "B")), (CPL.SVf "Y")))::[])),(Sequent ((CPL.FSf (PL.Dis
      ((PL.FVf "A"), (PL.FVf "B")))), (CPL.Comma ((CPL.SVf "X"), (CPL.SVf
      "Y")))))

  (** val coq_Disr : (PL.formula, CPL.structr) rule **)

  let coq_Disr =
    ((Sequent ((CPL.SVf "X"), (CPL.Comma ((CPL.FSf (PL.FVf "A")), (CPL.FSf
      (PL.FVf "B"))))))::[]),(Sequent ((CPL.SVf "X"), (CPL.FSf (PL.Dis
      ((PL.FVf "A"), (PL.FVf "B"))))))

  (** val coq_Impl : (PL.formula, CPL.structr) rule **)

  let coq_Impl =
    ((Sequent ((CPL.SVf "X"), (CPL.FSf (PL.FVf "A"))))::((Sequent ((CPL.FSf
      (PL.FVf "B")), (CPL.SVf "Y")))::[])),(Sequent ((CPL.FSf (PL.Imp
      ((PL.FVf "A"), (PL.FVf "B")))), (CPL.Comma ((CPL.Star (CPL.SVf "X")),
      (CPL.SVf "Y")))))

  (** val coq_Impr : (PL.formula, CPL.structr) rule **)

  let coq_Impr =
    ((Sequent ((CPL.Comma ((CPL.SVf "X"), (CPL.FSf (PL.FVf "A")))), (CPL.FSf
      (PL.FVf "B"))))::[]),(Sequent ((CPL.SVf "X"), (CPL.FSf (PL.Imp ((PL.FVf
      "A"), (PL.FVf "B"))))))

  (** val coq_Iaddl : (PL.formula, CPL.structr) rule **)

  let coq_Iaddl =
    ((Sequent ((CPL.SVf "X"), (CPL.SVf "Y")))::[]),(Sequent ((CPL.Comma
      ((CPL.SVf "X"), CPL.I)), (CPL.SVf "Y")))

  (** val coq_Idell : (PL.formula, CPL.structr) rule **)

  let coq_Idell =
    ((Sequent ((CPL.Comma ((CPL.SVf "X"), CPL.I)), (CPL.SVf
      "Y")))::[]),(Sequent ((CPL.SVf "X"), (CPL.SVf "Y")))

  (** val coq_Iwl : (PL.formula, CPL.structr) rule **)

  let coq_Iwl =
    ((Sequent (CPL.I, (CPL.SVf "Y")))::[]),(Sequent ((CPL.SVf "X"), (CPL.SVf
      "Y")))

  (** val coq_Iwr : (PL.formula, CPL.structr) rule **)

  let coq_Iwr =
    ((Sequent ((CPL.SVf "X"), CPL.I))::[]),(Sequent ((CPL.SVf "X"), (CPL.SVf
      "Y")))

  (** val coq_Comml : (PL.formula, CPL.structr) rule **)

  let coq_Comml =
    ((Sequent ((CPL.Comma ((CPL.SVf "X"), (CPL.SVf "Y"))), (CPL.SVf
      "Z")))::[]),(Sequent ((CPL.Comma ((CPL.SVf "Y"), (CPL.SVf "X"))),
      (CPL.SVf "Z")))

  (** val coq_Contl : (PL.formula, CPL.structr) rule **)

  let coq_Contl =
    ((Sequent ((CPL.Comma ((CPL.SVf "X"), (CPL.SVf "X"))), (CPL.SVf
      "Y")))::[]),(Sequent ((CPL.SVf "X"), (CPL.SVf "Y")))

  (** val coq_Assol : (PL.formula, CPL.structr) rule **)

  let coq_Assol =
    ((Sequent ((CPL.Comma ((CPL.SVf "X"), (CPL.Comma ((CPL.SVf "Y"), (CPL.SVf
      "Z"))))), (CPL.SVf "W")))::[]),(Sequent ((CPL.Comma ((CPL.Comma
      ((CPL.SVf "X"), (CPL.SVf "Y"))), (CPL.SVf "Z"))), (CPL.SVf "W")))

  (** val coq_Mlrn : (PL.formula, CPL.structr) rule **)

  let coq_Mlrn =
    ((Sequent ((CPL.Comma ((CPL.SVf "X"), (CPL.SVf "Y"))), (CPL.SVf
      "Z")))::[]),(Sequent ((CPL.SVf "X"), (CPL.Comma ((CPL.SVf "Z"),
      (CPL.Star (CPL.SVf "Y"))))))

  (** val coq_Mrrslln : (PL.formula, CPL.structr) rule **)

  let coq_Mrrslln =
    ((Sequent ((CPL.SVf "X"), (CPL.Comma ((CPL.SVf "Y"), (CPL.Star (CPL.SVf
      "Z"))))))::[]),(Sequent ((CPL.SVf "Z"), (CPL.Comma ((CPL.Star (CPL.SVf
      "X")), (CPL.SVf "Y")))))

  (** val coq_Mrls : (PL.formula, CPL.structr) rule **)

  let coq_Mrls =
    ((Sequent ((CPL.SVf "X"), (CPL.Comma ((CPL.Star (CPL.SVf "Y")), (CPL.SVf
      "Z")))))::[]),(Sequent ((CPL.Comma ((CPL.SVf "Y"), (CPL.SVf "X"))),
      (CPL.SVf "Z")))

  (** val coq_Snn : (PL.formula, CPL.structr) rule **)

  let coq_Snn =
    ((Sequent ((CPL.SVf "X"), (CPL.SVf "Y")))::[]),(Sequent ((CPL.Star
      (CPL.SVf "Y")), (CPL.Star (CPL.SVf "X"))))

  (** val coq_Sns : (PL.formula, CPL.structr) rule **)

  let coq_Sns =
    ((Sequent ((CPL.SVf "X"), (CPL.Star (CPL.SVf "Y"))))::[]),(Sequent
      ((CPL.SVf "Y"), (CPL.Star (CPL.SVf "X"))))

  (** val coq_DSEr : (PL.formula, CPL.structr) rule **)

  let coq_DSEr =
    ((Sequent ((CPL.SVf "X"), (CPL.Star (CPL.Star (CPL.SVf
      "Y")))))::[]),(Sequent ((CPL.SVf "X"), (CPL.SVf "Y")))

  (** val coq_Mrrn : (PL.formula, CPL.structr) rule **)

  let coq_Mrrn =
    ((Sequent ((CPL.SVf "X"), (CPL.Comma ((CPL.SVf "Y"), (CPL.SVf
      "Z")))))::[]),(Sequent ((CPL.Comma ((CPL.SVf "X"), (CPL.Star (CPL.SVf
      "Z")))), (CPL.SVf "Y")))

  (** val coq_Mlrsrln : (PL.formula, CPL.structr) rule **)

  let coq_Mlrsrln =
    ((Sequent ((CPL.Comma ((CPL.SVf "X"), (CPL.Star (CPL.SVf "Y")))),
      (CPL.SVf "Z")))::[]),(Sequent ((CPL.Comma ((CPL.Star (CPL.SVf "Z")),
      (CPL.SVf "X"))), (CPL.SVf "Y")))

  (** val coq_Mlls : (PL.formula, CPL.structr) rule **)

  let coq_Mlls =
    ((Sequent ((CPL.Comma ((CPL.Star (CPL.SVf "X")), (CPL.SVf "Y"))),
      (CPL.SVf "Z")))::[]),(Sequent ((CPL.SVf "Y"), (CPL.Comma ((CPL.SVf
      "X"), (CPL.SVf "Z")))))

  (** val coq_Ssn : (PL.formula, CPL.structr) rule **)

  let coq_Ssn =
    ((Sequent ((CPL.Star (CPL.SVf "X")), (CPL.SVf "Y")))::[]),(Sequent
      ((CPL.Star (CPL.SVf "Y")), (CPL.SVf "X")))

  (** val coq_Sss : (PL.formula, CPL.structr) rule **)

  let coq_Sss =
    ((Sequent ((CPL.Star (CPL.SVf "X")), (CPL.Star (CPL.SVf
      "Y"))))::[]),(Sequent ((CPL.SVf "Y"), (CPL.SVf "X")))

  (** val coq_DSEl : (PL.formula, CPL.structr) rule **)

  let coq_DSEl =
    ((Sequent ((CPL.Star (CPL.Star (CPL.SVf "X"))), (CPL.SVf
      "Y")))::[]),(Sequent ((CPL.SVf "X"), (CPL.SVf "Y")))

  (** val coq_Commr : (PL.formula, CPL.structr) rule **)

  let coq_Commr =
    ((Sequent ((CPL.SVf "X"), (CPL.Comma ((CPL.SVf "Y"), (CPL.SVf
      "Z")))))::[]),(Sequent ((CPL.SVf "X"), (CPL.Comma ((CPL.SVf "Z"),
      (CPL.SVf "Y")))))

  (** val coq_Mlln : (PL.formula, CPL.structr) rule **)

  let coq_Mlln =
    ((Sequent ((CPL.Comma ((CPL.SVf "X"), (CPL.SVf "Y"))), (CPL.SVf
      "Z")))::[]),(Sequent ((CPL.SVf "Y"), (CPL.Comma ((CPL.Star (CPL.SVf
      "X")), (CPL.SVf "Z")))))

  (** val coq_Mrrs : (PL.formula, CPL.structr) rule **)

  let coq_Mrrs =
    ((Sequent ((CPL.SVf "X"), (CPL.Comma ((CPL.SVf "Y"), (CPL.Star (CPL.SVf
      "Z"))))))::[]),(Sequent ((CPL.Comma ((CPL.SVf "X"), (CPL.SVf "Z"))),
      (CPL.SVf "Y")))

  (** val coq_Wkl : (PL.formula, CPL.structr) rule **)

  let coq_Wkl =
    ((Sequent ((CPL.SVf "X"), (CPL.SVf "Y")))::[]),(Sequent ((CPL.Comma
      ((CPL.SVf "Z"), (CPL.SVf "X"))), (CPL.SVf "Y")))
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

(** val cPL_DC : (PL.formula, CPL.structr) dISPCALC **)

let cPL_DC =
  (atrefl eqDec_formula f_PL pL_LANG eqDec_structr f_CPL cPL_LANG)::(CPLRules.coq_Iwr::(CPLRules.coq_Iaddl::(CPLRules.coq_Idell::(CPLRules.coq_Iwl::(CPLRules.coq_Comml::(CPLRules.coq_Contl::(CPLRules.coq_Assol::(
    (cUT eqDec_formula f_PL pL_LANG eqDec_structr f_CPL cPL_LANG)::(CPLRules.coq_Topl::(CPLRules.coq_Topr::(CPLRules.coq_Botl::(CPLRules.coq_Botr::(CPLRules.coq_Negl::(CPLRules.coq_Negr::(CPLRules.coq_Conl::(CPLRules.coq_Conr::(CPLRules.coq_Disl::(CPLRules.coq_Disr::(CPLRules.coq_Impl::(CPLRules.coq_Impr::(CPLRules.coq_Mlrn::(CPLRules.coq_Mrrslln::(CPLRules.coq_Mrls::(CPLRules.coq_Snn::(CPLRules.coq_Sns::(CPLRules.coq_DSEr::(CPLRules.coq_Mrrn::(CPLRules.coq_Mlrsrln::(CPLRules.coq_Mlls::[])))))))))))))))))))))))))))))

module CPLDeriv =
 struct
  (** val dernc_Sss : (PL.formula, CPL.structr) derivRuleNC **)

  let dernc_Sss =
    derivRuleNC_rule_bw_inDC eqDec_formula f_PL pL_LANG eqDec_structr f_CPL
      cPL_LANG cPL_DC ((Sequent ((CPL.Star (CPL.SVf "X")), (CPL.Star (CPL.SVf
      "Y"))))::[])
      (premsRule eqDec_formula f_PL pL_LANG eqDec_structr f_CPL cPL_LANG
        CPLRules.coq_DSEr)
      (conclRule eqDec_formula f_PL pL_LANG eqDec_structr f_CPL cPL_LANG
        CPLRules.coq_DSEr)
      (seq_matchsub eqDec_formula f_PL pL_LANG eqDec_structr f_CPL cPL_LANG
        (conclRule eqDec_formula f_PL pL_LANG eqDec_structr f_CPL cPL_LANG
          CPLRules.coq_DSEr) (Sequent ((CPL.SVf "Y"), (CPL.SVf "X"))))
      (ForallT_cons ((Sequent ((CPL.SVf "X"), (CPL.Star (CPL.Star (CPL.SVf
      "Y"))))), [],
      (derivRuleNC_rule_bw_inDC eqDec_formula f_PL pL_LANG eqDec_structr
        f_CPL cPL_LANG cPL_DC ((Sequent ((CPL.Star (CPL.SVf "X")), (CPL.Star
        (CPL.SVf "Y"))))::[])
        (premsRule eqDec_formula f_PL pL_LANG eqDec_structr f_CPL cPL_LANG
          CPLRules.coq_Sns)
        (conclRule eqDec_formula f_PL pL_LANG eqDec_structr f_CPL cPL_LANG
          CPLRules.coq_Sns)
        (seq_matchsub eqDec_formula f_PL pL_LANG eqDec_structr f_CPL cPL_LANG
          (conclRule eqDec_formula f_PL pL_LANG eqDec_structr f_CPL cPL_LANG
            CPLRules.coq_Sns) (Sequent ((CPL.SVf "Y"), (CPL.Star (CPL.Star
          (CPL.SVf "X")))))) (ForallT_cons ((Sequent ((CPL.SVf "X"),
        (CPL.Star (CPL.SVf "Y")))), [],
        (derivRuleNC_refl eqDec_formula f_PL pL_LANG eqDec_structr f_CPL
          cPL_LANG cPL_DC (Sequent ((CPL.Star (CPL.SVf "X")), (CPL.Star
          (CPL.SVf "Y"))))), ForallT_nil))), ForallT_nil))

  (** val dernc_DSEl : (PL.formula, CPL.structr) derivRuleNC **)

  let dernc_DSEl =
    let x = CPL.SVf "X" in
    let y = CPL.SVf "Y" in
    extend_DerivRuleNC eqDec_formula f_PL pL_LANG eqDec_structr f_CPL
      cPL_LANG cPL_DC CPLRules.coq_Sss dernc_Sss CPLRules.coq_DSEl (Der
      ((Sequent (x, y)), CPLRules.coq_Sss, ((Der ((Sequent ((CPL.Star y),
      (CPL.Star x))), CPLRules.coq_DSEr, ((Der ((Sequent ((CPL.Star y),
      (CPL.Star (CPL.Star (CPL.Star x))))), CPLRules.coq_Snn, ((Unf (Sequent
      ((CPL.Star (CPL.Star x)), y)))::[])))::[])))::[])))

  (** val dernc_Ssn : (PL.formula, CPL.structr) derivRuleNC **)

  let dernc_Ssn =
    Der ((Sequent ((CPL.Star (CPL.SVf "Y")), (CPL.SVf "X"))),
      CPLRules.coq_DSEr, ((Der ((Sequent ((CPL.Star (CPL.SVf "Y")), (CPL.Star
      (CPL.Star (CPL.SVf "X"))))), CPLRules.coq_Snn, ((Unf (Sequent
      ((CPL.Star (CPL.SVf "X")), (CPL.SVf "Y"))))::[])))::[]))

  (** val dernc_Sns : (PL.formula, CPL.structr) derivRuleNC **)

  let dernc_Sns =
    let x = CPL.SVf "X" in
    let y = CPL.SVf "Y" in
    extend_DerivRuleNC eqDec_formula f_PL pL_LANG eqDec_structr f_CPL
      cPL_LANG cPL_DC CPLRules.coq_DSEl dernc_DSEl CPLRules.coq_Sns (Der
      ((Sequent (y, (CPL.Star x))), CPLRules.coq_DSEl, ((Der ((Sequent
      ((CPL.Star (CPL.Star y)), (CPL.Star x))), CPLRules.coq_Snn, ((Unf
      (Sequent (x, (CPL.Star y))))::[])))::[])))

  (** val dernc_Mrrs : (PL.formula, CPL.structr) derivRuleNC **)

  let dernc_Mrrs =
    let x = CPL.SVf "X" in
    let y = CPL.SVf "Y" in
    let z = CPL.SVf "Z" in
    Der ((Sequent ((CPL.Comma (x, z)), y)), CPLRules.coq_Mrls, ((Der
    ((Sequent (z, (CPL.Comma ((CPL.Star x), y)))), CPLRules.coq_Mrrslln,
    ((Unf (Sequent (x, (CPL.Comma (y, (CPL.Star z))))))::[])))::[]))

  (** val dernc_Commr : (PL.formula, CPL.structr) derivRuleNC **)

  let dernc_Commr =
    let x = CPL.SVf "X" in
    let y = CPL.SVf "Y" in
    let z = CPL.SVf "Z" in
    Der ((Sequent (x, (CPL.Comma (z, y)))), CPLRules.coq_Mlls, ((Der
    ((Sequent ((CPL.Comma ((CPL.Star z), x)), y)), CPLRules.coq_Comml, ((Der
    ((Sequent ((CPL.Comma (x, (CPL.Star z))), y)), CPLRules.coq_Mrrn, ((Unf
    (Sequent (x, (CPL.Comma (y, z)))))::[])))::[])))::[]))

  (** val dernc_Mlln : (PL.formula, CPL.structr) derivRuleNC **)

  let dernc_Mlln =
    let x = CPL.SVf "X" in
    let y = CPL.SVf "Y" in
    let z = CPL.SVf "Z" in
    extend_DerivRuleNC eqDec_formula f_PL pL_LANG eqDec_structr f_CPL
      cPL_LANG cPL_DC CPLRules.coq_Commr dernc_Commr CPLRules.coq_Mlln (Der
      ((Sequent (y, (CPL.Comma ((CPL.Star x), z)))), CPLRules.coq_Commr,
      ((Der ((Sequent (y, (CPL.Comma (z, (CPL.Star x))))), CPLRules.coq_Mlrn,
      ((Der ((Sequent ((CPL.Comma (y, x)), z)), CPLRules.coq_Comml, ((Unf
      (Sequent ((CPL.Comma (x, y)), z)))::[])))::[])))::[])))

  (** val dernc_Wkl : (PL.formula, CPL.structr) derivRuleNC **)

  let dernc_Wkl =
    let x = CPL.SVf "X" in
    let y = CPL.SVf "Y" in
    let z = CPL.SVf "Z" in
    extend_DerivRuleNC eqDec_formula f_PL pL_LANG eqDec_structr f_CPL
      cPL_LANG cPL_DC CPLRules.coq_Mlln dernc_Mlln CPLRules.coq_Wkl (Der
      ((Sequent ((CPL.Comma (z, x)), y)), CPLRules.coq_Comml, ((Der ((Sequent
      ((CPL.Comma (x, z)), y)), CPLRules.coq_Mrls, ((Der ((Sequent (z,
      (CPL.Comma ((CPL.Star x), y)))), CPLRules.coq_Iwl, ((Der ((Sequent
      (CPL.I, (CPL.Comma ((CPL.Star x), y)))), CPLRules.coq_Mlln, ((Der
      ((Sequent ((CPL.Comma (x, CPL.I)), y)), CPLRules.coq_Iaddl, ((Unf
      (Sequent (x, y)))::[])))::[])))::[])))::[])))::[])))

  (** val dernc_frefl :
      PL.formula -> (PL.formula, CPL.structr) derivRuleNC **)

  let rec dernc_frefl = function
  | PL.Atf p ->
    Der ((Sequent ((CPL.FSf (PL.Atf p)), (CPL.FSf (PL.Atf p)))),
      (atrefl eqDec_formula f_PL pL_LANG eqDec_structr f_CPL cPL_LANG), [])
  | PL.FVf _ -> assert false (* absurd case *)
  | PL.Top ->
    Der ((Sequent ((CPL.FSf PL.Top), (CPL.FSf PL.Top))), CPLRules.coq_Topl,
      ((Der ((Sequent (CPL.I, (CPL.FSf PL.Top))), CPLRules.coq_Topr,
      []))::[]))
  | PL.Bot ->
    Der ((Sequent ((CPL.FSf PL.Bot), (CPL.FSf PL.Bot))), CPLRules.coq_Botr,
      ((Der ((Sequent ((CPL.FSf PL.Bot), CPL.I)), CPLRules.coq_Botl,
      []))::[]))
  | PL.Neg phi ->
    let iHA = dernc_frefl phi in
    derivRuleNC_rule_bw_inDC eqDec_formula f_PL pL_LANG eqDec_structr f_CPL
      cPL_LANG cPL_DC []
      (premsRule eqDec_formula f_PL pL_LANG eqDec_structr f_CPL cPL_LANG
        CPLRules.coq_Negr)
      (conclRule eqDec_formula f_PL pL_LANG eqDec_structr f_CPL cPL_LANG
        CPLRules.coq_Negr)
      (seq_matchsub eqDec_formula f_PL pL_LANG eqDec_structr f_CPL cPL_LANG
        (conclRule eqDec_formula f_PL pL_LANG eqDec_structr f_CPL cPL_LANG
          CPLRules.coq_Negr) (Sequent ((cPL_LANG.fS (PL.Neg phi)),
        (cPL_LANG.fS (PL.Neg phi))))) (ForallT_cons ((Sequent ((CPL.SVf "X"),
      (CPL.Star (CPL.FSf (PL.FVf "A"))))), [],
      (derivRuleNC_rule_bw_inDC eqDec_formula f_PL pL_LANG eqDec_structr
        f_CPL cPL_LANG cPL_DC []
        (premsRule eqDec_formula f_PL pL_LANG eqDec_structr f_CPL cPL_LANG
          CPLRules.coq_Negl)
        (conclRule eqDec_formula f_PL pL_LANG eqDec_structr f_CPL cPL_LANG
          CPLRules.coq_Negl)
        (seq_matchsub eqDec_formula f_PL pL_LANG eqDec_structr f_CPL cPL_LANG
          (conclRule eqDec_formula f_PL pL_LANG eqDec_structr f_CPL cPL_LANG
            CPLRules.coq_Negl) (Sequent ((CPL.FSf (PL.Neg phi)), (CPL.Star
          (CPL.FSf phi))))) (ForallT_cons ((Sequent ((CPL.Star (CPL.FSf
        (PL.FVf "A"))), (CPL.SVf "X"))), [],
        (derivRuleNC_rule_bw_inDC eqDec_formula f_PL pL_LANG eqDec_structr
          f_CPL cPL_LANG cPL_DC []
          (premsRule eqDec_formula f_PL pL_LANG eqDec_structr f_CPL cPL_LANG
            CPLRules.coq_Snn)
          (conclRule eqDec_formula f_PL pL_LANG eqDec_structr f_CPL cPL_LANG
            CPLRules.coq_Snn)
          (seq_matchsub eqDec_formula f_PL pL_LANG eqDec_structr f_CPL
            cPL_LANG
            (conclRule eqDec_formula f_PL pL_LANG eqDec_structr f_CPL
              cPL_LANG CPLRules.coq_Snn) (Sequent ((CPL.Star (CPL.FSf phi)),
            (CPL.Star (CPL.FSf phi))))) (ForallT_cons ((Sequent ((CPL.SVf
          "X"), (CPL.SVf "Y"))), [], iHA, ForallT_nil))), ForallT_nil))),
      ForallT_nil))
  | PL.Imp (phi, psi) ->
    let iHA1 = dernc_frefl phi in
    let iHA2 = dernc_frefl psi in
    derivRuleNC_rule_bw_inDC eqDec_formula f_PL pL_LANG eqDec_structr f_CPL
      cPL_LANG cPL_DC []
      (premsRule eqDec_formula f_PL pL_LANG eqDec_structr f_CPL cPL_LANG
        CPLRules.coq_Impr)
      (conclRule eqDec_formula f_PL pL_LANG eqDec_structr f_CPL cPL_LANG
        CPLRules.coq_Impr)
      (seq_matchsub eqDec_formula f_PL pL_LANG eqDec_structr f_CPL cPL_LANG
        (conclRule eqDec_formula f_PL pL_LANG eqDec_structr f_CPL cPL_LANG
          CPLRules.coq_Impr) (Sequent ((cPL_LANG.fS (PL.Imp (phi, psi))),
        (cPL_LANG.fS (PL.Imp (phi, psi)))))) (ForallT_cons ((Sequent
      ((CPL.Comma ((CPL.SVf "X"), (CPL.FSf (PL.FVf "A")))), (CPL.FSf (PL.FVf
      "B")))), [],
      (derivRuleNC_rule_bw_inDC eqDec_formula f_PL pL_LANG eqDec_structr
        f_CPL cPL_LANG cPL_DC []
        (premsRule eqDec_formula f_PL pL_LANG eqDec_structr f_CPL cPL_LANG
          CPLRules.coq_Comml)
        (conclRule eqDec_formula f_PL pL_LANG eqDec_structr f_CPL cPL_LANG
          CPLRules.coq_Comml)
        (seq_matchsub eqDec_formula f_PL pL_LANG eqDec_structr f_CPL cPL_LANG
          (conclRule eqDec_formula f_PL pL_LANG eqDec_structr f_CPL cPL_LANG
            CPLRules.coq_Comml) (Sequent ((CPL.Comma ((CPL.FSf (PL.Imp (phi,
          psi))), (CPL.FSf phi))), (CPL.FSf psi)))) (ForallT_cons ((Sequent
        ((CPL.Comma ((CPL.SVf "X"), (CPL.SVf "Y"))), (CPL.SVf "Z"))), [],
        (derivRuleNC_rule_bw_inDC eqDec_formula f_PL pL_LANG eqDec_structr
          f_CPL cPL_LANG cPL_DC []
          (premsRule eqDec_formula f_PL pL_LANG eqDec_structr f_CPL cPL_LANG
            CPLRules.coq_Mrls)
          (conclRule eqDec_formula f_PL pL_LANG eqDec_structr f_CPL cPL_LANG
            CPLRules.coq_Mrls)
          (seq_matchsub eqDec_formula f_PL pL_LANG eqDec_structr f_CPL
            cPL_LANG
            (conclRule eqDec_formula f_PL pL_LANG eqDec_structr f_CPL
              cPL_LANG CPLRules.coq_Mrls) (Sequent ((CPL.Comma ((CPL.FSf
            phi), (CPL.FSf (PL.Imp (phi, psi))))), (CPL.FSf psi))))
          (ForallT_cons ((Sequent ((CPL.SVf "X"), (CPL.Comma ((CPL.Star
          (CPL.SVf "Y")), (CPL.SVf "Z"))))), [],
          (derivRuleNC_rule_bw_inDC eqDec_formula f_PL pL_LANG eqDec_structr
            f_CPL cPL_LANG cPL_DC []
            (premsRule eqDec_formula f_PL pL_LANG eqDec_structr f_CPL
              cPL_LANG CPLRules.coq_Impl)
            (conclRule eqDec_formula f_PL pL_LANG eqDec_structr f_CPL
              cPL_LANG CPLRules.coq_Impl)
            (seq_matchsub eqDec_formula f_PL pL_LANG eqDec_structr f_CPL
              cPL_LANG
              (conclRule eqDec_formula f_PL pL_LANG eqDec_structr f_CPL
                cPL_LANG CPLRules.coq_Impl) (Sequent ((CPL.FSf (PL.Imp (phi,
              psi))), (CPL.Comma ((CPL.Star (CPL.FSf phi)), (CPL.FSf psi))))))
            (ForallT_cons ((Sequent ((CPL.SVf "X"), (CPL.FSf (PL.FVf "A")))),
            ((Sequent ((CPL.FSf (PL.FVf "B")), (CPL.SVf "Y")))::[]), iHA1,
            (ForallT_cons ((Sequent ((CPL.FSf (PL.FVf "B")), (CPL.SVf "Y"))),
            [], iHA2, ForallT_nil))))), ForallT_nil))), ForallT_nil))),
      ForallT_nil))
  | PL.Dis (phi, psi) ->
    let iHA1 = dernc_frefl phi in
    let iHA2 = dernc_frefl psi in
    derivRuleNC_rule_bw_inDC eqDec_formula f_PL pL_LANG eqDec_structr f_CPL
      cPL_LANG cPL_DC []
      (premsRule eqDec_formula f_PL pL_LANG eqDec_structr f_CPL cPL_LANG
        CPLRules.coq_Disr)
      (conclRule eqDec_formula f_PL pL_LANG eqDec_structr f_CPL cPL_LANG
        CPLRules.coq_Disr)
      (seq_matchsub eqDec_formula f_PL pL_LANG eqDec_structr f_CPL cPL_LANG
        (conclRule eqDec_formula f_PL pL_LANG eqDec_structr f_CPL cPL_LANG
          CPLRules.coq_Disr) (Sequent ((cPL_LANG.fS (PL.Dis (phi, psi))),
        (cPL_LANG.fS (PL.Dis (phi, psi)))))) (ForallT_cons ((Sequent
      ((CPL.SVf "X"), (CPL.Comma ((CPL.FSf (PL.FVf "A")), (CPL.FSf (PL.FVf
      "B")))))), [],
      (derivRuleNC_rule_bw_inDC eqDec_formula f_PL pL_LANG eqDec_structr
        f_CPL cPL_LANG cPL_DC []
        (premsRule eqDec_formula f_PL pL_LANG eqDec_structr f_CPL cPL_LANG
          CPLRules.coq_Disl)
        (conclRule eqDec_formula f_PL pL_LANG eqDec_structr f_CPL cPL_LANG
          CPLRules.coq_Disl)
        (seq_matchsub eqDec_formula f_PL pL_LANG eqDec_structr f_CPL cPL_LANG
          (conclRule eqDec_formula f_PL pL_LANG eqDec_structr f_CPL cPL_LANG
            CPLRules.coq_Disl) (Sequent ((CPL.FSf (PL.Dis (phi, psi))),
          (CPL.Comma ((CPL.FSf phi), (CPL.FSf psi)))))) (ForallT_cons
        ((Sequent ((CPL.FSf (PL.FVf "A")), (CPL.SVf "X"))), ((Sequent
        ((CPL.FSf (PL.FVf "B")), (CPL.SVf "Y")))::[]), iHA1, (ForallT_cons
        ((Sequent ((CPL.FSf (PL.FVf "B")), (CPL.SVf "Y"))), [], iHA2,
        ForallT_nil))))), ForallT_nil))
  | PL.Con (phi, psi) ->
    let iHA1 = dernc_frefl phi in
    let iHA2 = dernc_frefl psi in
    derivRuleNC_rule_bw_inDC eqDec_formula f_PL pL_LANG eqDec_structr f_CPL
      cPL_LANG cPL_DC []
      (premsRule eqDec_formula f_PL pL_LANG eqDec_structr f_CPL cPL_LANG
        CPLRules.coq_Conl)
      (conclRule eqDec_formula f_PL pL_LANG eqDec_structr f_CPL cPL_LANG
        CPLRules.coq_Conl)
      (seq_matchsub eqDec_formula f_PL pL_LANG eqDec_structr f_CPL cPL_LANG
        (conclRule eqDec_formula f_PL pL_LANG eqDec_structr f_CPL cPL_LANG
          CPLRules.coq_Conl) (Sequent ((cPL_LANG.fS (PL.Con (phi, psi))),
        (cPL_LANG.fS (PL.Con (phi, psi)))))) (ForallT_cons ((Sequent
      ((CPL.Comma ((CPL.FSf (PL.FVf "A")), (CPL.FSf (PL.FVf "B")))), (CPL.SVf
      "X"))), [],
      (derivRuleNC_rule_bw_inDC eqDec_formula f_PL pL_LANG eqDec_structr
        f_CPL cPL_LANG cPL_DC []
        (premsRule eqDec_formula f_PL pL_LANG eqDec_structr f_CPL cPL_LANG
          CPLRules.coq_Conr)
        (conclRule eqDec_formula f_PL pL_LANG eqDec_structr f_CPL cPL_LANG
          CPLRules.coq_Conr)
        (seq_matchsub eqDec_formula f_PL pL_LANG eqDec_structr f_CPL cPL_LANG
          (conclRule eqDec_formula f_PL pL_LANG eqDec_structr f_CPL cPL_LANG
            CPLRules.coq_Conr) (Sequent ((CPL.Comma ((CPL.FSf phi), (CPL.FSf
          psi))), (CPL.FSf (PL.Con (phi, psi)))))) (ForallT_cons ((Sequent
        ((CPL.SVf "X"), (CPL.FSf (PL.FVf "A")))), ((Sequent ((CPL.SVf "Y"),
        (CPL.FSf (PL.FVf "B"))))::[]), iHA1, (ForallT_cons ((Sequent
        ((CPL.SVf "Y"), (CPL.FSf (PL.FVf "B")))), [], iHA2, ForallT_nil))))),
      ForallT_nil))

  (** val coq_CPL_DC_derr_frefl :
      PL.formula -> (PL.formula, CPL.structr) derivRule **)

  let coq_CPL_DC_derr_frefl a =
    derrnc_derr eqDec_formula f_PL pL_LANG eqDec_structr f_CPL cPL_LANG
      cPL_DC
      (frefl eqDec_formula f_PL pL_LANG eqDec_structr f_CPL cPL_LANG a)
      (dernc_frefl a)
 end

module CPLBelnap =
 struct
  (** val coq_C8_Neg :
      CPL.structr -> CPL.structr -> PL.formula -> (PL.formula, CPL.structr)
      dertree list -> (PL.formula, CPL.structr) dertree **)

  let coq_C8_Neg x y a ld =
    c8_case_alt_imp_C8_case eqDec_formula f_PL pL_LANG eqDec_structr f_CPL
      cPL_LANG cPL_DC x y ((Sequent (x, (CPL.Star (CPL.FSf a))))::((Sequent
      ((CPL.Star (CPL.FSf a)), y))::[])) (fun hders ->
      let x0 = fun dC cs ->
        let _,x0 =
          forallT_deriv_cofseqs_iff eqDec_formula f_PL pL_LANG eqDec_structr
            f_CPL cPL_LANG dC cs
        in
        x0
      in
      let hders0 =
        x0 cPL_DC ((Sequent (x, (CPL.Star (CPL.FSf a))))::((Sequent
          ((CPL.Star (CPL.FSf a)), y))::[])) hders
      in
      let hders1 =
        forallT_inv (Sequent (x, (CPL.Star (CPL.FSf a)))) ((Sequent
          ((CPL.Star (CPL.FSf a)), y))::[]) hders0
      in
      let hders2 =
        forallT_inv_tail (Sequent (x, (CPL.Star (CPL.FSf a)))) ((Sequent
          ((CPL.Star (CPL.FSf a)), y))::[]) hders0
      in
      let hders3 = forallT_inv (Sequent ((CPL.Star (CPL.FSf a)), y)) [] hders2
      in
      deriv_cofseq_rule_bw_InstNC eqDec_formula f_PL pL_LANG eqDec_structr
        f_CPL cPL_LANG cPL_DC
        (premsRule eqDec_formula f_PL pL_LANG eqDec_structr f_CPL cPL_LANG
          CPLRules.coq_Sss)
        (conclRule eqDec_formula f_PL pL_LANG eqDec_structr f_CPL cPL_LANG
          CPLRules.coq_Sss)
        (seq_matchsub eqDec_formula f_PL pL_LANG eqDec_structr f_CPL cPL_LANG
          (conclRule eqDec_formula f_PL pL_LANG eqDec_structr f_CPL cPL_LANG
            CPLRules.coq_Sss) (Sequent (x, y))) CPLDeriv.dernc_Sss
        (ForallT_cons
        ((seqSubst eqDec_formula f_PL pL_LANG eqDec_structr f_CPL cPL_LANG
           (seq_matchsub eqDec_formula f_PL pL_LANG eqDec_structr f_CPL
             cPL_LANG
             (conclRule eqDec_formula f_PL pL_LANG eqDec_structr f_CPL
               cPL_LANG CPLRules.coq_Sss) (Sequent (x, y))) (Sequent
           ((CPL.Star (CPL.SVf "X")), (CPL.Star (CPL.SVf "Y"))))), [],
        (deriv_cofseq_rule_bw_inDC eqDec_formula f_PL pL_LANG eqDec_structr
          f_CPL cPL_LANG cPL_DC
          (premsRule eqDec_formula f_PL pL_LANG eqDec_structr f_CPL cPL_LANG
            (cUT eqDec_formula f_PL pL_LANG eqDec_structr f_CPL cPL_LANG))
          (conclRule eqDec_formula f_PL pL_LANG eqDec_structr f_CPL cPL_LANG
            (cUT eqDec_formula f_PL pL_LANG eqDec_structr f_CPL cPL_LANG))
          (cUT_spec eqDec_formula f_PL pL_LANG eqDec_structr f_CPL cPL_LANG a
            (CPL.Star y) (CPL.Star x))
          (forallT_deriv_cofseqs eqDec_formula f_PL pL_LANG eqDec_structr
            f_CPL cPL_LANG cPL_DC ((Sequent ((CPL.Star y), (CPL.FSf
            a)))::((Sequent ((CPL.FSf a), (CPL.Star x)))::[])) (ForallT_cons
            ((Sequent ((CPL.Star y), (CPL.FSf a))), ((Sequent ((CPL.FSf a),
            (CPL.Star x)))::[]),
            (deriv_cofseq_rule_bw_InstNC eqDec_formula f_PL pL_LANG
              eqDec_structr f_CPL cPL_LANG cPL_DC
              (premsRule eqDec_formula f_PL pL_LANG eqDec_structr f_CPL
                cPL_LANG CPLRules.coq_Ssn)
              (conclRule eqDec_formula f_PL pL_LANG eqDec_structr f_CPL
                cPL_LANG CPLRules.coq_Ssn)
              (seq_matchsub eqDec_formula f_PL pL_LANG eqDec_structr f_CPL
                cPL_LANG
                (conclRule eqDec_formula f_PL pL_LANG eqDec_structr f_CPL
                  cPL_LANG CPLRules.coq_Ssn) (Sequent ((CPL.Star y), (CPL.FSf
                a)))) CPLDeriv.dernc_Ssn (ForallT_cons
              ((seqSubst eqDec_formula f_PL pL_LANG eqDec_structr f_CPL
                 cPL_LANG
                 (seq_matchsub eqDec_formula f_PL pL_LANG eqDec_structr f_CPL
                   cPL_LANG
                   (conclRule eqDec_formula f_PL pL_LANG eqDec_structr f_CPL
                     cPL_LANG CPLRules.coq_Ssn) (Sequent ((CPL.Star y),
                   (CPL.FSf a)))) (Sequent ((CPL.Star (CPL.SVf "X")),
                 (CPL.SVf "Y")))), [], hders3, ForallT_nil))), (ForallT_cons
            ((Sequent ((CPL.FSf a), (CPL.Star x))), [],
            (deriv_cofseq_rule_bw_InstNC eqDec_formula f_PL pL_LANG
              eqDec_structr f_CPL cPL_LANG cPL_DC
              (premsRule eqDec_formula f_PL pL_LANG eqDec_structr f_CPL
                cPL_LANG CPLRules.coq_Sns)
              (conclRule eqDec_formula f_PL pL_LANG eqDec_structr f_CPL
                cPL_LANG CPLRules.coq_Sns)
              (seq_matchsub eqDec_formula f_PL pL_LANG eqDec_structr f_CPL
                cPL_LANG
                (conclRule eqDec_formula f_PL pL_LANG eqDec_structr f_CPL
                  cPL_LANG CPLRules.coq_Sns) (Sequent ((CPL.FSf a), (CPL.Star
                x)))) CPLDeriv.dernc_Sns (ForallT_cons
              ((seqSubst eqDec_formula f_PL pL_LANG eqDec_structr f_CPL
                 cPL_LANG
                 (seq_matchsub eqDec_formula f_PL pL_LANG eqDec_structr f_CPL
                   cPL_LANG
                   (conclRule eqDec_formula f_PL pL_LANG eqDec_structr f_CPL
                     cPL_LANG CPLRules.coq_Sns) (Sequent ((CPL.FSf a),
                   (CPL.Star x)))) (Sequent ((CPL.SVf "X"), (CPL.Star
                 (CPL.SVf "Y"))))), [], hders1, ForallT_nil))),
            ForallT_nil)))))), ForallT_nil))) ld

  (** val coq_C8_Con :
      CPL.structr -> CPL.structr -> CPL.structr -> PL.formula -> PL.formula
      -> (PL.formula, CPL.structr) dertree list -> (PL.formula, CPL.structr)
      dertree **)

  let coq_C8_Con x y z a b ld =
    c8_case_alt_imp_C8_case eqDec_formula f_PL pL_LANG eqDec_structr f_CPL
      cPL_LANG cPL_DC (CPL.Comma (x, y)) z ((Sequent (x, (CPL.FSf
      a)))::((Sequent (y, (CPL.FSf b)))::((Sequent ((CPL.Comma ((CPL.FSf a),
      (CPL.FSf b))), z))::[]))) (fun hders ->
      let x0 = fun dC cs ->
        let _,x0 =
          forallT_deriv_cofseqs_iff eqDec_formula f_PL pL_LANG eqDec_structr
            f_CPL cPL_LANG dC cs
        in
        x0
      in
      let hders0 =
        x0 cPL_DC ((Sequent (x, (CPL.FSf a)))::((Sequent (y, (CPL.FSf
          b)))::((Sequent ((CPL.Comma ((CPL.FSf a), (CPL.FSf b))), z))::[])))
          hders
      in
      let hders1 =
        forallT_inv (Sequent (x, (CPL.FSf a))) ((Sequent (y, (CPL.FSf
          b)))::((Sequent ((CPL.Comma ((CPL.FSf a), (CPL.FSf b))), z))::[]))
          hders0
      in
      let hders2 =
        forallT_inv_tail (Sequent (x, (CPL.FSf a))) ((Sequent (y, (CPL.FSf
          b)))::((Sequent ((CPL.Comma ((CPL.FSf a), (CPL.FSf b))), z))::[]))
          hders0
      in
      let hders3 =
        forallT_inv (Sequent (y, (CPL.FSf b))) ((Sequent ((CPL.Comma
          ((CPL.FSf a), (CPL.FSf b))), z))::[]) hders2
      in
      let hders4 =
        forallT_inv_tail (Sequent (y, (CPL.FSf b))) ((Sequent ((CPL.Comma
          ((CPL.FSf a), (CPL.FSf b))), z))::[]) hders2
      in
      let hders5 =
        forallT_inv (Sequent ((CPL.Comma ((CPL.FSf a), (CPL.FSf b))), z)) []
          hders4
      in
      deriv_cofseq_rule_bw_InstNC eqDec_formula f_PL pL_LANG eqDec_structr
        f_CPL cPL_LANG cPL_DC
        (premsRule eqDec_formula f_PL pL_LANG eqDec_structr f_CPL cPL_LANG
          CPLRules.coq_Mrrs)
        (conclRule eqDec_formula f_PL pL_LANG eqDec_structr f_CPL cPL_LANG
          CPLRules.coq_Mrrs)
        (seq_matchsub eqDec_formula f_PL pL_LANG eqDec_structr f_CPL cPL_LANG
          (conclRule eqDec_formula f_PL pL_LANG eqDec_structr f_CPL cPL_LANG
            CPLRules.coq_Mrrs) (Sequent ((CPL.Comma (x, y)), z)))
        CPLDeriv.dernc_Mrrs (ForallT_cons
        ((seqSubst eqDec_formula f_PL pL_LANG eqDec_structr f_CPL cPL_LANG
           (seq_matchsub eqDec_formula f_PL pL_LANG eqDec_structr f_CPL
             cPL_LANG
             (conclRule eqDec_formula f_PL pL_LANG eqDec_structr f_CPL
               cPL_LANG CPLRules.coq_Mrrs) (Sequent ((CPL.Comma (x, y)), z)))
           (Sequent ((CPL.SVf "X"), (CPL.Comma ((CPL.SVf "Y"), (CPL.Star
           (CPL.SVf "Z"))))))), [],
        (deriv_cofseq_rule_bw_inDC eqDec_formula f_PL pL_LANG eqDec_structr
          f_CPL cPL_LANG cPL_DC
          (premsRule eqDec_formula f_PL pL_LANG eqDec_structr f_CPL cPL_LANG
            (cUT eqDec_formula f_PL pL_LANG eqDec_structr f_CPL cPL_LANG))
          (conclRule eqDec_formula f_PL pL_LANG eqDec_structr f_CPL cPL_LANG
            (cUT eqDec_formula f_PL pL_LANG eqDec_structr f_CPL cPL_LANG))
          (cUT_spec eqDec_formula f_PL pL_LANG eqDec_structr f_CPL cPL_LANG a
            x (CPL.Comma (z, (CPL.Star y))))
          (forallT_deriv_cofseqs eqDec_formula f_PL pL_LANG eqDec_structr
            f_CPL cPL_LANG cPL_DC ((Sequent (x, (CPL.FSf a)))::((Sequent
            ((CPL.FSf a), (CPL.Comma (z, (CPL.Star y)))))::[])) (ForallT_cons
            ((Sequent (x, (CPL.FSf a))), ((Sequent ((CPL.FSf a), (CPL.Comma
            (z, (CPL.Star y)))))::[]), hders1, (ForallT_cons ((Sequent
            ((CPL.FSf a), (CPL.Comma (z, (CPL.Star y))))), [],
            (deriv_cofseq_rule_bw_inDC eqDec_formula f_PL pL_LANG
              eqDec_structr f_CPL cPL_LANG cPL_DC
              (premsRule eqDec_formula f_PL pL_LANG eqDec_structr f_CPL
                cPL_LANG CPLRules.coq_Mlrn)
              (conclRule eqDec_formula f_PL pL_LANG eqDec_structr f_CPL
                cPL_LANG CPLRules.coq_Mlrn)
              (seq_matchsub eqDec_formula f_PL pL_LANG eqDec_structr f_CPL
                cPL_LANG
                (conclRule eqDec_formula f_PL pL_LANG eqDec_structr f_CPL
                  cPL_LANG CPLRules.coq_Mlrn) (Sequent ((CPL.FSf a),
                (CPL.Comma (z, (CPL.Star y))))))
              (forallT_deriv_cofseqs eqDec_formula f_PL pL_LANG eqDec_structr
                f_CPL cPL_LANG cPL_DC
                (map
                  (seqSubst eqDec_formula f_PL pL_LANG eqDec_structr f_CPL
                    cPL_LANG
                    (seq_matchsub eqDec_formula f_PL pL_LANG eqDec_structr
                      f_CPL cPL_LANG
                      (conclRule eqDec_formula f_PL pL_LANG eqDec_structr
                        f_CPL cPL_LANG CPLRules.coq_Mlrn) (Sequent ((CPL.FSf
                      a), (CPL.Comma (z, (CPL.Star y)))))))
                  (premsRule eqDec_formula f_PL pL_LANG eqDec_structr f_CPL
                    cPL_LANG CPLRules.coq_Mlrn)) (ForallT_cons
                ((seqSubst eqDec_formula f_PL pL_LANG eqDec_structr f_CPL
                   cPL_LANG
                   (seq_matchsub eqDec_formula f_PL pL_LANG eqDec_structr
                     f_CPL cPL_LANG
                     (conclRule eqDec_formula f_PL pL_LANG eqDec_structr
                       f_CPL cPL_LANG CPLRules.coq_Mlrn) (Sequent ((CPL.FSf
                     a), (CPL.Comma (z, (CPL.Star y)))))) (Sequent
                   ((CPL.Comma ((CPL.SVf "X"), (CPL.SVf "Y"))), (CPL.SVf
                   "Z")))), [],
                (deriv_cofseq_rule_bw_inDC eqDec_formula f_PL pL_LANG
                  eqDec_structr f_CPL cPL_LANG cPL_DC
                  (premsRule eqDec_formula f_PL pL_LANG eqDec_structr f_CPL
                    cPL_LANG CPLRules.coq_Mrls)
                  (conclRule eqDec_formula f_PL pL_LANG eqDec_structr f_CPL
                    cPL_LANG CPLRules.coq_Mrls)
                  (seq_matchsub eqDec_formula f_PL pL_LANG eqDec_structr
                    f_CPL cPL_LANG
                    (conclRule eqDec_formula f_PL pL_LANG eqDec_structr f_CPL
                      cPL_LANG CPLRules.coq_Mrls) (Sequent ((CPL.Comma
                    ((CPL.FSf a), y)), z)))
                  (forallT_deriv_cofseqs eqDec_formula f_PL pL_LANG
                    eqDec_structr f_CPL cPL_LANG cPL_DC
                    (map
                      (seqSubst eqDec_formula f_PL pL_LANG eqDec_structr
                        f_CPL cPL_LANG
                        (seq_matchsub eqDec_formula f_PL pL_LANG
                          eqDec_structr f_CPL cPL_LANG
                          (conclRule eqDec_formula f_PL pL_LANG eqDec_structr
                            f_CPL cPL_LANG CPLRules.coq_Mrls) (Sequent
                          ((CPL.Comma ((CPL.FSf a), y)), z))))
                      (premsRule eqDec_formula f_PL pL_LANG eqDec_structr
                        f_CPL cPL_LANG CPLRules.coq_Mrls)) (ForallT_cons
                    ((seqSubst eqDec_formula f_PL pL_LANG eqDec_structr f_CPL
                       cPL_LANG
                       (seq_matchsub eqDec_formula f_PL pL_LANG eqDec_structr
                         f_CPL cPL_LANG
                         (conclRule eqDec_formula f_PL pL_LANG eqDec_structr
                           f_CPL cPL_LANG CPLRules.coq_Mrls) (Sequent
                         ((CPL.Comma ((CPL.FSf a), y)), z))) (Sequent
                       ((CPL.SVf "X"), (CPL.Comma ((CPL.Star (CPL.SVf "Y")),
                       (CPL.SVf "Z")))))), [],
                    (deriv_cofseq_rule_bw_inDC eqDec_formula f_PL pL_LANG
                      eqDec_structr f_CPL cPL_LANG cPL_DC
                      (premsRule eqDec_formula f_PL pL_LANG eqDec_structr
                        f_CPL cPL_LANG
                        (cUT eqDec_formula f_PL pL_LANG eqDec_structr f_CPL
                          cPL_LANG))
                      (conclRule eqDec_formula f_PL pL_LANG eqDec_structr
                        f_CPL cPL_LANG
                        (cUT eqDec_formula f_PL pL_LANG eqDec_structr f_CPL
                          cPL_LANG))
                      (cUT_spec eqDec_formula f_PL pL_LANG eqDec_structr
                        f_CPL cPL_LANG b y (CPL.Comma ((CPL.Star (CPL.FSf
                        a)), z)))
                      (forallT_deriv_cofseqs eqDec_formula f_PL pL_LANG
                        eqDec_structr f_CPL cPL_LANG cPL_DC ((Sequent (y,
                        (CPL.FSf b)))::((Sequent ((CPL.FSf b), (CPL.Comma
                        ((CPL.Star (CPL.FSf a)), z))))::[])) (ForallT_cons
                        ((Sequent (y, (CPL.FSf b))), ((Sequent ((CPL.FSf b),
                        (CPL.Comma ((CPL.Star (CPL.FSf a)), z))))::[]),
                        hders3, (ForallT_cons ((Sequent ((CPL.FSf b),
                        (CPL.Comma ((CPL.Star (CPL.FSf a)), z)))), [],
                        (deriv_cofseq_rule_bw_InstNC eqDec_formula f_PL
                          pL_LANG eqDec_structr f_CPL cPL_LANG cPL_DC
                          (premsRule eqDec_formula f_PL pL_LANG eqDec_structr
                            f_CPL cPL_LANG CPLRules.coq_Mlln)
                          (conclRule eqDec_formula f_PL pL_LANG eqDec_structr
                            f_CPL cPL_LANG CPLRules.coq_Mlln)
                          (seq_matchsub eqDec_formula f_PL pL_LANG
                            eqDec_structr f_CPL cPL_LANG
                            (conclRule eqDec_formula f_PL pL_LANG
                              eqDec_structr f_CPL cPL_LANG CPLRules.coq_Mlln)
                            (Sequent ((CPL.FSf b), (CPL.Comma ((CPL.Star
                            (CPL.FSf a)), z))))) CPLDeriv.dernc_Mlln
                          (ForallT_cons
                          ((seqSubst eqDec_formula f_PL pL_LANG eqDec_structr
                             f_CPL cPL_LANG
                             (seq_matchsub eqDec_formula f_PL pL_LANG
                               eqDec_structr f_CPL cPL_LANG
                               (conclRule eqDec_formula f_PL pL_LANG
                                 eqDec_structr f_CPL cPL_LANG
                                 CPLRules.coq_Mlln) (Sequent ((CPL.FSf b),
                               (CPL.Comma ((CPL.Star (CPL.FSf a)), z)))))
                             (Sequent ((CPL.Comma ((CPL.SVf "X"), (CPL.SVf
                             "Y"))), (CPL.SVf "Z")))), [], hders5,
                          ForallT_nil))), ForallT_nil)))))), ForallT_nil)))),
                ForallT_nil)))), ForallT_nil)))))), ForallT_nil))) ld

  (** val coq_C8_Dis :
      CPL.structr -> CPL.structr -> CPL.structr -> PL.formula -> PL.formula
      -> (PL.formula, CPL.structr) dertree list -> (PL.formula, CPL.structr)
      dertree **)

  let coq_C8_Dis x y z a b ld =
    c8_case_alt_imp_C8_case eqDec_formula f_PL pL_LANG eqDec_structr f_CPL
      cPL_LANG cPL_DC x (CPL.Comma (y, z)) ((Sequent (x, (CPL.Comma ((CPL.FSf
      a), (CPL.FSf b)))))::((Sequent ((CPL.FSf a), y))::((Sequent ((CPL.FSf
      b), z))::[]))) (fun hders ->
      let x0 = fun dC cs ->
        let _,x0 =
          forallT_deriv_cofseqs_iff eqDec_formula f_PL pL_LANG eqDec_structr
            f_CPL cPL_LANG dC cs
        in
        x0
      in
      let hders0 =
        x0 cPL_DC ((Sequent (x, (CPL.Comma ((CPL.FSf a), (CPL.FSf
          b)))))::((Sequent ((CPL.FSf a), y))::((Sequent ((CPL.FSf b),
          z))::[]))) hders
      in
      let hders1 =
        forallT_inv (Sequent (x, (CPL.Comma ((CPL.FSf a), (CPL.FSf b)))))
          ((Sequent ((CPL.FSf a), y))::((Sequent ((CPL.FSf b), z))::[]))
          hders0
      in
      let hders2 =
        forallT_inv_tail (Sequent (x, (CPL.Comma ((CPL.FSf a), (CPL.FSf
          b))))) ((Sequent ((CPL.FSf a), y))::((Sequent ((CPL.FSf b),
          z))::[])) hders0
      in
      let hders3 =
        forallT_inv (Sequent ((CPL.FSf a), y)) ((Sequent ((CPL.FSf b),
          z))::[]) hders2
      in
      let hders4 =
        forallT_inv_tail (Sequent ((CPL.FSf a), y)) ((Sequent ((CPL.FSf b),
          z))::[]) hders2
      in
      let hders5 = forallT_inv (Sequent ((CPL.FSf b), z)) [] hders4 in
      deriv_cofseq_rule_bw_inDC eqDec_formula f_PL pL_LANG eqDec_structr
        f_CPL cPL_LANG cPL_DC
        (premsRule eqDec_formula f_PL pL_LANG eqDec_structr f_CPL cPL_LANG
          CPLRules.coq_Mlls)
        (conclRule eqDec_formula f_PL pL_LANG eqDec_structr f_CPL cPL_LANG
          CPLRules.coq_Mlls)
        (seq_matchsub eqDec_formula f_PL pL_LANG eqDec_structr f_CPL cPL_LANG
          (conclRule eqDec_formula f_PL pL_LANG eqDec_structr f_CPL cPL_LANG
            CPLRules.coq_Mlls) (Sequent (x, (CPL.Comma (y, z)))))
        (forallT_deriv_cofseqs eqDec_formula f_PL pL_LANG eqDec_structr f_CPL
          cPL_LANG cPL_DC
          (map
            (seqSubst eqDec_formula f_PL pL_LANG eqDec_structr f_CPL cPL_LANG
              (seq_matchsub eqDec_formula f_PL pL_LANG eqDec_structr f_CPL
                cPL_LANG
                (conclRule eqDec_formula f_PL pL_LANG eqDec_structr f_CPL
                  cPL_LANG CPLRules.coq_Mlls) (Sequent (x, (CPL.Comma (y,
                z))))))
            (premsRule eqDec_formula f_PL pL_LANG eqDec_structr f_CPL
              cPL_LANG CPLRules.coq_Mlls)) (ForallT_cons
          ((seqSubst eqDec_formula f_PL pL_LANG eqDec_structr f_CPL cPL_LANG
             (seq_matchsub eqDec_formula f_PL pL_LANG eqDec_structr f_CPL
               cPL_LANG
               (conclRule eqDec_formula f_PL pL_LANG eqDec_structr f_CPL
                 cPL_LANG CPLRules.coq_Mlls) (Sequent (x, (CPL.Comma (y,
               z))))) (Sequent ((CPL.Comma ((CPL.Star (CPL.SVf "X")),
             (CPL.SVf "Y"))), (CPL.SVf "Z")))), [],
          (deriv_cofseq_rule_bw_inDC eqDec_formula f_PL pL_LANG eqDec_structr
            f_CPL cPL_LANG cPL_DC
            (premsRule eqDec_formula f_PL pL_LANG eqDec_structr f_CPL
              cPL_LANG
              (cUT eqDec_formula f_PL pL_LANG eqDec_structr f_CPL cPL_LANG))
            (conclRule eqDec_formula f_PL pL_LANG eqDec_structr f_CPL
              cPL_LANG
              (cUT eqDec_formula f_PL pL_LANG eqDec_structr f_CPL cPL_LANG))
            (cUT_spec eqDec_formula f_PL pL_LANG eqDec_structr f_CPL cPL_LANG
              b (CPL.Comma ((CPL.Star y), x)) z)
            (forallT_deriv_cofseqs eqDec_formula f_PL pL_LANG eqDec_structr
              f_CPL cPL_LANG cPL_DC ((Sequent ((CPL.Comma ((CPL.Star y), x)),
              (CPL.FSf b)))::((Sequent ((CPL.FSf b), z))::[])) (ForallT_cons
              ((Sequent ((CPL.Comma ((CPL.Star y), x)), (CPL.FSf b))),
              ((Sequent ((CPL.FSf b), z))::[]),
              (deriv_cofseq_rule_bw_inDC eqDec_formula f_PL pL_LANG
                eqDec_structr f_CPL cPL_LANG cPL_DC
                (premsRule eqDec_formula f_PL pL_LANG eqDec_structr f_CPL
                  cPL_LANG CPLRules.coq_Mlrsrln)
                (conclRule eqDec_formula f_PL pL_LANG eqDec_structr f_CPL
                  cPL_LANG CPLRules.coq_Mlrsrln)
                (seq_matchsub eqDec_formula f_PL pL_LANG eqDec_structr f_CPL
                  cPL_LANG
                  (conclRule eqDec_formula f_PL pL_LANG eqDec_structr f_CPL
                    cPL_LANG CPLRules.coq_Mlrsrln) (Sequent ((CPL.Comma
                  ((CPL.Star y), x)), (CPL.FSf b))))
                (forallT_deriv_cofseqs eqDec_formula f_PL pL_LANG
                  eqDec_structr f_CPL cPL_LANG cPL_DC
                  (map
                    (seqSubst eqDec_formula f_PL pL_LANG eqDec_structr f_CPL
                      cPL_LANG
                      (seq_matchsub eqDec_formula f_PL pL_LANG eqDec_structr
                        f_CPL cPL_LANG
                        (conclRule eqDec_formula f_PL pL_LANG eqDec_structr
                          f_CPL cPL_LANG CPLRules.coq_Mlrsrln) (Sequent
                        ((CPL.Comma ((CPL.Star y), x)), (CPL.FSf b)))))
                    (premsRule eqDec_formula f_PL pL_LANG eqDec_structr f_CPL
                      cPL_LANG CPLRules.coq_Mlrsrln)) (ForallT_cons
                  ((seqSubst eqDec_formula f_PL pL_LANG eqDec_structr f_CPL
                     cPL_LANG
                     (seq_matchsub eqDec_formula f_PL pL_LANG eqDec_structr
                       f_CPL cPL_LANG
                       (conclRule eqDec_formula f_PL pL_LANG eqDec_structr
                         f_CPL cPL_LANG CPLRules.coq_Mlrsrln) (Sequent
                       ((CPL.Comma ((CPL.Star y), x)), (CPL.FSf b))))
                     (Sequent ((CPL.Comma ((CPL.SVf "X"), (CPL.Star (CPL.SVf
                     "Y")))), (CPL.SVf "Z")))), [],
                  (deriv_cofseq_rule_bw_inDC eqDec_formula f_PL pL_LANG
                    eqDec_structr f_CPL cPL_LANG cPL_DC
                    (premsRule eqDec_formula f_PL pL_LANG eqDec_structr f_CPL
                      cPL_LANG
                      (cUT eqDec_formula f_PL pL_LANG eqDec_structr f_CPL
                        cPL_LANG))
                    (conclRule eqDec_formula f_PL pL_LANG eqDec_structr f_CPL
                      cPL_LANG
                      (cUT eqDec_formula f_PL pL_LANG eqDec_structr f_CPL
                        cPL_LANG))
                    (cUT_spec eqDec_formula f_PL pL_LANG eqDec_structr f_CPL
                      cPL_LANG a (CPL.Comma (x, (CPL.Star (CPL.FSf b)))) y)
                    (forallT_deriv_cofseqs eqDec_formula f_PL pL_LANG
                      eqDec_structr f_CPL cPL_LANG cPL_DC ((Sequent
                      ((CPL.Comma (x, (CPL.Star (CPL.FSf b)))), (CPL.FSf
                      a)))::((Sequent ((CPL.FSf a), y))::[])) (ForallT_cons
                      ((Sequent ((CPL.Comma (x, (CPL.Star (CPL.FSf b)))),
                      (CPL.FSf a))), ((Sequent ((CPL.FSf a), y))::[]),
                      (deriv_cofseq_rule_bw_inDC eqDec_formula f_PL pL_LANG
                        eqDec_structr f_CPL cPL_LANG cPL_DC
                        (premsRule eqDec_formula f_PL pL_LANG eqDec_structr
                          f_CPL cPL_LANG CPLRules.coq_Mrrn)
                        (conclRule eqDec_formula f_PL pL_LANG eqDec_structr
                          f_CPL cPL_LANG CPLRules.coq_Mrrn)
                        (seq_matchsub eqDec_formula f_PL pL_LANG
                          eqDec_structr f_CPL cPL_LANG
                          (conclRule eqDec_formula f_PL pL_LANG eqDec_structr
                            f_CPL cPL_LANG CPLRules.coq_Mrrn) (Sequent
                          ((CPL.Comma (x, (CPL.Star (CPL.FSf b)))), (CPL.FSf
                          a))))
                        (forallT_deriv_cofseqs eqDec_formula f_PL pL_LANG
                          eqDec_structr f_CPL cPL_LANG cPL_DC
                          (map
                            (seqSubst eqDec_formula f_PL pL_LANG
                              eqDec_structr f_CPL cPL_LANG
                              (seq_matchsub eqDec_formula f_PL pL_LANG
                                eqDec_structr f_CPL cPL_LANG
                                (conclRule eqDec_formula f_PL pL_LANG
                                  eqDec_structr f_CPL cPL_LANG
                                  CPLRules.coq_Mrrn) (Sequent ((CPL.Comma (x,
                                (CPL.Star (CPL.FSf b)))), (CPL.FSf a)))))
                            (premsRule eqDec_formula f_PL pL_LANG
                              eqDec_structr f_CPL cPL_LANG CPLRules.coq_Mrrn))
                          (ForallT_cons
                          ((seqSubst eqDec_formula f_PL pL_LANG eqDec_structr
                             f_CPL cPL_LANG
                             (seq_matchsub eqDec_formula f_PL pL_LANG
                               eqDec_structr f_CPL cPL_LANG
                               (conclRule eqDec_formula f_PL pL_LANG
                                 eqDec_structr f_CPL cPL_LANG
                                 CPLRules.coq_Mrrn) (Sequent ((CPL.Comma (x,
                               (CPL.Star (CPL.FSf b)))), (CPL.FSf a))))
                             (Sequent ((CPL.SVf "X"), (CPL.Comma ((CPL.SVf
                             "Y"), (CPL.SVf "Z")))))), [], hders1,
                          ForallT_nil)))), (ForallT_cons ((Sequent ((CPL.FSf
                      a), y)), [], hders3, ForallT_nil)))))), ForallT_nil)))),
              (ForallT_cons ((Sequent ((CPL.FSf b), z)), [], hders5,
              ForallT_nil)))))), ForallT_nil)))) ld

  (** val coq_C8_Imp :
      CPL.structr -> CPL.structr -> CPL.structr -> PL.formula -> PL.formula
      -> (PL.formula, CPL.structr) dertree list -> (PL.formula, CPL.structr)
      dertree **)

  let coq_C8_Imp x y z a b ld =
    c8_case_alt_imp_C8_case eqDec_formula f_PL pL_LANG eqDec_structr f_CPL
      cPL_LANG cPL_DC x (CPL.Comma ((CPL.Star y), z)) ((Sequent (y, (CPL.FSf
      a)))::((Sequent ((CPL.Comma (x, (CPL.FSf a))), (CPL.FSf b)))::((Sequent
      ((CPL.FSf b), z))::[]))) (fun hders ->
      let x0 = fun dC cs ->
        let _,x0 =
          forallT_deriv_cofseqs_iff eqDec_formula f_PL pL_LANG eqDec_structr
            f_CPL cPL_LANG dC cs
        in
        x0
      in
      let hders0 =
        x0 cPL_DC ((Sequent (y, (CPL.FSf a)))::((Sequent ((CPL.Comma (x,
          (CPL.FSf a))), (CPL.FSf b)))::((Sequent ((CPL.FSf b), z))::[])))
          hders
      in
      let hders1 =
        forallT_inv (Sequent (y, (CPL.FSf a))) ((Sequent ((CPL.Comma (x,
          (CPL.FSf a))), (CPL.FSf b)))::((Sequent ((CPL.FSf b), z))::[]))
          hders0
      in
      let hders2 =
        forallT_inv_tail (Sequent (y, (CPL.FSf a))) ((Sequent ((CPL.Comma (x,
          (CPL.FSf a))), (CPL.FSf b)))::((Sequent ((CPL.FSf b), z))::[]))
          hders0
      in
      let hders3 =
        forallT_inv (Sequent ((CPL.Comma (x, (CPL.FSf a))), (CPL.FSf b)))
          ((Sequent ((CPL.FSf b), z))::[]) hders2
      in
      let hders4 =
        forallT_inv_tail (Sequent ((CPL.Comma (x, (CPL.FSf a))), (CPL.FSf
          b))) ((Sequent ((CPL.FSf b), z))::[]) hders2
      in
      let hders5 = forallT_inv (Sequent ((CPL.FSf b), z)) [] hders4 in
      deriv_cofseq_rule_bw_InstNC eqDec_formula f_PL pL_LANG eqDec_structr
        f_CPL cPL_LANG cPL_DC
        (premsRule eqDec_formula f_PL pL_LANG eqDec_structr f_CPL cPL_LANG
          CPLRules.coq_Mlln)
        (conclRule eqDec_formula f_PL pL_LANG eqDec_structr f_CPL cPL_LANG
          CPLRules.coq_Mlln)
        (seq_matchsub eqDec_formula f_PL pL_LANG eqDec_structr f_CPL cPL_LANG
          (conclRule eqDec_formula f_PL pL_LANG eqDec_structr f_CPL cPL_LANG
            CPLRules.coq_Mlln) (Sequent (x, (CPL.Comma ((CPL.Star y), z)))))
        CPLDeriv.dernc_Mlln (ForallT_cons
        ((seqSubst eqDec_formula f_PL pL_LANG eqDec_structr f_CPL cPL_LANG
           (seq_matchsub eqDec_formula f_PL pL_LANG eqDec_structr f_CPL
             cPL_LANG
             (conclRule eqDec_formula f_PL pL_LANG eqDec_structr f_CPL
               cPL_LANG CPLRules.coq_Mlln) (Sequent (x, (CPL.Comma ((CPL.Star
             y), z))))) (Sequent ((CPL.Comma ((CPL.SVf "X"), (CPL.SVf "Y"))),
           (CPL.SVf "Z")))), [],
        (deriv_cofseq_rule_bw_inDC eqDec_formula f_PL pL_LANG eqDec_structr
          f_CPL cPL_LANG cPL_DC
          (premsRule eqDec_formula f_PL pL_LANG eqDec_structr f_CPL cPL_LANG
            (cUT eqDec_formula f_PL pL_LANG eqDec_structr f_CPL cPL_LANG))
          (conclRule eqDec_formula f_PL pL_LANG eqDec_structr f_CPL cPL_LANG
            (cUT eqDec_formula f_PL pL_LANG eqDec_structr f_CPL cPL_LANG))
          (cUT_spec eqDec_formula f_PL pL_LANG eqDec_structr f_CPL cPL_LANG b
            (CPL.Comma (y, x)) z)
          (forallT_deriv_cofseqs eqDec_formula f_PL pL_LANG eqDec_structr
            f_CPL cPL_LANG cPL_DC ((Sequent ((CPL.Comma (y, x)), (CPL.FSf
            b)))::((Sequent ((CPL.FSf b), z))::[])) (ForallT_cons ((Sequent
            ((CPL.Comma (y, x)), (CPL.FSf b))), ((Sequent ((CPL.FSf b),
            z))::[]),
            (deriv_cofseq_rule_bw_InstNC eqDec_formula f_PL pL_LANG
              eqDec_structr f_CPL cPL_LANG cPL_DC
              (premsRule eqDec_formula f_PL pL_LANG eqDec_structr f_CPL
                cPL_LANG CPLRules.coq_Mrrs)
              (conclRule eqDec_formula f_PL pL_LANG eqDec_structr f_CPL
                cPL_LANG CPLRules.coq_Mrrs)
              (seq_matchsub eqDec_formula f_PL pL_LANG eqDec_structr f_CPL
                cPL_LANG
                (conclRule eqDec_formula f_PL pL_LANG eqDec_structr f_CPL
                  cPL_LANG CPLRules.coq_Mrrs) (Sequent ((CPL.Comma (y, x)),
                (CPL.FSf b)))) CPLDeriv.dernc_Mrrs (ForallT_cons
              ((seqSubst eqDec_formula f_PL pL_LANG eqDec_structr f_CPL
                 cPL_LANG
                 (seq_matchsub eqDec_formula f_PL pL_LANG eqDec_structr f_CPL
                   cPL_LANG
                   (conclRule eqDec_formula f_PL pL_LANG eqDec_structr f_CPL
                     cPL_LANG CPLRules.coq_Mrrs) (Sequent ((CPL.Comma (y,
                   x)), (CPL.FSf b)))) (Sequent ((CPL.SVf "X"), (CPL.Comma
                 ((CPL.SVf "Y"), (CPL.Star (CPL.SVf "Z"))))))), [],
              (deriv_cofseq_rule_bw_inDC eqDec_formula f_PL pL_LANG
                eqDec_structr f_CPL cPL_LANG cPL_DC
                (premsRule eqDec_formula f_PL pL_LANG eqDec_structr f_CPL
                  cPL_LANG
                  (cUT eqDec_formula f_PL pL_LANG eqDec_structr f_CPL
                    cPL_LANG))
                (conclRule eqDec_formula f_PL pL_LANG eqDec_structr f_CPL
                  cPL_LANG
                  (cUT eqDec_formula f_PL pL_LANG eqDec_structr f_CPL
                    cPL_LANG))
                (cUT_spec eqDec_formula f_PL pL_LANG eqDec_structr f_CPL
                  cPL_LANG a y (CPL.Comma ((CPL.FSf b), (CPL.Star x))))
                (forallT_deriv_cofseqs eqDec_formula f_PL pL_LANG
                  eqDec_structr f_CPL cPL_LANG cPL_DC ((Sequent (y, (CPL.FSf
                  a)))::((Sequent ((CPL.FSf a), (CPL.Comma ((CPL.FSf b),
                  (CPL.Star x)))))::[])) (ForallT_cons ((Sequent (y, (CPL.FSf
                  a))), ((Sequent ((CPL.FSf a), (CPL.Comma ((CPL.FSf b),
                  (CPL.Star x)))))::[]), hders1, (ForallT_cons ((Sequent
                  ((CPL.FSf a), (CPL.Comma ((CPL.FSf b), (CPL.Star x))))),
                  [],
                  (deriv_cofseq_rule_bw_inDC eqDec_formula f_PL pL_LANG
                    eqDec_structr f_CPL cPL_LANG cPL_DC
                    (premsRule eqDec_formula f_PL pL_LANG eqDec_structr f_CPL
                      cPL_LANG CPLRules.coq_Mlrn)
                    (conclRule eqDec_formula f_PL pL_LANG eqDec_structr f_CPL
                      cPL_LANG CPLRules.coq_Mlrn)
                    (seq_matchsub eqDec_formula f_PL pL_LANG eqDec_structr
                      f_CPL cPL_LANG
                      (conclRule eqDec_formula f_PL pL_LANG eqDec_structr
                        f_CPL cPL_LANG CPLRules.coq_Mlrn) (Sequent ((CPL.FSf
                      a), (CPL.Comma ((CPL.FSf b), (CPL.Star x))))))
                    (forallT_deriv_cofseqs eqDec_formula f_PL pL_LANG
                      eqDec_structr f_CPL cPL_LANG cPL_DC
                      (map
                        (seqSubst eqDec_formula f_PL pL_LANG eqDec_structr
                          f_CPL cPL_LANG
                          (seq_matchsub eqDec_formula f_PL pL_LANG
                            eqDec_structr f_CPL cPL_LANG
                            (conclRule eqDec_formula f_PL pL_LANG
                              eqDec_structr f_CPL cPL_LANG CPLRules.coq_Mlrn)
                            (Sequent ((CPL.FSf a), (CPL.Comma ((CPL.FSf b),
                            (CPL.Star x)))))))
                        (premsRule eqDec_formula f_PL pL_LANG eqDec_structr
                          f_CPL cPL_LANG CPLRules.coq_Mlrn)) (ForallT_cons
                      ((seqSubst eqDec_formula f_PL pL_LANG eqDec_structr
                         f_CPL cPL_LANG
                         (seq_matchsub eqDec_formula f_PL pL_LANG
                           eqDec_structr f_CPL cPL_LANG
                           (conclRule eqDec_formula f_PL pL_LANG
                             eqDec_structr f_CPL cPL_LANG CPLRules.coq_Mlrn)
                           (Sequent ((CPL.FSf a), (CPL.Comma ((CPL.FSf b),
                           (CPL.Star x)))))) (Sequent ((CPL.Comma ((CPL.SVf
                         "X"), (CPL.SVf "Y"))), (CPL.SVf "Z")))), [],
                      (deriv_cofseq_rule_bw_inDC eqDec_formula f_PL pL_LANG
                        eqDec_structr f_CPL cPL_LANG cPL_DC
                        (premsRule eqDec_formula f_PL pL_LANG eqDec_structr
                          f_CPL cPL_LANG CPLRules.coq_Comml)
                        (conclRule eqDec_formula f_PL pL_LANG eqDec_structr
                          f_CPL cPL_LANG CPLRules.coq_Comml)
                        (seq_matchsub eqDec_formula f_PL pL_LANG
                          eqDec_structr f_CPL cPL_LANG
                          (conclRule eqDec_formula f_PL pL_LANG eqDec_structr
                            f_CPL cPL_LANG CPLRules.coq_Comml) (Sequent
                          ((CPL.Comma ((CPL.FSf a), x)), (CPL.FSf b))))
                        (forallT_deriv_cofseqs eqDec_formula f_PL pL_LANG
                          eqDec_structr f_CPL cPL_LANG cPL_DC
                          (map
                            (seqSubst eqDec_formula f_PL pL_LANG
                              eqDec_structr f_CPL cPL_LANG
                              (seq_matchsub eqDec_formula f_PL pL_LANG
                                eqDec_structr f_CPL cPL_LANG
                                (conclRule eqDec_formula f_PL pL_LANG
                                  eqDec_structr f_CPL cPL_LANG
                                  CPLRules.coq_Comml) (Sequent ((CPL.Comma
                                ((CPL.FSf a), x)), (CPL.FSf b)))))
                            (premsRule eqDec_formula f_PL pL_LANG
                              eqDec_structr f_CPL cPL_LANG CPLRules.coq_Comml))
                          (ForallT_cons
                          ((seqSubst eqDec_formula f_PL pL_LANG eqDec_structr
                             f_CPL cPL_LANG
                             (seq_matchsub eqDec_formula f_PL pL_LANG
                               eqDec_structr f_CPL cPL_LANG
                               (conclRule eqDec_formula f_PL pL_LANG
                                 eqDec_structr f_CPL cPL_LANG
                                 CPLRules.coq_Comml) (Sequent ((CPL.Comma
                               ((CPL.FSf a), x)), (CPL.FSf b)))) (Sequent
                             ((CPL.Comma ((CPL.SVf "X"), (CPL.SVf "Y"))),
                             (CPL.SVf "Z")))), [], hders3, ForallT_nil)))),
                      ForallT_nil)))), ForallT_nil)))))), ForallT_nil))),
            (ForallT_cons ((Sequent ((CPL.FSf b), z)), [], hders5,
            ForallT_nil)))))), ForallT_nil))) ld

  (** val coq_C8_holds :
      PL.formula -> (PL.formula, CPL.structr) dertree -> (PL.formula,
      CPL.structr) dertree **)

  let coq_C8_holds m dt =
    reduce_C8 eqDec_formula f_PL pL_LANG eqDec_structr f_CPL cPL_LANG cPL_DC
      (fun a _ x y rL lL rR lR _ _ _ _ _ _ _ _ ->
      eq_dec_in_list
        (eqdec
          (eqDec_rule eqDec_formula f_PL pL_LANG eqDec_structr f_CPL cPL_LANG))
        (atrefl eqDec_formula f_PL pL_LANG eqDec_structr f_CPL cPL_LANG)
        (CPLRules.coq_Topr::(CPLRules.coq_Botr::(CPLRules.coq_Negr::(CPLRules.coq_Conr::(CPLRules.coq_Disr::(CPLRules.coq_Impr::[]))))))
        rL (fun _ ->
        eq_dec_in_list
          (eqdec
            (eqDec_rule eqDec_formula f_PL pL_LANG eqDec_structr f_CPL
              cPL_LANG))
          (atrefl eqDec_formula f_PL pL_LANG eqDec_structr f_CPL cPL_LANG)
          (CPLRules.coq_Topl::(CPLRules.coq_Botl::(CPLRules.coq_Negl::(CPLRules.coq_Conl::(CPLRules.coq_Disl::(CPLRules.coq_Impl::[]))))))
          rR (fun _ ->
          let hwfrR =
            ruleInst_ruleSubst eqDec_formula f_PL pL_LANG eqDec_structr f_CPL
              cPL_LANG rR
              ((map
                 (conclDT eqDec_formula f_PL pL_LANG eqDec_structr f_CPL
                   cPL_LANG) lR),(Sequent ((cPL_LANG.fS a), y)))
          in
          (match lL with
           | [] ->
             (match lR with
              | [] ->
                let p = fst (fst hwfrR) "p" in
                Der ((Sequent ((CPL.FSf (PL.Atf p)), (CPL.FSf (PL.Atf p)))),
                (atrefl eqDec_formula f_PL pL_LANG eqDec_structr f_CPL
                  cPL_LANG), [])
              | _::_ -> assert false (* absurd case *))
           | _::_ -> assert false (* absurd case *))) (fun _ ->
          eq_dec_in_list
            (eqdec
              (eqDec_rule eqDec_formula f_PL pL_LANG eqDec_structr f_CPL
                cPL_LANG)) CPLRules.coq_Topl
            (CPLRules.coq_Botl::(CPLRules.coq_Negl::(CPLRules.coq_Conl::(CPLRules.coq_Disl::(CPLRules.coq_Impl::[])))))
            rR (fun _ -> assert false (* absurd case *)) (fun _ ->
            eq_dec_in_list
              (eqdec
                (eqDec_rule eqDec_formula f_PL pL_LANG eqDec_structr f_CPL
                  cPL_LANG)) CPLRules.coq_Botl
              (CPLRules.coq_Negl::(CPLRules.coq_Conl::(CPLRules.coq_Disl::(CPLRules.coq_Impl::[]))))
              rR (fun _ -> assert false (* absurd case *)) (fun _ ->
              eq_dec_in_list
                (eqdec
                  (eqDec_rule eqDec_formula f_PL pL_LANG eqDec_structr f_CPL
                    cPL_LANG)) CPLRules.coq_Negl
                (CPLRules.coq_Conl::(CPLRules.coq_Disl::(CPLRules.coq_Impl::[])))
                rR (fun _ -> assert false (* absurd case *)) (fun _ ->
                eq_dec_in_list
                  (eqdec
                    (eqDec_rule eqDec_formula f_PL pL_LANG eqDec_structr
                      f_CPL cPL_LANG)) CPLRules.coq_Conl
                  (CPLRules.coq_Disl::(CPLRules.coq_Impl::[])) rR (fun _ ->
                  assert false (* absurd case *)) (fun _ ->
                  eq_dec_in_list
                    (eqdec
                      (eqDec_rule eqDec_formula f_PL pL_LANG eqDec_structr
                        f_CPL cPL_LANG)) CPLRules.coq_Disl
                    (CPLRules.coq_Impl::[]) rR (fun _ -> assert false
                    (* absurd case *)) (fun _ ->
                    eq_dec_in_list
                      (eqdec
                        (eqDec_rule eqDec_formula f_PL pL_LANG eqDec_structr
                          f_CPL cPL_LANG)) CPLRules.coq_Impl [] rR (fun _ ->
                      assert false (* absurd case *)) (fun _ -> assert false
                      (* absurd case *))))))))) (fun _ ->
        eq_dec_in_list
          (eqdec
            (eqDec_rule eqDec_formula f_PL pL_LANG eqDec_structr f_CPL
              cPL_LANG)) CPLRules.coq_Topr
          (CPLRules.coq_Botr::(CPLRules.coq_Negr::(CPLRules.coq_Conr::(CPLRules.coq_Disr::(CPLRules.coq_Impr::[])))))
          rL (fun _ ->
          eq_dec_in_list
            (eqdec
              (eqDec_rule eqDec_formula f_PL pL_LANG eqDec_structr f_CPL
                cPL_LANG))
            (atrefl eqDec_formula f_PL pL_LANG eqDec_structr f_CPL cPL_LANG)
            (CPLRules.coq_Topl::(CPLRules.coq_Botl::(CPLRules.coq_Negl::(CPLRules.coq_Conl::(CPLRules.coq_Disl::(CPLRules.coq_Impl::[]))))))
            rR (fun _ -> assert false (* absurd case *)) (fun _ ->
            eq_dec_in_list
              (eqdec
                (eqDec_rule eqDec_formula f_PL pL_LANG eqDec_structr f_CPL
                  cPL_LANG)) CPLRules.coq_Topl
              (CPLRules.coq_Botl::(CPLRules.coq_Negl::(CPLRules.coq_Conl::(CPLRules.coq_Disl::(CPLRules.coq_Impl::[])))))
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
                  (eqDec_rule eqDec_formula f_PL pL_LANG eqDec_structr f_CPL
                    cPL_LANG)) CPLRules.coq_Botl
                (CPLRules.coq_Negl::(CPLRules.coq_Conl::(CPLRules.coq_Disl::(CPLRules.coq_Impl::[]))))
                rR (fun _ -> assert false (* absurd case *)) (fun _ ->
                eq_dec_in_list
                  (eqdec
                    (eqDec_rule eqDec_formula f_PL pL_LANG eqDec_structr
                      f_CPL cPL_LANG)) CPLRules.coq_Negl
                  (CPLRules.coq_Conl::(CPLRules.coq_Disl::(CPLRules.coq_Impl::[])))
                  rR (fun _ -> assert false (* absurd case *)) (fun _ ->
                  eq_dec_in_list
                    (eqdec
                      (eqDec_rule eqDec_formula f_PL pL_LANG eqDec_structr
                        f_CPL cPL_LANG)) CPLRules.coq_Conl
                    (CPLRules.coq_Disl::(CPLRules.coq_Impl::[])) rR (fun _ ->
                    assert false (* absurd case *)) (fun _ ->
                    eq_dec_in_list
                      (eqdec
                        (eqDec_rule eqDec_formula f_PL pL_LANG eqDec_structr
                          f_CPL cPL_LANG)) CPLRules.coq_Disl
                      (CPLRules.coq_Impl::[]) rR (fun _ -> assert false
                      (* absurd case *)) (fun _ ->
                      eq_dec_in_list
                        (eqdec
                          (eqDec_rule eqDec_formula f_PL pL_LANG
                            eqDec_structr f_CPL cPL_LANG)) CPLRules.coq_Impl
                        [] rR (fun _ -> assert false (* absurd case *))
                        (fun _ -> assert false (* absurd case *)))))))))
          (fun _ ->
          eq_dec_in_list
            (eqdec
              (eqDec_rule eqDec_formula f_PL pL_LANG eqDec_structr f_CPL
                cPL_LANG)) CPLRules.coq_Botr
            (CPLRules.coq_Negr::(CPLRules.coq_Conr::(CPLRules.coq_Disr::(CPLRules.coq_Impr::[]))))
            rL (fun _ ->
            eq_dec_in_list
              (eqdec
                (eqDec_rule eqDec_formula f_PL pL_LANG eqDec_structr f_CPL
                  cPL_LANG))
              (atrefl eqDec_formula f_PL pL_LANG eqDec_structr f_CPL cPL_LANG)
              (CPLRules.coq_Topl::(CPLRules.coq_Botl::(CPLRules.coq_Negl::(CPLRules.coq_Conl::(CPLRules.coq_Disl::(CPLRules.coq_Impl::[]))))))
              rR (fun _ -> assert false (* absurd case *)) (fun _ ->
              eq_dec_in_list
                (eqdec
                  (eqDec_rule eqDec_formula f_PL pL_LANG eqDec_structr f_CPL
                    cPL_LANG)) CPLRules.coq_Topl
                (CPLRules.coq_Botl::(CPLRules.coq_Negl::(CPLRules.coq_Conl::(CPLRules.coq_Disl::(CPLRules.coq_Impl::[])))))
                rR (fun _ -> assert false (* absurd case *)) (fun _ ->
                eq_dec_in_list
                  (eqdec
                    (eqDec_rule eqDec_formula f_PL pL_LANG eqDec_structr
                      f_CPL cPL_LANG)) CPLRules.coq_Botl
                  (CPLRules.coq_Negl::(CPLRules.coq_Conl::(CPLRules.coq_Disl::(CPLRules.coq_Impl::[]))))
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
                      (eqDec_rule eqDec_formula f_PL pL_LANG eqDec_structr
                        f_CPL cPL_LANG)) CPLRules.coq_Negl
                    (CPLRules.coq_Conl::(CPLRules.coq_Disl::(CPLRules.coq_Impl::[])))
                    rR (fun _ -> assert false (* absurd case *)) (fun _ ->
                    eq_dec_in_list
                      (eqdec
                        (eqDec_rule eqDec_formula f_PL pL_LANG eqDec_structr
                          f_CPL cPL_LANG)) CPLRules.coq_Conl
                      (CPLRules.coq_Disl::(CPLRules.coq_Impl::[])) rR
                      (fun _ -> assert false (* absurd case *)) (fun _ ->
                      eq_dec_in_list
                        (eqdec
                          (eqDec_rule eqDec_formula f_PL pL_LANG
                            eqDec_structr f_CPL cPL_LANG)) CPLRules.coq_Disl
                        (CPLRules.coq_Impl::[]) rR (fun _ -> assert false
                        (* absurd case *)) (fun _ ->
                        eq_dec_in_list
                          (eqdec
                            (eqDec_rule eqDec_formula f_PL pL_LANG
                              eqDec_structr f_CPL cPL_LANG))
                          CPLRules.coq_Impl [] rR (fun _ -> assert false
                          (* absurd case *)) (fun _ -> assert false
                          (* absurd case *))))))))) (fun _ ->
            eq_dec_in_list
              (eqdec
                (eqDec_rule eqDec_formula f_PL pL_LANG eqDec_structr f_CPL
                  cPL_LANG)) CPLRules.coq_Negr
              (CPLRules.coq_Conr::(CPLRules.coq_Disr::(CPLRules.coq_Impr::[])))
              rL (fun _ ->
              eq_dec_in_list
                (eqdec
                  (eqDec_rule eqDec_formula f_PL pL_LANG eqDec_structr f_CPL
                    cPL_LANG))
                (atrefl eqDec_formula f_PL pL_LANG eqDec_structr f_CPL
                  cPL_LANG)
                (CPLRules.coq_Topl::(CPLRules.coq_Botl::(CPLRules.coq_Negl::(CPLRules.coq_Conl::(CPLRules.coq_Disl::(CPLRules.coq_Impl::[]))))))
                rR (fun _ -> assert false (* absurd case *)) (fun _ ->
                eq_dec_in_list
                  (eqdec
                    (eqDec_rule eqDec_formula f_PL pL_LANG eqDec_structr
                      f_CPL cPL_LANG)) CPLRules.coq_Topl
                  (CPLRules.coq_Botl::(CPLRules.coq_Negl::(CPLRules.coq_Conl::(CPLRules.coq_Disl::(CPLRules.coq_Impl::[])))))
                  rR (fun _ -> assert false (* absurd case *)) (fun _ ->
                  eq_dec_in_list
                    (eqdec
                      (eqDec_rule eqDec_formula f_PL pL_LANG eqDec_structr
                        f_CPL cPL_LANG)) CPLRules.coq_Botl
                    (CPLRules.coq_Negl::(CPLRules.coq_Conl::(CPLRules.coq_Disl::(CPLRules.coq_Impl::[]))))
                    rR (fun _ -> assert false (* absurd case *)) (fun _ ->
                    eq_dec_in_list
                      (eqdec
                        (eqDec_rule eqDec_formula f_PL pL_LANG eqDec_structr
                          f_CPL cPL_LANG)) CPLRules.coq_Negl
                      (CPLRules.coq_Conl::(CPLRules.coq_Disl::(CPLRules.coq_Impl::[])))
                      rR (fun _ ->
                      let hwfrL =
                        ruleInst_ruleSubst eqDec_formula f_PL pL_LANG
                          eqDec_structr f_CPL cPL_LANG rL
                          ((map
                             (conclDT eqDec_formula f_PL pL_LANG
                               eqDec_structr f_CPL cPL_LANG) lL),(Sequent (x,
                          (cPL_LANG.fS a))))
                      in
                      let hwfrR =
                        ruleInst_ruleSubst eqDec_formula f_PL pL_LANG
                          eqDec_structr f_CPL cPL_LANG rR
                          ((map
                             (conclDT eqDec_formula f_PL pL_LANG
                               eqDec_structr f_CPL cPL_LANG) lR),(Sequent
                          ((cPL_LANG.fS a), y)))
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
                          (eqDec_rule eqDec_formula f_PL pL_LANG
                            eqDec_structr f_CPL cPL_LANG)) CPLRules.coq_Conl
                        (CPLRules.coq_Disl::(CPLRules.coq_Impl::[])) rR
                        (fun _ -> assert false (* absurd case *)) (fun _ ->
                        eq_dec_in_list
                          (eqdec
                            (eqDec_rule eqDec_formula f_PL pL_LANG
                              eqDec_structr f_CPL cPL_LANG))
                          CPLRules.coq_Disl (CPLRules.coq_Impl::[]) rR
                          (fun _ -> assert false (* absurd case *)) (fun _ ->
                          eq_dec_in_list
                            (eqdec
                              (eqDec_rule eqDec_formula f_PL pL_LANG
                                eqDec_structr f_CPL cPL_LANG))
                            CPLRules.coq_Impl [] rR (fun _ -> assert false
                            (* absurd case *)) (fun _ -> assert false
                            (* absurd case *))))))))) (fun _ ->
              eq_dec_in_list
                (eqdec
                  (eqDec_rule eqDec_formula f_PL pL_LANG eqDec_structr f_CPL
                    cPL_LANG)) CPLRules.coq_Conr
                (CPLRules.coq_Disr::(CPLRules.coq_Impr::[])) rL (fun _ ->
                eq_dec_in_list
                  (eqdec
                    (eqDec_rule eqDec_formula f_PL pL_LANG eqDec_structr
                      f_CPL cPL_LANG))
                  (atrefl eqDec_formula f_PL pL_LANG eqDec_structr f_CPL
                    cPL_LANG)
                  (CPLRules.coq_Topl::(CPLRules.coq_Botl::(CPLRules.coq_Negl::(CPLRules.coq_Conl::(CPLRules.coq_Disl::(CPLRules.coq_Impl::[]))))))
                  rR (fun _ -> assert false (* absurd case *)) (fun _ ->
                  eq_dec_in_list
                    (eqdec
                      (eqDec_rule eqDec_formula f_PL pL_LANG eqDec_structr
                        f_CPL cPL_LANG)) CPLRules.coq_Topl
                    (CPLRules.coq_Botl::(CPLRules.coq_Negl::(CPLRules.coq_Conl::(CPLRules.coq_Disl::(CPLRules.coq_Impl::[])))))
                    rR (fun _ -> assert false (* absurd case *)) (fun _ ->
                    eq_dec_in_list
                      (eqdec
                        (eqDec_rule eqDec_formula f_PL pL_LANG eqDec_structr
                          f_CPL cPL_LANG)) CPLRules.coq_Botl
                      (CPLRules.coq_Negl::(CPLRules.coq_Conl::(CPLRules.coq_Disl::(CPLRules.coq_Impl::[]))))
                      rR (fun _ -> assert false (* absurd case *)) (fun _ ->
                      eq_dec_in_list
                        (eqdec
                          (eqDec_rule eqDec_formula f_PL pL_LANG
                            eqDec_structr f_CPL cPL_LANG)) CPLRules.coq_Negl
                        (CPLRules.coq_Conl::(CPLRules.coq_Disl::(CPLRules.coq_Impl::[])))
                        rR (fun _ -> assert false (* absurd case *))
                        (fun _ ->
                        eq_dec_in_list
                          (eqdec
                            (eqDec_rule eqDec_formula f_PL pL_LANG
                              eqDec_structr f_CPL cPL_LANG))
                          CPLRules.coq_Conl
                          (CPLRules.coq_Disl::(CPLRules.coq_Impl::[])) rR
                          (fun _ ->
                          let hwfrL =
                            ruleInst_ruleSubst eqDec_formula f_PL pL_LANG
                              eqDec_structr f_CPL cPL_LANG rL
                              ((map
                                 (conclDT eqDec_formula f_PL pL_LANG
                                   eqDec_structr f_CPL cPL_LANG) lL),(Sequent
                              (x, (cPL_LANG.fS a))))
                          in
                          let hwfrR =
                            ruleInst_ruleSubst eqDec_formula f_PL pL_LANG
                              eqDec_structr f_CPL cPL_LANG rR
                              ((map
                                 (conclDT eqDec_formula f_PL pL_LANG
                                   eqDec_structr f_CPL cPL_LANG) lR),(Sequent
                              ((cPL_LANG.fS a), y)))
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
                              (eqDec_rule eqDec_formula f_PL pL_LANG
                                eqDec_structr f_CPL cPL_LANG))
                            CPLRules.coq_Disl (CPLRules.coq_Impl::[]) rR
                            (fun _ -> assert false (* absurd case *))
                            (fun _ ->
                            eq_dec_in_list
                              (eqdec
                                (eqDec_rule eqDec_formula f_PL pL_LANG
                                  eqDec_structr f_CPL cPL_LANG))
                              CPLRules.coq_Impl [] rR (fun _ -> assert false
                              (* absurd case *)) (fun _ -> assert false
                              (* absurd case *))))))))) (fun _ ->
                eq_dec_in_list
                  (eqdec
                    (eqDec_rule eqDec_formula f_PL pL_LANG eqDec_structr
                      f_CPL cPL_LANG)) CPLRules.coq_Disr
                  (CPLRules.coq_Impr::[]) rL (fun _ ->
                  eq_dec_in_list
                    (eqdec
                      (eqDec_rule eqDec_formula f_PL pL_LANG eqDec_structr
                        f_CPL cPL_LANG))
                    (atrefl eqDec_formula f_PL pL_LANG eqDec_structr f_CPL
                      cPL_LANG)
                    (CPLRules.coq_Topl::(CPLRules.coq_Botl::(CPLRules.coq_Negl::(CPLRules.coq_Conl::(CPLRules.coq_Disl::(CPLRules.coq_Impl::[]))))))
                    rR (fun _ -> assert false (* absurd case *)) (fun _ ->
                    eq_dec_in_list
                      (eqdec
                        (eqDec_rule eqDec_formula f_PL pL_LANG eqDec_structr
                          f_CPL cPL_LANG)) CPLRules.coq_Topl
                      (CPLRules.coq_Botl::(CPLRules.coq_Negl::(CPLRules.coq_Conl::(CPLRules.coq_Disl::(CPLRules.coq_Impl::[])))))
                      rR (fun _ -> assert false (* absurd case *)) (fun _ ->
                      eq_dec_in_list
                        (eqdec
                          (eqDec_rule eqDec_formula f_PL pL_LANG
                            eqDec_structr f_CPL cPL_LANG)) CPLRules.coq_Botl
                        (CPLRules.coq_Negl::(CPLRules.coq_Conl::(CPLRules.coq_Disl::(CPLRules.coq_Impl::[]))))
                        rR (fun _ -> assert false (* absurd case *))
                        (fun _ ->
                        eq_dec_in_list
                          (eqdec
                            (eqDec_rule eqDec_formula f_PL pL_LANG
                              eqDec_structr f_CPL cPL_LANG))
                          CPLRules.coq_Negl
                          (CPLRules.coq_Conl::(CPLRules.coq_Disl::(CPLRules.coq_Impl::[])))
                          rR (fun _ -> assert false (* absurd case *))
                          (fun _ ->
                          eq_dec_in_list
                            (eqdec
                              (eqDec_rule eqDec_formula f_PL pL_LANG
                                eqDec_structr f_CPL cPL_LANG))
                            CPLRules.coq_Conl
                            (CPLRules.coq_Disl::(CPLRules.coq_Impl::[])) rR
                            (fun _ -> assert false (* absurd case *))
                            (fun _ ->
                            eq_dec_in_list
                              (eqdec
                                (eqDec_rule eqDec_formula f_PL pL_LANG
                                  eqDec_structr f_CPL cPL_LANG))
                              CPLRules.coq_Disl (CPLRules.coq_Impl::[]) rR
                              (fun _ ->
                              let hwfrL =
                                ruleInst_ruleSubst eqDec_formula f_PL pL_LANG
                                  eqDec_structr f_CPL cPL_LANG rL
                                  ((map
                                     (conclDT eqDec_formula f_PL pL_LANG
                                       eqDec_structr f_CPL cPL_LANG) lL),(Sequent
                                  (x, (cPL_LANG.fS a))))
                              in
                              let hwfrR =
                                ruleInst_ruleSubst eqDec_formula f_PL pL_LANG
                                  eqDec_structr f_CPL cPL_LANG rR
                                  ((map
                                     (conclDT eqDec_formula f_PL pL_LANG
                                       eqDec_structr f_CPL cPL_LANG) lR),(Sequent
                                  ((cPL_LANG.fS a), y)))
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
                                  (eqDec_rule eqDec_formula f_PL pL_LANG
                                    eqDec_structr f_CPL cPL_LANG))
                                CPLRules.coq_Impl [] rR (fun _ ->
                                assert false (* absurd case *)) (fun _ ->
                                assert false (* absurd case *)))))))))
                  (fun _ ->
                  eq_dec_in_list
                    (eqdec
                      (eqDec_rule eqDec_formula f_PL pL_LANG eqDec_structr
                        f_CPL cPL_LANG)) CPLRules.coq_Impr [] rL (fun _ ->
                    eq_dec_in_list
                      (eqdec
                        (eqDec_rule eqDec_formula f_PL pL_LANG eqDec_structr
                          f_CPL cPL_LANG))
                      (atrefl eqDec_formula f_PL pL_LANG eqDec_structr f_CPL
                        cPL_LANG)
                      (CPLRules.coq_Topl::(CPLRules.coq_Botl::(CPLRules.coq_Negl::(CPLRules.coq_Conl::(CPLRules.coq_Disl::(CPLRules.coq_Impl::[]))))))
                      rR (fun _ -> assert false (* absurd case *)) (fun _ ->
                      eq_dec_in_list
                        (eqdec
                          (eqDec_rule eqDec_formula f_PL pL_LANG
                            eqDec_structr f_CPL cPL_LANG)) CPLRules.coq_Topl
                        (CPLRules.coq_Botl::(CPLRules.coq_Negl::(CPLRules.coq_Conl::(CPLRules.coq_Disl::(CPLRules.coq_Impl::[])))))
                        rR (fun _ -> assert false (* absurd case *))
                        (fun _ ->
                        eq_dec_in_list
                          (eqdec
                            (eqDec_rule eqDec_formula f_PL pL_LANG
                              eqDec_structr f_CPL cPL_LANG))
                          CPLRules.coq_Botl
                          (CPLRules.coq_Negl::(CPLRules.coq_Conl::(CPLRules.coq_Disl::(CPLRules.coq_Impl::[]))))
                          rR (fun _ -> assert false (* absurd case *))
                          (fun _ ->
                          eq_dec_in_list
                            (eqdec
                              (eqDec_rule eqDec_formula f_PL pL_LANG
                                eqDec_structr f_CPL cPL_LANG))
                            CPLRules.coq_Negl
                            (CPLRules.coq_Conl::(CPLRules.coq_Disl::(CPLRules.coq_Impl::[])))
                            rR (fun _ -> assert false (* absurd case *))
                            (fun _ ->
                            eq_dec_in_list
                              (eqdec
                                (eqDec_rule eqDec_formula f_PL pL_LANG
                                  eqDec_structr f_CPL cPL_LANG))
                              CPLRules.coq_Conl
                              (CPLRules.coq_Disl::(CPLRules.coq_Impl::[])) rR
                              (fun _ -> assert false (* absurd case *))
                              (fun _ ->
                              eq_dec_in_list
                                (eqdec
                                  (eqDec_rule eqDec_formula f_PL pL_LANG
                                    eqDec_structr f_CPL cPL_LANG))
                                CPLRules.coq_Disl (CPLRules.coq_Impl::[]) rR
                                (fun _ -> assert false (* absurd case *))
                                (fun _ ->
                                eq_dec_in_list
                                  (eqdec
                                    (eqDec_rule eqDec_formula f_PL pL_LANG
                                      eqDec_structr f_CPL cPL_LANG))
                                  CPLRules.coq_Impl [] rR (fun _ ->
                                  let hwfrL =
                                    ruleInst_ruleSubst eqDec_formula f_PL
                                      pL_LANG eqDec_structr f_CPL cPL_LANG rL
                                      ((map
                                         (conclDT eqDec_formula f_PL pL_LANG
                                           eqDec_structr f_CPL cPL_LANG) lL),(Sequent
                                      (x, (cPL_LANG.fS a))))
                                  in
                                  let hwfrR =
                                    ruleInst_ruleSubst eqDec_formula f_PL
                                      pL_LANG eqDec_structr f_CPL cPL_LANG rR
                                      ((map
                                         (conclDT eqDec_formula f_PL pL_LANG
                                           eqDec_structr f_CPL cPL_LANG) lR),(Sequent
                                      ((cPL_LANG.fS a), y)))
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
                                  (fun _ -> assert false (* absurd case *)))))))))
                    (fun _ -> assert false (* absurd case *))))))))) m dt
 end

(** val cPL_DC_Bel : (PL.formula, CPL.structr) bELNAP **)

let cPL_DC_Bel x x0 _ _ _ =
  CPLBelnap.coq_C8_holds x x0

(** val cPL_cutElim :
    (PL.formula, CPL.structr) dertree -> (PL.formula, CPL.structr) dertree **)

let cPL_cutElim dt =
  cutElim eqDec_formula f_PL pL_LANG eqDec_structr f_CPL cPL_LANG cPL_DC
    cPL_DC_Bel dt

(** val impcon_impr : (PL.formula, CPL.structr) rule **)

let impcon_impr =
  [],(Sequent ((CPL.FSf (PL.Imp ((PL.Atf "p"), (PL.Con ((PL.Atf "q"), (PL.Atf
    "r")))))), (CPL.FSf (PL.Imp ((PL.Atf "p"), (PL.Atf "r"))))))

(** val derr_impcon_impr : (PL.formula, CPL.structr) derivRule **)

let derr_impcon_impr =
  let p = PL.Atf "p" in
  let q = PL.Atf "q" in
  let r = PL.Atf "r" in
  extend_DerivRule_expl eqDec_formula f_PL pL_LANG eqDec_structr f_CPL
    cPL_LANG cPL_DC
    (frefl eqDec_formula f_PL pL_LANG eqDec_structr f_CPL cPL_LANG (PL.Con
      (q, r))) (CPLDeriv.coq_CPL_DC_derr_frefl (PL.Con (q, r))) impcon_impr
    (extend_DerivRule_expl eqDec_formula f_PL pL_LANG eqDec_structr f_CPL
      cPL_LANG
      (app cPL_DC
        ((frefl eqDec_formula f_PL pL_LANG eqDec_structr f_CPL cPL_LANG
           (PL.Con (q, r)))::[])) CPLRules.coq_Wkl
      (subDC_DerivRule eqDec_formula f_PL pL_LANG eqDec_structr f_CPL
        cPL_LANG cPL_DC
        (app cPL_DC
          ((frefl eqDec_formula f_PL pL_LANG eqDec_structr f_CPL cPL_LANG
             (PL.Con (q, r)))::[])) CPLRules.coq_Wkl
        (alr_DerivRule eqDec_formula f_PL pL_LANG eqDec_structr f_CPL
          cPL_LANG cPL_DC CPLRules.coq_Wkl
          (derrnc_derr eqDec_formula f_PL pL_LANG eqDec_structr f_CPL
            cPL_LANG cPL_DC CPLRules.coq_Wkl CPLDeriv.dernc_Wkl)))
      impcon_impr (Der ((Sequent ((CPL.FSf (PL.Imp (p, (PL.Con (q, r))))),
      (CPL.FSf (PL.Imp (p, r))))), CPLRules.coq_Impr, ((Der ((Sequent
      ((CPL.Comma ((CPL.FSf (PL.Imp (p, (PL.Con (q, r))))), (CPL.FSf p))),
      (CPL.FSf r))), CPLRules.coq_Comml, ((Der ((Sequent ((CPL.Comma
      ((CPL.FSf p), (CPL.FSf (PL.Imp (p, (PL.Con (q, r))))))), (CPL.FSf r))),
      (cUT eqDec_formula f_PL pL_LANG eqDec_structr f_CPL cPL_LANG), ((Der
      ((Sequent ((CPL.Comma ((CPL.FSf p), (CPL.FSf (PL.Imp (p, (PL.Con (q,
      r))))))), (CPL.FSf (PL.Con (q, r))))), CPLRules.coq_Mrls, ((Der
      ((Sequent ((CPL.FSf (PL.Imp (p, (PL.Con (q, r))))), (CPL.Comma
      ((CPL.Star (CPL.FSf p)), (CPL.FSf (PL.Con (q, r))))))),
      CPLRules.coq_Impl, ((Der ((Sequent ((CPL.FSf p), (CPL.FSf p))),
      (atrefl eqDec_formula f_PL pL_LANG eqDec_structr f_CPL cPL_LANG),
      []))::((Der ((Sequent ((CPL.FSf (PL.Con (q, r))), (CPL.FSf (PL.Con (q,
      r))))),
      (frefl eqDec_formula f_PL pL_LANG eqDec_structr f_CPL cPL_LANG (PL.Con
        (q, r))), []))::[]))))::[])))::((Der ((Sequent ((CPL.FSf (PL.Con (q,
      r))), (CPL.FSf r))), CPLRules.coq_Conl, ((Der ((Sequent ((CPL.Comma
      ((CPL.FSf q), (CPL.FSf r))), (CPL.FSf r))), CPLRules.coq_Wkl, ((Der
      ((Sequent ((CPL.FSf r), (CPL.FSf r))),
      (atrefl eqDec_formula f_PL pL_LANG eqDec_structr f_CPL cPL_LANG),
      []))::[])))::[])))::[]))))::[])))::[]))))
