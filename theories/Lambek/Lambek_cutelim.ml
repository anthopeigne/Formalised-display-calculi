
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

type ('a, 'r, 'x) subrelation = 'a -> 'a -> 'r -> 'x

(** val iffT_arrow_subrelation : (__, __) iffT -> (__, __) arrow **)

let iffT_arrow_subrelation x x0 =
  let a,_ = x in a x0

(** val iffT_flip_arrow_subrelation : (__, __) iffT -> (__, __) arrow **)

let iffT_flip_arrow_subrelation x x0 =
  let _,b = x in b x0

(** val flip2 : ('a1, 'a2, 'a3) subrelation -> ('a1, 'a2, 'a3) subrelation **)

let flip2 h =
  h

(** val in_dec : ('a1 -> 'a1 -> bool) -> 'a1 -> 'a1 list -> bool **)

let rec in_dec h a = function
| [] -> false
| y::l0 -> let s = h y a in if s then true else in_dec h a l0

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
  let a,b = x in let a0,b0 = y in if eqdec aED a a0 then eqdec bED b b0 else false

(** val eqDec_string : string eqDec **)

let eqDec_string =
  (=)

(** val comp : ('a2 -> 'a3) -> ('a1 -> 'a2) -> 'a1 -> 'a3 **)

let comp g f x =
  g (f x)

(** val list_biind :
    'a3 -> ('a1 -> 'a1 list -> 'a2 -> 'a2 list -> 'a3 -> 'a3) -> 'a1 list -> 'a2 list
    -> 'a3 **)

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
     | None -> let s = in_dec (eqdec eDB) b (f y) in if s then Some y else None)

(** val eq_dec_in_list :
    ('a1 -> 'a1 -> bool) -> 'a1 -> 'a1 list -> 'a1 -> (__ -> 'a2) -> (__ -> 'a2) -> 'a2 **)

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
   | a0::l1 -> (match l1 with
                | [] -> Some (ExistT (a, (ExistT (a0, __))))
                | _::_ -> None))

(** val in_map_inv_sig : 'a1 eqDec -> ('a2 -> 'a1) -> 'a2 list -> 'a1 -> 'a2 **)

let rec in_map_inv_sig aED f l y =
  match l with
  | [] -> assert false (* absurd case *)
  | y0::l0 ->
    let s = eqdec aED (f y0) y in
    if s
    then y0
    else let s0 = in_dec (eqdec aED) y (map f l0) in
         if s0 then in_map_inv_sig aED f l0 y else assert false (* absurd case *)

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
    'a1 list -> ('a1, 'a2) forallT -> ('a1, 'a2 -> 'a3) forallT -> ('a1, 'a3) forallT **)

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
    'a1 list -> ('a1 -> 'a2 -> 'a3) -> ('a1, 'a2) forallT -> ('a1, 'a3) forallT **)

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

(** val forallT_sig_elim : 'a1 list -> ('a1, 'a2) forallT -> 'a2 list **)

let rec forallT_sig_elim l h =
  match l with
  | [] -> []
  | _::l0 ->
    (match h with
     | ForallT_nil -> assert false (* absurd case *)
     | ForallT_cons (_, _, x, x0) -> let s = forallT_sig_elim l0 x0 in x::s)

(** val forall_ForallT : 'a1 eqDec -> 'a1 list -> (__, ('a1, __) forallT) iffT0 **)

let forall_ForallT aED l =
  (fun _ ->
    let _,x = forallT_forall aED l in let x0 = Obj.magic x in Obj.magic x0 __),
    (Obj.magic __)

type ('a, 'p) existsT =
| ExistsT_cons_hd of 'a * 'a list * 'p
| Exists_cons_tl of 'a * 'a list * ('a, 'p) existsT

(** val in_zip_pair_23_sig_1 :
    'a2 eqDec -> 'a3 eqDec -> 'a1 list -> 'a2 list -> 'a3 list -> 'a2 -> 'a3 -> 'a1 **)

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
                 in_dec (eqdec (eqDec_prod bED cED)) (b,c) (zip (fun x x0 -> x,x0) l l1)
               in
               if s0
               then in_zip_pair_23_sig_1 bED cED l0 l l1 b c
               else assert false (* absurd case *)))

(** val forallT_dec_E_sumbool :
    'a1 list -> ('a1, bool) forallT -> (('a1, __) existsT, ('a1, __) forallT) sum **)

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
                     ipse_rect : (__ -> ('expr -> ('expr -> __ -> __) -> __) -> 'expr
                                 -> __); conn : ('expr -> 'expr list -> 'expr) }

(** val ipse_rect :
    'a1 eqDec -> 'a1 fLANG -> ('a1 -> ('a1 -> __ -> 'a2) -> 'a2) -> 'a1 -> 'a2 **)

let ipse_rect _ fLANG0 x a =
  Obj.magic fLANG0.ipse_rect __ x a

type ('expr, 'ix) iXEXP =
  'expr -> 'ix option
  (* singleton inductive, whose constructor was Build_IXEXP *)

(** val var_dec :
    'a1 eqDec -> 'a1 fLANG -> ('a2 -> 'a1) -> ('a1, 'a2) iXEXP -> 'a1 -> 'a2 option **)

let var_dec _ _ _ iXEXP0 =
  iXEXP0

type 'formula lOGLANG = { atm : (string -> 'formula); fV : (string -> 'formula);
                          aTMVAR : ('formula, string) iXEXP;
                          fVVAR : ('formula, string) iXEXP }

type aSubst = string -> string

type 'formula fSubst = string -> 'formula

type 'formula afSubst = aSubst*'formula fSubst

(** val allVars :
    'a1 eqDec -> 'a1 fLANG -> ('a2 -> 'a1) -> ('a1, 'a2) iXEXP -> 'a1 -> 'a2 list **)

let allVars eD l var sVAR =
  ipse_rect eD l (fun a iH ->
    match var_dec eD l var sVAR a with
    | Some s -> s::[]
    | None ->
      list_union (l.ipse a) (fun b ->
        if in_dec (eqdec eD) b (l.ipse a) then iH b __ else []))

(** val fmlAtms : 'a1 eqDec -> 'a1 fLANG -> 'a1 lOGLANG -> 'a1 -> string list **)

let fmlAtms eDf lf lL =
  allVars eDf lf lL.atm lL.aTMVAR

(** val fmlFVs : 'a1 eqDec -> 'a1 fLANG -> 'a1 lOGLANG -> 'a1 -> string list **)

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
    'a1 eqDec -> 'a1 fLANG -> 'a1 lOGLANG -> 'a2 eqDec -> 'a2 fLANG -> ('a1, 'a2)
    sTRLANG -> ('a1, 'a2) sequent -> 'a2 **)

let antec _ _ _ _ _ _ = function
| Sequent (x, _) -> x

(** val succ :
    'a1 eqDec -> 'a1 fLANG -> 'a1 lOGLANG -> 'a2 eqDec -> 'a2 fLANG -> ('a1, 'a2)
    sTRLANG -> ('a1, 'a2) sequent -> 'a2 **)

let succ _ _ _ _ _ _ = function
| Sequent (_, y) -> y

(** val conclRule :
    'a1 eqDec -> 'a1 fLANG -> 'a1 lOGLANG -> 'a2 eqDec -> 'a2 fLANG -> ('a1, 'a2)
    sTRLANG -> ('a1, 'a2) rule -> ('a1, 'a2) sequent **)

let conclRule _ _ _ _ _ _ =
  snd

(** val premsRule :
    'a1 eqDec -> 'a1 fLANG -> 'a1 lOGLANG -> 'a2 eqDec -> 'a2 fLANG -> ('a1, 'a2)
    sTRLANG -> ('a1, 'a2) rule -> ('a1, 'a2) sequent list **)

let premsRule _ _ _ _ _ _ =
  fst

(** val sequent_eq_dec :
    'a1 eqDec -> 'a1 fLANG -> 'a1 lOGLANG -> 'a2 eqDec -> 'a2 fLANG -> ('a1, 'a2)
    sTRLANG -> ('a1, 'a2) sequent -> ('a1, 'a2) sequent -> bool **)

let sequent_eq_dec _ _ _ eDs _ _ s1 s2 =
  let Sequent (x, y) = s1 in
  let Sequent (x0, y0) = s2 in if eqdec eDs x x0 then eqdec eDs y y0 else false

(** val eqDec_sequent :
    'a1 eqDec -> 'a1 fLANG -> 'a1 lOGLANG -> 'a2 eqDec -> 'a2 fLANG -> ('a1, 'a2)
    sTRLANG -> ('a1, 'a2) sequent eqDec **)

let eqDec_sequent =
  sequent_eq_dec

(** val rule_eq_dec :
    'a1 eqDec -> 'a1 fLANG -> 'a1 lOGLANG -> 'a2 eqDec -> 'a2 fLANG -> ('a1, 'a2)
    sTRLANG -> ('a1, 'a2) rule -> ('a1, 'a2) rule -> bool **)

let rule_eq_dec eDf lf lL eDs ls sL r1 r2 =
  let a,b = r1 in
  let l,s = r2 in
  if eqdec (eqDec_list (eqDec_sequent eDf lf lL eDs ls sL)) a l
  then eqdec (eqDec_sequent eDf lf lL eDs ls sL) b s
  else false

(** val eqDec_rule :
    'a1 eqDec -> 'a1 fLANG -> 'a1 lOGLANG -> 'a2 eqDec -> 'a2 fLANG -> ('a1, 'a2)
    sTRLANG -> ('a1, 'a2) rule eqDec **)

let eqDec_rule =
  rule_eq_dec

(** val strIsFml_sig :
    'a1 eqDec -> 'a1 fLANG -> 'a1 lOGLANG -> 'a2 eqDec -> 'a2 fLANG -> ('a1, 'a2)
    sTRLANG -> 'a2 -> 'a1 **)

let strIsFml_sig _ _ _ eDs ls sL x =
  let s = var_dec eDs ls sL.fS sL.fSVAR x in
  (match s with
   | Some s0 -> s0
   | None -> assert false (* absurd case *))

(** val strIsFml_dec :
    'a1 eqDec -> 'a1 fLANG -> 'a1 lOGLANG -> 'a2 eqDec -> 'a2 fLANG -> ('a1, 'a2)
    sTRLANG -> 'a2 -> bool **)

let strIsFml_dec _ _ _ eDs ls sL x =
  let s = var_dec eDs ls sL.fS sL.fSVAR x in
  (match s with
   | Some _ -> true
   | None -> false)

(** val strCtnsFml_dec :
    'a1 eqDec -> 'a1 fLANG -> 'a1 lOGLANG -> 'a2 eqDec -> 'a2 fLANG -> ('a1, 'a2)
    sTRLANG -> 'a2 -> bool **)

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
    'a1 eqDec -> 'a1 fLANG -> 'a1 lOGLANG -> 'a2 eqDec -> 'a2 fLANG -> ('a1, 'a2)
    sTRLANG -> 'a2 -> string list **)

let strAtms eDf lf lL eDs ls sL =
  ipse_rect eDs ls (fun x iH ->
    match var_dec eDs ls sL.fS sL.fSVAR x with
    | Some s -> fmlAtms eDf lf lL s
    | None ->
      list_union (ls.ipse x) (fun x' ->
        if in_dec (eqdec eDs) x' (ls.ipse x) then iH x' __ else []))

(** val strFVs :
    'a1 eqDec -> 'a1 fLANG -> 'a1 lOGLANG -> 'a2 eqDec -> 'a2 fLANG -> ('a1, 'a2)
    sTRLANG -> 'a2 -> string list **)

let strFVs eDf lf lL eDs ls sL =
  ipse_rect eDs ls (fun x iH ->
    match var_dec eDs ls sL.fS sL.fSVAR x with
    | Some s -> fmlFVs eDf lf lL s
    | None ->
      list_union (ls.ipse x) (fun x' ->
        if in_dec (eqdec eDs) x' (ls.ipse x) then iH x' __ else []))

(** val strSVs :
    'a1 eqDec -> 'a1 fLANG -> 'a1 lOGLANG -> 'a2 eqDec -> 'a2 fLANG -> ('a1, 'a2)
    sTRLANG -> 'a2 -> string list **)

let strSVs _ _ _ eDs ls sL =
  allVars eDs ls sL.sV sL.sVVAR

(** val seqAtms :
    'a1 eqDec -> 'a1 fLANG -> 'a1 lOGLANG -> 'a2 eqDec -> 'a2 fLANG -> ('a1, 'a2)
    sTRLANG -> ('a1, 'a2) sequent -> string list **)

let seqAtms eDf lf lL eDs ls sL seq =
  app (strAtms eDf lf lL eDs ls sL (antec eDf lf lL eDs ls sL seq))
    (strAtms eDf lf lL eDs ls sL (succ eDf lf lL eDs ls sL seq))

(** val seqFVs :
    'a1 eqDec -> 'a1 fLANG -> 'a1 lOGLANG -> 'a2 eqDec -> 'a2 fLANG -> ('a1, 'a2)
    sTRLANG -> ('a1, 'a2) sequent -> string list **)

let seqFVs eDf lf lL eDs ls sL seq =
  app (strFVs eDf lf lL eDs ls sL (antec eDf lf lL eDs ls sL seq))
    (strFVs eDf lf lL eDs ls sL (succ eDf lf lL eDs ls sL seq))

(** val seqSVs :
    'a1 eqDec -> 'a1 fLANG -> 'a1 lOGLANG -> 'a2 eqDec -> 'a2 fLANG -> ('a1, 'a2)
    sTRLANG -> ('a1, 'a2) sequent -> string list **)

let seqSVs eDf lf lL eDs ls sL seq =
  app (strSVs eDf lf lL eDs ls sL (antec eDf lf lL eDs ls sL seq))
    (strSVs eDf lf lL eDs ls sL (succ eDf lf lL eDs ls sL seq))

type 'structr sSubst = string -> 'structr

type ('formula, 'structr) afsSubst = 'formula afSubst*'structr sSubst

(** val strSubst :
    'a1 eqDec -> 'a1 fLANG -> 'a1 lOGLANG -> 'a2 eqDec -> 'a2 fLANG -> ('a1, 'a2)
    sTRLANG -> ('a1, 'a2) afsSubst -> 'a2 -> 'a2 **)

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
    'a1 eqDec -> 'a1 fLANG -> 'a1 lOGLANG -> 'a2 eqDec -> 'a2 fLANG -> ('a1, 'a2)
    sTRLANG -> ('a1, 'a2) afsSubst -> ('a1, 'a2) sequent -> ('a1, 'a2) sequent **)

let seqSubst eDf lf lL eDs ls sL afs = function
| Sequent (x, y) ->
  Sequent ((strSubst eDf lf lL eDs ls sL afs x), (strSubst eDf lf lL eDs ls sL afs y))

(** val ruleSubst :
    'a1 eqDec -> 'a1 fLANG -> 'a1 lOGLANG -> 'a2 eqDec -> 'a2 fLANG -> ('a1, 'a2)
    sTRLANG -> ('a1, 'a2) afsSubst -> ('a1, 'a2) rule -> ('a1, 'a2) rule **)

let ruleSubst eDf lf lL eDs ls sL afs = function
| ps,c ->
  (map (seqSubst eDf lf lL eDs ls sL afs) ps),(seqSubst eDf lf lL eDs ls sL afs c)

(** val i_s :
    'a1 eqDec -> 'a1 fLANG -> 'a1 lOGLANG -> 'a2 eqDec -> 'a2 fLANG -> ('a1, 'a2)
    sTRLANG -> 'a2 sSubst **)

let i_s _ _ _ _ _ sL x =
  sL.sV x

(** val str_matchsub_Atm :
    'a1 eqDec -> 'a1 fLANG -> 'a1 lOGLANG -> 'a2 eqDec -> 'a2 fLANG -> ('a1, 'a2)
    sTRLANG -> 'a2 -> 'a2 -> aSubst **)

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
    'a1 eqDec -> 'a1 fLANG -> 'a1 lOGLANG -> 'a2 eqDec -> 'a2 fLANG -> ('a1, 'a2)
    sTRLANG -> 'a2 -> 'a2 -> 'a1 fSubst **)

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
    'a1 eqDec -> 'a1 fLANG -> 'a1 lOGLANG -> 'a2 eqDec -> 'a2 fLANG -> ('a1, 'a2)
    sTRLANG -> 'a2 -> 'a2 -> 'a2 sSubst **)

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
    'a1 eqDec -> 'a1 fLANG -> 'a1 lOGLANG -> 'a2 eqDec -> 'a2 fLANG -> ('a1, 'a2)
    sTRLANG -> ('a1, 'a2) sequent -> ('a1, 'a2) sequent -> aSubst **)

let seq_matchsub_Atm eDf lf lL eDs ls sL s t p =
  let Sequent (x1, y1) = s in
  let Sequent (x2, y2) = t in
  if in_dec (eqdec eqDec_string) p (strAtms eDf lf lL eDs ls sL x1)
  then str_matchsub_Atm eDf lf lL eDs ls sL x1 x2 p
  else if in_dec (eqdec eqDec_string) p (strAtms eDf lf lL eDs ls sL y1)
       then str_matchsub_Atm eDf lf lL eDs ls sL y1 y2 p
       else p

(** val seq_matchsub_FV :
    'a1 eqDec -> 'a1 fLANG -> 'a1 lOGLANG -> 'a2 eqDec -> 'a2 fLANG -> ('a1, 'a2)
    sTRLANG -> ('a1, 'a2) sequent -> ('a1, 'a2) sequent -> 'a1 fSubst **)

let seq_matchsub_FV eDf lf lL eDs ls sL s t v =
  let Sequent (x1, y1) = s in
  let Sequent (x2, y2) = t in
  if in_dec (eqdec eqDec_string) v (strFVs eDf lf lL eDs ls sL x1)
  then str_matchsub_FV eDf lf lL eDs ls sL x1 x2 v
  else if in_dec (eqdec eqDec_string) v (strFVs eDf lf lL eDs ls sL y1)
       then str_matchsub_FV eDf lf lL eDs ls sL y1 y2 v
       else lL.fV v

(** val seq_matchsub_SV :
    'a1 eqDec -> 'a1 fLANG -> 'a1 lOGLANG -> 'a2 eqDec -> 'a2 fLANG -> ('a1, 'a2)
    sTRLANG -> ('a1, 'a2) sequent -> ('a1, 'a2) sequent -> 'a2 sSubst **)

let seq_matchsub_SV eDf lf lL eDs ls sL s t v =
  let Sequent (x1, y1) = s in
  let Sequent (x2, y2) = t in
  if in_dec (eqdec eqDec_string) v (strSVs eDf lf lL eDs ls sL x1)
  then str_matchsub_SV eDf lf lL eDs ls sL x1 x2 v
  else if in_dec (eqdec eqDec_string) v (strSVs eDf lf lL eDs ls sL y1)
       then str_matchsub_SV eDf lf lL eDs ls sL y1 y2 v
       else sL.sV v

(** val seq_matchsub :
    'a1 eqDec -> 'a1 fLANG -> 'a1 lOGLANG -> 'a2 eqDec -> 'a2 fLANG -> ('a1, 'a2)
    sTRLANG -> ('a1, 'a2) sequent -> ('a1, 'a2) sequent -> ('a1, 'a2) afsSubst **)

let seq_matchsub eDf lf lL eDs ls sL s t =
  ((seq_matchsub_Atm eDf lf lL eDs ls sL s t),(seq_matchsub_FV eDf lf lL eDs ls sL s t)),
    (seq_matchsub_SV eDf lf lL eDs ls sL s t)

(** val listseq_matchsub_Atm :
    'a1 eqDec -> 'a1 fLANG -> 'a1 lOGLANG -> 'a2 eqDec -> 'a2 fLANG -> ('a1, 'a2)
    sTRLANG -> ('a1, 'a2) sequent list -> ('a1, 'a2) sequent list -> aSubst **)

let listseq_matchsub_Atm eDf lf lL eDs ls sL ls0 lt p =
  match in_some_dec eqDec_string p (zip (fun x x0 -> x,x0) ls0 lt)
          (comp (seqAtms eDf lf lL eDs ls sL) fst) with
  | Some s0 -> let s,t = s0 in seq_matchsub_Atm eDf lf lL eDs ls sL s t p
  | None -> p

(** val listseq_matchsub_FV :
    'a1 eqDec -> 'a1 fLANG -> 'a1 lOGLANG -> 'a2 eqDec -> 'a2 fLANG -> ('a1, 'a2)
    sTRLANG -> ('a1, 'a2) sequent list -> ('a1, 'a2) sequent list -> 'a1 fSubst **)

let listseq_matchsub_FV eDf lf lL eDs ls sL ls0 lt v =
  match in_some_dec eqDec_string v (zip (fun x x0 -> x,x0) ls0 lt)
          (comp (seqFVs eDf lf lL eDs ls sL) fst) with
  | Some s0 -> let s,t = s0 in seq_matchsub_FV eDf lf lL eDs ls sL s t v
  | None -> lL.fV v

(** val listseq_matchsub_SV :
    'a1 eqDec -> 'a1 fLANG -> 'a1 lOGLANG -> 'a2 eqDec -> 'a2 fLANG -> ('a1, 'a2)
    sTRLANG -> ('a1, 'a2) sequent list -> ('a1, 'a2) sequent list -> 'a2 sSubst **)

let listseq_matchsub_SV eDf lf lL eDs ls sL ls0 lt v =
  match in_some_dec eqDec_string v (zip (fun x x0 -> x,x0) ls0 lt)
          (comp (seqSVs eDf lf lL eDs ls sL) fst) with
  | Some s0 -> let s,t = s0 in seq_matchsub_SV eDf lf lL eDs ls sL s t v
  | None -> sL.sV v

(** val listseq_matchsub :
    'a1 eqDec -> 'a1 fLANG -> 'a1 lOGLANG -> 'a2 eqDec -> 'a2 fLANG -> ('a1, 'a2)
    sTRLANG -> ('a1, 'a2) sequent list -> ('a1, 'a2) sequent list -> ('a1, 'a2) afsSubst **)

let listseq_matchsub eDf lf lL eDs ls sL ls0 lt =
  ((listseq_matchsub_Atm eDf lf lL eDs ls sL ls0 lt),(listseq_matchsub_FV eDf lf lL eDs
                                                       ls sL ls0 lt)),(listseq_matchsub_SV
                                                                        eDf lf lL eDs
                                                                        ls sL ls0 lt)

(** val listseqSubst_dec :
    'a1 eqDec -> 'a1 fLANG -> 'a1 lOGLANG -> 'a2 eqDec -> 'a2 fLANG -> ('a1, 'a2)
    sTRLANG -> ('a1, 'a2) sequent list -> ('a1, 'a2) sequent list -> ('a1, 'a2)
    afsSubst option **)

let listseqSubst_dec eDf lf lL eDs ls sL ls0 lt =
  let s =
    eqdec (eqDec_list (eqDec_sequent eDf lf lL eDs ls sL))
      (map (seqSubst eDf lf lL eDs ls sL (listseq_matchsub eDf lf lL eDs ls sL ls0 lt))
        ls0) lt
  in
  if s then Some (listseq_matchsub eDf lf lL eDs ls sL ls0 lt) else None

(** val ruleSubst_dec :
    'a1 eqDec -> 'a1 fLANG -> 'a1 lOGLANG -> 'a2 eqDec -> 'a2 fLANG -> ('a1, 'a2)
    sTRLANG -> ('a1, 'a2) rule -> ('a1, 'a2) rule -> ('a1, 'a2) afsSubst option **)

let ruleSubst_dec eDf lf lL eDs ls sL r r' =
  let l,s = r in let l0,s0 = r' in listseqSubst_dec eDf lf lL eDs ls sL (s::l) (s0::l0)

(** val ruleInst_ruleSubst :
    'a1 eqDec -> 'a1 fLANG -> 'a1 lOGLANG -> 'a2 eqDec -> 'a2 fLANG -> ('a1, 'a2)
    sTRLANG -> ('a1, 'a2) rule -> ('a1, 'a2) rule -> ('a1, 'a2) afsSubst **)

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
| p::l' -> (fun x -> let s,a = p in if (=) x s then a else f_spec eDf lf lL l' x)

(** val s_spec :
    'a1 eqDec -> 'a1 fLANG -> 'a1 lOGLANG -> 'a2 eqDec -> 'a2 fLANG -> ('a1, 'a2)
    sTRLANG -> (string*'a2) list -> 'a2 sSubst **)

let rec s_spec eDf lf lL eDs ls sL = function
| [] -> i_s eDf lf lL eDs ls sL
| p::l' ->
  (fun x -> let s,x0 = p in if (=) x s then x0 else s_spec eDf lf lL eDs ls sL l' x)

(** val af_spec :
    'a1 eqDec -> 'a1 fLANG -> 'a1 lOGLANG -> (string*string) list -> (string*'a1) list
    -> 'a1 afSubst **)

let af_spec eDf lf lL lp lf0 =
  (a_spec lp),(f_spec eDf lf lL lf0)

(** val afs_spec :
    'a1 eqDec -> 'a1 fLANG -> 'a1 lOGLANG -> 'a2 eqDec -> 'a2 fLANG -> ('a1, 'a2)
    sTRLANG -> (string*string) list -> (string*'a1) list -> (string*'a2) list -> ('a1,
    'a2) afsSubst **)

let afs_spec eDf lf lL eDs ls sL lp lf0 ls0 =
  (af_spec eDf lf lL lp lf0),(s_spec eDf lf lL eDs ls sL ls0)

type ('formula, 'structr) dertree =
| Unf of ('formula, 'structr) sequent
| Der of ('formula, 'structr) sequent * ('formula, 'structr) rule
   * ('formula, 'structr) dertree list

(** val dertree_rect_gen :
    'a1 eqDec -> 'a1 fLANG -> 'a1 lOGLANG -> 'a2 eqDec -> 'a2 fLANG -> ('a1, 'a2)
    sTRLANG -> 'a4 -> (('a1, 'a2) dertree -> ('a1, 'a2) dertree list -> 'a3 -> 'a4 ->
    'a4) -> (('a1, 'a2) sequent -> 'a3) -> (('a1, 'a2) sequent -> ('a1, 'a2) rule ->
    ('a1, 'a2) dertree list -> 'a4 -> 'a3) -> ('a1, 'a2) dertree -> 'a3 **)

let rec dertree_rect_gen eDf lf lL eDs ls sL p_nil p_cons p_Unf p_Der dt =
  let go_list =
    let rec go_list = function
    | [] -> p_nil
    | t::l0 ->
      p_cons t l0 (dertree_rect_gen eDf lf lL eDs ls sL p_nil p_cons p_Unf p_Der t)
        (go_list l0)
    in go_list
  in
  (match dt with
   | Unf s -> p_Unf s
   | Der (s, r, l) -> p_Der s r l (go_list l))

(** val dertree_eq_dec :
    'a1 eqDec -> 'a1 fLANG -> 'a1 lOGLANG -> 'a2 eqDec -> 'a2 fLANG -> ('a1, 'a2)
    sTRLANG -> ('a1, 'a2) dertree -> ('a1, 'a2) dertree -> bool **)

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
      then let s2 = rule_eq_dec eDf lf lL eDs ls sL r1 r in if s2 then iH l else false
      else false)

(** val eqDec_dertree :
    'a1 eqDec -> 'a1 fLANG -> 'a1 lOGLANG -> 'a2 eqDec -> 'a2 fLANG -> ('a1, 'a2)
    sTRLANG -> ('a1, 'a2) dertree eqDec **)

let eqDec_dertree =
  dertree_eq_dec

(** val conclDT :
    'a1 eqDec -> 'a1 fLANG -> 'a1 lOGLANG -> 'a2 eqDec -> 'a2 fLANG -> ('a1, 'a2)
    sTRLANG -> ('a1, 'a2) dertree -> ('a1, 'a2) sequent **)

let conclDT _ _ _ _ _ _ = function
| Unf s -> s
| Der (s, _, _) -> s

(** val cUT :
    'a1 eqDec -> 'a1 fLANG -> 'a1 lOGLANG -> 'a2 eqDec -> 'a2 fLANG -> ('a1, 'a2)
    sTRLANG -> ('a1, 'a2) rule **)

let cUT _ _ lL _ _ sL =
  ((Sequent ((sL.sV "X"), (sL.fS (lL.fV "A"))))::((Sequent ((sL.fS (lL.fV "A")),
    (sL.sV "Y")))::[])),(Sequent ((sL.sV "X"), (sL.sV "Y")))

(** val cUT_spec :
    'a1 eqDec -> 'a1 fLANG -> 'a1 lOGLANG -> 'a2 eqDec -> 'a2 fLANG -> ('a1, 'a2)
    sTRLANG -> 'a1 -> 'a2 -> 'a2 -> ('a1, 'a2) afsSubst **)

let cUT_spec eDf lf lL eDs ls sL a x y =
  afs_spec eDf lf lL eDs ls sL [] (("A",a)::[]) (("X",x)::(("Y",y)::[]))

(** val lP_dec :
    'a1 eqDec -> 'a1 fLANG -> 'a1 lOGLANG -> 'a2 eqDec -> 'a2 fLANG -> ('a1, 'a2)
    sTRLANG -> ('a1, 'a2) dertree list -> 'a1 -> ('a2, (('a1, 'a2) rule, (('a1, 'a2)
    dertree list, ('a1, 'a2) dertree) sigT) sigT) sigT option **)

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
             if s4 then Some (ExistT (x1, (ExistT (r, (ExistT (l0, x0)))))) else None
        else None)
   | None -> None)

(** val rP_dec :
    'a1 eqDec -> 'a1 fLANG -> 'a1 lOGLANG -> 'a2 eqDec -> 'a2 fLANG -> ('a1, 'a2)
    sTRLANG -> ('a1, 'a2) dertree list -> 'a1 -> ('a2, (('a1, 'a2) dertree, (('a1, 'a2)
    rule, ('a1, 'a2) dertree list) sigT) sigT) sigT option **)

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
             if s4 then Some (ExistT (y, (ExistT (x, (ExistT (r, l0)))))) else None
        else None)
   | None -> None)

(** val right_cut_dec :
    'a1 eqDec -> 'a1 fLANG -> 'a1 lOGLANG -> 'a2 eqDec -> 'a2 fLANG -> ('a1, 'a2)
    sTRLANG -> ('a1, 'a2) dertree list -> (('a1, 'a2) dertree, (('a1, 'a2) dertree,
    ('a2, 'a1) sigT) sigT) sigT option **)

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
| Deriv_cofseq_ext of ('formula, 'structr) sequent list * ('formula, 'structr) sequent
   * ('formula, 'structr) rule * ('formula, 'structr) deriv_cofseqs
and ('formula, 'structr) deriv_cofseqs =
| Deriv_cofseqs_nil
| Deriv_cofseqs_cons of ('formula, 'structr) sequent
   * ('formula, 'structr) sequent list * ('formula, 'structr) deriv_cofseq
   * ('formula, 'structr) deriv_cofseqs

(** val deriv_cofseqs_mut_rect :
    'a1 eqDec -> 'a1 fLANG -> 'a1 lOGLANG -> 'a2 eqDec -> 'a2 fLANG -> ('a1, 'a2)
    sTRLANG -> ('a1, 'a2) dISPCALC -> (('a1, 'a2) sequent list -> ('a1, 'a2) sequent ->
    ('a1, 'a2) rule -> __ -> __ -> __ -> ('a1, 'a2) deriv_cofseqs -> 'a4 -> 'a3) -> 'a4
    -> (('a1, 'a2) sequent -> ('a1, 'a2) sequent list -> ('a1, 'a2) deriv_cofseq -> 'a3
    -> ('a1, 'a2) deriv_cofseqs -> 'a4 -> 'a4) -> ('a1, 'a2) sequent list -> ('a1, 'a2)
    deriv_cofseqs -> 'a4 **)

let deriv_cofseqs_mut_rect _ _ _ _ _ _ _ f f0 f1 =
  let rec f2 _ = function
  | Deriv_cofseq_ext (ps, c, r, d0) -> f ps c r __ __ __ d0 (f3 ps d0)
  and f3 _ = function
  | Deriv_cofseqs_nil -> f0
  | Deriv_cofseqs_cons (c, cs, d0, d1) -> f1 c cs d0 (f2 c d0) d1 (f3 cs d1)
  in f3

(** val deriv_cofseq_mut_rect :
    'a1 eqDec -> 'a1 fLANG -> 'a1 lOGLANG -> 'a2 eqDec -> 'a2 fLANG -> ('a1, 'a2)
    sTRLANG -> ('a1, 'a2) dISPCALC -> (('a1, 'a2) sequent list -> ('a1, 'a2) sequent ->
    ('a1, 'a2) rule -> __ -> __ -> __ -> ('a1, 'a2) deriv_cofseqs -> 'a4 -> 'a3) -> 'a4
    -> (('a1, 'a2) sequent -> ('a1, 'a2) sequent list -> ('a1, 'a2) deriv_cofseq -> 'a3
    -> ('a1, 'a2) deriv_cofseqs -> 'a4 -> 'a4) -> ('a1, 'a2) sequent -> ('a1, 'a2)
    deriv_cofseq -> 'a3 **)

let deriv_cofseq_mut_rect _ _ _ _ _ _ _ f f0 f1 =
  let rec f2 _ = function
  | Deriv_cofseq_ext (ps, c, r, d0) -> f ps c r __ __ __ d0 (f3 ps d0)
  and f3 _ = function
  | Deriv_cofseqs_nil -> f0
  | Deriv_cofseqs_cons (c, cs, d0, d1) -> f1 c cs d0 (f2 c d0) d1 (f3 cs d1)
  in f2

(** val forallT_deriv_cofseqs :
    'a1 eqDec -> 'a1 fLANG -> 'a1 lOGLANG -> 'a2 eqDec -> 'a2 fLANG -> ('a1, 'a2)
    sTRLANG -> ('a1, 'a2) dISPCALC -> ('a1, 'a2) sequent list -> (('a1, 'a2) sequent,
    ('a1, 'a2) deriv_cofseq) forallT -> ('a1, 'a2) deriv_cofseqs **)

let rec forallT_deriv_cofseqs eDf lf lL eDs ls sL dC cs hall =
  match cs with
  | [] -> Deriv_cofseqs_nil
  | y::l ->
    Deriv_cofseqs_cons (y, l, (forallT_inv y l hall),
      (forallT_deriv_cofseqs eDf lf lL eDs ls sL dC l (forallT_inv_tail y l hall)))

(** val forallT_deriv_cofseqs_iff :
    'a1 eqDec -> 'a1 fLANG -> 'a1 lOGLANG -> 'a2 eqDec -> 'a2 fLANG -> ('a1, 'a2)
    sTRLANG -> ('a1, 'a2) dISPCALC -> ('a1, 'a2) sequent list -> ((('a1, 'a2) sequent,
    ('a1, 'a2) deriv_cofseq) forallT, ('a1, 'a2) deriv_cofseqs) iffT0 **)

let forallT_deriv_cofseqs_iff eDf lf lL eDs ls sL dC cs =
  (forallT_deriv_cofseqs eDf lf lL eDs ls sL dC cs),(deriv_cofseqs_mut_rect eDf lf lL
                                                      eDs ls sL dC
                                                      (fun ps c r _ _ _ hders _ ->
                                                      Deriv_cofseq_ext (ps, c, r,
                                                      hders)) ForallT_nil
                                                      (fun c cs0 hder _ _ hallders ->
                                                      ForallT_cons (c, cs0, hder,
                                                      hallders)) cs)

(** val deriv_cofseq_iff :
    'a1 eqDec -> 'a1 fLANG -> 'a1 lOGLANG -> 'a2 eqDec -> 'a2 fLANG -> ('a1, 'a2)
    sTRLANG -> ('a1, 'a2) dISPCALC -> ('a1, 'a2) sequent -> (('a1, 'a2) deriv_cofseq,
    ('a1, 'a2) dertree) iffT0 **)

let deriv_cofseq_iff eDf lf lL eDs ls sL dC s =
  (deriv_cofseq_mut_rect eDf lf lL eDs ls sL dC (fun _ c r _ _ _ _ x -> Der (c, r, x))
    [] (fun _ _ _ x _ x0 -> x::x0) s),(fun x ->
    dertree_rect_gen eDf lf lL eDs ls sL ForallT_nil (fun t l pt pl -> ForallT_cons (t,
      l, pt, pl)) (fun _ _ _ -> assert false (* absurd case *)) (fun s0 r l iH _ _ ->
      let x0 = fun l0 ->
        let x0,_ = forall_ForallT (eqDec_dertree eDf lf lL eDs ls sL) l0 in Obj.magic x0
      in
      let hprol = x0 l __ in
      let x1 = fun l0 ->
        let x1,_ = forall_ForallT (eqDec_dertree eDf lf lL eDs ls sL) l0 in Obj.magic x1
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
      Deriv_cofseq_ext ((map (conclDT eDf lf lL eDs ls sL) l), s0, r, iH3)) x __ __)

(** val deriv_cofseqs_iff :
    'a1 eqDec -> 'a1 fLANG -> 'a1 lOGLANG -> 'a2 eqDec -> 'a2 fLANG -> ('a1, 'a2)
    sTRLANG -> ('a1, 'a2) dISPCALC -> ('a1, 'a2) sequent list -> (('a1, 'a2)
    deriv_cofseqs, ('a1, 'a2) dertree list) iffT0 **)

let deriv_cofseqs_iff eDf lf lL eDs ls sL dC ls0 =
  (deriv_cofseqs_mut_rect eDf lf lL eDs ls sL dC (fun _ c r _ _ _ _ x -> Der (c, r, x))
    [] (fun _ _ _ x _ x0 -> x::x0) ls0),(fun x ->
    let x0,_ = forallT_deriv_cofseqs_iff eDf lf lL eDs ls sL dC ls0 in
    x0
      (forallT_act ls0 (fun s ->
        let _,x1 = deriv_cofseq_iff eDf lf lL eDs ls sL dC s in x1)
        (let _,x1 = forallT_forall (eqDec_sequent eDf lf lL eDs ls sL) ls0 in
         x1 (fun s _ ->
           in_map_inv_sig (eqDec_sequent eDf lf lL eDs ls sL)
             (conclDT eDf lf lL eDs ls sL) x s))))

type ('formula, 'structr) c8 =
  'formula -> ('formula, 'structr) dertree -> __ -> __ -> __ -> ('formula, 'structr)
  dertree

(** val defSubs : string list -> 'a1 sSubst -> 'a1 sSubst -> 'a1 sSubst **)

let defSubs ls sub1 sub2 s =
  if in_dec (=) s ls then sub1 s else sub2 s

type ('formula, 'structr) sSubstfor = 'structr sSubst

(** val stepSub :
    'a1 eqDec -> 'a1 fLANG -> 'a1 lOGLANG -> 'a2 eqDec -> 'a2 fLANG -> ('a1, 'a2)
    sTRLANG -> ('a1, 'a2) afsSubst -> ('a1, 'a2) sequent -> ('a1, 'a2) sequent -> ('a1,
    'a2) sSubstfor -> ('a1, 'a2) afsSubst **)

let stepSub eDf lf lL eDs ls sL afs concl _ ssub =
  let af,suba = afs in af,(defSubs (seqSVs eDf lf lL eDs ls sL concl) ssub suba)

(** val comSubn :
    'a1 eqDec -> 'a1 fLANG -> 'a1 lOGLANG -> 'a2 eqDec -> 'a2 fLANG -> ('a1, 'a2)
    sTRLANG -> ('a2*'a2) list -> 'a2 sSubst list -> 'a1 afSubst -> 'a2 sSubst **)

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
    'a1 eqDec -> 'a1 fLANG -> 'a1 lOGLANG -> 'a2 eqDec -> 'a2 fLANG -> ('a1, 'a2)
    sTRLANG -> 'a1 -> 'a2 -> 'a2 -> 'a1 afSubst -> 'a2 sSubst -> bool -> 'a2 -> 'a2
    sSubst **)

let sF_str_sub eDf lf lL eDs ls sL a x y af s b z =
  ipse_rect eDs ls (fun x0 iH _ _ b0 z0 _ ->
    let s0 = eqdec eDs (strSubst eDf lf lL eDs ls sL (af,s) x0) z0 in
    if s0
    then s
    else let s1 =
           eqdec (eqDec_prod eDs eDs) ((strSubst eDf lf lL eDs ls sL (af,s) x0),z0)
             ((sL.fS a),y)
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
                      let l = zip (fun x1 x2 -> x1,x2) (ls.ipse x0) (ls.ipse z0) in
                      let _,x1 = forallT_forall (eqDec_prod eDs eDs) l in
                      x1 (fun x2 _ ->
                        let s4,s5 = x2 in
                        let hinX'Z' =
                          in_zip_pair_23_sig_1 eDs eDs (sL.sgnips x0)
                            (map (strSubst eDf lf lL eDs ls sL (af,s)) (ls.ipse x0))
                            (ls.ipse z0) (strSubst eDf lf lL eDs ls sL (af,s) s4) s5
                        in
                        iH s4 __ __ __ (nxorb b0 hinX'Z') s5 __)
                    in
                    let hall0 =
                      forallT_sig_elim
                        (zip (fun x1 x2 -> x1,x2) (ls.ipse x0) (ls.ipse z0)) hall
                    in
                    comSubn eDf lf lL eDs ls sL
                      (zip (fun x1 x2 -> x1,x2) (ls.ipse x0) (ls.ipse z0)) hall0 af)))
    x __ __ b z __

(** val exSub :
    'a1 eqDec -> 'a1 fLANG -> 'a1 lOGLANG -> 'a2 eqDec -> 'a2 fLANG -> ('a1, 'a2)
    sTRLANG -> 'a1 -> 'a2 -> 'a2 -> 'a2 -> 'a2 -> 'a1 afSubst -> 'a2 sSubst -> bool ->
    'a2 sSubst **)

let exSub eDf lf lL eDs ls sL a pat y _ stry af suba pn =
  sF_str_sub eDf lf lL eDs ls sL a pat y af suba pn stry

(** val seqExSub1 :
    'a1 eqDec -> 'a1 fLANG -> 'a1 lOGLANG -> 'a2 eqDec -> 'a2 fLANG -> ('a1, 'a2)
    sTRLANG -> ('a1, 'a2) sequent -> ('a1, 'a2) sequent -> ('a1, 'a2) sequent -> 'a1
    afSubst -> 'a2 sSubst -> bool -> 'a1 -> 'a2 -> ('a1, 'a2) sSubstfor **)

let seqExSub1 eDf lf lL eDs ls sL pat seqa seqy af suba pn a y =
  let Sequent (x, y0) = pat in
  let Sequent (x0, y1) = seqa in
  let Sequent (x1, y2) = seqy in
  let s = exSub eDf lf lL eDs ls sL a x y x0 x1 af suba (negb pn) in
  let s0 = exSub eDf lf lL eDs ls sL a y0 y y1 y2 af suba pn in
  defSubs (strSVs eDf lf lL eDs ls sL x) s s0

(** val seqExSub2 :
    'a1 eqDec -> 'a1 fLANG -> 'a1 lOGLANG -> 'a2 eqDec -> 'a2 fLANG -> ('a1, 'a2)
    sTRLANG -> 'a2 -> 'a2 -> 'a2 -> 'a2 -> 'a2 -> 'a2 -> ('a1, 'a2) sequent -> ('a1,
    'a2) sequent -> ('a1, 'a2) sequent -> 'a1 afSubst -> 'a2 sSubst -> 'a1 -> 'a2 ->
    bool -> ('a1, 'a2) sSubstfor **)

let seqExSub2 eDf lf lL eDs ls sL pant psuc aant asuc yant ysuc pat seqa seqy af suba a y pn =
  let s = strCtnsFml_dec eDf lf lL eDs ls sL pant in
  if s
  then let s0 = strCtnsFml_dec eDf lf lL eDs ls sL psuc in
       if s0 then suba else exSub eDf lf lL eDs ls sL a psuc y asuc ysuc af suba pn
  else let s0 = strCtnsFml_dec eDf lf lL eDs ls sL psuc in
       if s0
       then exSub eDf lf lL eDs ls sL a pant y aant yant af suba (negb pn)
       else seqExSub1 eDf lf lL eDs ls sL pat seqa seqy af suba pn a y

type ('formula, 'structr) bELNAP =
  ('formula, 'structr) c8
  (* singleton inductive, whose constructor was Build_BELNAP *)

(** val c8_holds :
    'a1 eqDec -> 'a1 fLANG -> 'a1 lOGLANG -> 'a2 eqDec -> 'a2 fLANG -> ('a1, 'a2)
    sTRLANG -> ('a1, 'a2) dISPCALC -> ('a1, 'a2) bELNAP -> 'a1 -> ('a1, 'a2) dertree ->
    ('a1, 'a2) dertree **)

let c8_holds _ _ _ _ _ _ _ bELNAP0 m dt =
  bELNAP0 m dt __ __ __

type ('formula, 'structr) derivRule =
  ('formula, 'structr) dertree
  (* singleton inductive, whose constructor was Build_DerivRule *)

(** val deriv_cofseq_rule_bw_inDC :
    'a1 eqDec -> 'a1 fLANG -> 'a1 lOGLANG -> 'a2 eqDec -> 'a2 fLANG -> ('a1, 'a2)
    sTRLANG -> ('a1, 'a2) dISPCALC -> ('a1, 'a2) sequent list -> ('a1, 'a2) sequent ->
    ('a1, 'a2) afsSubst -> ('a1, 'a2) deriv_cofseqs -> ('a1, 'a2) deriv_cofseq **)

let deriv_cofseq_rule_bw_inDC eDf lf lL eDs ls sL _ ss c afs hders =
  Deriv_cofseq_ext ((map (seqSubst eDf lf lL eDs ls sL afs) ss),
    (seqSubst eDf lf lL eDs ls sL afs c), (ss,c), hders)

(** val extSub2_fs :
    'a1 eqDec -> 'a1 fLANG -> 'a1 lOGLANG -> 'a2 eqDec -> 'a2 fLANG -> ('a1, 'a2)
    sTRLANG -> ('a1, 'a2) rule -> ('a1, 'a2) rule -> ('a1, 'a2) sequent -> 'a2 -> 'a2
    -> 'a2 -> 'a2 -> 'a2 -> 'a2 -> 'a1 -> 'a2 -> bool -> ('a1, 'a2) afsSubst **)

let extSub2_fs eDf lf lL eDs ls sL r rA conclY pant psuc aant asuc yant ysuc a y pn =
  let s = ruleInst_ruleSubst eDf lf lL eDs ls sL r rA in
  let a0,s0 = s in
  stepSub eDf lf lL eDs ls sL (a0,s0) (conclRule eDf lf lL eDs ls sL r) conclY
    (seqExSub2 eDf lf lL eDs ls sL pant psuc aant asuc yant ysuc
      (conclRule eDf lf lL eDs ls sL r) (conclRule eDf lf lL eDs ls sL rA) conclY a0 s0
      a y pn)

(** val seqreps_map_concl :
    'a1 eqDec -> 'a1 fLANG -> 'a1 lOGLANG -> 'a2 eqDec -> 'a2 fLANG -> ('a1, 'a2)
    sTRLANG -> bool -> 'a2 -> 'a2 -> ('a1, 'a2) sequent list -> ('a1, 'a2) sequent list
    -> (('a1, 'a2) sequent, ('a1, 'a2) sequent -> __ -> ('a1, 'a2) dertree) forallT ->
    ('a1, 'a2) dertree list **)

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
    'a1 eqDec -> 'a1 fLANG -> 'a1 lOGLANG -> 'a2 eqDec -> 'a2 fLANG -> ('a1, 'a2)
    sTRLANG -> ('a1, 'a2) dISPCALC -> ('a1, 'a2) bELNAP -> ('a1, 'a2) dertree -> ('a1,
    'a2) dertree -> 'a1 -> 'a2 -> ('a1, 'a2) sequent -> ('a1, 'a2) dertree **)

let makeCutLP eDf lf lL eDs ls sL _ _ dtAY dtA a y seqY =
  dertree_rect_gen eDf lf lL eDs ls sL ForallT_nil (fun t l pt pl -> ForallT_cons (t,
    l, pt, pl)) (fun _ _ _ -> assert false (* absurd case *))
    (fun s r l iH _ _ seqY0 _ ->
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
           if s2 then let s3 = eqdec eDs y2 y1 in if s3 then false else true else false
      else false
    in
    if h
    then let seqYl = Sequent (x0, (sL.fS a)) in
         let s1 =
           extSub2_fs eDf lf lL eDs ls sL r rA seqYl x y0 x1 y2 x0 (sL.fS a) a y true
         in
         let s2 =
           seqreps_map_concl eDf lf lL eDs ls sL true (sL.fS a) y
             (premsRule eDf lf lL eDs ls sL rA)
             (premsRule eDf lf lL eDs ls sL (ruleSubst eDf lf lL eDs ls sL s1 r))
             (let f = conclDT eDf lf lL eDs ls sL in
              let _,x2 = forallT_map f l in
              x2
                (let lemma = forallT_forall (eqDec_dertree eDf lf lL eDs ls sL) l in
                 flip2 (Obj.magic (fun _ _ -> iffT_flip_arrow_subrelation)) __ __ lemma
                   (let iH0 =
                      let lemma0 = forallT_forall (eqDec_dertree eDf lf lL eDs ls sL) l
                      in
                      iffT_arrow_subrelation (Obj.magic lemma0) (Obj.magic iH)
                    in
                    fun x3 _ t _ -> Obj.magic iH0 x3 __ __ __ t __)))
         in
         Der (seqY0, (cUT eDf lf lL eDs ls sL), ((Der (seqYl, r, s2))::(dtAY::[])))
    else let s1 = extSub2_fs eDf lf lL eDs ls sL r rA seqY0 x y0 x1 y2 x0 y1 a y true in
         let rsubY = ruleSubst eDf lf lL eDs ls sL s1 r in
         let s2 =
           seqreps_map_concl eDf lf lL eDs ls sL true (sL.fS a) y
             (premsRule eDf lf lL eDs ls sL rA) (premsRule eDf lf lL eDs ls sL rsubY)
             (let f = conclDT eDf lf lL eDs ls sL in
              let _,x2 = forallT_map f l in
              x2
                (let lemma = forallT_forall (eqDec_dertree eDf lf lL eDs ls sL) l in
                 flip2 (Obj.magic (fun _ _ -> iffT_flip_arrow_subrelation)) __ __ lemma
                   (let iH0 =
                      let lemma0 = forallT_forall (eqDec_dertree eDf lf lL eDs ls sL) l
                      in
                      iffT_arrow_subrelation (Obj.magic lemma0) (Obj.magic iH)
                    in
                    fun x3 _ t _ -> Obj.magic iH0 x3 __ __ __ t __)))
         in
         Der (seqY0, r, s2)) dtA __ __ seqY __

(** val allLP :
    'a1 eqDec -> 'a1 fLANG -> 'a1 lOGLANG -> 'a2 eqDec -> 'a2 fLANG -> ('a1, 'a2)
    sTRLANG -> ('a1, 'a2) dISPCALC -> ('a1, 'a2) bELNAP -> ('a1, 'a2) dertree -> 'a1 ->
    ('a1, 'a2) dertree **)

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
    'a1 eqDec -> 'a1 fLANG -> 'a1 lOGLANG -> 'a2 eqDec -> 'a2 fLANG -> ('a1, 'a2)
    sTRLANG -> ('a1, 'a2) dISPCALC -> ('a1, 'a2) bELNAP -> ('a1, 'a2) dertree -> ('a1,
    'a2) dertree -> 'a1 -> 'a2 -> ('a1, 'a2) sequent -> ('a1, 'a2) dertree **)

let makeCutLRP eDf lf lL eDs ls sL _ _ dtAY dtA a y seqY =
  dertree_rect_gen eDf lf lL eDs ls sL ForallT_nil (fun t l pt pl -> ForallT_cons (t,
    l, pt, pl)) (fun _ _ _ -> assert false (* absurd case *))
    (fun s r l iH _ _ seqY0 _ ->
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
           if s2 then let s3 = eqdec eDs x1 x0 in if s3 then false else true else false
      else false
    in
    if h
    then let seqYr = Sequent ((sL.fS a), y1) in
         let s1 =
           extSub2_fs eDf lf lL eDs ls sL r rA seqYr x y0 x1 y2 (sL.fS a) y1 a y false
         in
         let s2 =
           seqreps_map_concl eDf lf lL eDs ls sL false (sL.fS a) y
             (premsRule eDf lf lL eDs ls sL rA)
             (premsRule eDf lf lL eDs ls sL (ruleSubst eDf lf lL eDs ls sL s1 r))
             (let f = conclDT eDf lf lL eDs ls sL in
              let _,x2 = forallT_map f l in
              x2
                (let lemma = forallT_forall (eqDec_dertree eDf lf lL eDs ls sL) l in
                 flip2 (Obj.magic (fun _ _ -> iffT_flip_arrow_subrelation)) __ __ lemma
                   (let iH0 =
                      let lemma0 = forallT_forall (eqDec_dertree eDf lf lL eDs ls sL) l
                      in
                      iffT_arrow_subrelation (Obj.magic lemma0) (Obj.magic iH)
                    in
                    fun x3 _ t _ -> Obj.magic iH0 x3 __ __ __ t __)))
         in
         Der (seqY0, (cUT eDf lf lL eDs ls sL), (dtAY::((Der (seqYr, r, s2))::[])))
    else let s1 = extSub2_fs eDf lf lL eDs ls sL r rA seqY0 x y0 x1 y2 x0 y1 a y false
         in
         let rsubY = ruleSubst eDf lf lL eDs ls sL s1 r in
         let s2 =
           seqreps_map_concl eDf lf lL eDs ls sL false (sL.fS a) y
             (premsRule eDf lf lL eDs ls sL rA) (premsRule eDf lf lL eDs ls sL rsubY)
             (let f = conclDT eDf lf lL eDs ls sL in
              let _,x2 = forallT_map f l in
              x2
                (let lemma = forallT_forall (eqDec_dertree eDf lf lL eDs ls sL) l in
                 flip2 (Obj.magic (fun _ _ -> iffT_flip_arrow_subrelation)) __ __ lemma
                   (let iH0 =
                      let lemma0 = forallT_forall (eqDec_dertree eDf lf lL eDs ls sL) l
                      in
                      iffT_arrow_subrelation (Obj.magic lemma0) (Obj.magic iH)
                    in
                    fun x3 _ t _ -> Obj.magic iH0 x3 __ __ __ t __)))
         in
         Der (seqY0, r, s2)) dtA __ __ seqY __

(** val allLRP :
    'a1 eqDec -> 'a1 fLANG -> 'a1 lOGLANG -> 'a2 eqDec -> 'a2 fLANG -> ('a1, 'a2)
    sTRLANG -> ('a1, 'a2) dISPCALC -> ('a1, 'a2) bELNAP -> ('a1, 'a2) dertree -> 'a1 ->
    ('a1, 'a2) dertree **)

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
  ('formula, 'structr) dertree -> __ -> __ -> __ -> ('formula, 'structr) dertree

type ('formula, 'structr) canElimAll =
  ('formula, 'structr) dertree -> __ -> __ -> ('formula, 'structr) dertree

(** val canElim_canElimAll :
    'a1 eqDec -> 'a1 fLANG -> 'a1 lOGLANG -> 'a2 eqDec -> 'a2 fLANG -> ('a1, 'a2)
    sTRLANG -> ('a1, 'a2) dISPCALC -> ('a1, 'a2) canElim -> ('a1, 'a2) dertree -> ('a1,
    'a2) dertree **)

let canElim_canElimAll eDf lf lL eDs ls sL _ helim dt =
  dertree_rect_gen eDf lf lL eDs ls sL ForallT_nil (fun t l pt pl -> ForallT_cons (t,
    l, pt, pl)) (fun _ _ -> assert false (* absurd case *)) (fun s r l iH _ _ ->
    let x = fun l0 ->
      let x,_ = forall_ForallT (eqDec_dertree eDf lf lL eDs ls sL) l0 in Obj.magic x
    in
    let hvalup = x l __ in
    let x0 = fun l0 ->
      let x0,_ = forall_ForallT (eqDec_dertree eDf lf lL eDs ls sL) l0 in Obj.magic x0
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
    'a1 eqDec -> 'a1 fLANG -> 'a1 lOGLANG -> 'a2 eqDec -> 'a2 fLANG -> ('a1, 'a2)
    sTRLANG -> ('a1, 'a2) dISPCALC -> ('a1, 'a2) canElim -> ('a1, 'a2) dertree -> ('a1,
    'a2) dertree **)

let elimFmls =
  canElim_canElimAll

type ('formula, 'structr) canElimRaw =
  ('formula, 'structr) dertree -> __ -> __ -> ('formula, 'structr) dertree

type ('formula, 'structr) canElimAllRaw =
  ('formula, 'structr) dertree -> __ -> ('formula, 'structr) dertree

(** val canElim_cutOnFull_iff :
    'a1 eqDec -> 'a1 fLANG -> 'a1 lOGLANG -> 'a2 eqDec -> 'a2 fLANG -> ('a1, 'a2)
    sTRLANG -> ('a1, 'a2) dISPCALC -> (('a1, 'a2) canElimRaw, ('a1, 'a2) canElim) iffT0 **)

let canElim_cutOnFull_iff _ _ _ _ _ _ _ =
  (fun h dt _ _ _ -> h dt __ __),(fun h dt _ _ -> h dt __ __ __)

(** val canElimAll_cutOnFull_iff :
    'a1 eqDec -> 'a1 fLANG -> 'a1 lOGLANG -> 'a2 eqDec -> 'a2 fLANG -> ('a1, 'a2)
    sTRLANG -> ('a1, 'a2) dISPCALC -> (('a1, 'a2) canElimAllRaw, ('a1, 'a2) canElimAll)
    iffT0 **)

let canElimAll_cutOnFull_iff _ _ _ _ _ _ _ =
  (fun h dt _ _ -> h dt __),(fun h dt _ -> h dt __ __)

(** val canElim_ex :
    'a1 eqDec -> 'a1 fLANG -> 'a1 lOGLANG -> 'a2 eqDec -> 'a2 fLANG -> ('a1, 'a2)
    sTRLANG -> ('a1, 'a2) dISPCALC -> ('a3 -> ('a1, 'a2) canElim) -> ('a1, 'a2) dertree
    -> 'a3 -> ('a1, 'a2) dertree **)

let canElim_ex _ _ _ _ _ _ _ helim dt x =
  helim x dt __ __ __

(** val cutOnFmls_Full :
    'a1 eqDec -> 'a1 fLANG -> 'a1 lOGLANG -> 'a2 eqDec -> 'a2 fLANG -> ('a1, 'a2)
    sTRLANG -> ('a1, 'a2) dertree -> 'a1 **)

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
    'a1 eqDec -> 'a1 fLANG -> 'a1 lOGLANG -> 'a2 eqDec -> 'a2 fLANG -> ('a1, 'a2)
    sTRLANG -> ('a1, 'a2) dISPCALC -> ('a1 -> __ -> ('a1, 'a2) canElim) -> ('a1, 'a2)
    dertree -> ('a1, 'a2) dertree **)

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
    'a1 eqDec -> 'a1 fLANG -> 'a1 lOGLANG -> 'a2 eqDec -> 'a2 fLANG -> ('a1, 'a2)
    sTRLANG -> ('a1, 'a2) dISPCALC -> 'a1 -> ('a1, 'a2) canElim -> ('a1, 'a2) dertree
    -> ('a1, 'a2) dertree **)

let elimLP eDf lf lL eDs ls sL dC _ x dt =
  canElim_canElimAll eDf lf lL eDs ls sL dC x dt

(** val elimLRP :
    'a1 eqDec -> 'a1 fLANG -> 'a1 lOGLANG -> 'a2 eqDec -> 'a2 fLANG -> ('a1, 'a2)
    sTRLANG -> ('a1, 'a2) dISPCALC -> 'a1 -> ('a1, 'a2) canElim -> ('a1, 'a2) dertree
    -> ('a1, 'a2) dertree **)

let elimLRP eDf lf lL eDs ls sL dC _ x dt =
  canElim_canElimAll eDf lf lL eDs ls sL dC x dt

(** val allLP' :
    'a1 eqDec -> 'a1 fLANG -> 'a1 lOGLANG -> 'a2 eqDec -> 'a2 fLANG -> ('a1, 'a2)
    sTRLANG -> ('a1, 'a2) dISPCALC -> ('a1, 'a2) bELNAP -> 'a1 -> ('a1, 'a2) canElimAll
    -> ('a1, 'a2) dertree -> ('a1, 'a2) dertree **)

let allLP' eDf lf lL eDs ls sL dC bP a helim dt =
  let s = allLP eDf lf lL eDs ls sL dC bP dt a in helim s __ __

(** val allLRP' :
    'a1 eqDec -> 'a1 fLANG -> 'a1 lOGLANG -> 'a2 eqDec -> 'a2 fLANG -> ('a1, 'a2)
    sTRLANG -> ('a1, 'a2) dISPCALC -> ('a1, 'a2) bELNAP -> 'a1 -> ('a1, 'a2) canElimAll
    -> ('a1, 'a2) dertree -> ('a1, 'a2) dertree **)

let allLRP' eDf lf lL eDs ls sL dC bP a helim dt =
  let s = allLRP eDf lf lL eDs ls sL dC bP dt a in helim s __ __

(** val th8 :
    'a1 eqDec -> 'a1 fLANG -> 'a1 lOGLANG -> 'a2 eqDec -> 'a2 fLANG -> ('a1, 'a2)
    sTRLANG -> ('a1, 'a2) dISPCALC -> ('a1, 'a2) bELNAP -> 'a1 -> ('a1, 'a2) canElim ->
    ('a1, 'a2) dertree -> ('a1, 'a2) dertree **)

let th8 eDf lf lL eDs ls sL dC bP a h dt =
  allLP' eDf lf lL eDs ls sL dC bP a (fun x _ _ ->
    elimLP eDf lf lL eDs ls sL dC a (fun x0 _ _ _ ->
      allLRP' eDf lf lL eDs ls sL dC bP a (fun x1 _ _ ->
        elimLRP eDf lf lL eDs ls sL dC a h x1) x0) x) dt

(** val allch :
    'a1 eqDec -> 'a1 fLANG -> 'a1 lOGLANG -> 'a2 eqDec -> 'a2 fLANG -> ('a1, 'a2)
    sTRLANG -> ('a1, 'a2) dISPCALC -> ('a1, 'a2) bELNAP -> 'a1 -> ('a1, 'a2) canElimAll
    -> ('a1, 'a2) dertree -> ('a1, 'a2) dertree **)

let allch eDf lf lL eDs ls sL dC bP a helim dt =
  let s = c8_holds eDf lf lL eDs ls sL dC bP a dt in helim s __ __

(** val th8ch' :
    'a1 eqDec -> 'a1 fLANG -> 'a1 lOGLANG -> 'a2 eqDec -> 'a2 fLANG -> ('a1, 'a2)
    sTRLANG -> ('a1, 'a2) dISPCALC -> ('a1, 'a2) bELNAP -> 'a1 -> ('a1 -> __ -> ('a1,
    'a2) canElim) -> ('a1, 'a2) dertree -> ('a1, 'a2) dertree **)

let th8ch' eDf lf lL eDs ls sL dC bP a h dt =
  th8 eDf lf lL eDs ls sL dC bP a (fun x _ _ _ ->
    allch eDf lf lL eDs ls sL dC bP a (fun x0 _ _ ->
      elimFmls eDf lf lL eDs ls sL dC (fun x1 _ _ _ ->
        allElim eDf lf lL eDs ls sL dC h x1) x0) x) dt

(** val canElimFml :
    'a1 eqDec -> 'a1 fLANG -> 'a1 lOGLANG -> 'a2 eqDec -> 'a2 fLANG -> ('a1, 'a2)
    sTRLANG -> ('a1, 'a2) dISPCALC -> ('a1, 'a2) bELNAP -> 'a1 -> ('a1, 'a2) dertree ->
    ('a1, 'a2) dertree **)

let canElimFml eDf lf lL eDs ls sL dC bP a dt =
  ipse_rect eDf lf (fun a0 x x0 _ _ _ -> th8ch' eDf lf lL eDs ls sL dC bP a0 x x0) a dt
    __ __ __

(** val c3458_canElimRaw :
    'a1 eqDec -> 'a1 fLANG -> 'a1 lOGLANG -> 'a2 eqDec -> 'a2 fLANG -> ('a1, 'a2)
    sTRLANG -> ('a1, 'a2) dISPCALC -> ('a1, 'a2) bELNAP -> ('a1, 'a2) dertree -> ('a1,
    'a2) dertree **)

let c3458_canElimRaw eDf lf lL eDs ls sL dC bP dt =
  let _,x = canElim_cutOnFull_iff eDf lf lL eDs ls sL dC in
  x (fun dt0 _ _ ->
    let hdt0 = cutOnFmls_Full eDf lf lL eDs ls sL dt0 in
    (fun _ ->
    canElim_ex eDf lf lL eDs ls sL dC (fun phi x0 _ _ _ ->
      canElimFml eDf lf lL eDs ls sL dC bP phi x0) dt0 hdt0)) dt __ __

(** val cav :
    'a1 eqDec -> 'a1 fLANG -> 'a1 lOGLANG -> 'a2 eqDec -> 'a2 fLANG -> ('a1, 'a2)
    sTRLANG -> ('a1, 'a2) dISPCALC -> ('a1, 'a2) bELNAP -> ('a1, 'a2) dertree -> ('a1,
    'a2) dertree **)

let cav eDf lf lL eDs ls sL dC bP dt =
  let x = fun x ->
    elimFmls eDf lf lL eDs ls sL dC
      (fst (canElim_cutOnFull_iff eDf lf lL eDs ls sL dC) (fun x0 _ _ ->
        c3458_canElimRaw eDf lf lL eDs ls sL dC bP x0)) x
  in
  let _,x0 = canElimAll_cutOnFull_iff eDf lf lL eDs ls sL dC in
  x0 (fun x1 _ _ -> x x1) dt __

(** val cutElim :
    'a1 eqDec -> 'a1 fLANG -> 'a1 lOGLANG -> 'a2 eqDec -> 'a2 fLANG -> ('a1, 'a2)
    sTRLANG -> ('a1, 'a2) dISPCALC -> ('a1, 'a2) bELNAP -> ('a1, 'a2) dertree -> ('a1,
    'a2) dertree **)

let cutElim =
  cav

(** val atrefl :
    'a1 eqDec -> 'a1 fLANG -> 'a1 lOGLANG -> 'a2 eqDec -> 'a2 fLANG -> ('a1, 'a2)
    sTRLANG -> ('a1, 'a2) rule **)

let atrefl _ _ lL _ _ sL =
  [],(Sequent ((sL.fS (lL.atm "p")), (sL.fS (lL.atm "p"))))

module Lambek =
 struct
  type formula =
  | Atf of string
  | FVf of string
  | Top
  | Bot
  | Dis of formula * formula
  | Con of formula * formula
  | One
  | Zer
  | Fus of formula * formula
  | Und of formula * formula
  | Ove of formula * formula

  (** val formula_rect :
      (string -> 'a1) -> (string -> 'a1) -> 'a1 -> 'a1 -> (formula -> 'a1 -> formula ->
      'a1 -> 'a1) -> (formula -> 'a1 -> formula -> 'a1 -> 'a1) -> 'a1 -> 'a1 ->
      (formula -> 'a1 -> formula -> 'a1 -> 'a1) -> (formula -> 'a1 -> formula -> 'a1 ->
      'a1) -> (formula -> 'a1 -> formula -> 'a1 -> 'a1) -> formula -> 'a1 **)

  let rec formula_rect f f0 f1 f2 f3 f4 f5 f6 f7 f8 f9 = function
  | Atf p -> f p
  | FVf a -> f0 a
  | Top -> f1
  | Bot -> f2
  | Dis (phi, psi) ->
    f3 phi (formula_rect f f0 f1 f2 f3 f4 f5 f6 f7 f8 f9 phi) psi
      (formula_rect f f0 f1 f2 f3 f4 f5 f6 f7 f8 f9 psi)
  | Con (phi, psi) ->
    f4 phi (formula_rect f f0 f1 f2 f3 f4 f5 f6 f7 f8 f9 phi) psi
      (formula_rect f f0 f1 f2 f3 f4 f5 f6 f7 f8 f9 psi)
  | One -> f5
  | Zer -> f6
  | Fus (phi, psi) ->
    f7 phi (formula_rect f f0 f1 f2 f3 f4 f5 f6 f7 f8 f9 phi) psi
      (formula_rect f f0 f1 f2 f3 f4 f5 f6 f7 f8 f9 psi)
  | Und (phi, psi) ->
    f8 phi (formula_rect f f0 f1 f2 f3 f4 f5 f6 f7 f8 f9 phi) psi
      (formula_rect f f0 f1 f2 f3 f4 f5 f6 f7 f8 f9 psi)
  | Ove (phi, psi) ->
    f9 phi (formula_rect f f0 f1 f2 f3 f4 f5 f6 f7 f8 f9 phi) psi
      (formula_rect f f0 f1 f2 f3 f4 f5 f6 f7 f8 f9 psi)

  (** val formula_rec :
      (string -> 'a1) -> (string -> 'a1) -> 'a1 -> 'a1 -> (formula -> 'a1 -> formula ->
      'a1 -> 'a1) -> (formula -> 'a1 -> formula -> 'a1 -> 'a1) -> 'a1 -> 'a1 ->
      (formula -> 'a1 -> formula -> 'a1 -> 'a1) -> (formula -> 'a1 -> formula -> 'a1 ->
      'a1) -> (formula -> 'a1 -> formula -> 'a1 -> 'a1) -> formula -> 'a1 **)

  let rec formula_rec f f0 f1 f2 f3 f4 f5 f6 f7 f8 f9 = function
  | Atf p -> f p
  | FVf a -> f0 a
  | Top -> f1
  | Bot -> f2
  | Dis (phi, psi) ->
    f3 phi (formula_rec f f0 f1 f2 f3 f4 f5 f6 f7 f8 f9 phi) psi
      (formula_rec f f0 f1 f2 f3 f4 f5 f6 f7 f8 f9 psi)
  | Con (phi, psi) ->
    f4 phi (formula_rec f f0 f1 f2 f3 f4 f5 f6 f7 f8 f9 phi) psi
      (formula_rec f f0 f1 f2 f3 f4 f5 f6 f7 f8 f9 psi)
  | One -> f5
  | Zer -> f6
  | Fus (phi, psi) ->
    f7 phi (formula_rec f f0 f1 f2 f3 f4 f5 f6 f7 f8 f9 phi) psi
      (formula_rec f f0 f1 f2 f3 f4 f5 f6 f7 f8 f9 psi)
  | Und (phi, psi) ->
    f8 phi (formula_rec f f0 f1 f2 f3 f4 f5 f6 f7 f8 f9 phi) psi
      (formula_rec f f0 f1 f2 f3 f4 f5 f6 f7 f8 f9 psi)
  | Ove (phi, psi) ->
    f9 phi (formula_rec f f0 f1 f2 f3 f4 f5 f6 f7 f8 f9 phi) psi
      (formula_rec f f0 f1 f2 f3 f4 f5 f6 f7 f8 f9 psi)

  type structr =
  | SVf of string
  | FSf of formula
  | I
  | Coq__UU03a6_
  | Smc of structr * structr
  | Gre of structr * structr
  | Les of structr * structr

  (** val structr_rect :
      (string -> 'a1) -> (formula -> 'a1) -> 'a1 -> 'a1 -> (structr -> 'a1 -> structr
      -> 'a1 -> 'a1) -> (structr -> 'a1 -> structr -> 'a1 -> 'a1) -> (structr -> 'a1 ->
      structr -> 'a1 -> 'a1) -> structr -> 'a1 **)

  let rec structr_rect f f0 f1 f2 f3 f4 f5 = function
  | SVf x -> f x
  | FSf a -> f0 a
  | I -> f1
  | Coq__UU03a6_ -> f2
  | Smc (x, y) ->
    f3 x (structr_rect f f0 f1 f2 f3 f4 f5 x) y (structr_rect f f0 f1 f2 f3 f4 f5 y)
  | Gre (x, y) ->
    f4 x (structr_rect f f0 f1 f2 f3 f4 f5 x) y (structr_rect f f0 f1 f2 f3 f4 f5 y)
  | Les (x, y) ->
    f5 x (structr_rect f f0 f1 f2 f3 f4 f5 x) y (structr_rect f f0 f1 f2 f3 f4 f5 y)

  (** val structr_rec :
      (string -> 'a1) -> (formula -> 'a1) -> 'a1 -> 'a1 -> (structr -> 'a1 -> structr
      -> 'a1 -> 'a1) -> (structr -> 'a1 -> structr -> 'a1 -> 'a1) -> (structr -> 'a1 ->
      structr -> 'a1 -> 'a1) -> structr -> 'a1 **)

  let rec structr_rec f f0 f1 f2 f3 f4 f5 = function
  | SVf x -> f x
  | FSf a -> f0 a
  | I -> f1
  | Coq__UU03a6_ -> f2
  | Smc (x, y) ->
    f3 x (structr_rec f f0 f1 f2 f3 f4 f5 x) y (structr_rec f f0 f1 f2 f3 f4 f5 y)
  | Gre (x, y) ->
    f4 x (structr_rec f f0 f1 f2 f3 f4 f5 x) y (structr_rec f f0 f1 f2 f3 f4 f5 y)
  | Les (x, y) ->
    f5 x (structr_rec f f0 f1 f2 f3 f4 f5 x) y (structr_rec f f0 f1 f2 f3 f4 f5 y)
 end

module Lambek_LOG =
 struct
  (** val fml_eq_dec : Lambek.formula eq_dec **)

  let rec fml_eq_dec f x0 =
    match f with
    | Lambek.Atf p -> (match x0 with
                       | Lambek.Atf p0 -> (=) p p0
                       | _ -> false)
    | Lambek.FVf a -> (match x0 with
                       | Lambek.FVf a0 -> (=) a a0
                       | _ -> false)
    | Lambek.Top -> (match x0 with
                     | Lambek.Top -> true
                     | _ -> false)
    | Lambek.Bot -> (match x0 with
                     | Lambek.Bot -> true
                     | _ -> false)
    | Lambek.Dis (phi, psi) ->
      (match x0 with
       | Lambek.Dis (phi0, psi0) ->
         if fml_eq_dec phi phi0 then fml_eq_dec psi psi0 else false
       | _ -> false)
    | Lambek.Con (phi, psi) ->
      (match x0 with
       | Lambek.Con (phi0, psi0) ->
         if fml_eq_dec phi phi0 then fml_eq_dec psi psi0 else false
       | _ -> false)
    | Lambek.One -> (match x0 with
                     | Lambek.One -> true
                     | _ -> false)
    | Lambek.Zer -> (match x0 with
                     | Lambek.Zer -> true
                     | _ -> false)
    | Lambek.Fus (phi, psi) ->
      (match x0 with
       | Lambek.Fus (phi0, psi0) ->
         if fml_eq_dec phi phi0 then fml_eq_dec psi psi0 else false
       | _ -> false)
    | Lambek.Und (phi, psi) ->
      (match x0 with
       | Lambek.Und (phi0, psi0) ->
         if fml_eq_dec phi phi0 then fml_eq_dec psi psi0 else false
       | _ -> false)
    | Lambek.Ove (phi, psi) ->
      (match x0 with
       | Lambek.Ove (phi0, psi0) ->
         if fml_eq_dec phi phi0 then fml_eq_dec psi psi0 else false
       | _ -> false)

  (** val ipse : Lambek.formula -> Lambek.formula list **)

  let ipse = function
  | Lambek.Dis (a1, a2) -> a1::(a2::[])
  | Lambek.Con (a1, a2) -> a1::(a2::[])
  | Lambek.Fus (a1, a2) -> a1::(a2::[])
  | Lambek.Und (a1, a2) -> a1::(a2::[])
  | Lambek.Ove (a1, a2) -> a1::(a2::[])
  | _ -> []

  (** val ipse_rect :
      (Lambek.formula -> (Lambek.formula -> __ -> 'a1) -> 'a1) -> Lambek.formula -> 'a1 **)

  let rec ipse_rect h = function
  | Lambek.Dis (phi, psi) ->
    h (Lambek.Dis (phi, psi)) (fun b _ ->
      let s = fml_eq_dec b phi in
      if s
      then ipse_rect h phi
      else let s0 = fml_eq_dec b psi in
           if s0 then ipse_rect h psi else assert false (* absurd case *))
  | Lambek.Con (phi, psi) ->
    h (Lambek.Con (phi, psi)) (fun b _ ->
      let s = fml_eq_dec b phi in
      if s
      then ipse_rect h phi
      else let s0 = fml_eq_dec b psi in
           if s0 then ipse_rect h psi else assert false (* absurd case *))
  | Lambek.Fus (phi, psi) ->
    h (Lambek.Fus (phi, psi)) (fun b _ ->
      let s = fml_eq_dec b phi in
      if s
      then ipse_rect h phi
      else let s0 = fml_eq_dec b psi in
           if s0 then ipse_rect h psi else assert false (* absurd case *))
  | Lambek.Und (phi, psi) ->
    h (Lambek.Und (phi, psi)) (fun b _ ->
      let s = fml_eq_dec b phi in
      if s
      then ipse_rect h phi
      else let s0 = fml_eq_dec b psi in
           if s0 then ipse_rect h psi else assert false (* absurd case *))
  | Lambek.Ove (phi, psi) ->
    h (Lambek.Ove (phi, psi)) (fun b _ ->
      let s = fml_eq_dec b phi in
      if s
      then ipse_rect h phi
      else let s0 = fml_eq_dec b psi in
           if s0 then ipse_rect h psi else assert false (* absurd case *))
  | x -> h x (fun _ _ -> assert false (* absurd case *))

  (** val fml_df : Lambek.formula **)

  let fml_df =
    Lambek.Atf ""

  (** val conn : Lambek.formula -> Lambek.formula list -> Lambek.formula **)

  let conn a x =
    match a with
    | Lambek.Dis (_, _) ->
      (match x with
       | [] -> fml_df
       | b1::l0 -> (match l0 with
                    | [] -> fml_df
                    | b2::_ -> Lambek.Dis (b1, b2)))
    | Lambek.Con (_, _) ->
      (match x with
       | [] -> fml_df
       | b1::l0 -> (match l0 with
                    | [] -> fml_df
                    | b2::_ -> Lambek.Con (b1, b2)))
    | Lambek.Fus (_, _) ->
      (match x with
       | [] -> fml_df
       | b1::l0 -> (match l0 with
                    | [] -> fml_df
                    | b2::_ -> Lambek.Fus (b1, b2)))
    | Lambek.Und (_, _) ->
      (match x with
       | [] -> fml_df
       | b1::l0 -> (match l0 with
                    | [] -> fml_df
                    | b2::_ -> Lambek.Und (b1, b2)))
    | Lambek.Ove (_, _) ->
      (match x with
       | [] -> fml_df
       | b1::l0 -> (match l0 with
                    | [] -> fml_df
                    | b2::_ -> Lambek.Ove (b1, b2)))
    | _ -> a

  (** val coq_Atm_dec : Lambek.formula -> string option **)

  let coq_Atm_dec = function
  | Lambek.Atf p -> Some p
  | _ -> None

  (** val coq_FV_dec : Lambek.formula -> string option **)

  let coq_FV_dec = function
  | Lambek.FVf a0 -> Some a0
  | _ -> None
 end

(** val eqDec_formula : Lambek.formula eqDec **)

let eqDec_formula =
  Lambek_LOG.fml_eq_dec

(** val f_Lambek_log : Lambek.formula fLANG **)

let f_Lambek_log =
  { ipse = Lambek_LOG.ipse; ipse_rect = (fun _ -> Lambek_LOG.ipse_rect); conn =
    Lambek_LOG.conn }

(** val lambek_Atm : (Lambek.formula, string) iXEXP **)

let lambek_Atm =
  Lambek_LOG.coq_Atm_dec

(** val lambek_FV : (Lambek.formula, string) iXEXP **)

let lambek_FV =
  Lambek_LOG.coq_FV_dec

(** val lambek_log : Lambek.formula lOGLANG **)

let lambek_log =
  { atm = (fun x -> Lambek.Atf x); fV = (fun x -> Lambek.FVf x); aTMVAR = lambek_Atm;
    fVVAR = lambek_FV }

module Lambek_STR =
 struct
  (** val str_eq_dec : Lambek.structr eq_dec **)

  let rec str_eq_dec s x0 =
    match s with
    | Lambek.SVf x ->
      (match x0 with
       | Lambek.SVf x1 -> eqdec eqDec_string x x1
       | _ -> false)
    | Lambek.FSf a ->
      (match x0 with
       | Lambek.FSf a0 -> eqdec eqDec_formula a a0
       | _ -> false)
    | Lambek.I -> (match x0 with
                   | Lambek.I -> true
                   | _ -> false)
    | Lambek.Coq__UU03a6_ -> (match x0 with
                              | Lambek.Coq__UU03a6_ -> true
                              | _ -> false)
    | Lambek.Smc (x, y) ->
      (match x0 with
       | Lambek.Smc (x1, y0) -> if str_eq_dec x x1 then str_eq_dec y y0 else false
       | _ -> false)
    | Lambek.Gre (x, y) ->
      (match x0 with
       | Lambek.Gre (x1, y0) -> if str_eq_dec x x1 then str_eq_dec y y0 else false
       | _ -> false)
    | Lambek.Les (x, y) ->
      (match x0 with
       | Lambek.Les (x1, y0) -> if str_eq_dec x x1 then str_eq_dec y y0 else false
       | _ -> false)

  (** val ipse : Lambek.structr -> Lambek.structr list **)

  let ipse = function
  | Lambek.Smc (x1, x2) -> x1::(x2::[])
  | Lambek.Gre (x1, x2) -> x1::(x2::[])
  | Lambek.Les (x1, x2) -> x1::(x2::[])
  | _ -> []

  (** val ipse_rect :
      (Lambek.structr -> (Lambek.structr -> __ -> 'a1) -> 'a1) -> Lambek.structr -> 'a1 **)

  let rec ipse_rect h = function
  | Lambek.Smc (x, y) ->
    h (Lambek.Smc (x, y)) (fun b _ ->
      let s = str_eq_dec b x in
      if s
      then ipse_rect h x
      else let s0 = str_eq_dec b y in
           if s0 then ipse_rect h y else assert false (* absurd case *))
  | Lambek.Gre (x, y) ->
    h (Lambek.Gre (x, y)) (fun b _ ->
      let s = str_eq_dec b x in
      if s
      then ipse_rect h x
      else let s0 = str_eq_dec b y in
           if s0 then ipse_rect h y else assert false (* absurd case *))
  | Lambek.Les (x, y) ->
    h (Lambek.Les (x, y)) (fun b _ ->
      let s = str_eq_dec b x in
      if s
      then ipse_rect h x
      else let s0 = str_eq_dec b y in
           if s0 then ipse_rect h y else assert false (* absurd case *))
  | x -> h x (fun _ _ -> assert false (* absurd case *))

  (** val str_df : Lambek.structr **)

  let str_df =
    Lambek.SVf ""

  (** val conn : Lambek.structr -> Lambek.structr list -> Lambek.structr **)

  let conn x x0 =
    match x with
    | Lambek.Smc (_, _) ->
      (match x0 with
       | [] -> str_df
       | y1::l0 -> (match l0 with
                    | [] -> str_df
                    | y2::_ -> Lambek.Smc (y1, y2)))
    | Lambek.Gre (_, _) ->
      (match x0 with
       | [] -> str_df
       | y1::l0 -> (match l0 with
                    | [] -> str_df
                    | y2::_ -> Lambek.Gre (y1, y2)))
    | Lambek.Les (_, _) ->
      (match x0 with
       | [] -> str_df
       | y1::l0 -> (match l0 with
                    | [] -> str_df
                    | y2::_ -> Lambek.Les (y1, y2)))
    | _ -> x

  (** val coq_SV_dec : Lambek.structr -> string option **)

  let coq_SV_dec = function
  | Lambek.SVf x0 -> Some x0
  | _ -> None

  (** val coq_FS_dec : Lambek.structr -> Lambek.formula option **)

  let coq_FS_dec = function
  | Lambek.FSf a -> Some a
  | _ -> None

  (** val sgnips : Lambek.structr -> bool list **)

  let sgnips = function
  | Lambek.Smc (_, _) -> true::(true::[])
  | Lambek.Gre (_, _) -> false::(true::[])
  | Lambek.Les (_, _) -> true::(false::[])
  | _ -> []
 end

(** val eqDec_structr : Lambek.structr eqDec **)

let eqDec_structr =
  Lambek_STR.str_eq_dec

(** val f_Lambek : Lambek.structr fLANG **)

let f_Lambek =
  { ipse = Lambek_STR.ipse; ipse_rect = (fun _ -> Lambek_STR.ipse_rect); conn =
    Lambek_STR.conn }

(** val lambek_SV : (Lambek.structr, string) iXEXP **)

let lambek_SV =
  Lambek_STR.coq_SV_dec

(** val lambek_FS : (Lambek.structr, Lambek.formula) iXEXP **)

let lambek_FS =
  Lambek_STR.coq_FS_dec

(** val lambek_str : (Lambek.formula, Lambek.structr) sTRLANG **)

let lambek_str =
  { sV = (fun x -> Lambek.SVf x); fS = (fun x -> Lambek.FSf x); sVVAR = lambek_SV;
    fSVAR = lambek_FS; sgnips = Lambek_STR.sgnips }

module LambekRules =
 struct
  (** val coq_Topl : (Lambek.formula, Lambek.structr) rule **)

  let coq_Topl =
    ((Sequent (Lambek.I, (Lambek.SVf "X")))::[]),(Sequent ((Lambek.FSf Lambek.Top),
      (Lambek.SVf "X")))

  (** val coq_Topr : (Lambek.formula, Lambek.structr) rule **)

  let coq_Topr =
    [],(Sequent (Lambek.I, (Lambek.FSf Lambek.Top)))

  (** val coq_Botl : (Lambek.formula, Lambek.structr) rule **)

  let coq_Botl =
    [],(Sequent ((Lambek.FSf Lambek.Bot), Lambek.I))

  (** val coq_Botr : (Lambek.formula, Lambek.structr) rule **)

  let coq_Botr =
    ((Sequent ((Lambek.SVf "X"), Lambek.I))::[]),(Sequent ((Lambek.SVf "X"),
      (Lambek.FSf Lambek.Bot)))

  (** val coq_Conll : (Lambek.formula, Lambek.structr) rule **)

  let coq_Conll =
    ((Sequent ((Lambek.FSf (Lambek.FVf "A")), (Lambek.SVf "X")))::[]),(Sequent
      ((Lambek.FSf (Lambek.Con ((Lambek.FVf "A"), (Lambek.FVf "B")))), (Lambek.SVf
      "X")))

  (** val coq_Conlr : (Lambek.formula, Lambek.structr) rule **)

  let coq_Conlr =
    ((Sequent ((Lambek.FSf (Lambek.FVf "B")), (Lambek.SVf "X")))::[]),(Sequent
      ((Lambek.FSf (Lambek.Con ((Lambek.FVf "A"), (Lambek.FVf "B")))), (Lambek.SVf
      "X")))

  (** val coq_Conr : (Lambek.formula, Lambek.structr) rule **)

  let coq_Conr =
    ((Sequent ((Lambek.SVf "X"), (Lambek.FSf (Lambek.FVf "A"))))::((Sequent
      ((Lambek.SVf "X"), (Lambek.FSf (Lambek.FVf "B"))))::[])),(Sequent ((Lambek.SVf
      "X"), (Lambek.FSf (Lambek.Con ((Lambek.FVf "A"), (Lambek.FVf "B"))))))

  (** val coq_Disl : (Lambek.formula, Lambek.structr) rule **)

  let coq_Disl =
    ((Sequent ((Lambek.FSf (Lambek.FVf "A")), (Lambek.SVf "X")))::((Sequent
      ((Lambek.FSf (Lambek.FVf "B")), (Lambek.SVf "X")))::[])),(Sequent ((Lambek.FSf
      (Lambek.Dis ((Lambek.FVf "A"), (Lambek.FVf "B")))), (Lambek.SVf "X")))

  (** val coq_Disrl : (Lambek.formula, Lambek.structr) rule **)

  let coq_Disrl =
    ((Sequent ((Lambek.SVf "X"), (Lambek.FSf (Lambek.FVf "A"))))::[]),(Sequent
      ((Lambek.SVf "X"), (Lambek.FSf (Lambek.Dis ((Lambek.FVf "A"), (Lambek.FVf
      "B"))))))

  (** val coq_Disrr : (Lambek.formula, Lambek.structr) rule **)

  let coq_Disrr =
    ((Sequent ((Lambek.SVf "X"), (Lambek.FSf (Lambek.FVf "B"))))::[]),(Sequent
      ((Lambek.SVf "X"), (Lambek.FSf (Lambek.Dis ((Lambek.FVf "A"), (Lambek.FVf
      "B"))))))

  (** val coq_Onel : (Lambek.formula, Lambek.structr) rule **)

  let coq_Onel =
    ((Sequent (Lambek.Coq__UU03a6_, (Lambek.SVf "X")))::[]),(Sequent ((Lambek.FSf
      Lambek.One), (Lambek.SVf "X")))

  (** val coq_Oner : (Lambek.formula, Lambek.structr) rule **)

  let coq_Oner =
    [],(Sequent (Lambek.Coq__UU03a6_, (Lambek.FSf Lambek.One)))

  (** val coq_Zerl : (Lambek.formula, Lambek.structr) rule **)

  let coq_Zerl =
    [],(Sequent ((Lambek.FSf Lambek.Zer), Lambek.Coq__UU03a6_))

  (** val coq_Zerr : (Lambek.formula, Lambek.structr) rule **)

  let coq_Zerr =
    ((Sequent ((Lambek.SVf "X"), Lambek.Coq__UU03a6_))::[]),(Sequent ((Lambek.SVf "X"),
      (Lambek.FSf Lambek.Zer)))

  (** val coq_Fusl : (Lambek.formula, Lambek.structr) rule **)

  let coq_Fusl =
    ((Sequent ((Lambek.Smc ((Lambek.FSf (Lambek.FVf "A")), (Lambek.FSf (Lambek.FVf
      "B")))), (Lambek.SVf "X")))::[]),(Sequent ((Lambek.FSf (Lambek.Fus ((Lambek.FVf
      "A"), (Lambek.FVf "B")))), (Lambek.SVf "X")))

  (** val coq_Fusr : (Lambek.formula, Lambek.structr) rule **)

  let coq_Fusr =
    ((Sequent ((Lambek.SVf "X"), (Lambek.FSf (Lambek.FVf "A"))))::((Sequent
      ((Lambek.SVf "Y"), (Lambek.FSf (Lambek.FVf "B"))))::[])),(Sequent ((Lambek.Smc
      ((Lambek.SVf "X"), (Lambek.SVf "Y"))), (Lambek.FSf (Lambek.Fus ((Lambek.FVf "A"),
      (Lambek.FVf "B"))))))

  (** val coq_Undl : (Lambek.formula, Lambek.structr) rule **)

  let coq_Undl =
    ((Sequent ((Lambek.SVf "X"), (Lambek.FSf (Lambek.FVf "A"))))::((Sequent
      ((Lambek.FSf (Lambek.FVf "B")), (Lambek.SVf "Y")))::[])),(Sequent ((Lambek.FSf
      (Lambek.Und ((Lambek.FVf "A"), (Lambek.FVf "B")))), (Lambek.Gre ((Lambek.SVf
      "X"), (Lambek.SVf "Y")))))

  (** val coq_Undr : (Lambek.formula, Lambek.structr) rule **)

  let coq_Undr =
    ((Sequent ((Lambek.SVf "X"), (Lambek.Gre ((Lambek.FSf (Lambek.FVf "A")),
      (Lambek.FSf (Lambek.FVf "B"))))))::[]),(Sequent ((Lambek.SVf "X"), (Lambek.FSf
      (Lambek.Und ((Lambek.FVf "A"), (Lambek.FVf "B"))))))

  (** val coq_Ovel : (Lambek.formula, Lambek.structr) rule **)

  let coq_Ovel =
    ((Sequent ((Lambek.FSf (Lambek.FVf "A")), (Lambek.SVf "X")))::((Sequent
      ((Lambek.SVf "Y"), (Lambek.FSf (Lambek.FVf "B"))))::[])),(Sequent ((Lambek.FSf
      (Lambek.Ove ((Lambek.FVf "A"), (Lambek.FVf "B")))), (Lambek.Les ((Lambek.SVf
      "X"), (Lambek.SVf "Y")))))

  (** val coq_Over : (Lambek.formula, Lambek.structr) rule **)

  let coq_Over =
    ((Sequent ((Lambek.SVf "X"), (Lambek.Les ((Lambek.FSf (Lambek.FVf "A")),
      (Lambek.FSf (Lambek.FVf "B"))))))::[]),(Sequent ((Lambek.SVf "X"), (Lambek.FSf
      (Lambek.Ove ((Lambek.FVf "A"), (Lambek.FVf "B"))))))

  (** val coq_Iwl : (Lambek.formula, Lambek.structr) rule **)

  let coq_Iwl =
    ((Sequent (Lambek.I, (Lambek.SVf "Y")))::[]),(Sequent ((Lambek.SVf "X"),
      (Lambek.SVf "Y")))

  (** val coq_Iwr : (Lambek.formula, Lambek.structr) rule **)

  let coq_Iwr =
    ((Sequent ((Lambek.SVf "X"), Lambek.I))::[]),(Sequent ((Lambek.SVf "X"),
      (Lambek.SVf "Y")))

  (** val _UU03a6_addll : (Lambek.formula, Lambek.structr) rule **)

  let _UU03a6_addll =
    ((Sequent ((Lambek.SVf "X"), (Lambek.SVf "Y")))::[]),(Sequent ((Lambek.Smc
      (Lambek.Coq__UU03a6_, (Lambek.SVf "X"))), (Lambek.SVf "Y")))

  (** val _UU03a6_addlr : (Lambek.formula, Lambek.structr) rule **)

  let _UU03a6_addlr =
    ((Sequent ((Lambek.SVf "X"), (Lambek.SVf "Y")))::[]),(Sequent ((Lambek.Smc
      ((Lambek.SVf "X"), Lambek.Coq__UU03a6_)), (Lambek.SVf "Y")))

  (** val _UU03a6_addrl : (Lambek.formula, Lambek.structr) rule **)

  let _UU03a6_addrl =
    ((Sequent ((Lambek.SVf "X"), (Lambek.SVf "Y")))::[]),(Sequent ((Lambek.SVf "X"),
      (Lambek.Smc (Lambek.Coq__UU03a6_, (Lambek.SVf "Y")))))

  (** val _UU03a6_addrr : (Lambek.formula, Lambek.structr) rule **)

  let _UU03a6_addrr =
    ((Sequent ((Lambek.SVf "X"), (Lambek.SVf "Y")))::[]),(Sequent ((Lambek.SVf "X"),
      (Lambek.Smc ((Lambek.SVf "Y"), Lambek.Coq__UU03a6_))))

  (** val _UU03a6_delll : (Lambek.formula, Lambek.structr) rule **)

  let _UU03a6_delll =
    ((Sequent ((Lambek.Smc (Lambek.Coq__UU03a6_, (Lambek.SVf "X"))), (Lambek.SVf
      "Y")))::[]),(Sequent ((Lambek.SVf "X"), (Lambek.SVf "Y")))

  (** val _UU03a6_dellr : (Lambek.formula, Lambek.structr) rule **)

  let _UU03a6_dellr =
    ((Sequent ((Lambek.Smc ((Lambek.SVf "X"), Lambek.Coq__UU03a6_)), (Lambek.SVf
      "Y")))::[]),(Sequent ((Lambek.SVf "X"), (Lambek.SVf "Y")))

  (** val _UU03a6_delrl : (Lambek.formula, Lambek.structr) rule **)

  let _UU03a6_delrl =
    ((Sequent ((Lambek.SVf "X"), (Lambek.Smc (Lambek.Coq__UU03a6_, (Lambek.SVf
      "Y")))))::[]),(Sequent ((Lambek.SVf "X"), (Lambek.SVf "Y")))

  (** val _UU03a6_delrr : (Lambek.formula, Lambek.structr) rule **)

  let _UU03a6_delrr =
    ((Sequent ((Lambek.SVf "X"), (Lambek.Smc ((Lambek.SVf "Y"),
      Lambek.Coq__UU03a6_))))::[]),(Sequent ((Lambek.SVf "X"), (Lambek.SVf "Y")))

  (** val coq_Rlesmr : (Lambek.formula, Lambek.structr) rule **)

  let coq_Rlesmr =
    ((Sequent ((Lambek.SVf "X"), (Lambek.Les ((Lambek.SVf "Y"), (Lambek.SVf
      "Z")))))::[]),(Sequent ((Lambek.Smc ((Lambek.SVf "X"), (Lambek.SVf "Z"))),
      (Lambek.SVf "Y")))

  (** val coq_Rsmgel : (Lambek.formula, Lambek.structr) rule **)

  let coq_Rsmgel =
    ((Sequent ((Lambek.Smc ((Lambek.SVf "X"), (Lambek.SVf "Y"))), (Lambek.SVf
      "Z")))::[]),(Sequent ((Lambek.SVf "Y"), (Lambek.Gre ((Lambek.SVf "X"),
      (Lambek.SVf "Z")))))

  (** val coq_Rgesmr : (Lambek.formula, Lambek.structr) rule **)

  let coq_Rgesmr =
    ((Sequent ((Lambek.SVf "X"), (Lambek.Gre ((Lambek.SVf "Y"), (Lambek.SVf
      "Z")))))::[]),(Sequent ((Lambek.Smc ((Lambek.SVf "Y"), (Lambek.SVf "X"))),
      (Lambek.SVf "Z")))

  (** val coq_Rsmlel : (Lambek.formula, Lambek.structr) rule **)

  let coq_Rsmlel =
    ((Sequent ((Lambek.Smc ((Lambek.SVf "X"), (Lambek.SVf "Y"))), (Lambek.SVf
      "Z")))::[]),(Sequent ((Lambek.SVf "X"), (Lambek.Les ((Lambek.SVf "Z"),
      (Lambek.SVf "Y")))))

  (** val coq_Rlesml : (Lambek.formula, Lambek.structr) rule **)

  let coq_Rlesml =
    ((Sequent ((Lambek.Les ((Lambek.SVf "X"), (Lambek.SVf "Y"))), (Lambek.SVf
      "Z")))::[]),(Sequent ((Lambek.SVf "X"), (Lambek.Smc ((Lambek.SVf "Z"),
      (Lambek.SVf "Y")))))

  (** val coq_Rsmger : (Lambek.formula, Lambek.structr) rule **)

  let coq_Rsmger =
    ((Sequent ((Lambek.SVf "X"), (Lambek.Smc ((Lambek.SVf "Y"), (Lambek.SVf
      "Z")))))::[]),(Sequent ((Lambek.Gre ((Lambek.SVf "Y"), (Lambek.SVf "X"))),
      (Lambek.SVf "Z")))

  (** val coq_Rgesml : (Lambek.formula, Lambek.structr) rule **)

  let coq_Rgesml =
    ((Sequent ((Lambek.Gre ((Lambek.SVf "X"), (Lambek.SVf "Y"))), (Lambek.SVf
      "Z")))::[]),(Sequent ((Lambek.SVf "Y"), (Lambek.Smc ((Lambek.SVf "X"),
      (Lambek.SVf "Z")))))

  (** val coq_Rsmler : (Lambek.formula, Lambek.structr) rule **)

  let coq_Rsmler =
    ((Sequent ((Lambek.SVf "X"), (Lambek.Smc ((Lambek.SVf "Y"), (Lambek.SVf
      "Z")))))::[]),(Sequent ((Lambek.Les ((Lambek.SVf "X"), (Lambek.SVf "Z"))),
      (Lambek.SVf "Y")))
 end

type ('formula, 'structr) c8_case_alt =
  ('formula, 'structr) deriv_cofseqs -> ('formula, 'structr) deriv_cofseq

(** val c8_case_alt_imp_C8_case :
    'a1 eqDec -> 'a1 fLANG -> 'a1 lOGLANG -> 'a2 eqDec -> 'a2 fLANG -> ('a1, 'a2)
    sTRLANG -> ('a1, 'a2) dISPCALC -> 'a2 -> 'a2 -> ('a1, 'a2) sequent list -> ('a1,
    'a2) c8_case_alt -> ('a1, 'a2) dertree list -> ('a1, 'a2) dertree **)

let c8_case_alt_imp_C8_case eDf lf lL eDs ls sL dC x y ls0 halt ld =
  let s = Sequent (x, y) in
  let x0,_ = deriv_cofseq_iff eDf lf lL eDs ls sL dC s in
  x0 (halt (let _,x1 = deriv_cofseqs_iff eDf lf lL eDs ls sL dC ls0 in x1 ld))

(** val lP_exhibit :
    'a1 eqDec -> 'a1 fLANG -> 'a1 lOGLANG -> 'a2 eqDec -> 'a2 fLANG -> ('a1, 'a2)
    sTRLANG -> 'a1 -> ('a1, 'a2) sequent -> ('a1, 'a2) rule -> ('a1, 'a2) dertree list
    -> ('a2, (('a1, 'a2) rule, (('a1, 'a2) dertree list, ('a1, 'a2) dertree) sigT)
    sigT) sigT **)

let lP_exhibit eDf lf lL eDs ls sL a _ _ l =
  let s0 = lP_dec eDf lf lL eDs ls sL l a in
  (match s0 with
   | Some s -> s
   | None -> assert false (* absurd case *))

(** val rP_exhibit :
    'a1 eqDec -> 'a1 fLANG -> 'a1 lOGLANG -> 'a2 eqDec -> 'a2 fLANG -> ('a1, 'a2)
    sTRLANG -> 'a1 -> ('a1, 'a2) sequent -> ('a1, 'a2) rule -> ('a1, 'a2) dertree list
    -> ('a2, (('a1, 'a2) dertree, (('a1, 'a2) rule, ('a1, 'a2) dertree list) sigT)
    sigT) sigT **)

let rP_exhibit eDf lf lL eDs ls sL a _ _ l =
  let s0 = rP_dec eDf lf lL eDs ls sL l a in
  (match s0 with
   | Some s -> s
   | None -> assert false (* absurd case *))

(** val reduce_C8 :
    'a1 eqDec -> 'a1 fLANG -> 'a1 lOGLANG -> 'a2 eqDec -> 'a2 fLANG -> ('a1, 'a2)
    sTRLANG -> ('a1, 'a2) dISPCALC -> ('a1 -> ('a1, 'a2) dertree list -> 'a2 -> 'a2 ->
    ('a1, 'a2) rule -> ('a1, 'a2) dertree list -> ('a1, 'a2) rule -> ('a1, 'a2) dertree
    list -> ('a1, 'a2) afsSubst -> __ -> __ -> __ -> __ -> __ -> __ -> __ -> ('a1, 'a2)
    dertree) -> 'a1 -> ('a1, 'a2) dertree -> ('a1, 'a2) dertree **)

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
           ((map (conclDT eDf lf lL eDs ls sL) ((Der ((Sequent (x, (sL.fS a))), x0,
              x1))::((Der ((Sequent ((sL.fS a), x2)), x3, s5))::[]))),s)
       in
       hred a l x x2 x0 x1 x3 s5 hwfr __ __ __ __ __ __ __
  else Der (s, r, l)

(** val lambek_DC : (Lambek.formula, Lambek.structr) dISPCALC **)

let lambek_DC =
  (atrefl eqDec_formula f_Lambek_log lambek_log eqDec_structr f_Lambek lambek_str)::(
    (cUT eqDec_formula f_Lambek_log lambek_log eqDec_structr f_Lambek lambek_str)::(LambekRules.coq_Topl::(LambekRules.coq_Topr::(LambekRules.coq_Botl::(LambekRules.coq_Botr::(LambekRules.coq_Conll::(LambekRules.coq_Conlr::(LambekRules.coq_Conr::(LambekRules.coq_Disl::(LambekRules.coq_Disrl::(LambekRules.coq_Disrr::(LambekRules.coq_Onel::(LambekRules.coq_Oner::(LambekRules.coq_Zerl::(LambekRules.coq_Zerr::(LambekRules.coq_Fusl::(LambekRules.coq_Fusr::(LambekRules.coq_Undl::(LambekRules.coq_Undr::(LambekRules.coq_Ovel::(LambekRules.coq_Over::(LambekRules.coq_Iwl::(LambekRules.coq_Iwr::(LambekRules._UU03a6_addll::(LambekRules._UU03a6_addlr::(LambekRules._UU03a6_addrl::(LambekRules._UU03a6_addrr::(LambekRules._UU03a6_delll::(LambekRules._UU03a6_dellr::(LambekRules._UU03a6_delrl::(LambekRules._UU03a6_delrr::(LambekRules.coq_Rlesml::(LambekRules.coq_Rsmlel::(LambekRules.coq_Rlesmr::(LambekRules.coq_Rsmler::(LambekRules.coq_Rgesml::(LambekRules.coq_Rsmgel::(LambekRules.coq_Rgesmr::(LambekRules.coq_Rsmger::[])))))))))))))))))))))))))))))))))))))))

module LambekBelnap =
 struct
  (** val coq_C8_Con_l :
      Lambek.structr -> Lambek.structr -> Lambek.formula -> Lambek.formula ->
      (Lambek.formula, Lambek.structr) dertree list -> (Lambek.formula, Lambek.structr)
      dertree **)

  let coq_C8_Con_l x y a b ld =
    c8_case_alt_imp_C8_case eqDec_formula f_Lambek_log lambek_log eqDec_structr
      f_Lambek lambek_str lambek_DC x y ((Sequent (x, (Lambek.FSf a)))::((Sequent (x,
      (Lambek.FSf b)))::((Sequent ((Lambek.FSf a), y))::[]))) (fun hders ->
      let x0 = fun dC cs ->
        let _,x0 =
          forallT_deriv_cofseqs_iff eqDec_formula f_Lambek_log lambek_log eqDec_structr
            f_Lambek lambek_str dC cs
        in
        x0
      in
      let hders0 =
        x0 lambek_DC ((Sequent (x, (Lambek.FSf a)))::((Sequent (x, (Lambek.FSf
          b)))::((Sequent ((Lambek.FSf a), y))::[]))) hders
      in
      let hders1 =
        forallT_inv (Sequent (x, (Lambek.FSf a))) ((Sequent (x, (Lambek.FSf
          b)))::((Sequent ((Lambek.FSf a), y))::[])) hders0
      in
      let hders2 =
        forallT_inv_tail (Sequent (x, (Lambek.FSf a))) ((Sequent (x, (Lambek.FSf
          b)))::((Sequent ((Lambek.FSf a), y))::[])) hders0
      in
      let hders3 =
        forallT_inv_tail (Sequent (x, (Lambek.FSf b))) ((Sequent ((Lambek.FSf a),
          y))::[]) hders2
      in
      let hders4 = forallT_inv (Sequent ((Lambek.FSf a), y)) [] hders3 in
      deriv_cofseq_rule_bw_inDC eqDec_formula f_Lambek_log lambek_log eqDec_structr
        f_Lambek lambek_str lambek_DC
        (premsRule eqDec_formula f_Lambek_log lambek_log eqDec_structr f_Lambek
          lambek_str
          (cUT eqDec_formula f_Lambek_log lambek_log eqDec_structr f_Lambek lambek_str))
        (conclRule eqDec_formula f_Lambek_log lambek_log eqDec_structr f_Lambek
          lambek_str
          (cUT eqDec_formula f_Lambek_log lambek_log eqDec_structr f_Lambek lambek_str))
        (cUT_spec eqDec_formula f_Lambek_log lambek_log eqDec_structr f_Lambek
          lambek_str a x y)
        (forallT_deriv_cofseqs eqDec_formula f_Lambek_log lambek_log eqDec_structr
          f_Lambek lambek_str lambek_DC ((Sequent (x, (Lambek.FSf a)))::((Sequent
          ((Lambek.FSf a), y))::[])) (ForallT_cons ((Sequent (x, (Lambek.FSf a))),
          ((Sequent ((Lambek.FSf a), y))::[]), hders1, (ForallT_cons ((Sequent
          ((Lambek.FSf a), y)), [], hders4, ForallT_nil)))))) ld

  (** val coq_C8_Con_r :
      Lambek.structr -> Lambek.structr -> Lambek.formula -> Lambek.formula ->
      (Lambek.formula, Lambek.structr) dertree list -> (Lambek.formula, Lambek.structr)
      dertree **)

  let coq_C8_Con_r x y a b ld =
    c8_case_alt_imp_C8_case eqDec_formula f_Lambek_log lambek_log eqDec_structr
      f_Lambek lambek_str lambek_DC x y ((Sequent (x, (Lambek.FSf a)))::((Sequent (x,
      (Lambek.FSf b)))::((Sequent ((Lambek.FSf b), y))::[]))) (fun hders ->
      let x0 = fun dC cs ->
        let _,x0 =
          forallT_deriv_cofseqs_iff eqDec_formula f_Lambek_log lambek_log eqDec_structr
            f_Lambek lambek_str dC cs
        in
        x0
      in
      let hders0 =
        x0 lambek_DC ((Sequent (x, (Lambek.FSf a)))::((Sequent (x, (Lambek.FSf
          b)))::((Sequent ((Lambek.FSf b), y))::[]))) hders
      in
      let hders1 =
        forallT_inv_tail (Sequent (x, (Lambek.FSf a))) ((Sequent (x, (Lambek.FSf
          b)))::((Sequent ((Lambek.FSf b), y))::[])) hders0
      in
      let hders2 =
        forallT_inv (Sequent (x, (Lambek.FSf b))) ((Sequent ((Lambek.FSf b), y))::[])
          hders1
      in
      let hders3 =
        forallT_inv_tail (Sequent (x, (Lambek.FSf b))) ((Sequent ((Lambek.FSf b),
          y))::[]) hders1
      in
      let hders4 = forallT_inv (Sequent ((Lambek.FSf b), y)) [] hders3 in
      deriv_cofseq_rule_bw_inDC eqDec_formula f_Lambek_log lambek_log eqDec_structr
        f_Lambek lambek_str lambek_DC
        (premsRule eqDec_formula f_Lambek_log lambek_log eqDec_structr f_Lambek
          lambek_str
          (cUT eqDec_formula f_Lambek_log lambek_log eqDec_structr f_Lambek lambek_str))
        (conclRule eqDec_formula f_Lambek_log lambek_log eqDec_structr f_Lambek
          lambek_str
          (cUT eqDec_formula f_Lambek_log lambek_log eqDec_structr f_Lambek lambek_str))
        (cUT_spec eqDec_formula f_Lambek_log lambek_log eqDec_structr f_Lambek
          lambek_str b x y)
        (forallT_deriv_cofseqs eqDec_formula f_Lambek_log lambek_log eqDec_structr
          f_Lambek lambek_str lambek_DC ((Sequent (x, (Lambek.FSf b)))::((Sequent
          ((Lambek.FSf b), y))::[])) (ForallT_cons ((Sequent (x, (Lambek.FSf b))),
          ((Sequent ((Lambek.FSf b), y))::[]), hders2, (ForallT_cons ((Sequent
          ((Lambek.FSf b), y)), [], hders4, ForallT_nil)))))) ld

  (** val coq_C8_Dis_l :
      Lambek.structr -> Lambek.structr -> Lambek.formula -> Lambek.formula ->
      (Lambek.formula, Lambek.structr) dertree list -> (Lambek.formula, Lambek.structr)
      dertree **)

  let coq_C8_Dis_l x y a b ld =
    c8_case_alt_imp_C8_case eqDec_formula f_Lambek_log lambek_log eqDec_structr
      f_Lambek lambek_str lambek_DC x y ((Sequent (x, (Lambek.FSf a)))::((Sequent
      ((Lambek.FSf a), y))::((Sequent ((Lambek.FSf b), y))::[]))) (fun hders ->
      let x0 = fun dC cs ->
        let _,x0 =
          forallT_deriv_cofseqs_iff eqDec_formula f_Lambek_log lambek_log eqDec_structr
            f_Lambek lambek_str dC cs
        in
        x0
      in
      let hders0 =
        x0 lambek_DC ((Sequent (x, (Lambek.FSf a)))::((Sequent ((Lambek.FSf a),
          y))::((Sequent ((Lambek.FSf b), y))::[]))) hders
      in
      let hders1 =
        forallT_inv (Sequent (x, (Lambek.FSf a))) ((Sequent ((Lambek.FSf a),
          y))::((Sequent ((Lambek.FSf b), y))::[])) hders0
      in
      let hders2 =
        forallT_inv_tail (Sequent (x, (Lambek.FSf a))) ((Sequent ((Lambek.FSf a),
          y))::((Sequent ((Lambek.FSf b), y))::[])) hders0
      in
      let hders3 =
        forallT_inv (Sequent ((Lambek.FSf a), y)) ((Sequent ((Lambek.FSf b), y))::[])
          hders2
      in
      deriv_cofseq_rule_bw_inDC eqDec_formula f_Lambek_log lambek_log eqDec_structr
        f_Lambek lambek_str lambek_DC
        (premsRule eqDec_formula f_Lambek_log lambek_log eqDec_structr f_Lambek
          lambek_str
          (cUT eqDec_formula f_Lambek_log lambek_log eqDec_structr f_Lambek lambek_str))
        (conclRule eqDec_formula f_Lambek_log lambek_log eqDec_structr f_Lambek
          lambek_str
          (cUT eqDec_formula f_Lambek_log lambek_log eqDec_structr f_Lambek lambek_str))
        (cUT_spec eqDec_formula f_Lambek_log lambek_log eqDec_structr f_Lambek
          lambek_str a x y)
        (forallT_deriv_cofseqs eqDec_formula f_Lambek_log lambek_log eqDec_structr
          f_Lambek lambek_str lambek_DC ((Sequent (x, (Lambek.FSf a)))::((Sequent
          ((Lambek.FSf a), y))::[])) (ForallT_cons ((Sequent (x, (Lambek.FSf a))),
          ((Sequent ((Lambek.FSf a), y))::[]), hders1, (ForallT_cons ((Sequent
          ((Lambek.FSf a), y)), [], hders3, ForallT_nil)))))) ld

  (** val coq_C8_Dis_r :
      Lambek.structr -> Lambek.structr -> Lambek.formula -> Lambek.formula ->
      (Lambek.formula, Lambek.structr) dertree list -> (Lambek.formula, Lambek.structr)
      dertree **)

  let coq_C8_Dis_r x y a b ld =
    c8_case_alt_imp_C8_case eqDec_formula f_Lambek_log lambek_log eqDec_structr
      f_Lambek lambek_str lambek_DC x y ((Sequent (x, (Lambek.FSf b)))::((Sequent
      ((Lambek.FSf a), y))::((Sequent ((Lambek.FSf b), y))::[]))) (fun hders ->
      let x0 = fun dC cs ->
        let _,x0 =
          forallT_deriv_cofseqs_iff eqDec_formula f_Lambek_log lambek_log eqDec_structr
            f_Lambek lambek_str dC cs
        in
        x0
      in
      let hders0 =
        x0 lambek_DC ((Sequent (x, (Lambek.FSf b)))::((Sequent ((Lambek.FSf a),
          y))::((Sequent ((Lambek.FSf b), y))::[]))) hders
      in
      let hders1 =
        forallT_inv (Sequent (x, (Lambek.FSf b))) ((Sequent ((Lambek.FSf a),
          y))::((Sequent ((Lambek.FSf b), y))::[])) hders0
      in
      let hders2 =
        forallT_inv_tail (Sequent (x, (Lambek.FSf b))) ((Sequent ((Lambek.FSf a),
          y))::((Sequent ((Lambek.FSf b), y))::[])) hders0
      in
      let hders3 =
        forallT_inv_tail (Sequent ((Lambek.FSf a), y)) ((Sequent ((Lambek.FSf b),
          y))::[]) hders2
      in
      let hders4 = forallT_inv (Sequent ((Lambek.FSf b), y)) [] hders3 in
      deriv_cofseq_rule_bw_inDC eqDec_formula f_Lambek_log lambek_log eqDec_structr
        f_Lambek lambek_str lambek_DC
        (premsRule eqDec_formula f_Lambek_log lambek_log eqDec_structr f_Lambek
          lambek_str
          (cUT eqDec_formula f_Lambek_log lambek_log eqDec_structr f_Lambek lambek_str))
        (conclRule eqDec_formula f_Lambek_log lambek_log eqDec_structr f_Lambek
          lambek_str
          (cUT eqDec_formula f_Lambek_log lambek_log eqDec_structr f_Lambek lambek_str))
        (cUT_spec eqDec_formula f_Lambek_log lambek_log eqDec_structr f_Lambek
          lambek_str b x y)
        (forallT_deriv_cofseqs eqDec_formula f_Lambek_log lambek_log eqDec_structr
          f_Lambek lambek_str lambek_DC ((Sequent (x, (Lambek.FSf b)))::((Sequent
          ((Lambek.FSf b), y))::[])) (ForallT_cons ((Sequent (x, (Lambek.FSf b))),
          ((Sequent ((Lambek.FSf b), y))::[]), hders1, (ForallT_cons ((Sequent
          ((Lambek.FSf b), y)), [], hders4, ForallT_nil)))))) ld

  (** val coq_C8_Fus :
      Lambek.structr -> Lambek.structr -> Lambek.structr -> Lambek.formula ->
      Lambek.formula -> (Lambek.formula, Lambek.structr) dertree list ->
      (Lambek.formula, Lambek.structr) dertree **)

  let coq_C8_Fus x1 x2 y a b ld =
    c8_case_alt_imp_C8_case eqDec_formula f_Lambek_log lambek_log eqDec_structr
      f_Lambek lambek_str lambek_DC (Lambek.Smc (x1, x2)) y ((Sequent (x1, (Lambek.FSf
      a)))::((Sequent (x2, (Lambek.FSf b)))::((Sequent ((Lambek.Smc ((Lambek.FSf a),
      (Lambek.FSf b))), y))::[]))) (fun hders ->
      let x = fun dC cs ->
        let _,x =
          forallT_deriv_cofseqs_iff eqDec_formula f_Lambek_log lambek_log eqDec_structr
            f_Lambek lambek_str dC cs
        in
        x
      in
      let hders0 =
        x lambek_DC ((Sequent (x1, (Lambek.FSf a)))::((Sequent (x2, (Lambek.FSf
          b)))::((Sequent ((Lambek.Smc ((Lambek.FSf a), (Lambek.FSf b))), y))::[])))
          hders
      in
      let hders1 =
        forallT_inv (Sequent (x1, (Lambek.FSf a))) ((Sequent (x2, (Lambek.FSf
          b)))::((Sequent ((Lambek.Smc ((Lambek.FSf a), (Lambek.FSf b))), y))::[]))
          hders0
      in
      let hders2 =
        forallT_inv_tail (Sequent (x1, (Lambek.FSf a))) ((Sequent (x2, (Lambek.FSf
          b)))::((Sequent ((Lambek.Smc ((Lambek.FSf a), (Lambek.FSf b))), y))::[]))
          hders0
      in
      let hders3 =
        forallT_inv (Sequent (x2, (Lambek.FSf b))) ((Sequent ((Lambek.Smc ((Lambek.FSf
          a), (Lambek.FSf b))), y))::[]) hders2
      in
      let hders4 =
        forallT_inv_tail (Sequent (x2, (Lambek.FSf b))) ((Sequent ((Lambek.Smc
          ((Lambek.FSf a), (Lambek.FSf b))), y))::[]) hders2
      in
      let hders5 =
        forallT_inv (Sequent ((Lambek.Smc ((Lambek.FSf a), (Lambek.FSf b))), y)) []
          hders4
      in
      deriv_cofseq_rule_bw_inDC eqDec_formula f_Lambek_log lambek_log eqDec_structr
        f_Lambek lambek_str lambek_DC
        (premsRule eqDec_formula f_Lambek_log lambek_log eqDec_structr f_Lambek
          lambek_str LambekRules.coq_Rgesmr)
        (conclRule eqDec_formula f_Lambek_log lambek_log eqDec_structr f_Lambek
          lambek_str LambekRules.coq_Rgesmr)
        (seq_matchsub eqDec_formula f_Lambek_log lambek_log eqDec_structr f_Lambek
          lambek_str
          (conclRule eqDec_formula f_Lambek_log lambek_log eqDec_structr f_Lambek
            lambek_str LambekRules.coq_Rgesmr) (Sequent ((Lambek.Smc (x1, x2)), y)))
        (forallT_deriv_cofseqs eqDec_formula f_Lambek_log lambek_log eqDec_structr
          f_Lambek lambek_str lambek_DC
          (map
            (seqSubst eqDec_formula f_Lambek_log lambek_log eqDec_structr f_Lambek
              lambek_str
              (seq_matchsub eqDec_formula f_Lambek_log lambek_log eqDec_structr
                f_Lambek lambek_str
                (conclRule eqDec_formula f_Lambek_log lambek_log eqDec_structr f_Lambek
                  lambek_str LambekRules.coq_Rgesmr) (Sequent ((Lambek.Smc (x1, x2)),
                y))))
            (premsRule eqDec_formula f_Lambek_log lambek_log eqDec_structr f_Lambek
              lambek_str LambekRules.coq_Rgesmr)) (ForallT_cons
          ((seqSubst eqDec_formula f_Lambek_log lambek_log eqDec_structr f_Lambek
             lambek_str
             (seq_matchsub eqDec_formula f_Lambek_log lambek_log eqDec_structr f_Lambek
               lambek_str
               (conclRule eqDec_formula f_Lambek_log lambek_log eqDec_structr f_Lambek
                 lambek_str LambekRules.coq_Rgesmr) (Sequent ((Lambek.Smc (x1, x2)),
               y))) (Sequent ((Lambek.SVf "X"), (Lambek.Gre ((Lambek.SVf "Y"),
             (Lambek.SVf "Z")))))), [],
          (deriv_cofseq_rule_bw_inDC eqDec_formula f_Lambek_log lambek_log
            eqDec_structr f_Lambek lambek_str lambek_DC
            (premsRule eqDec_formula f_Lambek_log lambek_log eqDec_structr f_Lambek
              lambek_str
              (cUT eqDec_formula f_Lambek_log lambek_log eqDec_structr f_Lambek
                lambek_str))
            (conclRule eqDec_formula f_Lambek_log lambek_log eqDec_structr f_Lambek
              lambek_str
              (cUT eqDec_formula f_Lambek_log lambek_log eqDec_structr f_Lambek
                lambek_str))
            (cUT_spec eqDec_formula f_Lambek_log lambek_log eqDec_structr f_Lambek
              lambek_str b x2 (Lambek.Gre (x1, y)))
            (forallT_deriv_cofseqs eqDec_formula f_Lambek_log lambek_log eqDec_structr
              f_Lambek lambek_str lambek_DC ((Sequent (x2, (Lambek.FSf b)))::((Sequent
              ((Lambek.FSf b), (Lambek.Gre (x1, y))))::[])) (ForallT_cons ((Sequent
              (x2, (Lambek.FSf b))), ((Sequent ((Lambek.FSf b), (Lambek.Gre (x1,
              y))))::[]), hders3, (ForallT_cons ((Sequent ((Lambek.FSf b), (Lambek.Gre
              (x1, y)))), [],
              (deriv_cofseq_rule_bw_inDC eqDec_formula f_Lambek_log lambek_log
                eqDec_structr f_Lambek lambek_str lambek_DC
                (premsRule eqDec_formula f_Lambek_log lambek_log eqDec_structr f_Lambek
                  lambek_str LambekRules.coq_Rsmgel)
                (conclRule eqDec_formula f_Lambek_log lambek_log eqDec_structr f_Lambek
                  lambek_str LambekRules.coq_Rsmgel)
                (seq_matchsub eqDec_formula f_Lambek_log lambek_log eqDec_structr
                  f_Lambek lambek_str
                  (conclRule eqDec_formula f_Lambek_log lambek_log eqDec_structr
                    f_Lambek lambek_str LambekRules.coq_Rsmgel) (Sequent ((Lambek.FSf
                  b), (Lambek.Gre (x1, y)))))
                (forallT_deriv_cofseqs eqDec_formula f_Lambek_log lambek_log
                  eqDec_structr f_Lambek lambek_str lambek_DC
                  (map
                    (seqSubst eqDec_formula f_Lambek_log lambek_log eqDec_structr
                      f_Lambek lambek_str
                      (seq_matchsub eqDec_formula f_Lambek_log lambek_log eqDec_structr
                        f_Lambek lambek_str
                        (conclRule eqDec_formula f_Lambek_log lambek_log eqDec_structr
                          f_Lambek lambek_str LambekRules.coq_Rsmgel) (Sequent
                        ((Lambek.FSf b), (Lambek.Gre (x1, y))))))
                    (premsRule eqDec_formula f_Lambek_log lambek_log eqDec_structr
                      f_Lambek lambek_str LambekRules.coq_Rsmgel)) (ForallT_cons
                  ((seqSubst eqDec_formula f_Lambek_log lambek_log eqDec_structr
                     f_Lambek lambek_str
                     (seq_matchsub eqDec_formula f_Lambek_log lambek_log eqDec_structr
                       f_Lambek lambek_str
                       (conclRule eqDec_formula f_Lambek_log lambek_log eqDec_structr
                         f_Lambek lambek_str LambekRules.coq_Rsmgel) (Sequent
                       ((Lambek.FSf b), (Lambek.Gre (x1, y))))) (Sequent ((Lambek.Smc
                     ((Lambek.SVf "X"), (Lambek.SVf "Y"))), (Lambek.SVf "Z")))), [],
                  (deriv_cofseq_rule_bw_inDC eqDec_formula f_Lambek_log lambek_log
                    eqDec_structr f_Lambek lambek_str lambek_DC
                    (premsRule eqDec_formula f_Lambek_log lambek_log eqDec_structr
                      f_Lambek lambek_str LambekRules.coq_Rlesmr)
                    (conclRule eqDec_formula f_Lambek_log lambek_log eqDec_structr
                      f_Lambek lambek_str LambekRules.coq_Rlesmr)
                    (seq_matchsub eqDec_formula f_Lambek_log lambek_log eqDec_structr
                      f_Lambek lambek_str
                      (conclRule eqDec_formula f_Lambek_log lambek_log eqDec_structr
                        f_Lambek lambek_str LambekRules.coq_Rlesmr) (Sequent
                      ((Lambek.Smc (x1, (Lambek.FSf b))), y)))
                    (forallT_deriv_cofseqs eqDec_formula f_Lambek_log lambek_log
                      eqDec_structr f_Lambek lambek_str lambek_DC
                      (map
                        (seqSubst eqDec_formula f_Lambek_log lambek_log eqDec_structr
                          f_Lambek lambek_str
                          (seq_matchsub eqDec_formula f_Lambek_log lambek_log
                            eqDec_structr f_Lambek lambek_str
                            (conclRule eqDec_formula f_Lambek_log lambek_log
                              eqDec_structr f_Lambek lambek_str LambekRules.coq_Rlesmr)
                            (Sequent ((Lambek.Smc (x1, (Lambek.FSf b))), y))))
                        (premsRule eqDec_formula f_Lambek_log lambek_log eqDec_structr
                          f_Lambek lambek_str LambekRules.coq_Rlesmr)) (ForallT_cons
                      ((seqSubst eqDec_formula f_Lambek_log lambek_log eqDec_structr
                         f_Lambek lambek_str
                         (seq_matchsub eqDec_formula f_Lambek_log lambek_log
                           eqDec_structr f_Lambek lambek_str
                           (conclRule eqDec_formula f_Lambek_log lambek_log
                             eqDec_structr f_Lambek lambek_str LambekRules.coq_Rlesmr)
                           (Sequent ((Lambek.Smc (x1, (Lambek.FSf b))), y))) (Sequent
                         ((Lambek.SVf "X"), (Lambek.Les ((Lambek.SVf "Y"), (Lambek.SVf
                         "Z")))))), [],
                      (deriv_cofseq_rule_bw_inDC eqDec_formula f_Lambek_log lambek_log
                        eqDec_structr f_Lambek lambek_str lambek_DC
                        (premsRule eqDec_formula f_Lambek_log lambek_log eqDec_structr
                          f_Lambek lambek_str
                          (cUT eqDec_formula f_Lambek_log lambek_log eqDec_structr
                            f_Lambek lambek_str))
                        (conclRule eqDec_formula f_Lambek_log lambek_log eqDec_structr
                          f_Lambek lambek_str
                          (cUT eqDec_formula f_Lambek_log lambek_log eqDec_structr
                            f_Lambek lambek_str))
                        (cUT_spec eqDec_formula f_Lambek_log lambek_log eqDec_structr
                          f_Lambek lambek_str a x1 (Lambek.Les (y, (Lambek.FSf b))))
                        (forallT_deriv_cofseqs eqDec_formula f_Lambek_log lambek_log
                          eqDec_structr f_Lambek lambek_str lambek_DC ((Sequent (x1,
                          (Lambek.FSf a)))::((Sequent ((Lambek.FSf a), (Lambek.Les (y,
                          (Lambek.FSf b)))))::[])) (ForallT_cons ((Sequent (x1,
                          (Lambek.FSf a))), ((Sequent ((Lambek.FSf a), (Lambek.Les (y,
                          (Lambek.FSf b)))))::[]), hders1, (ForallT_cons ((Sequent
                          ((Lambek.FSf a), (Lambek.Les (y, (Lambek.FSf b))))), [],
                          (deriv_cofseq_rule_bw_inDC eqDec_formula f_Lambek_log
                            lambek_log eqDec_structr f_Lambek lambek_str lambek_DC
                            (premsRule eqDec_formula f_Lambek_log lambek_log
                              eqDec_structr f_Lambek lambek_str LambekRules.coq_Rsmlel)
                            (conclRule eqDec_formula f_Lambek_log lambek_log
                              eqDec_structr f_Lambek lambek_str LambekRules.coq_Rsmlel)
                            (seq_matchsub eqDec_formula f_Lambek_log lambek_log
                              eqDec_structr f_Lambek lambek_str
                              (conclRule eqDec_formula f_Lambek_log lambek_log
                                eqDec_structr f_Lambek lambek_str
                                LambekRules.coq_Rsmlel) (Sequent ((Lambek.FSf a),
                              (Lambek.Les (y, (Lambek.FSf b))))))
                            (forallT_deriv_cofseqs eqDec_formula f_Lambek_log
                              lambek_log eqDec_structr f_Lambek lambek_str lambek_DC
                              (map
                                (seqSubst eqDec_formula f_Lambek_log lambek_log
                                  eqDec_structr f_Lambek lambek_str
                                  (seq_matchsub eqDec_formula f_Lambek_log lambek_log
                                    eqDec_structr f_Lambek lambek_str
                                    (conclRule eqDec_formula f_Lambek_log lambek_log
                                      eqDec_structr f_Lambek lambek_str
                                      LambekRules.coq_Rsmlel) (Sequent ((Lambek.FSf a),
                                    (Lambek.Les (y, (Lambek.FSf b)))))))
                                (premsRule eqDec_formula f_Lambek_log lambek_log
                                  eqDec_structr f_Lambek lambek_str
                                  LambekRules.coq_Rsmlel)) (ForallT_cons
                              ((seqSubst eqDec_formula f_Lambek_log lambek_log
                                 eqDec_structr f_Lambek lambek_str
                                 (seq_matchsub eqDec_formula f_Lambek_log lambek_log
                                   eqDec_structr f_Lambek lambek_str
                                   (conclRule eqDec_formula f_Lambek_log lambek_log
                                     eqDec_structr f_Lambek lambek_str
                                     LambekRules.coq_Rsmlel) (Sequent ((Lambek.FSf a),
                                   (Lambek.Les (y, (Lambek.FSf b)))))) (Sequent
                                 ((Lambek.Smc ((Lambek.SVf "X"), (Lambek.SVf "Y"))),
                                 (Lambek.SVf "Z")))), [], hders5, ForallT_nil)))),
                          ForallT_nil)))))), ForallT_nil)))), ForallT_nil)))),
              ForallT_nil)))))), ForallT_nil)))) ld

  (** val coq_C8_Und :
      Lambek.structr -> Lambek.structr -> Lambek.structr -> Lambek.formula ->
      Lambek.formula -> (Lambek.formula, Lambek.structr) dertree list ->
      (Lambek.formula, Lambek.structr) dertree **)

  let coq_C8_Und x y1 y2 a b ld =
    c8_case_alt_imp_C8_case eqDec_formula f_Lambek_log lambek_log eqDec_structr
      f_Lambek lambek_str lambek_DC x (Lambek.Gre (y1, y2)) ((Sequent (x, (Lambek.Gre
      ((Lambek.FSf a), (Lambek.FSf b)))))::((Sequent (y1, (Lambek.FSf a)))::((Sequent
      ((Lambek.FSf b), y2))::[]))) (fun hders ->
      let x0 = fun dC cs ->
        let _,x0 =
          forallT_deriv_cofseqs_iff eqDec_formula f_Lambek_log lambek_log eqDec_structr
            f_Lambek lambek_str dC cs
        in
        x0
      in
      let hders0 =
        x0 lambek_DC ((Sequent (x, (Lambek.Gre ((Lambek.FSf a), (Lambek.FSf
          b)))))::((Sequent (y1, (Lambek.FSf a)))::((Sequent ((Lambek.FSf b),
          y2))::[]))) hders
      in
      let hders1 =
        forallT_inv (Sequent (x, (Lambek.Gre ((Lambek.FSf a), (Lambek.FSf b)))))
          ((Sequent (y1, (Lambek.FSf a)))::((Sequent ((Lambek.FSf b), y2))::[])) hders0
      in
      let hders2 =
        forallT_inv_tail (Sequent (x, (Lambek.Gre ((Lambek.FSf a), (Lambek.FSf b)))))
          ((Sequent (y1, (Lambek.FSf a)))::((Sequent ((Lambek.FSf b), y2))::[])) hders0
      in
      let hders3 =
        forallT_inv (Sequent (y1, (Lambek.FSf a))) ((Sequent ((Lambek.FSf b), y2))::[])
          hders2
      in
      let hders4 =
        forallT_inv_tail (Sequent (y1, (Lambek.FSf a))) ((Sequent ((Lambek.FSf b),
          y2))::[]) hders2
      in
      let hders5 = forallT_inv (Sequent ((Lambek.FSf b), y2)) [] hders4 in
      deriv_cofseq_rule_bw_inDC eqDec_formula f_Lambek_log lambek_log eqDec_structr
        f_Lambek lambek_str lambek_DC
        (premsRule eqDec_formula f_Lambek_log lambek_log eqDec_structr f_Lambek
          lambek_str LambekRules.coq_Rsmgel)
        (conclRule eqDec_formula f_Lambek_log lambek_log eqDec_structr f_Lambek
          lambek_str LambekRules.coq_Rsmgel)
        (seq_matchsub eqDec_formula f_Lambek_log lambek_log eqDec_structr f_Lambek
          lambek_str
          (conclRule eqDec_formula f_Lambek_log lambek_log eqDec_structr f_Lambek
            lambek_str LambekRules.coq_Rsmgel) (Sequent (x, (Lambek.Gre (y1, y2)))))
        (forallT_deriv_cofseqs eqDec_formula f_Lambek_log lambek_log eqDec_structr
          f_Lambek lambek_str lambek_DC
          (map
            (seqSubst eqDec_formula f_Lambek_log lambek_log eqDec_structr f_Lambek
              lambek_str
              (seq_matchsub eqDec_formula f_Lambek_log lambek_log eqDec_structr
                f_Lambek lambek_str
                (conclRule eqDec_formula f_Lambek_log lambek_log eqDec_structr f_Lambek
                  lambek_str LambekRules.coq_Rsmgel) (Sequent (x, (Lambek.Gre (y1,
                y2))))))
            (premsRule eqDec_formula f_Lambek_log lambek_log eqDec_structr f_Lambek
              lambek_str LambekRules.coq_Rsmgel)) (ForallT_cons
          ((seqSubst eqDec_formula f_Lambek_log lambek_log eqDec_structr f_Lambek
             lambek_str
             (seq_matchsub eqDec_formula f_Lambek_log lambek_log eqDec_structr f_Lambek
               lambek_str
               (conclRule eqDec_formula f_Lambek_log lambek_log eqDec_structr f_Lambek
                 lambek_str LambekRules.coq_Rsmgel) (Sequent (x, (Lambek.Gre (y1,
               y2))))) (Sequent ((Lambek.Smc ((Lambek.SVf "X"), (Lambek.SVf "Y"))),
             (Lambek.SVf "Z")))), [],
          (deriv_cofseq_rule_bw_inDC eqDec_formula f_Lambek_log lambek_log
            eqDec_structr f_Lambek lambek_str lambek_DC
            (premsRule eqDec_formula f_Lambek_log lambek_log eqDec_structr f_Lambek
              lambek_str LambekRules.coq_Rlesmr)
            (conclRule eqDec_formula f_Lambek_log lambek_log eqDec_structr f_Lambek
              lambek_str LambekRules.coq_Rlesmr)
            (seq_matchsub eqDec_formula f_Lambek_log lambek_log eqDec_structr f_Lambek
              lambek_str
              (conclRule eqDec_formula f_Lambek_log lambek_log eqDec_structr f_Lambek
                lambek_str LambekRules.coq_Rlesmr) (Sequent ((Lambek.Smc (y1, x)), y2)))
            (forallT_deriv_cofseqs eqDec_formula f_Lambek_log lambek_log eqDec_structr
              f_Lambek lambek_str lambek_DC
              (map
                (seqSubst eqDec_formula f_Lambek_log lambek_log eqDec_structr f_Lambek
                  lambek_str
                  (seq_matchsub eqDec_formula f_Lambek_log lambek_log eqDec_structr
                    f_Lambek lambek_str
                    (conclRule eqDec_formula f_Lambek_log lambek_log eqDec_structr
                      f_Lambek lambek_str LambekRules.coq_Rlesmr) (Sequent ((Lambek.Smc
                    (y1, x)), y2))))
                (premsRule eqDec_formula f_Lambek_log lambek_log eqDec_structr f_Lambek
                  lambek_str LambekRules.coq_Rlesmr)) (ForallT_cons
              ((seqSubst eqDec_formula f_Lambek_log lambek_log eqDec_structr f_Lambek
                 lambek_str
                 (seq_matchsub eqDec_formula f_Lambek_log lambek_log eqDec_structr
                   f_Lambek lambek_str
                   (conclRule eqDec_formula f_Lambek_log lambek_log eqDec_structr
                     f_Lambek lambek_str LambekRules.coq_Rlesmr) (Sequent ((Lambek.Smc
                   (y1, x)), y2))) (Sequent ((Lambek.SVf "X"), (Lambek.Les ((Lambek.SVf
                 "Y"), (Lambek.SVf "Z")))))), [],
              (deriv_cofseq_rule_bw_inDC eqDec_formula f_Lambek_log lambek_log
                eqDec_structr f_Lambek lambek_str lambek_DC
                (premsRule eqDec_formula f_Lambek_log lambek_log eqDec_structr f_Lambek
                  lambek_str
                  (cUT eqDec_formula f_Lambek_log lambek_log eqDec_structr f_Lambek
                    lambek_str))
                (conclRule eqDec_formula f_Lambek_log lambek_log eqDec_structr f_Lambek
                  lambek_str
                  (cUT eqDec_formula f_Lambek_log lambek_log eqDec_structr f_Lambek
                    lambek_str))
                (cUT_spec eqDec_formula f_Lambek_log lambek_log eqDec_structr f_Lambek
                  lambek_str a y1 (Lambek.Les (y2, x)))
                (forallT_deriv_cofseqs eqDec_formula f_Lambek_log lambek_log
                  eqDec_structr f_Lambek lambek_str lambek_DC ((Sequent (y1,
                  (Lambek.FSf a)))::((Sequent ((Lambek.FSf a), (Lambek.Les (y2,
                  x))))::[])) (ForallT_cons ((Sequent (y1, (Lambek.FSf a))), ((Sequent
                  ((Lambek.FSf a), (Lambek.Les (y2, x))))::[]), hders3, (ForallT_cons
                  ((Sequent ((Lambek.FSf a), (Lambek.Les (y2, x)))), [],
                  (deriv_cofseq_rule_bw_inDC eqDec_formula f_Lambek_log lambek_log
                    eqDec_structr f_Lambek lambek_str lambek_DC
                    (premsRule eqDec_formula f_Lambek_log lambek_log eqDec_structr
                      f_Lambek lambek_str LambekRules.coq_Rsmlel)
                    (conclRule eqDec_formula f_Lambek_log lambek_log eqDec_structr
                      f_Lambek lambek_str LambekRules.coq_Rsmlel)
                    (seq_matchsub eqDec_formula f_Lambek_log lambek_log eqDec_structr
                      f_Lambek lambek_str
                      (conclRule eqDec_formula f_Lambek_log lambek_log eqDec_structr
                        f_Lambek lambek_str LambekRules.coq_Rsmlel) (Sequent
                      ((Lambek.FSf a), (Lambek.Les (y2, x)))))
                    (forallT_deriv_cofseqs eqDec_formula f_Lambek_log lambek_log
                      eqDec_structr f_Lambek lambek_str lambek_DC
                      (map
                        (seqSubst eqDec_formula f_Lambek_log lambek_log eqDec_structr
                          f_Lambek lambek_str
                          (seq_matchsub eqDec_formula f_Lambek_log lambek_log
                            eqDec_structr f_Lambek lambek_str
                            (conclRule eqDec_formula f_Lambek_log lambek_log
                              eqDec_structr f_Lambek lambek_str LambekRules.coq_Rsmlel)
                            (Sequent ((Lambek.FSf a), (Lambek.Les (y2, x))))))
                        (premsRule eqDec_formula f_Lambek_log lambek_log eqDec_structr
                          f_Lambek lambek_str LambekRules.coq_Rsmlel)) (ForallT_cons
                      ((seqSubst eqDec_formula f_Lambek_log lambek_log eqDec_structr
                         f_Lambek lambek_str
                         (seq_matchsub eqDec_formula f_Lambek_log lambek_log
                           eqDec_structr f_Lambek lambek_str
                           (conclRule eqDec_formula f_Lambek_log lambek_log
                             eqDec_structr f_Lambek lambek_str LambekRules.coq_Rsmlel)
                           (Sequent ((Lambek.FSf a), (Lambek.Les (y2, x))))) (Sequent
                         ((Lambek.Smc ((Lambek.SVf "X"), (Lambek.SVf "Y"))),
                         (Lambek.SVf "Z")))), [],
                      (deriv_cofseq_rule_bw_inDC eqDec_formula f_Lambek_log lambek_log
                        eqDec_structr f_Lambek lambek_str lambek_DC
                        (premsRule eqDec_formula f_Lambek_log lambek_log eqDec_structr
                          f_Lambek lambek_str
                          (cUT eqDec_formula f_Lambek_log lambek_log eqDec_structr
                            f_Lambek lambek_str))
                        (conclRule eqDec_formula f_Lambek_log lambek_log eqDec_structr
                          f_Lambek lambek_str
                          (cUT eqDec_formula f_Lambek_log lambek_log eqDec_structr
                            f_Lambek lambek_str))
                        (cUT_spec eqDec_formula f_Lambek_log lambek_log eqDec_structr
                          f_Lambek lambek_str b (Lambek.Smc ((Lambek.FSf a), x)) y2)
                        (forallT_deriv_cofseqs eqDec_formula f_Lambek_log lambek_log
                          eqDec_structr f_Lambek lambek_str lambek_DC ((Sequent
                          ((Lambek.Smc ((Lambek.FSf a), x)), (Lambek.FSf
                          b)))::((Sequent ((Lambek.FSf b), y2))::[])) (ForallT_cons
                          ((Sequent ((Lambek.Smc ((Lambek.FSf a), x)), (Lambek.FSf
                          b))), ((Sequent ((Lambek.FSf b), y2))::[]),
                          (deriv_cofseq_rule_bw_inDC eqDec_formula f_Lambek_log
                            lambek_log eqDec_structr f_Lambek lambek_str lambek_DC
                            (premsRule eqDec_formula f_Lambek_log lambek_log
                              eqDec_structr f_Lambek lambek_str LambekRules.coq_Rgesmr)
                            (conclRule eqDec_formula f_Lambek_log lambek_log
                              eqDec_structr f_Lambek lambek_str LambekRules.coq_Rgesmr)
                            (seq_matchsub eqDec_formula f_Lambek_log lambek_log
                              eqDec_structr f_Lambek lambek_str
                              (conclRule eqDec_formula f_Lambek_log lambek_log
                                eqDec_structr f_Lambek lambek_str
                                LambekRules.coq_Rgesmr) (Sequent ((Lambek.Smc
                              ((Lambek.FSf a), x)), (Lambek.FSf b))))
                            (forallT_deriv_cofseqs eqDec_formula f_Lambek_log
                              lambek_log eqDec_structr f_Lambek lambek_str lambek_DC
                              (map
                                (seqSubst eqDec_formula f_Lambek_log lambek_log
                                  eqDec_structr f_Lambek lambek_str
                                  (seq_matchsub eqDec_formula f_Lambek_log lambek_log
                                    eqDec_structr f_Lambek lambek_str
                                    (conclRule eqDec_formula f_Lambek_log lambek_log
                                      eqDec_structr f_Lambek lambek_str
                                      LambekRules.coq_Rgesmr) (Sequent ((Lambek.Smc
                                    ((Lambek.FSf a), x)), (Lambek.FSf b)))))
                                (premsRule eqDec_formula f_Lambek_log lambek_log
                                  eqDec_structr f_Lambek lambek_str
                                  LambekRules.coq_Rgesmr)) (ForallT_cons
                              ((seqSubst eqDec_formula f_Lambek_log lambek_log
                                 eqDec_structr f_Lambek lambek_str
                                 (seq_matchsub eqDec_formula f_Lambek_log lambek_log
                                   eqDec_structr f_Lambek lambek_str
                                   (conclRule eqDec_formula f_Lambek_log lambek_log
                                     eqDec_structr f_Lambek lambek_str
                                     LambekRules.coq_Rgesmr) (Sequent ((Lambek.Smc
                                   ((Lambek.FSf a), x)), (Lambek.FSf b)))) (Sequent
                                 ((Lambek.SVf "X"), (Lambek.Gre ((Lambek.SVf "Y"),
                                 (Lambek.SVf "Z")))))), [], hders1, ForallT_nil)))),
                          (ForallT_cons ((Sequent ((Lambek.FSf b), y2)), [], hders5,
                          ForallT_nil)))))), ForallT_nil)))), ForallT_nil)))))),
              ForallT_nil)))), ForallT_nil)))) ld

  (** val coq_C8_Ove :
      Lambek.structr -> Lambek.structr -> Lambek.structr -> Lambek.formula ->
      Lambek.formula -> (Lambek.formula, Lambek.structr) dertree list ->
      (Lambek.formula, Lambek.structr) dertree **)

  let coq_C8_Ove x y1 y2 a b ld =
    c8_case_alt_imp_C8_case eqDec_formula f_Lambek_log lambek_log eqDec_structr
      f_Lambek lambek_str lambek_DC x (Lambek.Les (y1, y2)) ((Sequent (x, (Lambek.Les
      ((Lambek.FSf a), (Lambek.FSf b)))))::((Sequent ((Lambek.FSf a), y1))::((Sequent
      (y2, (Lambek.FSf b)))::[]))) (fun hders ->
      let x0 = fun dC cs ->
        let _,x0 =
          forallT_deriv_cofseqs_iff eqDec_formula f_Lambek_log lambek_log eqDec_structr
            f_Lambek lambek_str dC cs
        in
        x0
      in
      let hders0 =
        x0 lambek_DC ((Sequent (x, (Lambek.Les ((Lambek.FSf a), (Lambek.FSf
          b)))))::((Sequent ((Lambek.FSf a), y1))::((Sequent (y2, (Lambek.FSf
          b)))::[]))) hders
      in
      let hders1 =
        forallT_inv (Sequent (x, (Lambek.Les ((Lambek.FSf a), (Lambek.FSf b)))))
          ((Sequent ((Lambek.FSf a), y1))::((Sequent (y2, (Lambek.FSf b)))::[])) hders0
      in
      let hders2 =
        forallT_inv_tail (Sequent (x, (Lambek.Les ((Lambek.FSf a), (Lambek.FSf b)))))
          ((Sequent ((Lambek.FSf a), y1))::((Sequent (y2, (Lambek.FSf b)))::[])) hders0
      in
      let hders3 =
        forallT_inv (Sequent ((Lambek.FSf a), y1)) ((Sequent (y2, (Lambek.FSf b)))::[])
          hders2
      in
      let hders4 =
        forallT_inv_tail (Sequent ((Lambek.FSf a), y1)) ((Sequent (y2, (Lambek.FSf
          b)))::[]) hders2
      in
      let hders5 = forallT_inv (Sequent (y2, (Lambek.FSf b))) [] hders4 in
      deriv_cofseq_rule_bw_inDC eqDec_formula f_Lambek_log lambek_log eqDec_structr
        f_Lambek lambek_str lambek_DC
        (premsRule eqDec_formula f_Lambek_log lambek_log eqDec_structr f_Lambek
          lambek_str LambekRules.coq_Rsmlel)
        (conclRule eqDec_formula f_Lambek_log lambek_log eqDec_structr f_Lambek
          lambek_str LambekRules.coq_Rsmlel)
        (seq_matchsub eqDec_formula f_Lambek_log lambek_log eqDec_structr f_Lambek
          lambek_str
          (conclRule eqDec_formula f_Lambek_log lambek_log eqDec_structr f_Lambek
            lambek_str LambekRules.coq_Rsmlel) (Sequent (x, (Lambek.Les (y1, y2)))))
        (forallT_deriv_cofseqs eqDec_formula f_Lambek_log lambek_log eqDec_structr
          f_Lambek lambek_str lambek_DC
          (map
            (seqSubst eqDec_formula f_Lambek_log lambek_log eqDec_structr f_Lambek
              lambek_str
              (seq_matchsub eqDec_formula f_Lambek_log lambek_log eqDec_structr
                f_Lambek lambek_str
                (conclRule eqDec_formula f_Lambek_log lambek_log eqDec_structr f_Lambek
                  lambek_str LambekRules.coq_Rsmlel) (Sequent (x, (Lambek.Les (y1,
                y2))))))
            (premsRule eqDec_formula f_Lambek_log lambek_log eqDec_structr f_Lambek
              lambek_str LambekRules.coq_Rsmlel)) (ForallT_cons
          ((seqSubst eqDec_formula f_Lambek_log lambek_log eqDec_structr f_Lambek
             lambek_str
             (seq_matchsub eqDec_formula f_Lambek_log lambek_log eqDec_structr f_Lambek
               lambek_str
               (conclRule eqDec_formula f_Lambek_log lambek_log eqDec_structr f_Lambek
                 lambek_str LambekRules.coq_Rsmlel) (Sequent (x, (Lambek.Les (y1,
               y2))))) (Sequent ((Lambek.Smc ((Lambek.SVf "X"), (Lambek.SVf "Y"))),
             (Lambek.SVf "Z")))), [],
          (deriv_cofseq_rule_bw_inDC eqDec_formula f_Lambek_log lambek_log
            eqDec_structr f_Lambek lambek_str lambek_DC
            (premsRule eqDec_formula f_Lambek_log lambek_log eqDec_structr f_Lambek
              lambek_str LambekRules.coq_Rgesmr)
            (conclRule eqDec_formula f_Lambek_log lambek_log eqDec_structr f_Lambek
              lambek_str LambekRules.coq_Rgesmr)
            (seq_matchsub eqDec_formula f_Lambek_log lambek_log eqDec_structr f_Lambek
              lambek_str
              (conclRule eqDec_formula f_Lambek_log lambek_log eqDec_structr f_Lambek
                lambek_str LambekRules.coq_Rgesmr) (Sequent ((Lambek.Smc (x, y2)), y1)))
            (forallT_deriv_cofseqs eqDec_formula f_Lambek_log lambek_log eqDec_structr
              f_Lambek lambek_str lambek_DC
              (map
                (seqSubst eqDec_formula f_Lambek_log lambek_log eqDec_structr f_Lambek
                  lambek_str
                  (seq_matchsub eqDec_formula f_Lambek_log lambek_log eqDec_structr
                    f_Lambek lambek_str
                    (conclRule eqDec_formula f_Lambek_log lambek_log eqDec_structr
                      f_Lambek lambek_str LambekRules.coq_Rgesmr) (Sequent ((Lambek.Smc
                    (x, y2)), y1))))
                (premsRule eqDec_formula f_Lambek_log lambek_log eqDec_structr f_Lambek
                  lambek_str LambekRules.coq_Rgesmr)) (ForallT_cons
              ((seqSubst eqDec_formula f_Lambek_log lambek_log eqDec_structr f_Lambek
                 lambek_str
                 (seq_matchsub eqDec_formula f_Lambek_log lambek_log eqDec_structr
                   f_Lambek lambek_str
                   (conclRule eqDec_formula f_Lambek_log lambek_log eqDec_structr
                     f_Lambek lambek_str LambekRules.coq_Rgesmr) (Sequent ((Lambek.Smc
                   (x, y2)), y1))) (Sequent ((Lambek.SVf "X"), (Lambek.Gre ((Lambek.SVf
                 "Y"), (Lambek.SVf "Z")))))), [],
              (deriv_cofseq_rule_bw_inDC eqDec_formula f_Lambek_log lambek_log
                eqDec_structr f_Lambek lambek_str lambek_DC
                (premsRule eqDec_formula f_Lambek_log lambek_log eqDec_structr f_Lambek
                  lambek_str
                  (cUT eqDec_formula f_Lambek_log lambek_log eqDec_structr f_Lambek
                    lambek_str))
                (conclRule eqDec_formula f_Lambek_log lambek_log eqDec_structr f_Lambek
                  lambek_str
                  (cUT eqDec_formula f_Lambek_log lambek_log eqDec_structr f_Lambek
                    lambek_str))
                (cUT_spec eqDec_formula f_Lambek_log lambek_log eqDec_structr f_Lambek
                  lambek_str b y2 (Lambek.Gre (x, y1)))
                (forallT_deriv_cofseqs eqDec_formula f_Lambek_log lambek_log
                  eqDec_structr f_Lambek lambek_str lambek_DC ((Sequent (y2,
                  (Lambek.FSf b)))::((Sequent ((Lambek.FSf b), (Lambek.Gre (x,
                  y1))))::[])) (ForallT_cons ((Sequent (y2, (Lambek.FSf b))), ((Sequent
                  ((Lambek.FSf b), (Lambek.Gre (x, y1))))::[]), hders5, (ForallT_cons
                  ((Sequent ((Lambek.FSf b), (Lambek.Gre (x, y1)))), [],
                  (deriv_cofseq_rule_bw_inDC eqDec_formula f_Lambek_log lambek_log
                    eqDec_structr f_Lambek lambek_str lambek_DC
                    (premsRule eqDec_formula f_Lambek_log lambek_log eqDec_structr
                      f_Lambek lambek_str LambekRules.coq_Rsmgel)
                    (conclRule eqDec_formula f_Lambek_log lambek_log eqDec_structr
                      f_Lambek lambek_str LambekRules.coq_Rsmgel)
                    (seq_matchsub eqDec_formula f_Lambek_log lambek_log eqDec_structr
                      f_Lambek lambek_str
                      (conclRule eqDec_formula f_Lambek_log lambek_log eqDec_structr
                        f_Lambek lambek_str LambekRules.coq_Rsmgel) (Sequent
                      ((Lambek.FSf b), (Lambek.Gre (x, y1)))))
                    (forallT_deriv_cofseqs eqDec_formula f_Lambek_log lambek_log
                      eqDec_structr f_Lambek lambek_str lambek_DC
                      (map
                        (seqSubst eqDec_formula f_Lambek_log lambek_log eqDec_structr
                          f_Lambek lambek_str
                          (seq_matchsub eqDec_formula f_Lambek_log lambek_log
                            eqDec_structr f_Lambek lambek_str
                            (conclRule eqDec_formula f_Lambek_log lambek_log
                              eqDec_structr f_Lambek lambek_str LambekRules.coq_Rsmgel)
                            (Sequent ((Lambek.FSf b), (Lambek.Gre (x, y1))))))
                        (premsRule eqDec_formula f_Lambek_log lambek_log eqDec_structr
                          f_Lambek lambek_str LambekRules.coq_Rsmgel)) (ForallT_cons
                      ((seqSubst eqDec_formula f_Lambek_log lambek_log eqDec_structr
                         f_Lambek lambek_str
                         (seq_matchsub eqDec_formula f_Lambek_log lambek_log
                           eqDec_structr f_Lambek lambek_str
                           (conclRule eqDec_formula f_Lambek_log lambek_log
                             eqDec_structr f_Lambek lambek_str LambekRules.coq_Rsmgel)
                           (Sequent ((Lambek.FSf b), (Lambek.Gre (x, y1))))) (Sequent
                         ((Lambek.Smc ((Lambek.SVf "X"), (Lambek.SVf "Y"))),
                         (Lambek.SVf "Z")))), [],
                      (deriv_cofseq_rule_bw_inDC eqDec_formula f_Lambek_log lambek_log
                        eqDec_structr f_Lambek lambek_str lambek_DC
                        (premsRule eqDec_formula f_Lambek_log lambek_log eqDec_structr
                          f_Lambek lambek_str
                          (cUT eqDec_formula f_Lambek_log lambek_log eqDec_structr
                            f_Lambek lambek_str))
                        (conclRule eqDec_formula f_Lambek_log lambek_log eqDec_structr
                          f_Lambek lambek_str
                          (cUT eqDec_formula f_Lambek_log lambek_log eqDec_structr
                            f_Lambek lambek_str))
                        (cUT_spec eqDec_formula f_Lambek_log lambek_log eqDec_structr
                          f_Lambek lambek_str a (Lambek.Smc (x, (Lambek.FSf b))) y1)
                        (forallT_deriv_cofseqs eqDec_formula f_Lambek_log lambek_log
                          eqDec_structr f_Lambek lambek_str lambek_DC ((Sequent
                          ((Lambek.Smc (x, (Lambek.FSf b))), (Lambek.FSf
                          a)))::((Sequent ((Lambek.FSf a), y1))::[])) (ForallT_cons
                          ((Sequent ((Lambek.Smc (x, (Lambek.FSf b))), (Lambek.FSf
                          a))), ((Sequent ((Lambek.FSf a), y1))::[]),
                          (deriv_cofseq_rule_bw_inDC eqDec_formula f_Lambek_log
                            lambek_log eqDec_structr f_Lambek lambek_str lambek_DC
                            (premsRule eqDec_formula f_Lambek_log lambek_log
                              eqDec_structr f_Lambek lambek_str LambekRules.coq_Rlesmr)
                            (conclRule eqDec_formula f_Lambek_log lambek_log
                              eqDec_structr f_Lambek lambek_str LambekRules.coq_Rlesmr)
                            (seq_matchsub eqDec_formula f_Lambek_log lambek_log
                              eqDec_structr f_Lambek lambek_str
                              (conclRule eqDec_formula f_Lambek_log lambek_log
                                eqDec_structr f_Lambek lambek_str
                                LambekRules.coq_Rlesmr) (Sequent ((Lambek.Smc (x,
                              (Lambek.FSf b))), (Lambek.FSf a))))
                            (forallT_deriv_cofseqs eqDec_formula f_Lambek_log
                              lambek_log eqDec_structr f_Lambek lambek_str lambek_DC
                              (map
                                (seqSubst eqDec_formula f_Lambek_log lambek_log
                                  eqDec_structr f_Lambek lambek_str
                                  (seq_matchsub eqDec_formula f_Lambek_log lambek_log
                                    eqDec_structr f_Lambek lambek_str
                                    (conclRule eqDec_formula f_Lambek_log lambek_log
                                      eqDec_structr f_Lambek lambek_str
                                      LambekRules.coq_Rlesmr) (Sequent ((Lambek.Smc (x,
                                    (Lambek.FSf b))), (Lambek.FSf a)))))
                                (premsRule eqDec_formula f_Lambek_log lambek_log
                                  eqDec_structr f_Lambek lambek_str
                                  LambekRules.coq_Rlesmr)) (ForallT_cons
                              ((seqSubst eqDec_formula f_Lambek_log lambek_log
                                 eqDec_structr f_Lambek lambek_str
                                 (seq_matchsub eqDec_formula f_Lambek_log lambek_log
                                   eqDec_structr f_Lambek lambek_str
                                   (conclRule eqDec_formula f_Lambek_log lambek_log
                                     eqDec_structr f_Lambek lambek_str
                                     LambekRules.coq_Rlesmr) (Sequent ((Lambek.Smc (x,
                                   (Lambek.FSf b))), (Lambek.FSf a)))) (Sequent
                                 ((Lambek.SVf "X"), (Lambek.Les ((Lambek.SVf "Y"),
                                 (Lambek.SVf "Z")))))), [], hders1, ForallT_nil)))),
                          (ForallT_cons ((Sequent ((Lambek.FSf a), y1)), [], hders3,
                          ForallT_nil)))))), ForallT_nil)))), ForallT_nil)))))),
              ForallT_nil)))), ForallT_nil)))) ld

  (** val coq_C8_holds :
      Lambek.formula -> (Lambek.formula, Lambek.structr) dertree -> (Lambek.formula,
      Lambek.structr) dertree **)

  let coq_C8_holds m dt =
    reduce_C8 eqDec_formula f_Lambek_log lambek_log eqDec_structr f_Lambek lambek_str
      lambek_DC (fun a _ x y rL lL rR lR _ _ _ _ _ _ _ _ ->
      eq_dec_in_list
        (eqdec
          (eqDec_rule eqDec_formula f_Lambek_log lambek_log eqDec_structr f_Lambek
            lambek_str))
        (atrefl eqDec_formula f_Lambek_log lambek_log eqDec_structr f_Lambek lambek_str)
        (LambekRules.coq_Topr::(LambekRules.coq_Botr::(LambekRules.coq_Conr::(LambekRules.coq_Disrl::(LambekRules.coq_Disrr::(LambekRules.coq_Oner::(LambekRules.coq_Zerr::(LambekRules.coq_Fusr::(LambekRules.coq_Undr::(LambekRules.coq_Over::[]))))))))))
        rL (fun _ ->
        eq_dec_in_list
          (eqdec
            (eqDec_rule eqDec_formula f_Lambek_log lambek_log eqDec_structr f_Lambek
              lambek_str))
          (atrefl eqDec_formula f_Lambek_log lambek_log eqDec_structr f_Lambek
            lambek_str)
          (LambekRules.coq_Topl::(LambekRules.coq_Botl::(LambekRules.coq_Conll::(LambekRules.coq_Conlr::(LambekRules.coq_Disl::(LambekRules.coq_Onel::(LambekRules.coq_Zerl::(LambekRules.coq_Fusl::(LambekRules.coq_Undl::(LambekRules.coq_Ovel::[]))))))))))
          rR (fun _ ->
          let hwfrR =
            ruleInst_ruleSubst eqDec_formula f_Lambek_log lambek_log eqDec_structr
              f_Lambek lambek_str rR
              ((map
                 (conclDT eqDec_formula f_Lambek_log lambek_log eqDec_structr f_Lambek
                   lambek_str) lR),(Sequent ((lambek_str.fS a), y)))
          in
          (match lL with
           | [] ->
             (match lR with
              | [] ->
                let p = fst (fst hwfrR) "p" in
                Der ((Sequent ((Lambek.FSf (Lambek.Atf p)), (Lambek.FSf (Lambek.Atf
                p)))),
                (atrefl eqDec_formula f_Lambek_log lambek_log eqDec_structr f_Lambek
                  lambek_str), [])
              | _::_ -> assert false (* absurd case *))
           | _::_ -> assert false (* absurd case *))) (fun _ ->
          eq_dec_in_list
            (eqdec
              (eqDec_rule eqDec_formula f_Lambek_log lambek_log eqDec_structr f_Lambek
                lambek_str)) LambekRules.coq_Topl
            (LambekRules.coq_Botl::(LambekRules.coq_Conll::(LambekRules.coq_Conlr::(LambekRules.coq_Disl::(LambekRules.coq_Onel::(LambekRules.coq_Zerl::(LambekRules.coq_Fusl::(LambekRules.coq_Undl::(LambekRules.coq_Ovel::[])))))))))
            rR (fun _ -> assert false (* absurd case *)) (fun _ ->
            eq_dec_in_list
              (eqdec
                (eqDec_rule eqDec_formula f_Lambek_log lambek_log eqDec_structr
                  f_Lambek lambek_str)) LambekRules.coq_Botl
              (LambekRules.coq_Conll::(LambekRules.coq_Conlr::(LambekRules.coq_Disl::(LambekRules.coq_Onel::(LambekRules.coq_Zerl::(LambekRules.coq_Fusl::(LambekRules.coq_Undl::(LambekRules.coq_Ovel::[]))))))))
              rR (fun _ -> assert false (* absurd case *)) (fun _ ->
              eq_dec_in_list
                (eqdec
                  (eqDec_rule eqDec_formula f_Lambek_log lambek_log eqDec_structr
                    f_Lambek lambek_str)) LambekRules.coq_Conll
                (LambekRules.coq_Conlr::(LambekRules.coq_Disl::(LambekRules.coq_Onel::(LambekRules.coq_Zerl::(LambekRules.coq_Fusl::(LambekRules.coq_Undl::(LambekRules.coq_Ovel::[])))))))
                rR (fun _ -> assert false (* absurd case *)) (fun _ ->
                eq_dec_in_list
                  (eqdec
                    (eqDec_rule eqDec_formula f_Lambek_log lambek_log eqDec_structr
                      f_Lambek lambek_str)) LambekRules.coq_Conlr
                  (LambekRules.coq_Disl::(LambekRules.coq_Onel::(LambekRules.coq_Zerl::(LambekRules.coq_Fusl::(LambekRules.coq_Undl::(LambekRules.coq_Ovel::[]))))))
                  rR (fun _ -> assert false (* absurd case *)) (fun _ ->
                  eq_dec_in_list
                    (eqdec
                      (eqDec_rule eqDec_formula f_Lambek_log lambek_log eqDec_structr
                        f_Lambek lambek_str)) LambekRules.coq_Disl
                    (LambekRules.coq_Onel::(LambekRules.coq_Zerl::(LambekRules.coq_Fusl::(LambekRules.coq_Undl::(LambekRules.coq_Ovel::[])))))
                    rR (fun _ -> assert false (* absurd case *)) (fun _ ->
                    eq_dec_in_list
                      (eqdec
                        (eqDec_rule eqDec_formula f_Lambek_log lambek_log eqDec_structr
                          f_Lambek lambek_str)) LambekRules.coq_Onel
                      (LambekRules.coq_Zerl::(LambekRules.coq_Fusl::(LambekRules.coq_Undl::(LambekRules.coq_Ovel::[]))))
                      rR (fun _ -> assert false (* absurd case *)) (fun _ ->
                      eq_dec_in_list
                        (eqdec
                          (eqDec_rule eqDec_formula f_Lambek_log lambek_log
                            eqDec_structr f_Lambek lambek_str)) LambekRules.coq_Zerl
                        (LambekRules.coq_Fusl::(LambekRules.coq_Undl::(LambekRules.coq_Ovel::[])))
                        rR (fun _ -> assert false (* absurd case *)) (fun _ ->
                        eq_dec_in_list
                          (eqdec
                            (eqDec_rule eqDec_formula f_Lambek_log lambek_log
                              eqDec_structr f_Lambek lambek_str)) LambekRules.coq_Fusl
                          (LambekRules.coq_Undl::(LambekRules.coq_Ovel::[])) rR
                          (fun _ -> assert false (* absurd case *)) (fun _ ->
                          eq_dec_in_list
                            (eqdec
                              (eqDec_rule eqDec_formula f_Lambek_log lambek_log
                                eqDec_structr f_Lambek lambek_str))
                            LambekRules.coq_Undl (LambekRules.coq_Ovel::[]) rR
                            (fun _ -> assert false (* absurd case *)) (fun _ ->
                            eq_dec_in_list
                              (eqdec
                                (eqDec_rule eqDec_formula f_Lambek_log lambek_log
                                  eqDec_structr f_Lambek lambek_str))
                              LambekRules.coq_Ovel [] rR (fun _ -> assert false
                              (* absurd case *)) (fun _ -> assert false
                              (* absurd case *))))))))))))) (fun _ ->
        eq_dec_in_list
          (eqdec
            (eqDec_rule eqDec_formula f_Lambek_log lambek_log eqDec_structr f_Lambek
              lambek_str)) LambekRules.coq_Topr
          (LambekRules.coq_Botr::(LambekRules.coq_Conr::(LambekRules.coq_Disrl::(LambekRules.coq_Disrr::(LambekRules.coq_Oner::(LambekRules.coq_Zerr::(LambekRules.coq_Fusr::(LambekRules.coq_Undr::(LambekRules.coq_Over::[])))))))))
          rL (fun _ ->
          eq_dec_in_list
            (eqdec
              (eqDec_rule eqDec_formula f_Lambek_log lambek_log eqDec_structr f_Lambek
                lambek_str))
            (atrefl eqDec_formula f_Lambek_log lambek_log eqDec_structr f_Lambek
              lambek_str)
            (LambekRules.coq_Topl::(LambekRules.coq_Botl::(LambekRules.coq_Conll::(LambekRules.coq_Conlr::(LambekRules.coq_Disl::(LambekRules.coq_Onel::(LambekRules.coq_Zerl::(LambekRules.coq_Fusl::(LambekRules.coq_Undl::(LambekRules.coq_Ovel::[]))))))))))
            rR (fun _ -> assert false (* absurd case *)) (fun _ ->
            eq_dec_in_list
              (eqdec
                (eqDec_rule eqDec_formula f_Lambek_log lambek_log eqDec_structr
                  f_Lambek lambek_str)) LambekRules.coq_Topl
              (LambekRules.coq_Botl::(LambekRules.coq_Conll::(LambekRules.coq_Conlr::(LambekRules.coq_Disl::(LambekRules.coq_Onel::(LambekRules.coq_Zerl::(LambekRules.coq_Fusl::(LambekRules.coq_Undl::(LambekRules.coq_Ovel::[])))))))))
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
                  (eqDec_rule eqDec_formula f_Lambek_log lambek_log eqDec_structr
                    f_Lambek lambek_str)) LambekRules.coq_Botl
                (LambekRules.coq_Conll::(LambekRules.coq_Conlr::(LambekRules.coq_Disl::(LambekRules.coq_Onel::(LambekRules.coq_Zerl::(LambekRules.coq_Fusl::(LambekRules.coq_Undl::(LambekRules.coq_Ovel::[]))))))))
                rR (fun _ -> assert false (* absurd case *)) (fun _ ->
                eq_dec_in_list
                  (eqdec
                    (eqDec_rule eqDec_formula f_Lambek_log lambek_log eqDec_structr
                      f_Lambek lambek_str)) LambekRules.coq_Conll
                  (LambekRules.coq_Conlr::(LambekRules.coq_Disl::(LambekRules.coq_Onel::(LambekRules.coq_Zerl::(LambekRules.coq_Fusl::(LambekRules.coq_Undl::(LambekRules.coq_Ovel::[])))))))
                  rR (fun _ -> assert false (* absurd case *)) (fun _ ->
                  eq_dec_in_list
                    (eqdec
                      (eqDec_rule eqDec_formula f_Lambek_log lambek_log eqDec_structr
                        f_Lambek lambek_str)) LambekRules.coq_Conlr
                    (LambekRules.coq_Disl::(LambekRules.coq_Onel::(LambekRules.coq_Zerl::(LambekRules.coq_Fusl::(LambekRules.coq_Undl::(LambekRules.coq_Ovel::[]))))))
                    rR (fun _ -> assert false (* absurd case *)) (fun _ ->
                    eq_dec_in_list
                      (eqdec
                        (eqDec_rule eqDec_formula f_Lambek_log lambek_log eqDec_structr
                          f_Lambek lambek_str)) LambekRules.coq_Disl
                      (LambekRules.coq_Onel::(LambekRules.coq_Zerl::(LambekRules.coq_Fusl::(LambekRules.coq_Undl::(LambekRules.coq_Ovel::[])))))
                      rR (fun _ -> assert false (* absurd case *)) (fun _ ->
                      eq_dec_in_list
                        (eqdec
                          (eqDec_rule eqDec_formula f_Lambek_log lambek_log
                            eqDec_structr f_Lambek lambek_str)) LambekRules.coq_Onel
                        (LambekRules.coq_Zerl::(LambekRules.coq_Fusl::(LambekRules.coq_Undl::(LambekRules.coq_Ovel::[]))))
                        rR (fun _ -> assert false (* absurd case *)) (fun _ ->
                        eq_dec_in_list
                          (eqdec
                            (eqDec_rule eqDec_formula f_Lambek_log lambek_log
                              eqDec_structr f_Lambek lambek_str)) LambekRules.coq_Zerl
                          (LambekRules.coq_Fusl::(LambekRules.coq_Undl::(LambekRules.coq_Ovel::[])))
                          rR (fun _ -> assert false (* absurd case *)) (fun _ ->
                          eq_dec_in_list
                            (eqdec
                              (eqDec_rule eqDec_formula f_Lambek_log lambek_log
                                eqDec_structr f_Lambek lambek_str))
                            LambekRules.coq_Fusl
                            (LambekRules.coq_Undl::(LambekRules.coq_Ovel::[])) rR
                            (fun _ -> assert false (* absurd case *)) (fun _ ->
                            eq_dec_in_list
                              (eqdec
                                (eqDec_rule eqDec_formula f_Lambek_log lambek_log
                                  eqDec_structr f_Lambek lambek_str))
                              LambekRules.coq_Undl (LambekRules.coq_Ovel::[]) rR
                              (fun _ -> assert false (* absurd case *)) (fun _ ->
                              eq_dec_in_list
                                (eqdec
                                  (eqDec_rule eqDec_formula f_Lambek_log lambek_log
                                    eqDec_structr f_Lambek lambek_str))
                                LambekRules.coq_Ovel [] rR (fun _ -> assert false
                                (* absurd case *)) (fun _ -> assert false
                                (* absurd case *))))))))))))) (fun _ ->
          eq_dec_in_list
            (eqdec
              (eqDec_rule eqDec_formula f_Lambek_log lambek_log eqDec_structr f_Lambek
                lambek_str)) LambekRules.coq_Botr
            (LambekRules.coq_Conr::(LambekRules.coq_Disrl::(LambekRules.coq_Disrr::(LambekRules.coq_Oner::(LambekRules.coq_Zerr::(LambekRules.coq_Fusr::(LambekRules.coq_Undr::(LambekRules.coq_Over::[]))))))))
            rL (fun _ ->
            eq_dec_in_list
              (eqdec
                (eqDec_rule eqDec_formula f_Lambek_log lambek_log eqDec_structr
                  f_Lambek lambek_str))
              (atrefl eqDec_formula f_Lambek_log lambek_log eqDec_structr f_Lambek
                lambek_str)
              (LambekRules.coq_Topl::(LambekRules.coq_Botl::(LambekRules.coq_Conll::(LambekRules.coq_Conlr::(LambekRules.coq_Disl::(LambekRules.coq_Onel::(LambekRules.coq_Zerl::(LambekRules.coq_Fusl::(LambekRules.coq_Undl::(LambekRules.coq_Ovel::[]))))))))))
              rR (fun _ -> assert false (* absurd case *)) (fun _ ->
              eq_dec_in_list
                (eqdec
                  (eqDec_rule eqDec_formula f_Lambek_log lambek_log eqDec_structr
                    f_Lambek lambek_str)) LambekRules.coq_Topl
                (LambekRules.coq_Botl::(LambekRules.coq_Conll::(LambekRules.coq_Conlr::(LambekRules.coq_Disl::(LambekRules.coq_Onel::(LambekRules.coq_Zerl::(LambekRules.coq_Fusl::(LambekRules.coq_Undl::(LambekRules.coq_Ovel::[])))))))))
                rR (fun _ -> assert false (* absurd case *)) (fun _ ->
                eq_dec_in_list
                  (eqdec
                    (eqDec_rule eqDec_formula f_Lambek_log lambek_log eqDec_structr
                      f_Lambek lambek_str)) LambekRules.coq_Botl
                  (LambekRules.coq_Conll::(LambekRules.coq_Conlr::(LambekRules.coq_Disl::(LambekRules.coq_Onel::(LambekRules.coq_Zerl::(LambekRules.coq_Fusl::(LambekRules.coq_Undl::(LambekRules.coq_Ovel::[]))))))))
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
                      (eqDec_rule eqDec_formula f_Lambek_log lambek_log eqDec_structr
                        f_Lambek lambek_str)) LambekRules.coq_Conll
                    (LambekRules.coq_Conlr::(LambekRules.coq_Disl::(LambekRules.coq_Onel::(LambekRules.coq_Zerl::(LambekRules.coq_Fusl::(LambekRules.coq_Undl::(LambekRules.coq_Ovel::[])))))))
                    rR (fun _ -> assert false (* absurd case *)) (fun _ ->
                    eq_dec_in_list
                      (eqdec
                        (eqDec_rule eqDec_formula f_Lambek_log lambek_log eqDec_structr
                          f_Lambek lambek_str)) LambekRules.coq_Conlr
                      (LambekRules.coq_Disl::(LambekRules.coq_Onel::(LambekRules.coq_Zerl::(LambekRules.coq_Fusl::(LambekRules.coq_Undl::(LambekRules.coq_Ovel::[]))))))
                      rR (fun _ -> assert false (* absurd case *)) (fun _ ->
                      eq_dec_in_list
                        (eqdec
                          (eqDec_rule eqDec_formula f_Lambek_log lambek_log
                            eqDec_structr f_Lambek lambek_str)) LambekRules.coq_Disl
                        (LambekRules.coq_Onel::(LambekRules.coq_Zerl::(LambekRules.coq_Fusl::(LambekRules.coq_Undl::(LambekRules.coq_Ovel::[])))))
                        rR (fun _ -> assert false (* absurd case *)) (fun _ ->
                        eq_dec_in_list
                          (eqdec
                            (eqDec_rule eqDec_formula f_Lambek_log lambek_log
                              eqDec_structr f_Lambek lambek_str)) LambekRules.coq_Onel
                          (LambekRules.coq_Zerl::(LambekRules.coq_Fusl::(LambekRules.coq_Undl::(LambekRules.coq_Ovel::[]))))
                          rR (fun _ -> assert false (* absurd case *)) (fun _ ->
                          eq_dec_in_list
                            (eqdec
                              (eqDec_rule eqDec_formula f_Lambek_log lambek_log
                                eqDec_structr f_Lambek lambek_str))
                            LambekRules.coq_Zerl
                            (LambekRules.coq_Fusl::(LambekRules.coq_Undl::(LambekRules.coq_Ovel::[])))
                            rR (fun _ -> assert false (* absurd case *)) (fun _ ->
                            eq_dec_in_list
                              (eqdec
                                (eqDec_rule eqDec_formula f_Lambek_log lambek_log
                                  eqDec_structr f_Lambek lambek_str))
                              LambekRules.coq_Fusl
                              (LambekRules.coq_Undl::(LambekRules.coq_Ovel::[])) rR
                              (fun _ -> assert false (* absurd case *)) (fun _ ->
                              eq_dec_in_list
                                (eqdec
                                  (eqDec_rule eqDec_formula f_Lambek_log lambek_log
                                    eqDec_structr f_Lambek lambek_str))
                                LambekRules.coq_Undl (LambekRules.coq_Ovel::[]) rR
                                (fun _ -> assert false (* absurd case *)) (fun _ ->
                                eq_dec_in_list
                                  (eqdec
                                    (eqDec_rule eqDec_formula f_Lambek_log lambek_log
                                      eqDec_structr f_Lambek lambek_str))
                                  LambekRules.coq_Ovel [] rR (fun _ -> assert false
                                  (* absurd case *)) (fun _ -> assert false
                                  (* absurd case *))))))))))))) (fun _ ->
            eq_dec_in_list
              (eqdec
                (eqDec_rule eqDec_formula f_Lambek_log lambek_log eqDec_structr
                  f_Lambek lambek_str)) LambekRules.coq_Conr
              (LambekRules.coq_Disrl::(LambekRules.coq_Disrr::(LambekRules.coq_Oner::(LambekRules.coq_Zerr::(LambekRules.coq_Fusr::(LambekRules.coq_Undr::(LambekRules.coq_Over::[])))))))
              rL (fun _ ->
              eq_dec_in_list
                (eqdec
                  (eqDec_rule eqDec_formula f_Lambek_log lambek_log eqDec_structr
                    f_Lambek lambek_str))
                (atrefl eqDec_formula f_Lambek_log lambek_log eqDec_structr f_Lambek
                  lambek_str)
                (LambekRules.coq_Topl::(LambekRules.coq_Botl::(LambekRules.coq_Conll::(LambekRules.coq_Conlr::(LambekRules.coq_Disl::(LambekRules.coq_Onel::(LambekRules.coq_Zerl::(LambekRules.coq_Fusl::(LambekRules.coq_Undl::(LambekRules.coq_Ovel::[]))))))))))
                rR (fun _ -> assert false (* absurd case *)) (fun _ ->
                eq_dec_in_list
                  (eqdec
                    (eqDec_rule eqDec_formula f_Lambek_log lambek_log eqDec_structr
                      f_Lambek lambek_str)) LambekRules.coq_Topl
                  (LambekRules.coq_Botl::(LambekRules.coq_Conll::(LambekRules.coq_Conlr::(LambekRules.coq_Disl::(LambekRules.coq_Onel::(LambekRules.coq_Zerl::(LambekRules.coq_Fusl::(LambekRules.coq_Undl::(LambekRules.coq_Ovel::[])))))))))
                  rR (fun _ -> assert false (* absurd case *)) (fun _ ->
                  eq_dec_in_list
                    (eqdec
                      (eqDec_rule eqDec_formula f_Lambek_log lambek_log eqDec_structr
                        f_Lambek lambek_str)) LambekRules.coq_Botl
                    (LambekRules.coq_Conll::(LambekRules.coq_Conlr::(LambekRules.coq_Disl::(LambekRules.coq_Onel::(LambekRules.coq_Zerl::(LambekRules.coq_Fusl::(LambekRules.coq_Undl::(LambekRules.coq_Ovel::[]))))))))
                    rR (fun _ -> assert false (* absurd case *)) (fun _ ->
                    eq_dec_in_list
                      (eqdec
                        (eqDec_rule eqDec_formula f_Lambek_log lambek_log eqDec_structr
                          f_Lambek lambek_str)) LambekRules.coq_Conll
                      (LambekRules.coq_Conlr::(LambekRules.coq_Disl::(LambekRules.coq_Onel::(LambekRules.coq_Zerl::(LambekRules.coq_Fusl::(LambekRules.coq_Undl::(LambekRules.coq_Ovel::[])))))))
                      rR (fun _ ->
                      let hwfrL =
                        ruleInst_ruleSubst eqDec_formula f_Lambek_log lambek_log
                          eqDec_structr f_Lambek lambek_str rL
                          ((map
                             (conclDT eqDec_formula f_Lambek_log lambek_log
                               eqDec_structr f_Lambek lambek_str) lL),(Sequent (x,
                          (lambek_str.fS a))))
                      in
                      let hwfrR =
                        ruleInst_ruleSubst eqDec_formula f_Lambek_log lambek_log
                          eqDec_structr f_Lambek lambek_str rR
                          ((map
                             (conclDT eqDec_formula f_Lambek_log lambek_log
                               eqDec_structr f_Lambek lambek_str) lR),(Sequent
                          ((lambek_str.fS a), y)))
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
                                     coq_C8_Con_l (snd hwfrL "X") (snd hwfrR "X")
                                       (snd (fst hwfrR) "A") (snd (fst hwfrR) "B")
                                       (d::(d0::(d1::[])))
                                   | _::_ -> assert false (* absurd case *)))
                             | _::_ -> assert false (* absurd case *))))) (fun _ ->
                      eq_dec_in_list
                        (eqdec
                          (eqDec_rule eqDec_formula f_Lambek_log lambek_log
                            eqDec_structr f_Lambek lambek_str)) LambekRules.coq_Conlr
                        (LambekRules.coq_Disl::(LambekRules.coq_Onel::(LambekRules.coq_Zerl::(LambekRules.coq_Fusl::(LambekRules.coq_Undl::(LambekRules.coq_Ovel::[]))))))
                        rR (fun _ ->
                        let hwfrL =
                          ruleInst_ruleSubst eqDec_formula f_Lambek_log lambek_log
                            eqDec_structr f_Lambek lambek_str rL
                            ((map
                               (conclDT eqDec_formula f_Lambek_log lambek_log
                                 eqDec_structr f_Lambek lambek_str) lL),(Sequent (x,
                            (lambek_str.fS a))))
                        in
                        let hwfrR =
                          ruleInst_ruleSubst eqDec_formula f_Lambek_log lambek_log
                            eqDec_structr f_Lambek lambek_str rR
                            ((map
                               (conclDT eqDec_formula f_Lambek_log lambek_log
                                 eqDec_structr f_Lambek lambek_str) lR),(Sequent
                            ((lambek_str.fS a), y)))
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
                                       coq_C8_Con_r (snd hwfrL "X") (snd hwfrR "X")
                                         (snd (fst hwfrR) "A") (snd (fst hwfrR) "B")
                                         (d::(d0::(d1::[])))
                                     | _::_ -> assert false (* absurd case *)))
                               | _::_ -> assert false (* absurd case *))))) (fun _ ->
                        eq_dec_in_list
                          (eqdec
                            (eqDec_rule eqDec_formula f_Lambek_log lambek_log
                              eqDec_structr f_Lambek lambek_str)) LambekRules.coq_Disl
                          (LambekRules.coq_Onel::(LambekRules.coq_Zerl::(LambekRules.coq_Fusl::(LambekRules.coq_Undl::(LambekRules.coq_Ovel::[])))))
                          rR (fun _ -> assert false (* absurd case *)) (fun _ ->
                          eq_dec_in_list
                            (eqdec
                              (eqDec_rule eqDec_formula f_Lambek_log lambek_log
                                eqDec_structr f_Lambek lambek_str))
                            LambekRules.coq_Onel
                            (LambekRules.coq_Zerl::(LambekRules.coq_Fusl::(LambekRules.coq_Undl::(LambekRules.coq_Ovel::[]))))
                            rR (fun _ -> assert false (* absurd case *)) (fun _ ->
                            eq_dec_in_list
                              (eqdec
                                (eqDec_rule eqDec_formula f_Lambek_log lambek_log
                                  eqDec_structr f_Lambek lambek_str))
                              LambekRules.coq_Zerl
                              (LambekRules.coq_Fusl::(LambekRules.coq_Undl::(LambekRules.coq_Ovel::[])))
                              rR (fun _ -> assert false (* absurd case *)) (fun _ ->
                              eq_dec_in_list
                                (eqdec
                                  (eqDec_rule eqDec_formula f_Lambek_log lambek_log
                                    eqDec_structr f_Lambek lambek_str))
                                LambekRules.coq_Fusl
                                (LambekRules.coq_Undl::(LambekRules.coq_Ovel::[])) rR
                                (fun _ -> assert false (* absurd case *)) (fun _ ->
                                eq_dec_in_list
                                  (eqdec
                                    (eqDec_rule eqDec_formula f_Lambek_log lambek_log
                                      eqDec_structr f_Lambek lambek_str))
                                  LambekRules.coq_Undl (LambekRules.coq_Ovel::[]) rR
                                  (fun _ -> assert false (* absurd case *)) (fun _ ->
                                  eq_dec_in_list
                                    (eqdec
                                      (eqDec_rule eqDec_formula f_Lambek_log lambek_log
                                        eqDec_structr f_Lambek lambek_str))
                                    LambekRules.coq_Ovel [] rR (fun _ -> assert false
                                    (* absurd case *)) (fun _ -> assert false
                                    (* absurd case *))))))))))))) (fun _ ->
              eq_dec_in_list
                (eqdec
                  (eqDec_rule eqDec_formula f_Lambek_log lambek_log eqDec_structr
                    f_Lambek lambek_str)) LambekRules.coq_Disrl
                (LambekRules.coq_Disrr::(LambekRules.coq_Oner::(LambekRules.coq_Zerr::(LambekRules.coq_Fusr::(LambekRules.coq_Undr::(LambekRules.coq_Over::[]))))))
                rL (fun _ ->
                eq_dec_in_list
                  (eqdec
                    (eqDec_rule eqDec_formula f_Lambek_log lambek_log eqDec_structr
                      f_Lambek lambek_str))
                  (atrefl eqDec_formula f_Lambek_log lambek_log eqDec_structr f_Lambek
                    lambek_str)
                  (LambekRules.coq_Topl::(LambekRules.coq_Botl::(LambekRules.coq_Conll::(LambekRules.coq_Conlr::(LambekRules.coq_Disl::(LambekRules.coq_Onel::(LambekRules.coq_Zerl::(LambekRules.coq_Fusl::(LambekRules.coq_Undl::(LambekRules.coq_Ovel::[]))))))))))
                  rR (fun _ -> assert false (* absurd case *)) (fun _ ->
                  eq_dec_in_list
                    (eqdec
                      (eqDec_rule eqDec_formula f_Lambek_log lambek_log eqDec_structr
                        f_Lambek lambek_str)) LambekRules.coq_Topl
                    (LambekRules.coq_Botl::(LambekRules.coq_Conll::(LambekRules.coq_Conlr::(LambekRules.coq_Disl::(LambekRules.coq_Onel::(LambekRules.coq_Zerl::(LambekRules.coq_Fusl::(LambekRules.coq_Undl::(LambekRules.coq_Ovel::[])))))))))
                    rR (fun _ -> assert false (* absurd case *)) (fun _ ->
                    eq_dec_in_list
                      (eqdec
                        (eqDec_rule eqDec_formula f_Lambek_log lambek_log eqDec_structr
                          f_Lambek lambek_str)) LambekRules.coq_Botl
                      (LambekRules.coq_Conll::(LambekRules.coq_Conlr::(LambekRules.coq_Disl::(LambekRules.coq_Onel::(LambekRules.coq_Zerl::(LambekRules.coq_Fusl::(LambekRules.coq_Undl::(LambekRules.coq_Ovel::[]))))))))
                      rR (fun _ -> assert false (* absurd case *)) (fun _ ->
                      eq_dec_in_list
                        (eqdec
                          (eqDec_rule eqDec_formula f_Lambek_log lambek_log
                            eqDec_structr f_Lambek lambek_str)) LambekRules.coq_Conll
                        (LambekRules.coq_Conlr::(LambekRules.coq_Disl::(LambekRules.coq_Onel::(LambekRules.coq_Zerl::(LambekRules.coq_Fusl::(LambekRules.coq_Undl::(LambekRules.coq_Ovel::[])))))))
                        rR (fun _ -> assert false (* absurd case *)) (fun _ ->
                        eq_dec_in_list
                          (eqdec
                            (eqDec_rule eqDec_formula f_Lambek_log lambek_log
                              eqDec_structr f_Lambek lambek_str)) LambekRules.coq_Conlr
                          (LambekRules.coq_Disl::(LambekRules.coq_Onel::(LambekRules.coq_Zerl::(LambekRules.coq_Fusl::(LambekRules.coq_Undl::(LambekRules.coq_Ovel::[]))))))
                          rR (fun _ -> assert false (* absurd case *)) (fun _ ->
                          eq_dec_in_list
                            (eqdec
                              (eqDec_rule eqDec_formula f_Lambek_log lambek_log
                                eqDec_structr f_Lambek lambek_str))
                            LambekRules.coq_Disl
                            (LambekRules.coq_Onel::(LambekRules.coq_Zerl::(LambekRules.coq_Fusl::(LambekRules.coq_Undl::(LambekRules.coq_Ovel::[])))))
                            rR (fun _ ->
                            let hwfrL =
                              ruleInst_ruleSubst eqDec_formula f_Lambek_log lambek_log
                                eqDec_structr f_Lambek lambek_str rL
                                ((map
                                   (conclDT eqDec_formula f_Lambek_log lambek_log
                                     eqDec_structr f_Lambek lambek_str) lL),(Sequent
                                (x, (lambek_str.fS a))))
                            in
                            let hwfrR =
                              ruleInst_ruleSubst eqDec_formula f_Lambek_log lambek_log
                                eqDec_structr f_Lambek lambek_str rR
                                ((map
                                   (conclDT eqDec_formula f_Lambek_log lambek_log
                                     eqDec_structr f_Lambek lambek_str) lR),(Sequent
                                ((lambek_str.fS a), y)))
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
                                           coq_C8_Dis_l (snd hwfrL "X") (snd hwfrR "X")
                                             (snd (fst hwfrR) "A")
                                             (snd (fst hwfrR) "B") (d::(d0::(d1::[])))
                                         | _::_ -> assert false (* absurd case *))))
                                | _::_ -> assert false (* absurd case *)))) (fun _ ->
                            eq_dec_in_list
                              (eqdec
                                (eqDec_rule eqDec_formula f_Lambek_log lambek_log
                                  eqDec_structr f_Lambek lambek_str))
                              LambekRules.coq_Onel
                              (LambekRules.coq_Zerl::(LambekRules.coq_Fusl::(LambekRules.coq_Undl::(LambekRules.coq_Ovel::[]))))
                              rR (fun _ -> assert false (* absurd case *)) (fun _ ->
                              eq_dec_in_list
                                (eqdec
                                  (eqDec_rule eqDec_formula f_Lambek_log lambek_log
                                    eqDec_structr f_Lambek lambek_str))
                                LambekRules.coq_Zerl
                                (LambekRules.coq_Fusl::(LambekRules.coq_Undl::(LambekRules.coq_Ovel::[])))
                                rR (fun _ -> assert false (* absurd case *)) (fun _ ->
                                eq_dec_in_list
                                  (eqdec
                                    (eqDec_rule eqDec_formula f_Lambek_log lambek_log
                                      eqDec_structr f_Lambek lambek_str))
                                  LambekRules.coq_Fusl
                                  (LambekRules.coq_Undl::(LambekRules.coq_Ovel::[])) rR
                                  (fun _ -> assert false (* absurd case *)) (fun _ ->
                                  eq_dec_in_list
                                    (eqdec
                                      (eqDec_rule eqDec_formula f_Lambek_log lambek_log
                                        eqDec_structr f_Lambek lambek_str))
                                    LambekRules.coq_Undl (LambekRules.coq_Ovel::[]) rR
                                    (fun _ -> assert false (* absurd case *)) (fun _ ->
                                    eq_dec_in_list
                                      (eqdec
                                        (eqDec_rule eqDec_formula f_Lambek_log
                                          lambek_log eqDec_structr f_Lambek lambek_str))
                                      LambekRules.coq_Ovel [] rR (fun _ -> assert false
                                      (* absurd case *)) (fun _ -> assert false
                                      (* absurd case *))))))))))))) (fun _ ->
                eq_dec_in_list
                  (eqdec
                    (eqDec_rule eqDec_formula f_Lambek_log lambek_log eqDec_structr
                      f_Lambek lambek_str)) LambekRules.coq_Disrr
                  (LambekRules.coq_Oner::(LambekRules.coq_Zerr::(LambekRules.coq_Fusr::(LambekRules.coq_Undr::(LambekRules.coq_Over::[])))))
                  rL (fun _ ->
                  eq_dec_in_list
                    (eqdec
                      (eqDec_rule eqDec_formula f_Lambek_log lambek_log eqDec_structr
                        f_Lambek lambek_str))
                    (atrefl eqDec_formula f_Lambek_log lambek_log eqDec_structr
                      f_Lambek lambek_str)
                    (LambekRules.coq_Topl::(LambekRules.coq_Botl::(LambekRules.coq_Conll::(LambekRules.coq_Conlr::(LambekRules.coq_Disl::(LambekRules.coq_Onel::(LambekRules.coq_Zerl::(LambekRules.coq_Fusl::(LambekRules.coq_Undl::(LambekRules.coq_Ovel::[]))))))))))
                    rR (fun _ -> assert false (* absurd case *)) (fun _ ->
                    eq_dec_in_list
                      (eqdec
                        (eqDec_rule eqDec_formula f_Lambek_log lambek_log eqDec_structr
                          f_Lambek lambek_str)) LambekRules.coq_Topl
                      (LambekRules.coq_Botl::(LambekRules.coq_Conll::(LambekRules.coq_Conlr::(LambekRules.coq_Disl::(LambekRules.coq_Onel::(LambekRules.coq_Zerl::(LambekRules.coq_Fusl::(LambekRules.coq_Undl::(LambekRules.coq_Ovel::[])))))))))
                      rR (fun _ -> assert false (* absurd case *)) (fun _ ->
                      eq_dec_in_list
                        (eqdec
                          (eqDec_rule eqDec_formula f_Lambek_log lambek_log
                            eqDec_structr f_Lambek lambek_str)) LambekRules.coq_Botl
                        (LambekRules.coq_Conll::(LambekRules.coq_Conlr::(LambekRules.coq_Disl::(LambekRules.coq_Onel::(LambekRules.coq_Zerl::(LambekRules.coq_Fusl::(LambekRules.coq_Undl::(LambekRules.coq_Ovel::[]))))))))
                        rR (fun _ -> assert false (* absurd case *)) (fun _ ->
                        eq_dec_in_list
                          (eqdec
                            (eqDec_rule eqDec_formula f_Lambek_log lambek_log
                              eqDec_structr f_Lambek lambek_str)) LambekRules.coq_Conll
                          (LambekRules.coq_Conlr::(LambekRules.coq_Disl::(LambekRules.coq_Onel::(LambekRules.coq_Zerl::(LambekRules.coq_Fusl::(LambekRules.coq_Undl::(LambekRules.coq_Ovel::[])))))))
                          rR (fun _ -> assert false (* absurd case *)) (fun _ ->
                          eq_dec_in_list
                            (eqdec
                              (eqDec_rule eqDec_formula f_Lambek_log lambek_log
                                eqDec_structr f_Lambek lambek_str))
                            LambekRules.coq_Conlr
                            (LambekRules.coq_Disl::(LambekRules.coq_Onel::(LambekRules.coq_Zerl::(LambekRules.coq_Fusl::(LambekRules.coq_Undl::(LambekRules.coq_Ovel::[]))))))
                            rR (fun _ -> assert false (* absurd case *)) (fun _ ->
                            eq_dec_in_list
                              (eqdec
                                (eqDec_rule eqDec_formula f_Lambek_log lambek_log
                                  eqDec_structr f_Lambek lambek_str))
                              LambekRules.coq_Disl
                              (LambekRules.coq_Onel::(LambekRules.coq_Zerl::(LambekRules.coq_Fusl::(LambekRules.coq_Undl::(LambekRules.coq_Ovel::[])))))
                              rR (fun _ ->
                              let hwfrL =
                                ruleInst_ruleSubst eqDec_formula f_Lambek_log
                                  lambek_log eqDec_structr f_Lambek lambek_str rL
                                  ((map
                                     (conclDT eqDec_formula f_Lambek_log lambek_log
                                       eqDec_structr f_Lambek lambek_str) lL),(Sequent
                                  (x, (lambek_str.fS a))))
                              in
                              let hwfrR =
                                ruleInst_ruleSubst eqDec_formula f_Lambek_log
                                  lambek_log eqDec_structr f_Lambek lambek_str rR
                                  ((map
                                     (conclDT eqDec_formula f_Lambek_log lambek_log
                                       eqDec_structr f_Lambek lambek_str) lR),(Sequent
                                  ((lambek_str.fS a), y)))
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
                                             coq_C8_Dis_r (snd hwfrL "X")
                                               (snd hwfrR "X") (snd (fst hwfrR) "A")
                                               (snd (fst hwfrR) "B") (d::(d0::(d1::[])))
                                           | _::_ -> assert false (* absurd case *))))
                                  | _::_ -> assert false (* absurd case *)))) (fun _ ->
                              eq_dec_in_list
                                (eqdec
                                  (eqDec_rule eqDec_formula f_Lambek_log lambek_log
                                    eqDec_structr f_Lambek lambek_str))
                                LambekRules.coq_Onel
                                (LambekRules.coq_Zerl::(LambekRules.coq_Fusl::(LambekRules.coq_Undl::(LambekRules.coq_Ovel::[]))))
                                rR (fun _ -> assert false (* absurd case *)) (fun _ ->
                                eq_dec_in_list
                                  (eqdec
                                    (eqDec_rule eqDec_formula f_Lambek_log lambek_log
                                      eqDec_structr f_Lambek lambek_str))
                                  LambekRules.coq_Zerl
                                  (LambekRules.coq_Fusl::(LambekRules.coq_Undl::(LambekRules.coq_Ovel::[])))
                                  rR (fun _ -> assert false (* absurd case *))
                                  (fun _ ->
                                  eq_dec_in_list
                                    (eqdec
                                      (eqDec_rule eqDec_formula f_Lambek_log lambek_log
                                        eqDec_structr f_Lambek lambek_str))
                                    LambekRules.coq_Fusl
                                    (LambekRules.coq_Undl::(LambekRules.coq_Ovel::[]))
                                    rR (fun _ -> assert false (* absurd case *))
                                    (fun _ ->
                                    eq_dec_in_list
                                      (eqdec
                                        (eqDec_rule eqDec_formula f_Lambek_log
                                          lambek_log eqDec_structr f_Lambek lambek_str))
                                      LambekRules.coq_Undl (LambekRules.coq_Ovel::[])
                                      rR (fun _ -> assert false (* absurd case *))
                                      (fun _ ->
                                      eq_dec_in_list
                                        (eqdec
                                          (eqDec_rule eqDec_formula f_Lambek_log
                                            lambek_log eqDec_structr f_Lambek
                                            lambek_str)) LambekRules.coq_Ovel [] rR
                                        (fun _ -> assert false (* absurd case *))
                                        (fun _ -> assert false (* absurd case *)))))))))))))
                  (fun _ ->
                  eq_dec_in_list
                    (eqdec
                      (eqDec_rule eqDec_formula f_Lambek_log lambek_log eqDec_structr
                        f_Lambek lambek_str)) LambekRules.coq_Oner
                    (LambekRules.coq_Zerr::(LambekRules.coq_Fusr::(LambekRules.coq_Undr::(LambekRules.coq_Over::[]))))
                    rL (fun _ ->
                    eq_dec_in_list
                      (eqdec
                        (eqDec_rule eqDec_formula f_Lambek_log lambek_log eqDec_structr
                          f_Lambek lambek_str))
                      (atrefl eqDec_formula f_Lambek_log lambek_log eqDec_structr
                        f_Lambek lambek_str)
                      (LambekRules.coq_Topl::(LambekRules.coq_Botl::(LambekRules.coq_Conll::(LambekRules.coq_Conlr::(LambekRules.coq_Disl::(LambekRules.coq_Onel::(LambekRules.coq_Zerl::(LambekRules.coq_Fusl::(LambekRules.coq_Undl::(LambekRules.coq_Ovel::[]))))))))))
                      rR (fun _ -> assert false (* absurd case *)) (fun _ ->
                      eq_dec_in_list
                        (eqdec
                          (eqDec_rule eqDec_formula f_Lambek_log lambek_log
                            eqDec_structr f_Lambek lambek_str)) LambekRules.coq_Topl
                        (LambekRules.coq_Botl::(LambekRules.coq_Conll::(LambekRules.coq_Conlr::(LambekRules.coq_Disl::(LambekRules.coq_Onel::(LambekRules.coq_Zerl::(LambekRules.coq_Fusl::(LambekRules.coq_Undl::(LambekRules.coq_Ovel::[])))))))))
                        rR (fun _ -> assert false (* absurd case *)) (fun _ ->
                        eq_dec_in_list
                          (eqdec
                            (eqDec_rule eqDec_formula f_Lambek_log lambek_log
                              eqDec_structr f_Lambek lambek_str)) LambekRules.coq_Botl
                          (LambekRules.coq_Conll::(LambekRules.coq_Conlr::(LambekRules.coq_Disl::(LambekRules.coq_Onel::(LambekRules.coq_Zerl::(LambekRules.coq_Fusl::(LambekRules.coq_Undl::(LambekRules.coq_Ovel::[]))))))))
                          rR (fun _ -> assert false (* absurd case *)) (fun _ ->
                          eq_dec_in_list
                            (eqdec
                              (eqDec_rule eqDec_formula f_Lambek_log lambek_log
                                eqDec_structr f_Lambek lambek_str))
                            LambekRules.coq_Conll
                            (LambekRules.coq_Conlr::(LambekRules.coq_Disl::(LambekRules.coq_Onel::(LambekRules.coq_Zerl::(LambekRules.coq_Fusl::(LambekRules.coq_Undl::(LambekRules.coq_Ovel::[])))))))
                            rR (fun _ -> assert false (* absurd case *)) (fun _ ->
                            eq_dec_in_list
                              (eqdec
                                (eqDec_rule eqDec_formula f_Lambek_log lambek_log
                                  eqDec_structr f_Lambek lambek_str))
                              LambekRules.coq_Conlr
                              (LambekRules.coq_Disl::(LambekRules.coq_Onel::(LambekRules.coq_Zerl::(LambekRules.coq_Fusl::(LambekRules.coq_Undl::(LambekRules.coq_Ovel::[]))))))
                              rR (fun _ -> assert false (* absurd case *)) (fun _ ->
                              eq_dec_in_list
                                (eqdec
                                  (eqDec_rule eqDec_formula f_Lambek_log lambek_log
                                    eqDec_structr f_Lambek lambek_str))
                                LambekRules.coq_Disl
                                (LambekRules.coq_Onel::(LambekRules.coq_Zerl::(LambekRules.coq_Fusl::(LambekRules.coq_Undl::(LambekRules.coq_Ovel::[])))))
                                rR (fun _ -> assert false (* absurd case *)) (fun _ ->
                                eq_dec_in_list
                                  (eqdec
                                    (eqDec_rule eqDec_formula f_Lambek_log lambek_log
                                      eqDec_structr f_Lambek lambek_str))
                                  LambekRules.coq_Onel
                                  (LambekRules.coq_Zerl::(LambekRules.coq_Fusl::(LambekRules.coq_Undl::(LambekRules.coq_Ovel::[]))))
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
                                      (eqDec_rule eqDec_formula f_Lambek_log lambek_log
                                        eqDec_structr f_Lambek lambek_str))
                                    LambekRules.coq_Zerl
                                    (LambekRules.coq_Fusl::(LambekRules.coq_Undl::(LambekRules.coq_Ovel::[])))
                                    rR (fun _ -> assert false (* absurd case *))
                                    (fun _ ->
                                    eq_dec_in_list
                                      (eqdec
                                        (eqDec_rule eqDec_formula f_Lambek_log
                                          lambek_log eqDec_structr f_Lambek lambek_str))
                                      LambekRules.coq_Fusl
                                      (LambekRules.coq_Undl::(LambekRules.coq_Ovel::[]))
                                      rR (fun _ -> assert false (* absurd case *))
                                      (fun _ ->
                                      eq_dec_in_list
                                        (eqdec
                                          (eqDec_rule eqDec_formula f_Lambek_log
                                            lambek_log eqDec_structr f_Lambek
                                            lambek_str)) LambekRules.coq_Undl
                                        (LambekRules.coq_Ovel::[]) rR (fun _ ->
                                        assert false (* absurd case *)) (fun _ ->
                                        eq_dec_in_list
                                          (eqdec
                                            (eqDec_rule eqDec_formula f_Lambek_log
                                              lambek_log eqDec_structr f_Lambek
                                              lambek_str)) LambekRules.coq_Ovel [] rR
                                          (fun _ -> assert false (* absurd case *))
                                          (fun _ -> assert false (* absurd case *)))))))))))))
                    (fun _ ->
                    eq_dec_in_list
                      (eqdec
                        (eqDec_rule eqDec_formula f_Lambek_log lambek_log eqDec_structr
                          f_Lambek lambek_str)) LambekRules.coq_Zerr
                      (LambekRules.coq_Fusr::(LambekRules.coq_Undr::(LambekRules.coq_Over::[])))
                      rL (fun _ ->
                      eq_dec_in_list
                        (eqdec
                          (eqDec_rule eqDec_formula f_Lambek_log lambek_log
                            eqDec_structr f_Lambek lambek_str))
                        (atrefl eqDec_formula f_Lambek_log lambek_log eqDec_structr
                          f_Lambek lambek_str)
                        (LambekRules.coq_Topl::(LambekRules.coq_Botl::(LambekRules.coq_Conll::(LambekRules.coq_Conlr::(LambekRules.coq_Disl::(LambekRules.coq_Onel::(LambekRules.coq_Zerl::(LambekRules.coq_Fusl::(LambekRules.coq_Undl::(LambekRules.coq_Ovel::[]))))))))))
                        rR (fun _ -> assert false (* absurd case *)) (fun _ ->
                        eq_dec_in_list
                          (eqdec
                            (eqDec_rule eqDec_formula f_Lambek_log lambek_log
                              eqDec_structr f_Lambek lambek_str)) LambekRules.coq_Topl
                          (LambekRules.coq_Botl::(LambekRules.coq_Conll::(LambekRules.coq_Conlr::(LambekRules.coq_Disl::(LambekRules.coq_Onel::(LambekRules.coq_Zerl::(LambekRules.coq_Fusl::(LambekRules.coq_Undl::(LambekRules.coq_Ovel::[])))))))))
                          rR (fun _ -> assert false (* absurd case *)) (fun _ ->
                          eq_dec_in_list
                            (eqdec
                              (eqDec_rule eqDec_formula f_Lambek_log lambek_log
                                eqDec_structr f_Lambek lambek_str))
                            LambekRules.coq_Botl
                            (LambekRules.coq_Conll::(LambekRules.coq_Conlr::(LambekRules.coq_Disl::(LambekRules.coq_Onel::(LambekRules.coq_Zerl::(LambekRules.coq_Fusl::(LambekRules.coq_Undl::(LambekRules.coq_Ovel::[]))))))))
                            rR (fun _ -> assert false (* absurd case *)) (fun _ ->
                            eq_dec_in_list
                              (eqdec
                                (eqDec_rule eqDec_formula f_Lambek_log lambek_log
                                  eqDec_structr f_Lambek lambek_str))
                              LambekRules.coq_Conll
                              (LambekRules.coq_Conlr::(LambekRules.coq_Disl::(LambekRules.coq_Onel::(LambekRules.coq_Zerl::(LambekRules.coq_Fusl::(LambekRules.coq_Undl::(LambekRules.coq_Ovel::[])))))))
                              rR (fun _ -> assert false (* absurd case *)) (fun _ ->
                              eq_dec_in_list
                                (eqdec
                                  (eqDec_rule eqDec_formula f_Lambek_log lambek_log
                                    eqDec_structr f_Lambek lambek_str))
                                LambekRules.coq_Conlr
                                (LambekRules.coq_Disl::(LambekRules.coq_Onel::(LambekRules.coq_Zerl::(LambekRules.coq_Fusl::(LambekRules.coq_Undl::(LambekRules.coq_Ovel::[]))))))
                                rR (fun _ -> assert false (* absurd case *)) (fun _ ->
                                eq_dec_in_list
                                  (eqdec
                                    (eqDec_rule eqDec_formula f_Lambek_log lambek_log
                                      eqDec_structr f_Lambek lambek_str))
                                  LambekRules.coq_Disl
                                  (LambekRules.coq_Onel::(LambekRules.coq_Zerl::(LambekRules.coq_Fusl::(LambekRules.coq_Undl::(LambekRules.coq_Ovel::[])))))
                                  rR (fun _ -> assert false (* absurd case *))
                                  (fun _ ->
                                  eq_dec_in_list
                                    (eqdec
                                      (eqDec_rule eqDec_formula f_Lambek_log lambek_log
                                        eqDec_structr f_Lambek lambek_str))
                                    LambekRules.coq_Onel
                                    (LambekRules.coq_Zerl::(LambekRules.coq_Fusl::(LambekRules.coq_Undl::(LambekRules.coq_Ovel::[]))))
                                    rR (fun _ -> assert false (* absurd case *))
                                    (fun _ ->
                                    eq_dec_in_list
                                      (eqdec
                                        (eqDec_rule eqDec_formula f_Lambek_log
                                          lambek_log eqDec_structr f_Lambek lambek_str))
                                      LambekRules.coq_Zerl
                                      (LambekRules.coq_Fusl::(LambekRules.coq_Undl::(LambekRules.coq_Ovel::[])))
                                      rR (fun _ ->
                                      match lL with
                                      | [] -> assert false (* absurd case *)
                                      | d::l ->
                                        (match l with
                                         | [] ->
                                           (match lR with
                                            | [] -> d
                                            | _::_ -> assert false (* absurd case *))
                                         | _::_ -> assert false (* absurd case *)))
                                      (fun _ ->
                                      eq_dec_in_list
                                        (eqdec
                                          (eqDec_rule eqDec_formula f_Lambek_log
                                            lambek_log eqDec_structr f_Lambek
                                            lambek_str)) LambekRules.coq_Fusl
                                        (LambekRules.coq_Undl::(LambekRules.coq_Ovel::[]))
                                        rR (fun _ -> assert false (* absurd case *))
                                        (fun _ ->
                                        eq_dec_in_list
                                          (eqdec
                                            (eqDec_rule eqDec_formula f_Lambek_log
                                              lambek_log eqDec_structr f_Lambek
                                              lambek_str)) LambekRules.coq_Undl
                                          (LambekRules.coq_Ovel::[]) rR (fun _ ->
                                          assert false (* absurd case *)) (fun _ ->
                                          eq_dec_in_list
                                            (eqdec
                                              (eqDec_rule eqDec_formula f_Lambek_log
                                                lambek_log eqDec_structr f_Lambek
                                                lambek_str)) LambekRules.coq_Ovel [] rR
                                            (fun _ -> assert false (* absurd case *))
                                            (fun _ -> assert false (* absurd case *)))))))))))))
                      (fun _ ->
                      eq_dec_in_list
                        (eqdec
                          (eqDec_rule eqDec_formula f_Lambek_log lambek_log
                            eqDec_structr f_Lambek lambek_str)) LambekRules.coq_Fusr
                        (LambekRules.coq_Undr::(LambekRules.coq_Over::[])) rL (fun _ ->
                        eq_dec_in_list
                          (eqdec
                            (eqDec_rule eqDec_formula f_Lambek_log lambek_log
                              eqDec_structr f_Lambek lambek_str))
                          (atrefl eqDec_formula f_Lambek_log lambek_log eqDec_structr
                            f_Lambek lambek_str)
                          (LambekRules.coq_Topl::(LambekRules.coq_Botl::(LambekRules.coq_Conll::(LambekRules.coq_Conlr::(LambekRules.coq_Disl::(LambekRules.coq_Onel::(LambekRules.coq_Zerl::(LambekRules.coq_Fusl::(LambekRules.coq_Undl::(LambekRules.coq_Ovel::[]))))))))))
                          rR (fun _ -> assert false (* absurd case *)) (fun _ ->
                          eq_dec_in_list
                            (eqdec
                              (eqDec_rule eqDec_formula f_Lambek_log lambek_log
                                eqDec_structr f_Lambek lambek_str))
                            LambekRules.coq_Topl
                            (LambekRules.coq_Botl::(LambekRules.coq_Conll::(LambekRules.coq_Conlr::(LambekRules.coq_Disl::(LambekRules.coq_Onel::(LambekRules.coq_Zerl::(LambekRules.coq_Fusl::(LambekRules.coq_Undl::(LambekRules.coq_Ovel::[])))))))))
                            rR (fun _ -> assert false (* absurd case *)) (fun _ ->
                            eq_dec_in_list
                              (eqdec
                                (eqDec_rule eqDec_formula f_Lambek_log lambek_log
                                  eqDec_structr f_Lambek lambek_str))
                              LambekRules.coq_Botl
                              (LambekRules.coq_Conll::(LambekRules.coq_Conlr::(LambekRules.coq_Disl::(LambekRules.coq_Onel::(LambekRules.coq_Zerl::(LambekRules.coq_Fusl::(LambekRules.coq_Undl::(LambekRules.coq_Ovel::[]))))))))
                              rR (fun _ -> assert false (* absurd case *)) (fun _ ->
                              eq_dec_in_list
                                (eqdec
                                  (eqDec_rule eqDec_formula f_Lambek_log lambek_log
                                    eqDec_structr f_Lambek lambek_str))
                                LambekRules.coq_Conll
                                (LambekRules.coq_Conlr::(LambekRules.coq_Disl::(LambekRules.coq_Onel::(LambekRules.coq_Zerl::(LambekRules.coq_Fusl::(LambekRules.coq_Undl::(LambekRules.coq_Ovel::[])))))))
                                rR (fun _ -> assert false (* absurd case *)) (fun _ ->
                                eq_dec_in_list
                                  (eqdec
                                    (eqDec_rule eqDec_formula f_Lambek_log lambek_log
                                      eqDec_structr f_Lambek lambek_str))
                                  LambekRules.coq_Conlr
                                  (LambekRules.coq_Disl::(LambekRules.coq_Onel::(LambekRules.coq_Zerl::(LambekRules.coq_Fusl::(LambekRules.coq_Undl::(LambekRules.coq_Ovel::[]))))))
                                  rR (fun _ -> assert false (* absurd case *))
                                  (fun _ ->
                                  eq_dec_in_list
                                    (eqdec
                                      (eqDec_rule eqDec_formula f_Lambek_log lambek_log
                                        eqDec_structr f_Lambek lambek_str))
                                    LambekRules.coq_Disl
                                    (LambekRules.coq_Onel::(LambekRules.coq_Zerl::(LambekRules.coq_Fusl::(LambekRules.coq_Undl::(LambekRules.coq_Ovel::[])))))
                                    rR (fun _ -> assert false (* absurd case *))
                                    (fun _ ->
                                    eq_dec_in_list
                                      (eqdec
                                        (eqDec_rule eqDec_formula f_Lambek_log
                                          lambek_log eqDec_structr f_Lambek lambek_str))
                                      LambekRules.coq_Onel
                                      (LambekRules.coq_Zerl::(LambekRules.coq_Fusl::(LambekRules.coq_Undl::(LambekRules.coq_Ovel::[]))))
                                      rR (fun _ -> assert false (* absurd case *))
                                      (fun _ ->
                                      eq_dec_in_list
                                        (eqdec
                                          (eqDec_rule eqDec_formula f_Lambek_log
                                            lambek_log eqDec_structr f_Lambek
                                            lambek_str)) LambekRules.coq_Zerl
                                        (LambekRules.coq_Fusl::(LambekRules.coq_Undl::(LambekRules.coq_Ovel::[])))
                                        rR (fun _ -> assert false (* absurd case *))
                                        (fun _ ->
                                        eq_dec_in_list
                                          (eqdec
                                            (eqDec_rule eqDec_formula f_Lambek_log
                                              lambek_log eqDec_structr f_Lambek
                                              lambek_str)) LambekRules.coq_Fusl
                                          (LambekRules.coq_Undl::(LambekRules.coq_Ovel::[]))
                                          rR (fun _ ->
                                          let hwfrL =
                                            ruleInst_ruleSubst eqDec_formula
                                              f_Lambek_log lambek_log eqDec_structr
                                              f_Lambek lambek_str rL
                                              ((map
                                                 (conclDT eqDec_formula f_Lambek_log
                                                   lambek_log eqDec_structr f_Lambek
                                                   lambek_str) lL),(Sequent (x,
                                              (lambek_str.fS a))))
                                          in
                                          let hwfrR =
                                            ruleInst_ruleSubst eqDec_formula
                                              f_Lambek_log lambek_log eqDec_structr
                                              f_Lambek lambek_str rR
                                              ((map
                                                 (conclDT eqDec_formula f_Lambek_log
                                                   lambek_log eqDec_structr f_Lambek
                                                   lambek_str) lR),(Sequent
                                              ((lambek_str.fS a), y)))
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
                                                    | [] ->
                                                      assert false (* absurd case *)
                                                    | d1::l1 ->
                                                      (match l1 with
                                                       | [] ->
                                                         coq_C8_Fus (snd hwfrL "X")
                                                           (snd hwfrL "Y")
                                                           (snd hwfrR "X")
                                                           (snd (fst hwfrR) "A")
                                                           (snd (fst hwfrR) "B")
                                                           (d::(d0::(d1::[])))
                                                       | _::_ ->
                                                         assert false (* absurd case *)))
                                                 | _::_ ->
                                                   assert false (* absurd case *)))))
                                          (fun _ ->
                                          eq_dec_in_list
                                            (eqdec
                                              (eqDec_rule eqDec_formula f_Lambek_log
                                                lambek_log eqDec_structr f_Lambek
                                                lambek_str)) LambekRules.coq_Undl
                                            (LambekRules.coq_Ovel::[]) rR (fun _ ->
                                            assert false (* absurd case *)) (fun _ ->
                                            eq_dec_in_list
                                              (eqdec
                                                (eqDec_rule eqDec_formula f_Lambek_log
                                                  lambek_log eqDec_structr f_Lambek
                                                  lambek_str)) LambekRules.coq_Ovel []
                                              rR (fun _ -> assert false
                                              (* absurd case *)) (fun _ -> assert false
                                              (* absurd case *))))))))))))) (fun _ ->
                        eq_dec_in_list
                          (eqdec
                            (eqDec_rule eqDec_formula f_Lambek_log lambek_log
                              eqDec_structr f_Lambek lambek_str)) LambekRules.coq_Undr
                          (LambekRules.coq_Over::[]) rL (fun _ ->
                          eq_dec_in_list
                            (eqdec
                              (eqDec_rule eqDec_formula f_Lambek_log lambek_log
                                eqDec_structr f_Lambek lambek_str))
                            (atrefl eqDec_formula f_Lambek_log lambek_log eqDec_structr
                              f_Lambek lambek_str)
                            (LambekRules.coq_Topl::(LambekRules.coq_Botl::(LambekRules.coq_Conll::(LambekRules.coq_Conlr::(LambekRules.coq_Disl::(LambekRules.coq_Onel::(LambekRules.coq_Zerl::(LambekRules.coq_Fusl::(LambekRules.coq_Undl::(LambekRules.coq_Ovel::[]))))))))))
                            rR (fun _ -> assert false (* absurd case *)) (fun _ ->
                            eq_dec_in_list
                              (eqdec
                                (eqDec_rule eqDec_formula f_Lambek_log lambek_log
                                  eqDec_structr f_Lambek lambek_str))
                              LambekRules.coq_Topl
                              (LambekRules.coq_Botl::(LambekRules.coq_Conll::(LambekRules.coq_Conlr::(LambekRules.coq_Disl::(LambekRules.coq_Onel::(LambekRules.coq_Zerl::(LambekRules.coq_Fusl::(LambekRules.coq_Undl::(LambekRules.coq_Ovel::[])))))))))
                              rR (fun _ -> assert false (* absurd case *)) (fun _ ->
                              eq_dec_in_list
                                (eqdec
                                  (eqDec_rule eqDec_formula f_Lambek_log lambek_log
                                    eqDec_structr f_Lambek lambek_str))
                                LambekRules.coq_Botl
                                (LambekRules.coq_Conll::(LambekRules.coq_Conlr::(LambekRules.coq_Disl::(LambekRules.coq_Onel::(LambekRules.coq_Zerl::(LambekRules.coq_Fusl::(LambekRules.coq_Undl::(LambekRules.coq_Ovel::[]))))))))
                                rR (fun _ -> assert false (* absurd case *)) (fun _ ->
                                eq_dec_in_list
                                  (eqdec
                                    (eqDec_rule eqDec_formula f_Lambek_log lambek_log
                                      eqDec_structr f_Lambek lambek_str))
                                  LambekRules.coq_Conll
                                  (LambekRules.coq_Conlr::(LambekRules.coq_Disl::(LambekRules.coq_Onel::(LambekRules.coq_Zerl::(LambekRules.coq_Fusl::(LambekRules.coq_Undl::(LambekRules.coq_Ovel::[])))))))
                                  rR (fun _ -> assert false (* absurd case *))
                                  (fun _ ->
                                  eq_dec_in_list
                                    (eqdec
                                      (eqDec_rule eqDec_formula f_Lambek_log lambek_log
                                        eqDec_structr f_Lambek lambek_str))
                                    LambekRules.coq_Conlr
                                    (LambekRules.coq_Disl::(LambekRules.coq_Onel::(LambekRules.coq_Zerl::(LambekRules.coq_Fusl::(LambekRules.coq_Undl::(LambekRules.coq_Ovel::[]))))))
                                    rR (fun _ -> assert false (* absurd case *))
                                    (fun _ ->
                                    eq_dec_in_list
                                      (eqdec
                                        (eqDec_rule eqDec_formula f_Lambek_log
                                          lambek_log eqDec_structr f_Lambek lambek_str))
                                      LambekRules.coq_Disl
                                      (LambekRules.coq_Onel::(LambekRules.coq_Zerl::(LambekRules.coq_Fusl::(LambekRules.coq_Undl::(LambekRules.coq_Ovel::[])))))
                                      rR (fun _ -> assert false (* absurd case *))
                                      (fun _ ->
                                      eq_dec_in_list
                                        (eqdec
                                          (eqDec_rule eqDec_formula f_Lambek_log
                                            lambek_log eqDec_structr f_Lambek
                                            lambek_str)) LambekRules.coq_Onel
                                        (LambekRules.coq_Zerl::(LambekRules.coq_Fusl::(LambekRules.coq_Undl::(LambekRules.coq_Ovel::[]))))
                                        rR (fun _ -> assert false (* absurd case *))
                                        (fun _ ->
                                        eq_dec_in_list
                                          (eqdec
                                            (eqDec_rule eqDec_formula f_Lambek_log
                                              lambek_log eqDec_structr f_Lambek
                                              lambek_str)) LambekRules.coq_Zerl
                                          (LambekRules.coq_Fusl::(LambekRules.coq_Undl::(LambekRules.coq_Ovel::[])))
                                          rR (fun _ -> assert false (* absurd case *))
                                          (fun _ ->
                                          eq_dec_in_list
                                            (eqdec
                                              (eqDec_rule eqDec_formula f_Lambek_log
                                                lambek_log eqDec_structr f_Lambek
                                                lambek_str)) LambekRules.coq_Fusl
                                            (LambekRules.coq_Undl::(LambekRules.coq_Ovel::[]))
                                            rR (fun _ -> assert false
                                            (* absurd case *)) (fun _ ->
                                            eq_dec_in_list
                                              (eqdec
                                                (eqDec_rule eqDec_formula f_Lambek_log
                                                  lambek_log eqDec_structr f_Lambek
                                                  lambek_str)) LambekRules.coq_Undl
                                              (LambekRules.coq_Ovel::[]) rR (fun _ ->
                                              let hwfrL =
                                                ruleInst_ruleSubst eqDec_formula
                                                  f_Lambek_log lambek_log eqDec_structr
                                                  f_Lambek lambek_str rL
                                                  ((map
                                                     (conclDT eqDec_formula
                                                       f_Lambek_log lambek_log
                                                       eqDec_structr f_Lambek
                                                       lambek_str) lL),(Sequent (x,
                                                  (lambek_str.fS a))))
                                              in
                                              let hwfrR =
                                                ruleInst_ruleSubst eqDec_formula
                                                  f_Lambek_log lambek_log eqDec_structr
                                                  f_Lambek lambek_str rR
                                                  ((map
                                                     (conclDT eqDec_formula
                                                       f_Lambek_log lambek_log
                                                       eqDec_structr f_Lambek
                                                       lambek_str) lR),(Sequent
                                                  ((lambek_str.fS a), y)))
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
                                                             coq_C8_Und (snd hwfrL "X")
                                                               (snd hwfrR "X")
                                                               (snd hwfrR "Y")
                                                               (snd (fst hwfrR) "A")
                                                               (snd (fst hwfrR) "B")
                                                               (d::(d0::(d1::[])))
                                                           | _::_ ->
                                                             assert false
                                                               (* absurd case *))))
                                                  | _::_ ->
                                                    assert false (* absurd case *))))
                                              (fun _ ->
                                              eq_dec_in_list
                                                (eqdec
                                                  (eqDec_rule eqDec_formula
                                                    f_Lambek_log lambek_log
                                                    eqDec_structr f_Lambek lambek_str))
                                                LambekRules.coq_Ovel [] rR (fun _ ->
                                                assert false (* absurd case *))
                                                (fun _ -> assert false
                                                (* absurd case *))))))))))))) (fun _ ->
                          eq_dec_in_list
                            (eqdec
                              (eqDec_rule eqDec_formula f_Lambek_log lambek_log
                                eqDec_structr f_Lambek lambek_str))
                            LambekRules.coq_Over [] rL (fun _ ->
                            eq_dec_in_list
                              (eqdec
                                (eqDec_rule eqDec_formula f_Lambek_log lambek_log
                                  eqDec_structr f_Lambek lambek_str))
                              (atrefl eqDec_formula f_Lambek_log lambek_log
                                eqDec_structr f_Lambek lambek_str)
                              (LambekRules.coq_Topl::(LambekRules.coq_Botl::(LambekRules.coq_Conll::(LambekRules.coq_Conlr::(LambekRules.coq_Disl::(LambekRules.coq_Onel::(LambekRules.coq_Zerl::(LambekRules.coq_Fusl::(LambekRules.coq_Undl::(LambekRules.coq_Ovel::[]))))))))))
                              rR (fun _ -> assert false (* absurd case *)) (fun _ ->
                              eq_dec_in_list
                                (eqdec
                                  (eqDec_rule eqDec_formula f_Lambek_log lambek_log
                                    eqDec_structr f_Lambek lambek_str))
                                LambekRules.coq_Topl
                                (LambekRules.coq_Botl::(LambekRules.coq_Conll::(LambekRules.coq_Conlr::(LambekRules.coq_Disl::(LambekRules.coq_Onel::(LambekRules.coq_Zerl::(LambekRules.coq_Fusl::(LambekRules.coq_Undl::(LambekRules.coq_Ovel::[])))))))))
                                rR (fun _ -> assert false (* absurd case *)) (fun _ ->
                                eq_dec_in_list
                                  (eqdec
                                    (eqDec_rule eqDec_formula f_Lambek_log lambek_log
                                      eqDec_structr f_Lambek lambek_str))
                                  LambekRules.coq_Botl
                                  (LambekRules.coq_Conll::(LambekRules.coq_Conlr::(LambekRules.coq_Disl::(LambekRules.coq_Onel::(LambekRules.coq_Zerl::(LambekRules.coq_Fusl::(LambekRules.coq_Undl::(LambekRules.coq_Ovel::[]))))))))
                                  rR (fun _ -> assert false (* absurd case *))
                                  (fun _ ->
                                  eq_dec_in_list
                                    (eqdec
                                      (eqDec_rule eqDec_formula f_Lambek_log lambek_log
                                        eqDec_structr f_Lambek lambek_str))
                                    LambekRules.coq_Conll
                                    (LambekRules.coq_Conlr::(LambekRules.coq_Disl::(LambekRules.coq_Onel::(LambekRules.coq_Zerl::(LambekRules.coq_Fusl::(LambekRules.coq_Undl::(LambekRules.coq_Ovel::[])))))))
                                    rR (fun _ -> assert false (* absurd case *))
                                    (fun _ ->
                                    eq_dec_in_list
                                      (eqdec
                                        (eqDec_rule eqDec_formula f_Lambek_log
                                          lambek_log eqDec_structr f_Lambek lambek_str))
                                      LambekRules.coq_Conlr
                                      (LambekRules.coq_Disl::(LambekRules.coq_Onel::(LambekRules.coq_Zerl::(LambekRules.coq_Fusl::(LambekRules.coq_Undl::(LambekRules.coq_Ovel::[]))))))
                                      rR (fun _ -> assert false (* absurd case *))
                                      (fun _ ->
                                      eq_dec_in_list
                                        (eqdec
                                          (eqDec_rule eqDec_formula f_Lambek_log
                                            lambek_log eqDec_structr f_Lambek
                                            lambek_str)) LambekRules.coq_Disl
                                        (LambekRules.coq_Onel::(LambekRules.coq_Zerl::(LambekRules.coq_Fusl::(LambekRules.coq_Undl::(LambekRules.coq_Ovel::[])))))
                                        rR (fun _ -> assert false (* absurd case *))
                                        (fun _ ->
                                        eq_dec_in_list
                                          (eqdec
                                            (eqDec_rule eqDec_formula f_Lambek_log
                                              lambek_log eqDec_structr f_Lambek
                                              lambek_str)) LambekRules.coq_Onel
                                          (LambekRules.coq_Zerl::(LambekRules.coq_Fusl::(LambekRules.coq_Undl::(LambekRules.coq_Ovel::[]))))
                                          rR (fun _ -> assert false (* absurd case *))
                                          (fun _ ->
                                          eq_dec_in_list
                                            (eqdec
                                              (eqDec_rule eqDec_formula f_Lambek_log
                                                lambek_log eqDec_structr f_Lambek
                                                lambek_str)) LambekRules.coq_Zerl
                                            (LambekRules.coq_Fusl::(LambekRules.coq_Undl::(LambekRules.coq_Ovel::[])))
                                            rR (fun _ -> assert false
                                            (* absurd case *)) (fun _ ->
                                            eq_dec_in_list
                                              (eqdec
                                                (eqDec_rule eqDec_formula f_Lambek_log
                                                  lambek_log eqDec_structr f_Lambek
                                                  lambek_str)) LambekRules.coq_Fusl
                                              (LambekRules.coq_Undl::(LambekRules.coq_Ovel::[]))
                                              rR (fun _ -> assert false
                                              (* absurd case *)) (fun _ ->
                                              eq_dec_in_list
                                                (eqdec
                                                  (eqDec_rule eqDec_formula
                                                    f_Lambek_log lambek_log
                                                    eqDec_structr f_Lambek lambek_str))
                                                LambekRules.coq_Undl
                                                (LambekRules.coq_Ovel::[]) rR (fun _ ->
                                                assert false (* absurd case *))
                                                (fun _ ->
                                                eq_dec_in_list
                                                  (eqdec
                                                    (eqDec_rule eqDec_formula
                                                      f_Lambek_log lambek_log
                                                      eqDec_structr f_Lambek lambek_str))
                                                  LambekRules.coq_Ovel [] rR (fun _ ->
                                                  let hwfrL =
                                                    ruleInst_ruleSubst eqDec_formula
                                                      f_Lambek_log lambek_log
                                                      eqDec_structr f_Lambek lambek_str
                                                      rL
                                                      ((map
                                                         (conclDT eqDec_formula
                                                           f_Lambek_log lambek_log
                                                           eqDec_structr f_Lambek
                                                           lambek_str) lL),(Sequent (x,
                                                      (lambek_str.fS a))))
                                                  in
                                                  let hwfrR =
                                                    ruleInst_ruleSubst eqDec_formula
                                                      f_Lambek_log lambek_log
                                                      eqDec_structr f_Lambek lambek_str
                                                      rR
                                                      ((map
                                                         (conclDT eqDec_formula
                                                           f_Lambek_log lambek_log
                                                           eqDec_structr f_Lambek
                                                           lambek_str) lR),(Sequent
                                                      ((lambek_str.fS a), y)))
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
                                                              assert false
                                                                (* absurd case *)
                                                            | d1::l1 ->
                                                              (match l1 with
                                                               | [] ->
                                                                 coq_C8_Ove
                                                                   (snd hwfrL "X")
                                                                   (snd hwfrR "X")
                                                                   (snd hwfrR "Y")
                                                                   (snd (fst hwfrR) "A")
                                                                   (snd (fst hwfrR) "B")
                                                                   (d::(d0::(d1::[])))
                                                               | _::_ ->
                                                                 assert false
                                                                   (* absurd case *))))
                                                      | _::_ ->
                                                        assert false (* absurd case *))))
                                                  (fun _ -> assert false
                                                  (* absurd case *)))))))))))))
                            (fun _ -> assert false (* absurd case *))))))))))))) m dt
 end

(** val lambek_DCBel : (Lambek.formula, Lambek.structr) bELNAP **)

let lambek_DCBel x x0 _ _ _ =
  LambekBelnap.coq_C8_holds x x0

(** val lambek_cutElim :
    (Lambek.formula, Lambek.structr) dertree -> (Lambek.formula, Lambek.structr) dertree **)

let lambek_cutElim dt =
  cutElim eqDec_formula f_Lambek_log lambek_log eqDec_structr f_Lambek lambek_str
    lambek_DC lambek_DCBel dt

(** val derr_ex_rule : (Lambek.formula, Lambek.structr) derivRule **)

let derr_ex_rule =
  let p = Lambek.Atf "p" in
  let q = Lambek.Atf "q" in
  Der ((Sequent ((Lambek.FSf (Lambek.Fus ((Lambek.Ove (p, q)), q))), (Lambek.FSf
  (Lambek.Und ((Lambek.Ove (q, p)), q))))),
  (cUT eqDec_formula f_Lambek_log lambek_log eqDec_structr f_Lambek lambek_str), ((Der
  ((Sequent ((Lambek.FSf (Lambek.Fus ((Lambek.Ove (p, q)), q))), (Lambek.FSf p))),
  LambekRules.coq_Fusl, ((Der ((Sequent ((Lambek.Smc ((Lambek.FSf (Lambek.Ove (p, q))),
  (Lambek.FSf q))), (Lambek.FSf p))), LambekRules.coq_Rlesmr, ((Der ((Sequent
  ((Lambek.FSf (Lambek.Ove (p, q))), (Lambek.Les ((Lambek.FSf p), (Lambek.FSf q))))),
  LambekRules.coq_Ovel, ((Der ((Sequent ((Lambek.FSf p), (Lambek.FSf p))),
  (atrefl eqDec_formula f_Lambek_log lambek_log eqDec_structr f_Lambek lambek_str),
  []))::((Der ((Sequent ((Lambek.FSf q), (Lambek.FSf q))),
  (atrefl eqDec_formula f_Lambek_log lambek_log eqDec_structr f_Lambek lambek_str),
  []))::[]))))::[])))::[])))::((Der ((Sequent ((Lambek.FSf p), (Lambek.FSf (Lambek.Und
  ((Lambek.Ove (q, p)), q))))), LambekRules.coq_Undr, ((Der ((Sequent ((Lambek.FSf p),
  (Lambek.Gre ((Lambek.FSf (Lambek.Ove (q, p))), (Lambek.FSf q))))),
  LambekRules.coq_Rsmgel, ((Der ((Sequent ((Lambek.Smc ((Lambek.FSf (Lambek.Ove (q,
  p))), (Lambek.FSf p))), (Lambek.FSf q))), LambekRules.coq_Rlesmr, ((Der ((Sequent
  ((Lambek.FSf (Lambek.Ove (q, p))), (Lambek.Les ((Lambek.FSf q), (Lambek.FSf p))))),
  LambekRules.coq_Ovel, ((Der ((Sequent ((Lambek.FSf q), (Lambek.FSf q))),
  (atrefl eqDec_formula f_Lambek_log lambek_log eqDec_structr f_Lambek lambek_str),
  []))::((Der ((Sequent ((Lambek.FSf p), (Lambek.FSf p))),
  (atrefl eqDec_formula f_Lambek_log lambek_log eqDec_structr f_Lambek lambek_str),
  []))::[]))))::[])))::[])))::[])))::[])))
