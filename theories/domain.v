From mathcomp
Require Import
  ssreflect ssrfun ssrbool ssrnat seq eqtype choice fintype generic_quotient.

From extructures
Require Import ord fset fmap.

Require Import void nominal.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Delimit Scope dom_scope with dom.

Reserved Notation "x ⊑ y" (at level 50, no associativity).
Reserved Notation "x ⊏ y" (at level 50, no associativity).
Reserved Notation "x ⋢ y" (at level 50, no associativity).
Reserved Notation "x ⊑ y ⊑ z" (at level 50, y at next level, no associativity).
Reserved Notation "⊥" (at level 0).
Reserved Notation "x ⊔ y" (at level 40, left associativity).

Local Open Scope fset_scope.
Local Open Scope quotient_scope.

Obligation Tactic := idtac.

(* TODO:

- Port generic set and map lemmas and declarations to extructures.

- Change set variables from xs to X

- Simplify the definition of continuous functions to use that of plain
functions.

- Define a total version of lub.

- Define a quotient instance for cont.

- Have a separate upper-bound predicate

*)

Arguments imfsetP {_ _} [_ _ _].
Arguments fsubsetP {_} [_ _].
Arguments fset2P {_} [_ _ _].

Section Sets.

Variables T S : ordType.
Implicit Types (f : T -> S) (X : {fset T}).

Lemma imfset_fset f s : f @: fset s = fset [seq f x | x <- s].
Proof.
apply/eq_fset=> x; rewrite in_fset.
apply/(sameP imfsetP)/(iffP mapP).
- by case=> {x} x xin ->; exists x; rewrite ?in_fset.
- by case=> {x} x xin ->; exists x; rewrite -1?in_fset.
Qed.

Lemma imfset_eq0 f X : (f @: X == fset0) = (X == fset0).
Proof.
apply/(sameP idP)/(iffP idP)=> [/eqP ->|]; first by rewrite imfset0.
apply: contraTT; case/fset0Pn=> x xX; apply/fset0Pn; exists (f x).
by rewrite mem_imfset.
Qed.

Lemma fsvalK : cancel val (@fset T).
Proof. by move=> X; apply/eq_fset=> x; rewrite in_fset. Qed.

End Sets.

Section Maps.

Implicit Types (T : ordType) (S : Type).

Definition mapm2 T T' S S' f g (m : {fmap T -> S}) : {fmap T' -> S'} :=
  mkfmap [seq (f p.1, g p.2) | p <- m].

Lemma mapm2E T T' S S' (f : T -> T') (g : S -> S') m x :
  injective f ->
  mapm2 f g m (f x) = omap g (m x).
Proof.
rewrite /mapm2 => f_inj; rewrite mkfmapE /getm.
case: m=> [/= m _]; elim: m=> [|[x' y] m IH] //=.
by rewrite (inj_eq f_inj) [in RHS]fun_if IH.
Qed.

Lemma domm_map2 T T' S S' (f : T -> T') (g : S -> S') m :
  domm (mapm2 f g m) = f @: domm m.
Proof.
apply/eq_fset=> x; rewrite /mapm2 domm_mkfmap /unzip1 -map_comp /comp /=.
by rewrite /domm imfset_fset in_fset -map_comp.
Qed.

Lemma mapm2_comp T T' T'' S S' S'' f f' g g' :
  injective f  ->
  injective f' ->
  mapm2 (f' \o f) (g' \o g) =1
  @mapm2 T' T'' S' T'' f' g' \o @mapm2 T T' S S' f g.
Proof.
move=> f_inj f'_inj m; apply/eq_fmap=> x /=.
have [|xnin] := boolP (x \in domm (mapm2 (f' \o f) (g' \o g) m)).
- rewrite domm_map2; case/imfsetP=> {x} x xin ->.
  rewrite mapm2E /=; last exact: inj_comp.
  by rewrite !mapm2E //; case: (m x).
- move: (xnin); rewrite (dommPn _ _ xnin).
  rewrite !domm_map2 // imfset_comp -(domm_map2 f g) -(domm_map2 f' g').
  by move/dommPn=> ->.
Qed.

End Maps.

Arguments dommP {_ _} [_ _].
Arguments dommPn {_ _} [_ _].

Module Po.

Section ClassDef.

Record axioms_of anti T (appr : rel T) := Ax {
  _ : reflexive appr;
  _ : transitive appr;
  _ : if anti then antisymmetric appr else True
}.

Record mixin_of anti T := Mixin {
  appr : rel T;
  _    : axioms_of anti appr
}.

Record class_of anti T := Class {
  base  : Ord.class_of T;
  mixin : mixin_of anti T
}.
Local Coercion base : class_of >-> Ord.class_of.

Structure type anti := Pack {sort; _ : class_of anti sort}.
Local Coercion sort : type >-> Sortclass.
Variables (anti : bool) (T : Type) (cT : type anti).
Definition class := let: Pack _ c as cT' := cT return class_of anti cT' in c.
Definition clone c of phant_id class c := @Pack anti T c.
Let xT := let: Pack T _ := cT in T.
Notation xclass := (class : class_of anti xT).

Definition pack m :=
  fun b bT & phant_id (Ord.class bT) b => Pack (@Class anti T b m).

(* Inheritance *)
Definition eqType := @Equality.Pack cT xclass xT.
Definition choiceType := @Choice.Pack cT xclass xT.
Definition ordType := @Ord.Pack cT xclass xT.

End ClassDef.

Module Import Exports.
Coercion base : class_of >-> Ord.class_of.
Coercion mixin : class_of >-> mixin_of.
Coercion sort : type >-> Sortclass.
Coercion eqType : type >-> Equality.type.
Canonical eqType.
Coercion choiceType : type >-> Choice.type.
Canonical choiceType.
Coercion ordType : type >-> Ord.type.
Canonical ordType.
Notation poType := type.
Notation poMixin := mixin_of.
Notation PoMixin := Mixin.
Notation PoType T m := (@pack _ T m _ _ id).
Notation "[ 'poType' 'of' T 'for' cT ]" :=  (@clone _ T cT _ idfun)
  (at level 0, format "[ 'poType'  'of'  T  'for'  cT ]") : form_scope.
Notation "[ 'poType' 'of' T ]" := (@clone _ T _ _ id)
  (at level 0, format "[ 'poType'  'of'  T ]") : form_scope.
End Exports.

End Po.

Export Po.Exports.

Local Open Scope dom_scope.

Definition appr b (T : poType b) := Po.appr (Po.class T).
Notation "x ⊑ y" := (appr x y) : dom_scope.
Notation "x ⊏ y" := ((x ⊑ y) && (x != y)) : dom_scope.
Notation "x ⋢ y" := (~~ appr x y) : dom_scope.
Notation "x ⊑ y ⊑ z" := (appr x y && appr y z) : dom_scope.

Section PoTheory.

Variable (b : bool) (T : poType b).
Implicit Types x y z : T.
Implicit Types P : pred T.

Local Notation appr := (@appr b T) (only parsing).

Lemma apprxx : reflexive appr.
Proof. by case: T=> [? [? [? []]]]. Qed.

Lemma appr_trans : transitive appr.
Proof. by case: T=> [? [? [? []]]]. Qed.

Lemma apprE x : appr x = Po.appr (Po.class T) x.
Proof. by []. Qed.

End PoTheory.

Lemma appr_anti (T : poType true) : antisymmetric (@appr true T).
Proof. by case: T=> [? [? [? []]]]. Qed.

Section QuotPoType.

Variable (b : bool) (T : poType b).
Definition po_eq (x y : T) := x ⊑ y ⊑ x.

Lemma po_eqP : equiv_class_of po_eq.
Proof.
rewrite /po_eq; split.
- by move=> x; rewrite apprxx.
- by move=> x y; rewrite andbC.
- move=> y x z /andP [x_y y_x] /andP [y_z z_y].
  by rewrite (appr_trans x_y y_z) (appr_trans z_y y_x).
Qed.

Canonical po_eq_equiv := EquivRelPack po_eqP.

Record quot_po := QuotPo_ {
  quot_po_val : {eq_quot po_eq}
}.

Canonical quot_po_subType := Eval hnf in [newType for quot_po_val].
Definition quot_po_eqMixin := [eqMixin of quot_po by <:].
Canonical quot_po_eqType := Eval hnf in EqType quot_po quot_po_eqMixin.
Definition quot_po_choiceMixin := [choiceMixin of quot_po by <:].
Canonical quot_po_choiceType :=
  Eval hnf in ChoiceType quot_po quot_po_choiceMixin.
Definition quot_po_ordMixin := [ordMixin of quot_po by <:].
Canonical quot_po_ordType := Eval hnf in OrdType quot_po quot_po_ordMixin.

Definition quot_po_of & phant T := quot_po.
Identity Coercion quot_po_of_quot_po : quot_po_of >-> quot_po.

Notation "{ 'quot_po' T }" := (quot_po_of (Phant T))
  (at level 0, format "{ 'quot_po'  T }").

Canonical quot_po_of_subType := Eval hnf in [subType of {quot_po T}].
Canonical quot_po_of_eqType := Eval hnf in [eqType of {quot_po T}].
Canonical quot_po_of_choiceType := Eval hnf in [choiceType of {quot_po T}].
Canonical quot_po_of_ordType := Eval hnf in [ordType of {quot_po T}].

Implicit Types x y z : {quot_po T}.

Definition qappr x y := repr (val x) ⊑ repr (val y).

Lemma qapprP : Po.axioms_of true qappr.
Proof.
rewrite /qappr; split.
- move=> qx; exact: apprxx.
- move=> ???; exact: appr_trans.
- move=> [x] [y] /=.
  elim/quotP: x=> /= x ->; elim/quotP: y=> /= y -> xy.
  congr QuotPo_; exact/eqmodP.
Qed.

Definition quot_po_poMixin := PoMixin qapprP.
Canonical quot_po_poType := Eval hnf in PoType quot_po quot_po_poMixin.
Canonical quot_po_of_poType := Eval hnf in [poType of {quot_po T}].

Definition QuotPo (x : T) : {quot_po T} := QuotPo_ (\pi x).

Definition quot_po_repr x := repr (quot_po_val x).

Lemma quot_po_reprK : cancel quot_po_repr QuotPo.
Proof. by case=> x /=; congr QuotPo_; rewrite /= reprK. Qed.

Definition quot_po_quotMixin := QuotClass quot_po_reprK.
Canonical quot_po_quotType := Eval hnf in QuotType quot_po quot_po_quotMixin.
Canonical quot_po_of_quotType := Eval hnf in [quotType of {quot_po T}].

Lemma eq_quot_poP : {mono \pi_{quot_po T} : x y / po_eq x y >-> x == y}.
Proof. move=> x y; rewrite unlock; exact: piE. Qed.

Canonical quot_po_eqQuotType :=
  Eval hnf in EqQuotType po_eq quot_po eq_quot_poP.
Canonical quot_po_of_eqQuotType :=
  Eval hnf in [eqQuotType po_eq of {quot_po T}].

Lemma qapprE (x y : T) : (\pi_{quot_po T} x ⊑ \pi y) = (x ⊑ y).
Proof.
rewrite unlock apprE /= /qappr /= /QuotPo.
case: piP=> x' /eqmodP /andP [x_x' x'_x].
case: piP=> y' /eqmodP /andP [y_y' y'_y].
apply/(sameP idP)/(iffP idP).
- by move=> x_y; rewrite (appr_trans x'_x) // (appr_trans x_y).
- by move=> x'_y'; rewrite (appr_trans x_x') // (appr_trans x'_y').
Qed.

End QuotPoType.

Notation "{ 'quot_po' T }" := (quot_po_of (Phant T))
  (at level 0, format "{ 'quot_po'  T }").

Section SubTypePo.

Variables (bT : bool) (T : poType bT) (P : pred T) (sT : subType P).

Implicit Types x y z : sT.

Definition sub_appr x y := val x ⊑ val y.

Lemma sub_appr_ax : Po.axioms_of bT sub_appr.
Proof.
rewrite /sub_appr; split.
- move=> ?; exact: apprxx.
- move=> ???; exact: appr_trans.
- by case: bT T P sT=> // ????? /appr_anti/val_inj.
Qed.

Definition SubPoMixin := PoMixin sub_appr_ax.

End SubTypePo.

Notation "[ 'poMixin' 'of' T 'by' <: ]" :=
  (SubPoMixin _ : poMixin _ T)
  (at level 0, format "[ 'poMixin'  'of'  T  'by'  <: ]") : form_scope.

Section SubPoType.

Variables (bT : bool) (T : poType bT) (P : pred T).

Record subPoType := SubPoTypePack {
  subPo_sort  :> subType P;
  subPo_class :  Po.class_of bT subPo_sort;
  _ : forall x y : subPo_sort, @appr _ (Po.Pack subPo_class) x y = val x ⊑ val y
}.

Canonical sub_poType (sT : subPoType) : poType bT := Po.Pack (subPo_class sT).
Coercion sub_poType : subPoType >-> poType.

Definition pack_subPoType :=
  fun (U : Type) (sT : subType P) (poT : poType bT) & sT * poT -> U * U =>
  fun (cT : Po.class_of bT sT) & phant_id (Po.class poT) cT =>
  fun H => @SubPoTypePack sT cT H.

Definition appr_val (sT : subPoType) :
  forall (x y : sT), x ⊑ y = val x ⊑ val y :=
  let: SubPoTypePack _ _ res := sT in res.

End SubPoType.

Notation SubPoType T H := (@pack_subPoType _ _ _ T _ _ id _ id H).

Module DiscPo.

Section ClassDef.

Record mixin_of (T : poType true) := Mixin {
  _ : forall x y : T, x ⊑ y = (x == y)
}.

Section Mixins.

Variable T : ordType.
Implicit Types x y : T.

Lemma dapprP : Po.axioms_of true (@eq_op T).
Proof.
split.
- exact: eqxx.
- exact: eq_op_trans.
- by move=> x y /= /andP [/eqP ->].
Qed.

End Mixins.

Record class_of T :=
  Class {base : Po.class_of true T; mixin : mixin_of (Po.Pack base)}.
Local Coercion base : class_of >-> Po.class_of.

Structure type := Pack {sort; _ : class_of sort}.
Local Coercion sort : type >-> Sortclass.
Variables (T : Type) (cT : type).
Definition class := let: Pack _ c as cT' := cT return class_of cT' in c.
Definition clone c of phant_id class c := @Pack T c.
Let xT := let: Pack T _ := cT in T.
Notation xclass := (class : class_of xT).

Definition pack :=
  fun (bT : poType true) b & phant_id (Po.class bT) b =>
  fun    m => Pack (@Class T b m).

(* Inheritance *)
Definition eqType := @Equality.Pack cT xclass xT.
Definition choiceType := @Choice.Pack cT xclass xT.
Definition ordType := @Ord.Pack cT xclass xT.
Definition poType := @Po.Pack true cT xclass.

End ClassDef.

Module Import Exports.
Coercion base : class_of >-> Po.class_of.
Coercion mixin : class_of >-> mixin_of.
Coercion sort : type >-> Sortclass.
Coercion eqType : type >-> Equality.type.
Canonical eqType.
Coercion choiceType : type >-> Choice.type.
Canonical choiceType.
Coercion ordType : type >-> Ord.type.
Canonical ordType.
Coercion poType : type >-> Po.type.
Canonical poType.
Notation discPoType := type.
Notation discPoMixin := mixin_of.
Notation DiscPoMixin := Mixin.
Notation DiscPoType T m := (@pack T _ _ id m).
Notation "[ 'poType' 'for' T 'by' // ]" :=
  (PoType T (PoMixin (@dapprP _)))
  (at level 0, format "[ 'poType'  'for'  T  'by'  // ]")
  : form_scope.
Notation "[ 'discPoType' 'for' T ]" :=
  (DiscPoType T (@DiscPoMixin _ (fun x y : T => erefl)))
  (at level 0, format "[ 'discPoType'  'for'  T ]")
  : form_scope.
Notation "[ 'discPoType' 'of' T 'for' cT ]" :=  (@clone T cT _ idfun)
  (at level 0, format "[ 'discPoType'  'of'  T  'for'  cT ]")
  : form_scope.
Notation "[ 'discPoType' 'of' T ]" := (@clone T _ _ id)
  (at level 0, format "[ 'discPoType'  'of'  T ]") : form_scope.
End Exports.

End DiscPo.

Export DiscPo.Exports.

Canonical void_poType := Eval hnf in [poType for void by //].
Canonical void_discPoType := Eval hnf in [discPoType for void].

Canonical nat_poType := Eval hnf in [poType for nat by //].
Canonical nat_discPoType := Eval hnf in [discPoType for nat].

Canonical bool_poType := Eval hnf in [poType for bool by //].
Canonical bool_discPoType := Eval hnf in [discPoType for bool].

Section DiscPoTheory.

Variable T : discPoType.
Implicit Types x y : T.

Lemma apprD x y : x ⊑ y = (x == y).
Proof. by case: T x y => [? [? []]]. Qed.

End DiscPoTheory.

Variant coh T := Coh of T | Incoh.
Arguments Coh {_} _.
Arguments Incoh {_}.

Definition isCoh T (x : coh T) : bool :=
  if x is Coh _ then true else false.

Coercion isCoh : coh >-> bool.

Definition option_of_coh T (x : coh T) :=
  if x is Coh x then Some x else None.
Arguments option_of_coh {_} _.

Definition coh_of_option T (x : option T) :=
  if x is Some x then Coh x else Incoh.

Lemma option_of_cohK T : cancel (@option_of_coh T) (@coh_of_option T).
Proof. by case. Qed.

Lemma coh_of_optionK T : cancel (@coh_of_option T) (@option_of_coh T).
Proof. by case. Qed.

Definition coh_eqMixin (T : eqType) :=
  CanEqMixin (@option_of_cohK T).
Canonical coh_eqType (T : eqType) :=
  Eval hnf in EqType (coh T) (coh_eqMixin T).
Definition coh_choiceMixin (T : choiceType) :=
  CanChoiceMixin (@option_of_cohK T).
Canonical coh_choiceType (T : choiceType) :=
  Eval hnf in ChoiceType (coh T) (coh_choiceMixin T).
Definition coh_ordMixin (T : ordType) :=
  CanOrdMixin (@option_of_cohK T).
Canonical coh_ordType (T : ordType) :=
  Eval hnf in OrdType (coh T) (coh_ordMixin T).

Definition coh_appr b (T : poType b) (x y : coh T) :=
  match y, x with
  | Coh y, Coh x => x ⊑ y
  | Incoh, _     => true
  | _    , _     => false
  end.

Lemma coh_apprP bT (T : poType bT) : Po.axioms_of bT (@coh_appr bT T).
Proof.
split.
- case=> // x; exact: apprxx.
- case=> [y|] [x|] [z|] //; exact: appr_trans.
- by case: bT T=> // T [x|] [y|] // /appr_anti ->.
Qed.

Definition coh_poMixin b (T : poType b) :=
  PoMixin (coh_apprP T).
Canonical coh_poType b (T : poType b) :=
  Eval hnf in PoType (coh T) (coh_poMixin T).

Section ProdPoType.

Variables (bT bS : bool) (T : poType bT) (S : poType bS).

Definition prod_appr (x y : T * S) :=
  match x, y with
  | (x1, x2), (y1, y2) => (x1 ⊑ y1) && (x2 ⊑ y2)
  end.

Lemma prod_apprP : Po.axioms_of (bT && bS) prod_appr.
Proof.
split.
- by move=> [x1 x2]; rewrite /prod_appr !apprxx.
- move=> [y1 y2] [x1 x2] [z1 z2] /andP [h11 h12] /andP [h21 h22].
  by apply/andP; split; [apply: appr_trans h21| apply: appr_trans h22].
- rewrite /prod_appr; case: bT bS T S=> [] [] //= ?? [x1 y1] [x2 y2] /=.
  case/andP => [/andP [/= h1 h2] /andP [/= h3 h4]].
  by congr pair; apply: appr_anti; rewrite ?T_anti ?S_anti ?h1 ?h2 ?h3 ?h4.
Qed.

Definition prod_poMixin := PoMixin prod_apprP.
Canonical prod_poType := Eval hnf in PoType (T * S) prod_poMixin.

End ProdPoType.

Section SumPoType.

Variables (bT bS : bool) (T : poType bT) (S : poType bS).

Definition sum_appr (x y : T + S) :=
  match x, y with
  | inl x, inl y => x ⊑ y
  | inr x, inr y => x ⊑ y
  | _    , _     => false
  end.

Lemma sum_apprP : Po.axioms_of (bT && bS) sum_appr.
Proof.
split.
- case=> x; exact: apprxx.
- case=> [] y [] x [] z //; exact: appr_trans.
- rewrite /sum_appr; case: bT bS T S=> [] [] //= ??.
  by case=> [] x [] y // /appr_anti ->.
Qed.

Definition sum_poMixin := PoMixin sum_apprP.
Canonical sum_poType := Eval hnf in PoType (T + S) sum_poMixin.

End SumPoType.

Section OptionPoType.

Variable (bT : bool) (T : poType bT).

Definition oappr (x y : option T) :=
  match x, y with
  | Some x, Some y => x ⊑ y
  | None  , _      => true
  | _     , _      => false
  end.

Lemma oapprP : Po.axioms_of bT oappr.
Proof.
split.
- case=> // x; exact: apprxx.
- case=> [y|] [x|] [z|] //; exact: appr_trans.
- by rewrite /oappr; case: bT T=> [] // ? [x|] [y|] // /appr_anti ->.
Qed.

Definition option_poMixin := PoMixin oapprP.
Canonical option_poType := Eval hnf in PoType (option T) option_poMixin.

Lemma oapprE x y : x ⊑ y = oappr x y.
Proof. by []. Qed.

End OptionPoType.

Module PPo.

Section ClassDef.

Record mixin_of (anti : bool) (T : poType anti) := Mixin {
  bot : T;
  _   : forall x, bot ⊑ x
}.

Record class_of anti T :=
  Class {base : Po.class_of anti T; mixin : mixin_of (Po.Pack base)}.
Local Coercion base : class_of >-> Po.class_of.

Structure type anti := Pack {sort; _ : class_of anti sort}.
Local Coercion sort : type >-> Sortclass.
Variables (anti : bool) (T : Type) (cT : type anti).
Definition class := let: Pack _ c as cT' := cT return class_of anti cT' in c.
Definition clone c of phant_id class c := @Pack anti T c.
Let xT := let: Pack T _ := cT in T.
Notation xclass := (class : class_of anti xT).

Definition pack :=
  fun b bT & phant_id (@Po.class anti bT) b =>
  fun m    => Pack (@Class anti T b m).

(* Inheritance *)
Definition eqType := @Equality.Pack cT xclass xT.
Definition choiceType := @Choice.Pack cT xclass xT.
Definition ordType := @Ord.Pack cT xclass xT.
Definition poType := @Po.Pack anti cT xclass.

End ClassDef.

Module Import Exports.
Coercion base : class_of >-> Po.class_of.
Coercion mixin : class_of >-> mixin_of.
Coercion sort : type >-> Sortclass.
Coercion eqType : type >-> Equality.type.
Canonical eqType.
Coercion choiceType : type >-> Choice.type.
Canonical choiceType.
Coercion ordType : type >-> Ord.type.
Canonical ordType.
Coercion poType : type >-> Po.type.
Canonical poType.
Notation ppoType := type.
Notation ppoMixin := mixin_of.
Notation PPoMixin := Mixin.
Notation PPoType T m := (@pack _ T _ _ id m).
Notation "[ 'ppoType' 'of' T 'for' cT ]" :=  (@clone _ T _ cT idfun)
  (at level 0, format "[ 'ppoType'  'of'  T  'for'  cT ]") : form_scope.
Notation "[ 'ppoType' 'of' T ]" := (@clone _ T _ _ id)
  (at level 0, format "[ 'ppoType'  'of'  T ]") : form_scope.
End Exports.

End PPo.

Export PPo.Exports.

Definition bot bT (T : ppoType bT) : T :=
  PPo.bot (PPo.class T).
Notation "⊥" := (bot _).

Lemma botP bT (T : ppoType bT) (x : T) : ⊥ ⊑ x.
Proof. by case: T x => [? [? []]]. Qed.

Lemma appr_bot (T : ppoType true) (x : T) : reflect (x = ⊥) (x ⊑ ⊥).
Proof.
apply/(iffP idP); last by move=> ->; rewrite apprxx.
by move=> e; apply/appr_anti; rewrite e botP.
Qed.

Section QuotPPoType.

Variables (bT : bool) (T : ppoType bT).

Implicit Types x y : {quot_po T}.

Lemma quot_botP x : \pi_{quot_po T} ⊥ ⊑ x.
Proof. by elim/quotP: x=> x e; rewrite qapprE botP. Qed.

Definition quot_po_ppoMixin := PPoMixin quot_botP.
Canonical quot_po_ppoType := Eval hnf in PPoType (quot_po T) quot_po_ppoMixin.
Canonical quot_po_of_ppoType := Eval hnf in [ppoType of {quot_po T}].

End QuotPPoType.

Section SubPPoType.

Variables (bT : bool) (T : ppoType bT) (P : pred T) (sT : subPoType P).

Hypothesis P0 : P ⊥.

Lemma sub_botP x : (Sub ⊥ P0 : sT) ⊑ x.
Proof. by rewrite appr_val SubK botP. Qed.

End SubPPoType.

Notation "[ 'ppoMixin' 'of' T 'by' <: 'using' P0 ]" :=
  (PPoMixin (fun x : T => sub_botP P0 x))
  (at level 0, format "[ 'ppoMixin'  'of'  T  'by'  <:  'using'  P0 ]")
  : form_scope.

Section ProdPPoType.

Variables (bT bS : bool) (T : ppoType bT) (S : ppoType bS).

Definition prod_bot : T * S := (⊥, ⊥).

Lemma prod_botP x : prod_bot ⊑ x.
Proof. case: x=> ??; apply/andP; split; exact: botP. Qed.

Definition prod_ppoMixin := PPoMixin prod_botP.
Canonical prod_ppoType := Eval hnf in PPoType (T * S) prod_ppoMixin.

End ProdPPoType.

Section OptionPPoType.

Variable (bT : bool) (T : poType bT).

Lemma option_botP (x : option T) : None ⊑ x.
Proof. by []. Qed.

Definition option_ppoMixin := PPoMixin option_botP.
Canonical option_ppoType := Eval hnf in PPoType (option T) option_ppoMixin.

End OptionPPoType.

Section CohPPoType.

Variable (bT : bool) (T : ppoType bT).

Implicit Types x : coh T.

Lemma coh_botP x : Coh ⊥ ⊑ x.
Proof. case: x=> // x; exact: botP. Qed.

Definition coh_ppoMixin := PPoMixin coh_botP.
Canonical coh_ppoType := Eval hnf in PPoType (coh T) coh_ppoMixin.

End CohPPoType.

Section FFun.

Variables (T : ordType) (S : ppoType true).

Record ffun := FFun {
  ffun_val : {fmap T -> S};
  _        : ⊥ \notin codomm ffun_val
}.
Definition ffun_of & phant (T -> S) := ffun.

Identity Coercion ffun_of_ffun : ffun_of >-> ffun.

Notation "{ 'ffun' T }" := (ffun_of (Phant T))
  (at level 0, format "{ 'ffun'  T }" ) : dom_scope.

Canonical ffun_subType := [subType for ffun_val].
Definition ffun_eqMixin := [eqMixin of ffun by <:].
Canonical ffun_eqType := Eval hnf in EqType ffun ffun_eqMixin.
Definition ffun_choiceMixin := [choiceMixin of ffun by <:].
Canonical ffun_choiceType := Eval hnf in ChoiceType ffun ffun_choiceMixin.
Definition ffun_ordMixin := [ordMixin of ffun by <:].
Canonical ffun_ordType := Eval hnf in OrdType ffun ffun_ordMixin.

Canonical ffun_of_subType := Eval hnf in [subType of {ffun T -> S}].
Canonical ffun_of_eqType := Eval hnf in [eqType of {ffun T -> S}].
Canonical ffun_of_choiceType := Eval hnf in [choiceType of {ffun T -> S}].
Canonical ffun_of_ordType := Eval hnf in [ordType of {ffun T -> S}].

Definition ffapp (f : ffun) (x : T) : S :=
  if ffun_val f x is Some y then y else ⊥.

Coercion ffapp : ffun >-> Funclass.

Lemma eq_ffun (f g : {ffun T -> S}) : f =1 g <-> f = g.
Proof.
split=> [|-> //] fg; apply/val_inj/eq_fmap=> x.
move: (fg x); rewrite /ffapp /=.
case f_x: (ffun_val f x)=> [y1|];
case g_x: (ffun_val g x)=> [y2|] //; first by move=> ->.
- move=> e; suff: ⊥ \in codomm (ffun_val f) by rewrite (negbTE (valP f)).
  by apply/codommP; exists x; rewrite -e.
- move=> e; suff: ⊥ \in codomm (ffun_val g) by rewrite (negbTE (valP g)).
  by apply/codommP; exists x; rewrite e.
Qed.

Program Definition ffun_of_fmap (f : {fmap T -> S}) : {ffun T -> S} :=
  Sub (filterm (fun _ y => y != ⊥) f) _.

Next Obligation.
move=> f /=; apply/negP=> /codommP [x].
rewrite filtermE; case: (f x)=> [y|] //=.
case: eqP=> //= ? [?]; congruence.
Qed.

Lemma ffun_of_fmapE f x : ffun_of_fmap f x = if f x is Some y then y else ⊥.
Proof.
rewrite /ffun_of_fmap /ffapp filtermE; case f_x: (f x)=> [y|] //=.
by case: eqP.
Qed.

Definition mkffun (f : T -> S) (X : {fset T}) : {ffun T -> S} :=
  ffun_of_fmap (mkfmapf f X).

Lemma mkffunE f X x : mkffun f X x = if x \in X then f x else ⊥.
Proof. by rewrite /mkffun ffun_of_fmapE mkfmapfE; case: ifP. Qed.

Implicit Types f g : {ffun T -> S}.

Definition fsupp f := domm (ffun_val f).

Lemma fsuppPn f x : reflect (f x = ⊥) (x \notin fsupp f).
Proof.
rewrite /ffapp; apply/(iffP dommPn)=> [->|] //.
case f_x: (ffun_val f x)=> [y|] // e.
by move/codommPn/(_ x): (valP f); rewrite f_x e eqxx.
Qed.

Lemma mem_fsupp f x : (x \in fsupp f) = (f x != ⊥).
Proof. by apply/negb_inj; rewrite negbK; apply/(sameP (fsuppPn f x))/eqP. Qed.

Lemma fsupp_ffun_of_fmap (f : {fmap T -> S}) :
  fsupp (ffun_of_fmap f) =
  fset (filter (fun x => f x != Some ⊥) (domm f)).
Proof.
apply/eq_fset=> x; rewrite in_fset mem_filter /fsupp /=.
apply/(sameP idP)/(iffP idP).
- case/andP=> n0 /dommP [y f_x]; rewrite mem_domm filtermE f_x /=.
  by rewrite -(inj_eq (@Some_inj _)) -f_x n0 f_x.
- rewrite !mem_domm filtermE; case f_x: (f x)=> [y|] //=.
  by rewrite [in Some _ == _]eqE /=; case: ifP.
Qed.

Lemma fsupp_ffun_of_fmap_sub (f : {fmap T -> S}) :
  fsubset (fsupp (ffun_of_fmap f)) (domm f).
Proof.
apply/fsubsetP=> x /dommP [/= v e]; apply/dommP; exists v.
by move: e; rewrite filtermE; case: (f x)=> [y|] //=; case: ifP.
Qed.

Definition fappr f g :=
  all (fun x => f x ⊑ g x) (fsupp f :|: fsupp g).

Lemma fapprP f g : reflect (forall x, f x ⊑ g x) (fappr f g).
Proof.
rewrite /fappr; apply/(iffP allP); last by eauto.
move=> P x; have [f_x|/fsuppPn ->] := boolP (x \in fsupp f); last exact: botP.
by apply: P; rewrite in_fsetU f_x.
Qed.

Lemma fapprPn f g : reflect (exists x, f x ⋢ g x) (~~ fappr f g).
Proof.
rewrite /fappr; apply/(iffP allPn); first by case; eauto.
case=> x Px; exists x=> //; rewrite in_fsetU mem_domm.
by move: Px; rewrite /ffapp; case: (ffun_val f x); rewrite // botP.
Qed.

Lemma ffun_apprP : Po.axioms_of true fappr.
Proof.
split.
- move=> f; apply/allP=> x _; exact: apprxx.
- move=> g f h /fapprP fg /fapprP gh; apply/fapprP=> x.
  exact: appr_trans (fg x) (gh x).
- move=> f g /andP [/fapprP fg /fapprP gf]; apply/eq_ffun=> x.
  by apply/appr_anti; rewrite fg gf.
Qed.

Definition ffun_poMixin := PoMixin ffun_apprP.
Canonical ffun_poType := Eval hnf in PoType ffun ffun_poMixin.
Canonical ffun_of_poType := Eval hnf in [poType of {ffun T -> S}].

Program Definition ffun_bot : {ffun T -> S} :=
  Sub emptym _.
Next Obligation. by rewrite /= codomm0. Qed.

Lemma ffun_botP f : ffun_bot ⊑ f.
Proof. by apply/fapprP=> x; rewrite /ffapp /= botP. Qed.

Definition ffun_ppoMixin := PPoMixin ffun_botP.
Canonical ffun_ppoType := Eval hnf in PPoType ffun ffun_ppoMixin.
Canonical ffun_of_ppoType := Eval hnf in [ppoType of {ffun T -> S}].

Lemma fbotE x : ffapp ⊥ x = ⊥. Proof. by []. Qed.

Lemma fsupp0 : fsupp ⊥ = fset0.
Proof. exact: domm0. Qed.

Lemma mkffunS (f : T -> S) X Y : fsubset X Y -> mkffun f X ⊑ mkffun f Y.
Proof.
move=> sub; apply/fapprP=> x; rewrite !mkffunE; case: ifP; rewrite ?botP //.
by move=> x_X; rewrite (fsubsetP sub _ x_X) apprxx.
Qed.

End FFun.

Notation "{ 'ffun' T }" := (ffun_of (Phant T))
  (at level 0, format "{ 'ffun'  T }" ) : dom_scope.

Arguments fapprP {_ _} [_ _].
Arguments fapprPn {_ _} [_ _].

Section FFunMap.

Variables (T : ordType) (S S1 S2 R : ppoType true).
Variable g : S -> R.
Variable op : S1 -> S2 -> R.

Definition mapf (f : {ffun T -> S}) : {ffun T -> R} :=
  ffun_of_fmap (mkfmapf (g \o f) (fsupp f)).

Lemma mapfE f :
  g ⊥ = ⊥ ->
  forall x, mapf f x = g (f x).
Proof.
move=> strict x; rewrite /mapf ffun_of_fmapE mkfmapfE /=.
by rewrite /ffapp mem_domm; case: (ffun_val f x).
Qed.

Definition mapf_op (f1 : {ffun T -> S1}) (f2 : {ffun T -> S2}) :
  {ffun T -> R} :=
  ffun_of_fmap (mkfmapf (fun x => op (f1 x) (f2 x)) (fsupp f1 :|: fsupp f2)).

Lemma mapf_opE f1 f2 :
  op ⊥ ⊥ = ⊥ ->
  forall x, mapf_op f1 f2 x = op (f1 x) (f2 x).
Proof.
move=> strict x; rewrite /mapf_op ffun_of_fmapE mkfmapfE.
rewrite /ffapp in_fsetU !mem_domm.
by case: (ffun_val f1 x) (ffun_val f2 x)=> [y1|] // [y2|].
Qed.

Lemma fsupp_mapf_op f1 f2 :
  op ⊥ ⊥ = ⊥ ->
  fsubset (fsupp (mapf_op f1 f2)) (fsupp f1 :|: fsupp f2).
Proof.
move=> opBB; apply/fsubsetP=> x; apply: contraTT.
rewrite in_fsetU; case/norP=> /fsuppPn f1_x /fsuppPn f2_x.
by apply/fsuppPn; rewrite mapf_opE // f1_x f2_x.
Qed.

End FFunMap.

Section FFunMap2.

Variables (T1 T2 : ordType) (S1 S2 : ppoType true).

Definition mapf2 (f : T1 -> T2) (g : S1 -> S2) (h : {ffun T1 -> S1}) :=
  ffun_of_fmap (mapm2 f g (val h)).

Lemma mapf2E (f : T1 -> T2) (g : S1 -> S2) (h : {ffun T1 -> S1}) (x : T1) :
  injective f -> g ⊥ = ⊥ -> mapf2 f g h (f x) = g (h x).
Proof.
move=> f_inj eg; rewrite /mapf2 ffun_of_fmapE mapm2E // /ffapp /=.
by case: (ffun_val h x).
Qed.

End FFunMap2.

Section FFunCoh.

Variables (T : ordType) (S : ppoType true).
Implicit Types f : {ffun T -> coh S}.
Implicit Types g : {ffun T -> S}.

Definition ffun_coh f : coh {ffun T -> S} :=
  if Incoh \in codomm (ffun_val f) then Incoh
  else Coh (ffun_of_fmap (mkfmapfp (option_of_coh \o f) (fsupp f))).

Variant ffun_coh_spec f : coh {ffun T -> S} -> Prop :=
| FFunCohCoh g of (forall x, f x = Coh (g x)) : ffun_coh_spec f (Coh g)
| FFunCohIncoh x of x \in fsupp f & f x = Incoh : ffun_coh_spec f Incoh.

Lemma ffun_cohP f : ffun_coh_spec f (ffun_coh f).
Proof.
rewrite /ffun_coh; case: ifPn.
  case/codommP=> x e.
  have x_supp : x \in fsupp f by apply/dommP; exists Incoh.
  have f_x : f x = Incoh by rewrite /ffapp e.
  exact: FFunCohIncoh x_supp f_x.
move=> /codommPn f_coh; apply: FFunCohCoh=> x.
rewrite ffun_of_fmapE mkfmapfpE /= /ffapp.
by case: ifPn (f_coh x)=> [/dommP [[y|] ->]|/dommPn ->].
Qed.

Lemma ffun_coh_appr f g : f ⊑ mapf Coh g = ffun_coh f ⊑ Coh g.
Proof.
case: ffun_cohP=> [h hP|x x_supp f_x]; last first.
  by apply/negbTE/fapprPn; exists x; rewrite mapfE ?f_x.
apply/(sameP fapprP)/(iffP fapprP).
  move=> h_g x; rewrite mapfE // hP; exact: h_g.
move=> f_g x; suff: Coh (h x) ⊑ Coh (g x) by [].
by rewrite -hP -mapfE.
Qed.

Lemma ffun_cohE f g :
  ffun_coh f = Coh g -> forall x, f x = Coh (g x).
Proof. by case: ffun_cohP=> // {g} g gP [<-]. Qed.

End FFunCoh.

Module Dom.

Section ClassDef.

Record mixin_of anti (T : poType anti) := Mixin {
  lub : T -> T -> coh T;
  _ : forall x y z, (lub x y ⊑ Coh z) = (x ⊑ z) && (y ⊑ z)
}.

Record class_of anti T :=
  Class {base : Po.class_of anti T; mixin : mixin_of (Po.Pack base)}.
Local Coercion base : class_of >-> Po.class_of.

Structure type anti := Pack {sort; _ : class_of anti sort}.
Local Coercion sort : type >-> Sortclass.
Variables (anti : bool) (T : Type) (cT : type anti).
Definition class := let: Pack _ c as cT' := cT return class_of anti cT' in c.
Definition clone c of phant_id class c := @Pack anti T c.
Let xT := let: Pack T _ := cT in T.
Notation xclass := (class : class_of anti xT).

Definition pack :=
  fun b (bT : poType anti) & phant_id (Po.class bT) b =>
  fun m    => Pack (@Class anti T b m).

(* Inheritance *)
Definition eqType := @Equality.Pack cT xclass xT.
Definition choiceType := @Choice.Pack cT xclass xT.
Definition ordType := @Ord.Pack cT xclass xT.
Definition poType := @Po.Pack anti cT xclass.

End ClassDef.

Module Import Exports.
Coercion base : class_of >-> Po.class_of.
Coercion mixin : class_of >-> mixin_of.
Coercion sort : type >-> Sortclass.
Coercion eqType : type >-> Equality.type.
Canonical eqType.
Coercion choiceType : type >-> Choice.type.
Canonical choiceType.
Coercion ordType : type >-> Ord.type.
Canonical ordType.
Coercion poType : type >-> Po.type.
Canonical poType.
Notation domType := type.
Notation domMixin := mixin_of.
Notation DomMixin := Mixin.
Notation DomType T m := (@pack _ T _ _ id m).
Notation "[ 'domType' 'of' T 'for' cT ]" :=  (@clone _ T cT _ idfun)
  (at level 0, format "[ 'domType'  'of'  T  'for'  cT ]") : form_scope.
Notation "[ 'domType' 'of' T ]" := (@clone _ T _ _ id)
  (at level 0, format "[ 'domType'  'of'  T ]") : form_scope.
End Exports.

End Dom.

Export Dom.Exports.

Definition lub bT (T : domType bT) : T -> T -> coh T := Dom.lub (Dom.class T).
Arguments lub {_ _} _ _.
Notation "x ⊔ y" := (lub x y) : dom_scope.

Section DomTheory.

Variable (bT : bool) (T : domType bT).
Implicit Types x y z : T.
Implicit Types a b c : coh T.
Implicit Types xs ys zs : {fset T}.
Implicit Types P : pred T.

Local Notation lub  := (@lub T) (only parsing).

Lemma lub_appr x y z : (x ⊔ y ⊑ Coh z) = (x ⊑ z) && (y ⊑ z).
Proof. by case: T x y z => [? [? []]]. Qed.

Lemma lub_apprG x y a : (x ⊔ y ⊑ a) = (Coh x ⊑ a) && (Coh y ⊑ a).
Proof. by case: a=> [z|] //=; rewrite lub_appr. Qed.

End DomTheory.

Section DomTheoryAnti.

Variable (T : domType true).

Implicit Types x y z : T.
Implicit Types a b c : coh T.
Implicit Types xs ys zs : {fset T}.
Implicit Types P : pred T.

Local Notation lub  := (@lub _ T) (only parsing).

Lemma lub_unique x y a :
  (forall b, (a ⊑ b) = (Coh x ⊑ b) && (Coh y ⊑ b)) ->
  a = x ⊔ y.
Proof.
move=> aP; apply: appr_anti; rewrite aP -lub_apprG apprxx /=.
by rewrite lub_apprG -aP apprxx.
Qed.

Lemma lubxx x : x ⊔ x = Coh x.
Proof. by apply/esym/lub_unique=> // a; rewrite andbb. Qed.

Lemma lubC : commutative lub.
Proof. by move=> x y; apply/lub_unique=> a; rewrite andbC lub_apprG. Qed.

Lemma appr_lubl x y : Coh x ⊑ x ⊔ y.
Proof.
by move: (lub_apprG x y (x ⊔ y)); rewrite apprxx; case/esym/andP.
Qed.

Lemma appr_lubr x y : Coh y ⊑ x ⊔ y.
Proof. by rewrite lubC appr_lubl. Qed.

Lemma lub_idPl x y : reflect (x ⊔ y = Coh x) (y ⊑ x).
Proof.
apply/(iffP idP).
- by move=> yx; apply: appr_anti; rewrite appr_lubl lub_appr apprxx andbT.
- by move=> xy; move: (lub_appr x y x); rewrite xy apprxx; case/esym/andP.
Qed.

Lemma lub_idPr x y : reflect (x ⊔ y = Coh y) (x ⊑ y).
Proof. rewrite lubC; exact: lub_idPl. Qed.

Lemma mono_lub x1 x2 y1 y2 : x1 ⊑ x2 -> y1 ⊑ y2 -> x1 ⊔ y1 ⊑ x2 ⊔ y2.
Proof.
move=> x1_x2 y1_y2; rewrite lub_apprG.
by rewrite (appr_trans _ (appr_lubl x2 y2)) // (appr_trans _ (appr_lubr x2 y2)).
Qed.

End DomTheoryAnti.

Arguments lub_idPl {_} [_ _].
Arguments lub_idPr {_} [_ _].

Section QuotDomType.

Variable (bT : bool) (T : domType bT).

Implicit Types x y : {quot_po T}.

Definition qlub x y : coh {quot_po T} :=
  if repr x ⊔ repr y is Coh z then Coh (\pi z) else Incoh.

Lemma qlubP x y z : (qlub x y ⊑ Coh z) = (x ⊑ z) && (y ⊑ z).
Proof.
rewrite /qlub; elim/quotP: x=> x ->; elim/quotP: y=> y ->.
elim/quotP: z=> z ez; rewrite !qapprE -lub_appr; case: (x ⊔ y)=> // ?.
by rewrite apprE /= qapprE.
Qed.

Definition quot_po_domMixin := DomMixin qlubP.
Canonical quot_po_domType := Eval hnf in DomType (quot_po T) quot_po_domMixin.
Canonical quot_po_of_domType := Eval hnf in [domType of {quot_po T}].

End QuotDomType.

Section ProdDomType.

Variables (bT bS : bool) (T : domType bT) (S : domType bS).

Implicit Types x y z : T * S.
Implicit Types a : coh (T * S).

Definition prod_lub x y :=
  match x.1 ⊔ y.1, x.2 ⊔ y.2 with
  | Coh xy1, Coh xy2 => Coh (xy1, xy2)
  | _      , _       => Incoh
  end.

Lemma prod_lubP x y z : (prod_lub x y ⊑ Coh z) = (x ⊑ z) && (y ⊑ z).
Proof.
rewrite /prod_lub; case: x y z=> [x1 x2] [y1 y2] [z1 z2] //=.
apply/(sameP idP)/(iffP andP).
- case=> [/andP [/= xz1 xz2] /andP [/= yz1 yz2]].
  move: (lub_appr x1 y1 z1) (lub_appr x2 y2 z2); rewrite xz1 xz2 yz1 yz2.
  case: (x1 ⊔ y1) (x2 ⊔ y2)=> [xy1|] [xy2|] //= ??.
  by apply/andP; split.
- move: (lub_appr x1 y1 z1) (lub_appr x2 y2 z2).
  case: (x1 ⊔ y1) (x2 ⊔ y2)=> [xy1|] [xy2|] //=.
  rewrite ![in Coh _ ⊑ _]apprE /= ![in (_, _) ⊑ _]apprE /=.
  by move=> -> -> /andP [/andP [-> ->] /andP [-> ->]]; split.
Qed.

Definition prod_domMixin := DomMixin prod_lubP.
Canonical prod_domType := Eval hnf in DomType (T * S) prod_domMixin.

End ProdDomType.

Section SumDomType.

Variables (bT bS : bool) (T : domType bT) (S : domType bS).

Implicit Types x y z : T + S.
Implicit Types a : coh (T + S).

Definition sum_lub x y :=
  match x, y with
  | inl x, inl y => if x ⊔ y is Coh xy then Coh (inl xy) else Incoh
  | inr x, inr y => if x ⊔ y is Coh xy then Coh (inr xy) else Incoh
  | _    , _     => Incoh
  end.

Lemma sum_lubP x y z : (sum_lub x y ⊑ Coh z) = (x ⊑ z) && (y ⊑ z).
Proof.
by case: x y z=> [x|x] [y|y] [z|z]; rewrite ?andbF //=;
rewrite ?(apprE (inl _)) ?(apprE (inr _)) /= -?lub_appr;
case: (x ⊔ y).
Qed.

Definition sum_domMixin := DomMixin sum_lubP.
Canonical sum_domType :=
  Eval hnf in DomType (T + S) sum_domMixin.

End SumDomType.

Section OptionDomType.

Variable (bT : bool) (T : domType bT).
Implicit Types x y z : option T.

Definition option_lub x y :=
  match x, y with
  | Some x, Some y =>
    if x ⊔ y is Coh z then Coh (Some z) else Incoh
  | None  , _      => Coh y
  | _     , None   => Coh x
  end.

Lemma option_lubP x y z : (option_lub x y ⊑ Coh z) = (x ⊑ z) && (y ⊑ z).
Proof.
by case: x y z=> [x|] // [y|] [z|]; rewrite /= ?andbT //=;
rewrite ?(apprE (Some _)) /= -?lub_appr; case: (x ⊔ y).
Qed.

Definition option_domMixin := DomMixin option_lubP.
Canonical option_domType :=
  Eval hnf in DomType (option T) option_domMixin.

End OptionDomType.

Module PDom.

Section ClassDef.

Record class_of anti T :=
  Class {base : PPo.class_of anti T; mixin : Dom.mixin_of (Po.Pack base)}.
Local Coercion base : class_of >-> PPo.class_of.

Structure type anti := Pack {sort; _ : class_of anti sort}.
Local Coercion sort : type >-> Sortclass.
Variables (anti : bool) (T : Type) (cT : type anti).
Definition class := let: Pack _ c as cT' := cT return class_of anti cT' in c.
Definition clone c of phant_id class c := @Pack anti T c.
Let xT := let: Pack T _ := cT in T.
Notation xclass := (class : class_of anti xT).

Definition pack :=
  fun b bT_ppo & phant_id (@PPo.class anti bT_ppo) b =>
  fun m bT_dom & phant_id (Dom.mixin (@Dom.class anti bT_dom)) m =>
  Pack (@Class anti T b m).

(* Inheritance *)
Definition eqType := @Equality.Pack cT xclass xT.
Definition choiceType := @Choice.Pack cT xclass xT.
Definition ordType := @Ord.Pack cT xclass xT.
Definition poType := @Po.Pack anti cT xclass.
Definition ppoType := @PPo.Pack anti cT xclass.
Definition domType :=
  @Dom.Pack anti cT (@Dom.Class anti cT xclass (mixin xclass)).

End ClassDef.

Module Import Exports.
Coercion base : class_of >-> PPo.class_of.
Coercion mixin : class_of >-> Dom.mixin_of.
Coercion sort : type >-> Sortclass.
Coercion eqType : type >-> Equality.type.
Canonical eqType.
Coercion choiceType : type >-> Choice.type.
Canonical choiceType.
Coercion ordType : type >-> Ord.type.
Canonical ordType.
Coercion poType : type >-> Po.type.
Canonical poType.
Coercion ppoType : type >-> PPo.type.
Canonical ppoType.
Coercion domType : type >-> Dom.type.
Canonical domType.
Notation pdomType := type.
Notation PDomType T := (@pack _ T _ _ id _ _ id).
Notation "[ 'pdomType' 'of' T 'for' cT ]" :=  (@clone _ T cT _ idfun)
  (at level 0, format "[ 'pdomType'  'of'  T  'for'  cT ]") : form_scope.
Notation "[ 'pdomType' 'of' T ]" := (@clone _ T _ _ id)
  (at level 0, format "[ 'pdomType'  'of'  T ]") : form_scope.
End Exports.

End PDom.

Export PDom.Exports.

Canonical option_pdomType bT (T : domType bT) :=
  Eval hnf in PDomType (option T).

Section PDomTheory.

Variable T : pdomType true.

Implicit Types x y : T.

Lemma lubxB x : x ⊔ ⊥ = Coh x.
Proof.
by apply/esym/lub_unique; case=> [y|] //=; rewrite botP andbT.
Qed.

Lemma lubBx x : bot T ⊔ x = Coh x.
Proof. by rewrite lubC lubxB. Qed.

End PDomTheory.

Section FFunDomType.

Variables (T : ordType) (S : pdomType true).
Implicit Types (f g h : {ffun T -> S}) (x : T) (y : S).

Definition flub f g : coh {ffun T -> S} :=
  ffun_coh (mapf_op (@lub true S) f g).

Lemma flub_appr f g h : flub f g ⊑ Coh h = (f ⊑ h) && (g ⊑ h).
Proof.
rewrite /flub -ffun_coh_appr; apply/(sameP fapprP)/(iffP andP).
  case=> /fapprP fh /fapprP gh x; rewrite mapf_opE ?lubxB ?mapfE ?lub_appr //.
  by rewrite fh gh.
by move=> fgh; split; apply/fapprP=> x;
move/(_ x): fgh; rewrite mapf_opE ?lubxB ?mapfE ?lub_appr //; case/andP.
Qed.

Definition ffun_domMixin := DomMixin flub_appr.
Canonical ffun_domType := Eval hnf in DomType (ffun T S) ffun_domMixin.
Canonical ffun_pdomType := Eval hnf in PDomType (ffun T S).
Canonical ffun_of_domType := Eval hnf in [domType of {ffun T -> S}].
Canonical ffun_of_pdomType := Eval hnf in [pdomType of {ffun T -> S}].

Variant flub_spec f g : coh {ffun T -> S} -> Prop :=
| FLubCoh h of (forall x, f x ⊔ g x = Coh (h x)) : flub_spec f g (Coh h)
| FLubIncoh x of
  x \in fsupp f & x \in fsupp g & f x ⊔ g x = Incoh : flub_spec f g Incoh.

Lemma flubP f g : flub_spec f g (f ⊔ g).
Proof.
rewrite /lub /= /flub; case: ffun_cohP=> [h hP|x _].
  by apply: FLubCoh=> x; rewrite -hP mapf_opE ?lubxx.
rewrite mapf_opE ?lubxx // => incoh.
have /andP [f_x g_x]: (x \in fsupp f) && (x \in fsupp g).
  rewrite !mem_fsupp -negb_or; apply: contraTN (introT eqP incoh).
  by case/orP=> /eqP ->; rewrite ?lubxB ?lubBx.
exact: FLubIncoh incoh.
Qed.

Lemma flubE f g h x : f ⊔ g = Coh h -> f x ⊔ g x = Coh (h x).
Proof.
by rewrite {1}/lub /= /flub /= => /ffun_cohE/(_ x); rewrite mapf_opE ?lubxx.
Qed.

End FFunDomType.

Section Lubn.

Variable T : domType true.
Implicit Types (x y z : T) (xs ys zs : seq T) (a b c : coh (option T)).
Implicit Types (X Y Z : {fset T}).

Definition lubn X : coh (option T) :=
  foldr (fun x b => if b is Coh oy then Some x ⊔ oy else Incoh) ⊥ X.

Lemma lubn_appr X y : lubn X ⊑ Coh (Some y) = all (fun x => x ⊑ y) X.
Proof.
rewrite /lubn; elim: (val X)=> {X} /= [|x xs <-]; first exact: botP.
by case: (foldr _ _ xs)=> [lubn_xs|]; rewrite /= ?lub_appr ?andbF.
Qed.

Lemma lubn_apprG X b : lubn X ⊑ b = all (fun x => Coh (Some x) ⊑ b) X.
Proof.
rewrite /lubn; elim: (val X)=> {X} /= [|x xs <-]; first exact: botP.
by case: foldr b=> [[?|]|] [[?|]|]; rewrite /= ?lub_appr ?andbF ?andbT.
Qed.

Lemma lubn_unique X a :
  (forall b, a ⊑ b = all (fun x => Coh (Some x) ⊑ b) X) ->
  a = lubn X.
Proof.
move=> aP; apply/appr_anti; rewrite aP -lubn_apprG apprxx.
by rewrite lubn_apprG -aP apprxx.
Qed.

Lemma lubn0 : lubn fset0 = ⊥. Proof. by []. Qed.
Lemma lubn1 x : lubn (fset1 x) = Coh (Some x).
Proof. by rewrite /lubn /= lubxB. Qed.

Lemma lubnU X Y :
  lubn (X :|: Y) =
  match lubn X, lubn Y with
  | Coh x, Coh y => x ⊔ y
  | _    , _     => Incoh
  end.
Proof.
apply/esym/lubn_unique=> b; rewrite all_fsetU -!lubn_apprG.
by case: (lubn X) (lubn Y) b=> [x|] [y|] [b|]; rewrite ?andbF ?lub_appr.
Qed.

Lemma lubnS X Y : fsubset X Y -> lubn X ⊑ lubn Y.
Proof.
move=> /fsubsetP X_Y; rewrite lubn_apprG.
by apply/allP=> x /X_Y; move: x; apply/allP; rewrite -lubn_apprG apprxx.
Qed.

Lemma appr_lubn x X : x \in X -> Coh (Some x) ⊑ lubn X.
Proof. by move: x; apply/allP; rewrite -lubn_apprG apprxx. Qed.

Definition lub_closure X : {fset T} :=
  fset (pmap id (pmap (fun Y => option_of_coh (lubn Y)) (powerset X))).

Lemma lub_closureP x X:
  reflect (exists2 Y, fsubset Y X & lubn Y = Coh (Some x))
          (x \in lub_closure X).
Proof.
rewrite /lub_closure in_fset mem_pmap; apply/(iffP mapP)=> /=.
  case=> y; rewrite mem_pmap; case/mapP=> Y; rewrite powersetE.
  by case lubn_Y: (lubn Y)=> [?|] sub // [->] e_x; exists Y; rewrite // e_x.
case=> Y sub lubn_Y; exists (Some x); rewrite // ?lubn_Y.
by rewrite mem_pmap; apply/mapP; exists Y; rewrite ?lubn_Y ?powersetE.
Qed.

Lemma lub_closure_ext X : fsubset X (lub_closure X).
Proof.
apply/fsubsetP=> x x_in.
by apply/lub_closureP; exists (fset1 x); rewrite ?lubn1 ?fsub1set.
Qed.

Lemma lub_closureS X Y :
  fsubset X Y -> fsubset (lub_closure X) (lub_closure Y).
Proof.
move=> X_Y; apply/fsubsetP=> x /lub_closureP [Z Z_X lubn_Z].
by apply/lub_closureP; exists Z; rewrite // (fsubset_trans Z_X).
Qed.

Lemma lub_closure_idem X : lub_closure (lub_closure X) = lub_closure X.
Proof.
apply/eqP; rewrite eqEfsubset lub_closure_ext andbT.
apply/fsubsetP=> y /lub_closureP [Y sub lubn_Y]; apply/lub_closureP.
exists (fset (filter (fun x => x ⊑ y) X)).
  by apply/fsubsetP=> x; rewrite in_fset mem_filter; case/andP.
apply/esym/lubn_unique=> b; rewrite -lubn_Y lubn_apprG.
apply/(sameP allP)/(iffP allP)=> h x.
  move=> xP; have x_y: x ⊑ y.
    by move: x xP; apply/allP; rewrite -lubn_appr lubn_Y apprxx.
  case/(fsubsetP sub)/lub_closureP: xP=> Z sub' lubn_Z.
  have: lubn Z ⊑ Coh (Some y) by rewrite lubn_Z.
  rewrite lubn_appr=> Z_y; rewrite -lubn_Z lubn_apprG.
  apply/allP=> z z_Z; apply: h; rewrite in_fset mem_filter (allP Z_y _ z_Z).
  by rewrite (fsubsetP sub' _ z_Z).
rewrite in_fset mem_filter; case/andP=> x_y x_X.
suffices: Coh (Some y) ⊑ b by apply: appr_trans.
by rewrite -lubn_Y lubn_apprG; apply/allP.
Qed.

Lemma lub_closureA X Y :
  fsubset (lub_closure X) (lub_closure Y) = fsubset X (lub_closure Y).
Proof.
apply/(sameP idP)/(iffP idP); last exact: fsubset_trans (lub_closure_ext X).
by rewrite -{2}(lub_closure_idem Y); apply: lub_closureS.
Qed.

Lemma lub_closure0 : lub_closure fset0 = fset0.
Proof. by rewrite /lub_closure powerset0 /= fset0E. Qed.

Lemma lub_closure1 x : lub_closure (fset1 x) = fset1 x.
Proof.
apply/eqP; rewrite eqEfsubset lub_closure_ext andbT.
apply/fsubsetP=> y /lub_closureP [Y]; rewrite fsubset1.
by case/orP=> /eqP ->; rewrite ?lubn0 ?lubn1 ?in_fset1 //; case=> ->.
Qed.

End Lubn.

Arguments lub_closure0 {_}.
Arguments lub_closure1 {_} _.

Section Projections.

Variable T : domType true.

Record proj := Proj {
  proj_val :> {fset T};
  _        :  lub_closure proj_val == proj_val
}.
Definition proj_of of phant T := proj.
Identity Coercion proj_of_proj : proj_of >-> proj.

Notation "{ 'proj' T }" := (proj_of (Phant T))
  (at level 0, format "{ 'proj'  T }") : type_scope.

Canonical proj_subType := [subType for proj_val].
Definition proj_eqMixin := [eqMixin of proj by <:].
Canonical proj_eqType := Eval hnf in EqType proj proj_eqMixin.
Definition proj_choiceMixin := [choiceMixin of proj by <:].
Canonical proj_choiceType := Eval hnf in ChoiceType proj proj_choiceMixin.
Definition proj_ordMixin := [ordMixin of proj by <:].
Canonical proj_ordType := Eval hnf in OrdType proj proj_ordMixin.

Canonical proj_of_subType := [subType of {proj T}].
Canonical proj_of_eqType := [eqType of {proj T}].
Canonical proj_of_choiceType := [choiceType of {proj T}].
Canonical proj_of_ordType := [ordType of {proj T}].

Definition proj_of_fset X : {proj T} :=
  @Proj (lub_closure X) (introT eqP (lub_closure_idem X)).

Implicit Types X Y : {proj T}.

Definition proj0 : {proj T} :=
  @Proj fset0 (introT eqP lub_closure0).

Definition proj1 x : {proj T} :=
  @Proj (fset1 x) (introT eqP (lub_closure1 x)).

Definition projU X Y := proj_of_fset (X :|: Y).

Lemma projUl X Y : fsubset X (projU X Y).
Proof. exact: (fsubset_trans (fsubsetUl X Y) (lub_closure_ext _)). Qed.

Lemma projUr X Y : fsubset Y (projU X Y).
Proof. exact: (fsubset_trans (fsubsetUr X Y) (lub_closure_ext _)). Qed.

End Projections.

Notation "{ 'proj' T }" := (proj_of (Phant T))
  (at level 0, format "{ 'proj'  T }") : type_scope.

Arguments proj0 {_}.
Arguments proj1 {_} _.

Definition pred_of_proj (T : domType true) (xs : proj T) :=
  [pred x : T | x \in val xs].
Canonical proj_predType T := mkPredType (@pred_of_proj T).
Canonical proj_of_predType (T : domType true) := [predType of {proj T}].

Section ProjMap.

Variables (T S : domType true).

Implicit Types (X Y : {proj T}).

Definition mapp (f : T -> S) X : {proj S} :=
  proj_of_fset (f @: X).

End ProjMap.

Section ProjDom.

Variables (T : domType true) (X : {proj T}).

Structure proj_dom := ProjDom {
  proj_elt :> T;
  _        :  proj_elt \in X
}.

Implicit Types x y z : proj_dom.

Canonical proj_dom_subType := [subType for proj_elt].
Definition proj_dom_eqMixin := [eqMixin of proj_dom by <:].
Canonical proj_dom_eqType := Eval hnf in EqType proj_dom proj_dom_eqMixin.
Definition proj_dom_choiceMixin := [choiceMixin of proj_dom by <:].
Canonical proj_dom_choiceType :=
  Eval hnf in ChoiceType proj_dom proj_dom_choiceMixin.
Definition proj_dom_ordMixin := [ordMixin of proj_dom by <:].
Canonical proj_dom_ordType :=
  Eval hnf in OrdType proj_dom proj_dom_ordMixin.

Definition proj_dom_appr x y := val x ⊑ val y.

Lemma proj_dom_apprP : Po.axioms_of true proj_dom_appr.
Proof.
split.
- move=> ?; exact: apprxx.
- move=> ???; exact: appr_trans.
- by move=> ?? /appr_anti/val_inj.
Qed.

Definition proj_dom_poMixin := PoMixin proj_dom_apprP.
Canonical proj_dom_poType := Eval hnf in PoType proj_dom proj_dom_poMixin.

Program Definition proj_dom_lub x y : coh proj_dom :=
  match val x ⊔ val y with
  | Coh z => Coh (@ProjDom z _)
  | Incoh => Incoh
  end.
Next Obligation.
move=> /= x y z e; rewrite inE -(eqP (valP X)).
apply/lub_closureP; exists [fset val x; val y].
- by rewrite !fsubU1set fsub0set (valP x) (valP y).
- have {e} ->: Coh (Some z) = Some (val x) ⊔ Some (val y).
    by rewrite /lub /= -e.
  apply: lub_unique=> b; rewrite lubn_apprG.
  apply/(sameP allP)/(iffP andP).
  + by case=> ?? w /fset2P [] ->.
  + by move=> H; split; apply: H; apply/fset2P; eauto.
Qed.

Lemma proj_dom_lubP x y z : proj_dom_lub x y ⊑ Coh z = (x ⊑ z) && (y ⊑ z).
Proof.
rewrite -lub_appr /proj_dom_lub.
by case: (_ ⊔ _) (@proj_dom_lub_obligation_1 x y).
Qed.

Definition proj_dom_domMixin := DomMixin proj_dom_lubP.
Canonical proj_dom_domType := Eval hnf in DomType proj_dom proj_dom_domMixin.

End ProjDom.

Definition monotone bT bS (T : poType bT) (S : poType bS) (f : T -> S) :=
  forall x y, x ⊑ y -> f x ⊑ f y.

Definition isotone bT bS (T : poType bT) (S : poType bS) (f : T -> S) :=
  forall x y, (f x ⊑ f y) = (x ⊑ y).

Section Embeddings.

Variables T S : domType true.

Implicit Types f g : T -> S.
Implicit Types X : {fset T}.

Definition lub_preserving f :=
  forall x y, f x ⊔ f y = if x ⊔ y is Coh z then Coh (f z) else Incoh.

Lemma iso_mono f : isotone f -> monotone f.
Proof. by move=> iso_f x y; rewrite iso_f. Qed.

Lemma iso_inj f : isotone f -> injective f.
Proof. by move=> fP x y e; apply/appr_anti; rewrite -2!fP e apprxx. Qed.

Lemma inj_iso f : injective f -> lub_preserving f -> isotone f.
Proof.
move=> f_inj f_emb x y.
apply/(sameP lub_idPr)/(iffP lub_idPr); rewrite f_emb; first by move=> ->.
by case: (x ⊔ y)=> // ? [] /f_inj ->.
Qed.

Lemma lub_preserving_mono f : lub_preserving f -> monotone f.
Proof.
by move=> f_emb x y /lub_idPl xy; apply/lub_idPl; rewrite f_emb xy.
Qed.

Lemma lubn_imfset f X :
  lub_preserving f ->
  lubn (f @: X) = if lubn X is Coh ox then Coh (omap f ox) else Incoh.
Proof.
move=> f_lub; elim/fset_ind: X=> [|x X _ IH].
  by rewrite imfset0 lubn0.
rewrite imfsetU1 !lubnU !lubn1 IH; case: (lubn X)=> [[x'|]|] //=.
by rewrite /lub /= f_lub; case: (x ⊔ x').
Qed.

Lemma lub_closure_imfset f X :
  lub_preserving f ->
  lub_closure (f @: X) = f @: lub_closure X.
Proof.
move=> f_lub; apply/eq_fset=> y.
apply/(sameP (lub_closureP _ _))/(iffP imfsetP).
  case=> {y} x /lub_closureP [X' sub elub] ->.
  by exists (f @: X'); rewrite ?imfsetS // lubn_imfset ?elub.
case=> Y subY elubY; pose X' := fset [seq x <- X | f x \in Y].
have subX: fsubset X' X.
  by apply/fsubsetP=> x; rewrite in_fset mem_filter; case/andP.
have eY: Y = f @: X'.
  apply/eq_fset=> y'; apply/(sameP idP)/(iffP imfsetP).
  - case=> {y'} x xin ->.
    by move: xin; rewrite in_fset mem_filter; case/andP.
  - move/fsubsetP: subY=> subY inY.
    case/imfsetP: (subY _ inY) (inY)=> {y' inY} x xin -> inY.
    by exists x; rewrite // in_fset mem_filter inY.
move: elubY; rewrite eY lubn_imfset //.
case elubX': (lubn X')=> {y} [[x'|//]|//] [<-].
by exists x'=> //; apply/lub_closureP; exists X'.
Qed.

Lemma val_mapp f (X : {proj T}) : lub_preserving f -> val (mapp f X) = f @: X.
Proof.
by move=> f_lub; rewrite /= lub_closure_imfset // (eqP (valP X)).
Qed.

Lemma mappP f (X : {proj T}) y :
  lub_preserving f ->
  reflect (exists2 x, x \in X & y = f x) (y \in mapp f X).
Proof. move=> fP; rewrite inE val_mapp //; exact/imfsetP. Qed.

Lemma mem_mapp f (X : {proj T}) x :
  injective f -> lub_preserving f -> (f x \in mapp f X) = (x \in X).
Proof.
move=> f_inj f_lub; rewrite inE val_mapp //.
apply/(sameP idP)/(iffP idP); first exact: mem_imfset.
by case/imfsetP=> ? ? /f_inj ->.
Qed.

End Embeddings.

Section SubPoDomType.

Variables (bT : bool) (T : domType bT) (P : pred T) (sT : subPoType P).

Implicit Types x y : sT.

Hypothesis P_lub :
  forall x y (z : T), val x ⊔ val y = Coh z -> P z.

Definition sub_lub x y : coh sT :=
  match val x ⊔ val y as oz return val x ⊔ val y = oz -> coh sT with
  | Coh z => fun e => Coh (Sub z (P_lub e))
  | Incoh => fun _ => Incoh
  end erefl.

Lemma sub_lub_val x y :
  val x ⊔ val y = if sub_lub x y is Coh z then Coh (val z) else Incoh.
Proof.
rewrite /sub_lub; move: (@P_lub x y) (erefl _).
by case: (val x ⊔ val y)=> // ???; rewrite SubK.
Qed.

Lemma sub_lub_appr x y z : sub_lub x y ⊑ Coh z = (x ⊑ z) && (y ⊑ z).
Proof.
rewrite 2!appr_val -lub_appr sub_lub_val; case: (sub_lub x y)=> [w|] //.
exact/appr_val.
Qed.

End SubPoDomType.

Notation "[ 'domMixin' 'of' T 'by' <: 'using' H ]" :=
  (DomMixin (fun x y z : T => sub_lub_appr H x y z))
  (at level 0, format "[ 'domMixin'  'of'  T  'by'  <:  'using'  H ]")
  : form_scope.

Section SubDomType.

Variables (T : domType true) (P : pred T).

Record subDomType := SubDomTypePack {
  subDom_sort :> subPoType P;
  subDom_class : Dom.class_of true subDom_sort;
  _ : @lub_preserving (Dom.Pack subDom_class) T val
}.

Definition sub_domType (sT : subDomType) : domType true :=
  Dom.Pack (subDom_class sT).

Coercion sub_domType : subDomType >-> domType.
Canonical sub_domType.

Definition lub_val (sT : subDomType) : @lub_preserving sT T val :=
  let: SubDomTypePack _ _ H := sT in H.

Definition pack_subDomType :=
  fun (U : Type) (sT : subPoType P) (dT : domType true) & sT * dT -> U * U =>
  fun (c : Dom.class_of true sT) & phant_id (Dom.class dT) c =>
  fun H => @SubDomTypePack sT c H.

End SubDomType.

Notation SubDomType T H := (@pack_subDomType _ _ T _ _ id _ id H).
Notation "[ 'subDomType' 'for' T ]" :=
  (SubDomType T (@sub_lub_val _ _ _ _ _)).

Section Retract.

Variable T : domType true.
Implicit Types (X Y : {proj T}) (x y z : T).

Definition retract X x :=
  if lubn (fset [seq y <- val X | y ⊑ x]) is Coh y then y else ⊥.

Lemma retract0 x : retract proj0 x = ⊥.
Proof. by rewrite /retract -fset0E lubn0. Qed.

Lemma retract1 x y : retract (proj1 x) y = if x ⊑ y then Some x else None.
Proof.
by rewrite /retract /=; case: ifP=> _; rewrite -?fset1E -?fset0E.
Qed.

Lemma retractPG X x oy :
  reflect (forall z, z \in X -> z ⊑ x -> Some z ⊑ oy) (retract X x ⊑ oy).
Proof.
rewrite /retract; set Y := fset _; have: lubn Y ⊑ Coh (Some x).
  rewrite lubn_appr; apply/allP=> ?; rewrite /Y in_fset mem_filter.
  by case/andP.
case: (lubn Y) (lubn_apprG Y (Coh oy)) => // ox e _.
move: e; rewrite {1}apprE /= => ->; apply/(iffP allP).
  by move=> H z z_X z_x; apply: H; rewrite /Y in_fset mem_filter z_x.
by move=> H z; rewrite /Y in_fset mem_filter; case/andP=> ??; apply: H.
Qed.

Lemma retractP X x y :
  reflect (forall z, z \in X -> z ⊑ x -> z ⊑ y) (retract X x ⊑ Some y).
Proof. exact: (retractPG _ _ (Some y)). Qed.

Lemma retract_unique X x oy :
  (forall oz, reflect (forall w, w \in X -> w ⊑ x -> Some w ⊑ oz) (oy ⊑ oz)) ->
  retract X x = oy.
Proof.
move=> oyP; apply/appr_anti/andP; split.
- exact/retractPG/oyP/apprxx.
- exact/oyP/retractPG/apprxx.
Qed.

Lemma retract_lub_closure X x y : retract X x = Some y -> y \in X.
Proof.
move=> e; rewrite inE -(eqP (valP X)); apply/lub_closureP.
pose Y := fset [seq y <- val X | y ⊑ x]; exists Y.
  by apply/fsubsetP => z; rewrite in_fset mem_filter => /andP [].
by move: e; rewrite /retract; case: (lubn _)=> // _ ->.
Qed.

Lemma retract_appr X x : retract X x ⊑ Some x.
Proof. exact/retractP. Qed.

Lemma retract_mono X : monotone (retract X).
Proof.
move=> x y x_y; apply/retractPG=> z z_X z_x.
apply/retractPG: (z) z_X (appr_trans z_x x_y); exact: apprxx.
Qed.

Lemma retractK X x : x \in X -> retract X x = Some x.
Proof.
move=> x_X; apply/appr_anti; rewrite retract_appr /=.
move: {-3 5}(x) x_X (apprxx x); exact/retractPG/apprxx.
Qed.

Lemma retractS X Y x :
  fsubset X Y ->
  obind (retract X) (retract Y x) = retract X x.
Proof.
move=> X_Y; apply/appr_anti/andP; split.
  case Y_x: (retract Y x)=> [y|] //=.
  apply/retractPG=> z z_X z_y.
  have y_x: y ⊑ x by move: (retract_appr Y x); rewrite Y_x.
  apply/retractPG: (z) z_X (appr_trans z_y y_x); exact: apprxx.
apply/retractPG=> z z_X z_x.
have: Some z ⊑ retract Y x.
  apply/retractPG: (z) (fsubsetP X_Y _ z_X) z_x; exact: apprxx.
case: (retract Y x) (retract_appr Y x)=> [y|] //= y_x z_y.
by apply/retractPG/apprxx: (z) z_X (z_y : z ⊑ y).
Qed.

Lemma retract_idem X x :
  obind (retract X) (retract X x) = retract X x.
Proof. exact/retractS/fsubsetxx. Qed.

Lemma retractU X Y x :
  retract X x ⊔ retract Y x = Coh (retract (proj_of_fset (X :|: Y)) x).
Proof.
apply/esym/lub_unique; case=> [oy|] //=; rewrite /appr /=.
apply/(sameP (retractPG _ _ _))/(iffP andP).
  case=> /retractPG X_x /retractPG Y_x z /lub_closureP [Z sub lubn_Z] z_x.
  suffices: Coh (Some z) ⊑ Coh oy by [].
  rewrite -lubn_Z lubn_apprG; apply/allP=> y y_Z.
  have y_z: y ⊑ z.
    by move: y y_Z; apply/allP; rewrite -lubn_appr lubn_Z apprxx.
  case/(fsubsetP sub _)/fsetUP: y_Z=> [y_X|y_Y].
  - by apply: X_x; rewrite // (appr_trans y_z).
  - by apply: Y_x; rewrite // (appr_trans y_z).
by move=> H; split; apply/retractPG=> z z_in z_x; apply: H=> //;
apply/fsubsetP: (z) z_in; rewrite (fsubset_trans (lub_closure_ext _));
rewrite // lub_closureS ?fsubsetUl ?fsubsetUr.
Qed.

End Retract.

Lemma retract_imfset (T S : domType true) (f : T -> S) (X : {proj T}) x :
  injective f -> lub_preserving f ->
  retract (mapp f X) (f x) = omap f (retract X x).
Proof.
move=> f_inj f_lub; apply: appr_anti; apply/andP; split.
- apply/retractPG=> _ /mappP - /(_ f_lub) [x' x'_X ->].
  rewrite inj_iso // => x'_x.
  move/retractPG/(_ _ x'_X x'_x): (apprxx (retract X x)).
  case: (retract X x)=> [x''|] //; rewrite !oapprE /= => x'_x''.
  by rewrite inj_iso.
- case X_x: (retract X x)=> [x'|] //=.
  move/retractPG: (apprxx (retract (mapp f X) (f x))); apply.
  + by rewrite mem_mapp // (retract_lub_closure X_x).
  + by rewrite inj_iso //; move: (retract_appr X x); rewrite X_x.
Qed.

Section FMapMonotone.

Variables (T : poType true) (S : ppoType true).
Implicit Types (f : {ffun T -> S}) (x y : T).

Definition monotoneb f :=
  all (fun '(x, y) => x ⊑ y ==> f x ⊑ f y)
      [seq (x, y) | x <- fsupp f, y <- fsupp f].

Lemma monotonebP f :
  reflect {in fsupp f &, monotone f} (monotoneb f).
Proof.
apply/(iffP allP).
- move=> fP x y xin yin; apply/implyP; move/(_ (x, y)): fP; apply.
  by apply/allpairsP; exists (x, y); split.
- move=> fP /= [_ _] /allpairsP [[x y] [/= xin yin [-> ->]]].
  by apply/implyP; apply: fP.
Qed.

Lemma monotoneb0 : monotoneb ⊥.
Proof. by apply/monotonebP; rewrite fsupp0. Qed.

End FMapMonotone.

Section Saturated.

Variables (T : domType true) (S : pdomType true).

Definition saturated (f : {ffun T -> S}) :=
  monotoneb f && (lub_closure (fsupp f) == fsupp f).

Record sat := Sat {
  sat_val : {ffun T -> S};
  _       : saturated sat_val
}.

Definition sat_of & phant (T -> S) := sat.
Identity Coercion sat_of_sat : sat_of >-> sat.

Canonical sat_subType := [subType for sat_val].
Definition sat_eqMixin := [eqMixin of sat by <:].
Canonical sat_eqType := Eval hnf in EqType sat sat_eqMixin.
Definition sat_choiceMixin := [choiceMixin of sat by <:].
Canonical sat_choiceType := Eval hnf in ChoiceType sat sat_choiceMixin.
Definition sat_ordMixin := [ordMixin of sat by <:].
Canonical sat_ordType := Eval hnf in OrdType sat sat_ordMixin.

Notation "{ 'sat' T }" := (sat_of (Phant T))
  (at level 0, format "{ 'sat'  T }").

Canonical sat_of_eqType := [eqType of {sat T -> S}].
Canonical sat_of_choiceType := [choiceType of {sat T -> S}].
Canonical sat_of_ordType := [ordType of {sat T -> S}].

Implicit Types (f g h : {sat T -> S}).

Lemma sat_suppP f : lub_closure (fsupp (val f)) == fsupp (val f).
Proof. by case/andP: (valP f). Qed.

Definition ssupp f : {proj T} := Proj (sat_suppP f).

Definition sapp (f : sat) x : S :=
  if retract (ssupp f) x is Some x' then val f x' else ⊥.

Local Coercion sapp : sat >-> Funclass.

Lemma sat_mono f : monotone f.
Proof.
move=> x y x_y; rewrite /sapp; move: (retract_mono (ssupp f) x_y).
case f_x: (retract (ssupp f) x) => [x'|]; rewrite ?botP //.
case f_y: (retract (ssupp f) y) => [y'|] // x'_y'.
by case/andP: (valP f)=> /monotonebP mono _; apply: mono;
rewrite ?(retract_lub_closure f_x) ?(retract_lub_closure f_y).
Qed.

Program Definition sat0 : {sat T -> S} := @Sat ⊥ _.
Next Obligation.
by rewrite /saturated monotoneb0 fsupp0 lub_closure0 eqxx.
Qed.

Lemma in_saturated_mkffun (f : T -> S) (X : {proj T}) :
  {in X &, monotone f} -> saturated (mkffun f X).
Proof.
move=> f_mono; apply/andP; split.
  apply/monotonebP=> y z y_in z_in y_z; rewrite !mkffunE.
  move/(fsubsetP (fsupp_ffun_of_fmap_sub _)): y_in.
  move/(fsubsetP (fsupp_ffun_of_fmap_sub _)): z_in.
  rewrite !domm_mkfmapf !in_fset => z_X y_X; rewrite z_X y_X; exact: f_mono.
rewrite eqEfsubset lub_closure_ext andbT.
apply/fsubsetP=> x /lub_closureP [Y sub lubn_Y].
rewrite fsupp_ffun_of_fmap in_fset mem_filter mem_domm mkfmapfE.
have x_X: x \in val X.
  rewrite -(eqP (valP X)); apply/lub_closureP; exists Y=> //.
  by rewrite (fsubset_trans sub) ?(fsubset_trans (fsupp_ffun_of_fmap_sub _));
  rewrite ?domm_mkfmapf ?fsvalK ?fsubsetxx.
rewrite x_X; have /fset0Pn [y y_Y] : Y != fset0.
  by apply/eqP=> e; rewrite e lubn0 in lubn_Y.
suffices: f x != ⊥ by rewrite andbT.
have y_X: y \in X.
  move: (fsubsetP sub _ y_Y); apply: contraTT=> y_X; apply/fsuppPn.
  by rewrite mkffunE (negbTE y_X).
have /(f_mono _ _ y_X x_X) y_x: y ⊑ x.
  by apply/allP: (y) y_Y; rewrite -lubn_appr lubn_Y apprxx.
apply: contraTN y_x => /eqP ->.
move/(fsubsetP sub _): y_Y; rewrite fsupp_ffun_of_fmap in_fset.
rewrite mem_filter mem_domm mkfmapfE; case: ifP; rewrite ?andbF //.
rewrite andbT => _; apply: contraNN=> f_y; apply/eqP/appr_anti.
rewrite apprE /= f_y; exact: botP.
Qed.

Lemma saturated_mkffun (f : T -> S) (X : {proj T}) :
  monotone f -> saturated (mkffun f X).
Proof.
move=> f_mono; apply: in_saturated_mkffun=> ????; exact: f_mono.
Qed.

Definition mksat (f : T -> S) (X : {proj T}) : {sat T -> S} :=
  if insub (mkffun f X) is Some g then g else sat0.

Lemma in_mksatE (f : T -> S) (X : {proj T}) x :
  {in X &, monotone f} ->
  mksat f X x = if retract X x is Some x' then f x' else ⊥.
Proof.
rewrite /sapp /mksat => f_mono.
have f_sat := in_saturated_mkffun f_mono.
rewrite insubT /=.
have X'P : forall x', x' \in ssupp (Sat f_sat) = (x' \in X) && (f x' != ⊥).
  move=> x'; rewrite /ssupp inE /= fsupp_ffun_of_fmap in_fset.
  by rewrite mem_filter !mem_domm mkfmapfE; case: (x' \in X);
  rewrite // andbT.
have sub: fsubset (ssupp (Sat f_sat)) X.
  by apply/fsubsetP=> x'; rewrite X'P; case/andP.
rewrite -(retractS _ sub); case X_x: (retract X x)=> [x'|] //=.
have [f_x'|f_x'] := altP (f x' =P ⊥).
  suffices ->: retract (ssupp (Sat f_sat)) x' = None by rewrite f_x'.
  apply/appr_anti; rewrite botP andbT.
  apply/retractPG=> y; rewrite X'P; case/andP=> y_X f_y y_x'.
  have x'_X: x' \in X by exact: retract_lub_closure X_x.
  move: (f_mono _ _ y_X x'_X y_x'); rewrite f_x' => e.
  suffices e': f y = ⊥ by rewrite e' eqxx in f_y.
  by apply/appr_anti; rewrite e botP.
rewrite retractK ?X'P ?f_x' ?(retract_lub_closure X_x) //.
by rewrite mkffunE ?(retract_lub_closure X_x).
Qed.

Lemma mksatE (f : T -> S) (X : {proj T}) x :
  monotone f ->
  mksat f X x = if retract X x is Some x' then f x' else ⊥.
Proof. move=> mono_f; apply: in_mksatE=> ????; exact: mono_f. Qed.

Lemma mksatK f (X : {proj T}) : fsubset (ssupp f) X -> f =1 mksat f X.
Proof.
move=> sub x; rewrite mksatE /sapp; try exact: sat_mono.
by rewrite -(retractS x sub); case: (retract _ x).
Qed.

Lemma val_mksat (f : T -> S) (X : {proj T}) :
  monotone f -> val (mksat f X) = mkffun f X.
Proof.
move=> mono_f; have f_sat := saturated_mkffun X mono_f.
by rewrite /mksat insubT.
Qed.

Lemma appr_mksat (f : T -> S) (X : {proj T}) x :
  monotone f -> mksat f X x ⊑ f x.
Proof.
move=> mono_f; rewrite mksatE //.
case X_x: retract=> [x'|]; rewrite ?botP //.
by apply: mono_f; move: (retract_appr X x); rewrite X_x.
Qed.

Definition sappr f g := val f ⊑ mkffun g (ssupp f).

Lemma sapprP f g : reflect (forall x, f x ⊑ g x) (sappr f g).
Proof.
apply/(iffP fapprP).
- move=> fg x; rewrite {1}/sapp.
  case fx: (retract _ x)=> [x'|]; rewrite ?botP //.
  have x'_x : x' ⊑ x by move: (retract_appr (ssupp f) x); rewrite fx.
  move: (fg x'); rewrite mkffunE (retract_lub_closure fx)=> fgx'.
  exact: appr_trans fgx' (sat_mono g x'_x).
- move=> fg x; rewrite mkffunE.
  case: ifPn=> [x_supp|/fsuppPn ->]; last by rewrite apprxx.
  by move: (fg x); rewrite {1}/sapp; rewrite retractK.
Qed.

Lemma sapprPn f g : reflect (exists x, f x ⋢ g x) (~~ sappr f g).
apply/(iffP fapprPn).
- case=> x fgx; exists x; apply: contraNN fgx.
  rewrite mkffunE; case: ifPn=> [fx|/fsuppPn ->]; last by rewrite apprxx.
  by rewrite {1}/sapp retractK.
- case=> x; rewrite {1}/sapp; case fx: (retract _ x)=> [x'|]; rewrite ?botP //.
  move=> fgx; exists x'; apply: contraNN fgx.
  rewrite mkffunE (retract_lub_closure fx)=> fgx; apply: appr_trans fgx _.
  by apply: sat_mono; move: (retract_appr (ssupp f) x); rewrite fx.
Qed.

Lemma sappr_ax : Po.axioms_of false sappr.
Proof.
split=> //.
- move=> f; apply/sapprP=> x; exact: apprxx.
- move=> g f h /sapprP fg /sapprP gh; apply/sapprP=> x.
  exact: (appr_trans (fg x) (gh x)).
Qed.

Definition sat_poMixin := PoMixin sappr_ax.
Canonical sat_poType := Eval hnf in PoType sat sat_poMixin.
Canonical sat_of_poType := Eval hnf in [poType of {sat T -> S}].

Lemma sat_botP f : sat0 ⊑ f.
Proof.
apply/sapprP=> x; rewrite /sapp /=; case: retract=> [?|]; exact/botP.
Qed.

Definition sat_ppoMixin := PPoMixin sat_botP.
Canonical sat_ppoType := Eval hnf in PPoType sat sat_ppoMixin.
Canonical sat_of_ppoType := Eval hnf in [ppoType of {sat T -> S}].

Lemma sapprE f g (X : {proj T}) :
  fsubset (ssupp f) X -> f ⊑ g = val f ⊑ mkffun g X.
Proof.
move=> sub; apply/(sameP idP)/(iffP idP); last first.
  rewrite apprE /= /sappr; move=> fg; apply: appr_trans fg _.
  exact: (mkffunS (sapp g)).
move=> /fapprP fg; apply/sapprP=> x; rewrite {1}/sapp.
case f_x: retract=> [x'|]; rewrite ?botP //.
apply: appr_trans (fg x') _; rewrite mkffunE.
rewrite (fsubsetP sub) ?(retract_lub_closure f_x) //.
by rewrite sat_mono //; move: (retract_appr (ssupp f) x); rewrite f_x.
Qed.

Definition slub f g : coh {sat T -> S} :=
  let X := projU (ssupp f) (ssupp g) in
  let f := mksat f X in
  let g := mksat g X in
  if val f ⊔ val g is Coh h then Coh (mksat h X)
  else Incoh.

Variant slub_spec f g : coh {sat T -> S} -> Prop :=
| SLubCoh h of (forall x, f x ⊔ g x = Coh (h x)) : slub_spec f g (Coh h)
| SLubIncoh x of f x ⊔ g x = Incoh : slub_spec f g Incoh.

Lemma slubP f g : slub_spec f g (slub f g).
Proof.
rewrite /slub.
set X := projU (ssupp f) (ssupp g).
set f' := mksat f X.
set g' := mksat g X.
case: flubP=> [h hP|x _ _]; last first.
  rewrite /f' /g' !val_mksat; try exact: sat_mono.
  rewrite !mkffunE; case: ifP => [_|]; last by rewrite lubxx.
  exact: SLubIncoh.
have h_mono: {in X &, monotone h}.
  move=> x y x_X y_X x_y; suff: Coh (h x) ⊑ Coh (h y) by [].
  rewrite -!hP mono_lub // /f' /g' val_mksat ?mkffunE ?x_X ?y_X;
  exact: sat_mono.
apply: SLubCoh=> x.
rewrite (@mksatK _ X (projUl (ssupp f) (ssupp g))).
rewrite (@mksatK _ X (projUr (ssupp f) (ssupp g))).
rewrite 2?mksatE ?in_mksatE //; try exact: sat_mono.
case x_X: (retract X x)=> [x'|]; rewrite ?lubxx // -hP.
rewrite /f' /g' !val_mksat ?mkffunE; try exact: sat_mono.
by rewrite (retract_lub_closure x_X).
Qed.

Lemma slub_appr f g h : slub f g ⊑ Coh h = (f ⊑ h) && (g ⊑ h).
Proof.
case: slubP=> [fg fgP|x]; last first.
  have [->|f_x] := altP (f x =P ⊥); first by rewrite lubBx.
  have [->|g_x] := altP (g x =P ⊥); first by rewrite lubxB.
  move=> incoh; apply/esym/negbTE/andP; case=> [/sapprP fh /sapprP gh].
  by move: (lub_appr (f x) (g x) (h x)); rewrite incoh fh gh.
apply/(sameP idP)/(iffP idP).
  case/andP=> /sapprP fh /sapprP gh; apply/sapprP=> x.
  suff: Coh (fg x) ⊑ Coh (h x) by [].
  by rewrite -fgP lub_appr fh gh.
move/sapprP=> fghP; apply/andP; split; apply/sapprP=> x;
apply: (@appr_trans _ _ (fg x)); rewrite ?fghP //;
by move: (appr_lubl (f x) (g x)) (appr_lubr (f x) (g x)); rewrite fgP.
Qed.

Definition sat_domMixin := DomMixin slub_appr.
Canonical sat_domType := Eval hnf in DomType sat sat_domMixin.
Canonical sat_of_domType := Eval hnf in [domType of {sat T -> S}].
Canonical sat_pdomType := Eval hnf in PDomType sat.
Canonical sat_of_pdomType := Eval hnf in PDomType {sat T -> S}.

End Saturated.

Notation "{ 'sat'  T }" := (sat_of (Phant T))
  (at level 0, format "{ 'sat'  T }").

Coercion sapp : sat >-> Funclass.

Section SaturatedMap.

Variables (T1 T2 : domType true) (S1 S2 : pdomType true).



Section Continuous.

Variables (T : domType true) (S : pdomType true).

Record cont := Cont {
  cont_val : {quot_po {sat T -> S}}
}.
Definition cont_of & phant (T -> S) := cont.
Identity Coercion cont_of_cont : cont_of >-> cont.

Notation "{ 'cont' T }" := (cont_of (Phant T))
  (at level 0, format "{ 'cont'  T }").

Canonical cont_subType := [newType for cont_val].
Definition cont_eqMixin := [eqMixin of cont by <:].
Canonical cont_eqType := Eval hnf in EqType cont cont_eqMixin.
Definition cont_choiceMixin := [choiceMixin of cont by <:].
Canonical cont_choiceType := Eval hnf in ChoiceType cont cont_choiceMixin.
Definition cont_ordMixin := [ordMixin of cont by <:].
Canonical cont_ordType := Eval hnf in OrdType cont cont_ordMixin.
Definition cont_poMixin := [poMixin of cont by <:].
Canonical cont_poType := Eval hnf in PoType cont cont_poMixin.
Canonical cont_subPoType := Eval hnf in SubPoType cont (fun x y => erefl).
Definition cont_ppoMixin := [ppoMixin of cont by <: using erefl].
Canonical cont_ppoType := Eval hnf in PPoType cont cont_ppoMixin.
Definition cont_domMixin :=
  [domMixin of cont by <: using (fun f g h e => erefl)].
Canonical cont_domType := Eval hnf in DomType cont cont_domMixin.
Canonical cont_subDomType := Eval hnf in [subDomType for cont].
Canonical cont_pdomType := Eval hnf in PDomType cont.

Canonical cont_of_subType := Eval hnf in [subType of {cont T -> S}].
Canonical cont_of_eqType := Eval hnf in [eqType of {cont T -> S}].
Canonical cont_of_choiceType := Eval hnf in [choiceType of {cont T -> S}].
Canonical cont_of_ordType := Eval hnf in [ordType of {cont T -> S}].
Canonical cont_of_poType := Eval hnf in [poType of {cont T -> S}].
Canonical cont_of_ppoType := Eval hnf in [ppoType of {cont T -> S}].
Canonical cont_of_domType := Eval hnf in [domType of {cont T -> S}].
Canonical cont_of_subDomType := Eval hnf in [subDomType for {cont T -> S}].
Canonical cont_of_pdomType := Eval hnf in [pdomType of {cont T -> S}].

Implicit Types f g h : {cont T -> S}.

Definition capp (f : cont) (x : T) : S := repr (val f) x.

Coercion capp : cont >-> Funclass.

Lemma cappE (f : {sat T -> S}) : Cont (\pi f) =1 f.
Proof.
move=> x; rewrite /capp /=; case: piP=> g /eqP; rewrite piE.
by case/andP=> /sapprP fg /sapprP gf; apply: appr_anti; rewrite fg gf.
Qed.

Lemma capprP f g : reflect (forall x, f x ⊑ g x) (f ⊑ g).
Proof.
case: f g=> [f] [g]; rewrite /capp appr_val /=.
elim/quotP: f=> f ->; elim/quotP: g=> g ->; rewrite qapprE.
exact: sapprP.
Qed.

Lemma capprPn f g : reflect (exists x, f x ⋢ g x) (f ⋢ g).
Proof.
case: f g=> [f] [g]; rewrite /capp appr_val /=.
elim/quotP: f=> f ->; elim/quotP: g=> g ->; rewrite qapprE.
exact: sapprPn.
Qed.

Lemma eq_cont f g : f =1 g <-> f = g.
Proof.
by split=> [|-> //] e; apply: appr_anti; apply/andP; split;
apply/capprP=> x; rewrite e apprxx.
Qed.

Lemma clubE f g :
  f ⊔ g = if val f ⊔ val g is Coh h then Coh (Cont h) else Incoh.
Proof. by rewrite lub_val; case: lub=> [[h]|]. Qed.

Variant club_spec f g : coh {cont T -> S} -> Prop :=
| CLubCoh h of (forall x, f x ⊔ g x = Coh (h x)) : club_spec f g (Coh h)
| CLubIncoh x of f x ⊔ g x = Incoh : club_spec f g Incoh.

Lemma clubP f g : club_spec f g (f ⊔ g).
Proof.
case: f g=> [f] [g]; rewrite clubE /=.
elim/quotP: f=> f ef; elim/quotP: g=> g eg.
rewrite /lub /= /qlub ef eg /lub /=; case: slubP=> [h hP|].
- apply: CLubCoh=> x; rewrite /capp /= ef eg hP.
  case: piP=> h' /eqP; rewrite piE; case/andP=> [/sapprP h_h' /sapprP h'_h].
  by congr Coh; apply: appr_anti; rewrite h_h' h'_h.
- by move=> x incoh; apply: (@CLubIncoh _ _ x); rewrite /capp /= ef eg.
Qed.

Definition mkcont (f : T -> S) (X : {proj T}) : {cont T -> S} :=
  Cont (\pi (mksat f X)).

Lemma in_mkcontE (f : T -> S) (X : {proj T}) x :
  {in X &, monotone f} ->
  mkcont f X x = if retract X x is Some x' then f x' else ⊥.
Proof. by move=> f_mono; rewrite /mkcont cappE in_mksatE. Qed.

Lemma mkcontE (f : T -> S) (X : {proj T}) x :
  monotone f ->
  mkcont f X x = if retract X x is Some x' then f x' else ⊥.
Proof. move=> f_mono; rewrite in_mkcontE // => ????; exact: f_mono. Qed.

End Continuous.

Section MapProperties.

Variables (T T' T'' : ordType) (S S' S'' : domType true).
Implicit Types (f : {fmap T -> S}).
Implicit Types (h : T -> T') (g : S -> S').

Lemma mapm2_mono h g :
  injective h -> monotone g -> monotone (mapm2 h g).
Proof.
move=> h_inj g_mono f1 f2 /fapprP f1f2; apply/fapprP=> x'.
have [|/dommPn -> //] := boolP (x' \in domm (mapm2 h g f1)).
rewrite domm_map2; case/imfsetP=> {x'} x xin ->; rewrite !mapm2E //.
by case/dommP: xin (f1f2 x)=> y1 ->; case: (f2 x)=> [y2|//] /= /g_mono.
Qed.

Lemma mapm2_iso h g :
  injective h -> isotone g -> isotone (mapm2 h g).
Proof.
move=> h_inj g_iso f1 f2; apply/(sameP idP)/(iffP idP).
  exact: mapm2_mono h_inj (iso_mono g_iso) _ _.
move=> /fapprP f1f2; apply/fapprP=> x; move: (f1f2 (h x)).
rewrite !mapm2E //; case: (f1 x) (f2 x)=> [y1|//] [y2|//] /=.
by rewrite oapprE g_iso.
Qed.

(* FIXME: This proof has to be easier *)
Lemma mapm2_lub h g :
  injective h -> lub_preserving g -> lub_preserving (mapm2 h g).
Proof.
move=> h_inj g_lub f1 f2; apply/esym/lub_unique.
move=> f3; apply/(sameP andP)/(iffP idP).
- case ef12: (f1 ⊔ f2)=> [f12|//] /=.
  move=> /fapprP f12P.
  suffices H: forall x, (mapm2 h g f1 x ⊑ f3 x) && (mapm2 h g f2 x ⊑ f3 x).
    by split; apply/fapprP=> x; case/andP: (H x).
  move=> x; rewrite is_lub_lub.
  have [|] := boolP (x \in h @: domm f12); last first.
    rewrite (domm_lub ef12) imfsetU in_fsetU negb_or.
    rewrite -2!(domm_map2 h g) !mem_domm.
    by case: (mapm2 h g f1 x) (mapm2 h g f2 x)=> [?|] [?|].
  case/imfsetP=> {x} x xin ->; move: (f12P (h x)); rewrite !mapm2E //.
  move: xin; rewrite mem_domm (flubE ef12).
  case: (f1 x) (f2 x)=> [x1|] [x2|] //=.
  by rewrite ![Some _ ⊔ _]/lub /= g_lub; case: (x1 ⊔ x2)=> //=.
- move/andP; rewrite is_lub_lub.
  case ef12': (mapm2 _ _ _ ⊔ mapm2 _ _ _)=> [f12'|//] f12f3.
  case ef12: (f1 ⊔ f2)=> [f12|] /=.
  + apply/fapprP=> x.
    have [|] := boolP (x \in h @: domm f12); last first.
      by rewrite -(domm_map2 h g) mem_domm; case: (mapm2 _ _ _ x).
    case/imfsetP=> {x} x xin ->.
    rewrite mapm2E // (flubE ef12).
    move/fapprP: f12f3=> /(_ (h x)); apply: appr_trans.
    rewrite (flubE ef12') !mapm2E //.
    move: xin; rewrite mem_domm (flubE ef12).
    case: (f1 x) (f2 x)=> [x1|] [x2|] //=; try by rewrite apprxx.
    by rewrite /lub /= g_lub; case: (_ ⊔ _)=> //= ?; rewrite apprxx.
  + case/flub_None: ef12=> x.
    case ex1: (f1 x)=> [x1|//]; case ex2: (f2 x)=> [x2|//].
    rewrite /lub /=; case ex12: (x1 ⊔ x2)=> [//|] _.
    suffices: f12' (h x).
      by rewrite (flubE ef12') !mapm2E // ex1 ex2 /= /lub /= g_lub ex12.
    rewrite -mem_domm (domm_lub ef12') in_fsetU !mem_domm !mapm2E //.
    by rewrite ex1.
Qed.

End MapProperties.

Section MapMonotone.

Variables T T' S S' : domType.
Implicit Types (f : T -> T') (g : S -> S').
Implicit Types (h : {fmap T -> S}).

Lemma mapm2_mono2 f g h :
  isotone f -> monotone g -> monotoneb h ->
  monotoneb (mapm2 f g h).
Proof.
move=> f_iso g_mono /monotonebP h_mono; apply/monotonebP.
rewrite domm_map2=> _ _ /imfsetP [x xin ->] /imfsetP [y yin ->].
rewrite f_iso ?mapm2E; try exact: iso_inj.
move=> /(h_mono _ _ xin yin).
by case/dommP: xin=> x' ->; case/dommP: yin=> y' -> /g_mono.
Qed.

End MapMonotone.

Module SubDom.

Section ClassDef.

Variables (T : domType) (P : pred T).

Record type := Pack {
  sort : subType P;
  _    : lub_closed P
}.

Local Coercion sort : type >-> subType.

Variable sT : type.

Implicit Types x y z : sT.

Definition subType_appr x y := val x ⊑ val y.
Definition subType_lub x y : option sT :=
  obind (fun z : T => insub z) (val x ⊔ val y).

Lemma lub_val x y : val x ⊔ val y = omap val (subType_lub x y).
Proof.
rewrite /subType_lub; case: sT x y => /= S SP x y.
case e: lub => [z|] //=.
by rewrite (insubT P (SP _ _ (valP x) (valP y) _ e)) /= SubK.
Qed.

Lemma subTypeP : Dom.axioms subType_appr subType_lub.
Proof.
split.
- move=> x; exact: apprxx.
- move=> y x z; exact: appr_trans.
- move=> x y xy; exact/val_inj/anti_appr.
by move=> x y z; rewrite /subType_appr is_lub_lub lub_val; case: subType_lub.
Qed.

Definition domMixin := DomMixin subTypeP.
Definition domType := DomType sT domMixin.

Definition pack (sT : subType P) m & phant sT := Pack sT m.

End ClassDef.

Module Import Exports.
Coercion sort : type >-> subType.
Coercion domType : type >-> Dom.type.
Canonical domType.
Notation subDomType := type.
Notation SubDomType T m := (@pack _ _ _ m (Phant T)).
Notation "[ 'domMixin' 'of' T 'by' <: ]" :=
    (domMixin _ : Dom.mixin_of T)
  (at level 0, format "[ 'domMixin'  'of'  T  'by'  <: ]") : form_scope.
End Exports.

End SubDom.
Export SubDom.Exports.

Section SubDomTheory.

Variables (T : domType) (P : pred T) (sT : subDomType P).
Implicit Types x y z : sT.

Lemma lub_val x y : val x ⊔ val y = omap val (x ⊔ y).
Proof. exact: SubDom.lub_val. Qed.

Lemma appr_val x y : x ⊑ y = val x ⊑ val y.
Proof. by rewrite !appr_lubL lub_val; case: (_ ⊔ _). Qed.

End SubDomTheory.

Section ProjDom.

Variables (T : domType) (xs : proj T).

Structure proj_dom := ProjDom {
  proj_elt :> T;
  _        :  proj_elt \in xs
}.

Canonical proj_dom_subType := [subType for proj_elt].
Definition proj_dom_eqMixin := [eqMixin of proj_dom by <:].
Canonical proj_dom_eqType := Eval hnf in EqType proj_dom proj_dom_eqMixin.
Definition proj_dom_choiceMixin := [choiceMixin of proj_dom by <:].
Canonical proj_dom_choiceType :=
  Eval hnf in ChoiceType proj_dom proj_dom_choiceMixin.
Definition proj_dom_ordMixin := [ordMixin of proj_dom by <:].
Canonical proj_dom_ordType :=
  Eval hnf in OrdType proj_dom proj_dom_ordMixin.

Lemma proj_domP : lub_closed (mem xs).
Proof. apply/lub_closedP/eqP; exact: (valP xs). Qed.

Canonical proj_dom_subDomType :=
  Eval hnf in SubDomType proj_dom proj_domP.
Definition proj_dom_domMixin := [domMixin of proj_dom by <:].
Canonical proj_dom_domType :=
  Eval hnf in DomType proj_dom proj_dom_domMixin.

End ProjDom.

Coercion proj_dom : proj >-> Sortclass.

Module Sat.

Section Def.

Variable T S : domType.
Implicit Types (f g : {fmap T -> S}) (x : T).

Definition saturated f :=
  (lub_closure (domm f) == domm f) && monotoneb f.

Lemma saturated0 : saturated emptym.
Proof.
by rewrite /saturated domm0 lub_closure0 eqxx monotoneb0.
Qed.

Lemma saturated1 x y : saturated (setm emptym x y).
Proof.
rewrite /saturated domm_set domm0 fsetU0 lub_closure1 eqxx.
apply/monotonebP=> x1 x2; rewrite domm_set domm0 fsetU0.
by move=> /fset1P -> /fset1P -> _; rewrite apprxx.
Qed.

Record sat := Sat {
  sat_val : {fmap T -> S};
  _       : saturated sat_val
}.

Canonical sat_subType := [subType for sat_val].
Definition sat_eqMixin := [eqMixin of sat by <:].
Canonical sat_eqType := Eval hnf in EqType sat sat_eqMixin.
Definition sat_choiceMixin := [choiceMixin of sat by <:].
Canonical sat_choiceType := Eval hnf in ChoiceType sat sat_choiceMixin.
Definition sat_ordMixin := [ordMixin of sat by <:].
Canonical sat_ordType := Eval hnf in OrdType sat sat_ordMixin.

Definition app f x :=
  odflt (lubn (fset (pmap f [seq x' <- domm f | x' ⊑ x]))) None.

Definition saturate f : option sat :=
  let g := mkfmapfp (app f) (lub_closure (domm f)) in
  if f ⊑ g then insub g else None.

Variant saturate_spec f : option sat -> Type :=
| SaturateSome fs of
  f ⊑ sat_val fs &
  (forall gs, f ⊑ sat_val gs -> sat_val fs ⊑ sat_val gs) :
  saturate_spec f (Some fs)
| SaturateNone of
  (forall gs, f ⋢ sat_val gs) :
  saturate_spec f None.

Lemma saturateP f : saturate_spec f (saturate f).
Proof.
rewrite /saturate; set g := mkfmapfp (app f) _.
have gP1: forall gs, f ⊑ sat_val gs -> g ⊑ sat_val gs.
  move=> gs /fapprP f_gs; apply/fapprP=> x.
  rewrite /g mkfmapfpE; case: ifP=> [x_dom|//].
  rewrite /app; case: lubnP=> //= y not0 yP.
  have /dommP [y' gs_x]: x \in domm (sat_val gs).
    move: (x) x_dom; apply/fsubsetP/lub_closure_min.
      by apply/domm_appr/fapprP.
    by apply/lub_closedP/eqP; case/andP: (valP gs).
  rewrite gs_x; suffices: y ⊑ y' by [].
  rewrite -{}yP; apply/allP=> y''; rewrite in_fset mem_pmap.
  case/mapP=> x''; rewrite mem_filter; case/andP=> x''_x _ /esym f_x''.
  move/(_ x''): f_gs; rewrite f_x''.
  case gs_x'': (sat_val gs x'')=> [y'''|//] y''_y'''.
  suffices: y''' ⊑ y' by apply: appr_trans.
  have /andP [_ /monotonebP mono] := valP gs.
  by move/(_ x'' x _ _ x''_x): mono; rewrite gs_x gs_x''; apply;
  rewrite mem_domm ?gs_x ?gs_x''.
have gP2: forall gs, f ⊑ sat_val gs -> f ⊑ g.
  move=> gs f_gs; apply/fapprP=> x.
  rewrite mkfmapfpE; case f_x: (f x)=> [y|//].
  rewrite (fsubsetP (lub_closure_ext (domm f))) ?mem_domm ?f_x // /app.
  move/fapprP/(_ x): (f_gs); rewrite f_x.
  case gs_x: (sat_val gs x)=> [y'|//] y_y'.
  set Y := fset (pmap f _).
  have Yn0: Y != fset0.
    apply/fset0Pn; exists y.
    rewrite /Y in_fset mem_pmap -f_x; apply/mapP.
    by exists x=> //; rewrite mem_filter apprxx mem_domm f_x.
  have y'_ub: all (fun y => y ⊑ y') Y.
    apply/allP=> y''; rewrite /Y in_fset mem_pmap.
    case/mapP=> x'; rewrite mem_filter; case/andP=> x'_x _ /esym f_x'.
    move/fapprP/(_ x'): (f_gs); rewrite f_x'.
    case gs_x': (sat_val gs x')=> [y'''|//] y''_y'''.
    suffices: y''' ⊑ y' by apply: appr_trans.
    have /andP [_ /monotonebP mono] := valP gs.
    move/(_ x' x _ _ x'_x): mono.
    by rewrite gs_x' gs_x; apply; rewrite mem_domm ?gs_x' ?gs_x.
  move: (is_lubn_lubn Y y'); rewrite Yn0 y'_ub.
  case lubn_YP: (lubn Y)=> [lubn_Y|//] /= _.
  move: (lubn_appr_conv lubn_Y lubn_YP); rewrite apprxx.
  move=> /allP; apply; rewrite /Y in_fset mem_pmap -f_x.
  by apply/mapP; exists x; rewrite // mem_filter apprxx mem_domm f_x.
have gP3: forall gs, f ⊑ sat_val gs -> saturated g.
  move=> gs f_gs; rewrite /saturated.
  have domm_g: domm g = lub_closure (domm f).
    rewrite /g domm_mkfmapfp; apply/eq_fset=> x.
    rewrite in_fset mem_filter andbC.
    have [x_in|] //= := boolP (x \in _).
    rewrite /app; set Y := fset _.
    have /lub_closureP [X Xsub lubn_XP] := x_in.
    have /fset0Pn [x0 x0_in] : X != fset0.
      by apply: lubn_neq0; rewrite lubn_XP.
    case/(fsubsetP Xsub)/dommP: (x0_in)=> y f_x0.
    have Yn0: Y != fset0.
      apply/fset0Pn; exists y; rewrite /Y in_fset mem_pmap -f_x0.
      apply/mapP; exists x0; rewrite // mem_filter mem_domm f_x0.
      by rewrite (lubn_ub lubn_XP).
    move/fapprP/(_ x0): (f_gs)=> f_x0_gs_x0.
    have gs_x: x \in domm (sat_val gs).
      move: (x) x_in; apply/fsubsetP/lub_closure_min.
        by apply/domm_appr.
      by apply/lub_closedP/eqP; case/andP: (valP gs).
    have /andP [_ /monotonebP' mono] := valP gs.
    have := appr_trans f_x0_gs_x0 (mono _ _ (lubn_ub lubn_XP x0_in) gs_x).
    rewrite f_x0; case gs_xE: (val gs x)=> [y'|] //= y_y'.
    have y'_ub: all (fun y'' => y'' ⊑ y') Y.
      apply/allP=> y''; rewrite /Y in_fset mem_pmap.
      case/mapP=> x'; rewrite mem_filter.
      case/andP=> x'_x _ /esym f_x'.
      move/fapprP/(_ x'): (f_gs).
      rewrite f_x'; case gs_x': (sat_val gs x')=> [y'''|] // y''_y'''.
      suffices: y''' ⊑ y' by apply: appr_trans.
      by move/(_ _ _ x'_x): mono; rewrite mem_domm gs_xE gs_x'; apply.
    by move: (is_lubn_lubn Y y'); rewrite Yn0 y'_ub; case: (lubn _).
  rewrite domm_g lub_closure_idem eqxx /=.
  apply/monotonebP'=> x1 x2 x1x2.
  rewrite /g domm_mkfmapfp in_fset mem_filter.
  case/andP=> app_f_x2 x2_in.
  rewrite !mkfmapfpE x2_in; case: ifP=> // x1_in.
  move: app_f_x2; rewrite /app.
  set Y1 := fset (pmap f [seq x' <- domm f | x' ⊑ x1]).
  set Y2 := fset (pmap f [seq x' <- domm f | x' ⊑ x2]).
  have /lubnS: fsubset Y1 Y2.
    apply/fsubsetP=> y; rewrite /Y1 /Y2 !in_fset !mem_pmap.
    case/mapP=> x; rewrite mem_filter; case/andP=> x_x1 _ /esym f_x.
    apply/mapP; exists x; rewrite -?f_x // mem_filter (appr_trans x_x1) //.
    by rewrite mem_domm f_x.
  case: (lubn Y1)=> [y1|] //=.
  by case: (lubn Y2).
case: ifPn=> [fg|/fapprPn fgN]; last first.
  apply: SaturateNone=> gs; apply/negP=> /gP2/fapprP/(_ (xchoose fgN)).
  by rewrite (negbTE (xchooseP fgN)).
case: insubP=> [/= gs sat_g e|gN]; last first.
  apply: SaturateNone=> gs; apply: contra gN; exact: gP3.
by apply: SaturateSome; rewrite e.
Qed.

Implicit Types fs gs hs : sat.

Definition sat_appr (fs gs : sat) : bool :=
  sat_val fs ⊑ sat_val gs.

Definition sat_lub (fs gs : sat) : option sat :=
  if sat_val fs ⊔ sat_val gs is Some hs then saturate hs else None.

Lemma sat_lubP : Dom.axioms sat_appr sat_lub.
Proof.
rewrite /sat_appr /sat_lub; split.
- by move=> fs; rewrite apprxx.
- by move=> hs fs gs; apply: appr_trans.
- by move=> fs gs /anti_appr/val_inj.
move=> fs gs hs; rewrite is_lub_lub; case: lub=> // h.
case: saturateP=> [fgs|/(_ hs)/negbTE ->] // h_fgs fgs_opt.
apply/(sameP idP)/(iffP idP); first by apply: appr_trans.
exact: fgs_opt.
Qed.

Definition sat_domMixin := DomMixin sat_lubP.
Canonical sat_domType := Eval hnf in DomType sat sat_domMixin.

End Def.

End Sat.

Module Cont.

Section Def.

Variables T S : domType.

Record precont := PreCont { sat_of : Sat.sat T S }.

Definition app f x := obind f (retract (domm (val f)) x).

Implicit Types fi gi hi : {f | saturated f}.

Definition cont_appr fi gi :=
  all (fun x => app (val fi) x ⊑ app (val gi) x)
      (lub_closure (domm (val fi) :|: domm (val gi))).

Lemma cont_apprP fi gi :
  reflect (forall x, app (val fi) x ⊑ app (val gi) x) (cont_appr fi gi).
Proof.
apply/(iffP allP)=> //; move=> efg x; rewrite /app.
rewrite -(retractS x (fsubsetUl (domm (val fi)) (domm (val gi)))).
rewrite -(retractS x (fsubsetUr (domm (val fi)) (domm (val gi)))).
case e: (retract (_ :|: _) x)=> [x'|] //=.
exact: (efg _ (retract_lub_closure e)).
Qed.

Lemma cont_apprPn fi gi :
  reflect (exists x, app (val fi) x ⋢ app (val gi) x) (~~ cont_appr fi gi).
Proof.
apply/(iffP allPn); first by case; eauto.
case=> x; rewrite /app.
rewrite -(retractS x (fsubsetUl (domm (val fi)) (domm (val gi)))).
rewrite -(retractS x (fsubsetUr (domm (val fi)) (domm (val gi)))).
case ex: (retract (domm (val fi) :|: domm (val gi)) x)=> [x'|] //=.
move=> fg; exists x'=> //; exact: retract_lub_closure ex.
Qed.

Lemma cont_apprxx : reflexive cont_appr.
Proof. by move=> fi; apply/cont_apprP=> x; rewrite apprxx. Qed.

Lemma cont_appr_trans : transitive cont_appr.
Proof.
move=> gi fi hi /cont_apprP fg /cont_apprP gh.
apply/cont_apprP=> x; exact: appr_trans (fg x) (gh x).
Qed.

Lemma app_mono fi gi x1 x2 :
  cont_appr fi gi -> x1 ⊑ x2 -> app (val fi) x1 ⊑ app (val gi) x2.
Proof.
rewrite /app => /cont_apprP figi x1x2.
apply: (@appr_trans _ (obind (val fi) (retract (domm (val fi)) x2))).
  move: (retract_mono (domm (val fi)) x1x2).
  case e1: (retract (domm (val fi)) x1)=> [x1'|] //=.
  case e2: (retract (domm (val fi)) x2)=> [x2'|] //=.
  rewrite oapprE=> x1'x2'.
  case/andP: (valP fi) => /eqP closed /monotonebP mono.
  rewrite -closed in mono.
  exact: mono (retract_lub_closure e1) (retract_lub_closure e2) x1'x2'.
exact/figi.
Qed.

Notation pcont_lub fi gi :=
  (mkfmapfp (fun x => odflt None (app (val fi) x ⊔ app (val gi) x))
            (lub_closure (domm (val fi) :|: domm (val gi)))).

Definition cont_lub fi gi : option {f | saturated f} :=
  if insub (pcont_lub fi gi) is Some hi then
    if cont_appr fi hi && cont_appr gi hi then Some hi
    else None
  else None.

Lemma cont_lubP : QDom.axioms cont_appr cont_lub.
Proof.
split=> /=.
- move=> fq; exact: cont_apprxx.
- move=> gq fq hq; exact: cont_appr_trans.
move=> fi gi hi; rewrite /cont_lub /=.
set clos := lub_closure (domm (val fi) :|: domm (val gi)).
set fg   := mkfmapfp _ clos.
have e :
  forall hi, fsubset (domm (val hi)) (domm (val fi) :|: domm (val gi)) ->
  forall x, app (val hi) x = obind (app (val hi)) (retract clos x).
  move=> hi' sub.
  move: (fsubset_trans sub (lub_closure_ext _)) => {sub} sub x.
  by rewrite /app -(retractS _ sub); case: (retract clos x).
have ret_clos : forall x x', retract clos x = Some x' -> x' \in clos.
  move=> x x' ex; move: (retract_lub_closure ex).
  by rewrite lub_closure_idem => ->.
move: {e} (e _ (fsubsetUl _ _)) (e _ (fsubsetUr _ _))=> fE gE.
have [/allP coh|/allPn [x x_in incoh]] :=
  boolP (all (fun x => app (val fi) x ⊔ app (val gi) x) clos).
  have {coh} coh : forall x, app (val fi) x ⊔ app (val gi) x.
    move=> x; rewrite fE gE; case ex: (retract clos x) => [x'|] //=.
    apply: coh; rewrite /clos -lub_closure_idem.
    by apply: retract_lub_closure ex.
  have domm_fg : domm fg = clos.
    apply/eq_fset=> x'; rewrite domm_mkfmapfp in_fset mem_filter andbC.
    have [in_clos|] //= := boolP (x' \in lub_closure _).
    move: (coh x').
    case fi_x': (app (val fi) x')=> [y1|] //=;
    case gi_x': (app (val gi) x')=> [y2|] //=.
      by rewrite /lub /=; case: lub.
    move: fi_x'; rewrite /app.
    case e_fi_x': (retract (domm (val fi)) x')=> [x''|] //=.
      move=> fi_x''; move: (retract_lub_closure e_fi_x').
      case/andP: (valP fi)=> /eqP -> _.
      by rewrite mem_domm fi_x''.
    move=> _ _; move: gi_x'; rewrite /app.
    case e_gi_x': (retract (domm (val gi)) x')=> [x''|] //=.
      move=> gi_x''; move: (retract_lub_closure e_gi_x').
      case/andP: (valP gi)=> /eqP ->.
      by rewrite mem_domm gi_x''.
    by move/retractK: in_clos; rewrite retractU e_fi_x' e_gi_x'.
  have fgE : forall x, obind fg (retract clos x)
                       = odflt None (app (val fi) x ⊔ app (val gi) x).
    move=> x; rewrite fE gE; case ex: (retract clos x)=> [x'|] //=.
    by rewrite mkfmapfpE (ret_clos _ _ ex).
  have Pfg : (lub_closure (domm fg) == domm fg) && monotoneb fg.
    rewrite domm_fg /clos lub_closure_idem eqxx /=.
    apply/monotonebP=> x1 x2 in1 in2 x1x2; move: (fgE x1) (fgE x2) (in2).
    rewrite {1 2}domm_fg in in1 in2.
    rewrite mem_domm ?retractK ?lub_closure_idem //= => -> ->.
    move: (coh x1) (coh x2).
    case el1: (app (val fi) x1 ⊔ app (val gi) x1)=> [[l1|]|] //= _.
    case el2: (app (val fi) x2 ⊔ app (val gi) x2)=> [[l2|]|] //= _.
    move: (is_lub_lub (app (val fi) x1) (app (val gi) x1) (Some l2)).
    rewrite el1 => <- => _; apply/andP; split.
      exact: (appr_trans (app_mono (cont_apprxx fi) x1x2) (lub_apprL el2)).
    exact: (appr_trans (app_mono (cont_apprxx gi) x1x2) (lub_apprR el2)).
  rewrite insubT.
  set fgi : {f | saturated f} := Sub fg Pfg.
  have {fgE} fgE : forall x, app (val fgi) x =
                             odflt None (app (val fi) x ⊔ app (val gi) x).
    by move=> x; rewrite {1}/app /= domm_fg.
  move: fgi fgE => /= {fg Pfg domm_fg} fgi fgiE.
  have -> /= : cont_appr fi fgi && cont_appr gi fgi.
    apply/andP; split.
      apply/cont_apprP=> x; rewrite fgiE fE gE.
      case ex: (retract clos x)=> [x'|] //=.
      move: (coh x').
      case ey: lub=> [y|] //= _.
      exact: (lub_apprL ey).
    apply/cont_apprP=> x; rewrite fgiE fE gE.
    case ex: (retract clos x)=> [x'|] //=.
    move: (coh x').
    case ey: lub=> [y|] //= _.
    exact: (lub_apprR ey).
  apply/(sameP andP)/(iffP (cont_apprP _ _)).
    move=> fgi_hi; split; apply/allP=> x in_clos.
      move: (is_lub_lub (app (val fi) x) (app (val gi) x) (app (val hi) x)).
      move: (fgi_hi x) (coh x); rewrite fgiE.
      by case: lub=> /= [y|] // -> _ /andP [].
    move: (is_lub_lub (app (val fi) x) (app (val gi) x) (app (val hi) x)).
    move: (fgi_hi x) (coh x); rewrite fgiE.
    by case: lub=> /= [y|] // -> _ /andP [].
  case=> /cont_apprP fi_hi /cont_apprP gi_hi x; rewrite fgiE; move: (coh x).
  move: (is_lub_lub (app (val fi) x) (app (val gi) x) (app (val hi) x)).
  by rewrite fi_hi gi_hi /=; case: lub.
have {incoh} incoh : forall hi', ~~ (cont_appr fi hi' && cont_appr gi hi').
  move=> hi'; apply: contra incoh => /andP [/cont_apprP fiP /cont_apprP giP].
  move: (is_lub_lub (app (val fi) x) (app (val gi) x) (app (val hi') x)).
  by rewrite fiP giP; case: lub.
rewrite (negbTE (incoh hi)); case: insubP=> /= [fgi inc|] //.
by rewrite (negbTE (incoh fgi)).
Qed.

Canonical cont_predom := Eval hnf in QDom.PreDom cont_lubP.

(* FIXME: Using a regular definition here makes it harder for Coq to figure out
   that the coercion into functions below is valid. *)

Record type (p : phant (T -> S)) := Cont {
  quot_of_cont : {qdom cont_appr}
}.



Module Cont.

Section Def.

Variable T S : domType.
Implicit Types (f g : {fmap T -> S}) (x : T).

Local Open Scope quotient_scope.

Definition saturated f :=
  (lub_closure (domm f) == domm f) && monotoneb f.

Lemma saturated0 : saturated emptym.
Proof.
by rewrite /saturated domm0 lub_closure0 eqxx monotoneb0.
Qed.

Lemma saturated1 x y : saturated (setm emptym x y).
Proof.
rewrite /saturated domm_set domm0 fsetU0 lub_closure1 eqxx.
apply/monotonebP=> x1 x2; rewrite domm_set domm0 fsetU0.
by move=> /fset1P -> /fset1P -> _; rewrite apprxx.
Qed.

Definition app f x := obind f (retract (domm f) x).

Implicit Types fi gi hi : {f | saturated f}.

Definition cont_appr fi gi :=
  all (fun x => app (val fi) x ⊑ app (val gi) x)
      (lub_closure (domm (val fi) :|: domm (val gi))).

Lemma cont_apprP fi gi :
  reflect (forall x, app (val fi) x ⊑ app (val gi) x) (cont_appr fi gi).
Proof.
apply/(iffP allP)=> //; move=> efg x; rewrite /app.
rewrite -(retractS x (fsubsetUl (domm (val fi)) (domm (val gi)))).
rewrite -(retractS x (fsubsetUr (domm (val fi)) (domm (val gi)))).
case e: (retract (_ :|: _) x)=> [x'|] //=.
exact: (efg _ (retract_lub_closure e)).
Qed.

Lemma cont_apprPn fi gi :
  reflect (exists x, app (val fi) x ⋢ app (val gi) x) (~~ cont_appr fi gi).
Proof.
apply/(iffP allPn); first by case; eauto.
case=> x; rewrite /app.
rewrite -(retractS x (fsubsetUl (domm (val fi)) (domm (val gi)))).
rewrite -(retractS x (fsubsetUr (domm (val fi)) (domm (val gi)))).
case ex: (retract (domm (val fi) :|: domm (val gi)) x)=> [x'|] //=.
move=> fg; exists x'=> //; exact: retract_lub_closure ex.
Qed.

Lemma cont_apprxx : reflexive cont_appr.
Proof. by move=> fi; apply/cont_apprP=> x; rewrite apprxx. Qed.

Lemma cont_appr_trans : transitive cont_appr.
Proof.
move=> gi fi hi /cont_apprP fg /cont_apprP gh.
apply/cont_apprP=> x; exact: appr_trans (fg x) (gh x).
Qed.

Lemma app_mono fi gi x1 x2 :
  cont_appr fi gi -> x1 ⊑ x2 -> app (val fi) x1 ⊑ app (val gi) x2.
Proof.
rewrite /app => /cont_apprP figi x1x2.
apply: (@appr_trans _ (obind (val fi) (retract (domm (val fi)) x2))).
  move: (retract_mono (domm (val fi)) x1x2).
  case e1: (retract (domm (val fi)) x1)=> [x1'|] //=.
  case e2: (retract (domm (val fi)) x2)=> [x2'|] //=.
  rewrite oapprE=> x1'x2'.
  case/andP: (valP fi) => /eqP closed /monotonebP mono.
  rewrite -closed in mono.
  exact: mono (retract_lub_closure e1) (retract_lub_closure e2) x1'x2'.
exact/figi.
Qed.

Notation pcont_lub fi gi :=
  (mkfmapfp (fun x => odflt None (app (val fi) x ⊔ app (val gi) x))
            (lub_closure (domm (val fi) :|: domm (val gi)))).

Definition cont_lub fi gi : option {f | saturated f} :=
  if insub (pcont_lub fi gi) is Some hi then
    if cont_appr fi hi && cont_appr gi hi then Some hi
    else None
  else None.

Lemma cont_lubP : QDom.axioms cont_appr cont_lub.
Proof.
split=> /=.
- move=> fq; exact: cont_apprxx.
- move=> gq fq hq; exact: cont_appr_trans.
move=> fi gi hi; rewrite /cont_lub /=.
set clos := lub_closure (domm (val fi) :|: domm (val gi)).
set fg   := mkfmapfp _ clos.
have e :
  forall hi, fsubset (domm (val hi)) (domm (val fi) :|: domm (val gi)) ->
  forall x, app (val hi) x = obind (app (val hi)) (retract clos x).
  move=> hi' sub.
  move: (fsubset_trans sub (lub_closure_ext _)) => {sub} sub x.
  by rewrite /app -(retractS _ sub); case: (retract clos x).
have ret_clos : forall x x', retract clos x = Some x' -> x' \in clos.
  move=> x x' ex; move: (retract_lub_closure ex).
  by rewrite lub_closure_idem => ->.
move: {e} (e _ (fsubsetUl _ _)) (e _ (fsubsetUr _ _))=> fE gE.
have [/allP coh|/allPn [x x_in incoh]] :=
  boolP (all (fun x => app (val fi) x ⊔ app (val gi) x) clos).
  have {coh} coh : forall x, app (val fi) x ⊔ app (val gi) x.
    move=> x; rewrite fE gE; case ex: (retract clos x) => [x'|] //=.
    apply: coh; rewrite /clos -lub_closure_idem.
    by apply: retract_lub_closure ex.
  have domm_fg : domm fg = clos.
    apply/eq_fset=> x'; rewrite domm_mkfmapfp in_fset mem_filter andbC.
    have [in_clos|] //= := boolP (x' \in lub_closure _).
    move: (coh x').
    case fi_x': (app (val fi) x')=> [y1|] //=;
    case gi_x': (app (val gi) x')=> [y2|] //=.
      by rewrite /lub /=; case: lub.
    move: fi_x'; rewrite /app.
    case e_fi_x': (retract (domm (val fi)) x')=> [x''|] //=.
      move=> fi_x''; move: (retract_lub_closure e_fi_x').
      case/andP: (valP fi)=> /eqP -> _.
      by rewrite mem_domm fi_x''.
    move=> _ _; move: gi_x'; rewrite /app.
    case e_gi_x': (retract (domm (val gi)) x')=> [x''|] //=.
      move=> gi_x''; move: (retract_lub_closure e_gi_x').
      case/andP: (valP gi)=> /eqP ->.
      by rewrite mem_domm gi_x''.
    by move/retractK: in_clos; rewrite retractU e_fi_x' e_gi_x'.
  have fgE : forall x, obind fg (retract clos x)
                       = odflt None (app (val fi) x ⊔ app (val gi) x).
    move=> x; rewrite fE gE; case ex: (retract clos x)=> [x'|] //=.
    by rewrite mkfmapfpE (ret_clos _ _ ex).
  have Pfg : (lub_closure (domm fg) == domm fg) && monotoneb fg.
    rewrite domm_fg /clos lub_closure_idem eqxx /=.
    apply/monotonebP=> x1 x2 in1 in2 x1x2; move: (fgE x1) (fgE x2) (in2).
    rewrite {1 2}domm_fg in in1 in2.
    rewrite mem_domm ?retractK ?lub_closure_idem //= => -> ->.
    move: (coh x1) (coh x2).
    case el1: (app (val fi) x1 ⊔ app (val gi) x1)=> [[l1|]|] //= _.
    case el2: (app (val fi) x2 ⊔ app (val gi) x2)=> [[l2|]|] //= _.
    move: (is_lub_lub (app (val fi) x1) (app (val gi) x1) (Some l2)).
    rewrite el1 => <- => _; apply/andP; split.
      exact: (appr_trans (app_mono (cont_apprxx fi) x1x2) (lub_apprL el2)).
    exact: (appr_trans (app_mono (cont_apprxx gi) x1x2) (lub_apprR el2)).
  rewrite insubT.
  set fgi : {f | saturated f} := Sub fg Pfg.
  have {fgE} fgE : forall x, app (val fgi) x =
                             odflt None (app (val fi) x ⊔ app (val gi) x).
    by move=> x; rewrite {1}/app /= domm_fg.
  move: fgi fgE => /= {fg Pfg domm_fg} fgi fgiE.
  have -> /= : cont_appr fi fgi && cont_appr gi fgi.
    apply/andP; split.
      apply/cont_apprP=> x; rewrite fgiE fE gE.
      case ex: (retract clos x)=> [x'|] //=.
      move: (coh x').
      case ey: lub=> [y|] //= _.
      exact: (lub_apprL ey).
    apply/cont_apprP=> x; rewrite fgiE fE gE.
    case ex: (retract clos x)=> [x'|] //=.
    move: (coh x').
    case ey: lub=> [y|] //= _.
    exact: (lub_apprR ey).
  apply/(sameP andP)/(iffP (cont_apprP _ _)).
    move=> fgi_hi; split; apply/allP=> x in_clos.
      move: (is_lub_lub (app (val fi) x) (app (val gi) x) (app (val hi) x)).
      move: (fgi_hi x) (coh x); rewrite fgiE.
      by case: lub=> /= [y|] // -> _ /andP [].
    move: (is_lub_lub (app (val fi) x) (app (val gi) x) (app (val hi) x)).
    move: (fgi_hi x) (coh x); rewrite fgiE.
    by case: lub=> /= [y|] // -> _ /andP [].
  case=> /cont_apprP fi_hi /cont_apprP gi_hi x; rewrite fgiE; move: (coh x).
  move: (is_lub_lub (app (val fi) x) (app (val gi) x) (app (val hi) x)).
  by rewrite fi_hi gi_hi /=; case: lub.
have {incoh} incoh : forall hi', ~~ (cont_appr fi hi' && cont_appr gi hi').
  move=> hi'; apply: contra incoh => /andP [/cont_apprP fiP /cont_apprP giP].
  move: (is_lub_lub (app (val fi) x) (app (val gi) x) (app (val hi') x)).
  by rewrite fiP giP; case: lub.
rewrite (negbTE (incoh hi)); case: insubP=> /= [fgi inc|] //.
by rewrite (negbTE (incoh fgi)).
Qed.

Canonical cont_predom := Eval hnf in QDom.PreDom cont_lubP.

(* FIXME: Using a regular definition here makes it harder for Coq to figure out
   that the coercion into functions below is valid. *)

Record type (p : phant (T -> S)) := Cont {
  quot_of_cont : {qdom cont_appr}
}.

End Def.

Module Exports.

Notation "{ 'cont' T }" := (Cont.type (Phant T))
  (at level 0, format "{ 'cont'  T }") : type_scope.

Section WithVar.

Variables T S : domType.

Canonical cont_newType :=
  Eval hnf in [newType for @Cont.quot_of_cont _ _ (Phant (T -> S))].
Definition cont_eqMixin :=
  [eqMixin of {cont T -> S} by <:].
Canonical cont_eqType :=
  Eval hnf in EqType {cont T -> S} cont_eqMixin.
Definition cont_choiceMixin :=
  [choiceMixin of {cont T -> S} by <:].
Canonical cont_choiceType :=
  Eval hnf in ChoiceType {cont T -> S} cont_choiceMixin.
Definition cont_ordMixin :=
  [ordMixin of {cont T -> S} by <:].
Canonical cont_ordType :=
  Eval hnf in OrdType {cont T -> S} cont_ordMixin.
Canonical cont_subDomType :=
  Eval hnf in SubDomType {cont T -> S} (fun _ _ _ _ _ _ => erefl).
Definition cont_domMixin :=
  [domMixin of {cont T -> S} by <:].
Canonical cont_domType :=
  Eval hnf in DomType {cont T -> S} cont_domMixin.

End WithVar.

End Exports.

End Cont.

Export Cont.Exports.

Definition cont_app T S p (f : @Cont.type T S p) x : option S :=
  Cont.app (val (repr (Cont.quot_of_cont f))) x.

Coercion cont_app : Cont.type >-> Funclass.

Section ContDom.

Local Open Scope quotient_scope.

Variables T S : domType.
Implicit Types f g fg : {cont T -> S}.
Implicit Types (x y : T).

Definition fmap_of_cont f : {fmap T -> S} :=
  val (repr (Cont.quot_of_cont f)).

Definition Cont (h : {fmap T -> S}) : {cont T -> S} :=
  if insub h is Some hi then Cont.Cont _ (\pi hi)
  else Cont.Cont (Phant (T -> S)) (\pi (Sub emptym (Cont.saturated0 _ _))).

Lemma cont_appE f x :
  f x = obind (fmap_of_cont f) (retract (domm (fmap_of_cont f)) x).
Proof. by []. Qed.

Lemma cont_appEin f x :
  x \in domm (fmap_of_cont f) -> f x = fmap_of_cont f x.
Proof.
move=> xin; rewrite cont_appE retractK //.
move: x xin; exact/fsubsetP/lub_closure_ext.
Qed.

Lemma fmap_of_contK : cancel fmap_of_cont Cont.
Proof.
case=> f; rewrite /fmap_of_cont /Cont -[f in RHS]reprK /=.
by case: (repr f)=> {f} f fP; rewrite insubT.
Qed.

Lemma fmap_of_contP f : Cont.saturated (fmap_of_cont f).
Proof. exact: valP. Qed.

Lemma cont_apprP f g : reflect (forall x, f x ⊑ g x) (f ⊑ g).
Proof. exact/Cont.cont_apprP. Qed.

Lemma cont_app_mono f g x y : f ⊑ g -> x ⊑ y -> f x ⊑ g y.
Proof. exact/Cont.app_mono. Qed.

Lemma eq_cont f g : f =1 g <-> f = g.
Proof.
split; last by move=> ->.
by move=> fg; apply/anti_appr/andP; split; apply/cont_apprP=> x;
rewrite fg apprxx.
Qed.

Lemma ContE h x :
  Cont.saturated h ->
  Cont h x = obind h (retract (domm h) x).
Proof.
rewrite /Cont=> h_sat; rewrite insubT /= /cont_app /=.
case: piP=> h' /eqmodP /andP [/Cont.cont_apprP e1 /Cont.cont_apprP e2].
by apply/anti_appr; rewrite e1 e2.
Qed.

Definition cont0 := Cont emptym.

Lemma cont0E x : cont0 x = None.
Proof.
by rewrite /cont0 ContE ?Cont.saturated0 // domm0 retract0.
Qed.

Definition cont1 x z := Cont (setm emptym x z).

Lemma cont1E x z y : cont1 x z y = if x ⊑ y then Some z else None.
Proof.
rewrite /cont1 ContE ?Cont.saturated1 //.
rewrite domm_set domm0 fsetU0 retract1.
by case: ifP=> _ //=; rewrite setmE eqxx.
Qed.

End ContDom.

Arguments cont_apprP {_ _} [_ _].

Section ContMapping.

Variables T1 T2 S1 S2 : domType.
Implicit Types (f : T1 -> T2) (g : S1 -> S2) (h : {cont T1 -> S1}).
Implicit Types (x : T1).

Definition mapc f g h : {cont T2 -> S2} :=
  Cont (mapm2 f g (fmap_of_cont h)).

Lemma mapm2_saturated f g (h : {fmap T1 -> S1}) :
  injective f -> lub_preserving f -> monotone g ->
  Cont.saturated h -> Cont.saturated (mapm2 f g h).
Proof.
move=> f_inj f_lub g_mono /andP [h_lub h_mono].
rewrite /Cont.saturated domm_map2 mapm2_mono2 //; last exact: inj_iso.
by rewrite lub_closure_imfset // (eqP h_lub) eqxx.
Qed.

Lemma mapcE f g h x :
  injective f -> lub_preserving f -> monotone g ->
  mapc f g h (f x) = omap g (h x).
Proof.
move=> f_inj f_lub g_mono; rewrite /mapc.
rewrite -[h in RHS]fmap_of_contK [in RHS]ContE; last exact: fmap_of_contP.
move: (fmap_of_cont h) (fmap_of_contP h)=> {h} h hP.
rewrite ContE; last exact: mapm2_saturated.
rewrite domm_map2 retract_imfset //.
case: (retract (domm h) x)=> {x} [x|] //=; by rewrite mapm2E.
Qed.

Lemma mapc_mono f g :
  injective f -> lub_preserving f -> monotone g ->
  monotone (mapc f g).
Proof.
move=> f_inj f_lub g_mono h1 h2 h1h2; apply/cont_apprP=> x2.
rewrite {1}/mapc ContE; try exact: mapm2_saturated (fmap_of_contP _).
rewrite domm_map2; case ex2': (retract _ _)=> [x2'|//] /=.
move: (retract_lub_closure ex2'); rewrite lub_closure_imfset //.
case/andP: (fmap_of_contP h1)=> /eqP -> _ x2'in.
case/imfsetP: x2'in ex2'=> {x2'} x1 x1in -> ex2'.
move/cont_apprP/(_ x1): h1h2; rewrite mapm2E -?cont_appEin //.
case: (h1 x1)=> [y1|//] /=.
rewrite cont_appE; case ex1': (retract _ _)=> [x1'|//] /=.
have efx1': retract (f @: domm (fmap_of_cont h2)) (f x1) = Some (f x1').
  by rewrite retract_imfset // ex1'.
have fx1_x2: f x1 ⊑ x2.
  by move: (retract_appr (f @: domm (fmap_of_cont h1)) x2); rewrite ex2'.
move: (retract_mono (f @: (domm (fmap_of_cont h2))) fx1_x2); rewrite efx1'.
case: (retract _ _) (retract_appr (f @: domm (fmap_of_cont h2)) x2)=> // x2'.
move=> x2'_x2 fx1'_x2' y1_x1'.
have: mapc f g h2 (f x1') ⊑ mapc f g h2 x2.
  rewrite cont_app_mono ?apprxx //.
  exact: appr_trans fx1'_x2' x2'_x2.
apply: appr_trans; rewrite mapcE // cont_appE retractK /=; last first.
  apply: retract_lub_closure ex1'.
case: (fmap_of_cont h2 x1') y1_x1'=> [y2|//] /=; exact: g_mono.
Qed.

End ContMapping.

Section MemoryDef.

Variable T : Type.

CoInductive memory := Memory of {fmap name -> T}.

Definition fmap_of_memory (m : memory) := let: Memory m := m in m.

Canonical memory_newType := [newType for fmap_of_memory].

End MemoryDef.

Definition load (T : Type) (m : memory T) (n : name) := val m n.
Coercion load : memory >-> Funclass.

Definition memory_eqMixin (T : eqType) :=
  [eqMixin of memory T by <:].
Canonical memory_eqType (T : eqType) :=
  Eval hnf in EqType (memory T) (memory_eqMixin T).
Definition memory_choiceMixin (T : choiceType) :=
  [choiceMixin of memory T by <:].
Canonical memory_choiceType (T : choiceType) :=
  Eval hnf in ChoiceType (memory T) (memory_choiceMixin T).
Definition memory_ordMixin (T : ordType) :=
  [ordMixin of memory T by <:].
Canonical memory_ordType (T : ordType) :=
  Eval hnf in OrdType (memory T) (memory_ordMixin T).

Section MemoryDom.

Variable T : domType.

Implicit Types m : memory T.

Definition memory_appr m1 m2 :=
  [&& domm (val m1) == domm (val m2) & val m1 ⊑ val m2].

Definition memory_lub m1 m2 :=
  if domm (val m1) == domm (val m2) then
    omap (@Memory _) (val m1 ⊔ val m2)
  else None.

Lemma memory_lubP : Dom.axioms memory_appr memory_lub.
Proof.
rewrite /memory_appr /memory_lub; split.
- by move=> m; rewrite eqxx apprxx.
- move=> m2 m1 m3 /andP [/eqP -> H12] /andP [->] /=.
  exact: appr_trans H12.
- move=> m1 m2 /andP [/andP [_ H12] /andP [_ H21]].
  by apply/val_inj/anti_appr/andP; split.
move=> m1 m2 m3; case: ifP=> [/eqP e12|ne12]; last first.
  by case: eqP => [<-|//]; rewrite eq_sym ne12 /= andbF.
rewrite -e12; move: (is_lub_lub (val m1) (val m2) (val m3)).
case: (altP (_ =P _)) => [e13 ->|ne13].
  case lub12: (val m1 ⊔ val m2)=> [m12|] //=.
  by rewrite (domm_lub lub12) -e12 fsetUid e13 eqxx.
case lub12: (val m1 ⊔ val m2)=> [m12|] //=.
by rewrite (domm_lub lub12) -e12 fsetUid (negbTE ne13).
Qed.

Definition memory_domMixin := DomMixin memory_lubP.
Canonical memory_domType := Eval hnf in DomType (memory T) memory_domMixin.

End MemoryDom.

(* FIXME: These probably belong somewhere else *)

Section Untag.

Variables (I : eqType) (T_ : I -> Type).

Definition untag i (u : {i : I & T_ i}) : option (T_ i) :=
  match i =P tag u with
  | ReflectT eq_it => Some (eq_rect_r T_ (tagged u) eq_it)
  | ReflectF _     => None
  end.

Lemma TaggedK i : pcancel (Tagged T_) (@untag i).
by move=> x; rewrite /untag; case: eqP => // eq_nt; rewrite eq_axiomK.
Qed.

End Untag.

Section Tagged.

Variables (I : ordType) (T_ : I -> domType).
Implicit Types u v : {i : I & T_ i}.

Definition tag_appr u v :=
  (tag u == tag v) && (tagged u ⊑ tagged_as u v).

Definition tag_lub u v :=
  if tag u == tag v then omap (Tagged T_) (tagged u ⊔ tagged_as u v)
  else None.

Lemma tag_apprP : Dom.axioms tag_appr tag_lub.
Proof.
rewrite /tag_appr /tag_lub; split.
- by move=> [i x] /=; rewrite eqxx tagged_asE apprxx.
- move=> [i2 x2] [i1 x1] [i3 x3] /=.
  case: eqP x2 => //= <- {i2} x2; rewrite tagged_asE.
  case: eqP x3 => //= <- {i3} x3; rewrite !tagged_asE.
  exact: appr_trans.
- move=> [i1 x1] [i2] /=; case: eqP => //= <- {i2} x2.
  by rewrite !tagged_asE eqxx /= => /anti_appr ->.
move=> [i1 x1] [i2 x2] [i3] /=.
case: (altP (i1 =P i2)) x2=> [<- {i2}|i1i2] x2.
  rewrite tagged_asE; case: (altP (i1 =P i3))=> [<- {i3}|i1i3] //= x3.
    rewrite !tagged_asE is_lub_lub; case: (x1 ⊔ x2)=> //= x12.
    by rewrite eqxx tagged_asE.
  case: (x1 ⊔ x2)=> //= x12; by rewrite (negbTE i1i3).
by case: (i1 =P i3)=> //= <- x3; rewrite eq_sym (negbTE i1i2) /= andbF.
Qed.

Definition tag_domMixin := DomMixin tag_apprP.
Canonical tag_domType :=
  Eval hnf in DomType {i : I & T_ i} tag_domMixin.

Lemma tag_apprE u v :
  (u ⊑ v) = (tag u == tag v) && (tagged u ⊑ tagged_as u v).
Proof. by []. Qed.

Lemma tag_lubE u v :
  u ⊔ v =
  if tag u == tag v then omap (Tagged T_) (tagged u ⊔ tagged_as u v)
  else None.
Proof. by []. Qed.

End Tagged.

Section DIter.

Implicit Types (T : nat -> Type) (n m : nat).

Fixpoint diter T_ n (f : forall m, T_ m -> T_ m.+1) (x : T_ 0) : T_ n :=
  if n is n.+1 then f n (diter n f x) else x.

Lemma diter_add T_ n m (f : forall m, T_ m -> T_ m.+1) (x : T_ 0) :
  diter (n + m) f x = diter n (fun k => f (k + m)) (diter m f x).
Proof. by elim: n => [//|n /= ->]. Qed.

Lemma leq_ind n (T : forall m, n <= m -> Prop) :
  T n (leqnn n) ->
  (forall m (nm : n <= m), T m nm -> T m.+1 (leq_trans nm (leqnSn m))) ->
  (forall m (nm : n <= m), T m nm).
Proof.
move=> P0 PS; elim=> [|m IH] nm.
  move: nm (nm) T P0 {PS}; rewrite {1}leqn0 => /eqP -> nm T.
  by rewrite (eq_irrelevance (leqnn 0) nm).
move: nm (nm) T P0 PS IH; rewrite {1}leq_eqVlt.
case/orP=> [/eqP -> {n}|].
  rewrite -[m < m.+1]/(m <= m) => nm T P0 _ _.
  by rewrite -(eq_irrelevance (leqnn m.+1) nm).
move=> nm nm1 T _ PS IH; move: (PS _ nm (IH nm)).
by rewrite (eq_irrelevance (leq_trans _ _) nm1).
Qed.

Definition nat_trans T_ n m (e : n <= m)
  (f : forall k, T_ k -> T_ k.+1) (x : T_ n) : T_ m :=
  eq_rect (m - n + n) T_
          (@diter (fun k => T_ (k + n)) (m - n)
                  (fun k => f  (k + n)) x)
          m (subnK e).

Lemma nat_trans_nn T_ n (e : n <= n)
      (f : forall k, T_ k -> T_ k.+1) (x : T_ n) : nat_trans e f x = x.
Proof.
rewrite /nat_trans; move: (subnK e); rewrite subnn=> p.
by rewrite eq_axiomK /=.
Qed.

Lemma nat_transS T_ n m (e : n <= m)
      (f : forall k, T_ k -> T_ k.+1) (x : T_ n) :
  nat_trans (leq_trans e (leqnSn m)) f x = f m (nat_trans e f x).
Proof.
rewrite /nat_trans; move: (subnK _); rewrite (subSn e) => p /=.
move: (m - n) p (subnK e) => k p p'.
have -> : p = congr1 S p' by exact/eq_irrelevance.
move: (diter _ _ _) => x'; by case: m / p' {e p}.
Qed.

Lemma nat_trans_trans T_ n m p (nm : n <= m) (mp : m <= p) (np : n <= p)
  (f : forall k, T_ k -> T_ k.+1) (x : T_ n) :
  nat_trans np f x = nat_trans mp f (nat_trans nm f x).
Proof.
elim/leq_ind: p / mp np => [|p mp IH] np.
  by rewrite nat_trans_nn (eq_irrelevance nm np).
rewrite (eq_irrelevance np (leq_trans (leq_trans nm mp) (leqnSn _))).
by rewrite !nat_transS IH.
Qed.

End DIter.

Section InverseLimit.

Implicit Types T S U : domType.

CoInductive emb_class_of T S (e : T -> S) (r : S -> option T) : Prop :=
  EmbClass of pcancel e r & forall x y, e x ⊑ y = Some x ⊑ r y.

Record embedding T S := Embedding {
  emb_app :> T -> S;
  emb_ret :  S -> option T;
  _       :  emb_class_of emb_app emb_ret
}.
Definition embedding_of T S of phant (T -> S) := embedding T S.
Identity Coercion embedding_of_embedding : embedding_of >-> embedding.

Notation "{ 'emb' T }" := (embedding_of (Phant T))
  (at level 0, format "{ 'emb'  T }") : type_scope.

Notation "e '^r'" := (emb_ret e)
  (at level 3, no associativity, format "e ^r") : dom_scope.

Lemma emb_appK T S (e : {emb T -> S}) : pcancel e e^r.
Proof. by case: e => ?? []. Qed.

Lemma emb_inj T S (e : {emb T -> S}) : injective e.
Proof. exact/pcan_inj/emb_appK. Qed.

Lemma emb_retP T S (e : {emb T -> S}) : forall x y, e x ⊑ y = Some x ⊑ e^r y.
Proof. by case: e => ?? []. Qed.

Lemma emb_appr T S (e : {emb T -> S}) x y : x ⊑ y = e x ⊑ e y.
Proof. by rewrite emb_retP emb_appK. Qed.

Lemma emb_apprR T S (e : {emb T -> S}) x y : x ⊑ y -> e^r x ⊑ e^r y.
Proof.
move=> xy; case ex: (e^r x)=> [x'|] //=.
have x'x: e x' ⊑ x by rewrite emb_retP -ex apprxx.
by rewrite -emb_retP; apply: appr_trans xy.
Qed.

Lemma emb_lub T S (e : {emb T -> S}) x y : e x ⊔ e y = omap e (x ⊔ y).
Proof.
by apply/esym/lub_unique=> z; case: (lubP x y)=> [xy Pxy|] /=;
rewrite !emb_retP; case: (e^r z)=> [z'|] //=; rewrite !oapprE.
Qed.

Lemma eq_emb T S (e1 e2 : {emb T -> S}) : e1 =1 e2 <-> e1^r =1 e2^r.
Proof.
split=> e x.
  apply/anti_appr; case ey1: (e1^r x)=> [y1|] //=.
    rewrite -emb_retP -e emb_retP ey1 apprxx /=.
    case ey2: (e2^r x)=> [y2|] //=.
    by rewrite -ey1 -emb_retP e emb_retP ey2 apprxx /=.
  case ey2: (e2^r x)=> [y2|] //=.
  by rewrite -ey1 -emb_retP e emb_retP ey2 apprxx.
apply/anti_appr; rewrite emb_retP e emb_appK apprxx.
by rewrite emb_retP -e emb_appK apprxx.
Qed.

Lemma id_embP T : emb_class_of (@id T) Some.
Proof. by split. Qed.
Canonical id_emb T := Eval hnf in Embedding (id_embP T).

Lemma comp_embP T S U (e1 : {emb U -> S}) (e2 : {emb S -> T}) :
  emb_class_of (e2 \o e1) (pcomp e1^r e2^r).
Proof.
split; first by apply: pcan_pcomp; apply: emb_appK.
move=> x y /=; rewrite emb_retP /pcomp; case: (e2^r y)=> [z|] //=.
by rewrite oapprE emb_retP.
Qed.
Canonical comp_emb T S U (e1 : {emb U -> S}) (e2 : {emb S -> T}) :=
  Embedding (comp_embP e1 e2).

Lemma retr_embP T (sT : {proj T}) :
  emb_class_of (@proj_elt T sT) (pcomp insub (retract sT)).
Proof.
split.
- move=> /= x; rewrite /pcomp retractK /= ?valK //.
  move/eqP: (valP sT) => /= ->; exact: valP.
move=> /= x y; rewrite /pcomp; case: retractP => [z|]; move/eqP: (valP sT) => -> /=.
  move=> z_in -> /=; last exact: (valP x).
  by rewrite insubT.
move=> -> //; exact: (valP x).
Qed.
Canonical retr_emb T (sT : {proj T}) := Embedding (retr_embP sT).

Lemma of_void_embP T : emb_class_of (of_void T) (@to_void T).
Proof. by split; case. Qed.
Canonical of_void_emb T := Embedding (of_void_embP T).

(* FIXME: Move *)
Lemma Tagged_embP (I : ordType) (T_ : I -> domType) i :
  emb_class_of (Tagged T_) (@untag _ _ i).
Proof.
split; first exact/TaggedK.
move=> /= x [j y]; rewrite tag_apprE /=.
rewrite /untag /=; move: y; case: (i =P j)=> //.
move=> p; move: (p); rewrite -{}p => p y.
by rewrite eq_axiomK /= tagged_asE.
Qed.
Canonical Tagged_emb I TT i := Embedding (@Tagged_embP I TT i).

Record functor := Functor {
  f_obj  :> domType -> domType;
  f_mor  :  forall T S : domType, {emb T -> S} -> {emb f_obj T -> f_obj S};
  f_ext  :  forall (T S : domType) (e1 e2 : {emb T -> S}),
              e1 =1 e2 -> f_mor e1 =1 f_mor e2;
  f_id   :  forall T, f_mor (id_emb T) =1 id;
  f_comp :  forall (T S U : domType) (e1 : {emb S -> U}) (e2 : {emb T -> S}),
              f_mor (comp_emb e2 e1) =1 comp_emb (f_mor e2) (f_mor e1);
  f_cont :  forall (T : domType) (x : f_obj T),
            exists (sT : {proj T}) (x' : f_obj [domType of sT]),
              x = f_mor (retr_emb sT) x'
}.

Variable F : functor.

Fixpoint chain n : domType :=
  if n is n.+1 then F (chain n) else [domType of void].

Fixpoint chain_mor1 n : {emb chain n -> chain n.+1} :=
  if n is n.+1 then f_mor F (chain_mor1 n) else of_void_emb (chain 1).

Definition chain_mor n m (nm : n <= m) : {emb chain n -> chain m} :=
  @nat_trans (fun k => {emb chain n -> chain k}) _ _ nm
             (fun k e => comp_emb e (chain_mor1 k)) (id_emb _).

Lemma chain_mor_nn n (nn : n <= n) : chain_mor nn = id_emb _.
Proof. by rewrite /chain_mor nat_trans_nn. Qed.

Lemma chain_mor_trans n m p (nm : n <= m) (mp : m <= p) :
  chain_mor (leq_trans nm mp) =1 chain_mor mp \o chain_mor nm.
Proof.
move=> x /=; rewrite /chain_mor.
elim/leq_ind: p / mp=> [|p mp IH].
  by rewrite !nat_trans_nn (eq_irrelevance (leq_trans _ _) nm).
rewrite (eq_irrelevance (leq_trans _ _)
                        (leq_trans (leq_trans nm mp) (leqnSn p))).
by rewrite !nat_transS /= IH.
Qed.

Lemma chain_morS n m (nm : n <= m) (SnSm : n < m.+1) :
  chain_mor SnSm =1 f_mor F (chain_mor nm).
Proof.
move=> x; elim/leq_ind: m / nm SnSm => [|m nm IH] SnSm.
  by rewrite !chain_mor_nn f_id.
rewrite {2}/chain_mor nat_transS /= f_comp /=.
rewrite (eq_irrelevance SnSm (@leq_trans m.+1 n.+1 m.+2 nm (leqnSn m.+1))).
by rewrite /chain_mor nat_transS /= IH.
Qed.

Implicit Types x y : {n : nat & chain n}.

Definition invlim_appr x y : bool :=
  chain_mor (leq_maxl (tag x) (tag y)) (tagged x)
  ⊑ chain_mor (leq_maxr (tag x) (tag y)) (tagged y).

Lemma invlim_apprE x y c (xc : tag x <= c) (yc : tag y <= c) :
  invlim_appr x y = (chain_mor xc (tagged x) ⊑ chain_mor yc (tagged y)).
Proof.
have xyc : maxn (tag x) (tag y) <= c by rewrite geq_max xc.
rewrite (eq_irrelevance xc (leq_trans (leq_maxl _ _) xyc)).
rewrite (eq_irrelevance yc (leq_trans (leq_maxr _ _) xyc)).
by rewrite !chain_mor_trans /= -emb_appr.
Qed.

Lemma anti_invlim_appr x y c (xc : tag x <= c) (yc : tag y <= c) :
  invlim_appr x y && invlim_appr y x ->
  chain_mor xc (tagged x) = chain_mor yc (tagged y).
Proof.
rewrite (invlim_apprE xc yc) (invlim_apprE yc xc); exact/anti_appr.
Qed.

Definition invlim_lub x y :=
  omap (Tagged chain)
       (chain_mor (leq_maxl (tag x) (tag y)) (tagged x)
        ⊔ chain_mor (leq_maxr (tag x) (tag y)) (tagged y)).

Lemma invlim_lubP : QDom.axioms invlim_appr invlim_lub.
Proof.
split.
- move=> x; rewrite /invlim_appr.
  by rewrite (eq_irrelevance (leq_maxl _ _) (leq_maxr _ _)) apprxx.
- move=> y x z.
  pose c := maxn (tag x) (maxn (tag y) (tag z)).
  have xc : tag x <= c by rewrite leq_maxl.
  have yc : tag y <= c by rewrite /c (maxnC (tag y)) maxnA leq_maxr.
  have zc : tag z <= c by rewrite /c maxnA leq_maxr.
  rewrite (invlim_apprE xc yc) (invlim_apprE yc zc) (invlim_apprE xc zc).
  exact: appr_trans.
move=> x y z.
pose c := maxn (tag x) (maxn (tag y) (tag z)).
have xc : tag x <= c by rewrite leq_maxl.
have yc : tag y <= c by rewrite /c (maxnC (tag y)) maxnA leq_maxr.
have zc : tag z <= c by rewrite /c maxnA leq_maxr.
have xyc : maxn (tag x) (tag y) <= c by rewrite geq_max xc.
rewrite (invlim_apprE xc zc) (invlim_apprE yc zc) /invlim_lub is_lub_lub.
rewrite (eq_irrelevance xc (leq_trans (leq_maxl _ _) xyc)).
rewrite (eq_irrelevance yc (leq_trans (leq_maxr _ _) xyc)).
rewrite !chain_mor_trans /= emb_lub.
case: (_ ⊔ _)=> [xy|] //=.
by rewrite (@invlim_apprE (Tagged chain xy) _ _ xyc zc).
Qed.
Canonical invlim_predom := QDom.PreDom invlim_lubP.

Definition mu := {qdom invlim_appr}.
Definition mu_of of phantom (domType -> domType) F := mu.

Notation P := (Phantom _ (f_obj F)).
Canonical mu_eqType := Eval hnf in [eqType of mu].
Canonical mu_choiceType := Eval hnf in [choiceType of mu].
Canonical mu_quotType := Eval hnf in [quotType of mu].
Canonical mu_ordType := Eval hnf in [ordType of mu].
Canonical mu_domType := Eval hnf in [domType of mu].
Canonical mu_of_eqType := Eval hnf in [eqType of mu_of P].
Canonical mu_of_choiceType := Eval hnf in [choiceType of mu_of P].
Canonical mu_of_quotType := Eval hnf in [quotType of mu_of P].
Canonical mu_of_ordType := Eval hnf in [ordType of mu_of P].
Canonical mu_of_domType := Eval hnf in [domType of mu_of P].

Notation "{ 'mu' F }" :=
  (mu_of (Phantom (domType -> domType) (f_obj F)))
  (at level 0, format "{ 'mu'  F }") : type_scope.

Local Open Scope quotient_scope.

Definition in_mu n (x : chain n) : {mu F} :=
  \pi (Tagged chain x).

Definition out_mu n (x : {mu F}) : option (chain n) :=
  (chain_mor (leq_maxl n (tag (repr x))))^r
    (chain_mor (leq_maxr n (tag (repr x))) (tagged (repr x))).

Lemma in_mu_embP n : emb_class_of (@in_mu n) (@out_mu n).
Proof.
rewrite /in_mu /out_mu; split.
  move=> x /=; case: piP => y.
  move: (leq_maxl _ _) (leq_maxr _ _)=> xc yc.
  move=> /eqmodP/(@anti_invlim_appr (Tagged chain x) _ _ xc yc) /= <-.
  by rewrite emb_appK.
move=> /= x; elim/quotP=> /= y ->; rewrite pi_appr /=.
move: (leq_maxl _ _) (leq_maxr _ _)=> xc yc.
by rewrite (@invlim_apprE (Tagged chain x) _ _ xc yc) emb_retP.
Qed.
Canonical in_mu_emb n := Embedding (in_mu_embP n).

Lemma in_mu_chain_mor n m (e : n <= m) (x : chain n) :
  in_mu (chain_mor e x) = in_mu x.
Proof.
rewrite /in_mu; apply/eqmodP=> /=; rewrite /QDom.qdom_eq /=.
by rewrite !(@invlim_apprE _ _ m) !chain_mor_nn !apprxx.
Qed.

Lemma out_mu_chain_mor n m (e : n <= m) (x : {mu F}) :
  obind (chain_mor e)^r (out_mu m x) = out_mu n x.
Proof.
suff : comp_emb (chain_mor e) (@in_mu_emb m) =1 @in_mu_emb n.
  by move=> /eq_emb /= <-.
exact/in_mu_chain_mor.
Qed.

Lemma mu_inv (xs : {fset {mu F}}) :
  exists n (xs' : {fset chain n}), xs = @in_mu n @: xs'.
Proof.
pose n  := foldr maxn 0 [seq tag (repr x) | x <- xs].
pose ys := fset (pmap (@out_mu n) xs).
have Pn : forall x : {mu F}, x \in xs -> tag (repr x) <= n.
  move=> x; rewrite /n inE /=; elim: (FSet.fsval xs)=> //= x'' xs' IH.
  rewrite inE; case/orP=> [/eqP <- {x''}|]; first exact/leq_maxl.
  by move=> x'_in; rewrite leq_max IH // orbT.
exists n, ys.
apply/eq_fset=> /= x; apply/(sameP idP)/(iffP idP).
  case/imfsetP=> y; rewrite in_fset mem_pmap.
  case/mapP=> /= x' x'_in ex' ex.
  move: (Pn x' x'_in)=> x'_n.
  rewrite (_ : x = x') // ex.
  move: ex'; rewrite /out_mu; move: (leq_maxl _ _) (leq_maxr _ _).
  rewrite (maxn_idPl x'_n) => nn {x'_n} x'_n; rewrite chain_mor_nn /=.
  move=> [->]; rewrite in_mu_chain_mor /in_mu -[RHS]reprK; congr \pi.
  by case: (repr x').
move=> x_in; apply/imfsetP; move: (Pn x x_in) => x_n.
exists (chain_mor x_n (tagged (repr x))).
  rewrite /ys in_fset mem_pmap; apply/mapP=> /=.
  exists x=> //; rewrite /out_mu.
  move: (leq_maxl _ _) (leq_maxr _ _).
  rewrite (maxn_idPl x_n) => nn x_n'.
  by rewrite chain_mor_nn /= (eq_irrelevance x_n x_n').
rewrite in_mu_chain_mor /in_mu -[LHS]reprK; congr \pi.
by case: (repr x).
Qed.

Definition unroll (x : {mu F}) : F [domType of {mu F}] :=
  let x' := repr x in
  match tag x' as n return chain n -> _ with
  | 0    => fun xx => of_void _ xx
  | n.+1 => fun xx => f_mor F (in_mu_emb n) xx
  end (tagged x').

Lemma unrollE n (x : chain n.+1) :
  unroll (\pi (Tagged chain x)) = f_mor F (in_mu_emb n) x.
Proof.
rewrite /unroll /=; case: piP=> [[[|m] y]]; first by case: y.
move: (leq_maxl n m) (leq_maxr n m)=> xc yc.
move: (xc) (yc); rewrite -ltnS -[m <= _]ltnS => SxSc SySc.
move=> /eqmodP.
move=> /(@anti_invlim_appr (Tagged chain x) (Tagged chain y) _ SxSc SySc).
rewrite /= (chain_morS xc SxSc) (chain_morS yc SySc).
have em : in_mu_emb m =1 comp_emb (@chain_mor m (maxn n m) yc) (in_mu_emb _).
  by move=> y' /=; rewrite in_mu_chain_mor.
have en : in_mu_emb n =1 comp_emb (@chain_mor n (maxn n m) xc) (in_mu_emb _).
  by move=> x' /=; rewrite in_mu_chain_mor.
by rewrite (f_ext em) (f_ext en) !f_comp /= => ->.
Qed.

Lemma unroll_appr (x y : {mu F}) : unroll x ⊑ unroll y = x ⊑ y.
Proof.
elim/quotP: x => [[ /= [|n] x] _]; first by case: x.
elim/quotP: y => [[ /= [|m] y] _]; first by case: y.
rewrite !unrollE.
have h : forall a b (e : a <= b),
  in_mu_emb a =1 comp_emb (chain_mor e) (in_mu_emb b).
- by move=> a b e ?; rewrite /= in_mu_chain_mor.
rewrite (f_ext (h _ _ (leq_maxl n m))).
rewrite (f_ext (h _ _ (leq_maxr n m))).
rewrite !f_comp /= -emb_appr pi_appr /=.
move: {-}(leq_maxl n m); rewrite -ltnS => l.
move: {-}(leq_maxr n m); rewrite -ltnS => r.
rewrite !(@invlim_apprE (Tagged chain x) (Tagged chain y) _ l r) /=.
by rewrite (chain_morS (leq_maxl n m) l x) (chain_morS (leq_maxr n m) r y).
Qed.

Lemma unroll_inj : injective unroll.
Proof.
move=> x y xy; apply/anti_appr.
by rewrite -!unroll_appr xy !apprxx.
Qed.

Lemma unroll_sur (x : F [domType of {mu F}]) :
  exists y : {mu F}, unroll y == x.
Proof.
(* FIXME: The type of sT below is huge and slows down everything *)
have [/= sT [{x} x ->]] := f_cont x.
have [/= n [sS e_sT]] := mu_inv sT.
have /lub_closedP/eqP sS_clos : lub_closed (mem sS).
  move=> x1 x2 in_sS1 in_sS2 x12 e_x12.
  have in_sT1 : in_mu x1 \in sT.
    by rewrite inE /= e_sT; apply/imfsetP; eauto.
  have in_sT2 : in_mu x2 \in sT.
    by rewrite inE /= e_sT; apply/imfsetP; eauto.
  have {e_x12} e_x12 : in_mu x1 ⊔ in_mu x2 = Some (in_mu x12).
    by rewrite emb_lub e_x12.
  have /eqP/lub_closedP := valP sT.
  move=> /(_ _ _ in_sT1 in_sT2 _ e_x12).
  rewrite /= e_sT inE mem_imfset_inj //.
  exact/emb_inj.
move: e_sT.
have [{sS sS_clos} sS -> /= e_sT] : exists sS' : {proj chain n}, sS = val sS'.
  by exists (Proj sS_clos).
have in_mu_sur : forall y : sT, exists y' : sS, (val y == in_mu y').
- move=> [/= y]; rewrite inE /= e_sT; case/imfsetP=> y' in_sS ->.
  by exists (Sub y' in_sS).
pose S_of_T (y : sT) : sS := xchoose (in_mu_sur y).
pose T_of_S (x : sS) : option sT := (retr_emb sT)^r (in_mu x).
have S_of_TP : emb_class_of S_of_T T_of_S; first split.
- move=> y; rewrite /S_of_T /T_of_S /=.
  move: (xchooseP (in_mu_sur y)) => /eqP <- /=.
  rewrite /pcomp retractK /= ?valK //.
  move: (valP sT) => /= /eqP ->.
  exact/valP.
- move=> x' y'.
  have in_sT : in_mu y' \in sT.
    rewrite inE /= e_sT mem_imfset_inj; first exact/valP.
    exact/emb_inj.
  rewrite /S_of_T /T_of_S /= /pcomp retractK /=; last first.
    by move: (valP sT)=> /eqP ->.
  rewrite (insubT (mem sT) in_sT) oapprE.
  move: (xchooseP (in_mu_sur x'))=> /eqP /=.
  by rewrite !appr_val /= => e; rewrite {2}e -!emb_appr.
pose S_of_T_emb : {emb sT -> sS} := Embedding S_of_TP.
exists (@in_mu n.+1 (f_mor F (comp_emb S_of_T_emb (retr_emb sS)) x)).
apply/eqP; rewrite /in_mu /= unrollE.
move: (@f_comp F _ _ _ (in_mu_emb n) (comp_emb S_of_T_emb (retr_emb sS)) x).
move=> /= <-; apply/f_ext=> y /=.
by rewrite /S_of_T; move: (xchooseP (in_mu_sur y)) => /eqP <-.
Qed.

Definition roll (x : F [domType of {mu F}]) : {mu F} :=
  xchoose (unroll_sur x).

Lemma rollK : cancel roll unroll.
Proof.
move=> x; apply/eqP; rewrite /roll; exact/(xchooseP (unroll_sur x)).
Qed.

Lemma unrollK : cancel unroll roll.
Proof. exact/(inj_can_sym rollK unroll_inj). Qed.

Lemma roll_appr (x y : F [domType of {mu F}]) : roll x ⊑ roll y = x ⊑ y.
Proof. by rewrite -unroll_appr !rollK. Qed.

End InverseLimit.

Notation "{ 'emb' T }" := (embedding_of (Phant T))
  (at level 0, format "{ 'emb'  T }") : type_scope.

Notation "e '^r'" := (emb_ret e)
  (at level 3, no associativity, format "e ^r") : dom_scope.

Notation "{ 'mu' F }" :=
  (mu_of (Phantom (domType -> domType) (f_obj F)))
  (at level 0, format "{ 'mu'  F }") : type_scope.
