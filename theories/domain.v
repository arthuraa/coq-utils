From mathcomp
Require Import
  ssreflect ssrfun ssrbool ssrnat seq eqtype choice fintype generic_quotient
  tuple finfun.

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

- Make countOrdType and finOrdType interfaces for extructures

*)

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

Lemma void_apprP : Po.axioms_of true (fun x y : void => true).
Proof. by split; case. Qed.
Definition void_poMixin := PoMixin void_apprP.
Canonical void_poType := Eval hnf in PoType void void_poMixin.
Canonical void_discPoType := Eval hnf in [discPoType for void].

Canonical bool_poType := Eval hnf in [poType for bool by //].
Canonical bool_discPoType := Eval hnf in [discPoType for bool].

Lemma unit_apprP : Po.axioms_of true (fun x y : unit => true).
Proof. by split=> // - [] []. Qed.
Definition unit_poMixin := PoMixin unit_apprP.
Canonical unit_poType := Eval hnf in PoType unit unit_poMixin.
Canonical unit_discPoType := Eval hnf in [discPoType for unit].

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

Lemma unit_botP x : tt ⊑ x.
Proof. by case: x. Qed.
Definition unit_ppoMixin := PPoMixin unit_botP.
Canonical unit_ppoType := Eval hnf in PPoType unit unit_ppoMixin.

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

Definition unit_domMixin :=
  @DomMixin _ unit_poType (fun _ _ => Coh tt) (fun _ _ _ => erefl).
Canonical unit_domType := Eval hnf in DomType unit unit_domMixin.

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
Definition base2 anti T c := Dom.Class (@mixin anti T c).

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
Definition domType := @Dom.Pack anti cT (base2 xclass).

End ClassDef.

Module Import Exports.
Coercion base : class_of >-> PPo.class_of.
Coercion base2 : class_of >-> Dom.class_of.
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

Module FinDom.

Section ClassDef.

Record class_of anti T := Class {
  base : Dom.class_of anti T;
  mixin : Finite.mixin_of (Equality.Pack base T)
}.
Local Coercion base : class_of >-> Dom.class_of.

Definition base2 anti T c := Finite.Class (@mixin anti T c).

Structure type anti := Pack {sort; _ : class_of anti sort}.
Local Coercion sort : type >-> Sortclass.
Variables (anti : bool) (T : Type) (cT : type anti).
Definition class := let: Pack _ c as cT' := cT return class_of anti cT' in c.
Definition clone c of phant_id class c := @Pack anti T c.
Let xT := let: Pack T _ := cT in T.
Notation xclass := (class : class_of anti xT).

Definition pack :=
  fun b_dom (domT : domType anti) & phant_id (Dom.class domT) b_dom =>
  fun m (finT : finType) & phant_id (Finite.mixin (Finite.class finT)) m =>
  @Pack anti T (@Class anti T b_dom m).

(* Inheritance *)
Definition eqType := @Equality.Pack cT xclass xT.
Definition choiceType := @Choice.Pack cT xclass xT.
Definition countType := @Countable.Pack cT (base2 xclass) xT.
Definition finType := @Finite.Pack cT (base2 xclass) xT.
Definition ordType := @Ord.Pack cT xclass xT.
Definition poType := @Po.Pack anti cT xclass.
Definition domType := @Dom.Pack anti cT xclass.

End ClassDef.

Module Import Exports.
Coercion base : class_of >-> Dom.class_of.
Coercion mixin : class_of >-> Finite.mixin_of.
Coercion base2 : class_of >-> Finite.class_of.
Coercion sort : type >-> Sortclass.
Coercion eqType : type >-> Equality.type.
Canonical eqType.
Coercion choiceType : type >-> Choice.type.
Canonical choiceType.
Coercion countType : type >-> Countable.type.
Canonical countType.
Coercion finType : type >-> Finite.type.
Canonical finType.
Coercion ordType : type >-> Ord.type.
Canonical ordType.
Coercion poType : type >-> Po.type.
Canonical poType.
Coercion domType : type >-> Dom.type.
Canonical domType.
Notation finDomType := type.
Notation FinDomType T := (@pack _ T _ _ id _ _ id).
Notation "[ 'finDomType' 'of' T 'for' cT ]" :=  (@clone _ T cT _ idfun)
  (at level 0, format "[ 'finDomType'  'of'  T  'for'  cT ]") : form_scope.
Notation "[ 'finDomType' 'of' T ]" := (@clone _ T _ _ id)
  (at level 0, format "[ 'finDomType'  'of'  T ]") : form_scope.
End Exports.

End FinDom.

Export FinDom.Exports.

Module FinPDom.

Section ClassDef.

Record class_of anti T := Class {
  base : PDom.class_of anti T;
  mixin : Finite.mixin_of (Equality.Pack base T)
}.
Local Coercion base : class_of >-> PDom.class_of.

Definition base2 anti T c := Finite.Class (@mixin anti T c).

Structure type anti := Pack {sort; _ : class_of anti sort}.
Local Coercion sort : type >-> Sortclass.
Variables (anti : bool) (T : Type) (cT : type anti).
Definition class := let: Pack _ c as cT' := cT return class_of anti cT' in c.
Definition clone c of phant_id class c := @Pack anti T c.
Let xT := let: Pack T _ := cT in T.
Notation xclass := (class : class_of anti xT).

Definition pack :=
  fun b_dom (domT : pdomType anti) & phant_id (PDom.class domT) b_dom =>
  fun m (finT : finType) & phant_id (Finite.mixin (Finite.class finT)) m =>
  @Pack anti T (@Class anti T b_dom m).

(* Inheritance *)
Definition eqType := @Equality.Pack cT xclass xT.
Definition choiceType := @Choice.Pack cT xclass xT.
Definition countType := @Countable.Pack cT (base2 xclass) xT.
Definition finType := @Finite.Pack cT (base2 xclass) xT.
Definition ordType := @Ord.Pack cT xclass xT.
Definition poType := @Po.Pack anti cT xclass.
Definition ppoType := @PPo.Pack anti cT xclass.
Definition domType := @Dom.Pack anti cT xclass.
Definition pdomType := @PDom.Pack anti cT xclass.
Definition finDomType := @FinDom.Pack anti cT (@FinDom.Class _ _ xclass (base2 xclass)).

End ClassDef.

Module Import Exports.
Coercion base : class_of >-> PDom.class_of.
Coercion mixin : class_of >-> Finite.mixin_of.
Coercion base2 : class_of >-> Finite.class_of.
Coercion sort : type >-> Sortclass.
Coercion eqType : type >-> Equality.type.
Canonical eqType.
Coercion choiceType : type >-> Choice.type.
Canonical choiceType.
Coercion countType : type >-> Countable.type.
Canonical countType.
Coercion finType : type >-> Finite.type.
Canonical finType.
Coercion ordType : type >-> Ord.type.
Canonical ordType.
Coercion poType : type >-> Po.type.
Canonical poType.
Coercion ppoType : type >-> PPo.type.
Canonical ppoType.
Coercion domType : type >-> Dom.type.
Canonical domType.
Coercion pdomType : type >-> PDom.type.
Canonical pdomType.
Coercion finDomType : type >-> FinDom.type.
Canonical finDomType.
Notation finPDomType := type.
Notation FinPDomType T := (@pack _ T _ _ id _ _ id).
Notation "[ 'finPDomType' 'of' T 'for' cT ]" :=  (@clone _ T cT _ idfun)
  (at level 0, format "[ 'finPDomType'  'of'  T  'for'  cT ]") : form_scope.
Notation "[ 'finPDomType' 'of' T ]" := (@clone _ T _ _ id)
  (at level 0, format "[ 'finPDomType'  'of'  T ]") : form_scope.
End Exports.

End FinPDom.

Export FinPDom.Exports.

Section FFun.

Variables (T : finDomType true) (S : poType true).

Definition ffun_ordMixin := [ordMixin of finfun_type T S by <:].
Canonical ffun_ordType :=
  Eval hnf in OrdType (finfun_type T S) ffun_ordMixin.
Canonical ffun_of_ordType :=
  Eval hnf in [ordType of {ffun T -> S}].

Implicit Types (f g h : {ffun T -> S}).

Definition fappr f g := [forall x : T, f x ⊑ g x].

Lemma fapprP f g : reflect (forall x, f x ⊑ g x) (fappr f g).
Proof. exact: forallP. Qed.

Lemma fapprPn f g : reflect (exists x, f x ⋢ g x) (~~ fappr f g).
Proof. by apply/(iffP existsP). Qed.

Lemma ffun_apprP : Po.axioms_of true fappr.
Proof.
split.
- move=> f; apply/fapprP=> x; exact: apprxx.
- move=> g f h /fapprP fg /fapprP gh; apply/fapprP=> x.
  exact: appr_trans (fg x) (gh x).
- move=> f g /andP [/fapprP fg /fapprP gf]; apply/ffunP=> x.
  by apply/appr_anti; rewrite fg gf.
Qed.

Definition ffun_poMixin := PoMixin ffun_apprP.
Canonical ffun_poType := Eval hnf in PoType (finfun_type T S) ffun_poMixin.
Canonical ffun_of_poType := Eval hnf in [poType of {ffun T -> S}].

End FFun.

Arguments fapprP {_ _} [_ _].
Arguments fapprPn {_ _} [_ _].

Section FFunPPoType.

Variables (T : finDomType true) (S : ppoType true).

Implicit Types f : {ffun T -> S}.

Lemma ffun_botP f : finfun (fun _ => ⊥) ⊑ f.
Proof. by apply/fapprP=> x; rewrite ffunE botP. Qed.

Definition ffun_ppoMixin := PPoMixin ffun_botP.
Canonical ffun_ppoType := Eval hnf in PPoType (finfun_type T S) ffun_ppoMixin.
Canonical ffun_of_ppoType := Eval hnf in [ppoType of {ffun T -> S}].

Lemma fbotE x : (⊥ : {ffun T -> S}) x = ⊥. Proof. by rewrite ffunE. Qed.

End FFunPPoType.

Section FFunDomType.

Variables (T : finDomType true) (S : domType true).

Implicit Types f g h : {ffun T -> S}.

Lemma flub_proof f g :
  [forall x, f x ⊔ g x] ->
  forall x, exists y, f x ⊔ g x == Coh y.
Proof.
move=> /forallP e x; move/(_ x): e.
by case: lub=> [y|] //= _; exists y.
Qed.

Definition flub f g : coh {ffun T -> S} :=
  if decP (@idP [forall x, f x ⊔ g x]) is left e then
    Coh (finfun (fun x => xchoose (flub_proof e x)))
  else Incoh.

Variant flub_spec f g : coh {ffun T -> S} -> Prop :=
| FLubCoh h of (forall x, f x ⊔ g x = Coh (h x)) : flub_spec f g (Coh h)
| FLubIncoh x of f x ⊔ g x = Incoh : flub_spec f g Incoh.

(* FIXME: could use the above proof *)
Lemma flub_appr f g h : flub f g ⊑ Coh h = (f ⊑ h) && (g ⊑ h).
Proof.
apply/(sameP idP)/(iffP andP)=> [[fh gh]|fgh]; last split.
- have e: [forall x, f x ⊔ g x].
    apply/forallP=> x; move: (lub_appr (f x) (g x) (h x)).
    by rewrite (fapprP fh x) (fapprP gh x); case: lub.
  rewrite /flub; case: decP; last by rewrite e.
  move=> {e} e; apply/fapprP=> x; rewrite ffunE.
  move: (xchooseP (flub_proof e x)) (lub_appr (f x) (g x) (h x)).
  move=> /eqP {1}->.
  by rewrite (fapprP fh x) (fapprP gh x).
- move: fgh; rewrite /flub; case: decP=> // e /fapprP fgh.
  apply/fapprP=> x; move/(_ x): fgh; rewrite ffunE; apply: appr_trans.
  by move/eqP: (xchooseP (flub_proof e x)) (appr_lubl (f x) (g x)) => {1}->.
- move: fgh; rewrite /flub; case: decP=> // e /fapprP fgh.
  apply/fapprP=> x; move/(_ x): fgh; rewrite ffunE; apply: appr_trans.
  by move/eqP: (xchooseP (flub_proof e x)) (appr_lubr (f x) (g x)) => {1}->.
Qed.

Definition ffun_domMixin := DomMixin flub_appr.
Canonical ffun_domType := Eval hnf in DomType (finfun_type T S) ffun_domMixin.
Canonical ffun_of_domType := Eval hnf in [domType of {ffun T -> S}].

Lemma flubP f g : flub_spec f g (f ⊔ g).
Proof.
rewrite /lub /= /flub; case: decP=> [e|/negP/existsP].
- apply: FLubCoh=> x; rewrite ffunE.
  exact/eqP/(xchooseP (flub_proof e x)).
- case=> x xP; apply: (@FLubIncoh f g x).
  by case: lub xP.
Qed.

Lemma flubE f g h :
  f ⊔ g = Coh h ->
  forall x, f x ⊔ g x = Coh (h x).
Proof. by case: flubP=> // {h} h hP [<-]. Qed.

Lemma flub_Coh f g h :
  f ⊔ g = Coh h <-> forall x, f x ⊔ g x = Coh (h x).
Proof.
split; first exact: flubE.
case: flubP=> [h'|].
- move=> h'P hP; congr Coh; apply/ffunP => x.
  suff: Coh (h' x) = Coh (h x) by case.
  by rewrite -h'P -hP.
- by move=> x xP /(_ x); rewrite xP.
Qed.

Lemma flub_Incoh f g :
  f ⊔ g = Incoh <-> exists x, f x ⊔ g x = Incoh.
Proof.
case: flubP=> [h hP|x xP].
- by split=> //; case=> x; rewrite hP.
- by split=> // _; exists x.
Qed.

End FFunDomType.

Canonical ffun_pdomType (T : finDomType true) (S : pdomType true) :=
  Eval hnf in PDomType (finfun_type T S).

Canonical ffun_of_pdomType (T : finDomType true) (S : pdomType true) :=
  Eval hnf in PDomType {ffun T -> S}.

Canonical ffun_finDomType (T S : finDomType true) :=
  Eval hnf in FinDomType (finfun_type T S).

Canonical ffun_of_finDomType (T S : finDomType true) :=
  Eval hnf in FinDomType {ffun T -> S}.

Canonical ffun_finPDomType (T : finDomType true) (S : finPDomType true) :=
  Eval hnf in FinPDomType (finfun_type T S).

Canonical ffun_of_finPDomType (T : finDomType true) (S : finPDomType true) :=
  Eval hnf in FinPDomType {ffun T -> S}.

Canonical unit_pdomType := Eval hnf in PDomType unit.

Canonical unit_finDomType := Eval hnf in FinDomType unit.

Canonical unit_finPDomType := Eval hnf in FinPDomType unit.

Canonical option_finDomType (T : finDomType true) :=
  Eval hnf in FinDomType (option T).

Canonical option_finPDomType (T : finDomType true) :=
  Eval hnf in FinPDomType (option T).

Canonical prod_finDomType (T S : finDomType true) :=
  Eval hnf in FinDomType (T * S).

Canonical prod_pdomType (T S : pdomType true) :=
  Eval hnf in PDomType (T * S).

Canonical prod_finPDomType (T S : finPDomType true) :=
  Eval hnf in FinPDomType (T * S).

Canonical sum_finDomType (T S : finDomType true) :=
  Eval hnf in FinDomType (T + S).

Section Lubn.

Variable T : pdomType true.
Implicit Types (x y z : T) (a b c : coh T) (X Y Z : {fset T}).

Definition lubn X : coh T :=
  foldr (fun x b => if b is Coh y then x ⊔ y else Incoh) ⊥ X.

Lemma lubn_appr X y : lubn X ⊑ Coh y = all (fun x => x ⊑ y) X.
Proof.
rewrite /lubn; elim: (val X)=> {X} /= [|x xs <-]; first exact: botP.
by case: (foldr _ _ xs)=> [lubn_xs|]; rewrite /= ?lub_appr ?andbF.
Qed.

Lemma lubn_apprG X b : lubn X ⊑ b = all (fun x => Coh x ⊑ b) X.
Proof.
rewrite /lubn; elim: (val X)=> {X} /= [|x xs <-]; first exact: botP.
by case: foldr b=> [?|] [?|]; rewrite /= ?lub_appr ?andbF ?andbT.
Qed.

Lemma lubn_unique X a :
  (forall b, a ⊑ b = all (fun x => Coh x ⊑ b) X) ->
  a = lubn X.
Proof.
move=> aP; apply/appr_anti; rewrite aP -lubn_apprG apprxx.
by rewrite lubn_apprG -aP apprxx.
Qed.

Lemma lubn0 : lubn fset0 = ⊥. Proof. by []. Qed.
Lemma lubn1 x : lubn (fset1 x) = Coh x.
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

Lemma lubn2 x y : lubn [fset x; y] = x ⊔ y.
Proof. by rewrite !lubnU !lubn1 lubn0 /= lubxB. Qed.

Lemma lubnS X Y : fsubset X Y -> lubn X ⊑ lubn Y.
Proof.
move=> /fsubsetP X_Y; rewrite lubn_apprG.
by apply/allP=> x /X_Y; move: x; apply/allP; rewrite -lubn_apprG apprxx.
Qed.

Lemma appr_lubn x X : x \in X -> Coh x ⊑ lubn X.
Proof. by move: x; apply/allP; rewrite -lubn_apprG apprxx. Qed.

Definition lub_closure X : {fset T} :=
  fset (pmap (fun Y => option_of_coh (lubn Y)) (powerset X)).

Lemma lub_closureP x X:
  reflect (exists2 Y, fsubset Y X & lubn Y = Coh x)
          (x \in lub_closure X).
Proof.
rewrite /lub_closure in_fset mem_pmap; apply/(iffP mapP)=> /=.
  case=> Y; rewrite powersetE => sub.
  by case lubn_Y: (lubn Y)=> [?|] // [->]; exists Y; rewrite // e_x.
by case=> Y sub lubn_Y; exists Y; rewrite ?lubn_Y ?powersetE.
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
  have: lubn Z ⊑ Coh y by rewrite lubn_Z.
  rewrite lubn_appr=> Z_y; rewrite -lubn_Z lubn_apprG.
  apply/allP=> z z_Z; apply: h; rewrite in_fset mem_filter (allP Z_y _ z_Z).
  by rewrite (fsubsetP sub' _ z_Z).
rewrite in_fset mem_filter; case/andP=> x_y x_X.
suffices: Coh y ⊑ b by apply: appr_trans.
by rewrite -lubn_Y lubn_apprG; apply/allP.
Qed.

Lemma lub_closureA X Y :
  fsubset (lub_closure X) (lub_closure Y) = fsubset X (lub_closure Y).
Proof.
apply/(sameP idP)/(iffP idP); last exact: fsubset_trans (lub_closure_ext X).
by rewrite -{2}(lub_closure_idem Y); apply: lub_closureS.
Qed.

Lemma lub_closure0 : lub_closure fset0 = fset1 ⊥.
Proof. by rewrite /lub_closure powerset0 /= fset1E. Qed.

Lemma lub_closure1 x : lub_closure (fset1 x) = [fset x; ⊥].
Proof.
apply/eq_fset=> y; apply/(sameP (lub_closureP _ _))/(iffP fset2P).
- by case=> -> {y}; [exists (fset1 x)|exists fset0];
  rewrite ?lubn0 ?lubn1 ?fsubsetxx ?fsub0set.
- by case=> Y; rewrite fsubset1; case/orP=> /eqP -> {Y};
  rewrite ?lubn0 ?lubn1 => - [->]; eauto.
Qed.

End Lubn.

Arguments lub_closure0 {_}.
Arguments lub_closure1 {_} _.

Section Projections.

Variable T : pdomType true.

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

Definition proj_appr X Y := fsubset (val X) (val Y).

Lemma proj_apprP : Po.axioms_of true proj_appr.
Proof.
split.
- move=> ?; exact: fsubsetxx.
- move=> ???; exact: fsubset_trans.
- by move=> ??; rewrite -eqEfsubset=> /eqP/val_inj.
Qed.

Definition proj_poMixin := PoMixin proj_apprP.
Canonical proj_poType := Eval hnf in PoType proj proj_poMixin.
Canonical proj_of_poType := Eval hnf in [poType of {proj T}].

Lemma proj_botP X : proj_of_fset fset0 ⊑ X.
Proof.
rewrite apprE /= /proj_appr -(eqP (valP X)) /=.
apply: lub_closureS; exact: fsub0set.
Qed.

Definition proj_ppoMixin := PPoMixin proj_botP.
Canonical proj_ppoType := PPoType proj proj_ppoMixin.
Canonical proj_of_ppoType := Eval hnf in [ppoType of {proj T}].

Definition pred_of_proj (X : proj) :=
  [pred x : T | x \in val X].
Canonical proj_predType := mkPredType pred_of_proj.
Canonical proj_of_predType := [predType of {proj T}].

Definition projU X Y := proj_of_fset (X :|: Y).

Lemma projUP X Y x :
  reflect (exists x' y', [/\ x' \in X, y' \in Y & x' ⊔ y' = Coh x])
          (x \in projU X Y).
Proof.
apply/(iffP (lub_closureP _ _));  last first.
  case=> [x' [y' [x'P y'P x'y']]]; exists [fset x'; y']; rewrite ?lubn2 //.
  by apply/fsubsetP=> _ /fset2P [] ->; rewrite in_fsetU ?x'P ?y'P ?orbT.
case=> Z sub; have -> : Z = Z :&: X :|: Z :&: Y.
  apply/eqP; rewrite eqEfsubset fsubUset !fsubsetIl !andbT.
  apply/fsubsetP=> z z_Z; rewrite in_fsetU !in_fsetI.
  by rewrite z_Z /= -in_fsetU (fsubsetP sub _ z_Z).
rewrite lubnU; case lubn_X: (lubn (Z :&: X))=> [x'|] //=.
case lubn_Y: (lubn (Z :&: Y))=> [y'|] //= xy.
exists x', y'; split=> //.
- rewrite inE -(eqP (valP X)); apply/lub_closureP.
  by exists (Z :&: X); rewrite //= fsubsetIr.
- rewrite inE -(eqP (valP Y)); apply/lub_closureP.
  by exists (Z :&: Y); rewrite //= fsubsetIr.
Qed.

End Projections.

Notation "{ 'proj' T }" := (proj_of (Phant T))
  (at level 0, format "{ 'proj'  T }") : type_scope.

Lemma projB (T : pdomType true) (X : {proj T}) : ⊥ \in X.
Proof.
rewrite inE -(eqP (valP X)); apply/lub_closureP.
by exists fset0; rewrite ?fsub0set ?lubn0.
Qed.

Lemma eq_proj (T : pdomType true) (X Y : {proj T}) : X =i Y <-> X = Y.
Proof.
split=> [|-> //] XY; apply/val_inj/eq_fset; exact: XY.
Qed.

Section ProjMap.

Variables (T S : pdomType true).

Implicit Types (X Y : {proj T}).

Definition mapp (f : T -> S) X : {proj S} :=
  proj_of_fset (f @: X).

Lemma eq_mapp f g : f =1 g -> mapp f =1 mapp g.
Proof. by move=> fg X; rewrite /mapp (eq_imfset fg). Qed.

End ProjMap.

Lemma mapp_id (T : pdomType true) (X : {proj T}) : mapp id X = X.
Proof. apply/val_inj; rewrite /= imfset_id; apply/eqP/(valP X). Qed.

Section FinProj.

Variable T : finPDomType true.

Definition projT := proj_of_fset (fset (enum T)).

Lemma in_projT x : x \in projT.
Proof.
rewrite inE /=; apply/lub_closureP; exists (fset1 x).
- by rewrite fsub1set in_fset mem_enum.
- by rewrite lubn1.
Qed.

End FinProj.

Arguments projT {_}.

Section Monotone.

Definition monotone bT bS (T : poType bT) (S : poType bS) (f : T -> S) :=
  forall x y, x ⊑ y -> f x ⊑ f y.

Definition isotone bT bS (T : poType bT) (S : poType bS) (f : T -> S) :=
  forall x y, (f x ⊑ f y) = (x ⊑ y).

Lemma monotone_id bT (T : poType bT) : monotone (@id T).
Proof. by []. Qed.

Lemma monotone_comp bT bS bR (T : poType bT) (S : poType bS) (R : poType bR)
  (f : T -> S) (g : S -> R) :
  monotone f -> monotone g -> monotone (g \o f).
Proof.
by move=> f_mono g_mono x y xy; apply: g_mono; exact: f_mono.
Qed.

End Monotone.

Section Embeddings.

Variables T S : domType true.

Implicit Types f g : T -> S.
Implicit Types X : {fset T}.

Definition lub_preserving f :=
  forall x y, f x ⊔ f y = if x ⊔ y is Coh z then Coh (f z) else Incoh.

Lemma eq_lub_preserving f g : lub_preserving f -> f =1 g -> lub_preserving g.
Proof.
by move=> fP e x y; rewrite -!e fP; case: lub=> //= ?; rewrite e.
Qed.

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

End Embeddings.

Lemma lub_preserving_id (T : domType true) : lub_preserving (@id T).
Proof. by move=> x y; case: (x ⊔ y). Qed.

Lemma lub_preserving_comp (T S R : domType true) (f : T -> S) (g : S -> R) :
  lub_preserving f -> lub_preserving g -> lub_preserving (g \o f).
Proof.
by move=> f_lub g_lub x y; rewrite /= g_lub f_lub; case: (x ⊔ y).
Qed.

Section EmbeddingsPointed.

Variables T S : pdomType true.

Implicit Types f g : T -> S.
Implicit Types X : {fset T}.

Lemma lubn_imfset f X :
  f ⊥ = ⊥ ->
  lub_preserving f ->
  lubn (f @: X) = if lubn X is Coh x then Coh (f x) else Incoh.
Proof.
move=> f_str f_lub; elim/fset_ind: X=> [|x X _ IH].
  by rewrite imfset0 !lubn0 /= f_str.
by rewrite imfsetU1 !lubnU !lubn1 IH; case: (lubn X)=> [x'|].
Qed.

Lemma lub_closure_imfset f X :
  f ⊥ = ⊥ ->
  lub_preserving f ->
  lub_closure (f @: X) = f @: lub_closure X.
Proof.
move=> f_str f_lub; apply/eq_fset=> y.
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
case elubX': (lubn X')=> {y} [x'|//] [<-].
by exists x'=> //; apply/lub_closureP; exists X'.
Qed.

Lemma val_mapp f (X : {proj T}) :
  f ⊥ = ⊥ -> lub_preserving f -> val (mapp f X) = f @: X.
Proof.
by move=> f_str f_lub; rewrite /= lub_closure_imfset // (eqP (valP X)).
Qed.

Lemma mappP f (X : {proj T}) y :
  f ⊥ = ⊥ ->
  lub_preserving f ->
  reflect (exists2 x, x \in X & y = f x) (y \in mapp f X).
Proof. move=> f_str fP; rewrite inE val_mapp //; exact/imfsetP. Qed.

Lemma mem_mapp f (X : {proj T}) x :
  injective f -> f ⊥ = ⊥ -> lub_preserving f ->
  (f x \in mapp f X) = (x \in X).
Proof.
move=> f_inj f_str f_lub; rewrite inE val_mapp //.
apply/(sameP idP)/(iffP idP); first exact: mem_imfset.
by case/imfsetP=> ? ? /f_inj ->.
Qed.

End EmbeddingsPointed.

Lemma mapp_comp (T S R : pdomType true) (g : S -> R) (f : T -> S)
  (X : {proj T}) :
  g ⊥ = ⊥ -> lub_preserving g ->
  f ⊥ = ⊥ -> lub_preserving f ->
  mapp (g \o f) X = mapp g (mapp f X).
Proof.
move=> ????; apply/val_inj; rewrite /= imfset_comp.
by rewrite !lub_closure_imfset // !(eqP (valP X)).
Qed.

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

Section ProjDom.

Variable (T : pdomType true) (X : proj T).

Structure proj_dom := ProjDom {
  proj_elt :> T;
  _        :  proj_elt \in X
}.

Implicit Types x y z : proj_dom.

Canonical proj_dom_subType := [subType for @proj_elt].
Definition proj_dom_eqMixin := [eqMixin of proj_dom by <:].
Canonical proj_dom_eqType := Eval hnf in EqType proj_dom proj_dom_eqMixin.
Definition proj_dom_choiceMixin := [choiceMixin of proj_dom by <:].
Canonical proj_dom_choiceType :=
  Eval hnf in ChoiceType proj_dom proj_dom_choiceMixin.
Definition proj_dom_ordMixin := [ordMixin of proj_dom by <:].
Canonical proj_dom_ordType :=
  Eval hnf in OrdType proj_dom proj_dom_ordMixin.

Definition proj_dom_poMixin := SubPoMixin [subType of proj_dom].
Canonical proj_dom_poType := Eval hnf in PoType proj_dom proj_dom_poMixin.
Canonical proj_dom_subPoType := SubPoType proj_dom (fun _ _ => erefl).

Lemma proj_dom_lubP x y (z : T) : val x ⊔ val y = Coh z -> z \in X.
Proof.
move=> xyz; rewrite inE -(eqP (valP X)).
apply/lub_closureP; exists [fset val x; val y].
  apply/fsubsetP=> ? /fset2P [] ->; exact: valP.
by rewrite lubn2.
Qed.

Definition proj_dom_domMixin :=
  [domMixin of proj_dom by <: using proj_dom_lubP].
Canonical proj_dom_domType :=
  Eval hnf in DomType proj_dom proj_dom_domMixin.
Canonical prod_dom_subDomType := Eval hnf in [subDomType for proj_dom].

Lemma proj_dom_botP x : ProjDom (projB X) ⊑ x.
Proof. exact: botP. Qed.

Definition proj_dom_ppoMixin := PPoMixin proj_dom_botP.
Canonical proj_dom_ppoType := Eval hnf in PPoType proj_dom proj_dom_ppoMixin.
Canonical proj_dom_pdomType := Eval hnf in PDomType proj_dom.

Definition seq_sub_of_proj_dom (x : proj_dom) : seq_sub X :=
  SeqSub (valP x).

Definition proj_dom_of_seq_sub (x : seq_sub X) : proj_dom :=
  ProjDom (valP x).

Lemma seq_sub_of_proj_domK : cancel seq_sub_of_proj_dom proj_dom_of_seq_sub.
Proof. by case/SubP=> x Px; apply/val_inj. Qed.

Definition proj_dom_countMixin := CanCountMixin seq_sub_of_proj_domK.
Canonical proj_dom_countType :=
  Eval hnf in CountType proj_dom proj_dom_countMixin.
Definition proj_dom_finMixin := CanFinMixin seq_sub_of_proj_domK.
Canonical proj_dom_finType :=
  Eval hnf in FinType proj_dom proj_dom_finMixin.
Canonical proj_dom_finDomType := Eval hnf in FinDomType proj_dom.
Canonical proj_dom_finPDomType := Eval hnf in FinPDomType proj_dom.

End ProjDom.

Coercion proj_dom : proj >-> Sortclass.

Section Retract.

Variables (T : finPDomType true) (S : pdomType true).
Variable f : T -> S.
Hypothesis f_str : f ⊥ = ⊥.
Hypothesis f_lub : lub_preserving f.

Implicit Types (x y : T) (a b : S).

Definition retract a : T :=
  if lubn (fset (enum [pred x | f x ⊑ a])) is Coh x then x
  else ⊥.

(*Lemma retract0 a : retract proj0 a = ⊥.
Proof. by rewrite /retract -fset0E lubn0. Qed.

Lemma retract1 x a : retract (proj1 x) a = if f x ⊑ a then Some x else None.
Proof.
by rewrite /retract /=; case: ifP=> _; rewrite -?fset1E -?fset0E.
Qed.
*)

Lemma retractK x : injective f -> retract (f x) = x.
Proof.
move=> f_inj; rewrite /retract (_ : lubn _ = Coh x) //.
apply/esym/lubn_unique; case=> /= [y|]; last by apply/esym/allP=> y.
apply/(sameP idP)/(iffP allP).
  by apply; rewrite in_fset mem_enum inE apprxx.
move=> xy z; rewrite in_fset mem_enum inE // (inj_iso f_inj f_lub) .
by move=> xz; apply: appr_trans xy.
Qed.

Lemma retract_appr a : f (retract a) ⊑ a.
Proof.
rewrite /retract; set Y := fset _; have: lubn (f @: Y) ⊑ Coh a.
  rewrite lubn_appr; apply/allP=> _ /imfsetP [x xP ->].
  by move: xP; rewrite /Y in_fset mem_filter; case/andP.
by move: (lubn_apprG (f @: Y) (Coh a)); rewrite lubn_imfset //; case: lubn.
Qed.

Lemma retract_mono : monotone retract.
Proof.
move=> a b ab; rewrite /retract.
set Ya := fset (enum [pred x | f x ⊑ a]).
set Yb := fset (enum [pred x | f x ⊑ b]).
have Yab : fsubset Ya Yb.
  apply/fsubsetP=> c; rewrite !in_fset !mem_enum !inE => e.
  by apply: appr_trans ab.
have: lubn (f @: Yb) ⊑ Coh b.
  rewrite lubn_appr; apply/allP=> _ /imfsetP [x xP ->].
  by move: xP; rewrite /Yb in_fset mem_filter; case/andP.
move: (lubnS Yab); rewrite lubn_imfset //.
by case: (lubn Ya) (lubn Yb)=> [a'|] [b'|] //.
Qed.

Lemma retractB : injective f -> retract ⊥ = ⊥.
Proof. by move=> f_inj; rewrite -f_str retractK. Qed.

(* The injectivity hypothesis could be removed if we weaken retractK *)
Lemma retractA : injective f -> forall x b, f x ⊑ b = x ⊑ retract b.
Proof.
move=> f_inj x b; apply/(sameP idP)/(iffP idP).
- move=> /(lub_preserving_mono f_lub) xb; apply: appr_trans xb _.
  exact: retract_appr.
- by move=> /retract_mono; rewrite retractK.
Qed.

End Retract.

Lemma eq_retract (T : finPDomType true) (S : pdomType true) (f g : T -> S) :
  f =1 g -> retract f =1 retract g.
Proof.
move=> fg x; have e: [pred y | f y ⊑ x] =i [pred y | g y ⊑ x].
  by move=> y; rewrite !inE fg.
by rewrite /retract (eq_enum e).
Qed.

Lemma retract_comp (T S : finPDomType true) (R : pdomType true)
  (g : S -> R) (f : T -> S) :
  injective g -> g ⊥ = ⊥ -> lub_preserving g ->
  injective f -> f ⊥ = ⊥ -> lub_preserving f ->
  retract (g \o f) =1 retract f \o retract g.
Proof.
move=> g_inj g_str g_lub f_inj f_str f_lub x /=.
apply/appr_anti; rewrite -(@retractA _ _ f) // -(@retractA _ _ g) //.
rewrite (@retract_appr _ _ (g \o f)) /= ?f_str //; last first.
  exact/lub_preserving_comp.
rewrite -(@retractA _ _ (g \o f)) /=; first last.
- exact/inj_comp.
- exact/lub_preserving_comp.
- by rewrite f_str.
apply: appr_trans (retract_appr g_str g_lub x).
exact/(lub_preserving_mono g_lub)/retract_appr.
Qed.

(*Lemma retract_imfset (T S R : pdomType true) (f : T -> S) (g : S -> R) (X : {proj T}) x :
  injective f -> f ⊥ = ⊥ -> lub_preserving f ->
  injective g -> g ⊥ = ⊥ -> lub_preserving g ->
  retract g (mapp f X) (f x)

Lemma project_imfset (T S : domType true) (f : T -> S) (X : {proj T}) x :
  injective f -> lub_preserving f ->
  project (mapp f X) (f x) = omap f (project X x).
Proof.
move=> f_inj f_lub; apply: appr_anti; apply/andP; split.
- apply/projectPG=> _ /mappP - /(_ f_lub) [x' x'_X ->].
  rewrite inj_iso // => x'_x.
  move/projectPG/(_ _ x'_X x'_x): (apprxx (project X x)).
  case: (project X x)=> [x''|] //; rewrite !oapprE /= => x'_x''.
  by rewrite inj_iso.
- case X_x: (project X x)=> [x'|] //=.
  move/projectPG: (apprxx (project (mapp f X) (f x))); apply.
  + by rewrite mem_mapp // (project_lub_closure X_x).
  + by rewrite inj_iso //; move: (project_appr X x); rewrite X_x.
Qed.*)

Section Mono.

Variables (T : finDomType true) (S : domType true).

Definition monotoneb (f : T -> S) :=
  [forall x : T, forall y, x ⊑ y ==> f x ⊑ f y].

Lemma monotoneP f : reflect (monotone f) (monotoneb f).
Proof.
apply/(iffP idP).
- move=> f_mono x y xy.
  by move: f_mono=> /forallP/(_ x)/forallP/(_ y)/implyP/(_ xy).
- move=> f_mono.
  by apply/forallP=> x; apply/forallP=> y; apply/implyP/f_mono.
Qed.

Record mono := Mono {
  mono_val :> {ffun T -> S};
  _        :  monotoneb mono_val
}.

Definition mono_of & phant (T -> S) := mono.
Identity Coercion mono_of_mono : mono_of >-> mono.

Notation "{ 'mono' T }" := (mono_of (Phant T))
  (at level 0, format "{ 'mono'  T }") : form_scope.

Implicit Types f g h : {mono T -> S}.

Canonical mono_subType := Eval hnf in [subType for mono_val].
Definition mono_eqMixin := [eqMixin of mono by <:].
Canonical mono_eqType := Eval hnf in EqType mono mono_eqMixin.
Definition mono_choiceMixin := [choiceMixin of mono by <:].
Canonical mono_choiceType := Eval hnf in ChoiceType mono mono_choiceMixin.
Definition mono_ordMixin := [ordMixin of mono by <:].
Canonical mono_ordType := Eval hnf in OrdType mono mono_ordMixin.
Definition mono_poMixin := [poMixin of mono by <:].
Canonical mono_poType := Eval hnf in PoType mono mono_poMixin.
Canonical mono_subPoType := Eval hnf in SubPoType mono (fun _ _ => erefl).

Lemma monoP f : monotone f.
Proof. exact/monotoneP/(valP f). Qed.

Lemma monotoneb_lub f g hh : val f ⊔ val g = Coh hh -> monotoneb hh.
Proof.
move=> fg; apply/monotoneP=> x y xy.
suff: Coh (hh x) ⊑ Coh (hh y) by []; rewrite -!(flubE fg).
by apply: mono_lub; apply: monoP.
Qed.

Definition mono_domMixin := [domMixin of mono by <: using monotoneb_lub].
Canonical mono_domType := Eval hnf in DomType mono mono_domMixin.
Canonical mono_subDomType := Eval hnf in [subDomType for mono].

Canonical mono_of_subType := Eval hnf in [subType of {mono T -> S}].
Canonical mono_of_eqType := Eval hnf in [eqType of {mono T -> S}].
Canonical mono_of_choiceType := Eval hnf in [choiceType of {mono T -> S}].
Canonical mono_of_ordType := Eval hnf in [ordType of {mono T -> S}].
Canonical mono_of_poType := Eval hnf in [poType of {mono T -> S}].
Canonical mono_of_domType := Eval hnf in [domType of {mono T -> S}].

Lemma finfun_monotone (f : T -> S) (H : monotone f) : monotoneb (finfun f).
Proof. by apply/monotoneP=> x y xy; rewrite !ffunE; apply: H. Qed.

Definition mkmono (f : T -> S) (H : monotone f) : {mono T -> S} :=
  Sub (finfun f) (finfun_monotone H).

Lemma mkmonoE (f : T -> S) (H : monotone f) : @mkmono f H =1 f.
Proof. exact: ffunE. Qed.

Lemma mono_lub_Coh f g h :
  f ⊔ g = Coh h <-> forall x, f x ⊔ g x = Coh (h x).
Proof.
split.
- by move=> fg; move: (lub_val f g); rewrite fg=> /flub_Coh; apply.
- move=> /flub_Coh hP; move: (lub_val f g); rewrite /= hP.
  by case: (f ⊔ g)=> [?|] //= [] /val_inj ->.
Qed.

Lemma mono_lub_Incoh f g :
  f ⊔ g = Incoh <-> exists x, f x ⊔ g x = Incoh.
Proof.
split.
- by move=> fg; move: (lub_val f g); rewrite fg=> /flub_Incoh; apply.
- move/flub_Incoh=> hP; move: (lub_val f g); rewrite /= hP.
  by case: (f ⊔ g).
Qed.

End Mono.

Notation "{ 'mono' T }" := (mono_of (Phant T))
  (at level 0, format "{ 'mono'  T }") : form_scope.

Arguments mkmono {_ _} _ _.

Definition mono_id (T : finDomType true) : {mono T -> T} :=
  mkmono id (@monotone_id _ T).

Definition mono_comp
    (T S R : finDomType true) (g : {mono S -> R}) (f : {mono T -> S}) :
    {mono T -> R} :=
  mkmono (g \o f) (monotone_comp (monoP f) (monoP g)).

Section MonoPDom.

Variables (T : finDomType true) (S : pdomType true).

Program Definition mono_bot : {mono T -> S} := @Mono _ _ ⊥ _.
Next Obligation.
by apply/monotoneP=> x y xy; rewrite fbotE botP.
Qed.

Lemma mono_botP f : mono_bot ⊑ f.
Proof. by apply/fapprP=> x; rewrite fbotE botP. Qed.

Definition mono_ppoMixin := PPoMixin mono_botP.
Canonical mono_ppoType := Eval hnf in PPoType (mono T S) mono_ppoMixin.
Canonical mono_of_ppoType := Eval hnf in [ppoType of {mono T -> S}].
Canonical mono_pdomType := Eval hnf in PDomType (mono T S).
Canonical mono_of_pdomType := Eval hnf in PDomType {mono T -> S}.

End MonoPDom.

Section MonoFin.

Variables (T S : finDomType true).

(* FIXME: The subtype-based notations for declaring count and fin mixins are not
   working. *)
Canonical mono_countMixin :=
  Eval hnf in sub_countMixin [subType of mono T S].
Canonical mono_countType :=
  Eval hnf in CountType (mono T S) mono_countMixin.
Canonical mono_of_countType :=
  Eval hnf in [countType of {mono T -> S}].
Canonical mono_subCountType := Eval hnf in [subCountType of mono T S].
Canonical mono_of_subCountType := Eval hnf in [subCountType of {mono T -> S}].
Definition mono_finMixin := SubFinMixin [subCountType of mono T S].
Canonical mono_finType := Eval hnf in FinType (mono T S) mono_finMixin.
Canonical mono_of_finType := Eval hnf in [finType of {mono T -> S}].
Canonical mono_finDomType := Eval hnf in FinDomType (mono T S).
Canonical mono_of_finDomType := Eval hnf in FinDomType (mono T S).

End MonoFin.

Canonical mono_finPDomType (T : finDomType true) (S : finPDomType true) :=
  Eval hnf in FinPDomType (mono T S).
Canonical mono_of_finPDomType (T : finDomType true) (S : finPDomType true) :=
  Eval hnf in FinPDomType {mono T -> S}.

Reserved Notation "g ∘ f" (at level 20, left associativity).

Set Universe Polymorphism.

Module Cat.

Section ClassDef.

Universes i.

Record class_of (T : Type@{i}) := Class {
  hom  : T -> T -> Type@{i};
  id   : forall X, hom X X;
  comp : forall X Y Z, hom Y Z -> hom X Y -> hom X Z;
  _    : forall X Y (f : hom X Y), comp f (id _) = f;
  _    : forall X Y (f : hom X Y), comp (id _) f = f;
  _    : forall X Y Z W (h : hom Z W) (g : hom Y Z) (f : hom X Y),
           comp h (comp g f) = comp (comp h g) f
}.

Record type := Pack {sort : Type@{i}; _ : class_of sort}.
Local Coercion sort : type >-> Sortclass.
Variables (T : Type) (cT : type).
Definition class := let: Pack _ c as cT' := cT return class_of cT' in c.
Definition clone c of phant_id class c := @Pack T c.
Let xT := let: Pack T _ := cT in T.
Notation xclass := (class : class_of xT).

End ClassDef.

Module Import Exports.
Coercion sort : type >-> Sortclass.
Notation catType := type.
Notation catMixin := class_of.
Notation CatMixin := Class.
Notation CatType T m := (@Pack T m).
Notation "[ 'catType' 'of' T 'for' cT ]" :=  (@clone T cT _ idfun)
  (at level 0, format "[ 'catType'  'of'  T  'for'  cT ]") : form_scope.
Notation "[ 'catType' 'of' T ]" := (@clone T _ _ (fun x => x))
  (at level 0, format "[ 'catType'  'of'  T ]") : form_scope.
End Exports.

End Cat.

Export Cat.Exports.

Definition hom (C : catType) (X Y : C) :=
  Cat.hom (Cat.class C) X Y.

Definition cat_comp (C : catType) (X Y Z : C) : hom Y Z -> hom X Y -> hom X Z :=
  @Cat.comp _ (Cat.class C) X Y Z.

Definition cat_id (C : catType) (X : C) : hom X X := Cat.id (Cat.class C) X.

Section CatTheory.

Variable C : catType.

Implicit Types X Y Z W : C.

Local Notation "g ∘ f" := (cat_comp g f).
Local Notation "1" := (cat_id _).

Lemma compf1 X Y (f : hom X Y) : f ∘ 1 = f.
Proof.
by move: f; unfold cat_comp, cat_id, hom; case: Cat.class.
Qed.

Lemma comp1f X Y (f : hom X Y) : 1 ∘ f = f.
Proof.
by move: f; unfold cat_comp, cat_id, hom; case: Cat.class.
Qed.

Lemma compA X Y Z W (h : hom Z W) (g : hom Y Z) (f : hom X Y) :
  h ∘ (g ∘ f) = h ∘ g ∘ f.
Proof.
by move: h g f; unfold cat_comp, hom; case: Cat.class.
Qed.

End CatTheory.

Local Notation "g ∘ f" := (cat_comp g f).
Local Notation "1" := (cat_id _).

Record functor (C D : catType) := Functor {
  fobj  :> C -> D;
  fmap  :  forall X Y : C, hom X Y -> hom (fobj X) (fobj Y);
  fmap1 :  forall (X : C), fmap (cat_id X) = 1;
  fmapD :  forall (X Y Z : C) (g : hom Y Z) (f : hom X Y),
             fmap (g ∘ f) = fmap g ∘ fmap f
}.

Arguments Functor {_ _} _ _ _ _.

Definition functor_of (C D : catType) & phant (C -> D) := functor C D.
Notation "{ 'functor' T }" := (functor_of (Phant T))
  (at level 0, format "{ 'functor'  T }") : form_scope.

Identity Coercion functor_of_functor : functor_of >-> functor.

Definition idF (C : catType) : {functor C -> C} :=
  Functor id (fun _ _ => id) (fun _ => erefl) (fun _ _ _ _ _ => erefl).

Arguments idF {_}.

Program Definition constF (C D : catType) (X : D) : {functor C -> D} :=
  Functor (fun _ => X) (fun _ _ _ => 1) (fun _ => erefl) _.

Next Obligation. by move=> *; rewrite compf1. Qed.

Program Definition compF (C D E : catType)
    (G : {functor D -> E}) (F : {functor C -> D}) :
    {functor C -> E} :=
  Functor (G \o F) (fun X Y f => fmap G (fmap F f)) _ _.

Next Obligation. by move=> *; rewrite /= !fmap1. Qed.
Next Obligation. by move=> *; rewrite /= !fmapD. Qed.

Section ProdCat.

Variables C D E : catType.

Implicit Types (X Y Z W : C * D).

Local Notation prod_hom X Y := (hom X.1 Y.1 * hom X.2 Y.2)%type.

Definition prod_id X : prod_hom X X := (1, 1).

Definition prod_comp X Y Z (g : prod_hom Y Z) (f : prod_hom X Y) :
  prod_hom X Z :=
  (g.1 ∘ f.1, g.2 ∘ f.2).

Lemma prod_compf1 X Y (f : prod_hom X Y) : prod_comp f (prod_id _) = f.
Proof.
by case: f=> [a b]; unfold prod_comp; rewrite /= !compf1.
Qed.

Lemma prod_comp1f X Y (f : prod_hom X Y) : prod_comp (prod_id _) f = f.
Proof.
by case: f=> [a b]; unfold prod_comp; rewrite /= !comp1f.
Qed.

Lemma prod_compA X Y Z W
  (h : prod_hom Z W) (g : prod_hom Y Z) (f : prod_hom X Y) :
  prod_comp h (prod_comp g f) = prod_comp (prod_comp h g) f.
Proof.
by unfold prod_comp; case: h g f => [??] [??] [??]; rewrite /= !compA.
Qed.

Definition prod_catMixin := CatMixin prod_compf1 prod_comp1f prod_compA.
Canonical prod_catType := Eval hnf in CatType (C * D) prod_catMixin.

Program Definition tupleF (F : {functor E -> C}) (G : {functor E -> D}) :
    {functor E -> C * D} :=
  Functor (fun A => (F A, G A)) (fun A B f => (fmap F f, fmap G f)) _ _.

Next Obligation. by move=> /= F G A; rewrite !fmap1. Qed.
Next Obligation. by move=> /= F G A1 A2 A3 g f; rewrite !fmapD. Qed.

End ProdCat.

Unset Universe Polymorphism.

Module Lat.

Section ClassDef.

Record mixin_of (T : poType true) := Mixin {
  join : T -> T -> T;
  _    : forall x y z, join x y ⊑ z = (x ⊑ z) && (y ⊑ z)
}.

Record class_of T := Class {
  base : PPo.class_of true T;
  mixin : mixin_of (Po.Pack base)
}.
Local Coercion base : class_of >-> PPo.class_of.

Structure type := Pack {sort; _ : class_of sort}.
Local Coercion sort : type >-> Sortclass.
Variables (T : Type) (cT : type).
Definition class := let: Pack _ c as cT' := cT return class_of cT' in c.
Definition clone c of phant_id class c := @Pack T c.
Let xT := let: Pack T _ := cT in T.
Notation xclass := (class : class_of xT).

Definition pack :=
  fun b (bT : ppoType true) & phant_id (PPo.class bT) b =>
  fun m => Pack (@Class T b m).

(* Inheritance *)
Definition eqType := @Equality.Pack cT xclass xT.
Definition choiceType := @Choice.Pack cT xclass xT.
Definition ordType := @Ord.Pack cT xclass xT.
Definition poType := @Po.Pack true cT xclass.
Definition ppoType := @PPo.Pack true cT xclass.

End ClassDef.

Module Import Exports.
Coercion base : class_of >-> PPo.class_of.
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
Coercion ppoType : type >-> PPo.type.
Canonical ppoType.
Notation latType := type.
Notation latMixin := mixin_of.
Notation LatMixin := Mixin.
Notation LatType T m := (@pack T _ _ id m).
Notation "[ 'latType' 'of' T 'for' cT ]" :=  (@clone T cT _ idfun)
  (at level 0, format "[ 'latType'  'of'  T  'for'  cT ]") : form_scope.
Notation "[ 'latType' 'of' T ]" := (@clone T _ _ id)
  (at level 0, format "[ 'latType'  'of'  T ]") : form_scope.
End Exports.

End Lat.

Export Lat.Exports.

Section LatTheory.

Variable T : latType.

Implicit Types x y z : T.

Definition join : T -> T -> T := Lat.join (Lat.class T).

Notation "x ∨ y" := (join x y) (at level 40, left associativity).

Lemma appr_join x y z : x ∨ y ⊑ z = (x ⊑ z) && (y ⊑ z).
Proof.
rewrite /join.
by case: (Lat.mixin (Lat.class T))=> ? /= /(_ x y z).
Qed.

Lemma join_apprl x y : x ⊑ x ∨ y.
Proof.
by move: (apprxx (x ∨ y)); rewrite appr_join; case/andP.
Qed.

Lemma join_apprr x y : y ⊑ x ∨ y.
Proof.
by move: (apprxx (x ∨ y)); rewrite appr_join; case/andP.
Qed.

Lemma joinxx : idempotent join.
Proof.
by move=> x; apply/appr_anti; rewrite join_apprr appr_join apprxx.
Qed.

Lemma joinC : commutative join.
Proof.
by move=> x y; apply/appr_anti; rewrite !appr_join !join_apprl !join_apprr.
Qed.

Lemma joinA : associative join.
Proof.
move=> /= x y z; apply/appr_anti/andP; split.
- rewrite appr_join (appr_trans (join_apprl x y)) //= ?join_apprl //.
  rewrite appr_join (appr_trans (join_apprr x y)) //= ?join_apprr //.
  by rewrite join_apprl.
- rewrite 2!appr_join join_apprl (appr_trans (join_apprl y z)) ?join_apprr //.
  by rewrite (appr_trans (join_apprr y z)) ?join_apprr.
Qed.

End LatTheory.

Arguments join {_}.

Notation "x ∨ y" := (join x y) (at level 40, left associativity).

Section LatCat.

Variable T : latType.

Implicit Types x y z : T.

Definition lat_hom x y : Type := x ⊑ y.

Definition lat_id x : lat_hom x x := apprxx x.

Definition lat_comp x y z (g : lat_hom y z) (f : lat_hom x y) : lat_hom x z :=
  appr_trans f g.

Lemma lat_compf1 x y (f : lat_hom x y) : lat_comp f (lat_id _) = f.
Proof. exact: eq_irrelevance. Qed.

Lemma lat_comp1f x y (f : lat_hom x y) : lat_comp (lat_id _) f = f.
Proof. exact: eq_irrelevance. Qed.

Lemma lat_compA x y z w (h : lat_hom z w) (g : lat_hom y z) (f : lat_hom x y) :
  lat_comp h (lat_comp g f) = lat_comp (lat_comp h g) f.
Proof. exact: eq_irrelevance. Qed.

Definition lat_catMixin := CatMixin lat_compf1 lat_comp1f lat_compA.
Canonical lat_catType := CatType T lat_catMixin.

End LatCat.

Coercion lat_catType : latType >-> catType.

Lemma nat_apprP : Po.axioms_of true leq.
Proof.
split.
- exact: leqnn.
- exact: leq_trans.
- exact: anti_leq.
Qed.

Definition nat_poMixin := PoMixin nat_apprP.
Canonical nat_poType := Eval hnf in PoType nat nat_poMixin.
Definition nat_ppoMixin := PPoMixin leq0n.
Canonical nat_ppoType := Eval hnf in PPoType nat nat_ppoMixin.

Definition nat_latMixin := LatMixin (fun x y z => geq_max z x y).
Canonical nat_latType := Eval hnf in LatType nat nat_latMixin.
Canonical nat_catType :=
  Eval hnf in CatType nat (lat_catMixin [latType of nat]).

Section ProjLatType.

Variable (T : pdomType true).

Implicit Types X Y Z : {proj T}.

Lemma proj_joinP X Y Z : projU X Y ⊑ Z = (X ⊑ Z) && (Y ⊑ Z).
Proof.
apply/(sameP idP)/(iffP idP).
- case/andP=> XZ YZ.
  rewrite apprE /= /proj_appr -(eqP (valP Z)).
  by apply: lub_closureS; rewrite fsubUset; apply/andP; split.
- move=> XYZ; apply/andP; split; apply: appr_trans XYZ.
  + exact: (fsubset_trans (fsubsetUl X Y) (lub_closure_ext _)).
  + exact: (fsubset_trans (fsubsetUr X Y) (lub_closure_ext _)).
Qed.

Definition proj_latMixin := LatMixin proj_joinP.
Canonical proj_latType := Eval hnf in LatType (proj T) proj_latMixin.
Canonical proj_of_latType := Eval hnf in [latType of {proj T}].
Canonical proj_catType :=
  CatType (proj T) (lat_catMixin [latType of proj T]).
Canonical proj_of_catType := Eval hnf in [catType of {proj T}].
Definition proj_domMixin := @DomMixin _ _ (fun X Y => Coh (projU X Y)) proj_joinP.
Canonical proj_domType := Eval hnf in DomType (proj T) proj_domMixin.
Canonical proj_of_domType := Eval hnf in [domType of {proj T}].
Canonical proj_pdomType := Eval hnf in PDomType (proj T).
Canonical proj_of_pdomType := Eval hnf in PDomType {proj T}.

End ProjLatType.

Section ProjFin.

Variable T : finPDomType true.

(* FIXME: Move to extructures *)

Definition fset_countMixin :=
  sub_countMixin (fset_subType T).
Canonical fset_countType :=
  Eval hnf in CountType (FSet.fset_type T) fset_countMixin.
Canonical fset_of_countType :=
  Eval hnf in [countType of {fset T}].

Definition fset_enum := val (powerset (fset (enum T))).
Lemma fset_enumP : fset_enum =i {: {fset T}}.
Proof.
move=> /= X; rewrite /fset_enum powersetE.
by apply/fsubsetP=> /= x; rewrite in_fset mem_enum.
Qed.
Definition fset_finMixin :=
  UniqFinMixin (uniq_fset (powerset (fset (enum T)))) fset_enumP.
Canonical fset_finType :=
  Eval hnf in FinType (FSet.fset_type T) fset_finMixin.
Canonical fset_of_finType :=
  Eval hnf in [finType of {fset T}].

Definition proj_countMixin := [countMixin of proj T by <:].
Canonical proj_countType := Eval hnf in CountType (proj T) proj_countMixin.
Canonical proj_of_countType := Eval hnf in [countType of {proj T}].
Canonical proj_subCountType := Eval hnf in [subCountType of proj T].
Canonical proj_of_subCountType := Eval hnf in [subCountType of {proj T}].
Definition proj_finMixin := [finMixin of proj T by <:].
Canonical proj_finType := Eval hnf in FinType (proj T) proj_finMixin.
Canonical proj_of_finType := Eval hnf in [finType of {proj T}].
Canonical proj_finDomType := Eval hnf in FinDomType (proj T).
Canonical proj_of_finDomType := Eval hnf in FinDomType {proj T}.
Canonical proj_finPDomType := Eval hnf in FinPDomType (proj T).
Canonical proj_of_finPDomType := Eval hnf in FinPDomType {proj T}.

End ProjFin.

Section FinDomCatType.

Implicit Types T S R : finDomType true.

Definition lub_preservingb
    (T : finDomType true) (S : domType true) (f : T -> S) :=
  [forall x, forall y, f x ⊔ f y ==
    if x ⊔ y is Coh z then Coh (f z) else Incoh].

Lemma lub_preservingP T S f :
  reflect (lub_preserving f) (@lub_preservingb T S f).
Proof.
apply/(iffP forallP).
- by move=> H x y; move/(_ x)/forallP/(_ y)/eqP: H.
- move=> H x; apply/forallP=> y; apply/eqP.
  exact: H.
Qed.

Section TypeDef.

Variables T S : finDomType true.

Record finDom_hom := FinDomHom {
  dom_hom_val :> {mono T -> S};
  _           :  injectiveb dom_hom_val && lub_preservingb dom_hom_val
}.

Canonical finDom_hom_subType := Eval hnf in [subType for dom_hom_val].
Definition finDom_eqMixin := [eqMixin of finDom_hom by <:].
Canonical finDom_eqType := Eval hnf in EqType finDom_hom finDom_eqMixin.

Lemma finDom_hom_inj (f : finDom_hom) : injective f.
Proof. by apply/injectiveP; case/andP: (valP f). Qed.

Lemma finDom_hom_lub (f : finDom_hom) : lub_preserving f.
Proof. by apply/lub_preservingP; case/andP: (valP f). Qed.

Lemma finDom_hom_iso (f : finDom_hom) : isotone f.
Proof. apply: inj_iso; [exact: finDom_hom_inj|exact: finDom_hom_lub]. Qed.

End TypeDef.

Lemma finDom_id_proof T :
  injectiveb (@mono_id T) && lub_preservingb (@mono_id T).
Proof.
apply/andP; split.
- by apply/injectiveP=> ??; rewrite !mkmonoE.
- apply/lub_preservingP; apply: eq_lub_preserving (@lub_preserving_id T) _.
  by move=> ?; rewrite mkmonoE.
Qed.

Definition finDom_id T : finDom_hom T T :=
  FinDomHom (finDom_id_proof T).

Lemma finDom_comp_proof T S R (g : finDom_hom S R) (f : finDom_hom T S) :
  injectiveb (mono_comp g f) && lub_preservingb (mono_comp g f).
Proof.
apply/andP; split.
- apply/injectiveP.
  apply: eq_inj _ (fsym (mkmonoE _)); apply: inj_comp; exact: finDom_hom_inj.
- apply/lub_preservingP.
  apply: eq_lub_preserving _ (fsym (mkmonoE _)).
  apply: lub_preserving_comp; exact: finDom_hom_lub.
Qed.

Definition finDom_comp T S R (g : finDom_hom S R) (f : finDom_hom T S) :=
  FinDomHom (finDom_comp_proof g f).

Lemma finDom_compf1 T S (f : finDom_hom T S) :
  finDom_comp f (finDom_id T) = f.
Proof.
by apply/val_inj/val_inj/ffunP=> x; rewrite /= ffunE /= ffunE.
Qed.

Lemma finDom_comp1f T S (f : finDom_hom T S) :
  finDom_comp (finDom_id S) f = f.
Proof.
by apply/val_inj/val_inj/ffunP=> x; rewrite /= ffunE /= ffunE.
Qed.

Lemma finDom_compA T S R U
  (h : finDom_hom R U) (g : finDom_hom S R) (f : finDom_hom T S) :
  finDom_comp h (finDom_comp g f) = finDom_comp (finDom_comp h g) f.
Proof.
by apply/val_inj/val_inj/ffunP=> x; do ![rewrite /= ffunE].
Qed.

Definition finDom_catMixin := CatMixin finDom_compf1 finDom_comp1f finDom_compA.
Canonical finDom_catType := CatType (finDomType true) finDom_catMixin.

Lemma finDom_idE T (x : T) : cat_id T x = x.
Proof. by rewrite mkmonoE. Qed.

Lemma finDom_compE T S R (g : hom S R) (f : hom T S) x : (g ∘ f) x = g (f x).
Proof. by rewrite mkmonoE. Qed.

End FinDomCatType.

Section FinPDomCatType.

Implicit Types T S R : finPDomType true.

Section TypeDef.

Variables T S : finPDomType true.

Record finPDom_hom := FinPDomHom {
  pdom_hom_val :> finDom_hom T S;
  _            :  pdom_hom_val ⊥ == ⊥
}.

Canonical finPDom_hom_subType := Eval hnf in [subType for pdom_hom_val].
Definition finPDom_eqMixin := [eqMixin of finPDom_hom by <:].
Canonical finPDom_eqType := Eval hnf in EqType finPDom_hom finPDom_eqMixin.

Lemma finPDom_homB (f : finPDom_hom) : f ⊥ = ⊥.
Proof. exact/eqP/(valP f). Qed.

End TypeDef.

Lemma finPDom_id_proof T : finDom_id T ⊥ == ⊥.
Proof. by apply/eqP; rewrite mkmonoE. Qed.

Definition finPDom_id T : finPDom_hom T T :=
  FinPDomHom (finPDom_id_proof T).

Lemma finPDom_comp_proof T S R (g : finPDom_hom S R) (f : finPDom_hom T S) :
  finDom_comp g f ⊥ == ⊥.
Proof. by apply/eqP; rewrite mkmonoE /= !finPDom_homB. Qed.

Definition finPDom_comp T S R (g : finPDom_hom S R) (f : finPDom_hom T S) :=
  FinPDomHom (finPDom_comp_proof g f).

Lemma finPDom_compf1 T S (f : finPDom_hom T S) :
  finPDom_comp f (finPDom_id T) = f.
Proof.
by apply/val_inj/val_inj/val_inj/ffunP=> x; rewrite /= ffunE /= ffunE.
Qed.

Lemma finPDom_comp1f T S (f : finPDom_hom T S) :
  finPDom_comp (finPDom_id S) f = f.
Proof.
by apply/val_inj/val_inj/val_inj/ffunP=> x; rewrite /= ffunE /= ffunE.
Qed.

Lemma finPDom_compA T S R U
  (h : finPDom_hom R U) (g : finPDom_hom S R) (f : finPDom_hom T S) :
  finPDom_comp h (finPDom_comp g f) = finPDom_comp (finPDom_comp h g) f.
Proof.
by apply/val_inj/val_inj/val_inj/ffunP=> x; do ![rewrite /= ffunE].
Qed.

Definition finPDom_catMixin := CatMixin finPDom_compf1 finPDom_comp1f finPDom_compA.
Canonical finPDom_catType := CatType (finPDomType true) finPDom_catMixin.

Lemma finPDom_idE T (x : T) : cat_id T x = x.
Proof. by rewrite mkmonoE. Qed.

Lemma finPDom_compE T S R (g : hom S R) (f : hom T S) x : (g ∘ f) x = g (f x).
Proof. by rewrite mkmonoE. Qed.

Program Definition finPDom_bot T : finPDom_hom unit_finPDomType T :=
  @FinPDomHom _ _ (@FinDomHom _ _ ⊥ _) _.

Next Obligation.
move=> T; apply/andP; split.
- by apply/injectiveP; case=> [] [].
- by apply/lub_preservingP; case=> [] []; rewrite !lubxx.
Qed.

Next Obligation. by move=> T /=; rewrite ffunE. Qed.

End FinPDomCatType.

Arguments finPDom_bot {_}.

Program Definition forgetF : {functor finPDomType true -> finDomType true} :=
  Functor (fun T => T) (fun T S f => f)
          (fun T => erefl) (fun T S R f g => erefl).

Program Definition prodF :
    {functor finPDomType true * finPDomType true -> finPDomType true} :=
  Functor (fun X => [finPDomType of X.1 * X.2])
          (fun (X Y : finPDomType true * finPDomType true) f =>
             Sub (Sub (mkmono (fun x : X.1 * X.2 => (f.1 x.1, f.2 x.2) : [finPDomType of Y.1 * Y.2]) _) _) _)
          _ _.

Next Obligation.
move=> [T1 T2] [S1 S2] [/= f1 f2] [x1 x2] [y1 y2] /andP [xy1 xy2].
by apply/andP; split; apply: monoP.
Qed.

Next Obligation.
move=> [T1 T2] [S1 S2] [/= f1 f2]; apply/andP; split.
- apply/injectiveP; case=> [x1 x2] [y1 y2]; rewrite !ffunE /=.
  by case=> /finDom_hom_inj -> /finDom_hom_inj ->.
- apply/lub_preservingP; case=> [x1 x2] [y1 y2]; rewrite !ffunE /=.
  rewrite /lub /= /prod_lub /= !finDom_hom_lub.
  by case: (x1 ⊔ y1) (x2 ⊔ y2)=> [xy1|] [xy2|] //=; rewrite ffunE.
Qed.

Next Obligation.
move=> [T1 T2] [S1 S2] [/= f1 f2]; apply/eqP; rewrite ffunE.
by rewrite (eqP (valP f1)) (eqP (valP f2)).
Qed.

Next Obligation.
move=> [T1 T2]; apply/val_inj/val_inj/val_inj/ffunP; case=> [x1 x2].
by rewrite /= !ffunE.
Qed.

Next Obligation.
case=> [T1 T2] [S1 S2] [R1 R2] [/= g1 g2] [/= f1 f2].
apply/val_inj/val_inj/val_inj/ffunP; case=> [x1 x2] /=.
by rewrite /= !ffunE /= !ffunE.
Qed.

Definition sumF_map
    (X Y : finDomType true * finDomType true)
    (f : hom X.1 Y.1 * hom X.2 Y.2)
    (x : [finDomType of X.1 + X.2]) : [finDomType of Y.1 + Y.2] :=
  match x with
  | inl x => inl (f.1 x)
  | inr x => inr (f.2 x)
  end.

Program Definition sumF :
    {functor finDomType true * finDomType true -> finDomType true} :=
  Functor (fun X => sum_finDomType X.1 X.2)
          (fun X Y f => Sub (mkmono (sumF_map f)  _) _)
          _ _.

Next Obligation.
move=> [T1 T2] [S1 S2] [/= f1 f2] [] x [] y //.
- exact: (monoP f1).
- exact: (monoP f2).
Qed.

Next Obligation.
move=> [T1 T2] [S1 S2] [/= f1 f2]; apply/andP; split.
- by apply/injectiveP; case=> [] x [] y; rewrite !ffunE //=;
  case=> /finDom_hom_inj ->.
- by apply/lub_preservingP; case=> [] x [] y; rewrite !ffunE //=;
  rewrite /lub /= finDom_hom_lub; case: (x ⊔ y)=> [xy|] //=;
  rewrite !ffunE.
Qed.

Next Obligation.
by move=> [T1 T2]; apply/val_inj/val_inj/ffunP; case=> /= x;
rewrite !ffunE /= !ffunE.
Qed.

Next Obligation.
move=> [T1 T2] [S1 S2] [R1 R2] [/= g1 g2] [/= f1 f2].
by apply/val_inj/val_inj/ffunP; case=> [] x /=; rewrite !ffunE /= !ffunE.
Qed.

Program Definition optionF :
    {functor finDomType true -> finPDomType true} :=
  Functor option_finPDomType
          (fun T S f => Sub (Sub (mkmono (omap f) _) _) _)
          _ _.

Next Obligation.
move=> T S f [x|] [y|] //=; exact: (monoP f).
Qed.

Next Obligation.
move=> T S f; apply/andP; split.
- apply/injectiveP; case=> [x|] [y|]; rewrite !ffunE //=.
  by case=> /finDom_hom_inj ->.
- apply/lub_preservingP; case=> [x|] [y|]; rewrite !ffunE //= ?ffunE //=.
  rewrite /lub /= finDom_hom_lub; case: (x ⊔ y)=> [xy|] //=.
  by rewrite ffunE.
Qed.

Next Obligation. by move=> T S f; rewrite /= ffunE. Qed.

Next Obligation.
by move=> T; apply/val_inj/val_inj/val_inj/ffunP; case=> [x|] /=;
rewrite !ffunE /= ?ffunE.
Qed.

Next Obligation.
by move=> T S R g f; apply/val_inj/val_inj/val_inj/ffunP; case=> [x|];
rewrite !ffunE /= !ffunE.
Qed.

Program Definition monoF :
    {functor finPDomType true * finPDomType true -> finPDomType true} :=
  Functor (fun X => mono_finPDomType X.1 X.2)
          (fun X Y f =>
             Sub (Sub (mkmono (fun g => mono_comp f.2 (mono_comp g (mkmono (retract f.1) _))) _)
                      _) _)
          _ _.

Next Obligation.
by move=> ????; apply: retract_mono; [exact/finPDom_homB|exact/finDom_hom_lub].
Qed.

Next Obligation.
move=> [T1 T2] [S1 S2] [/= f1 f2] /= g1 g2 /fapprP g12.
apply/fapprP=> x; rewrite /= !ffunE /= !ffunE /= !ffunE /=.
by apply/(monoP f2)/g12.
Qed.

Next Obligation.
move=> [T1 T2] [S1 S2] [/= f1 f2] /=; apply/andP; split.
- apply/injectiveP=> g1 g2; rewrite !ffunE /=.
  move/(congr1 val)/ffunP=> g12; apply/val_inj/ffunP=> x.
  move/(_ (f1 x)): g12; rewrite /= !ffunE /= !ffunE /= !ffunE /=.
  move/finDom_hom_inj; rewrite retractK //.
  + exact: finDom_hom_lub.
  + exact: finDom_hom_inj.
- apply/lub_preservingP=> g1 g2; rewrite /= !ffunE.
  case e12: (g1 ⊔ g2)=> [g12|] /=.
  + apply/mono_lub_Coh=> x; rewrite /= !ffunE /= !ffunE /= !ffunE /=.
    by rewrite finDom_hom_lub; move/mono_lub_Coh: e12=> ->.
  + move/mono_lub_Incoh: e12=> [x xE].
    apply/mono_lub_Incoh; exists (f1 x).
    do ![rewrite /= !ffunE /=]; rewrite finDom_hom_lub !retractK ?xE //.
    * exact: finDom_hom_lub.
    * exact: finDom_hom_inj.
Qed.

Next Obligation.
move=> [T1 T2] [S1 S2] [/= f1 f2]; apply/eqP/val_inj/ffunP=> x.
by do ![rewrite /= !ffunE /=]; rewrite finPDom_homB.
Qed.

Next Obligation.
move=> [T1 T2] /=; apply/val_inj/val_inj/val_inj/ffunP=> f /=.
apply/val_inj/ffunP=> x; do ![rewrite /= !ffunE /=].
rewrite {1}(_ : x = [ffun x => x] x); try by rewrite ffunE.
rewrite -{1}[x]/(proj_elt (Sub x (in_projT x))) retractK //.
- by move=> ??; rewrite !ffunE /=; case: lub=> //= ?; rewrite ffunE.
- by move=> ??; rewrite !ffunE.
Qed.

Next Obligation.
move=> [T1 T2] [S1 S2] [R1 R2] [/= g1 g2] [/= f1 f2].
apply/val_inj/val_inj/val_inj/ffunP=> h /=.
do ![rewrite /= !ffunE /=]; apply/val_inj/ffunP=> x /=.
do ![rewrite /= !ffunE /=]; congr (g2 (f2 (h _))).
rewrite (eq_retract (ffunE _)) retract_comp //;
do 1?[apply/finPDom_homB|apply/finDom_hom_inj|apply/finDom_hom_lub].
Qed.

Program Definition projF :
  {functor finPDomType true -> finPDomType true} :=
  Functor proj_finPDomType
          (fun X Y f =>
             Sub (Sub (mkmono (mapp f) _) _) _)
          _ _.

Next Obligation.
by move=> T S f X Y XY; apply/lub_closureS/imfsetS.
Qed.

Next Obligation.
move=> T S f /=; apply/andP; split.
  apply/injectiveP=> X Y; rewrite !ffunE; move=> /(congr1 val).
  do 2![rewrite val_mapp; do 1?[apply/finPDom_homB|apply/finDom_hom_lub]].
  by move=> /(@imfset_inj _ _ _ (@finDom_hom_inj _ _ f)) /val_inj.
apply/lub_preservingP=> X Y; rewrite !ffunE /lub /= ffunE /=; congr Coh.
have mappP_f := @mappP _ _ _ _ _ (finPDom_homB f) (@finDom_hom_lub _ _ f).
have mem_mapp_f :=
  @mem_mapp _ _ _ _ _ (@finDom_hom_inj _ _ f) (finPDom_homB f) (@finDom_hom_lub _ _ f).
apply/eq_proj=> x; apply/(sameP idP)/(iffP idP).
- case/mappP_f=> {x} x /projUP [x1 [x2 [x1P x2P xE]]] ->.
  apply/projUP; exists (f x1), (f x2).
  by split; rewrite ?mem_mapp_f ?finDom_hom_lub ?xE.
- case/projUP=> [x1 [x2 [x1P x2P]]].
  case/mappP_f: x1P=> {x1} x1 x1P ->; case/mappP_f: x2P=> {x2} x2 x2P ->.
  rewrite finDom_hom_lub; case xE: (x1 ⊔ x2)=> {x} [x|] // [<-].
  by rewrite mem_mapp_f; apply/projUP; exists x1, x2; split.
Qed.

Next Obligation.
move=> T S f /=; apply/eqP; rewrite ffunE; apply/val_inj; rewrite /=.
by rewrite lub_closure0 imfset1 finPDom_homB -[RHS]lub_closure_idem lub_closure0.
Qed.

Next Obligation.
move=> T /=; apply/val_inj/val_inj/val_inj/ffunP=> X /=.
by rewrite !ffunE (eq_mapp (ffunE (fun x : T => x))) mapp_id.
Qed.

Next Obligation.
move=> T S R g f /=; apply/val_inj/val_inj/val_inj/ffunP=> X /=.
do ![rewrite /= !ffunE /=]; rewrite (eq_mapp (ffunE (g \o f))).
by apply: mapp_comp; do 1?[exact/finDom_hom_lub|exact/finPDom_homB].
Qed.

Section FinPDomColim.

Variables (I : latType) (F : {functor I -> finPDomType true}).

Record precolim := PreColim_ { tagged_of_precolim :> {i & F i} }.

Definition PreColim (i : I) (x : F i) := PreColim_ (Tagged (fun i => F i) x).
Arguments PreColim : clear implicits.

Canonical precolim_subType :=
  Eval hnf in [newType for tagged_of_precolim].
Canonical precolim_eqType :=
  Eval hnf in EqType precolim [eqMixin of precolim by <:].
Canonical precolim_choiceType :=
  Eval hnf in ChoiceType precolim [choiceMixin of precolim by <:].
Canonical precolim_ordType :=
  Eval hnf in OrdType precolim [ordMixin of precolim by <:].

Implicit Types x y z : precolim.

Definition precolim_appr x y :=
  fmap F (join_apprl (tag x) (tag y)) (tagged x)
  ⊑ fmap F (join_apprr (tag x) (tag y)) (tagged y).

Lemma precolim_apprE x y i (ex : tag x ⊑ i) (ey : tag y ⊑ i) :
  precolim_appr x y =
  fmap F ex (tagged x) ⊑ fmap F ey (tagged y).
Proof.
rewrite /precolim_appr.
have exy : tag x ∨ tag y ⊑ i by rewrite appr_join ex ey.
rewrite -(finDom_hom_iso (fmap F exy)) -!finPDom_compE -!fmapD.
congr (fmap F _ (tagged x) ⊑ fmap F _ (tagged y)); exact: eq_irrelevance.
Qed.

Lemma precolim_apprP : Po.axioms_of false precolim_appr.
Proof.
split=> [x|y x z|//].
  by rewrite (precolim_apprE (apprxx (tag x)) (apprxx (tag x))) apprxx.
have xi : tag x ⊑ tag x ∨ tag y ∨ tag z.
  by rewrite -joinA join_apprl.
have yi : tag y ⊑ tag x ∨ tag y ∨ tag z.
  by rewrite (appr_trans (join_apprr (tag x) (tag y))) // join_apprl.
have zi : tag z ⊑ tag x ∨ tag y ∨ tag z by rewrite join_apprr.
rewrite (precolim_apprE xi yi) (precolim_apprE yi zi) (precolim_apprE xi zi).
exact: appr_trans.
Qed.

Definition precolim_poMixin := PoMixin precolim_apprP.
Canonical precolim_poType :=
  Eval hnf in PoType precolim precolim_poMixin.

Lemma precolim_botP x : PreColim ⊥ ⊥ ⊑ x.
Proof.
rewrite /appr /=.
rewrite (@precolim_apprE (PreColim ⊥ ⊥) x _ (botP (tag x)) (apprxx (tag x))).
by rewrite (eqP (valP (fmap F (botP (tag x))))) botP.
Qed.

Definition precolim_ppoMixin := PPoMixin precolim_botP.
Canonical precolim_ppoType := Eval hnf in PPoType precolim precolim_ppoMixin.

Definition precolim_lub x y : coh precolim :=
  let xx := fmap F (join_apprl (tag x) (tag y)) (tagged x) in
  let yy := fmap F (join_apprr (tag x) (tag y)) (tagged y) in
  if xx ⊔ yy is Coh zz then Coh (PreColim _ zz) else Incoh.

Lemma precolim_lubE x y i (xi : tag x ⊑ i) (yi : tag y ⊑ i) :
  if fmap F xi (tagged x) ⊔ fmap F yi (tagged y) is Coh zz then
    exists z (zi : tag z ⊑ i),
      precolim_lub x y = Coh z /\
      zz = fmap F zi (tagged z)
  else precolim_lub x y = Incoh.
Proof.
rewrite /precolim_lub.
have zi : tag x ∨ tag y ⊑ i by rewrite appr_join xi yi.
rewrite (eq_irrelevance xi (appr_trans (join_apprl _ _) zi)).
rewrite (eq_irrelevance yi (appr_trans (join_apprr _ _) zi)).
rewrite !fmapD !finDom_compE finDom_hom_lub.
by case: lub=> // zz; exists (PreColim _ zz), zi; split.
Qed.

Lemma precolim_lub_appr x y z :
  precolim_lub x y ⊑ Coh z = (x ⊑ z) && (y ⊑ z).
Proof.
have xi : tag x ⊑ tag x ∨ tag y ∨ tag z.
  by rewrite -joinA join_apprl.
have yi : tag y ⊑ tag x ∨ tag y ∨ tag z.
  by rewrite (appr_trans (join_apprr (tag x) (tag y))) // join_apprl.
have zi : tag z ⊑ tag x ∨ tag y ∨ tag z by rewrite join_apprr.
rewrite [x ⊑ z](precolim_apprE xi zi) [y ⊑ z](precolim_apprE yi zi).
rewrite -lub_appr; move: (precolim_lubE xi yi); case: lub=> [|-> //].
move=> _ [xy [xyi [-> ->]]].
by rewrite [Coh xy ⊑ Coh z](precolim_apprE xyi zi).
Qed.

Definition precolim_domMixin := DomMixin precolim_lub_appr.
Canonical precolim_domType :=
  Eval hnf in DomType precolim precolim_domMixin.
Canonical precolim_pdomType := Eval hnf in PDomType precolim.

Record colim := Colim_ { quot_of_colim : {quot_po precolim} }.

Canonical colim_subType := Eval hnf in [newType for quot_of_colim].
Canonical colim_eqType :=
  Eval hnf in EqType colim [eqMixin of colim by <:].
Canonical colim_choiceType :=
  Eval hnf in ChoiceType colim [choiceMixin of colim by <:].
Canonical colim_ordType :=
  Eval hnf in OrdType colim [ordMixin of colim by <:].
Canonical colim_poType :=
  Eval hnf in PoType colim [poMixin of colim by <:].
Canonical colim_subPoType :=
  Eval hnf in SubPoType colim (fun _ _ => erefl).
Canonical colim_ppoType :=
  Eval hnf in PPoType colim [ppoMixin of colim by <: using erefl].
Canonical colim_domType :=
  Eval hnf in DomType colim [domMixin of colim by <:
                               using (fun _ _ _ _ => erefl)].
Canonical colim_pdomType :=
  Eval hnf in PDomType colim.

Definition Colim (i : I) (x : F i) : colim :=
  Colim_ (\pi (PreColim i x)).

Arguments Colim : clear implicits.

Lemma colimP (P : colim -> Type) :
  (forall i (x : F i), P (Colim i x)) ->
  forall x : colim, P x.
Proof.
move=> H [x]; elim/quotP: x=> y <- /=.
rewrite reprK; case: y=> [[i y]] /=.
exact: (H i y).
Qed.

Lemma colim_apprE i j (x : F i) (y : F j) k (ik : i ⊑ k) (jk : j ⊑ k) :
  Colim i x ⊑ Colim j y = fmap F ik x ⊑ fmap F jk y.
Proof.
rewrite {1}/appr /= /sub_appr /= qapprE.
by rewrite {1}/appr /= (@precolim_apprE (PreColim i x) (PreColim j y) _ ik jk).
Qed.

Lemma colim_apprP i j (x : F i) (y : F j) :
  reflect (exists k (xi : i ⊑ k) (yi : j ⊑ k), fmap F xi x ⊑ fmap F yi y)
          (Colim i x ⊑ Colim j y).
Proof.
apply/(iffP idP); last by case=> k [a [b e]]; rewrite (colim_apprE _ _ a b).
rewrite {1}/appr /= /sub_appr /= qapprE.
pose xi := join_apprl i j; pose yi := join_apprr i j.
rewrite {1}/appr /= (@precolim_apprE (PreColim i x) (PreColim j y) _ xi yi).
by move=> e; exists (i ∨ j), xi, yi.
Qed.

Lemma eq_colim i j (x : F i) (y : F j) :
  (exists k (xi : i ⊑ k) (yi : j ⊑ k), fmap F xi x = fmap F yi y) <->
  Colim i x = Colim j y.
Proof.
split.
- by case=> k [xi [yi e]]; apply/appr_anti/andP; split;
  apply/colim_apprP; [exists k, xi, yi|exists k, yi, xi];
  rewrite e apprxx.
- case=> /eqP; rewrite piE /po_eq /= /appr /=.
  pose xi := join_apprl i j; pose yi := join_apprr i j.
  rewrite (@precolim_apprE (PreColim i x) (PreColim j y) _ xi yi).
  rewrite (@precolim_apprE (PreColim j y) (PreColim i x) _ yi xi) /=.
  by move=> /appr_anti e; exists (i ∨ j), xi, yi.
Qed.

Definition colim_tag (x : colim) : I :=
  tag (repr (val x)).

Definition colim_val (x : colim) : F (colim_tag x) :=
  tagged (repr (val x)).

Lemma Colim_fmap i j (ij : i ⊑ j) (x : F i) :
  Colim j (fmap F ij x) = Colim i x.
Proof.
apply/eq_colim; exists j, (apprxx j), ij.
by rewrite (eq_irrelevance (apprxx j) (1 : hom j j)) fmap1 finDom_idE.
Qed.

Lemma colim_valK (x : colim) : Colim _ (colim_val x) = x.
Proof.
case: x=> x; rewrite /Colim /colim_val /colim_tag /= /PreColim.
elim/quotP: x=> /= - [x] -> /=.
by congr (Colim_ (\pi (PreColim_ _))); case: x.
Qed.

Lemma ColimB (i : I) : Colim i ⊥ = ⊥.
Proof.
apply/eq_colim; exists i, (apprxx i), (botP i).
by rewrite !(eqP (valP (fmap F _))).
Qed.

Lemma Colim_inj (i : I) : injective (Colim i).
Proof.
move=> x y /eq_colim; case=> k [xi [yi]].
by rewrite (eq_irrelevance xi yi) => /finDom_hom_inj.
Qed.

Lemma Colim_lub (i : I) : lub_preserving (Colim i).
Proof.
move=> x y; apply/esym/lub_unique; case=> [z|] //=.
elim/colimP: z=> j z.
pose ik := join_apprl i j; pose jk := join_apprr i j.
rewrite ![Coh _ ⊑ _](colim_apprE _ _ ik jk) -lub_appr finDom_hom_lub.
by case: (x ⊔ y)=> [xy|] //=; rewrite [Coh _ ⊑ _](colim_apprE _ _ ik jk).
Qed.

Definition colim_proj_tag (X : {proj colim}) : I :=
  foldr (fun (x : colim) j => tag (repr (val x)) ∨ j) ⊥ X.

Lemma colim_proj_tagP (X : {proj colim}) (x : X) :
  colim_tag (val x) ⊑ colim_proj_tag X.
Proof.
case: x=> [x]; rewrite /= inE inE /= /colim_proj_tag.
elim: (val (val X))=> [|y ys IH] //=.
rewrite inE; case/orP=> [/eqP ->|x_ys]; first exact: join_apprl.
apply: appr_trans (IH x_ys) _; apply: join_apprr.
Qed.

Definition colim_proj_inv (X : {proj colim}) (x : X) : F (colim_proj_tag X) :=
  fmap F (colim_proj_tagP x) (colim_val (val x)).

Lemma colim_proj_invK (X : {proj colim}) (x : X) :
  Colim _ (colim_proj_inv x) = val x.
Proof. by rewrite /colim_proj_inv Colim_fmap colim_valK. Qed.

Lemma colim_proj_invB (X : {proj colim}) : @colim_proj_inv X ⊥ = ⊥.
Proof.
apply: (@Colim_inj (colim_proj_tag X)).
by rewrite colim_proj_invK ColimB.
Qed.

Lemma colim_proj_inv_lub (X : {proj colim}) :
  lub_preserving (@colim_proj_inv X).
Proof.
move=> /= x y; move: (Colim_lub (colim_proj_inv x) (colim_proj_inv y)).
rewrite !colim_proj_invK lub_val.
case: (x ⊔ y) (colim_proj_inv x ⊔ _ y) => [xy|] [fxy|] //= [e].
congr Coh; apply: (@Colim_inj (colim_proj_tag X)).
by rewrite -e colim_proj_invK.
Qed.

Lemma proj_colimP (X : {proj colim}) :
  exists (Y : {proj F (colim_proj_tag X)}), X = mapp (Colim _) Y.
Proof.
have m1 := mappP _ _ (ColimB (colim_proj_tag X)) (@Colim_lub (colim_proj_tag X)).
have m2 := mappP _ _ (colim_proj_invB X) (@colim_proj_inv_lub X).
exists (mapp (@colim_proj_inv X) projT); apply/eq_proj=> /= x.
apply/(sameP idP)/(iffP idP).
- case/m1=> {x} x xP ->; case/m2: xP=> {x} x xP ->.
  by rewrite colim_proj_invK (valP x).
- move=> x_X; apply/m1.
  exists (colim_proj_inv (Sub x x_X)); last by rewrite colim_proj_invK.
  apply/m2; exists (Sub x x_X)=> //; exact: in_projT.
Qed.

End FinPDomColim.

Section Casts.

Variable (T : Type).
Implicit Types (x y z : T).

Definition cast (P : T -> Type) x y (e : x = y) : P x -> P y :=
  match e with erefl => id end.

Lemma castD (P : T -> Type) x y z (p : x = y) (q : y = z) (a : P x) :
  cast q (cast p a) = cast (etrans p q) a.
Proof. by case: z / q=> /=. Qed.

End Casts.

Arguments cast {T} P {x y} e.

Definition castK (T P : Type) (x y : T) (p : x = y) : cast (fun _ => P) p = id :=
  match p with erefl => erefl end.

Definition sapp_cast T S (P : T -> S -> Type) x1 x2 y (p : x1 = x2) :
  forall (f : forall y, P x1 y),
    cast (fun x => forall y, P x y) p f y = cast (fun x => P x y) p (f y) :=
  match p with erefl => fun _ => erefl end.

Definition cast_sapp T (S R : T -> Type) x1 x2 (p : x1 = x2) :
  forall (f : forall x, S x -> R x) (a : S x1),
  f x2 (cast S p a) = cast R p (f x1 a) :=
  match p with erefl => fun _ _ => erefl end.

Definition dapp_cast T (P : T -> Type) (Q : forall x, P x -> Type) x y
  (p : x = y) :
  forall (f : forall a : P x, Q x a) (a : P y),
  cast (fun x => forall a : P x, Q x a) p f a =
  match esym p as q in _ = z return Q z (cast P q a) -> Q y a with
  | erefl => id
  end (f (cast P (esym p) a)) :=
  match p with
  | erefl => fun _ _ => erefl
  end.

Definition cast_congr1 T (P : T -> Type) x y (p : x = y) :
  forall (a : P x), cast P p a = cast id (congr1 P p) a :=
  match p with erefl => fun a => erefl end.

Definition eq_tagged (I : Type) (T_ : I -> Type) (x y : {i : I & T_ i}) (e : x = y) :
  cast T_ (congr1 tag e) (tagged x) = tagged y :=
  match e with
  | erefl => erefl
  end.

Lemma eq_Tagged (I : Type) (T_ : I -> Type) (x y : {i : I & T_ i}) :
  forall (p : tag x = tag y),
    cast T_ p (tagged x) = tagged y ->
    x = y.
Proof.
by case: x y=> [i xi] [j yj] /= p; case: j / p yj => yj /= <-.
Qed.

Section IsoOfEq.

Variable C : catType.

Implicit Types X Y Z : C.

Definition iso_of_eq X Y (e : X = Y) : hom X Y :=
  match e with erefl => cat_id _ end.

Lemma iso_of_eqK X Y (e : X = Y) : iso_of_eq e ∘ iso_of_eq (esym e) = 1.
Proof. by case: Y / e; rewrite comp1f. Qed.

Lemma iso_of_eqKV X Y (e : X = Y) : iso_of_eq (esym e) ∘ iso_of_eq e = 1.
Proof. by case: Y / e; rewrite comp1f. Qed.

Lemma iso_of_eqD X Y Z (e1 : Y = Z) (e2 : X = Y) :
  iso_of_eq (etrans e2 e1) = iso_of_eq e1 ∘ iso_of_eq e2.
Proof. by case: Z / e1 e2 => e2; rewrite /= comp1f. Qed.

End IsoOfEq.

Section NatFunctor.

Variables (C : catType) (X : nat -> C) (f : forall i, hom (X i) (X i.+1)).

Fixpoint chain_map_def n m : hom (X n) (X (m + n)) :=
  match m with
  | 0    => 1
  | m.+1 => f (m + n) ∘ chain_map_def n m
  end.

(*Lemma chain_map_defSn n m :
  chain_map_def n m.+1 =
  iso_of_eq (congr1 X (addnS _ _)) ∘ chain_map_def n.+1 m ∘ f n.
Proof.


elim: m=> [|m IH] /=; first by rewrite eq_axiomK /= compf1.
rewrite compA IH /= -[LHS]compA -[RHS]compA; congr comp.
move: (addnS m n) (addnS m.+1 n); rewrite -![_.+1 + _]/((_ + _).+1).
(* FIXME: Why is this rewrite needed? *)
rewrite -![m.+2 + _]/((_ + _).+2).
move: (m + n.+1) (m + n).+1=> a b q.
by case: b / q=> q /=; rewrite !eq_axiomK /= comp1f compf1.
Qed.
*)

Fact chain_map_key : unit. Proof. exact: tt. Qed.

Definition chain_map n m (nm : n <= m) : hom (X n) (X m) :=
  locked_with
    chain_map_key
    (iso_of_eq (congr1 X (subnK nm)) ∘ chain_map_def _ _).

Lemma chain_mapS n m (nm : n <= m) (nm1 : n <= m.+1) :
  chain_map nm1 = f m ∘ chain_map nm.
Proof.
rewrite /chain_map !unlock.
move: (subnK nm) (subnK nm1); rewrite (subSn nm) /=.
move: {nm nm1} (m - n)=> o; rewrite -[o.+1 + n]/(o + n).+1 => e.
by case: m / e => ?; rewrite eq_axiomK /= !comp1f.
Qed.

Lemma chain_map0 n (nn : n <= n) : chain_map nn = 1.
Proof.
rewrite /chain_map unlock; move: (subnK nn); rewrite subnn=> e.
by rewrite eq_axiomK /= comp1f.
Qed.

Lemma chain_map1 n (nSn : n <= n.+1) : chain_map nSn = f n.
Proof. by rewrite (chain_mapS (leqnn n) nSn) chain_map0 compf1. Qed.

Lemma chain_mapD n m o (nm : n <= m) (mo : m <= o) :
  chain_map (@appr_trans _ _ m _ _ nm mo) = chain_map mo ∘ chain_map nm.
Proof.
move: (mo) (appr_trans _ _); rewrite -(subnK mo) {mo}.
elim: (o - m)=> {o} [|o IH] /=.
  move=> mo no; rewrite /chain_map !unlock; move: (subnK mo).
  rewrite -![0 + m]/(m) subnn => {mo} mo; rewrite eq_axiomK /= compf1.
  by rewrite (eq_irrelevance no nm) comp1f.
rewrite -![o.+1 + _]/(o + _).+1 => mo no.
rewrite (chain_mapS (leq_trans nm (leq_addl o m)) no).
rewrite (IH (leq_addl o m) (leq_trans nm (leq_addl o m))).
by rewrite (chain_mapS (leq_addl o m) mo) compA.
Qed.

Definition chain : {functor nat -> C} :=
  @Functor _ _ X chain_map
           (fun n => chain_map0 (apprxx n))
           (fun n m p f g => chain_mapD g f).

Lemma chain_coneP Y (g : forall n, hom (X n) Y) :
  (forall n, g n = g n.+1 ∘ f n) ->
  forall n m (nm : n <= m), g n = g m ∘ chain_map nm.
Proof.
move=> /= gP n m nm; rewrite /chain_map !unlock.
move: (m - n) (subnK nm)=> p e; case: m / e {nm}; rewrite comp1f.
elim: p=> [|p IH] /=; first by rewrite compf1.
by rewrite IH gP compA.
Qed.

End NatFunctor.

Delimit Scope functor_scope with F.

Notation "⟨ f , g , .. , h ⟩" :=
  (tupleF .. (tupleF f g) .. h)
  (format "⟨ f ,  g ,  .. ,  h ⟩") : functor_scope.

Notation "f + g" := (compF sumF ⟨f, g⟩%F) : functor_scope.

Notation "f * g" := (compF prodF ⟨f, g⟩%F) : functor_scope.

Notation "{ 'proj' f }" := (compF projF f) : functor_scope.

Notation "f -> g" := (compF monoF ⟨f,g⟩%F) : functor_scope.

Notation "{ 'forget' f }" := (compF forgetF f) : functor_scope.

Notation "'X" := idF : functor_scope.

Section Recursive.

Variable F : {functor finPDomType true -> finPDomType true}.

Definition muX n := iter n F unit_finPDomType.

Fixpoint muF n : hom (muX n) (muX n.+1) :=
  match n with
  | 0 => finPDom_bot
  | n.+1 => fmap F (muF n)
  end.

Definition mu := colim (@chain _ muX muF).

End Recursive.

Section Universal.

Definition univF : {functor finPDomType true -> finPDomType true} :=
  compF optionF ({forget {proj 'X}} +
                 {forget 'X -> 'X} +
                 {forget 'X * 'X} +
                 ({forget 'X} + {forget 'X}) +
                 constF _ unit_finDomType)%F.

Definition univ := mu univF.



Lemma down_comp
  (C D : catType@{i j}) (X : nat -> C) (f : forall n, C (X n.+1) (X n))
  (G : {functor C -> D}) n m (nm : n <= m) :
  fmap G (down f nm) = down (fun n => fmap G (f n)) nm.
Proof.
move: (nm); rewrite -(subnK nm); elim: (m - n)=> {m nm} [|m IH].
  by move=> ?; rewrite !down0 fmap1.
change (m.+1 + n) with (m + n).+1 => nm.
by rewrite !(downS _ (leq_addl m n)) fmapD IH.
Qed.

Lemma down_comp_cone
  (C D : catType@{i j}) (X : nat -> C) (f : forall n, C (X n.+1) (X n))
  Y (g : forall n, C Y (X n)) (gP : forall n, g n = f n ∘ g n.+1)
  (F : {functor C -> D}) :
  forall n, fmap F (g n) = fmap F (f n) ∘ fmap F (g n.+1).
Proof. by move=> n; rewrite -fmapD gP. Qed.

Arguments down_comp_cone {_ _ _} _ {_} _ _ _ _.


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
