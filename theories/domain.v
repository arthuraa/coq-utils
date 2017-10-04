From mathcomp
Require Import ssreflect ssrfun ssrbool ssrnat seq eqtype choice fintype.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Delimit Scope dom_scope with dom.

Reserved Notation "x ⊑ y" (at level 50, no associativity).
Reserved Notation "x ⊑ y ⊑ z" (at level 50, y at next level, no associativity).
Reserved Notation "x ⊔ y" (at level 40, left associativity).

Module Dom.

Section ClassDef.

Record mixin_of T := Mixin {
  approx : rel T;
  merge : T -> T -> T;
  _ : reflexive approx;
  _ : transitive approx;
  _ : antisymmetric approx;
  _ : forall x y, approx x (merge x y);
  _ : forall x y z,
        (approx y (merge x y) && approx (merge x y) z)
        = (approx x z && approx y z)
}.

Record class_of T := Class {base : Countable.class_of T; mixin : mixin_of T}.
Local Coercion base : class_of >->  Countable.class_of.

Structure type := Pack {sort; _ : class_of sort; _ : Type}.
Local Coercion sort : type >-> Sortclass.
Variables (T : Type) (cT : type).
Definition class := let: Pack _ c _ as cT' := cT return class_of cT' in c.
Definition clone c of phant_id class c := @Pack T c T.
Let xT := let: Pack T _ _ := cT in T.
Notation xclass := (class : class_of xT).

Definition pack m :=
  fun b bT & phant_id (Countable.class bT) b => Pack (@Class T b m) T.

(* Inheritance *)
Definition eqType := @Equality.Pack cT xclass xT.
Definition choiceType := @Choice.Pack cT xclass xT.
Definition countType := @Countable.Pack cT xclass xT.

End ClassDef.

Module Import Exports.
Coercion base : class_of >-> Countable.class_of.
Coercion mixin : class_of >-> mixin_of.
Coercion sort : type >-> Sortclass.
Coercion eqType : type >-> Equality.type.
Canonical eqType.
Coercion choiceType : type >-> Choice.type.
Canonical choiceType.
Coercion countType : type >-> Countable.type.
Canonical countType.
Notation domType := type.
Notation domMixin := mixin_of.
Notation DomMixin := Mixin.
Notation DomType T m := (@pack T m _ _ id).
Notation "[ 'domType' 'of' T 'for' cT ]" :=  (@clone T cT _ idfun)
  (at level 0, format "[ 'domType'  'of'  T  'for'  cT ]") : form_scope.
Notation "[ 'domType' 'of' T ]" := (@clone T _ _ id)
  (at level 0, format "[ 'domType'  'of'  T ]") : form_scope.
End Exports.

End Dom.

Export Dom.Exports.

Definition approx T := Dom.approx (Dom.class T).
Definition merge T := Dom.merge (Dom.class T).

Notation "x ⊑ y" := (approx x y) : dom_scope.
Notation "x ⊑ y ⊑ z" := (approx x y && approx y z) : dom_scope.
Notation "x ⊔ y" := (merge x y) : dom_scope.

Local Open Scope dom_scope.

Section Theory.

Variable (T : domType).
Implicit Types (x y : T).

Lemma approx_refl : reflexive (@approx T).
Proof. by case: T => [? [? []]]. Qed.

Lemma approx_trans : transitive (@approx T).
Proof. by case: T => [? [? []]]. Qed.

Lemma anti_approx : antisymmetric (@approx T).
Proof. by case: T => [? [? []]]. Qed.

Lemma approx_mergel x y : x ⊑ x ⊔ y.
Proof. by case: T x y => [? [? []]]. Qed.

Lemma merge_lub x y z : y ⊑ x ⊔ y ⊑ z = (x ⊑ z) && (y ⊑ z).
Proof. by case: T x y z=> [? [? []]]. Qed.

Lemma approx_merger x y z : x ⊑ z -> y ⊑ z -> y ⊑ x ⊔ y.
Proof.
move=> xz yz; have := merge_lub x y z; rewrite xz yz.
by case/andP.
Qed.

Lemma mergeC x y z : x ⊑ z -> y ⊑ z -> x ⊔ y = y ⊔ x.
Proof.
move=> xz yz; move: (merge_lub x y z) (merge_lub y x z).
rewrite xz yz; case/andP=> yxy _; case/andP=> xyx _.
apply: anti_approx.
move: (merge_lub x y (y ⊔ x)) (merge_lub y x (x ⊔ y)).
by rewrite yxy xyx !approx_mergel /= => -> ->.
Qed.

Lemma mergeC' x y : y ⊑ x ⊔ y -> x ⊔ y = y ⊔ x.
Proof. by apply: mergeC; rewrite approx_mergel. Qed.

End Theory.

Module Discrete.

Section ClassDef.

Record mixin_of (T : domType) := Mixin {
  _ : forall x y : T, x ⊑ y = (x == y)
}.

Section Mixins.

Variable T : countType.
Implicit Types x y : T.

Definition dapprox x y := (x == y).
Definition dmerge x y := x.

Lemma dapprox_refl : reflexive dapprox.
Proof. exact: eqxx. Qed.
Lemma dapprox_trans : transitive dapprox.
Proof. by move=> ??? /eqP ->. Qed.
Lemma anti_dapprox : antisymmetric dapprox.
Proof. by move=> x y /andP [/eqP ->]. Qed.
Lemma dapprox_mergel x y : dapprox x (dmerge x y).
Proof. exact: eqxx. Qed.
Lemma dmerge_lub x y z :
  (dapprox y (dmerge x y) && dapprox (dmerge x y) z)
  = (dapprox x z && dapprox y z).
Proof.
rewrite /dapprox /dmerge.
by case: (x =P z) => [->|_]; rewrite (andbF, andbT).
Qed.

Definition DefDomMixin :=
  DomMixin dapprox_refl dapprox_trans anti_dapprox dapprox_mergel dmerge_lub.

Definition DefMixin :=
  @Mixin (DomType T DefDomMixin) (fun _ _ => erefl).

End Mixins.

Record class_of T :=
  Class {base : Dom.class_of T; mixin : mixin_of (Dom.Pack base T)}.
Local Coercion base : class_of >-> Dom.class_of.

Structure type := Pack {sort; _ : class_of sort; _ : Type}.
Local Coercion sort : type >-> Sortclass.
Variables (T : Type) (cT : type).
Definition class := let: Pack _ c _ as cT' := cT return class_of cT' in c.
Definition clone c of phant_id class c := @Pack T c T.
Let xT := let: Pack T _ _ := cT in T.
Notation xclass := (class : class_of xT).

Definition pack b0 (m0 : mixin_of (@Dom.Pack T b0 T)) :=
  fun bT b & phant_id (Dom.class bT) b =>
  fun    m & phant_id m0 m => Pack (@Class T b m) T.

(* Inheritance *)
Definition eqType := @Equality.Pack cT xclass xT.
Definition choiceType := @Choice.Pack cT xclass xT.
Definition countType := @Countable.Pack cT xclass xT.
Definition domType := @Dom.Pack cT xclass xT.

End ClassDef.

Module Import Exports.
Coercion base : class_of >-> Dom.class_of.
Coercion mixin : class_of >-> mixin_of.
Coercion sort : type >-> Sortclass.
Coercion eqType : type >-> Equality.type.
Canonical eqType.
Coercion choiceType : type >-> Choice.type.
Canonical choiceType.
Coercion countType : type >-> Countable.type.
Canonical countType.
Coercion domType : type >-> Dom.type.
Canonical domType.
Notation discDomType := type.
Notation discDomMixin := mixin_of.
Notation DiscDomMixin := Mixin.
Notation DiscDomType T m := (@pack T _ m _ _ id _ id).
Notation "[ 'domType' 'for' T 'by' // ]" :=
  (DomType T (DefDomMixin [countType of T]))
  (at level 0, format "[ 'domType'  'for'  T  'by'  // ]")
  : form_scope.
Notation "[ 'discDomType' 'for' T ]" :=
  (DiscDomType T (@DiscDomMixin [domType of T] (fun _ _ => erefl)))
  (at level 0, format "[ 'discDomType'  'for'  T ]")
  : form_scope.
Notation "[ 'discDomType' 'of' T 'for' cT ]" :=  (@clone T cT _ idfun)
  (at level 0, format "[ 'discDomType'  'of'  T  'for'  cT ]")
  : form_scope.
Notation "[ 'discDomType' 'of' T ]" := (@clone T _ _ id)
  (at level 0, format "[ 'discDomType'  'of'  T ]") : form_scope.
End Exports.

End Discrete.

Export Discrete.Exports.

Canonical nat_domType := [domType for nat by //].
Canonical nat_discDomMixin := [discDomType for nat].

Canonical bool_domType := [domType for bool by //].
Canonical bool_discDomType := [discDomType for bool].

Section DiscreteTheory.

Variable T : discDomType.
Implicit Types x y : T.

Lemma approxD x y : x ⊑ y = (x == y).
Proof. by case: T x y => [? [? []]]. Qed.

Lemma mergeD x y : x ⊔ y = x.
Proof. by move: (approx_mergel x y); rewrite approxD => /eqP <-. Qed.

End DiscreteTheory.

Section Lifting.

Variable T : domType.
Implicit Types x y : option T.

Definition oapprox x y :=
  match x, y with
  | Some x, Some y => x ⊑ y
  | Some _, _      => false
  | None  , _      => true
  end.

Definition omerge x y :=
  match x, y with
  | Some x, Some y => Some (x ⊔ y)
  | Some _, _      => x
  | None  , _      => y
  end.

Lemma oapprox_refl : reflexive oapprox.
Proof. by case=> [x|] //=; rewrite approx_refl. Qed.
Lemma oapprox_trans : transitive oapprox.
Proof. case=> [z|] [x|] [y|] //=; exact: approx_trans. Qed.
Lemma anti_oapprox : antisymmetric oapprox.
Proof. by case=> [x|] [y|] //= /anti_approx ->. Qed.
Lemma oapprox_mergel x y : oapprox x (omerge x y).
Proof.
by case: x y => [x|] [y|] //=; rewrite (approx_mergel, approx_refl).
Qed.
Lemma omerge_lub x y z :
  (oapprox y (omerge x y) && oapprox (omerge x y) z)
  = (oapprox x z && oapprox y z).
Proof.
by case: x y z => [x|] [y|] [z|] //=;
rewrite ?approx_refl ?merge_lub ?andbT ?andbF.
Qed.

Definition option_domMixin :=
  DomMixin oapprox_refl oapprox_trans anti_oapprox oapprox_mergel omerge_lub.
Canonical option_domType := Eval hnf in DomType (option T) option_domMixin.

End Lifting.
