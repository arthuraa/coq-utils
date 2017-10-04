From mathcomp
Require Import ssreflect ssrfun ssrbool ssrnat seq eqtype choice fintype.

Require Import ord fset.

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
  lub : T -> T -> option T;
  _ : forall x, lub x x = Some x;
  _ : commutative lub;
  _ : forall x y z, obind (lub^~ z) (lub x y) = obind (lub x) (lub y z)
}.

Record class_of T := Class {base : Ord.Total.class_of T; mixin : mixin_of T}.
Local Coercion base : class_of >-> Ord.Total.class_of.

Structure type := Pack {sort; _ : class_of sort; _ : Type}.
Local Coercion sort : type >-> Sortclass.
Variables (T : Type) (cT : type).
Definition class := let: Pack _ c _ as cT' := cT return class_of cT' in c.
Definition clone c of phant_id class c := @Pack T c T.
Let xT := let: Pack T _ _ := cT in T.
Notation xclass := (class : class_of xT).

Definition pack m :=
  fun b bT & phant_id (Ord.Total.class bT) b => Pack (@Class T b m) T.

(* Inheritance *)
Definition eqType := @Equality.Pack cT xclass xT.
Definition choiceType := @Choice.Pack cT xclass xT.
Definition ordType := @Ord.Total.Pack cT xclass xT.

End ClassDef.

Module Import Exports.
Coercion base : class_of >-> Ord.Total.class_of.
Coercion mixin : class_of >-> mixin_of.
Coercion sort : type >-> Sortclass.
Coercion eqType : type >-> Equality.type.
Canonical eqType.
Coercion choiceType : type >-> Choice.type.
Canonical choiceType.
Coercion ordType : type >-> Ord.Total.type.
Canonical ordType.
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

Definition lub T := Dom.lub (Dom.class T).
Notation "x ⊔ y" := (lub x y) : dom_scope.

Local Open Scope dom_scope.

Section Theory.

Variable (T : domType).
Implicit Types x y z : T.
Implicit Types xs ys zs : seq T.
Implicit Types P : pred T.

Lemma lubxx x : x ⊔ x = Some x.
Proof. by case: T x => [? [? []]]. Qed.

Lemma lubC : commutative (@lub T).
Proof. by case: T => [? [? []]]. Qed.

Lemma lubA x y z : obind ((@lub T)^~ z) (lub x y) = obind (lub x) (lub y z).
Proof. by case: T x y z => [? [? []]]. Qed.

Definition approx x y := x ⊔ y == Some y.

Notation "x ⊑ y" := (approx x y) : dom_scope.
Notation "x ⊑ y ⊑ z" := (approx x y && approx y z) : dom_scope.

Lemma approx_refl : reflexive approx.
Proof. by move=> x; rewrite /approx lubxx. Qed.
Lemma approx_trans : transitive approx.
Proof.
move=> y x z /eqP xy /eqP yz; rewrite /approx.
by move: (lubA x y z); rewrite xy yz /= -yz => ->.
Qed.
Lemma anti_approx : antisymmetric approx.
Proof.
move=> x y; rewrite /approx lubC.
by case/andP => /eqP -> /eqP [->].
Qed.

Definition is_ub x ys := all (approx^~ x) ys.
Definition is_lub x ys :=
  is_ub x ys /\ forall x', is_ub x' ys -> x ⊑ x'.

Lemma lub_approxL x y xy : x ⊔ y = Some xy -> x ⊑ xy.
Proof.
rewrite /approx => exy.
by move: (lubA x x y); rewrite exy lubxx /= -exy => <-.
Qed.

Lemma lub_approxR x y xy : x ⊔ y = Some xy -> y ⊑ xy.
Proof. by rewrite lubC; apply: lub_approxL. Qed.

Lemma lub_approx x y z :
  (x ⊑ z) && (y ⊑ z) = if x ⊔ y is Some xy then xy ⊑ z else false.
Proof.
apply/(sameP andP)/(iffP idP).
  case exy: (x ⊔ y) => [xy|] //= xy_z.
  by split; apply: approx_trans xy_z;
  rewrite (lub_approxL exy, lub_approxR exy).
case=> /eqP exz /eqP eyz.
move: (lubA x y z); rewrite eyz /= exz.
by case: (x ⊔ y) => [xy|] //= /eqP.
Qed.

Definition lubn xs : option T :=
  if xs is x :: xs' then
    foldl (fun ox x' => obind (fun x => lub x x') ox) (Some x) xs'
  else None.

Lemma lubnP xs y :
  ~~ nilp xs && all (approx^~ y) xs
  = if lubn xs is Some x then x ⊑ y else false.
Proof.
case: xs => [|x xs] //=.
elim: xs x => [|x' xs IH] x //=; first by rewrite andbT.
rewrite andbA lub_approx; case: (x ⊔ x') => [xx'|] //=.
by rewrite (_ : foldl _ _ _ = None) //; elim: xs {x IH}.
Qed.

End Theory.

Notation "x ⊑ y" := (approx x y) : dom_scope.
Notation "x ⊑ y ⊑ z" := (approx x y && approx y z) : dom_scope.

Module Discrete.

Section ClassDef.

Record mixin_of (T : domType) := Mixin {
  _ : forall x y : T, x ⊔ y = if x == y then Some x else None
}.

Section Mixins.

Variable T : ordType.
Implicit Types x y : T.

Definition dlub x y := if x == y then Some x else None.

Lemma dlubxx x : dlub x x = Some x.
Proof. by rewrite /dlub eqxx. Qed.

Lemma dlubC : commutative dlub.
Proof.
by move=> x y; rewrite /dlub eq_sym; case: eqP=> // ->.
Qed.

Lemma dlubA x y z : obind (dlub^~ z) (dlub x y) = obind (dlub x) (dlub y z).
Proof.
rewrite /dlub; have [->|ne] /= := altP (x =P y).
  by case: eqP => //=; rewrite eqxx.
by case: eqP => //=; rewrite (negbTE ne).
Qed.

Definition DefDomMixin := DomMixin dlubxx dlubC dlubA.
Program Definition DefMixin :=
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
Definition ordType := @Ord.Total.Pack cT xclass xT.
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
Coercion ordType : type >-> Ord.Total.type.
Canonical ordType.
Coercion domType : type >-> Dom.type.
Canonical domType.
Notation discDomType := type.
Notation discDomMixin := mixin_of.
Notation DiscDomMixin := Mixin.
Notation DiscDomType T m := (@pack T _ m _ _ id _ id).
Notation "[ 'domType' 'for' T 'by' // ]" :=
  (DomType T (DefDomMixin [ordType of T]))
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

Lemma lubD x y : x ⊔ y = if x == y then Some x else None.
Proof. by case: T x y => [? [? []]]. Qed.

Lemma approxD x y : x ⊑ y = (x == y).
Proof. by rewrite /approx lubD; case: ifP => //= ->. Qed.

End DiscreteTheory.

Section Lifting.

Variable T : domType.
Implicit Types x y : option T.

Definition olub x y :=
  match x, y with
  | Some x, Some y => omap Some (x ⊔ y)
  | Some _, None   => Some x
  | None  , _      => Some y
  end.

Lemma olubxx x : olub x x = Some x.
Proof. by case: x => [x|] //=; rewrite lubxx. Qed.
Lemma olubC : commutative olub.
Proof. by move=> [x|] [y|] //=; rewrite /olub lubC. Qed.
Lemma olubA x y z : obind (olub^~ z) (olub x y) = obind (olub x) (olub y z).
Proof.
case: x y z => [x|] [y|] [z|] //=; try by case: lub.
case: (x ⊔ y) (lubA x y z) => [xy|] //=.
  by move=> ->; case: lub.
by case: lub=> //= ? <-.
Qed.

Definition option_domMixin := DomMixin olubxx olubC olubA.
Canonical option_domType := Eval hnf in DomType (option T) option_domMixin.

End Lifting.
