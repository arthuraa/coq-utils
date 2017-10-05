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
Local Open Scope fset_scope.

Section Theory.

Variable (T : domType).
Implicit Types x y z : T.
Implicit Types xs ys zs : {fset T}.
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

Lemma lub_approxL x y xy : x ⊔ y = Some xy -> x ⊑ xy.
Proof.
rewrite /approx => exy.
by move: (lubA x x y); rewrite exy lubxx /= -exy => <-.
Qed.

Lemma lub_approxR x y xy : x ⊔ y = Some xy -> y ⊑ xy.
Proof. by rewrite lubC; apply: lub_approxL. Qed.

(* XXX: This can probably be subsumed by the nary version *)
Notation is_lub x y oxy :=
  (forall z, (x ⊑ z) && (y ⊑ z) = if oxy is Some xy then xy ⊑ z else false).

Lemma is_lub_lub x y : is_lub x y (x ⊔ y).
Proof.
move=> z; apply/(sameP andP)/(iffP idP).
  case exy: (x ⊔ y) => [xy|] //= xy_z.
  by split; apply: approx_trans xy_z;
  rewrite (lub_approxL exy, lub_approxR exy).
case=> /eqP exz /eqP eyz.
move: (lubA x y z); rewrite eyz /= exz.
by case: (x ⊔ y) => [xy|] //= /eqP.
Qed.

CoInductive lub_spec x y : option T -> Type :=
| LubSome xy
  of (forall z, (x ⊑ z) && (y ⊑ z) = xy ⊑ z) : lub_spec x y (Some xy)
| LubNone of (forall z, (x ⊑ z) && (y ⊑ z) = false) : lub_spec x y None.

Lemma lubP x y : lub_spec x y (x ⊔ y).
Proof. by move: (is_lub_lub x y); case: (x ⊔ y); constructor. Qed.

Lemma lub_unique x y oxy : is_lub x y oxy -> oxy = x ⊔ y.
Proof.
case: (lubP x y) oxy => [xy|] h1 [xy'|] h2 //.
- congr Some; apply: anti_approx.
  by rewrite -h2 h1 approx_refl -h1 h2 approx_refl.
- by move: (h1 xy) (h2 xy) => ->; rewrite approx_refl.
by move: (h2 xy') (h1 xy') => ->; rewrite approx_refl.
Qed.

Definition lubn xs : option T :=
  if val xs is x :: xs' then
    foldl (fun ox x' => obind (fun x => lub x x') ox) (Some x) xs'
  else None.

Lemma lubn0 : lubn fset0 = None.
Proof. by []. Qed.

Lemma lubn1 x : lubn (fset1 x) = Some x.
Proof. by []. Qed.

Lemma lubn_neq0 xs : lubn xs -> xs != fset0.
Proof. by apply: contraTN => /eqP ->. Qed.

Notation is_lubn xs ox :=
  (forall y, (xs != fset0) && all (approx^~ y) (FSet.fsval xs)
   = if ox is Some x then x ⊑ y else false).

Lemma is_lubn_lubn xs : is_lubn xs (lubn xs).
Proof.
move=> y; rewrite -sizes_eq0 size_eq0 /lubn /=.
case: {xs} (FSet.fsval xs) => [|x xs] //=.
elim: xs x => [|x' xs IH] x //=; first by rewrite andbT.
rewrite andbA is_lub_lub; case: (x ⊔ x') => [xx'|] //=.
by rewrite (_ : foldl _ _ _ = None) //; elim: xs {x IH}.
Qed.

CoInductive lubn_spec xs : option T -> Type :=
| LubnSome x of xs != fset0
  & (forall y, all (approx^~ y) xs = x ⊑ y)
  : lubn_spec xs (Some x)
| LubnNone
  of (xs != fset0 -> forall y, all (approx^~ y) xs = false)
  : lubn_spec xs None.

Lemma lubnP xs : lubn_spec xs (lubn xs).
Proof.
move: (is_lubn_lubn xs); case e: (lubn xs) => [x|] /= h; constructor.
- by move: (h x); rewrite approx_refl; case/andP.
- by move=> y; rewrite -h lubn_neq0 ?e.
by move=> ne0 y; rewrite -(h y) ne0.
Qed.

Lemma lubn_unique xs ox : is_lubn xs ox -> ox = lubn xs.
Proof.
case: (lubnP xs) ox=> [x ne|] h1 [x'|] h2 //.
- congr Some; apply: anti_approx; rewrite ne /= in h2.
  by rewrite -h2 h1 approx_refl -h1 h2 approx_refl.
- by move: (h1 x) (h2 x); rewrite ne approx_refl => ->.
move: (h2 x'); rewrite approx_refl => /andP [ne {h2} h2].
by rewrite h1 in h2.
Qed.

Lemma approx_lubn xs x :
  xs != fset0 ->
  (forall y, all (approx ^~ y) xs = x ⊑ y) ->
  lubn xs = Some x.
Proof.
move=> ne0 h; case: lubnP=> [x' _ h'|/(_ ne0) /(_ x)].
  congr Some; apply: anti_approx.
  by rewrite -h' h approx_refl -h h' approx_refl.
by rewrite h approx_refl.
Qed.

Lemma lubn_approx_conv xs x y :
  lubn xs = Some x ->
  all (approx^~ y) xs = x ⊑ y.
Proof. by move=> e; move: (is_lubn_lubn xs y); rewrite lubn_neq0 ?e //. Qed.

Lemma lubnU xs ys :
  lubn (xs :|: ys) =
  match lubn xs, lubn ys with
  | Some x, Some y => x ⊔ y
  | Some x, None   => if ys != fset0 then None else Some x
  | None  , Some y => if xs != fset0 then None else Some y
  | None  , None   => None
  end.
Proof.
have [->|xn0] /= := altP (xs =P _); first by rewrite fset0U; case: lubn.
have [->|yn0] /= := altP (ys =P _); first by rewrite fsetU0; case: lubn.
apply/esym/lubn_unique => z; rewrite fsetU_eq0 negb_and xn0 yn0 all_fsetU /=.
move: (is_lubn_lubn xs z) (is_lubn_lubn ys z); rewrite xn0 yn0 /= => -> ->.
case: (lubn xs) (lubn ys) => [x|] [y|] //; last by rewrite andbF.
exact: is_lub_lub.
Qed.

Definition lub_closure xs :=
  fset (pmap (fun ys => lubn ys) (powerset xs)).

Lemma lub_closureP x xs :
  reflect (exists2 ys, fsubset ys xs & lubn ys = Some x)
          (x \in lub_closure xs).
Proof.
rewrite /lub_closure in_fset mem_pmap; apply/(iffP mapP)=> /=.
  by case=> /= ys; rewrite powersetE => sub ->; exists ys.
by case=> /= ys sub lub; exists ys; rewrite ?lub ?powersetE.
Qed.

Definition lub_closed xs :=
  forall x1 x2 x12,
    x1 \in xs -> x2 \in xs -> x1 ⊔ x2 = Some x12 ->
    x12 \in xs.

Lemma lub_closure_closed xs : lub_closed (lub_closure xs).
Proof.
move=> x1 x2 x12 /lub_closureP [ys1 sub1 e1] /lub_closureP [ys2 sub2 e2] h.
apply/lub_closureP; exists (ys1 :|: ys2); first by rewrite fsubUset sub1.
by rewrite lubnU e1 e2.
Qed.

Lemma lub_closure_min xs ys :
  fsubset xs ys -> lub_closed ys -> fsubset (lub_closure xs) ys.
Proof.
move=> /fsubsetP sub ysP; apply/fsubsetP=> /= x /lub_closureP [zs sub' xP].
elim/fset_ind: zs x sub' xP => [//|x zs _ IH y].
rewrite fsubU1set lubnU /= => /andP [x_in sub'].
case ez: (lubn zs) => [z|] //=.
  move=> xz; apply/(ysP x z y) => //; by [apply: sub|apply: IH].
by case: ifP=> // _ [<-]; apply/sub.
Qed.

Lemma lub_closure_ext xs : fsubset xs (lub_closure xs).
Proof.
apply/fsubsetP=> x; rewrite -fsub1set -powersetE => x_in.
rewrite /lub_closure in_fset mem_pmap.
by apply/mapP; exists (fset1 x).
Qed.

Lemma lub_closed_closure xs : lub_closed xs -> lub_closure xs = xs.
Proof.
move=> closed; apply/eqP; rewrite eqEfsubset lub_closure_ext andbT.
apply: lub_closure_min => //; exact: fsubsetxx.
Qed.

Lemma lub_closure_inc xs ys :
  fsubset xs ys -> fsubset (lub_closure xs) (lub_closure ys).
Proof.
rewrite -powersetS /lub_closure => /fsubsetP sub; apply/fsubsetP => x.
rewrite !in_fset !mem_pmap; case/mapP => /= zs /sub in_zs e.
by apply/mapP; eauto.
Qed.

Lemma lub_closure_idem xs : lub_closure (lub_closure xs) = lub_closure xs.
Proof.
apply/eqP; rewrite eqEfsubset lub_closure_ext andbT.
apply: lub_closure_min; by [apply: fsubsetxx|apply: lub_closure_closed].
Qed.

Lemma lub_closureS xs ys :
  fsubset (lub_closure xs) (lub_closure ys) = fsubset xs (lub_closure ys).
Proof.
apply/(sameP idP)/(iffP idP); last exact: fsubset_trans (lub_closure_ext xs).
by rewrite -{2}(lub_closure_idem ys); apply: lub_closure_inc.
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
