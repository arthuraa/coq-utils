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
Reserved Notation "x ⊑ y ⊑ z" (at level 50, y at next level, no associativity).
Reserved Notation "x ⊔ y" (at level 40, left associativity).

Module Dom.

Section ClassDef.

(* XXX: This could be subsumed by an nary version *)
Definition is_lub T (appr : rel T) (x y : T) (o : option T) :=
  forall z,
    appr x z && appr y z
    = if o is Some xy then appr xy z else false.

Record axioms T (appr : rel T) (lub : T -> T -> option T) := Ax {
  _ : reflexive appr;
  _ : transitive appr;
  _ : antisymmetric appr;
  _ : forall x y, is_lub appr x y (lub x y)
}.

Record mixin_of T := Mixin {
  appr : rel T;
  lub : T -> T -> option T;
  _ : axioms appr lub
}.

Record class_of T := Class {base : Ord.class_of T; mixin : mixin_of T}.
Local Coercion base : class_of >-> Ord.class_of.

Structure type := Pack {sort; _ : class_of sort; _ : Type}.
Local Coercion sort : type >-> Sortclass.
Variables (T : Type) (cT : type).
Definition class := let: Pack _ c _ as cT' := cT return class_of cT' in c.
Definition clone c of phant_id class c := @Pack T c T.
Let xT := let: Pack T _ _ := cT in T.
Notation xclass := (class : class_of xT).

Definition pack m :=
  fun b bT & phant_id (Ord.class bT) b => Pack (@Class T b m) T.

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

Definition appr T := Dom.appr (Dom.class T).
Definition lub T := Dom.lub (Dom.class T).
Notation "x ⊑ y" := (appr x y) : dom_scope.
Notation "x ⊑ y ⊑ z" := (appr x y && appr y z) : dom_scope.
Notation "x ⊔ y" := (lub x y) : dom_scope.

Local Open Scope dom_scope.
Local Open Scope fset_scope.

Section Theory.

Variable (T : domType).
Implicit Types x y z : T.
Implicit Types xs ys zs : {fset T}.
Implicit Types P : pred T.

Local Notation appr := (@appr T) (only parsing).
Local Notation lub  := (@lub T) (only parsing).

Lemma apprxx : reflexive appr.
Proof. by case: T => [? [? [? ? []]]]. Qed.

Lemma appr_trans : transitive appr.
Proof. by case: T => [? [? [? ? []]]]. Qed.

Lemma anti_appr : antisymmetric appr.
Proof. by case: T => [? [? [? ? []]]]. Qed.

Lemma is_lub_lub x y : Dom.is_lub appr x y (x ⊔ y).
Proof. by case: T x y => [? [? [? ? []]]]. Qed.

Lemma lub_unique x y o : Dom.is_lub appr x y o -> o = x ⊔ y.
Proof.
move: (x ⊔ y) (is_lub_lub x y) => o' Po' Po.
without loss [z Pz]: o o' Po Po' / exists z, o = Some z.
  case eo: o Po => [z|]; rewrite -eo => Po; first by apply; eauto.
  case eo': o' Po'=> [z'|]; rewrite -eo'=> Po' P; try congruence.
  by apply/esym/P; eauto.
move/(_ z): (Po'); rewrite Po Pz apprxx; case: o' Po'=> [z'|] // Po'.
move/(_ z'): (Po); rewrite Po' Pz apprxx => h1 h2.
by congr Some; apply: anti_appr; rewrite -h1 -h2.
Qed.

Lemma lubxx x : x ⊔ x = Some x.
Proof. by apply/esym/lub_unique=> y; rewrite andbb. Qed.

Lemma lubC : commutative lub.
Proof. by move=> x y; apply/lub_unique=> z; rewrite andbC is_lub_lub. Qed.

Lemma appr_lubL x y : (x ⊑ y) = (x ⊔ y == Some y).
Proof.
apply/(sameP idP)/(iffP eqP)=> h.
  by move: (is_lub_lub x y y); rewrite h !apprxx andbT.
apply/esym/lub_unique => z; rewrite andbC.
have [yz|//] := boolP (y ⊑ z); by rewrite (appr_trans h yz).
Qed.

Lemma appr_lubR x y : (x ⊑ y) = (y ⊔ x == Some y).
Proof. by rewrite lubC appr_lubL. Qed.

(*
Lemma lubA x y z : obind (lub^~ z) (x ⊔ y) = obind (lub x) (y ⊔ z).
Proof.
case:
by case: T x y z => [? [? [? []]]]. Qed.*)

Lemma lub_apprL x y xy : x ⊔ y = Some xy -> x ⊑ xy.
Proof.
move=> Pxy; move: (is_lub_lub x y xy); rewrite Pxy apprxx.
by case/andP.
Qed.

Lemma lub_apprR x y xy : x ⊔ y = Some xy -> y ⊑ xy.
Proof. by rewrite lubC; apply: lub_apprL. Qed.

CoInductive lub_spec x y : option T -> Type :=
| LubSome xy
  of (forall z, (x ⊑ z) && (y ⊑ z) = xy ⊑ z) : lub_spec x y (Some xy)
| LubNone of (forall z, (x ⊑ z) && (y ⊑ z) = false) : lub_spec x y None.

Lemma lubP x y : lub_spec x y (x ⊔ y).
Proof. by move: (is_lub_lub x y); case: (x ⊔ y); constructor. Qed.

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
  (forall y, (xs != fset0) && all (appr^~ y) (FSet.fsval xs)
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
  & (forall y, all (appr^~ y) xs = x ⊑ y)
  : lubn_spec xs (Some x)
| LubnNone
  of (xs != fset0 -> forall y, all (appr^~ y) xs = false)
  : lubn_spec xs None.

Lemma lubnP xs : lubn_spec xs (lubn xs).
Proof.
move: (is_lubn_lubn xs); case e: (lubn xs) => [x|] /= h; constructor.
- by move: (h x); rewrite apprxx; case/andP.
- by move=> y; rewrite -h lubn_neq0 ?e.
by move=> ne0 y; rewrite -(h y) ne0.
Qed.

Lemma lubn_unique xs ox : is_lubn xs ox -> ox = lubn xs.
Proof.
case: (lubnP xs) ox=> [x ne|] h1 [x'|] h2 //.
- congr Some; apply: anti_appr; rewrite ne /= in h2.
  by rewrite -h2 h1 apprxx -h1 h2 apprxx.
- by move: (h1 x) (h2 x); rewrite ne apprxx => ->.
move: (h2 x'); rewrite apprxx => /andP [ne {h2} h2].
by rewrite h1 in h2.
Qed.

Lemma appr_lubn xs x :
  xs != fset0 ->
  (forall y, all (appr ^~ y) xs = x ⊑ y) ->
  lubn xs = Some x.
Proof.
move=> ne0 h; case: lubnP=> [x' _ h'|/(_ ne0) /(_ x)].
  congr Some; apply: anti_appr.
  by rewrite -h' h apprxx -h h' apprxx.
by rewrite h apprxx.
Qed.

Lemma lubn_appr_conv xs x y :
  lubn xs = Some x ->
  all (appr^~ y) xs = x ⊑ y.
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

Lemma lubnS xs ys :
  fsubset xs ys ->
  match lubn xs, lubn ys with
  | Some x, Some y => x ⊑ y
  | None  , Some y => xs == fset0
  | _     , _      => true
  end.
Proof.
rewrite -{-1}(fsetID ys xs) => /fsetIidPr ->; rewrite lubnU.
case: (lubnP xs)=> [x nx0 Px|].
  case: lubnP=> [y ny0 Py|]; last by case: ifP=> //; rewrite apprxx.
  case: lubP=> [xy /(_ xy)|] //.
  by rewrite apprxx => /andP [].
by case: lubnP=> [y ny0 Py|//]; case: eqP.
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

(* FIXME: Try to clean up closure lemmas *)

Definition lub_closed (P : pred T) :=
  {in P &, forall x1 x2 x12, x1 ⊔ x2 = Some x12 -> x12 \in P}.

Lemma lub_closure_closed xs : lub_closed (mem (lub_closure xs)).
Proof.
move=> x1 x2 /lub_closureP [ys1 sub1 e1] /lub_closureP [ys2 sub2 e2] x12 h.
apply/lub_closureP; exists (ys1 :|: ys2); first by rewrite fsubUset sub1.
by rewrite lubnU e1 e2.
Qed.

Lemma lub_closure_min xs ys :
  fsubset xs ys -> lub_closed (mem ys) -> fsubset (lub_closure xs) ys.
Proof.
move=> /fsubsetP sub ysP; apply/fsubsetP=> /= x /lub_closureP [zs sub' xP].
elim/fset_ind: zs x sub' xP => [//|x zs _ IH y].
rewrite fsubU1set lubnU /= => /andP [x_in sub'].
case ez: (lubn zs) => [z|] //=.
  move=> xz; apply/(ysP x z) => //; by [apply: sub|apply: IH].
by case: ifP=> // _ [<-]; apply/sub.
Qed.

Lemma lub_closure_ext xs : fsubset xs (lub_closure xs).
Proof.
apply/fsubsetP=> x; rewrite -fsub1set -powersetE => x_in.
rewrite /lub_closure in_fset mem_pmap.
by apply/mapP; exists (fset1 x).
Qed.

Lemma lub_closed_closure xs : lub_closed (mem xs) -> lub_closure xs = xs.
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

Lemma lub_closedP xs : lub_closed (mem xs) <-> lub_closure xs = xs.
Proof.
split; first exact: lub_closed_closure.
move=> <-; exact: lub_closure_closed.
Qed.

Lemma lub_closure0 : lub_closure fset0 = fset0.
Proof. by rewrite /lub_closure powerset0 /= fset0E. Qed.

Lemma lub_closure1 x : lub_closure (fset1 x) = fset1 x.
Proof.
apply/lub_closed_closure=> x1 x2; rewrite !in_fset1.
by move=> /eqP -> /eqP ->; rewrite lubxx => _ [<-]; rewrite in_fset1.
Qed.

(* FIXME: This probably needs a better name *)
Record lcset := LCSet {
  lcval :> {fset T};
  _     :  lub_closure lcval == lcval
}.
Definition lcset_of of phant T := lcset.
Identity Coercion lcset_of_lcset : lcset_of >-> lcset.

Canonical lcset_subType := [subType for lcval].
Definition lcset_eqMixin := [eqMixin of lcset by <:].
Canonical lcset_eqType := Eval hnf in EqType lcset lcset_eqMixin.
Definition lcset_choiceMixin := [choiceMixin of lcset by <:].
Canonical lcset_choiceType := Eval hnf in ChoiceType lcset lcset_choiceMixin.
Definition lcset_ordMixin := [ordMixin of lcset by <:].
Canonical lcset_ordType := Eval hnf in OrdType lcset lcset_ordMixin.

Canonical lcset_of_subType := [subType of lcset_of (Phant T)].
Canonical lcset_of_eqType := [eqType of lcset_of (Phant T)].
Canonical lcset_of_choiceType := [choiceType of lcset_of (Phant T)].
Canonical lcset_of_ordType := [ordType of lcset_of (Phant T)].

Program Definition lcset0 := @LCSet fset0 _.
Next Obligation. by rewrite lub_closure0. Qed.
Program Definition lcset1 x := @LCSet (fset1 x) _.
Next Obligation. by rewrite lub_closure1. Qed.

End Theory.

Notation "{ 'lcset' T }" := (lcset_of (Phant T))
  (at level 0, format "{ 'lcset'  T }") : type_scope.

Definition pred_of_lcset (T : domType) (xs : lcset T) :=
  [pred x : T | x \in val xs].
Canonical lcset_predType T := mkPredType (@pred_of_lcset T).
Canonical lcset_of_predType (T : domType) := [predType of {lcset T}].

Module QDom.

Record axioms T (qappr : rel T) (qlub : T -> T -> option T) := Ax {
  _ : reflexive qappr;
  _ : transitive qappr;
  _ : forall x y, Dom.is_lub qappr x y (qlub x y)
}.

Record predom T := PreDom {
  qappr : rel T;
  qlub  : T -> T -> option T;
   _    : axioms qappr qlub
}.

Section Dom.

Local Open Scope quotient_scope.

Variable T : ordType.
Variable D : predom T.

Local Notation qappr := (qappr D).
Local Notation qlub  := (qlub D).

Implicit Types x y : T.

Lemma qappr_refl : reflexive qappr.
Proof. by case: D => ?? []. Qed.

Lemma qappr_trans : transitive qappr.
Proof. by case: D => ?? []. Qed.

Lemma is_lub_qlub : forall x y, Dom.is_lub qappr x y (qlub x y).
Proof. by case: D => ?? []. Qed.

Definition qdom_eq x y := qappr x y && qappr y x.

Lemma qdom_eqP : equiv_class_of qdom_eq.
Proof.
rewrite /qdom_eq; case: D=> r l [refl trans _] /=; split.
- by move=> x; rewrite !refl.
- by move=> x y; rewrite andbC.
move=> y x z /andP [xy yx] /andP [yz zy].
by rewrite (trans _ _ _ xy) // (trans _ _ _ zy).
Qed.

Canonical qdom_eq_equiv := EquivRelPack qdom_eqP.

Definition type := {eq_quot qdom_eq}.
Definition type_of of phantom (rel T) qappr := type.

Implicit Types qx qy : type.

Definition qdom_appr qx qy := qappr (repr qx) (repr qy).
Definition qdom_lub qx qy : option {eq_quot qdom_eq} :=
  omap \pi (qlub (repr qx) (repr qy)).

Lemma qdom_lubP : Dom.axioms qdom_appr qdom_lub.
Proof.
split.
- move=> qx; exact: qappr_refl.
- move=> ???; exact: qappr_trans.
- move=> qx qy; rewrite /qdom_appr.
  elim/quotP: qx=> /= x ->; elim/quotP: qy=> /= y -> xy.
  exact/eqmodP.
rewrite /qdom_appr /qdom_lub /=.
elim/quotP=> /= x ex; elim/quotP=> /= y ey; elim/quotP=> /= z ez.
rewrite ex ey ez is_lub_qlub; case: (qlub x y) => [xy|] //=.
case: piP=> /= xy' /eqmodP/andP [l1 l2].
apply/(sameP idP)/(iffP idP); [move: l1|move: l2]; exact: qappr_trans.
Qed.

Canonical qdom_eqType := Eval hnf in [eqType of type].
Canonical qdom_choiceType := Eval hnf in [choiceType of type].
Canonical qdom_quotType := Eval hnf in [quotType of type].
Canonical qdom_ordType := Eval hnf in [ordType of type].
Definition qdom_domMixin := DomMixin qdom_lubP.
Canonical qdom_domType := Eval hnf in DomType type qdom_domMixin.

Canonical qdom_of_eqType := Eval hnf in [eqType of type_of (Phantom _ _)].
Canonical qdom_of_choiceType :=
  Eval hnf in [choiceType of type_of (Phantom _ _)].
Canonical qdom_of_quotType := Eval hnf in [quotType of type_of (Phantom _ _)].
Canonical qdom_of_ordType := Eval hnf in [ordType of type_of (Phantom _ _)].
Canonical qdom_of_domType := Eval hnf in [domType of type_of (Phantom _ _)].

End Dom.

End QDom.

Coercion QDom.qappr : QDom.predom >-> rel.

Notation "{ 'qdom' lt }" :=
  (QDom.type_of (Phantom (rel _) lt))
  (at level 0, format "{ 'qdom'  lt }") : type_scope.

Canonical QDom.qdom_eqType.
Canonical QDom.qdom_choiceType.
Canonical QDom.qdom_quotType.
Canonical QDom.qdom_ordType.
Canonical QDom.qdom_domType.

Canonical QDom.qdom_of_eqType.
Canonical QDom.qdom_of_choiceType.
Canonical QDom.qdom_of_quotType.
Canonical QDom.qdom_of_ordType.
Canonical QDom.qdom_of_domType.

Section QDomTheory.

Local Open Scope quotient_scope.

Variable T : ordType.
Variable apprT : QDom.predom T.
Implicit Types (x y : T) (qx qy : {qdom apprT}).

Lemma pi_appr x y : \pi_{qdom apprT} x ⊑ \pi y = apprT x y.
Proof.
rewrite /appr /= /QDom.qdom_appr.
case: piP => x' /eqmodP/andP [xx' x'x].
case: piP => y' /eqmodP/andP [yy' y'y].
apply/(sameP idP)/(iffP idP).
  by move=> xy; apply: QDom.qappr_trans (QDom.qappr_trans xy yy').
by move=> x'y'; apply: QDom.qappr_trans (QDom.qappr_trans x'y' y'y).
Qed.

End QDomTheory.

Module Discrete.

Section ClassDef.

Record mixin_of (T : domType) := Mixin {
  _ : forall x y : T, x ⊑ y = (x == y)
}.

Section Mixins.

Variable T : ordType.
Implicit Types x y : T.

Lemma dlubP : Dom.axioms eq_op (fun x y => if x == y then Some x else None).
Proof.
split.
- exact: eqxx.
- exact: eq_op_trans.
- by move=> x y /andP [/eqP ->].
move=> x y; case: (altP eqP)=> [<- {y} y|ne z]; first exact: andbb.
by case: (altP (x =P z))=> [<-|//]; rewrite eq_sym (negbTE ne).
Qed.

Definition DefDomMixin := DomMixin dlubP.
Definition DefMixin := @Mixin (DomType T DefDomMixin) (fun _ _ => erefl).

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
Definition ordType := @Ord.Pack cT xclass xT.
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
Coercion ordType : type >-> Ord.type.
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

Canonical void_domType := [domType for void by //].
Canonical void_discDomType := [discDomType for void].

Canonical nat_domType := [domType for nat by //].
Canonical nat_discDomType := [discDomType for nat].

Canonical bool_domType := [domType for bool by //].
Canonical bool_discDomType := [discDomType for bool].

Section DiscreteTheory.

Variable T : discDomType.
Implicit Types x y : T.

Lemma apprD x y : x ⊑ y = (x == y).
Proof. by case: T x y => [? [? []]]. Qed.

Lemma lubD x y : x ⊔ y = if x == y then Some x else None.
Proof.
apply/esym/lub_unique=> z; rewrite !apprD.
case: (altP (x =P y))=> [->|ne]; first by rewrite !apprD andbb.
case: (altP (x =P z))=> [<-|ne'] //.
by rewrite eq_sym (negbTE ne).
Qed.

End DiscreteTheory.

Section Lifting.

Variable T : domType.
Implicit Types x y : option T.

Definition oappr x y :=
  if x is Some x then
    if y is Some y then x ⊑ y else false
  else true.

Definition olub x y :=
  match x, y with
  | Some x, Some y => omap Some (x ⊔ y)
  | Some _, None   => Some x
  | None  , _      => Some y
  end.

Lemma olubP : Dom.axioms oappr olub.
Proof.
split.
- by case=> [x|] //=; rewrite apprxx.
- move=> [x|] [y|] [z|] //=; exact: appr_trans.
- by case=> [x|] [y|] //= /anti_appr ->.
case=> [x|] [y|] [z|] //=; rewrite ?andbT ?is_lub_lub //; by case: lub.
Qed.

Definition option_domMixin := DomMixin olubP.
Canonical option_domType := Eval hnf in DomType (option T) option_domMixin.

Lemma oapprE x y :
  x ⊑ y =
  if x is Some x then
    if y is Some y then x ⊑ y else false
  else true.
Proof. by []. Qed.

Lemma oapprBx x : None ⊑ x.
Proof. by rewrite oapprE. Qed.

Lemma oapprxB x : x ⊑ None = (x == None).
Proof. by rewrite oapprE; case: x. Qed.

End Lifting.

Section Retract.

Variable T : domType.
Implicit Types (xs : {fset T}) (x y : T).

Definition retract xs x :=
  lubn (fset [seq y <- xs | y ⊑ x]).

CoInductive retract_spec xs x : option T -> Prop :=
| RetractSome y
  of y \in lub_closure xs
  &  (forall z, z \in lub_closure xs -> z ⊑ x = z ⊑ y)
  :  retract_spec xs x (Some y)
| RetractNone
  of (forall z, z \in lub_closure xs -> z ⊑ x = false)
  :  retract_spec xs x None.

Lemma retractP xs x : retract_spec xs x (retract xs x).
Proof.
rewrite /retract; case exs: (lubn _)=> [y|] //; constructor.
- apply/lub_closureP; eexists; eauto.
  by apply/fsubsetP=> z; rewrite in_fset mem_filter => /andP [].
- move=> z /lub_closureP [zs sub ezs]; apply/(sameP idP)/(iffP idP).
    move: (is_lubn_lubn (fset [seq y <- xs | y ⊑ x]) x).
    rewrite lubn_neq0 ?exs //= all_fset filter_all => /esym yx.
    by move=> zy; apply: appr_trans zy yx.
  move=> zx; have sub' : fsubset zs (fset [seq y <- xs | y ⊑ x]).
    apply/fsubsetP=> w w_in; rewrite in_fset mem_filter (fsubsetP _ _ sub) //.
    move: (is_lubn_lubn zs); rewrite ezs lubn_neq0 ?ezs //=.
    move=> /(_ z); rewrite apprxx => /allP/(_ _ w_in) wz.
    by rewrite (appr_trans wz zx).
  by move: (lubnS sub'); rewrite ezs exs.
move=> z /lub_closureP [zs sub ezs]; apply/negbTE/negP => zx.
move: (is_lubn_lubn (fset [seq y <- xs | y ⊑ x])); rewrite exs.
have: fsubset zs (fset [seq y <- xs | y ⊑ x]).
  apply/fsubsetP=> w w_in; rewrite in_fset mem_filter (fsubsetP _ _ sub) //.
  move: (is_lubn_lubn zs); rewrite ezs lubn_neq0 ?ezs //=.
  move=> /(_ z); rewrite apprxx => /allP/(_ _ w_in) wz.
  by rewrite (appr_trans wz zx).
case: (_ =P fset0) => [->|_] /=.
  by rewrite fsubset0 -[_ == fset0]negbK lubn_neq0 ?ezs.
by move=> sub' /(_ x); rewrite all_fset filter_all.
Qed.

Lemma retract_appr xs x : retract xs x ⊑ Some x.
Proof.
rewrite /retract oapprE; case: lubnP=> [x' ne0 /(_ x)|] //=.
by rewrite all_fset filter_all => <-.
Qed.

Lemma retract_lub_closure xs x x' :
  retract xs x = Some x' ->
  x' \in lub_closure xs.
Proof.
move=> e; apply/lub_closureP; exists (fset [seq y <- xs | y ⊑ x])=> //.
by apply/fsubsetP => y; rewrite in_fset mem_filter => /andP [].
Qed.

Lemma retractS xs ys x :
  fsubset xs ys ->
  obind (retract xs) (retract ys x) = retract xs x.
Proof.
rewrite /retract; case: lubnP=> [y ny0 Py|ne] //= /fsubsetP sub.
  congr lubn; apply/eq_fset=> z; rewrite !in_fset !mem_filter.
  rewrite [LHS]andbC [RHS]andbC; have [in_xs|] //= := boolP (_ \in xs).
  move: (Py x); rewrite all_fset filter_all => /esym yx.
  apply/(sameP idP)/(iffP idP); last by move=> h; apply: (appr_trans h).
  move=> zx; move: (Py y); rewrite apprxx => /allP/(_ z).
  by rewrite in_fset mem_filter zx => /(_ (sub _ in_xs)).
case: lubnP=> [x' nx'0 Px'|] //=.
have/ne {ne} Pys: fset [seq y <- ys | y ⊑ x] != fset0.
  apply: contra nx'0; rewrite -!fsubset0.
  apply/fsubset_trans/fsubsetP=> y; rewrite !in_fset !mem_filter.
  by case/andP => -> /sub ->.
by move/(_ x): Pys; rewrite all_fset filter_all.
Qed.

Lemma retract_idem xs x :
  obind (retract xs) (retract xs x) = retract xs x.
Proof. exact/retractS/fsubsetxx. Qed.

Lemma retractK xs x : x \in lub_closure xs -> retract xs x = Some x.
Proof.
move=> /lub_closureP [ys sub ex].
have eys: ys = fset [seq y <- ys | y ⊑ x].
  move: (is_lubn_lubn ys x); rewrite ex apprxx.
  case/andP=> _ /allP ub; apply/eq_fset=> y.
  rewrite in_fset mem_filter andbC.
  by have [/ub|] //= := boolP (y \in ys).
move: (retractS x sub); rewrite {3}/retract -eys ex.
case e1: (retract xs x)=> [x'|] //= e2; apply/anti_appr.
by rewrite -{1}e1 retract_appr -e2 retract_appr.
Qed.

Lemma retract_mono xs x y : x ⊑ y -> retract xs x ⊑ retract xs y.
Proof.
move=> xy; rewrite /retract.
have sub : fsubset (fset [seq z <- xs | z ⊑ x]) (fset [seq z <- xs | z ⊑ y]).
  apply/fsubsetP=> z; rewrite !in_fset !mem_filter => /andP [zx ->].
  by rewrite (appr_trans zx xy).
move: (lubnS sub).
case ex: (lubn (fset [seq z <- xs | z ⊑ x])) => [x'|] //=.
move: (is_lubn_lubn (fset [seq z <- xs | z ⊑ y]) y).
have [ey| ney] //= := boolP (fset _ == fset0).
  suff ex0 : fset [seq z <- xs | z ⊑ x] = fset0 by rewrite ex0 in ex.
  apply/eqP; rewrite -fsubset0; rewrite -fsubset0 in ey.
  by rewrite (fsubset_trans sub ey).
by rewrite all_fset filter_all; case: (lubn _) => [y'|] //=.
Qed.

Lemma retractU xs1 xs2 x :
  retract (xs1 :|: xs2) x =
  match retract xs1 x, retract xs2 x with
  | Some x1, Some x2 => x1 ⊔ x2
  | None   , Some x2 => Some x2
  | Some x1, None    => Some x1
  | None   , None    => None
  end.
Proof.
rewrite /retract.
set l1 := fset [seq y <- xs1 | y ⊑ x].
set l2 := fset [seq y <- xs2 | y ⊑ x].
have -> : fset [seq y <- xs1 :|: xs2 | y ⊑ x] = l1 :|: l2.
  apply/eq_fset=> y; rewrite in_fsetU !in_fset !mem_filter in_fsetU.
  by rewrite andb_orr.
rewrite lubnU.
move: (is_lubn_lubn l1 x) (is_lubn_lubn l2 x).
case e1: (lubn (fset [seq y <- xs1 | y ⊑ x]))=> [y1|] //=;
case e2: (lubn (fset [seq y <- xs2 | y ⊑ x]))=> [y2|] //=;
rewrite /l1 /l2 !all_fset !filter_all !andbT; first by move=> _ ->.
by move=> -> _.
Qed.

End Retract.

Section ProductDomain.

Variables T S : domType.
Implicit Types (x : T) (y : S) (p : T * S).

Definition prod_appr p1 p2 := (p1.1 ⊑ p2.1) && (p1.2 ⊑ p2.2).

Definition prod_lub p1 p2 :=
  match p1.1 ⊔ p2.1, p1.2 ⊔ p2.2 with
  | Some x, Some y => Some (x, y)
  | _     , _      => None
  end.

Lemma prod_lubP : Dom.axioms prod_appr prod_lub.
Proof.
split.
- by move=> p; rewrite /prod_appr !apprxx.
- move=> p1 p2 p3 /andP [h11 h12] /andP [h21 h22].
  by apply/andP; split; [apply: appr_trans h21| apply: appr_trans h22].
- move=> [x1 y1] [x2 y2] /= /andP [/andP [/= h1 h2] /andP [/= h3 h4]].
  by congr pair; apply: anti_appr; rewrite ?h1 ?h2 ?h3 ?h4.
move=> [x1 y1] [x2 y2] [x3 y3] /=; rewrite /prod_appr /prod_lub /=.
rewrite -andbA [(y1 ⊑ y3) && _]andbA [(y1 ⊑ y3) && _]andbC !andbA.
rewrite is_lub_lub -andbA is_lub_lub.
by case: (x1 ⊔ x2) (y1 ⊔ y2) => [x12|] [y12|] //=; rewrite andbF.
Qed.

Definition prod_domMixin := DomMixin prod_lubP.
Canonical prod_domType := Eval hnf in DomType (T * S) prod_domMixin.

End ProductDomain.

Section FMapDom.

Variable (T : ordType) (S : domType).
Implicit Types (x : T) (y : S) (f g h : {fmap T -> S}).

Definition fappr f g := all (fun x => f x ⊑ g x) (domm f :|: domm g).

Lemma fapprP f g : reflect (forall x, f x ⊑ g x) (fappr f g).
Proof.
rewrite /fappr; apply/(iffP allP); last by eauto.
move=> P x.
have [x_in|] := boolP (x \in domm f :|: domm g); first by eauto.
rewrite in_fsetU negb_or !mem_domm.
by case: (f x) (g x) => [?|] [?|].
Qed.

Lemma fapprPn f g : reflect (exists x, ~~ (f x ⊑ g x)) (~~ fappr f g).
Proof.
rewrite /fappr; apply/(iffP allPn); first by case; eauto.
case=> x Px; exists x=> //; rewrite in_fsetU mem_domm.
by move: Px; rewrite oapprE; case: (f x).
Qed.

Notation pflub f g :=
  (mkfmapfp (fun x => odflt None (f x ⊔ g x)) (domm f :|: domm g)).

Definition flub f g :=
  if fappr f (pflub f g) && fappr g (pflub f g) then Some (pflub f g)
  else None.

Lemma flubP : Dom.axioms fappr flub.
Proof.
split.
- by move=> f; apply/fapprP=> x; rewrite apprxx.
- move=> f g h /fapprP fg /fapprP gh; apply/fapprP=> x.
  by apply: appr_trans (fg x) (gh x).
- move=> f g /andP [/fapprP fg /fapprP gf].
  by apply/eq_fmap=> x; apply/anti_appr; rewrite fg gf.
move=> f g; rewrite /flub; set h := pflub f g.
have Ph : forall x, h x = odflt None (f x ⊔ g x).
  move=> x; rewrite /h mkfmapfpE in_fsetU !mem_domm.
  by case: (f x) (g x) => [x1|] [x2|].
case: ifPn => [/andP [/fapprP fh /fapprP gh]|].
  move=> h'; apply/(sameP andP)/(iffP (fapprP _ _)).
    by move=> hh'; split; apply/fapprP=> x; move: (hh' x); apply: appr_trans.
  case=> /fapprP fh' /fapprP gh' x; rewrite Ph.
  move: (is_lub_lub (f x) (g x) (h' x)).
  by rewrite fh' gh' /=; case: lub.
move: h Ph => h Ph Pfg.
without loss /fapprPn [x Px] : f g h Ph {Pfg} / ~~ fappr f h.
  case/nandP: Pfg => [Pf | Pg]; first by eauto.
  move=> gen h'; rewrite andbC; apply: (gen g f h)=> //.
  by move=> x; rewrite Ph lubC.
move=> h'; apply: contraNF Px => /andP [/fapprP Pf /fapprP Pg].
move: (is_lub_lub (f x) (g x) (h' x)); rewrite Pf Pg Ph.
case e: lub=> [y|] //=; by move: (lub_apprL e).
Qed.

Definition fmap_domMixin := DomMixin flubP.
Canonical fmap_domType :=
  Eval hnf in DomType {fmap T -> S} fmap_domMixin.

Lemma domm_appr f g : f ⊑ g -> fsubset (domm f) (domm g).
Proof.
move=> /fapprP fg; apply/fsubsetP=> x; rewrite 2!mem_domm.
by move: (fg x); case: (f x) (g x)=> [y1|] //= [y2|] //=.
Qed.

Lemma domm_lub f g h : f ⊔ g = Some h -> domm h = domm f :|: domm g.
Proof.
move=> fg; apply/eqP; rewrite eqEfsubset fsubUset !domm_appr ?andbT;
try by [apply: lub_apprR fg|apply: lub_apprL fg].
move: fg; rewrite /lub /= /flub /=; case: ifP=> // _ [<- {h}].
apply/fsubsetP=> x; rewrite domm_mkfmapfp in_fset mem_filter.
by case/andP.
Qed.

End FMapDom.

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

Section LCSubDom.

Variables (T : domType) (xs : lcset T).

Structure lcset_sub := LCSetSub {
  lcsetval :> T;
  _        :  lcsetval \in xs
}.

Canonical lcset_sub_subType := [subType for lcsetval].
Definition lcset_sub_eqMixin := [eqMixin of lcset_sub by <:].
Canonical lcset_sub_eqType := Eval hnf in EqType lcset_sub lcset_sub_eqMixin.
Definition lcset_sub_choiceMixin := [choiceMixin of lcset_sub by <:].
Canonical lcset_sub_choiceType :=
  Eval hnf in ChoiceType lcset_sub lcset_sub_choiceMixin.
Definition lcset_sub_ordMixin := [ordMixin of lcset_sub by <:].
Canonical lcset_sub_ordType :=
  Eval hnf in OrdType lcset_sub lcset_sub_ordMixin.

Lemma lcset_subP : lub_closed (mem xs).
Proof. apply/lub_closedP/eqP; exact: (valP xs). Qed.

Canonical lcset_sub_subDomType :=
  Eval hnf in SubDomType lcset_sub lcset_subP.
Definition lcset_sub_domMixin := [domMixin of lcset_sub by <:].
Canonical lcset_sub_domType :=
  Eval hnf in DomType lcset_sub lcset_sub_domMixin.

End LCSubDom.

Coercion lcset_sub : lcset >-> Sortclass.

Module IncFun.

Section Def.

Variable T S : domType.
Implicit Types (f g : {fmap T -> S}) (x : T).

Local Open Scope quotient_scope.

Definition increasing f :=
  all (fun p => p.1 ⊑ p.2 ==> f p.1 ⊑ f p.2)
      [seq (x1, x2) | x1 <- lub_closure (domm f),
                      x2 <- lub_closure (domm f) ].

Lemma increasingP f :
  reflect (lub_closed (mem (domm f))
           /\ {in domm f &, forall x1 x2, x1 ⊑ x2 -> f x1 ⊑ f x2})
          (increasing f).
Proof.
apply/(iffP allP)=> /= [inc | [clos inc]].
  have/fsubsetP ext := lub_closure_ext (domm f).
  have clos : lub_closed (mem (domm f)); last split=> //.
    move=> x1 x2 /dommP [y1 e1] /dommP [y2 e2] x12 e12.
    have/inc/implyP/(_ (lub_apprL e12)):
      (x1, x12) \in [seq (x1, x12) | x1  <- lub_closure (domm f),
                                     x12 <- lub_closure (domm f)].
      apply/allpairsP; exists (x1, x12)=> /=; split=> //=.
        by apply/ext; rewrite mem_domm e1.
      apply/(lub_closure_closed _ _ e12); apply/ext;
      by rewrite mem_domm (e1, e2).
    rewrite e1 /= mem_domm; by case: (f x12).
  move=> x1 x2 in1 in2 x1x2.
  suff/inc/implyP/(_ x1x2):
    (x1, x2) \in [seq (x1, x2) | x1 <- lub_closure (domm f),
                                 x2 <- lub_closure (domm f) ] by [].
  by apply/allpairsP; exists (x1, x2); split=> //=; eauto.
rewrite (lub_closed_closure clos).
case=> [? ?] /allpairsP [[x1 x2] [in1 in2 [-> ->]]].
by apply/implyP/inc.
Qed.

Implicit Types fi gi hi : {f | increasing f}.

Definition inc_app fi x := obind (val fi) (retract (domm (val fi)) x).

Definition inc_appr fi gi :=
  all (fun x => inc_app fi x ⊑ inc_app gi x)
      (lub_closure (domm (val fi) :|: domm (val gi))).

Lemma inc_apprP fi gi :
  reflect (forall x, inc_app fi x ⊑ inc_app gi x) (inc_appr fi gi).
Proof.
apply/(iffP allP)=> //; move=> efg x; rewrite /inc_app.
rewrite -(retractS x (fsubsetUl (domm (val fi)) (domm (val gi)))).
rewrite -(retractS x (fsubsetUr (domm (val fi)) (domm (val gi)))).
case e: (retract (_ :|: _) x)=> [x'|] //=.
exact: (efg _ (retract_lub_closure e)).
Qed.

Lemma inc_apprPn fi gi :
  reflect (exists x, ~~ (inc_app fi x ⊑ inc_app gi x)) (~~ inc_appr fi gi).
Proof.
apply/(iffP allPn); first by case; eauto.
case=> x; rewrite /inc_app.
rewrite -(retractS x (fsubsetUl (domm (val fi)) (domm (val gi)))).
rewrite -(retractS x (fsubsetUr (domm (val fi)) (domm (val gi)))).
case ex: (retract (domm (val fi) :|: domm (val gi)) x)=> [x'|] //=.
move=> fg; exists x'=> //; exact: retract_lub_closure ex.
Qed.

Lemma inc_apprxx : reflexive inc_appr.
Proof. by move=> fi; apply/inc_apprP=> x; rewrite apprxx. Qed.

Lemma inc_appr_trans : transitive inc_appr.
Proof.
move=> gi fi hi /inc_apprP fg /inc_apprP gh.
apply/inc_apprP=> x; exact: appr_trans (fg x) (gh x).
Qed.

Lemma inc_app_inc fi gi x1 x2 :
  inc_appr fi gi -> x1 ⊑ x2 -> inc_app fi x1 ⊑ inc_app gi x2.
Proof.
rewrite /inc_app => /inc_apprP figi x1x2.
apply: (@appr_trans _ (obind (val fi) (retract (domm (val fi)) x2))).
  move: (retract_mono (domm (val fi)) x1x2).
  case e1: (retract (domm (val fi)) x1)=> [x1'|] //=.
  case e2: (retract (domm (val fi)) x2)=> [x2'|] //=.
  rewrite oapprE=> x1'x2'.
  move/increasingP: (valP fi) => [/lub_closed_closure <- inc].
  exact: (inc x1' x2' (retract_lub_closure e1) (retract_lub_closure e2) x1'x2').
exact/figi.
Qed.

Definition inc_eq fi gi := inc_appr fi gi && inc_appr gi fi.

Lemma inc_eqP fi gi : reflect (inc_app fi =1 inc_app gi) (inc_eq fi gi).
Proof.
apply/(iffP andP).
  case=> [/inc_apprP fg /inc_apprP gf] x; apply/anti_appr.
  by rewrite fg gf.
by move=> e; split; apply/inc_apprP=> x; rewrite e apprxx.
Qed.

Lemma inc_eqxx : reflexive inc_eq.
Proof. by move=> fi; rewrite /inc_eq inc_apprxx. Qed.

Lemma inc_eq_sym : symmetric inc_eq.
Proof. by move=> fi gi; rewrite /inc_eq andbC. Qed.

Lemma inc_eq_trans : transitive inc_eq.
Proof.
move=> gi fi hi /andP [fg gf] /andP [gh hg]; apply/andP; split.
  exact: inc_appr_trans fg gh.
exact: inc_appr_trans hg gf.
Qed.

Definition inc_eq_equiv :=
  Eval hnf in EquivRel inc_eq inc_eqxx inc_eq_sym inc_eq_trans.

Notation pinc_lub fi gi :=
  (mkfmapfp (fun x => odflt None (inc_app fi x ⊔ inc_app gi x))
            (lub_closure (domm (val fi) :|: domm (val gi)))).

Definition inc_lub fi gi : option {f | increasing f} :=
  if insub (pinc_lub fi gi) is Some hi then
    if inc_appr fi hi && inc_appr gi hi then Some hi
    else None
  else None.

Lemma inc_lubP : QDom.axioms inc_appr inc_lub.
Proof.
split=> /=.
- move=> fq; exact: inc_apprxx.
- move=> gq fq hq; exact: inc_appr_trans.
move=> fi gi hi; rewrite /inc_lub /=.
set clos := lub_closure (domm (val fi) :|: domm (val gi)).
set fg   := mkfmapfp _ clos.
have e :
  forall hi, fsubset (domm (val hi)) (domm (val fi) :|: domm (val gi)) ->
  forall x, inc_app hi x = obind (inc_app hi) (retract clos x).
  move=> hi' sub.
  move: (fsubset_trans sub (lub_closure_ext _)) => {sub} sub x.
  by rewrite /inc_app -(retractS _ sub); case: (retract clos x).
have ret_clos : forall x x', retract clos x = Some x' -> x' \in clos.
  move=> x x' ex; move: (retract_lub_closure ex).
  by rewrite lub_closure_idem => ->.
move: {e} (e _ (fsubsetUl _ _)) (e _ (fsubsetUr _ _))=> fE gE.
have [/allP coh|/allPn [x x_in incoh]] :=
  boolP (all (fun x => inc_app fi x ⊔ inc_app gi x) clos).
  have {coh} coh : forall x, inc_app fi x ⊔ inc_app gi x.
    move=> x; rewrite fE gE; case ex: (retract clos x) => [x'|] //=.
    apply: coh; rewrite /clos -lub_closure_idem.
    by apply: retract_lub_closure ex.
  have domm_fg : domm fg = clos.
    apply/eq_fset=> x'; rewrite domm_mkfmapfp in_fset mem_filter andbC.
    have [in_clos|] //= := boolP (x' \in lub_closure _).
    move: (coh x').
    case fi_x': (inc_app fi x')=> [y1|] //=;
    case gi_x': (inc_app gi x')=> [y2|] //=.
      by rewrite /lub /=; case: lub.
    move: fi_x'; rewrite /inc_app.
    case e_fi_x': (retract (domm (val fi)) x')=> [x''|] //=.
      move=> fi_x''; move: (retract_lub_closure e_fi_x').
      case/increasingP: (valP fi)=> /lub_closed_closure -> _.
      by rewrite mem_domm fi_x''.
    move=> _ _; move: gi_x'; rewrite /inc_app.
    case e_gi_x': (retract (domm (val gi)) x')=> [x''|] //=.
      move=> gi_x''; move: (retract_lub_closure e_gi_x').
      case/increasingP: (valP gi)=> /lub_closed_closure -> _.
      by rewrite mem_domm gi_x''.
    by move/retractK: in_clos; rewrite retractU e_fi_x' e_gi_x'.
  have fgE : forall x, obind fg (retract clos x)
                       = odflt None (inc_app fi x ⊔ inc_app gi x).
    move=> x; rewrite fE gE; case ex: (retract clos x)=> [x'|] //=.
    by rewrite mkfmapfpE (ret_clos _ _ ex).
  have Pfg : increasing fg.
    apply/increasingP; split; rewrite domm_fg; first exact/lub_closure_closed.
    move=> x1 x2 in1 in2 x1x2; move: (fgE x1) (fgE x2) (in2).
    rewrite -{3}domm_fg mem_domm ?retractK ?lub_closure_idem //= => -> ->.
    move: (coh x1) (coh x2).
    case el1: (inc_app fi x1 ⊔ inc_app gi x1)=> [[l1|]|] //= _.
    case el2: (inc_app fi x2 ⊔ inc_app gi x2)=> [[l2|]|] //= _.
    move: (is_lub_lub (inc_app fi x1) (inc_app gi x1) (Some l2)).
    rewrite el1 => <- => _; apply/andP; split.
      exact: (appr_trans (inc_app_inc (inc_apprxx fi) x1x2) (lub_apprL el2)).
    exact: (appr_trans (inc_app_inc (inc_apprxx gi) x1x2) (lub_apprR el2)).
  rewrite (insubT increasing Pfg).
  have {fgE} fgE : forall x, inc_app (Sub fg Pfg) x =
                             odflt None (inc_app fi x ⊔ inc_app gi x).
    by move=> x; rewrite {1}/inc_app /= domm_fg.
  move: (Sub fg Pfg : {f | increasing f}) fgE => /= {fg Pfg domm_fg} fgi fgiE.
  have -> /= : inc_appr fi fgi && inc_appr gi fgi.
    apply/andP; split.
      apply/inc_apprP=> x; rewrite fgiE fE gE.
      case ex: (retract clos x)=> [x'|] //=.
      move: (coh x').
      case ey: lub=> [y|] //= _.
      exact: (lub_apprL ey).
    apply/inc_apprP=> x; rewrite fgiE fE gE.
    case ex: (retract clos x)=> [x'|] //=.
    move: (coh x').
    case ey: lub=> [y|] //= _.
    exact: (lub_apprR ey).
  apply/(sameP andP)/(iffP (inc_apprP _ _)).
    move=> fgi_hi; split; apply/allP=> x in_clos.
      move: (is_lub_lub (inc_app fi x) (inc_app gi x) (inc_app hi x)).
      move: (fgi_hi x) (coh x); rewrite fgiE.
      by case: lub=> /= [y|] // -> _ /andP [].
    move: (is_lub_lub (inc_app fi x) (inc_app gi x) (inc_app hi x)).
    move: (fgi_hi x) (coh x); rewrite fgiE.
    by case: lub=> /= [y|] // -> _ /andP [].
  case=> /inc_apprP fi_hi /inc_apprP gi_hi x; rewrite fgiE; move: (coh x).
  move: (is_lub_lub (inc_app fi x) (inc_app gi x) (inc_app hi x)).
  by rewrite fi_hi gi_hi /=; case: lub.
have {incoh} incoh : forall hi', ~~ (inc_appr fi hi' && inc_appr gi hi').
  move=> hi'; apply: contra incoh => /andP [/inc_apprP fiP /inc_apprP giP].
  move: (is_lub_lub (inc_app fi x) (inc_app gi x) (inc_app hi' x)).
  by rewrite fiP giP; case: lub.
rewrite (negbTE (incoh hi)); case: insubP=> /= [fgi inc|] //.
by rewrite (negbTE (incoh fgi)).
Qed.

Canonical incfun_predom := Eval hnf in QDom.PreDom inc_lubP.

(* FIXME: Using a regular definition here makes it harder for Coq to figure out
   that the coercion into functions below is valid. *)

(*CoInductive type := IncFun {
  quot_of_incfun : {qdom inc_appr}
}.*)
Definition type := {qdom inc_appr}.
Definition type_of of phant (T -> S) := type.
Identity Coercion type_of_type : type_of >-> type.

End Def.

Module Exports.

Notation "{ 'incfun' T }" := (IncFun.type_of (Phant T))
  (at level 0, format "{ 'incfun'  T }") : type_scope.

Section WithVar.

Variables T S : domType.

Canonical incfun_eqType := Eval hnf in [eqType of IncFun.type T S].
Canonical incfun_choiceType := Eval hnf in [choiceType of IncFun.type T S].
Canonical incfun_ordType := Eval hnf in [ordType of IncFun.type T S].
Canonical incfun_domType := Eval hnf in [domType of IncFun.type T S].

Canonical incfun_of_eqType := Eval hnf in [eqType of {incfun T -> S}].
Canonical incfun_of_choiceType := Eval hnf in [choiceType of {incfun T -> S}].
Canonical incfun_of_ordType := Eval hnf in [ordType of {incfun T -> S}].
Canonical incfun_of_domType := Eval hnf in [domType of {incfun T -> S}].

End WithVar.

End Exports.

End IncFun.

Export IncFun.Exports.

Definition inc_app (T S : domType) (f : IncFun.type T S) x : option S :=
  IncFun.inc_app (repr f) x.

Coercion inc_app : IncFun.type >-> Funclass.
(* This seems to be needed here *)
Identity Coercion incfun_of_incfun : IncFun.type_of >-> IncFun.type.

Section IncFunDom.

Local Open Scope quotient_scope.

Variables T S : domType.
Implicit Types f g : {incfun T -> S}.
Implicit Types (x y : T).

Lemma inc_apprP f g : reflect (forall x, f x ⊑ g x) (f ⊑ g).
Proof. exact/IncFun.inc_apprP. Qed.

Lemma inc_app_inc f g x y : f ⊑ g -> x ⊑ y -> f x ⊑ g y.
Proof. exact/IncFun.inc_app_inc. Qed.

Lemma eq_incfun f g : f =1 g <-> f = g.
Proof.
split; last by move=> ->.
by move=> fg; apply/anti_appr/andP; split; apply/inc_apprP=> x;
rewrite fg apprxx.
Qed.

End IncFunDom.

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

Lemma retr_embP T (sT : {lcset T}) :
  emb_class_of (@lcsetval T sT) (pcomp insub (retract sT)).
Proof.
split.
- move=> /= x; rewrite /pcomp retractK /= ?valK //.
  move/eqP: (valP sT) => /= ->; exact: valP.
move=> /= x y; rewrite /pcomp; case: retractP => [z|]; move/eqP: (valP sT) => -> /=.
  move=> z_in -> /=; last exact: (valP x).
  by rewrite insubT.
move=> -> //; exact: (valP x).
Qed.
Canonical retr_emb T (sT : {lcset T}) := Embedding (retr_embP sT).

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
            exists (sT : {lcset T}) (x' : f_obj [domType of sT]),
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
have [{sS sS_clos} sS -> /= e_sT] : exists sS' : {lcset chain n}, sS = val sS'.
  by exists (LCSet sS_clos).
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
