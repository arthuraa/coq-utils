From mathcomp
Require Import
  ssreflect ssrfun ssrbool ssrnat seq eqtype choice fintype generic_quotient.


Require Import ord fset fmap.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Delimit Scope dom_scope with dom.

Reserved Notation "x ⊑ y" (at level 50, no associativity).
Reserved Notation "x ⊑ y ⊑ z" (at level 50, y at next level, no associativity).
Reserved Notation "x ⊔ y" (at level 40, left associativity).

Module Dom.

Section ClassDef.

(* XXX: There could be subsumed by an nary version *)
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
  lubn (fset [seq y <- xs| y ⊑ x]).

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

Section FunctionDom.

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

CoInductive flub_spec f g : option {fmap T -> S} -> Prop :=
| FLubSome h
  of (forall x, h x = odflt None (f x ⊔ g x))
  &  (forall x, (f x ⊑ h x) && (g x ⊑ h x))
  :  flub_spec f g (Some h)
| FLubNone x of ~~ (f x ⊔ g x) : flub_spec f g None.

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

End FunctionDom.

Section IncFunctionDom.

Local Open Scope quotient_scope.

Variables T S : domType.
Implicit Types (x : T) (y : S).

Record pre_fundom := PreFundom {
  pfdval :> {fmap T -> S};
  _      :  all (fun p => p.1 ⊑ p.2 ==> pfdval p.1 ⊑ pfdval p.2)
                [seq (x1, x2) | x1 <- domm pfdval, x2 <- domm pfdval]
}.

Canonical pre_fundom_subType := Eval hnf in [subType for pfdval].
Definition pre_fundom_eqMixin := [eqMixin of pre_fundom by <:].
Canonical pre_fundom_eqType :=
  Eval hnf in EqType pre_fundom pre_fundom_eqMixin.
Definition pre_fundom_choiceMixin := [choiceMixin of pre_fundom by <:].
Canonical pre_fundom_choiceType :=
  Eval hnf in ChoiceType pre_fundom pre_fundom_choiceMixin.
Definition pre_fundom_ordMixin := [ordMixin of pre_fundom by <:].
Canonical pre_fundom_ordType :=
  Eval hnf in OrdType pre_fundom pre_fundom_ordMixin.

Definition fdapp (f : {fmap T -> S}) x := obind f (retract (domm f) x).

Definition fdeq (f g : pre_fundom) :=
  all (fun x => fdapp f x == fdapp g x) (lub_closure (domm f :|: domm g)).

Lemma fdeqP (f g : pre_fundom) : reflect (fdapp f =1 fdapp g) (fdeq f g).
Proof.
apply(iffP idP); last by by move=> efg; apply/allP=> x _; apply/eqP/efg.
move=> /allP efg x.
without loss [y] : f g efg / exists y, fdapp f x = Some y.
  case ef: (fdapp f x) => [y|] //=; rewrite -ef; first by apply; eauto.
  case eg: (fdapp g x) => [y|] //=.
  rewrite -eg => h; apply/esym; apply: h; last by eauto.
  by move=> x'; rewrite fsetUC eq_sym; eauto.
rewrite /fdapp.
rewrite -(retractS x (fsubsetUl (domm f) (domm g))).
rewrite -(retractS x (fsubsetUr (domm f) (domm g))).
case e: (retract (_ :|: _) x)=> [x'|] //=.
by move/(_ _ (retract_lub_closure e))/eqP: efg.
Qed.

Lemma fdeq_refl : reflexive fdeq.
Proof. by move=> f; apply/fdeqP=> x. Qed.

Lemma fdeq_sym : symmetric fdeq.
Proof.
by move=> f g; apply/(sameP (fdeqP _ _))/(iffP (fdeqP _ _))=> /fsym.
Qed.

Lemma fdeq_trans : transitive fdeq.
Proof.
move=> g f h /fdeqP fg /fdeqP gh; apply/fdeqP.
exact: ftrans fg gh.
Qed.

Definition fdeq_equiv :=
  Eval hnf in EquivRel fdeq fdeq_refl fdeq_sym fdeq_trans.

CoInductive fundom := Fundom of {eq_quot fdeq_equiv}.

Definition quot_of_fundom f := let: Fundom f := f in f.

Canonical fundom_newType := [newType for quot_of_fundom].
Definition fundom_eqMixin := [eqMixin of fundom by <:].
Canonical fundom_eqType := Eval hnf in EqType fundom fundom_eqMixin.
Definition fundom_choiceMixin := [choiceMixin of fundom by <:].
Canonical fundom_choiceType :=
  Eval hnf in ChoiceType fundom fundom_choiceMixin.
Definition fundom_ordMixin := [ordMixin of fundom by <:].
Canonical fundom_ordType := Eval hnf in OrdType fundom fundom_ordMixin.


End IncFunctionDom.
