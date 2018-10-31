From mathcomp Require Import ssreflect ssrfun ssrbool ssrnat eqtype seq.

From extructures Require Import ord.

Require Import void.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Definition cast T (P : T -> Type) x y (e : x = y) : P x -> P y :=
  match e with erefl => id end.

Arguments cast {_} _ {_ _} _.

Record functor := Functor {
  fobj      :> Type -> Type;
  fmap      :  forall T S, (T -> S) -> (fobj T -> fobj S);
  fmap_eq   :  forall T S (f g : T -> S), f =1 g -> fmap f =1 fmap g;
  fmap1     :  forall T, fmap (@id T) =1 id;
  fmap_comp :  forall T S R (f : T -> S) (g : S -> R),
                 fmap (g \o f) =1 fmap g \o fmap f
}.

Module Ind.

Section ClassDef.

Record mixin_of T (F : functor) := Mixin {
  Roll     :  F T -> T;
  case     :  forall S, (F T -> S) -> T -> S;
  rec      :  forall S, (F (T * S)%type -> S) -> T -> S;
  _        :  forall S f a, rec f (Roll a) =
                            f (fmap (fun x => (x, rec f x)) a) :> S;
  _        :  forall S f a, case f (Roll a) = f a :> S;
  _        :  forall P,
                (forall (a : F {x & P x}), P (Roll (fmap tag a))) ->
                forall x, P x
}.
Notation class_of := mixin_of (only parsing).

Record type F := Pack {sort : Type; _ : class_of sort F; _ : Type}.
Local Coercion sort : type >-> Sortclass.
Variables (F : functor) (T : Type) (cT : type F).
Definition class := let: Pack _ c _ as cT' := cT return class_of cT' F in c.
Definition clone c of phant_id class c := @Pack F T c T.
Let xT := let: Pack T _ _ := cT in T.
Notation xclass := (class : class_of xT).

Definition pack c := @Pack F T c T.

End ClassDef.

Module Exports.
Coercion sort : type >-> Sortclass.
Notation indType := type.
Notation IndMixin := Mixin.
Notation IndType F T m := (@pack F T m).
Notation "[ 'indMixin' 'of' T ]" := (class _ : mixin_of T)
  (at level 0, format "[ 'indMixin'  'of'  T ]") : form_scope.
Notation "[ 'indType' 'of' T 'for' C ]" := (@clone T C _ idfun id)
  (at level 0, format "[ 'indType'  'of'  T  'for'  C ]") : form_scope.
Notation "[ 'indType' 'of' T ]" := (@clone T _ _ id id)
  (at level 0, format "[ 'indType'  'of'  T ]") : form_scope.
End Exports.

End Ind.
Export Ind.Exports.

Section IndTheory.

Variable F : functor.
Variable T : indType F.

Definition Roll := (Ind.Roll (Ind.class T)).
Definition case := (Ind.case (Ind.class T)).
Definition rec  := (Ind.rec  (Ind.class T)).

Lemma recE S f a : rec f (Roll a) =
                   f (fmap (fun x => (x, rec f x)) a) :> S.
Proof. by rewrite /Roll /rec; case: (T) f a=> [? []]. Qed.

Lemma caseE S f a : case f (Roll a) = f a :> S.
Proof. by rewrite /Roll /case; case: (T) f a=> [? []]. Qed.

Lemma indP P :
  (forall (a : F {x & P x}), P (Roll (fmap tag a))) ->
  forall x, P x.
Proof. by rewrite /Roll /rec; case: (T) P => [? []]. Qed.

Definition unroll := case id.

Lemma RollK : cancel Roll unroll.
Proof. by move=> x; rewrite /unroll caseE. Qed.

Lemma Roll_inj : injective Roll.
Proof. exact: can_inj RollK. Qed.

Lemma unrollK : cancel unroll Roll.
Proof. by elim/indP=> args; rewrite RollK. Qed.

Lemma unroll_inj : injective unroll.
Proof. exact: can_inj unrollK. Qed.

End IndTheory.

Fixpoint fin n :=
  if n is n.+1 then option (fin n) else Empty_set.

Fixpoint all_fin n : (fin n -> Prop) -> Prop :=
  match n with
  | 0    => fun P => True
  | n.+1 => fun P => P None /\ @all_fin n (fun i => P (Some i))
  end.

Lemma all_finP n (P : fin n -> Prop) : all_fin P <-> (forall i, P i).
Proof.
split; elim: n P=> [|n IH] P //=.
- case=> ? H [i|] //; exact: (IH (fun i => P (Some i))).
- by move=> H; split; [exact: (H None)|apply: IH; eauto].
Qed.

Fixpoint nth_fin T (xs : seq T) : fin (size xs) -> T :=
  match xs with
  | [::]    => fun n => match n with end
  | x :: xs => fun n => if n is Some n then nth_fin n else x
  end.

Fixpoint leq_fin n : forall i j : fin n, (i = j) + bool :=
  match n with
  | 0    => fun i => match i with end
  | n.+1 =>
    fun i =>
      match i return forall j, (i = j) + bool with
      | None    => fun j => if j is None then inl erefl else inr true
      | Some i' => fun j => if j is Some j' then
                              match leq_fin i' j' with
                              | inl e => inl (f_equal Some e)
                              | inr b => inr b
                              end
                            else inr false
      end
  end.

Lemma leq_finii n i : @leq_fin n i i = inl erefl.
Proof.
elim: n i=> [|n IH] // [i|] //=; by rewrite IH.
Qed.

Section Hlist.

Variables (I : Type) (T_ : I -> Type).

Implicit Types (i : I) (ix : seq I).

Definition hlist ix : Type :=
  foldr (fun i S => T_ i * S)%type unit ix.

Definition hfun ix S : Type :=
  foldr (fun i R => T_ i -> R) S ix.

Fixpoint happ ix S : hfun ix S -> hlist ix -> S :=
  match ix with
  | [::]    => fun f _    => f
  | i :: ix => fun f args => happ (f args.1) args.2
  end.

Fixpoint hcurry ix S : (hlist ix -> S) -> hfun ix S :=
  match ix with
  | [::]    => fun f   => f tt
  | i :: ix => fun f x => hcurry (fun args=> f (x, args))
  end.

Lemma hcurryK ix S (f : hlist ix -> S) l : happ (hcurry f) l = f l.
Proof.
by elim: ix f l=> /= [? []|i ix IH f [x l]] //; rewrite IH.
Qed.

Fixpoint hcat (ix1 ix2 : seq I) :
  hlist ix1 -> hlist ix2 -> hlist (ix1 ++ ix2) :=
  match ix1 with
  | [::] => fun _ l2 => l2
  | i :: ix1 => fun l1 l2 => (l1.1, hcat l1.2 l2)
  end.

Fixpoint nth_hlist (ix : seq I) :
    hlist ix -> forall n : fin (size ix), T_ (nth_fin n) :=
  match ix with
  | [::]    => fun l n => match n with end
  | i :: ix => fun l n => match n with
                          | Some n => nth_hlist l.2 n
                          | None   => l.1
                          end
  end.

Fixpoint hlist_of_seq (f : forall i, T_ i) ix : hlist ix :=
  if ix is i :: ix then (f i, hlist_of_seq f ix) else tt.

Lemma nth_hlist_of_seq f ix n :
  nth_hlist (hlist_of_seq f ix) n = f (nth_fin n).
Proof. elim: ix n=> /= [|i ix IH] // [n|]; by rewrite ?IH. Qed.

Fixpoint hlist_of_fun ix : forall (f : forall n : fin (size ix), T_ (nth_fin n)), hlist ix :=
  match ix with
  | [::]    => fun _ => tt
  | i :: ix => fun f => (f None, hlist_of_fun (fun n => f (Some n)))
  end.

Lemma nth_hlist_of_fun ix f n : nth_hlist (@hlist_of_fun ix f) n = f n.
Proof.
by elim: ix f n=> [|i ix IH] //= f [n|] //; rewrite IH.
Qed.

Fixpoint all_hlist ix : (hlist ix -> Prop) -> Prop :=
  match ix with
  | i :: ix => fun P => forall x, all_hlist (fun l => P (x, l))
  | [::]    => fun P => P tt
  end.

Lemma all_hlistP ix P : @all_hlist ix P <-> (forall l, P l).
Proof.
split; elim: ix P=> [|i ix IH] //=; first by move=> P ? [].
- by move=> P H [x l]; move/(_ x)/IH in H.
- by move=> P H x; apply: IH=> l.
Qed.

Fixpoint hfold S (f : forall i, T_ i -> S -> S) a ix : hlist ix -> S :=
  match ix with
  | [::] => fun _ => a
  | i :: ix => fun l => f i l.1 (hfold f a l.2)
  end.

End Hlist.

Coercion happ : hfun >-> Funclass.

Fixpoint hmap I (T_ S_ : I -> Type) (f : forall i, T_ i -> S_ i) ix :
  hlist T_ ix -> hlist S_ ix :=
  match ix with
  | [::]    => fun _ => tt
  | i :: ix => fun l => (f i l.1, hmap f l.2)
  end.

Lemma hmap_eq I (T_ S_ : I -> Type) (f g : forall i, T_ i -> S_ i) :
  (forall i, f i =1 g i) ->
  forall ix, @hmap _ _ _ f ix =1 @hmap _ _ _ g ix.
Proof.
by move=> efg; elim=> [[]|i ix IH] // [x l] /=; rewrite efg IH.
Qed.

Lemma hmap1 I (T_ : I -> Type) ix (l : hlist T_ ix) : hmap (fun i => id) l = l.
Proof.
by elim: ix l=> /= [[]|i ix IH] // [x l] /=; rewrite IH.
Qed.

Lemma hmap_comp I (T_ S_ R_ : I -> Type)
                (f : forall i, T_ i -> S_ i)
                (g : forall i, S_ i -> R_ i) ix (l : hlist T_ ix) :
  hmap g (hmap f l) = hmap (fun i => g i \o f i) l.
Proof.
by elim: ix l=> [[]|i ix IH] //= [x l] /=; rewrite IH.
Qed.

Fixpoint hzip I (T_ S_ : I -> Type) ix :
  hlist T_ ix -> hlist S_ ix -> hlist (fun i => T_ i * S_ i)%type ix :=
  match ix with
  | [::] => fun _ _ => tt
  | i :: ix => fun lx ly => ((lx.1, ly.1), hzip lx.2 ly.2)
  end.

Fixpoint hlist_map I J (T_ : J -> Type) (f : I -> J) (ix : seq I) :
  hlist T_ [seq f i | i <- ix] = hlist (T_ \o f) ix :=
  match ix with
  | [::]    => erefl
  | i :: ix => f_equal (prod (T_ (f i))) (hlist_map T_ f ix)
  end.

Fixpoint hfun_map I J (T_ : J -> Type) (f : I -> J) S (ix : seq I) :
  hfun T_ [seq f i | i <- ix] S = hfun (T_ \o f) ix S :=
  match ix with
  | [::]    => erefl
  | i :: ix => f_equal (fun R => T_ (f i) -> R) (hfun_map T_ f S ix)
  end.

Fixpoint hlist_eq I (T_ S_ : I -> Type) (e : forall i, T_ i = S_ i) ix :
  hlist T_ ix = hlist S_ ix :=
  match ix with
  | [::]    => erefl
  | i :: ix => f_equal2 prod (e i) (hlist_eq e ix)
  end.

Fixpoint hfun_eq I (T_ S_ : I -> Type) (e : forall i, T_ i = S_ i) ix R :
  hfun T_ ix R = hfun S_ ix R :=
  match ix with
  | [::]    => erefl
  | i :: ix => f_equal2 (fun X Y => X -> Y) (e i) (hfun_eq e ix R)
  end.

Variant kind T := Other of T | Rec.

Arguments Rec {_}.

Definition kmap T S (f : T -> S) (k : kind T) :=
  if k is Other x then Other (f x) else Rec.
Definition arity T := seq (kind T).
Definition signature T := seq (arity T).
Definition sig_map T S (f : T -> S) (s : signature T) : signature S :=
  [seq [seq kmap f k | k <- a] | a <- s].

Section PolyFunctor.

Variables (A : Type) (A_sort : A -> Type).

Local Coercion A_sort : A >-> Sortclass.

Implicit Types (k : kind A) (a : arity A).

Variable s : signature A.

Definition type_of_arg S (k : kind A) : Type :=
  if k is Other R then R else S.

Definition type_of_arg_map S R (f : S -> R) k :
  type_of_arg S k -> type_of_arg R k :=
  if k is Rec then f else id.

Record polyf T := Polyf {
  pconstr : fin (size s);
  pargs : hlist (type_of_arg T) (nth_fin pconstr)
}.

Definition poly_fmap S R (f : S -> R) (x : polyf S) : polyf R :=
  Polyf (hmap (type_of_arg_map f) (pargs x)).

Lemma poly_fmap_eq S R (f g : S -> R) :
  f =1 g ->
  poly_fmap f =1 poly_fmap g.
Proof.
move=> efg [c args] /=; rewrite /poly_fmap /=; congr Polyf.
by apply/hmap_eq; case.
Qed.

Lemma poly_fmap1 S (x : polyf S) : poly_fmap id x = x.
Proof.
rewrite /poly_fmap; case: x=> i args /=.
rewrite (_ : hmap _ args = hmap (fun _ => id) args) ?hmap1 //.
by elim: (nth_fin i) args=> {i} [[]|[R|] ks IH] //= [arg args] /=;
rewrite IH.
Qed.

Lemma poly_fmap_comp T S R f (g : S -> R) (x : polyf T) :
  poly_fmap (g \o f) x = poly_fmap g (poly_fmap f x).
Proof.
case: x=> [i args]; rewrite /poly_fmap /= hmap_comp; congr Polyf.
by apply/hmap_eq; case=> [?|].
Qed.

Canonical polyf_functor :=
  Functor poly_fmap_eq poly_fmap1 poly_fmap_comp.

Lemma Polyf_inj T i : injective (@Polyf T i).
Proof.
move=> args1 args2 e.
pose get x :=
  (if leq_fin (pconstr x) i is inl e then
     cast (fun i => hlist (type_of_arg T) (nth_fin i)) e (pargs x)
   else args1).
move/(f_equal get): e; by rewrite /get leq_finii.
Qed.

End PolyFunctor.

Module CoqInd.

Section Basic.

Variable (A : Type) (A_sort : A -> Type) (T : Type).
Local Coercion A_sort : A >-> Sortclass.

Implicit Types (k : kind A) (a : arity A) (s : signature A).

Definition constructors s :=
  hlist (fun a => hfun (type_of_arg A_sort T) a T) s.

Fixpoint branch S a : Type :=
  match a with
  | Other R :: ks => R      -> branch S ks
  | Rec     :: ks => T -> S -> branch S ks
  | [::]          => S
  end.

Definition recursor s := forall S, hfun (branch S) s (T -> S).

Fixpoint branch_of_hfun S a :
  hfun (type_of_arg A_sort (T * S)) a S -> branch S a :=
  match a with
  | Other R :: a => fun f x   => branch_of_hfun (f x)
  | Rec     :: a => fun f x y => branch_of_hfun (f (x, y))
  | [::]         => fun f     => f
  end.

Fixpoint hfun_of_branch S a :
  branch S a -> hfun (type_of_arg A_sort (T * S)) a S :=
  match a with
  | Other R :: a => fun f x => hfun_of_branch (f x)
  | Rec     :: a => fun f p => hfun_of_branch (f p.1 p.2)
  | [::]         => fun f   => f
  end.

Lemma branch_of_hfunK S a f args :
  hfun_of_branch (@branch_of_hfun S a f) args = f args.
Proof.
by elim: a f args=> [|[R|] a IH] f //= [[x y] args] //.
Qed.

Definition recursor_eq s (cs : constructors s) (r : recursor s) :=
  forall S,
  all_hlist (fun bs : hlist (branch S) s =>
  all_fin   (fun i : fin (size s) =>
  all_hlist (fun args : hlist (type_of_arg A_sort T) (nth_fin i) =>
    r S bs (nth_hlist cs i args) =
    hfun_of_branch (nth_hlist bs i)
                   (hmap (type_of_arg_map (fun x => (x, r S bs x))) args)))).

Definition destructor s :=
  forall S, hfun (fun a => hfun (type_of_arg A_sort T) a S) s (T -> S).

Definition destructor_eq s (cs : constructors s) (d : destructor s) :=
  forall S,
  all_hlist (fun bs : hlist (fun ks => hfun (type_of_arg A_sort T) ks S) s =>
  all_fin   (fun i : fin (size s) =>
  all_hlist (fun args : hlist (type_of_arg A_sort T) (nth_fin i) =>
    d S bs (nth_hlist cs i args) = nth_hlist bs i args))).

Fixpoint ind_branch (P : T -> Type) a :
  hfun (type_of_arg A_sort T) a T -> Type :=
  match a with
  | Other R :: a => fun c => forall x : R,        ind_branch P (c x)
  | Rec     :: a => fun c => forall x : T, P x -> ind_branch P (c x)
  | [::]         => fun c => P c
  end.

Fixpoint ind_at (P : T -> Type) s : constructors s -> Type :=
  match s with
  | ks :: s => fun cs => ind_branch P cs.1 -> ind_at P cs.2
  | [::]    => fun cs => forall x, P x
  end.

End Basic.

Section ClassDef.

Variables (A : Type) (A_sort : A -> Type) (s : signature A).

Record mixin_of T := Mixin {
  Cons      : constructors A_sort T s;
  rec       : recursor A_sort T s;
  case      : destructor A_sort T s;
  _         : recursor_eq Cons rec;
  _         : destructor_eq Cons case;
  _         : forall P, ind_at P Cons;
}.

Record type := Pack {sort : Type; class : @mixin_of sort; _ : Type}.
Variables (T : Type).
Definition recE (m : mixin_of T) : recursor_eq (Cons m) (rec m) :=
  let: Mixin _ _ _ recE _ _ := m in recE.
Definition caseE (m : mixin_of T) : destructor_eq (Cons m) (case m) :=
  let: Mixin _ _ _ _ caseE _ := m in caseE.
Definition indP (m : mixin_of T) :=
  let: Mixin _ _ _ _ _ indP := m
  return forall P : T -> Type, ind_at P (Cons m)
  in indP.

End ClassDef.

Module Exports.
Coercion sort : type >-> Sortclass.
Coercion class : type >-> mixin_of.
Notation coqIndType := type.
Notation CoqIndType A A_sort s T m := (@Pack A A_sort s T m T).
Notation CoqIndMixin := Mixin.
End Exports.

End CoqInd.
Export CoqInd.Exports.

Section CoqIndTheory.

Variables (A : Type) (A_sort : A -> Type) (s : signature A).
Variable T : coqIndType A_sort s.

Local Notation F := (polyf_functor A_sort s).

Definition coqInd_Roll (x : F T) :=
  nth_hlist (@CoqInd.Cons _ _ _ _ T) (pconstr x) (pargs x).

Definition branches_of_hfun S (body : F (T * S)%type -> S) :=
  hlist_of_fun (fun i => CoqInd.branch_of_hfun (hcurry (fun l => body (Polyf l)))).

Definition coqInd_rec S (body : F (T * S)%type -> S) :=
  happ (@CoqInd.rec _ _ _ _ T S) (branches_of_hfun body).

Definition coqInd_case S (body : F T -> S) :=
  happ (@CoqInd.case _ _ _ _ T S)
       (hlist_of_fun (fun i => hcurry (fun l => body (Polyf l)))).

Lemma coqInd_recE S f a : @coqInd_rec S f (coqInd_Roll a) =
                          f (fmap (fun x => (x, coqInd_rec f x)) a).
Proof.
case: a=> [i args]; have := CoqInd.recE T S.
move/all_hlistP/(_ (branches_of_hfun f)).
move/all_finP/(_ i).
move/all_hlistP/(_ args).
rewrite /coqInd_rec /coqInd_Roll => -> /=.
rewrite /poly_fmap /=; move: (hmap _ _)=> l.
by rewrite /branches_of_hfun nth_hlist_of_fun CoqInd.branch_of_hfunK hcurryK.
Qed.

Lemma coqInd_caseE S f a : coqInd_case f (coqInd_Roll a) = f a :> S.
Proof.
case: a => [i args]; have := CoqInd.caseE T S.
move/all_hlistP/(_ (hlist_of_fun (fun i => hcurry (fun l => f (Polyf l))))).
move/all_finP/(_ i).
move/all_hlistP/(_ args).
rewrite /coqInd_case /coqInd_Roll => -> /=.
by rewrite nth_hlist_of_fun hcurryK.
Qed.

Lemma coqInd_indP P :
  (forall (a : F {x & P x}), P (coqInd_Roll (fmap tag a))) ->
  forall x, P x.
Proof.
rewrite /coqInd_Roll.
case: (T) P => S [/= Cons _ _ _ _ indP] _ P.
have {indP} indP:
    (forall i, CoqInd.ind_branch P (nth_hlist Cons i)) ->
    (forall x, P x).
  move/(_ P): indP.
  elim: (s) Cons=> [|a s' IH] //= [c cs] /= indP hyps.
  move: (hyps None)=> /indP/IH; apply=> i.
  exact: (hyps (Some i)).
move=> hyps; apply: indP=> j.
have {hyps} hyps:
  forall args : hlist (type_of_arg _ {x : S & P x}) (nth_fin j),
    P (nth_hlist Cons j (hmap (type_of_arg_map tag) args)).
  move=> args; exact: (hyps (Polyf args)).
elim: (nth_fin j) (nth_hlist Cons j) hyps=> [|[i|] ks IH] //=.
- by move=> ? /(_ tt).
- move=> c hyps x; apply: IH=> args.
  exact: (hyps (x, args)).
- move=> constr hyps x H; apply: IH=> args.
  exact: (hyps (existT _ x H, args)).
Qed.

Definition coqInd_indMixin :=
  IndMixin coqInd_recE coqInd_caseE coqInd_indP.
Canonical coqInd_indType :=
  Eval hnf in IndType F T coqInd_indMixin.

End CoqIndTheory.

(*
Section CoqIndTransport.

Variables (A : Type) (A_sort : A -> Type).
Variables (B : Type) (A_of_B : B -> A).

Fixpoint branch_mapA T S a :
   CoqInd.branch A_sort T S [seq kmap A_of_B k | k <- a] =
   CoqInd.branch (A_sort \o A_of_B) T S a :=
  match a with
  | [::] => erefl
  | Other R :: a => f_equal (fun U => A_sort (A_of_B R) -> U) (branch_mapA T S a)
  | Rec     :: a => f_equal (fun U => T -> S -> U) (branch_mapA T S a)
  end.

Definition type_of_arg_mapA T k :
  type_of_arg A_sort T (kmap A_of_B k) = type_of_arg (A_sort \o A_of_B) T k :=
  match k with
  | Rec => erefl
  | Other R => erefl
  end.

Fixpoint constructors_mapA T s :
  CoqInd.constructors A_sort T (sig_map A_of_B s) =
  CoqInd.constructors (A_sort \o A_of_B) T s :=
  match s with
  | [::] => erefl
  | a :: s =>
    let e := etrans (hfun_map (type_of_arg A_sort T) (kmap A_of_B) T a)
                    (hfun_eq (type_of_arg_mapA T) a T) in
    f_equal2 prod e (constructors_mapA T s)
  end.

Definition recursor_mapA T s :
  CoqInd.recursor A_sort T (sig_map A_of_B s) ->
  CoqInd.recursor (A_sort \o A_of_B) T s :=
  fun rec S =>
    let e := etrans (hfun_map (CoqInd.branch A_sort T S) _ (T -> S) s)
                    (hfun_eq (branch_mapA T S) s (T -> S)) in
    cast id e (rec S).

Definition destructor_mapA T s :
  CoqInd.destructor A_sort T (sig_map A_of_B s) ->
  CoqInd.destructor (A_sort \o A_of_B) T s.
move=> case S.
pose e1 := hfun_map (fun a => hfun (type_of_arg A_sort T) a S) (map (kmap A_of_B)) (T -> S) s.
pose e2 := hfun_eq (fun a => hfun_map (type_of_arg A_sort T) (kmap A_of_B) S a) s (T -> S).
pose e3 := hfun_eq (fun a => hfun_eq (type_of_arg_mapA T) a S) s (T -> S).
pose e := etrans e1 (etrans e2 e3).
exact: (cast id e (case S)).
Defined.

Lemma recursion_eqP T s Cons rec:
  @CoqInd.recursor_eq _ _ T (sig_map A_of_B s) Cons rec ->
  @CoqInd.recursor_eq _ _ T s
                      (cast id (constructors_mapA T s) Cons)
                      (recursor_mapA rec).
Proof.
move=> recE S.
apply/all_hlistP=> l.
apply/all_finP=> i.
apply/all_hlistP=> args.
move/(_ S)/all_hlistP: recE.
pose el := etrans (hlist_map (CoqInd.branch A_sort T S) (map (kmap A_of_B)) s)
                  (hlist_eq (branch_mapA T S) s).
move/(_ (cast id (esym el) l))/all_finP.
move



Variables (T : coqIndType A_sort (sig_map A_of_B s)).
*)

Module CoqIndEqType.

Section ClassDef.

Record class_of A A_sort s T := Class {
  base : Equality.class_of T;
  mixin : @CoqInd.mixin_of A A_sort s T
}.

Record type A A_sort s :=
  Pack {sort : Type; _ : @class_of A A_sort s sort; _ : Type}.
Local Coercion sort : type >-> Sortclass.

Variables (A : Type) (A_sort : A -> Type) (s : signature A).
Variables (T : Type) (cT : type A_sort s).
Definition class :=
  let: Pack _ c _ as cT' := cT return class_of A_sort s cT' in c.
Definition clone c of phant_id class c := @Pack _ A_sort s T c T.
Let xT := let: Pack T _ _ := cT in T.
Notation xclass := (class : class_of A_sort s xT).

Definition pack c := @Pack _ A_sort s T c T.

Definition eqType := @Equality.Pack cT (base xclass) xT.
Definition coqIndType := @CoqInd.Pack A A_sort s cT (mixin xclass) xT.

End ClassDef.

Section Exports.
Coercion sort : type >-> Sortclass.
Coercion eqType : type >-> Equality.type.
Coercion coqIndType : type >-> CoqInd.type.
Notation coqIndEqType := type.
End Exports.

End CoqIndEqType.

Section GenericEqType.

Variable (A : Type) (A_sort : A -> eqType) (s : signature A).
Variable (T : coqIndType A_sort s).

Definition ind_eq : T -> T -> bool :=
  rec (fun args1 x2 =>
         let args2 := unroll x2 in
         match leq_fin (pconstr args2) (pconstr args1) with
         | inl e =>
           hfold (fun k =>
                    if k is Other i then
                      fun args res => (args.1 == args.2) && res
                    else
                      fun args res =>
                        (args.1.2 args.2) && res)
                 true
                 (hzip (pargs args1)
                       (cast (fun i => hlist (type_of_arg _ T) (nth_fin i))
                             e (pargs args2)))
         | inr _ => false
         end).

Lemma ind_eqP : Equality.axiom ind_eq.
Proof.
elim/indP=> [[i_x x]] y.
rewrite /ind_eq recE /= -[rec _]/(ind_eq).
rewrite -{1}[y]unrollK; move: {y} (unroll y)=> [i_y y] /=.
case le: (leq_fin i_y i_x)=> [e|b]; last first.
  constructor=> /Roll_inj /= [] e _.
  by move: le; rewrite e leq_finii.
case: i_x / e x {le} => /= x.
apply/(@iffP (hmap (type_of_arg_map tag) x = y)); first last.
- by move=> /Roll_inj/Polyf_inj.
- by move=> <-.
elim: {i_y} (nth_fin i_y) x y=> [|[R|] ks IH] //=.
- by move=> [] []; constructor.
- move=> [x xs] [y ys] /=; apply/(iffP andP).
  + by case=> [/eqP -> /IH ->].
  + by case=> [<- <-]; split=> //; apply/IH.
- move=> [[x IHx] xs] [y ys] /=; apply(iffP andP).
  + by case=> [/IHx -> /IH ->].
  + by case=> [<- <-]; split; [apply/IHx| apply/IH].
Qed.

Definition CoqIndEqMixin := EqMixin ind_eqP.

End GenericEqType.

Section Instances.

Variables (A : Type) (A_sort : A -> Type).
Local Coercion A_sort : A >-> Sortclass.
Variables (a a1 a2 : A).

Definition unit_signature : signature A := [:: [::]].

Definition unit_constructors :
  CoqInd.constructors A_sort unit unit_signature := (tt, tt).

Definition unit_rec :
  CoqInd.recursor A_sort unit unit_signature :=
  fun S => @unit_rect (fun _ => S).

Definition unit_case :
  CoqInd.destructor A_sort unit unit_signature :=
  fun S ftt x => match x with tt => ftt end.

Lemma unit_recE :
  CoqInd.recursor_eq unit_constructors unit_rec.
Proof. by []. Qed.

Lemma unit_caseE :
  CoqInd.destructor_eq unit_constructors unit_case.
Proof. by []. Qed.

Lemma unit_indP P : CoqInd.ind_at P unit_constructors.
Proof. exact: unit_rect. Qed.

Definition unit_coqIndMixin := CoqIndMixin unit_recE unit_caseE unit_indP.
Canonical unit_coqIndType :=
  Eval hnf in CoqIndType _ _ _ unit unit_coqIndMixin.

Definition void_signature : signature A := [::].

Definition void_constructors :
  CoqInd.constructors A_sort void void_signature := tt.

Definition void_rec :
  CoqInd.recursor A_sort void void_signature :=
  fun S => @Empty_set_rect (fun _ => S).

Definition void_case :
  CoqInd.destructor A_sort void void_signature :=
  fun S x => match x with end.

Lemma void_recE :
  CoqInd.recursor_eq void_constructors void_rec.
Proof. by []. Qed.

Lemma void_caseE :
  CoqInd.destructor_eq void_constructors void_case.
Proof. by []. Qed.

Lemma void_indP P : CoqInd.ind_at P void_constructors.
Proof. exact: Empty_set_rect. Qed.

Definition void_coqIndMixin := CoqIndMixin void_recE void_caseE void_indP.
Canonical void_coqIndType :=
  Eval hnf in CoqIndType _ _ _ void void_coqIndMixin.

Definition bool_signature : signature A := [:: [::]; [::]].

Definition bool_constructors :
  CoqInd.constructors A_sort bool bool_signature :=
  (true, (false, tt)).

Definition bool_rec :
  CoqInd.recursor A_sort bool bool_signature :=
  fun S => @bool_rect (fun _ => S).

Definition bool_case :
  CoqInd.destructor A_sort bool bool_signature :=
  fun S ftrue ffalse b => if b then ftrue else ffalse.

Lemma bool_recE : CoqInd.recursor_eq bool_constructors bool_rec.
Proof. by []. Qed.

Lemma bool_caseE : CoqInd.destructor_eq bool_constructors bool_case.
Proof. by []. Qed.

Lemma bool_indP P : CoqInd.ind_at P bool_constructors.
Proof. exact: bool_rect. Qed.

Definition bool_coqIndMixin := CoqIndMixin bool_recE bool_caseE bool_indP.
Canonical bool_coqIndType :=
  Eval hnf in CoqIndType A A_sort _ bool bool_coqIndMixin.

Definition nat_signature : signature A := [:: [::]; [:: Rec]].

Definition nat_constructors :
  CoqInd.constructors A_sort nat nat_signature :=
  (O, (S, tt)).

Definition nat_rec : CoqInd.recursor A_sort nat nat_signature :=
  fun S => @nat_rect (fun _ => S).

Definition nat_case : CoqInd.destructor A_sort nat nat_signature :=
  fun S fz fs n => if n is n.+1 then fs n else fz.

Lemma nat_recE : CoqInd.recursor_eq nat_constructors nat_rec.
Proof. by []. Qed.

Lemma nat_caseE : CoqInd.destructor_eq nat_constructors nat_case.
Proof. by []. Qed.

Lemma nat_indP P : CoqInd.ind_at P nat_constructors.
Proof. exact: nat_rect. Qed.

Definition nat_coqIndMixin := CoqIndMixin nat_recE nat_caseE nat_indP.
Canonical nat_coqIndType := CoqIndType A A_sort _ nat nat_coqIndMixin.

Definition option_signature : signature A :=
  [:: [:: Other a]; [::]].

Definition option_constructors :
  CoqInd.constructors A_sort (option a) option_signature :=
  (@Some a, (@None a, tt)).

Definition option_rec :
  CoqInd.recursor A_sort (option a) option_signature :=
  fun S => @option_rect a (fun _ => S).

Definition option_case :
  CoqInd.destructor A_sort (option a) option_signature :=
  fun S fsome fnone o =>
    if o is Some x then fsome x else fnone.

Lemma option_recE :
  CoqInd.recursor_eq option_constructors option_rec.
Proof. by []. Qed.

Lemma option_caseE :
  CoqInd.destructor_eq option_constructors option_case.
Proof. by []. Qed.

Lemma option_indP P : CoqInd.ind_at P option_constructors.
Proof. exact: option_rect. Qed.

Definition option_coqIndMixin :=
  CoqIndMixin option_recE option_caseE option_indP.
Canonical option_coqIndType :=
  Eval hnf in CoqIndType _ _ _ (option a) option_coqIndMixin.

Definition sum_signature : signature A :=
  [:: [:: Other a1]; [:: Other a2]].

Definition sum_constructors :
  CoqInd.constructors A_sort (a1 + a2)%type sum_signature :=
  (@inl _ _, (@inr _ _, tt)).

Definition sum_rec :
  CoqInd.recursor A_sort (a1 + a2)%type sum_signature :=
  fun S => @sum_rect _ _ (fun _ => S).

Definition sum_case :
  CoqInd.destructor A_sort (a1 + a2)%type sum_signature :=
  fun S finl finr x =>
    match x with inl x => finl x | inr x => finr x end.

Lemma sum_recE : CoqInd.recursor_eq sum_constructors sum_rec.
Proof. by []. Qed.

Lemma sum_caseE : CoqInd.destructor_eq sum_constructors sum_case.
Proof. by []. Qed.

Lemma sum_indP P : CoqInd.ind_at P sum_constructors.
Proof. exact: sum_rect. Qed.

Definition sum_coqIndMixin := CoqIndMixin sum_recE sum_caseE sum_indP.
Canonical sum_coqIndType := Eval hnf in CoqIndType _ _ _ (a1 + a2)%type sum_coqIndMixin.

Definition prod_signature : signature A :=
  [:: [:: Other a1; Other a2]].

Definition prod_constructors :
  CoqInd.constructors A_sort (a1 * a2)%type prod_signature :=
  (@pair _ _, tt).

Definition prod_rec :
  CoqInd.recursor A_sort (a1 * a2)%type prod_signature :=
  fun S => @prod_rect _ _ (fun _ => S).

Definition prod_case :
  CoqInd.destructor A_sort (a1 *  a2)%type prod_signature :=
  fun S c p => let: (x, y) := p in c x y.

Lemma prod_recE : CoqInd.recursor_eq prod_constructors prod_rec.
Proof. by []. Qed.

Lemma prod_caseE : CoqInd.destructor_eq prod_constructors prod_case.
Proof. by []. Qed.

Lemma prod_indP P : CoqInd.ind_at P prod_constructors.
Proof. exact: prod_rect. Qed.

Definition prod_coqIndMixin := CoqIndMixin prod_recE prod_caseE prod_indP.
Canonical prod_coqIndType :=
  Eval hnf in CoqIndType _ _ _ (a1 * a2)%type prod_coqIndMixin.

Definition seq_signature : signature A :=
  [:: [::]; [:: Other a; Rec]].

Definition seq_constructors :
  CoqInd.constructors A_sort (seq a) seq_signature :=
  (@nil _, (@cons _, tt)).

Definition seq_rec :
  CoqInd.recursor A_sort (seq a) seq_signature :=
  fun S => @list_rect _ (fun _ => S).

Definition seq_case :
  CoqInd.destructor A_sort (seq a) seq_signature :=
  fun S fnil fcons l =>
    match l with nil => fnil | cons x y => fcons x y end.

Lemma seq_recE : CoqInd.recursor_eq seq_constructors seq_rec.
Proof. by []. Qed.

Lemma seq_caseE : CoqInd.destructor_eq seq_constructors seq_case.
Proof. by []. Qed.

Lemma seq_indP P : CoqInd.ind_at P seq_constructors.
Proof. exact: list_rect. Qed.

Definition seq_coqIndMixin := CoqIndMixin seq_recE seq_caseE seq_indP.
Canonical seq_coqIndType :=
  Eval hnf in CoqIndType _ _ _ (seq a) seq_coqIndMixin.

End Instances.
