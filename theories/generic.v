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

Record type F := Pack {sort : Type; _ : class_of sort F}.
Local Coercion sort : type >-> Sortclass.
Variables (F : functor) (T : Type) (cT : type F).
Definition class := let: Pack _ c as cT' := cT return class_of cT' F in c.
Definition clone c of phant_id class c := @Pack F T c.
Let xT := let: Pack T _ := cT in T.
Notation xclass := (class : class_of xT).

Definition pack c := @Pack F T c.

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

Section Ilist.

Variables (T : Type).

Definition ilist n := iter n (prod T) unit.

Fixpoint nth_ilist n : ilist n -> fin n -> T :=
  match n with
  | 0    => fun l i => match i with end
  | n.+1 => fun l i => if i is Some j then nth_ilist l.2 j else l.1
  end.

Fixpoint ilist_of_seq s : ilist (size s) :=
  match s with
  | [::] => tt
  | x :: s => (x, ilist_of_seq s)
  end.

Fixpoint seq_of_ilist n : ilist n -> seq T :=
  match n with
  | 0    => fun l => [::]
  | n.+1 => fun l => l.1 :: seq_of_ilist l.2
  end.

End Ilist.

Fixpoint imap T S (f : T -> S) n : ilist T n -> ilist S n :=
  match n with
  | 0    => fun l => tt
  | n.+1 => fun l => (f l.1, imap f l.2)
  end.

Lemma imap_eq (T S : Type) (f g : T -> S) :
  f =1 g ->
  forall n, @imap _ _ f n =1 @imap _ _ g n.
Proof.
by move=> efg; elim=> [[]|n IH] // [x l] /=; rewrite efg IH.
Qed.

Lemma imap1 (T: Type) n (l : ilist T n) : imap id l = l.
Proof.
by elim: n l=> /= [[]|n IH] // [x l] /=; rewrite IH.
Qed.

Lemma imap_comp (T S R : Type)
                (f : T -> S) (g : S -> R) n (l : ilist T n) :
  imap g (imap f l) = imap (g \o f) l.
Proof.
by elim: n l=> [[]|n IH] //= [x l] /=; rewrite IH.
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

Section PolyFunctor.

Variables (n : nat) (A : fin n -> Type) (ns : fin n -> nat).

Record polyf T := Polyf {
  pconstr : fin n;
  pargs   : A pconstr;
  prargs  : ilist T (ns pconstr)
}.

Definition poly_fmap T S (f : T -> S) (x : polyf T) : polyf S :=
  Polyf (pargs x) (imap f (prargs x)).

Lemma poly_fmap_eq S R (f g : S -> R) :
  f =1 g ->
  poly_fmap f =1 poly_fmap g.
Proof.
move=> efg [c args rargs] /=; rewrite /poly_fmap /=; congr Polyf.
exact/imap_eq.
Qed.

Lemma poly_fmap1 S (x : polyf S) : poly_fmap id x = x.
Proof.
rewrite /poly_fmap; case: x=> i args rargs /=; by rewrite imap1.
Qed.

Lemma poly_fmap_comp T S R f (g : S -> R) (x : polyf T) :
  poly_fmap (g \o f) x = poly_fmap g (poly_fmap f x).
Proof.
by case: x=> [i args rargs]; rewrite /poly_fmap /= imap_comp.
Qed.

Canonical polyf_functor :=
  Functor poly_fmap_eq poly_fmap1 poly_fmap_comp.

Lemma Polyf_inj T i a1 r1 a2 r2 :
  @Polyf T i a1 r1 = @Polyf _ i a2 r2 -> (a1, r1) = (a2, r2).
Proof.
pose get x :=
  if leq_fin (pconstr x) i is inl e then
    cast (fun k : fin n => A k * ilist T (ns k))%type
         e (pargs x, prargs x)
  else (a1, r1).
by move=> /(f_equal get); rewrite /get /= leq_finii /=.
Qed.

End PolyFunctor.

Arguments Polyf {_ _ _ _} _ _ _.

Variant kind := Other of Type | Rec.

Definition is_other k := if k is Other R then Some R else None.
Definition is_rec k := ~~ (is_other k).

Module CoqInd.

Section Basic.

Variable (T : Type).

Definition arity := seq kind.
Definition signature := seq arity.

Implicit Types (k : kind) (a : arity) (s : signature).

Definition type_of_arg S (k : kind) : Type :=
  if k is Other R then R else S.

Definition type_of_arg_map S R (f : S -> R) k :
  type_of_arg S k -> type_of_arg R k :=
  if k is Rec then f else id.

Definition constructors s :=
  hlist (fun a => hfun (type_of_arg T) a T) s.

Fixpoint branch S a : Type :=
  match a with
  | Other R :: ks => R      -> branch S ks
  | Rec     :: ks => T -> S -> branch S ks
  | [::]          => S
  end.

Definition recursor s := forall S, hfun (branch S) s (T -> S).

Fixpoint branch_of_hfun S a :
  hfun (type_of_arg (T * S)) a S -> branch S a :=
  match a with
  | Other R :: a => fun f x   => branch_of_hfun (f x)
  | Rec     :: a => fun f x y => branch_of_hfun (f (x, y))
  | [::]         => fun f     => f
  end.

Fixpoint hfun_of_branch S a :
  branch S a -> hfun (type_of_arg (T * S)) a S :=
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
  all_hlist (fun args : hlist (type_of_arg T) (nth_fin i) =>
    r S bs (nth_hlist cs i args) =
    hfun_of_branch (nth_hlist bs i)
                   (hmap (type_of_arg_map (fun x => (x, r S bs x))) args)))).

Definition destructor s :=
  forall S, hfun (fun a => hfun (type_of_arg T) a S) s (T -> S).

Definition destructor_eq s (cs : constructors s) (d : destructor s) :=
  forall S,
  all_hlist (fun bs : hlist (fun ks => hfun (type_of_arg T) ks S) s =>
  all_fin   (fun i : fin (size s) =>
  all_hlist (fun args : hlist (type_of_arg T) (nth_fin i) =>
    d S bs (nth_hlist cs i args) = nth_hlist bs i args))).

Fixpoint ind_branch (P : T -> Type) a :
  hfun (type_of_arg T) a T -> Type :=
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

Variables (s : signature).

Record mixin_of T := Mixin {
  Cons      : constructors T s;
  rec       : recursor T s;
  case      : destructor T s;
  _         : recursor_eq Cons rec;
  _         : destructor_eq Cons case;
  _         : forall P, ind_at P Cons;
}.

Record type := Pack {sort : Type; class : @mixin_of sort}.
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
Notation CoqIndType s T m := (@Pack s T m).
Notation CoqIndMixin := Mixin.
End Exports.

End CoqInd.
Export CoqInd.Exports.

Section CoqIndTheory.

Import CoqInd.

Variables (s : signature).
Variable T : coqIndType s.

Fixpoint args_of_arity a : Type :=
  match a with
  | Other R :: a => R * args_of_arity a
  | Rec     :: a => args_of_arity a
  | [::]         => unit
  end.

Fixpoint rargs_of_arity a : Type :=
  match a with
  | Other R :: a => args_of_arity a
  | Rec     :: a => T * args_of_arity a
  | [::]         => unit
  end.

Fixpoint proj_args S a : hlist (type_of_arg S) a -> args_of_arity a :=
  match a with
  | Other R :: a => fun l => (l.1, proj_args l.2)
  | Rec     :: a => fun l => proj_args l.2
  | [::]         => fun l => l
  end.

Fixpoint proj_rargs S a : hlist (type_of_arg S) a -> ilist S (count is_rec a) :=
  match a with
  | Other R :: a => fun l => proj_rargs l.2
  | Rec     :: a => fun l => (l.1, proj_rargs l.2)
  | [::]         => fun l => l
  end.

Fixpoint pack_args S a : args_of_arity a -> ilist S (count is_rec a) -> hlist (type_of_arg S) a :=
  match a with
  | Other R :: a => fun args rargs => (args.1, @pack_args S a args.2 rargs)
  | Rec     :: a => fun args rargs => (rargs.1, @pack_args S a args rargs.2)
  | [::]         => fun args rargs => tt
  end.

Lemma proj_args_pack S a args rargs :
  proj_args (@pack_args S a args rargs) = args.
Proof.
elim: a args rargs=> [[]|[R|] a IH] //=.
by case=> [??] ?; rewrite IH.
Qed.

Lemma proj_rargs_pack S a args rargs :
  proj_rargs (@pack_args S a args rargs) = rargs.
Proof.
elim: a args rargs=> [_ []|[R|] a IH] //=.
by move=> ? [??]; rewrite IH.
Qed.

Lemma hmap_pack S R (f : S -> R) a args rargs :
  hmap (type_of_arg_map f) (@pack_args _ a args rargs) =
  pack_args args (imap f rargs).
Proof.
elim: a args rargs=> [|[?|] a IH] //=.
- by move=> [??] ?; rewrite IH.
- by move=> ? [??]; rewrite IH.
Qed.

Let F :=
  (@polyf_functor (size s)
                  (fun k => args_of_arity (nth_fin k))
                  (fun k => count is_rec (nth_fin k))).

Definition coqInd_Roll (x : F T) :=
  nth_hlist (@Cons _ _ T) (pconstr x) (pack_args (pargs x) (prargs x)).

Definition branches_of_fun S (body : F (T * S)%type -> S) :=
  hlist_of_fun (fun i =>
    branch_of_hfun
      (hcurry
         (fun l => body (Polyf i (proj_args l) (proj_rargs l))))).

Definition coqInd_rec S (body : F (T * S)%type -> S) :=
  happ (@CoqInd.rec _ _ T S) (branches_of_fun body).

Definition coqInd_case S (body : F T -> S) :=
  happ (@CoqInd.case _ _ T S)
       (hlist_of_fun
          (fun i =>
             hcurry
               (fun l =>
                  body (Polyf i (proj_args l) (proj_rargs l))))).

Lemma coqInd_recE S f a : @coqInd_rec S f (coqInd_Roll a) =
                          f (fmap (fun x => (x, coqInd_rec f x)) a).
Proof.
case: a=> [i args rargs]; have := CoqInd.recE T S.
move/all_hlistP/(_ (branches_of_fun f)).
move/all_finP/(_ i).
move/all_hlistP/(_ (pack_args args rargs)).
rewrite /coqInd_rec /coqInd_Roll => -> /=.
rewrite /poly_fmap /= nth_hlist_of_fun branch_of_hfunK hcurryK.
by rewrite !hmap_pack proj_args_pack proj_rargs_pack.
Qed.

Lemma coqInd_caseE S f a : coqInd_case f (coqInd_Roll a) = f a :> S.
Proof.
case: a => [i args rargs]; have := CoqInd.caseE T S.
move/all_hlistP.
move/(_ (hlist_of_fun (fun i => hcurry (fun l => f (Polyf i (proj_args l) (proj_rargs l)))))).
move/all_finP/(_ i).
move/all_hlistP/(_ (pack_args args rargs)).
rewrite /coqInd_case /coqInd_Roll => -> /=.
by rewrite nth_hlist_of_fun hcurryK proj_args_pack proj_rargs_pack.
Qed.

Lemma coqInd_indP P :
  (forall (a : F {x & P x}), P (coqInd_Roll (fmap tag a))) ->
  forall x, P x.
Proof.
rewrite /coqInd_Roll.
case: (T) P => S [/= Cons _ _ _ _ indP] P.
have {indP} indP:
    (forall i, CoqInd.ind_branch P (nth_hlist Cons i)) ->
    (forall x, P x).
  move/(_ P): indP.
  elim: (s) Cons=> [|a s' IH] //= [c cs] /= indP hyps.
  move: (hyps None)=> /indP/IH; apply=> i.
  exact: (hyps (Some i)).
move=> hyps; apply: indP=> j.
have {hyps} hyps:
  forall (args : args_of_arity (nth_fin j))
         (rargs : ilist {x & P x} (count is_rec (nth_fin j))),
    P (nth_hlist Cons j (hmap (type_of_arg_map tag) (pack_args args rargs))).
  move=> args rargs.
  move: (hyps (Polyf j args rargs)); by rewrite hmap_pack.
elim: (nth_fin j) (nth_hlist Cons j) hyps=> [|[i|] ks IH] //=.
- by move=> ? /(_ tt tt).
- move=> c hyps x; apply: IH=> args.
  exact: (hyps (x, args)).
- move=> constr hyps x H; apply: IH=> args rargs.
  exact: (hyps args (existT _ x H, rargs)).
Qed.

Definition coqInd_indMixin :=
  IndMixin coqInd_recE coqInd_caseE coqInd_indP.
Canonical coqInd_indType :=
  Eval hnf in IndType F T coqInd_indMixin.

End CoqIndTheory.

Module IndEqType.

Section ClassDef.

Record class_of T F := Class {
  base : Equality.class_of T;
  mixin : Ind.mixin_of T F
}.

Record type F :=
  Pack {sort : Type; _ : class_of sort F; _ : Type}.
Local Coercion sort : type >-> Sortclass.

Variables (F : functor) (T : Type) (cT : type F).
Definition class :=
  let: Pack _ c _ as cT' := cT return class_of cT' F in c.
Definition clone c of phant_id class c := @Pack F T c T.
Let xT := let: Pack T _ _ := cT in T.
Notation xclass := (class : class_of xT F).

Definition pack c := @Pack F T c T.

Definition eqType := @Equality.Pack cT (base xclass).
Definition indType := @Ind.Pack F cT (mixin xclass).

End ClassDef.

Section Exports.
Coercion sort : type >-> Sortclass.
Coercion eqType : type >-> Equality.type.
Coercion indType : type >-> Ind.type.
Notation indEqType := type.
End Exports.

End IndEqType.

Section GenericEqType.

Variable (s : seq (eqType * nat)).
Let F := (@polyf_functor (size s)
                         (fun i => (nth_fin i).1)
                         (fun i => (nth_fin i).2)).
Variable (T : indType F).

Definition ind_eq : T -> T -> bool :=
  rec (fun args1 x2 =>
         let args2 := unroll x2 in
         match leq_fin (pconstr args2) (pconstr args1) with
         | inl e =>
           (pargs args1 == (cast _ e (pargs args2))) &&
           all id [seq p.1.2 p.2
                  | p <- zip (seq_of_ilist (prargs args1))
                             (seq_of_ilist (prargs args2))]
         | inr _ => false
         end).

Lemma ind_eqP : Equality.axiom ind_eq.
Proof.
elim/indP=> [[i_x xargs x]] y.
rewrite /ind_eq recE /= -[rec _]/(ind_eq) /poly_fmap /=.
rewrite -{1}[y]unrollK; move: {y} (unroll y)=> [i_y yargs y] /=.
case le: (leq_fin i_y i_x)=> [e|b]; last first.
  constructor=> /Roll_inj /= [] e _ _.
  by move: le; rewrite e leq_finii.
case: i_x / e xargs x {le} => /= xargs x.
apply/(@iffP (xargs = yargs /\ imap tag x = y)); first last.
- by move=> /Roll_inj e; case: (Polyf_inj e)=> -> ->.
- by move=> [<- <-].
apply/(iffP andP).
- case=> [/eqP -> e]; split=> //.
  elim: {i_y yargs xargs} (nth_fin i_y).2 x y e=> [[] []|n IH] //=.
  by case=> [[/= x Px] xs] [y ys] /= /andP [/Px -> /IH ->].
- case=> [-> <-]; split=> //.
  elim: {i_y y yargs xargs} (nth_fin i_y).2 x=> [[]|n IH] //=.
  case=> [[/= x Px] xs]; apply/andP; split; [exact/Px|exact/IH].
Qed.

Definition CoqIndEqMixin := EqMixin ind_eqP.

End GenericEqType.

Section Instances.

Import CoqInd.

Variables (a a1 a2 : Type).

Definition unit_signature : signature := [:: [::]].

Definition unit_constructors :
  CoqInd.constructors unit unit_signature := (tt, tt).

Definition unit_rec :
  CoqInd.recursor unit unit_signature :=
  fun S => @unit_rect (fun _ => S).

Definition unit_case :
  CoqInd.destructor unit unit_signature :=
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
  Eval hnf in CoqIndType _ unit unit_coqIndMixin.

Definition void_signature : signature := [::].

Definition void_constructors :
  CoqInd.constructors void void_signature := tt.

Definition void_rec :
  CoqInd.recursor void void_signature :=
  fun S => @Empty_set_rect (fun _ => S).

Definition void_case :
  CoqInd.destructor void void_signature :=
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
  Eval hnf in CoqIndType _ void void_coqIndMixin.

Definition bool_signature : signature := [:: [::]; [::]].

Definition bool_constructors :
  CoqInd.constructors bool bool_signature :=
  (true, (false, tt)).

Definition bool_rec :
  CoqInd.recursor bool bool_signature :=
  fun S => @bool_rect (fun _ => S).

Definition bool_case :
  CoqInd.destructor bool bool_signature :=
  fun S ftrue ffalse b => if b then ftrue else ffalse.

Lemma bool_recE : CoqInd.recursor_eq bool_constructors bool_rec.
Proof. by []. Qed.

Lemma bool_caseE : CoqInd.destructor_eq bool_constructors bool_case.
Proof. by []. Qed.

Lemma bool_indP P : CoqInd.ind_at P bool_constructors.
Proof. exact: bool_rect. Qed.

Definition bool_coqIndMixin := CoqIndMixin bool_recE bool_caseE bool_indP.
Canonical bool_coqIndType :=
  Eval hnf in CoqIndType _ bool bool_coqIndMixin.

Definition nat_signature : signature := [:: [::]; [:: Rec]].

Definition nat_constructors :
  CoqInd.constructors nat nat_signature :=
  (O, (S, tt)).

Definition nat_rec : CoqInd.recursor nat nat_signature :=
  fun S => @nat_rect (fun _ => S).

Definition nat_case : CoqInd.destructor nat nat_signature :=
  fun S fz fs n => if n is n.+1 then fs n else fz.

Lemma nat_recE : CoqInd.recursor_eq nat_constructors nat_rec.
Proof. by []. Qed.

Lemma nat_caseE : CoqInd.destructor_eq nat_constructors nat_case.
Proof. by []. Qed.

Lemma nat_indP P : CoqInd.ind_at P nat_constructors.
Proof. exact: nat_rect. Qed.

Definition nat_coqIndMixin := CoqIndMixin nat_recE nat_caseE nat_indP.
Canonical nat_coqIndType := CoqIndType _ nat nat_coqIndMixin.

Definition option_signature : signature :=
  [:: [:: Other a]; [::]].

Definition option_constructors :
  CoqInd.constructors (option a) option_signature :=
  (@Some a, (@None a, tt)).

Definition option_rec :
  CoqInd.recursor (option a) option_signature :=
  fun S => @option_rect a (fun _ => S).

Definition option_case :
  CoqInd.destructor (option a) option_signature :=
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
  Eval hnf in CoqIndType _ (option a) option_coqIndMixin.

Definition sum_signature : signature :=
  [:: [:: Other a1]; [:: Other a2]].

Definition sum_constructors :
  CoqInd.constructors (a1 + a2)%type sum_signature :=
  (@inl _ _, (@inr _ _, tt)).

Definition sum_rec :
  CoqInd.recursor (a1 + a2)%type sum_signature :=
  fun S => @sum_rect _ _ (fun _ => S).

Definition sum_case :
  CoqInd.destructor (a1 + a2)%type sum_signature :=
  fun S finl finr x =>
    match x with inl x => finl x | inr x => finr x end.

Lemma sum_recE : CoqInd.recursor_eq sum_constructors sum_rec.
Proof. by []. Qed.

Lemma sum_caseE : CoqInd.destructor_eq sum_constructors sum_case.
Proof. by []. Qed.

Lemma sum_indP P : CoqInd.ind_at P sum_constructors.
Proof. exact: sum_rect. Qed.

Definition sum_coqIndMixin := CoqIndMixin sum_recE sum_caseE sum_indP.
Canonical sum_coqIndType := Eval hnf in CoqIndType _ (a1 + a2)%type sum_coqIndMixin.

Definition prod_signature : signature :=
  [:: [:: Other a1; Other a2]].

Definition prod_constructors :
  CoqInd.constructors (a1 * a2)%type prod_signature :=
  (@pair _ _, tt).

Definition prod_rec :
  CoqInd.recursor (a1 * a2)%type prod_signature :=
  fun S => @prod_rect _ _ (fun _ => S).

Definition prod_case :
  CoqInd.destructor (a1 *  a2)%type prod_signature :=
  fun S c p => let: (x, y) := p in c x y.

Lemma prod_recE : CoqInd.recursor_eq prod_constructors prod_rec.
Proof. by []. Qed.

Lemma prod_caseE : CoqInd.destructor_eq prod_constructors prod_case.
Proof. by []. Qed.

Lemma prod_indP P : CoqInd.ind_at P prod_constructors.
Proof. exact: prod_rect. Qed.

Definition prod_coqIndMixin := CoqIndMixin prod_recE prod_caseE prod_indP.
Canonical prod_coqIndType :=
  Eval hnf in CoqIndType _ (a1 * a2)%type prod_coqIndMixin.

Definition seq_signature : signature :=
  [:: [::]; [:: Other a; Rec]].

Definition seq_constructors :
  CoqInd.constructors (seq a) seq_signature :=
  (@nil _, (@cons _, tt)).

Definition seq_rec :
  CoqInd.recursor (seq a) seq_signature :=
  fun S => @list_rect _ (fun _ => S).

Definition seq_case :
  CoqInd.destructor (seq a) seq_signature :=
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
  Eval hnf in CoqIndType _ (seq a) seq_coqIndMixin.

End Instances.
