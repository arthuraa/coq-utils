From mathcomp Require Import ssreflect ssrfun ssrbool ssrnat eqtype seq choice.

From extructures Require Import ord.

Require Import void.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Definition cast T (P : T -> Type) x y (e : x = y) : P x -> P y :=
  match e with erefl => id end.

Arguments cast {_} _ {_ _} _.

Notation "e1 * e2" := (etrans e1 e2) : eq_scope.
Notation "e ^-1" := (esym e) : eq_scope.

Notation svalP := proj2_sig.

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

Fixpoint nat_of_fin n : fin n -> nat :=
  match n with
  | 0    => fun i => match i with end
  | n.+1 => fun i => if i is Some i then (nat_of_fin i).+1 else 0
  end.

Lemma leq_nat_of_fin n (i j : fin n) :
  (nat_of_fin i <= nat_of_fin j) = if leq_fin i j is inr b then b else true.
Proof.
elim: n i j=> [[]|n IH] /= [i|] [j|] //.
by rewrite ltnS IH; case: (leq_fin i j).
Qed.

Lemma nat_of_fin_inj n : injective (@nat_of_fin n).
Proof. by elim: n=> [[]|n IH] /= [i|] [j|] // [/IH ->]. Qed.

Fixpoint fin_of_nat n m : option (fin n) :=
  match n with
  | 0 => None
  | n.+1 => if m is m.+1 then if fin_of_nat n m is Some i then Some (Some i) else None
            else Some None
  end.

Lemma nat_of_finK n : pcancel (@nat_of_fin n) (@fin_of_nat n).
Proof.
by elim: n=> [[]|n IH /= [i|]] //=; rewrite IH.
Qed.

Lemma leq_fin_swap n (i j : fin n) :
  leq_fin i j =
  match leq_fin j i with
  | inl e => inl (esym e)
  | inr b => inr (~~ b)
  end.
Proof.
move: (leq_nat_of_fin i j) (leq_nat_of_fin j i).
case: ltngtP=> [||/nat_of_fin_inj ->]; last by rewrite leq_finii.
- case: (leq_fin i j)=> // _ ji <-.
  case: (leq_fin j i) ji => [e|b _ <- //].
  by rewrite {1}e ltnn.
- case: (leq_fin j i)=> // [] [] //=.
  case: (leq_fin i j)=> [e|b _ <- //].
  by rewrite {1}e ltnn.
Qed.

Fixpoint enum_fin n : seq (fin n) :=
  match n with
  | 0 => [::]
  | n.+1 => None :: [seq Some i | i <- enum_fin n]
  end.

Fixpoint size_map T S (f : T -> S) (s : seq T) : size [seq f i | i <- s] = size s :=
  match s with
  | [::] => erefl
  | i :: s => congr1 succn (size_map f s)
  end.

Fixpoint size_enum_fin n : size (enum_fin n) = n :=
  match n with
  | 0 => erefl
  | n.+1 => congr1 succn (size_map Some (enum_fin n) * size_enum_fin n)%EQ
  end.

Definition map_fin (n : nat) T (f : fin n -> T) : seq T :=
  [seq f i | i <- enum_fin n].

Definition cast_fin n m (e : n = m) : forall (i : fin n.+1),
  cast fin (congr1 succn e) i =
  if i is Some j then Some (cast fin e j) else None :=
  match e with
  | erefl => fun i => if i is None then erefl else erefl
  end.

Fixpoint fin_eqMixin n : Equality.mixin_of (fin n) :=
  match n with
  | 0 => void_eqMixin
  | n.+1 => option_eqMixin (EqType _ (fin_eqMixin n))
  end.
Canonical fin_eqType n := EqType (fin n) (fin_eqMixin n).

Fixpoint fin_choiceMixin n : Choice.mixin_of (fin n) :=
  match n with
  | 0 => void_choiceMixin
  | n.+1 => option_choiceMixin (ChoiceType _ (fin_choiceMixin n))
  end.
Canonical fin_choiceType n :=
  Eval hnf in ChoiceType (fin n) (fin_choiceMixin n).

Fixpoint fin_countMixin n : Countable.mixin_of (fin n) :=
  match n with
  | 0 => void_countMixin
  | n.+1 => option_countMixin (CountType _ (fin_countMixin n))
  end.
Canonical fin_countType n :=
  Eval hnf in CountType (fin n) (fin_countMixin n).

Section Ilist.

Variables (T : Type).

Definition ilist n := iter n (prod T) unit.

Fixpoint nth_ilist n : ilist n -> fin n -> T :=
  match n with
  | 0    => fun l i => match i with end
  | n.+1 => fun l i => if i is Some j then nth_ilist l.2 j else l.1
  end.

Fixpoint ilist_of_fun n : forall (f : fin n -> T), ilist n :=
  match n with
  | 0    => fun _ => tt
  | n.+1 => fun f => (f None, ilist_of_fun (fun i => f (Some i)))
  end.

Fixpoint nth_ilist_of_fun n : forall (f : fin n -> T) (i : fin n), nth_ilist (ilist_of_fun f) i = f i :=
  match n with
  | 0    => fun f i => match i with end
  | n.+1 => fun f i => if i is Some j then nth_ilist_of_fun (fun j => f (Some j)) j else erefl
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

Section Hsum.

Variables (I : Type) (T_ : I -> Type).

Implicit Types (i : I) (ix : seq I).

Definition hsum ix : Type :=
  foldr (fun i S => T_ i + S)%type void ix.

Fixpoint hin ix : forall n : fin (size ix), T_ (nth_fin n) -> hsum ix :=
  if ix is i :: ix then
    fun n : fin (size ix).+1 =>
      if n is Some n' then fun x : T_ (nth_fin n') => inr (hin x)
      else fun x => inl x
  else fun n => match n with end.

Fixpoint hcase S ix : (forall n : fin (size ix), T_ (nth_fin n) -> S) -> hsum ix -> S :=
  if ix is i :: ix then
    fun f x =>
      match x with
      | inl x => f None x
      | inr x => hcase (fun n x => f (Some n) x) x
      end
  else fun _ x => match x with end.

Lemma hcaseE S ix
  (f : forall n : fin (size ix), T_ (nth_fin n) -> S)
  (n : fin (size ix))
  (x : T_ (nth_fin n)) : hcase f (hin x) = f n x.
Proof.
by elim: ix f n x=> [_ []|i ix IH] /= f [n|] // x; rewrite IH.
Qed.

End Hsum.

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

(*
Fixpoint hlist_of_fun (f : forall i, T_ i) ix : hlist ix :=
  if ix is i :: ix then (f i, hlist_of_fun f ix) else tt.

Lemma nth_hlist_of_fun f ix n :
  nth_hlist (hlist_of_fun f ix) n = f (nth_fin n).
Proof. elim: ix n=> /= [|i ix IH] // [n|]; by rewrite ?IH. Qed.
*)

Fixpoint seq_of_hlist S ix (f : forall i, T_ i -> S) : hlist ix -> seq S :=
  match ix with
  | [::] => fun _ => [::]
  | i :: ix => fun l => f i l.1 :: seq_of_hlist f l.2
  end.

Fixpoint hlist_of_seq S ix (f : forall i, S -> option (T_ i)) : seq S -> option (hlist ix) :=
  match ix with
  | [::] => fun xs => Some tt
  | i :: ix => fun xs => if xs is x :: xs then
                           match f i x, hlist_of_seq ix f xs with
                           | Some y, Some l => Some (y, l)
                           | _ , _ => None
                           end
                         else None
  end.

Lemma seq_of_hlistK S ix f g :
  (forall i, pcancel (f i) (g i)) ->
  pcancel (@seq_of_hlist S ix f) (@hlist_of_seq S ix g).
Proof.
move=> fK; elim: ix=> [[]|i ix IH /= [x l]] //=.
by rewrite fK IH.
Qed.

Fixpoint seq_of_hlist_in S ix :
  (forall n : fin (size ix), T_ (nth_fin n) -> S) ->
  hlist ix -> seq S :=
  if ix is i :: ix then
    fun f xs => f None xs.1 :: seq_of_hlist_in (fun n => f (Some n)) xs.2
  else fun _ _ => [::].

Fixpoint hlist_of_seq_in S ix (f : forall n : fin (size ix), S -> option (T_ (nth_fin n))) (xs : seq S) {struct xs} : option (hlist ix) :=
  match xs with
  | [::] =>
    match ix return option (hlist ix) with
    | [::] => Some tt
    | _ => None
    end
  | x :: xs =>
    match ix return (forall n : fin (size ix), S -> option (T_ (nth_fin n))) -> option (hlist ix) with
    | [::] => fun _ => None
    | i :: ix => fun f =>
                   match f None x, hlist_of_seq_in (fun n => f (Some n)) xs with
                   | Some y, Some ys => Some (y, ys)
                   | _, _ => None
                   end
    end f
  end.

Lemma seq_of_hlist_inK S ix
  (f : forall n : fin (size ix), T_ (nth_fin n) -> S)
  (g : forall n : fin (size ix), S -> option (T_ (nth_fin n))) :
  (forall n, pcancel (f n) (g n)) ->
  pcancel (seq_of_hlist_in f) (hlist_of_seq_in g).
Proof.
elim: ix f g=> [??? []|i ix IH] //= f g fK [x xs] /=.
by rewrite fK IH // => n ?; rewrite fK.
Qed.

Lemma hlist_of_seq_in_map
  S R ix (f : forall n : fin (size ix), R -> option (T_ (nth_fin n))) (g : S -> R) (xs : seq S) :
  hlist_of_seq_in f [seq g x | x <- xs] = hlist_of_seq_in (fun n x => f n (g x)) xs.
Proof.
elim: ix f xs=> [|i ix IH] /= f [|x xs] //=.
by case: (f None (g x))=> [y|] //=; rewrite IH.
Qed.

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

Definition hmap_in I (T_ S_ : I -> Type) ix :
  (forall n : fin (size ix), T_ (nth_fin n) -> S_ (nth_fin n)) ->
  hlist T_ ix -> hlist S_ ix :=
  fun f l => hlist_of_fun (fun n => f n (nth_hlist l n)).

Fixpoint hpmap_in I (T_ S_ : I -> Type) ix :
  (forall n : fin (size ix), T_ (nth_fin n) -> option (S_ (nth_fin n))) ->
  hlist T_ ix -> option (hlist S_ ix) :=
  match ix with
  | [::] =>
    fun f l => Some tt
  | i :: ix =>
    fun f l => if hpmap_in (fun n => f (Some n)) l.2 is Some l' then
                 if f None l.1 is Some x then
                   Some (x, l')
                 else None
               else None
  end.

Lemma hmap_pinK I (T_ S_ : I -> Type) ix
  (f : forall n : fin (size ix), T_ (nth_fin n) -> S_ (nth_fin n))
  (g : forall n : fin (size ix), S_ (nth_fin n) -> option (T_ (nth_fin n))) :
  (forall n, pcancel (f n) (g n)) -> pcancel (hmap_in f) (hpmap_in g).
Proof.
rewrite /hmap_in; elim: ix f g=> [|i ix IH] //= f g fK => [[]|[x xs]] //=.
rewrite fK (IH (fun n => f (Some n)) (fun n => g (Some n))) //.
move=> n; exact: (fK (Some n)).
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

Variant kind := Other of Type | Rec.

Definition is_other k := if k is Other R then Some R else None.
Definition is_rec k := ~~ (is_other k).

Definition arity := seq kind.
Definition signature := seq arity.

Identity Coercion seq_of_arity : arity >-> seq.
Identity Coercion seq_of_sig : signature >-> seq.

Section ClassLifting.

Variables (K : Type) (sort : K -> Type).

Definition kind_class k :=
  if k is Other T then {sT : K | sort sT = T} else unit.

Record kind_inst := KindInst {
  kind_inst_sort  :> kind;
  kind_inst_class :  kind_class kind_inst_sort
}.

Record arity_inst := ArityInst {
  arity_inst_sort  :> arity;
  arity_inst_class :  hlist kind_class arity_inst_sort;
}.

Record sig_inst := SigInst {
  sig_inst_sort  :> signature;
  sig_inst_class :  hlist (hlist kind_class) sig_inst_sort;
}.

Implicit Types (k : kind) (a : arity) (s : signature).
Implicit Types (ki : kind_inst) (ai : arity_inst) (si : sig_inst).

Canonical Other_kind_inst T :=
  @KindInst (Other (sort T)) (exist _ T erefl).

Canonical Rec_kind_inst :=
  @KindInst Rec tt.

Canonical nth_fin_kind_inst (ai : arity_inst) (i : fin (size ai)) :=
  @KindInst (nth_fin i) (nth_hlist (arity_inst_class ai) i).

Canonical nil_arity_inst :=
  @ArityInst nil tt.

Canonical cons_arity_inst ki ai :=
  @ArityInst (kind_inst_sort ki :: arity_inst_sort ai)
             (kind_inst_class ki, arity_inst_class ai).

Canonical nth_fin_arity_inst (si : sig_inst) (i : fin (size si)) :=
  @ArityInst (nth_fin i) (nth_hlist (sig_inst_class si) i).

Canonical nil_sig_inst :=
  @SigInst nil tt.

Canonical cons_sig_inst ai si :=
  @SigInst (arity_inst_sort ai :: sig_inst_sort si)
           (arity_inst_class ai, sig_inst_class si).

Definition arity_rec (T : arity -> Type)
  (Tnil   : T [::])
  (TOther : forall (R : K) (a : arity), T a -> T (Other (sort R) :: a))
  (TRec   : forall (a : arity), T a -> T (Rec :: a)) :=
  fix arity_rec (a : arity) : hlist kind_class a -> T a :=
    match a with
    | [::]             => fun ac => Tnil
    | Other Rsort :: a => fun ac =>
      cast (fun Rsort => T (Other Rsort :: a)) (svalP ac.1)
           (TOther (sval ac.1) a (arity_rec a ac.2))
    | Rec :: a         => fun ac => TRec a (arity_rec a ac.2)
    end.

Lemma arity_ind (T : forall a, hlist kind_class a -> Type)
  (Tnil : T [::] tt)
  (TOther : forall (R : K) (a : arity) (ac : hlist kind_class a),
      T a ac -> T (Other (sort R) :: a) (exist _ R erefl, ac))
  (TRec : forall (a : arity) (ac : hlist kind_class a),
      T a ac -> T (Rec :: a) (tt, ac))
  (a : arity) (ac : hlist kind_class a) : T a ac.
Proof.
elim: a ac=> [|[Rsort|] a IH] => /= [[]|[[R e] ac]|[[] ac]] //.
  by case: Rsort / e; apply: TOther.
by apply: TRec.
Qed.

End ClassLifting.

Definition type_of_kind S (k : kind) : Type :=
  if k is Other R then R else S.

Definition type_of_kind_map S R (f : S -> R) k :
  type_of_kind S k -> type_of_kind R k :=
  if k is Rec then f else id.

Module CoqInd.

Section Basic.

Variable (T : Type).

Implicit Types (k : kind) (a : arity) (s : signature).

Definition constructors s :=
  hlist (fun a => hfun (type_of_kind T) a T) s.

Fixpoint branch S a : Type :=
  match a with
  | Other R :: ks => R      -> branch S ks
  | Rec     :: ks => T -> S -> branch S ks
  | [::]          => S
  end.

Definition recursor s := forall S, hfun (branch S) s (T -> S).

Fixpoint branch_of_hfun S a :
  hfun (type_of_kind (T * S)) a S -> branch S a :=
  match a with
  | Other R :: a => fun f x   => branch_of_hfun (f x)
  | Rec     :: a => fun f x y => branch_of_hfun (f (x, y))
  | [::]         => fun f     => f
  end.

Fixpoint hfun_of_branch S a :
  branch S a -> hfun (type_of_kind (T * S)) a S :=
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
  all_hlist (fun args : hlist (type_of_kind T) (nth_fin i) =>
    r S bs (nth_hlist cs i args) =
    hfun_of_branch (nth_hlist bs i)
                   (hmap (type_of_kind_map (fun x => (x, r S bs x))) args)))).

Definition destructor s :=
  forall S, hfun (fun a => hfun (type_of_kind T) a S) s (T -> S).

Definition destructor_eq s (cs : constructors s) (d : destructor s) :=
  forall S,
  all_hlist (fun bs : hlist (fun ks => hfun (type_of_kind T) ks S) s =>
  all_fin   (fun i : fin (size s) =>
  all_hlist (fun args : hlist (type_of_kind T) (nth_fin i) =>
    d S bs (nth_hlist cs i args) = nth_hlist bs i args))).

Fixpoint ind_branch (P : T -> Type) a :
  hfun (type_of_kind T) a T -> Type :=
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

Record type := Pack {sort : Type; class : mixin_of sort}.
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

Module CoqIndFunctor.

Section TypeDef.

Import CoqInd.

Variables (s : signature).

Record type T := CoqInd {
  constr : fin (size s);
  args : hlist (type_of_kind T) (nth_fin constr)
}.

Arguments CoqInd {_} _ _.

Local Notation F := type.

Definition fmap T S (f : T -> S) (x : F T) : F S :=
  CoqInd (constr x) (hmap (type_of_kind_map f) (args x)).

Lemma fmap_eq T S (f g : T -> S) : f =1 g -> fmap f =1 fmap g.
Proof.
by move=> e [i args]; congr CoqInd; apply: hmap_eq; case.
Qed.

Lemma fmap1 T : @fmap T T id =1 id.
Proof.
move=> [i args] /=; congr CoqInd; rewrite -[RHS]hmap1.
by apply: hmap_eq; case.
Qed.

Lemma fmap_comp T S R (f : T -> S) (g : S -> R) :
  fmap (g \o f) =1 fmap g \o fmap f.
Proof.
move=> [i args] /=; congr CoqInd; rewrite /= hmap_comp.
by apply: hmap_eq; case.
Qed.

Canonical coqInd_functor := Functor fmap_eq fmap1 fmap_comp.

Lemma inj T (i : fin (size s)) (a b : hlist (type_of_kind T) (nth_fin i)) :
  CoqInd i a = CoqInd i b -> a = b.
Proof.
pose get x :=
  if leq_fin (constr x) i is inl e then
    cast (fun j : fin (size s) => hlist (type_of_kind T) (nth_fin j)) e (args x)
  else a.
by move=> /(congr1 get); rewrite /get /= leq_finii /=.
Qed.

Variable T : coqIndType s.

Definition Roll (x : F T) : T :=
  nth_hlist (@Cons _ _ T) (constr x) (args x).

Definition branches_of_fun S (body : F (T * S)%type -> S) :=
  hlist_of_fun (fun i =>
    branch_of_hfun
      (hcurry
         (fun l => body (CoqInd i l)))).

Definition rec S (body : F (T * S)%type -> S) :=
  happ (@CoqInd.rec _ _ T S) (branches_of_fun body).

Definition case S (body : F T -> S) :=
  happ (@CoqInd.case _ _ T S)
       (hlist_of_fun
          (fun i =>
             hcurry
               (fun l =>
                  body (CoqInd i l)))).

Lemma recE S f a : @rec S f (Roll a) =
                   f (fmap (fun x => (x, rec f x)) a).
Proof.
case: a=> [i args]; have := CoqInd.recE T S.
move/all_hlistP/(_ (branches_of_fun f)).
move/all_finP/(_ i).
move/all_hlistP/(_ args).
rewrite /rec /Roll => -> /=.
by rewrite /= nth_hlist_of_fun branch_of_hfunK hcurryK.
Qed.

Lemma caseE S f a : case f (Roll a) = f a :> S.
Proof.
case: a => [i args]; have := CoqInd.caseE T S.
move/all_hlistP.
move/(_ (hlist_of_fun (fun i => hcurry (fun l => f (CoqInd i l))))).
move/all_finP/(_ i).
move/all_hlistP/(_ args).
rewrite /case /Roll => -> /=.
by rewrite nth_hlist_of_fun hcurryK.
Qed.

Lemma indP P :
  (forall (a : F {x & P x}), P (Roll (fmap tag a))) ->
  forall x, P x.
Proof.
rewrite /Roll.
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
  forall args : hlist (type_of_kind {x : S & P x}) (nth_fin j),
    P (nth_hlist Cons j (hmap (type_of_kind_map tag) args)).
  by move=> args; move: (hyps (CoqInd j args)).
elim: (nth_fin j) (nth_hlist Cons j) hyps=> [|[i|] ks IH] //=.
- by move=> ? /(_ tt).
- move=> c hyps x; apply: IH=> args.
  exact: (hyps (x, args)).
- move=> constr hyps x H; apply: IH=> args.
  exact: (hyps (existT _ x H, args)).
Qed.

Canonical indType :=
  Eval hnf in IndType coqInd_functor T (IndMixin recE caseE indP).

End TypeDef.

End CoqIndFunctor.

Canonical CoqIndFunctor.coqInd_functor.
Canonical CoqIndFunctor.indType.
Coercion CoqIndFunctor.indType : coqIndType >-> indType.

Module IndEqType.

Local Notation kind_class := (kind_class Equality.sort).
Local Notation kind_inst := (kind_inst Equality.sort).
Local Notation arity_inst := (arity_inst Equality.sort).
Local Notation sig_inst := (sig_inst Equality.sort).

Section EqType.

Variable (s : sig_inst).
Let F := CoqIndFunctor.coqInd_functor s.
Variable (T : indType F).

Let eq_op_branch a (ac : hlist kind_class a) :
  hlist (type_of_kind (T * (T -> bool))) a ->
  hlist (type_of_kind T)                 a ->
  bool :=
  @arity_rec _ _ (fun a => hlist _ a -> hlist _ a -> bool)
    (fun _ _ => true)
    (fun R a rec x y => (x.1 == y.1) && rec x.2 y.2)
    (fun   a rec x y => x.1.2 y.1 && rec x.2 y.2) a ac.

Let eq_op : T -> T -> bool :=
  rec (fun args1 =>
         case
           (fun args2 =>
              match leq_fin (CoqIndFunctor.constr args2) (CoqIndFunctor.constr args1) with
              | inl e =>
                eq_op_branch
                  (nth_hlist (sig_inst_class s) (CoqIndFunctor.constr args1))
                  (CoqIndFunctor.args args1)
                  (cast (hlist (type_of_kind T) \o @nth_fin _ _) e (CoqIndFunctor.args args2))
              | inr _ => false
              end)).

Lemma eq_opP : Equality.axiom eq_op.
Proof.
elim/indP=> [[i_x xargs]] y.
rewrite /eq_op recE /= -[rec _]/(eq_op) /=.
rewrite -[y]unrollK caseE; move: {y} (unroll y)=> [i_y yargs] /=.
case le: (leq_fin i_y i_x)=> [e|b]; last first.
  constructor=> /Roll_inj /= [] e _.
  by move: le; rewrite e leq_finii.
case: i_x / e xargs {le} => /= xargs.
apply/(@iffP (hmap (type_of_kind_map tag) xargs = yargs)); first last.
- by move=> /Roll_inj /CoqIndFunctor.inj.
- by move=> <-.
elim/arity_ind: {i_y} (nth_fin i_y) / (nth_hlist _ _) xargs yargs=> //=.
- by move=> _ []; constructor.
- move=> R a ac IH [x xargs] [y yargs] /=.
  apply/(iffP andP)=> [[/eqP ? /IH ?]|[/eqP ? /IH]];
  intuition (eauto; congruence).
- move=> a ac IH [[x xP] xargs] [y yargs] /=.
  apply/(iffP andP)=> [[/xP ? /IH ?]|[/xP ? /IH ?]];
  intuition (eauto; congruence).
Qed.

End EqType.

Record type (F : functor) := Pack {
  sort      : Type;
  eq_class  : Equality.class_of sort;
  ind_class : Ind.mixin_of sort F;
}.

Definition eqType F (T : type F) := Equality.Pack (eq_class T).
Definition indType F (T : type F) := Ind.Pack (ind_class T).

Definition eqMixin :=
  fun (T : Type) =>
  fun s (sT : coqIndType s) & phant_id (CoqInd.sort sT) T =>
  fun (ss : sig_inst) & phant_id s (sig_inst_sort ss) =>
  fun (cT : CoqInd.mixin_of ss T) & phant_id (CoqInd.class sT) cT =>
    ltac:(
      let ax := constr:(@eq_opP ss (CoqInd.Pack cT)) in
      match type of ax with
      | Equality.axiom ?e =>
        let e' := eval compute -[eq_op Equality.sort andb] in e in
        exact: @EqMixin T e' ax
      end).

Module Import Exports.
Notation "[ 'indEqMixin' 'for' T ]" :=
  (let m := @eqMixin T _ _ id _ id _ id in
   ltac:(
     let x := eval hnf in m in
     exact x))
  (at level 0, format "[ 'indEqMixin'  'for'  T ]") : form_scope.
Notation indEqType := type.
Coercion sort : type >-> Sortclass.
Coercion eqType : type >-> Equality.type.
Canonical eqType.
Coercion indType : type >-> Ind.type.
Canonical indType.
End Exports.

End IndEqType.

Export IndEqType.Exports.

Section TreeOfCoqInd.

Variables (s : signature).
Let F := CoqIndFunctor.coqInd_functor s.
Variables (T : indType F).

Import GenTree.

Definition coq_ind_arg :=
  hsum (hsum (type_of_kind void)) s.

Definition mk_coq_ind_arg (i : fin (size s)) (j : fin (size (nth_fin i))) :
  type_of_kind void (nth_fin j) -> coq_ind_arg :=
  fun x => hin (hin x).

Definition proj_coq_ind_arg
  (i : fin (size s)) (j : fin (size (nth_fin i))) (x : coq_ind_arg) :
  option (type_of_kind void (nth_fin j)) :=
  hcase (fun i' =>
    if leq_fin i' i is inl e then
      match e^-1 in _ = i'
      return (hsum (fun k => type_of_kind void k) (nth_fin i') -> option _) with
      | erefl =>
        hcase (fun j' =>
          if leq_fin j' j is inl e then
            match e^-1 in _ = j'
            return (type_of_kind void (nth_fin j') -> option _)
            with
            | erefl => fun x => Some x
            end
          else fun _ => None)
      end
    else fun _ => None) x.

Lemma mk_coq_ind_argK i j : pcancel (@mk_coq_ind_arg i j) (@proj_coq_ind_arg i j).
Proof.
by move=> x; rewrite /proj_coq_ind_arg hcaseE leq_finii /= hcaseE leq_finii.
Qed.

Let wrap (i : fin (size s)) (j : fin (size (nth_fin i))) :
  type_of_kind (tree coq_ind_arg) (nth_fin j) -> tree coq_ind_arg :=
  match nth_fin j as k
  return (type_of_kind void k -> coq_ind_arg) ->
         type_of_kind (tree coq_ind_arg) k -> tree coq_ind_arg
  with
  | Other R => fun c x => Leaf (c x)
  | Rec     => fun c x => x
  end (@mk_coq_ind_arg i j).

Definition tree_of_coq_ind (x : T) : tree coq_ind_arg :=
  rec (fun x =>
         let i := CoqIndFunctor.constr x in
         Node (nat_of_fin i)
           (seq_of_hlist_in (@wrap i)
              (hmap (type_of_kind_map snd) (CoqIndFunctor.args x)))) x.

Fixpoint coq_ind_of_tree (x : tree coq_ind_arg) : option T :=
  match x with
  | Leaf _ => None
  | Node c args =>
    if fin_of_nat (size s) c is Some i then
      let args := [seq (t, coq_ind_of_tree t) | t <- args] in
      if hlist_of_seq_in (fun j ts =>
                            match nth_fin j as k
                                  return (coq_ind_arg -> option (type_of_kind void k)) ->
                                         option (type_of_kind T k) with
                            | Other R => fun f => if ts.1 is Leaf x then f x else None
                            | Rec => fun _ => ts.2
                            end (@proj_coq_ind_arg i j)) args is Some args then
        Some (Roll (CoqIndFunctor.CoqInd args))
      else None
    else None
  end.

Lemma tree_of_coq_indK : pcancel tree_of_coq_ind coq_ind_of_tree.
Proof.
elim/indP=> [[i args]].
rewrite /tree_of_coq_ind recE /= -[rec _]/(tree_of_coq_ind).
rewrite nat_of_finK !hmap_comp /=.
set args' := hlist_of_seq_in _ _.
suffices -> : args' = Some (hmap (type_of_kind_map tag) args) by [].
rewrite {}/args' hlist_of_seq_in_map /= /wrap.
move: (@mk_coq_ind_arg i) (@proj_coq_ind_arg i) (@mk_coq_ind_argK i).
elim: {i} (nth_fin i) args=> [|[R|] a IH] //= args C p CK.
  by rewrite CK IH //= => j x; rewrite CK.
case: args=> [[x xP] args] /=; rewrite xP IH //.
by move=> j ?; rewrite CK.
Qed.

End TreeOfCoqInd.

Definition pack_tree_of_coq_indK :=
  fun (T : Type) =>
  fun s (sT_ind : coqIndType s) & phant_id (CoqInd.sort sT_ind) T =>
  @tree_of_coq_indK _ sT_ind.

Notation "[ 'indChoiceMixin' 'for' T ]" :=
  (PcanChoiceMixin (@pack_tree_of_coq_indK T _ _ id))
  (at level 0, format "[ 'indChoiceMixin'  'for'  T ]") : form_scope.

Notation "[ 'indCountMixin' 'for' T ]" :=
  (PcanCountMixin (@pack_tree_of_coq_indK T _ _ id))
  (at level 0, format "[ 'indCountMixin'  'for'  T ]") : form_scope.

Module IndOrdType.

Local Notation kind_class := (kind_class Ord.sort).
Local Notation kind_inst := (kind_inst Ord.sort).
Local Notation arity_inst := (arity_inst Ord.sort).
Local Notation sig_inst := (sig_inst Ord.sort).

Section OrdType.

Variable (s : sig_inst).
Let F := CoqIndFunctor.coqInd_functor s.
Variable (T : indEqType F).

Definition leq_branch a (ac : hlist kind_class a) :
  hlist (type_of_kind (T * (T -> bool))) a ->
  hlist (type_of_kind T)                 a ->
  bool :=
  @arity_rec
    _ _ (fun a => hlist (type_of_kind (T * (T -> bool))) a -> hlist (type_of_kind T) a -> bool)
    (fun _ _ => true)
    (fun R a rec x y =>
       if x.1 == y.1 then rec x.2 y.2 else (x.1 <= y.1)%ord)
    (fun   a rec x y =>
       if x.1.1 == y.1 then rec x.2 y.2 else x.1.2 y.1) a ac.

Definition leq : T -> T -> bool :=
  rec (fun args1 =>
         case
           (fun args2 =>
              match leq_fin (CoqIndFunctor.constr args2) (CoqIndFunctor.constr args1) with
              | inl e =>
                leq_branch
                  (nth_hlist (sig_inst_class s) (CoqIndFunctor.constr args1))
                  (CoqIndFunctor.args args1)
                  (cast (hlist (type_of_kind T) \o @nth_fin _ _) e (CoqIndFunctor.args args2))
              | inr b => ~~ b
              end)).

Lemma leqP : Ord.axioms leq.
Proof.
have anti: antisymmetric leq.
  elim/indP=> [[i_x xargs]] y.
  rewrite -(unrollK y); case: {y} (unroll y)=> [i_y yargs].
  rewrite /leq !recE -[rec _]/(leq) /= !caseE /=.
  case ie: (leq_fin i_y i_x) (leq_nat_of_fin i_y i_x)=> [e|b].
    case: i_x / e {ie} xargs=> xargs _ /=; rewrite leq_finii /= => h.
    congr (Roll (CoqIndFunctor.CoqInd _))=> /=.
    elim/arity_ind: {i_y} (nth_fin i_y) / (nth_hlist _ _) xargs yargs h
        => [[] []|R a ac IH|a ac IH] //=.
      case=> [x xargs] [y yargs] /=.
      rewrite eq_sym; case: (altP (_ =P _))=> [-> /IH ->|yx] //.
      by move=> /Ord.anti_leq e; rewrite e eqxx in yx.
    case=> [[x xP] xargs] [y yargs] /=.
    rewrite eq_sym; case: (altP (_ =P _))=> [-> /IH ->|yx /xP e] //.
    by rewrite e eqxx in yx.
  case: (leq_fin i_x i_y) (leq_nat_of_fin i_x i_y)=> [e|b'].
    by rewrite e leq_finii in ie.
  move=> <- <-.
  have ne: nat_of_fin i_y != nat_of_fin i_x.
    by apply/eqP=> /nat_of_fin_inj e; rewrite e leq_finii in ie.
    by case: ltngtP ne.
split=> //.
- elim/indP=> [[i args]].
  rewrite /leq recE /= -[rec _]/(leq) caseE leq_finii /=.
  elim/arity_ind: {i} _ / (nth_hlist _ _) args=> [[]|R a ac IH|a ac IH] //=.
    by case=> [x args]; rewrite /= eqxx.
  by case=> [[x xP] args] /=; rewrite eqxx.
- move=> y x z; elim/indP: x y z=> [[i_x xargs]] y z.
  rewrite -(unrollK y) -(unrollK z).
  move: (unroll y) (unroll z)=> {y z} [i_y yargs] [i_z zargs].
  rewrite /leq !recE /= -[rec _]/(leq) !caseE /=.
  case: (leq_fin i_y i_x) (leq_nat_of_fin i_y i_x)=> [e _|b] //.
    case: i_x / e xargs=> /= xargs.
    case: (leq_fin i_z i_y) (leq_nat_of_fin i_z i_y)=> [e _|b] //.
      case: i_y / e xargs yargs => xargs yargs /=.
      elim/arity_ind: {i_z} _ / (nth_hlist _ _) xargs yargs zargs => [//|R|] a ac IH /=.
        case=> [x xargs] [y yargs] [z zargs] /=.
        case: (altP (_ =P _)) => [<-|xy].
          case: ifP=> // /eqP _; exact: IH.
        case: (altP (_ =P _)) => [<-|yz]; first by rewrite (negbTE xy).
        case: (altP (_ =P _)) => [<-|xz]; last exact: Ord.leq_trans.
        move=> c1 c2; suffices e: x = y by rewrite e eqxx in xy.
        by have /andP/Ord.anti_leq := conj c1 c2.
      case=> [[x xP] xargs] [y yargs] [z zargs] /=.
      case: (altP (x =P y))=> [<-|xy].
        case: (altP (x =P z))=> [_|//]; exact: IH.
      case: (altP (x =P z))=> [<-|yz].
        rewrite eq_sym (negbTE xy)=> le1 le2.
        suffices e : x = y by rewrite e eqxx in xy.
        by apply: anti; rewrite le1.
      case: (altP (_ =P _))=> [<-|_] //; exact: xP.
  move=> <- {b} i_xy.
  case: (leq_fin i_z i_y) (leq_nat_of_fin i_z i_y)=> [e _|_ <-].
    case: i_y / e yargs i_xy=> /= yargs.
    by rewrite leq_nat_of_fin; case: (leq_fin i_z i_x).
  case: (leq_fin i_z i_x) (leq_nat_of_fin i_z i_x)=> [e|_ <-].
    by case: i_x / e i_xy xargs; rewrite -ltnNge => /ltnW ->.
  move: i_xy; rewrite -!ltnNge; exact: ltn_trans.
- elim/indP=> [[i_x xargs]] y.
  rewrite -(unrollK y); case: {y} (unroll y)=> [i_y yargs].
  rewrite /leq !recE /= -[rec _]/(leq) !caseE /= (leq_fin_swap i_x i_y).
  case: (leq_fin i_y i_x)=> [e|[] //].
  case: i_x / e xargs=> /= xargs.
  elim/arity_ind: {i_y} _ / (nth_hlist _ _) xargs yargs=> [[] []|R|] //= a ac IH.
    case=> [x xargs] [y yargs] /=.
    rewrite eq_sym; case: (altP eqP)=> [{y} _|]; first exact: IH.
    by rewrite Ord.leq_total.
  case=> /= [[x xP] xargs] [y yargs] /=.
  by rewrite eq_sym; case: (altP eqP).
Qed.

End OrdType.

Definition ordMixin :=
  fun (T : Type) =>
  fun (b : Choice.class_of T) bT & phant_id (Choice.class bT) b =>
  fun s (sT : coqIndType s) & phant_id (CoqInd.sort sT) T =>
  fun (ss : sig_inst) & phant_id s (sig_inst_sort ss) =>
  fun (cT : CoqInd.mixin_of ss T) & phant_id (CoqInd.class sT) cT =>
    ltac:(
      let ax := constr:(@leqP _ (IndEqType.Pack b (Ind.class (CoqInd.Pack cT)))) in
      match type of ax with
      | Ord.axioms ?e =>
        let e' := (eval compute -[Ord.leq eq_op Equality.sort Choice.sort Ord.sort Ord.eqType andb] in e) in
        exact: @OrdMixin T e' ax
      end).

Module Import Exports.
Notation "[ 'indOrdMixin' 'for' T ]" :=
  (let m := @ordMixin T _ _ id _ _ id _ id _ id in
   ltac:(
     let x := eval hnf in m in
     exact x))
  (at level 0, format "[ 'indOrdMixin'  'for'  T ]") : form_scope.
End Exports.

End IndOrdType.

Export IndOrdType.Exports.

Section Instances.

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

Module Example.

Inductive tree (T : Type) :=
| Leaf of nat
| Node of T & tree T & tree T.
Arguments Leaf {_} _.

Definition tree_signature (T : Type) : signature :=
  [:: [:: Other nat]; [:: Other T; Rec; Rec]].

Definition tree_constructors (T : Type) :
  CoqInd.constructors (tree T) (tree_signature T) :=
  (@Leaf T, (@Node T, tt)).

Definition tree_case (T : Type) :
  CoqInd.destructor (tree T) (tree_signature T) :=
  fun S fLeaf fNode t =>
    match t with Leaf n => fLeaf n | Node x t1 t2 => fNode x t1 t2 end.

Lemma tree_recE T : CoqInd.recursor_eq (tree_constructors T) (fun S => @tree_rect T (fun _ => S)).
Proof. by []. Qed.

Lemma tree_caseE T : CoqInd.destructor_eq (tree_constructors T) (@tree_case T).
Proof. by []. Qed.

Lemma tree_indP T P : CoqInd.ind_at P (tree_constructors T).
Proof. exact: tree_rect. Qed.

Definition tree_coqIndMixin T :=
  Eval cbv delta [tree_constructors tree_signature tree_case] in
  CoqIndMixin (@tree_recE T) (@tree_caseE T) (@tree_indP T).
Canonical tree_coqIndType T :=
  Eval hnf in CoqIndType _ (tree T) (tree_coqIndMixin T).

Definition tree_eqMixin (T : eqType) :=
  Eval simpl in [indEqMixin for tree T].
Canonical tree_eqType (T : eqType) :=
  Eval hnf in EqType (tree T) (tree_eqMixin T).
Definition tree_choiceMixin (T : choiceType) :=
  [indChoiceMixin for tree T].
Canonical tree_choiceType (T : choiceType) :=
  Eval hnf in ChoiceType (tree T) (tree_choiceMixin T).
Definition tree_countMixin (T : countType) :=
  [indCountMixin for tree T].
Canonical tree_countType (T : countType) :=
  Eval hnf in CountType (tree T) (tree_countMixin T).
Definition tree_ordMixin (T : ordType) :=
  Eval simpl in [indOrdMixin for tree T].
Set Printing Implicit.
Canonical tree_ordType (T : ordType) :=
  Eval hnf in OrdType (tree T) (tree_ordMixin T).

End Example.
