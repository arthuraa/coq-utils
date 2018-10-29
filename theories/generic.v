From mathcomp Require Import ssreflect ssrfun ssrbool ssrnat eqtype seq.

From extructures Require Import ord.

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

Record indType (F : functor) := IndType {
  ind_sort :> Type;
  Roll     :  F ind_sort -> ind_sort;
  case     :  forall T, (F ind_sort -> T) -> ind_sort -> T;
  rec      :  forall T, (F (ind_sort * T)%type -> T) -> ind_sort -> T;
  _        :  forall T f a, rec f (Roll a) =
                            f (fmap (fun x => (x, rec f x)) a) :> T;
  _        :  forall T f a, case f (Roll a) = f a :> T;
  _        :  forall P,
                (forall (a : F {x & P x}), P (Roll (fmap tag a))) ->
                forall x, P x
}.

Section IndTheory.

Variable F : functor.
Variable T : indType F.

Local Notation Roll := (@Roll F T).
Local Notation case := (@case F T).
Local Notation rec  := (@rec F T).

Lemma recE S f a : rec f (Roll a) =
                   f (fmap (fun x => (x, rec f x)) a) :> S.
Proof. by rewrite /Roll /rec; case: (T) f a. Qed.

Lemma caseE S f a : case f (Roll a) = f a :> S.
Proof. by rewrite /Roll /case; case: (T) f a. Qed.

Lemma indP P :
  (forall (a : F {x & P x}), P (Roll (fmap tag a))) ->
  forall x, P x.
Proof. by rewrite /Roll /rec; case: (T) P. Qed.

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

Section PolyFunctor.

Variables (I : Type) (T_ : I -> Type).

Variant kind := Other of I | Rec.

Implicit Types (k : kind) (ks : seq kind).

Variable s : seq (seq kind).

Definition type_of_arg S (k : kind) : Type :=
  if k is Other i then T_ i else S.

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

Arguments Rec {_}.

Section IndEqType.

Variables (I : Type) (K_ : I -> eqType).
Variables (s : seq (seq (kind I))) (T : indType (polyf_functor K_ s)).

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
                       (cast (fun i => hlist (type_of_arg K_ T) (nth_fin i))
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

End IndEqType.


Module CoqInd.

Section ClassDef.

Variable (I : Type) (K_ : I -> Type) (T : Type).
Implicit Types (ks : seq (kind I)) (s : seq (seq (kind I))).

Fixpoint rbranch S ks : Type :=
  match ks with
  | Other i :: ks => K_ i   -> rbranch S ks
  | Rec     :: ks => T -> S -> rbranch S ks
  | [::]          => S
  end.

Definition recursor s :=
  forall S, hfun (rbranch S) s (T -> S).

Definition constructors s :=
  hlist (fun ks => hfun (type_of_arg K_ T) ks T) s.

Fixpoint rbranch_of_hfun S ks :
  hfun (type_of_arg K_ (T * S)) ks S -> rbranch S ks :=
  match ks with
  | Other i :: ks => fun f x   => rbranch_of_hfun (f x)
  | Rec     :: ks => fun f x y => rbranch_of_hfun (f (x, y))
  | [::]          => fun f     => f
  end.

Fixpoint hfun_of_rbranch S ks :
  rbranch S ks -> hfun (type_of_arg K_ (T * S)) ks S :=
  match ks with
  | Other i :: ks => fun f x => hfun_of_rbranch (f x)
  | Rec     :: ks => fun f p => hfun_of_rbranch (f p.1 p.2)
  | [::]          => fun f   => f
  end.

Lemma rbranch_of_hfunK S ks f args :
  hfun_of_rbranch (@rbranch_of_hfun S ks f) args = f args.
Proof.
by elim: ks f args=> [|[R|] ks IH] f //= [[x y] args] //.
Qed.

Definition rbranches_of_hfun S s (body : polyf K_ s (T * S) -> S) :=
  hlist_of_fun (fun i => rbranch_of_hfun (hcurry (fun l => body (Polyf l)))).

Definition rec_of_U s (r : recursor s) S (body : polyf K_ s (T * S) -> S) :=
  happ (r S) (rbranches_of_hfun body).

Definition Roll_of_U s (cs : constructors s) (x : polyf K_ s T) :=
  nth_hlist cs (pconstr x) (pargs x).

Definition recursor_eq s (cs : constructors s) (r : recursor s) :=
  forall S,
  all_hlist (fun bs : hlist (rbranch S) s =>
  all_fin   (fun n : fin (size s) =>
  all_hlist (fun args : hlist (type_of_arg K_ T) (nth_fin n) =>
    r S bs (nth_hlist cs n args) =
    hfun_of_rbranch (nth_hlist bs n)
                   (hmap (type_of_arg_map (fun x => (x, r S bs x))) args)))).

Lemma recursor_eqP s cs r :
  @recursor_eq s cs r ->
  forall S f a, @rec_of_U s r S f (Roll_of_U cs a) =
                f (fmap (fun x => (x, @rec_of_U s r S f x)) a).
Proof.
move=> H S f [i args]; move/(_ S): H.
move/all_hlistP/(_ (rbranches_of_hfun f)).
move/all_finP/(_ i).
move/all_hlistP/(_ args).
rewrite /rec_of_U /Roll_of_U => -> /=.
rewrite /poly_fmap /=; move: (hmap _ _)=> l.
by rewrite /rbranches_of_hfun nth_hlist_of_fun rbranch_of_hfunK hcurryK.
Qed.

Definition destructor s :=
  forall S, hfun (fun ks => hfun (type_of_arg K_ T) ks S) s (T -> S).

Definition case_of_U s (d : destructor s) S (body : polyf K_ s T -> S) :=
  happ (d S) (hlist_of_fun (fun i => hcurry (fun l => body (Polyf l)))).

Definition destructor_eq s (cs : constructors s) (d : destructor s) :=
  forall S,
  all_hlist (fun bs : hlist (fun ks => hfun (type_of_arg K_ T) ks S) s =>
  all_fin   (fun n : fin (size s) =>
  all_hlist (fun args : hlist (type_of_arg K_ T) (nth_fin n) =>
    d S bs (nth_hlist cs n args) = nth_hlist bs n args))).

Lemma destructor_eqP s cs d :
  @destructor_eq s cs d ->
  forall S f a, @case_of_U s d S f (Roll_of_U cs a) =
                f a.
Proof.
move=> H S f [i args]; move/(_ S): H.
move/all_hlistP/(_ (hlist_of_fun (fun i => hcurry (fun l => f (Polyf l))))).
move/all_finP/(_ i).
move/all_hlistP/(_ args).
rewrite /case_of_U /Roll_of_U => -> /=.
by rewrite nth_hlist_of_fun hcurryK.
Qed.

Fixpoint ind_rbranch (P : T -> Type) ks :
  hfun (type_of_arg K_ T) ks T -> Type :=
  match ks with
  | Other i :: ks => fun c => forall x : K_ i,     ind_rbranch P (c x)
  | Rec     :: ks => fun c => forall x : T, P x -> ind_rbranch P (c x)
  | [::]          => fun c => P c
  end.

Fixpoint ind_at (P : T -> Type) s : constructors s -> Type :=
  match s with
  | ks :: s => fun cs => ind_rbranch P cs.1 -> ind_at P cs.2
  | [::]    => fun cs => forall x, P x
  end.

Lemma ind_atP s cs :
  (forall P : T -> Type, @ind_at P s cs) ->
  forall (P : T -> Type),
    (forall (args : polyf K_ s {x & P x}),
        P (Roll_of_U cs (poly_fmap tag args))) ->
  forall x, P x.
Proof.
move=> indP P; move/(_ P) in indP.
have {indP} indP:
    (forall i, ind_rbranch P (nth_hlist cs i)) ->
    (forall x, P x).
  elim: s cs indP=> [|ks s IH] //= [c cs] /= indP hyps.
  move: (hyps None)=> /indP/IH; apply=> i.
  exact: (hyps (Some i)).
rewrite /Roll_of_U; move=> hyps; apply: indP=> j.
have {hyps} hyps:
  forall args : hlist (type_of_arg K_ {x : T & P x}) (nth_fin j),
    P (nth_hlist cs j (hmap (type_of_arg_map tag) args)).
  move=> args; exact: (hyps (Polyf args)).
elim: (nth_fin j) (nth_hlist cs j) hyps=> {cs} [|[i|] ks IH] //=.
- by move=> ? /(_ tt).
- move=> c hyps x; apply: IH=> args.
  exact: (hyps (x, args)).
- move=> constr hyps x H; apply: IH=> args.
  exact: (hyps (existT _ x H, args)).
Qed.

Variables (s : seq (seq (kind I))).
Variables (cs : constructors s) (r : recursor s) (d : destructor s).
Hypothesis Hr : recursor_eq cs r.
Hypothesis Hd : destructor_eq cs d.
Hypothesis Hind : forall P, ind_at P cs.

Definition IndType :=
  IndType (recursor_eqP Hr) (destructor_eqP Hd) (ind_atP Hind).

End ClassDef.

End CoqInd.

Definition CoqIndType := CoqInd.IndType.

Section Seq.

Definition seq_sig : seq (seq (kind (fin 1))) :=
  [:: [::]; [:: Other None; Rec]].

Definition seq_constructors T := (@nil T, (@cons T, tt)).

Definition seq_indType T :=
  @CoqIndType (fin 1) (@nth_fin _ [:: T]) (seq T)
              seq_sig
              (seq_constructors T)
              (fun S => @list_rect T (fun _ => S))
              (fun S fnil fcons x =>
                 match x with
                 | nil => fnil
                 | cons a b => fcons a b
                 end).

End Seq.
