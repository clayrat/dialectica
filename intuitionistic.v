(** Goedel's "Dialectica" functional interpretation of logic, slightly generalized and
   adapted for Coq.

   As a starting point we take chapter VI, "Goedel's Functional Interpretation", by J.
   Avigad and S. Feferman from "Handbook of Proof Theory", edited by S.R. Buss, published
   by Elsevier Science, 1995. A preliminary draft is available at
   http://www.andrew.cmu.edu/user/avigad/Papers/dialect.pdf.

   Author: Andrej Bauer, http://andrej.com/
*)

From Coq Require Import ssreflect ssrbool ssrfun Eqdep_dec.
From mathcomp Require Import ssrnat eqtype.

Set Bullet Behavior "None".
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

(** * Basic definitions *)

(** We shall allow universal and existential quantification over arbitrary inhabited types.
    The usual interpretation allows quantification over the natural numbers (and possibly
    functionals over the natural numbers), which are of course inhabited. *)

Record Inhabited := inhabit { ty :> Set; member : ty }.

(** The inhabited natural numbers. *)

Definition N := inhabit 0.

(** The inductive type [prp] is a "deep embedding" of the abstract syntax of
    the object language that we shall interpret into Coq. We admit only decidable primitive
    predicates, as is usual in the basic Dialectica variant.

    Our embedding allows us to express "exotic" propositional functions [p : ty -> prp] in
    which the logical structure of [p x] may depend on [x]. Because of this phenomenon we
    will be forced later on to introduce certain type dependencies where there are none in
    the usual Dialectica interpretation. *)

Inductive prp : Type :=
  | primitive : forall p : bool, prp
  | conjunction : prp -> prp -> prp
  | disjunction : prp -> prp -> prp
  | implication : prp -> prp -> prp
  | negation : prp -> prp
  | universal : forall {ty : Inhabited}, (ty -> prp) -> prp
  | existential : forall {ty : Inhabited}, (ty -> prp) -> prp.

(** Convenient notation for the object language. *)

Notation "'[' p ']'" := (primitive p) (at level 80, no associativity).
Notation "'neg' x" := (negation x) (at level 70, no associativity).
Notation "x 'and' y" := (conjunction x y) (at level 74, left associativity).
Notation "x 'or' y" := (disjunction x y) (at level 76, left associativity).
Notation "x ==>> y" := (implication x y) (at level 78, right associativity).
Notation "'all' x : t , p" :=  (@universal t (fun x => p)) (at level 80, x at level 99).
Notation "'some' x : t , p" :=  (@existential t (fun x => p)) (at level 80, x at level 99).

(** With each proposition [p] we associate the types [W p] and [C p] of "witnesses" and
    "counters", respectively. Think of them as moves in a game between a player [W] and an
    opponent [C]. We make two changes to the standard Dialectica representation.

    First, we use sum for counters of conjunctions, where normally a product is used. This
    gives us symmetry between conjunction and disjunction, simplifies the notorious
    conjunction contraction [and_contr], but complicates the adjunction between implication
    and conjunction. Thomas Streicher pointed out that the change is inessential in the
    sense that we could prove a separate lemma which allows us to pass from counters for [p
    and q] as pairs to counters as elements of a sum (such a lemma relies in decidability
    of the [dia] relation defined below).

    Second, because we allow the structure of a propositional function to depend on the
    argument, we are forced to introduce type dependency into [W p] and [C p] when [p] is a
    quantified statement. This is not a big surprise, but what is a little more surprising
    is that the counters for existentials, [C (existential ty p')], involve a dependency
    not only on [ty] but also on [W (p' x)]. The dependency is needed in the rule
    [exists_elim]. The rest of Dialectica interpetation is not influenced by this change,
    with the exception of the Independence of Premise where we have to impose a condition
    that is not required in the usual interpretation.

    These type-dependencies clearly point towards an even more type-dependent Dialectica variant.
    Indeed, we are going to investigate it in a separate file. For now we are just trying
    to faithfully represent the Dialectica interpretation. *)

Fixpoint W (p : prp) : Set :=
  match p with
     | primitive p => unit
     | conjunction p1 p2 => (W p1) * (W p2)
     | disjunction p1 p2 => (W p1) + (W p2)
     | implication p1 p2 => (W p1 -> W p2) * (W p1 * C p2 -> C p1)
     | negation p' => W p' -> C p'
     | universal ty p' => forall x : ty, W (p' x)
     | existential ty p' => { x : ty & W (p' x) }
  end

with C p : Set :=
  match p with
     | primitive p => unit
     | conjunction p1 p2 => (C p1) + (C p2)
     | disjunction p1 p2 => (C p1) * (C p2)
     | implication p1 p2 => (W p1) * (C p2)
     | negation p' => W p'
     | universal ty p' => { x : ty & C (p' x) }
     | existential ty p' => forall x : ty, W (p' x) -> C (p' x)
   end.

(** The types [W] and [C] are always inhabited because we restrict quantifiers to inhabited
    types. *)

Definition WC_member (p : prp) : W p * C p.
elim: p=>//=.
- by move=>?[??]?[??]; do!split=>//; right.
- by move=>?[??]?[??]; do!split=>//; left.
- by move=>?[??]?[??].
- by move=>?[??].
- move=>ty ? H; split.
  - by move=>x; case: (H x).
  - by exists (member ty); case: (H (member ty)).
- move=>ty ? H; split.
- by exists (member ty); case: (H (member ty)).
- by move=>x ?; case: (H x).
Defined.

Definition W_member (p : prp) := (WC_member p).1.
Definition C_member (p : prp) := (WC_member p).2.

(** The relation [dia p w c] is what is usually written as [p_D] in the Dialectica
    interpretation, i.e., the matrix of the interpreted formula.

    In terms of games, [dia p w c] tells whether the player move [w] wins against the
    opponent move [c] in the game determined by the proposition [p].
*)

Fixpoint dia (p : prp) : W p -> C p -> Prop :=
  match p return W p -> C p -> Prop with
    | primitive p => fun _ _ => p
    | conjunction p1 p2 =>
      fun a b => match b with
                    | inl b1 => dia a.1 b1
                    | inr b2 => dia a.2 b2
                  end
    | disjunction p1 p2 =>
      fun a b => match a with
                    | inl x => dia x b.1
                    | inr u => dia u b.2
                  end
    | implication p1 p2 =>
      fun a b => dia b.1 (a.2 b) -> dia (a.1 b.1) b.2
    | negation p' =>
      fun a b => ~ dia b (a b)
    | universal _ p' =>
      fun a b => dia (a (projT1 b)) (projT2 b)
    | existential _ p' =>
      fun a b => dia (projT2 a) (b (projT1 a) (projT2 a))
  end.

(** The [dia] relation is decidable. This fact is used only in the adjunction between
    conjunction and implication.

    (Actually, it's also used for the validity of induction).
*)

Fixpoint diab (p : prp) : W p -> C p -> bool :=
  match p return W p -> C p -> bool with
    | primitive p => fun _ _ => p
    | conjunction p1 p2 =>
      fun a b => match b with
                    | inl b1 => diab a.1 b1
                    | inr b2 => diab a.2 b2
                  end
    | disjunction p1 p2 =>
      fun a b => match a with
                    | inl x => diab x b.1
                    | inr u => diab u b.2
                  end
    | implication p1 p2 =>
      fun a b => diab b.1 (a.2 b) ==> diab (a.1 b.1) b.2
    | negation p' =>
      fun a b => ~~ diab b (a b)
    | universal _ p' =>
      fun a b => diab (a (projT1 b)) (projT2 b)
    | existential _ p' =>
      fun a b => diab (projT2 a) (b (projT1 a) (projT2 a))
  end.

Lemma diaP (p : prp) (a : W p) (b : C p) : reflect (dia a b) (diab a b).
Proof.
elim: p a b=>//=.
- by move=>? _ _; exact: idP.
- by move=>? H1 ? H2 ?; case=>?; [exact: H1|exact: H2].
- by move=>? H1 ? H2; case=>??; [exact: H1|exact: H2].
- move=>? H1 ? H2 ??; case: H1=>/=; last by move=>H; apply: ReflectT=>?; exfalso; apply: H.
  by case: H2=>/= D1 ?; [apply: ReflectT | apply: ReflectF=>H; apply/D1/H].
- by move=>? H ??; case: H=>/= ?; [apply: ReflectF|apply: ReflectT].
Qed.

(** Of course, a decidable proposition is stable for double negation. *)

Lemma dia_not_not_stable (p : prp) (w : W p) (c : C p) : ~ ~ dia w c -> dia w c.
Proof.
by move/classicP=>H; apply/diaP/H => /diaP.
Qed.

(** The predicate [valid p] is the Dialectica interpretation of [p]. It says that there is
    [w] such that [dia p w c] holds for any [c]. In terms of games semantics this means
    that [W] has a winning strategy (which amounts to a winning move [w]). *)

Definition valid (p : prp) := { a : W p | forall b : C p, dia a b }.

(** * Validity of inference rules *)

(** We now verify that the Hilbert-style axioms for first-order logic are validated by our
    interpretation. We follow Avigad & Feferman. *)

Theorem modus_ponens (p q : prp) : valid p -> valid (p ==>> q) -> valid q.
Proof.
rewrite /valid /=; case=>wp H; case; case=>u ? /= G.
exists (u wp)=>b.
by apply/(G (_, _))/H.
Qed.

Theorem impl_chain (p q r : prp) : valid (p ==>> q) -> valid (q ==>> r) -> valid (p ==>> r).
Proof.
rewrite /valid /=; case; case=>a b /= H; case; case=>c d /= G.
exists (fun w => c (a w), fun v => b (v.1, d (a v.1, v.2)))=>/= g ?.
apply: (G (a g.1, g.2))=>/=.
by apply: (H (g.1, d (a g.1, g.2))).
Qed.

Theorem or_contr (p : prp) : valid (p or p ==>> p).
Proof.
rewrite /valid /=.
exists (fun x => (match x with inl a => a | inr a => a end), fun x => (x.2, x.2))=>/=.
by case; case.
Qed.

(** In the following theorem we avoid decidability of [dia] because we defined
    counters of conjunctions as sums. *)

Theorem and_contr (p : prp) : valid (p ==>> p and p).
Proof.
rewrite /valid /=.
exists (fun x => (x,x),
        fun y => match y.2 with inl c => c | inr c => c end)=>/=.
by case=>?; case.
Qed.

Theorem or_introl (p q : prp) : valid (p ==>> p or q).
Proof.
rewrite /valid /=.
by exists (inl, fst \o snd).
Qed.

Theorem and_eliml (p q : prp) : valid (p and q ==>> p).
Proof.
rewrite /valid /=.
by exists (fst, inl \o snd).
Qed.

Theorem or_comm (p q : prp) : valid (p or q ==>> q or p).
Proof.
rewrite /valid /=.
exists (fun x => match x with inl a => inr a | inr b => inl b end,
        fun y => (y.2.2, y.2.1))=>/=.
by case; case.
Qed.

Theorem and_comm (p q : prp) : valid (p and q ==>> q and p).
Proof.
rewrite /valid /=.
exists (fun x => (x.2, x.1),
        fun y => match y.2 with inl c => inr c | inr c => inl c end)=>/=.
by case=>?; case.
Qed.

Theorem or_distr (p q r : prp) : valid (p ==>> q) -> valid (r or p ==>> r or q).
Proof.
rewrite /valid /=; case; case=>a b /= H.
exists (fun x => match x with inl t => inl t | inr u => inr (a u) end,
        fun y => match y.1 with
                   | inl i => (y.2.1, b (W_member p, y.2.2))
                   | inr j => (y.2.1, b (j         , y.2.2))
                 end)=>/=.
case; case=>?[??] //= ?.
by apply: (H (_,_)).
Qed.

(** The next two theorems verify the adjunction between conjunction and implication. This is
    where we need decidability of [dia p w c] and inhabitation of [W] and [C]. *)

Theorem impl_conj_adjunct1 (p q r : prp) : valid (p ==>> (q ==>> r)) -> valid (p and q ==>> r).
Proof.
rewrite /valid /=; case; case=>a b /= H.
exists (fun x => (a x.1).1 x.2,
        fun (y : W p * W q * C r) =>
          let: ((wp, wq), cr) := y in
          if diab wq ((a wp).2 (wq, cr))
          then inl (b (wp, (wq, cr)))
          else inr ((a wp).2 (wq, cr)))=>/=.
move=>[[??]?].
case: (diaP _ ((a _).2 _))=>//= ??.
by apply: (H (_,(_,_))).
Qed.

Theorem impl_conj_adjunct2 (p q r : prp) : valid (p and q ==>> r) -> valid (p ==>> (q ==>> r)).
Proof.
rewrite /valid /=; case; case=>a b /= H.
exists (fun x => (fun u => a (x, u),
                  fun v => match b ((x, v.1), v.2) with
                              | inl c => C_member q
                              | inr d => d
                            end),
        fun y => match b ((y.1, y.2.1), y.2.2) with
                   | inl c => c
                   | inr d => C_member p
                 end)=>/=.
move=>[?[??]] /= F G.
apply: (H (_,_,_))=>/=; move: F G.
by case: (b _).
Qed.

Theorem false_elim (p : prp) : valid ([false] ==>> p).
Proof.
rewrite /valid /=.
exists (fun _ => W_member p, fun _ => tt)=>/=.
by move=>?.
Qed.

Theorem forall_intro {ty : Inhabited} (p : prp) (q : ty -> prp) :
  (forall x : ty, valid (p ==>> q x)) -> valid (p ==>> all x : ty, q x).
Proof.
rewrite /valid /= =>H.
exists (fun u x => (projT1 (H x)).1 u,
        fun (y : W p * {x : ty & C (q x)}) =>
          (projT1 (H (projT1 y.2))).2 (y.1, projT2 y.2)).
move=>[?[??]] /= H0.
case: H H0=>/= ? H.
by apply: H (_,_).
Qed.

Theorem forall_elim {ty : Inhabited} (a : ty) (p : ty -> prp) :
  valid ((all x : ty, p x) ==>> p a).
Proof.
rewrite /valid /=.
by exists (fun f => f a, fun y => existT _ a y.2).
Qed.

Theorem exists_intro {ty : Inhabited} (a : ty) (p : ty -> prp) :
  valid (p a ==>> some x : ty, p x).
Proof.
rewrite /valid /=.
by exists (fun x => existT _ a x, fun y => y.2 a y.1).
Qed.

(** This is the rule in which we need the dependency of counters in existential statements. *)

Theorem exists_elim {ty : Inhabited} (p : ty -> prp) (q : prp) :
  (forall x : ty, valid (p x ==>> q)) -> valid ((some x : ty, p x) ==>> q).
Proof.
rewrite /valid /= => H.
exists (fun (u : {x : ty & W (p x)}) => (projT1 (H (projT1 u))).1 (projT2 u),
        fun v x w => (projT1 (H x)).2 (w, v.2)).
move=>[[??]?] /= H0.
case: H H0=>/= ? H.
by apply: H (_,_).
Qed.

(** * Equality

      Next we verify the rules of equality. To keep things simple we only consider equality
      of natural numbers. In the general case we could consider decidable equality on an
      inhabited type. *)

Definition prpEq (m n : nat) := [m == n].

(** Dialectica equality implies equality. *)

Theorem prpEq_eq (m n : N) : valid (prpEq m n) -> m = n.
Proof.
rewrite /prpEq /valid /=; case=>_ H.
by apply/eqP/H.
Qed.

(** Reflexivity. *)

Theorem prpEq_refl (n : N) : valid (prpEq n n).
Proof. by rewrite /valid /= eq_refl. Qed.

(** Equality implies Dialectica equality, of course *)

Theorem eq_prpEq (m n : N) : m = n -> valid (prpEq m n).
Proof. by move=>->; exact: prpEq_refl. Qed.

(** Leibniz's law as a rule of inference. *)

Theorem leibniz_rule (p : N -> prp) (m n : N) :
  valid (prpEq m n) -> valid (p m) -> valid (p n).
Proof. by rewrite /valid /=; case=>_ H; move/eqP: (H tt)=>->. Qed.

(** Proving Leibniz's law as a proposition is more complicated because of type dependency
    that is not present in the usual Dialectica interpretation.

   We need UIP (Uniqueness of Identity Proofs) for natural numbers here. *)

Lemma eqN_decidable (m n : nat) : decidable (m = n).
Proof.
  revert m n.
  induction m; induction n; [left|right|right|]; auto.
  destruct (IHm n) as [E1 | E2].
  rewrite E1.
  left; reflexivity.
  right; injection; auto.
Qed.

Definition W_transfer (p : nat -> prp) (m n : nat) : W (p m) -> W (p n).
Proof.
  intros w.
  destruct (eqN_decidable m n) as [E1 | E2].
  rewrite <- E1.
  exact w.
  exact (W_member ((p n))).
Defined.

Definition C_transfer (p : nat -> prp) (m n : nat) : C (p m) -> C (p n).
Proof.
  intros c.
  destruct (eqN_decidable m n) as [E1 | E2].
  rewrite <- E1.
  exact c.
  exact (C_member ((p n))).
Defined.

(** Finally, the validity of Leibniz's law is proved. If someone knows a shortcut,
    I would like to know about it. *)

Theorem leibniz (p : nat -> prp) (m n : nat) : valid (prpEq m n ==>> p m ==>> p n).
Proof.
rewrite /valid /=.
exists (fun _ => (fun w => @W_transfer _ _ _ w,
                  fun y => @C_transfer _ _ _ y.2),
        fun _ => tt)=>/=.
move=>[[] [??]] /=; rewrite /C_transfer /W_transfer.
move=>/eqP E; destruct E.
case: (eqN_decidable m m)=> // E1.
by rewrite (UIP_dec eqN_decidable E1 (refl_equal m)).
Qed.

(** * Natural numbers

      Next we verify that the natural numbers obey Peano axioms. They are easy, except for
      induction which has two parts: the usual "forward" direction by primitive recursion,
      and a "backwards" direction in which we search for a counter-example, starting from an
      upper bound and going down to 0. *)

Theorem nat_zero_not_succ (n : nat) : valid (neg (prpEq (S n) 0)).
Proof. by rewrite /valid /=; exists (fun _ => tt). Qed.

Theorem succ_injective (m n : nat) : valid (prpEq (S m) (S n) ==>> prpEq m n).
Proof. by rewrite /valid /=; exists (fun _ => tt, fun _ => tt). Qed.

(** Given a propositional function [p : nat -> prp], suppose [p m] is not valid. Then [p
   0] is not valid, or one of induction steps [p k ==> p (S k)] fails. The "backwards"
   direction of the Dialectica interpretation of induction is a search functional which
   looks for a failed base case or failed induction step. We construct it separately from
   the main proof. *)

Definition search (p : nat -> prp) (m : nat) :
  W (p 0) ->
  (forall k : nat, W (p k) -> W (p (S k))) ->
  (forall k : nat, W (p k) * C (p (S k)) -> C (p k)) ->
  C (p m) ->
  C (p 0) + {n : nat & (W (p n) * C (p (S n)))%type}.
Proof.
move=>z s b c; elim: m c; first by move=>?; left.
move=>m IH c.
pose w := nat_rect _ z s m.
case: (diaP w (b m (w,c)))=>_.
- by right; exists m.
by apply/IH/b.
Defined.

(** Finally we verify validity of induction. *)

Theorem N_induction (p : nat -> prp) (m : nat) :
  valid (p 0 and (all n : N, p n ==>> p (S n)) ==>> p m).
Proof.
rewrite /valid /=.
exists (fun x => nat_rect _ x.1 (fun k => (x.2 k).1) m,
        fun y => search y.1.1
                   (fun k => (y.1.2 k).1)
                   (fun k => (y.1.2 k).2)
                   y.2)=>/=.
move=>[[??] c] /=.
elim: m c=>//; rewrite /search /= =>? IH ?.
case: diaP=>/= [D1|D2] H.
- by apply/H/D1.
by exfalso; apply/D2/IH/H.
Qed.

(** Having done ordinary induction one is tempted to try validating induction for
   W-types... but not here. *)

(** * Markov Principle and Independence of Premise *)

(** The Dialectica interpretation is characterized by two non-intuitionistic reasoning principles,
    namely Markov principle (MP) and Independence of Premise (IP).

    Both MP and IP involve primitive propositional function [N -> bool]. The point of
    these is that their [W] and [C] types are the unit. So instead of actually using
    primitive proposition, we shall use arbitrary propositions whose [W] and [C] types are
    singletons. First we make the relevant definitions. *)

Definition singleton (t : Inhabited) := forall x, x = member t.

Definition trivial_C (p : prp) := singleton (inhabit (C_member p)).
Definition trivial_W (p : prp) := singleton (inhabit (W_member p)).

(** Primitive propositions are trivial, of course. *)

Lemma primitive_trivial_W (b : bool) : trivial_W ([b]).
Proof. by case. Qed.

Lemma primitive_trivial_C (b : bool) : trivial_C ([b]).
Proof. by case. Qed.

(** Whether there are trivial propositions, other than the primitive ones, depends on what
   extra axioms we have available. For example, in the presence of extensionality of
   functions, implications and negations of trivial propositions are trivial. We do not
   dwell on the exact conditions that give us trivial propositions, but only demonstrate
   how to use extensionality of functions whose codomain is a singleton set to derive
   triviality of implication of trivial propositions.
*)

(** We are only interested in extensionality of functions [s -> t] for which
    [t] is a singleton. Such extensionality can be phrased as "any power of a
    singleton is a singleton". *)

Definition singleton_power :=
  forall t, singleton t -> forall s : Set, singleton (inhabit (fun _ : s => member t)).

(** I _think_ there is no way of proving [singleton_power], is there? We can use it to
    show that [W (p ==> q)] is trivial if [C p] and [W q] are trivial. *)

Lemma implication_trivial_W (p q : prp) :
  singleton_power -> trivial_C p -> trivial_W q -> trivial_W (p ==>> q).
Proof.
move=>E TCp TWq; rewrite /trivial_W /singleton /W_member /=; case=>f g.
rewrite (E _ TWq _ f) (E _ TCp _ g) /=.
by rewrite 2![WC_member _]surjective_pairing.
Qed.

(** Triviality of [C (p ==> q)] does not require any extra assumptions. *)
Lemma implication_trivial_C (p q : prp) :
  trivial_W p -> trivial_C q -> trivial_C (p ==>> q).
Proof.
move=>TWp TCq; rewrite /trivial_C /C_member /=; case=>wp cq /=.
rewrite (TWp wp) (TCq cq) /=.
by rewrite 2![WC_member _]surjective_pairing.
Qed.

(** ** Markov principle *)

(** Markov principle holds for any inhabited type (not just the natural numbers) and
   a proposition which has trivial [W] and [C] types. *)

Theorem markov_generalized (t : Inhabited) (p : t -> prp) :
  (forall x, trivial_C (p x)) ->
  (forall x, trivial_W (p x)) ->
  valid (neg (all x : t, neg (p x)) ==>> some x : t, p x).
Proof.
rewrite /valid /= => TC TW.
pose u := fun (h : _ -> {x : t & W (p x)}) =>
            let y := projT1 (h (fun x (_ : W (p x)) => C_member (p x))) in
            existT (fun x : t => W (p x)) y (W_member (p y)).
exists (u, fun _ x _ => C_member (p x))=>/=.
move=>[f g] /=.
pose v := projT1 (f (fun x _ => C_member (p x))).
pose w := projT2 (f (fun (x : t) (_ : W (p x)) => C_member (p x))).
rewrite (TC v (g v (W_member (p v)))) /=.
move: (TW v w); rewrite /w =>->/=.
by apply: dia_not_not_stable.
Qed.

(** The usual Markov principle now follows easily. *)

Theorem markov (p : nat -> bool) :
  valid (neg (all n : N, neg ([p n])) ==>> some n : N, ([p n])).
Proof.
by apply: markov_generalized=>?; [exact: primitive_trivial_C | exact: primitive_trivial_W].
Qed.

(** ** The Independence of Premise *)

(** The usual IP relates propositional functions [p : s -> bool] and [q : t -> prp]:

    [((all x : s, p x) ==> some y : t, q y) ==> some y : t, (all x : s, p x) ==> q y]

    It is possible to generalize [p] to [p : s -> prp] with trival [W (p x)]. On the other
    hand, the type-dependencies force us to require that [C (q y)] be trivial. *)

Theorem ip_generalized (s t : Inhabited) (p : s -> prp) (q : t -> prp) :
  (forall (x : s), trivial_W (p x)) ->
  (forall (y : t), trivial_C (q y)) ->
  valid (((all x : s, p x) ==>> some y : t, q y) ==>>
          some y : t, (all x : s, p x) ==>> q y).
Proof.
rewrite /valid /= => TW TC.
pose u := fun (x : s) => W_member (p x).
pose v := fun (y : t) (w : W (q y)) => C_member (q y).
exists (fun a => existT _ (projT1 (a.1 u)) (fun _ => projT2 (a.1 u),
                                            fun b => a.2 (u, v)),
        fun _ => (u,v))=>/=.
move=>[[f g] h] /=.
pose y := projT1 (f u).
pose z := projT1 (g (u, v)).
move=>G H.
rewrite (TC y (h y (fun=> projT2 (f u), fun=> g (u, v))).2) /=.
rewrite (TC y (v y (projT2 (f u)))) /= in G.
apply: G.
by rewrite (TW z ((h y (fun=> projT2 (f u), fun=> g (u, v))).1 z)) /= in H.
Qed.

(** A special case of our IP occurs when [p] is a primitive propositional function. *)

Theorem ip (s t : Inhabited) (p : s -> bool) (q : t -> prp) :
  (forall (y : t), trivial_C (q y)) ->
  valid (((all x : s, ([p x])) ==>> some y : t, q y) ==>>
          some y : t, (all x : s, ([p x])) ==>> q y).
Proof.
move=>?; apply: ip_generalized=>//.
by move=>?; apply: primitive_trivial_W.
Qed.

(** This concludes the verification of the Dialectica interpretation in Coq. There are at
    least three interesting directions to go:

    - Extract programs from the Dialectica interpretation. It looks like this could be done
      for extraction into Scheme. Extraction into Haskell and Ocaml seem more complicated
      because the [W] and [C] types are dependent and there seems no easy way of
      translating them into a simply-typed programming language. Presumably, concrete
      examples could be extracted with the help of "[Extraction Inline W C.]".

    - Explore other variants, such as the Diller-Nahm interpretation, or perhaps the
      interpretations a la Ulrich Kohlenbach and Paolo Oliva.

    - Explore the possibility of having a fully dependent Dialectica interpretation.
      Initial investigations by Thomas Streicher and myself indicate that it can be done.
      This would give us a way of constructing a two-level type system (with Prop separate
      from Set) that validates MP and IP. *)
