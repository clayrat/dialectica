From Coq Require Import ssreflect ssrbool ssrfun Eqdep_dec FunctionalExtensionality.
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
  | atm : forall p : bool, prp
  | pls (A B : prp)
  | tns (A B : prp)
  | bng (A : prp)
  | opp (A : prp)
  | unv : forall {ty : Inhabited}, (ty -> prp) -> prp.

Definition neg A := opp (bng A).
Definition wth A B := opp (pls (opp A) (opp B)).
Definition arr A B := opp (tns A (opp B)).
Definition ext {ty : Inhabited} (f: ty -> prp) : prp := opp (@unv ty (opp \o f)).
Definition whn A := opp (bng (opp A)).

(** Convenient notation for the object language. *)

Notation "'[' p ']'" := (atm p).
Notation "¬ x" := (neg x) (at level 70, no associativity).
Notation "x ＆ y" := (wth x y) (at level 74, left associativity).
Notation "x ⊕ y" := (pls x y) (at level 76, left associativity).
Notation "x ⊗ y" := (tns x y) (at level 76, left associativity).
Notation "x ⊸ y" := (arr x y) (at level 78, right associativity).
Notation "! x" := (bng x) (at level 1, format "! x").
Notation "? x" := (whn x) (at level 1, format "? x").
Notation "∀ x : t , p" :=  (@unv t (fun x => p)) (at level 80, x at level 99).
Notation "∃ x : t , p" :=  (@ext t (fun x => p)) (at level 80, x at level 99).

(** With each proposition [p] we associate the types [W p] and [C p] of "witnesses" and
   "counters", respectively. Think of them as moves in a game between a player [W] and an
   opponent [C]. We make two changes to the standard Dialectica representation.

   First, we use sum for counters of conjunctions, where normally a product is used. This
   gives us symmetry between conjunction and disjunction, simplifies the notorious
   conjunction contraction [and_contr], but complicates the adjunction between implication
   and conjunction. Thomas Streicher pointed out that the change is inessential in the
   sense that we could prove a separate lemma which allows us to pass from counters for [p
   and q] as pairs to counters as elements of a sum (such a lemma relies in decidability
   of the [rel] relation defined below).

   Second, because we allow the structure of a propositional function to depend on the
   argument, we are forced to introduce type dependency into [W p] and [C p] when [p] is a
   quantified statement. This is not a big surprise, but what is a little more surprising
   is that the counters for existentials, [C (existential ty p')], involve a dependency
   not only on [ty] but also on [W (p' x)]. The dependency is needed in the rule
   [exists_elim]. The rest of Dialectica interpetation is not influenced by this change,
   with the exception of the Independence of Premise where we have to impose a condition
   that is not required in the usual interpretation.

   These type-dependencies clearly towards an even more type-dependent Dialectica variant.
   Indeed, we are going to investigate it in a separate file. For now we are just trying
   to faithfully represent the Dialectica interpretation. *)

Section LinDia.

Variable ctx : Type.
Variable daimon : ctx.

Fixpoint W (p : prp) : Type :=
  match p with
    | atm _ => unit
    | pls p1 p2 => W p1 + W p2
    | tns p1 p2 => W p1 * W p2
    | bng p => W p
    | opp p => C p
    | unv ty p' => forall x : ty, W (p' x)
  end

with C p :=
  match p with
    | atm _ => ctx
    | pls p1 p2 => C p1 * C p2
    | tns p1 p2 => (W p1 -> C p2) * (W p2 -> C p1)
    | bng p => W p -> C p
    | opp p => W p
    | unv ty p' => { x : ty & C (p' x) }
  end.

(** The types [W] and [C] are always inhabited because we restrict quantifiers to inhabited
   types. *)

Definition WC_member (A : prp) : W A * C A.
Proof.
elim: A=>//=. (* atm case needs the daimon *)
- by move=>?[??]?[??]; do!split=>//; right.
- by move=>?[??]?[??].
- by move=>?[??].
- by move=>?[??].
move=>ty ? H; split.
- by move=>x; case: (H x).
- by exists (member ty); case: (H (member ty)).
Defined.

Definition W_member (A : prp) := (WC_member A).1.
Definition C_member (A : prp) := (WC_member A).2.

Notation "⊢ A" := (W A) (at level 89).
Notation "⊣ A" := (C A) (at level 89).

(** The relation [rel p w c] is what is usually written as [p_D] in the Dialectica
    interpretation, i.e., the matrix of the interpreted formula.

    In terms of games, [rel p w c] tells whether the player move [w] wins against the
    opponent move [c] in the game determined by the proposition [p].
*)

Fixpoint rel (A : prp) : W A -> C A -> Prop :=
  match A return W A -> C A -> Prop with
    | atm p => fun _ _ => p
    | pls A B => fun w z => match w with
                 | inl u => rel u z.1
                 | inr v => rel v z.2
                 end
    | tns A B => fun w z => match w, z with
                 | (u, v), (zl, zr) => rel u (zr v) /\ rel v (zl u)
                 end
    | bng A => fun u y => @rel A u (y u)
    | opp A => fun x u => ~ rel u x
    | unv T A => fun w z => match z with
                 | existT t u => rel (w t) u
                 end
  end.

(** The [rel] relation is decidable. *)

Fixpoint relb (A : prp) : W A -> C A -> bool :=
  match A return W A -> C A -> bool with
    | atm p => fun _ _ => p
    | pls A B => fun w z => match w with
                 | inl u => relb u z.1
                 | inr v => relb v z.2
                 end
    | tns A B => fun w z => match w, z with
                 | (u, v), (zl, zr) => relb u (zr v) && relb v (zl u)
                 end
    | bng A => fun u y => @relb A u (y u)
    | opp A => fun x u => ~~ relb u x
    | unv T A => fun w z => match z with
                 | existT t u => relb (w t) u
                 end
  end.

Theorem relP (p : prp) (a : W p) (b : C p) : reflect (rel a b) (relb a b).
Proof.
elim: p a b=>//=.
- by move=>? _ _; exact: idP.
- by move=>? H1 ? H2; case=>??; [exact: H1|exact: H2].
- move=>? H1 ? H2 [??][??] /=; case: H1=>/=; last by move=>?; apply: ReflectF; case.
  by case: H2=>??; [apply: ReflectT | apply: ReflectF; case].
- by move=>? H ??; case: H=>/= ?; [apply: ReflectF|apply: ReflectT].
by move=>?? H ?[??] /=; apply: H.
Qed.

(** Of course, a decidable proposition is stable for double negation. *)

Lemma rel_not_not (A : prp) (u : W A) (x : C A) : ~ ~ rel u x -> rel u x.
Proof. by move/classicP=>H; apply/relP/H => /relP. Qed.

Lemma rel_arr : forall A B (w : W (A ⊸ B)) (z : C (A ⊸ B)),
  rel w z <-> (rel z.1 (w.2 z.2) -> rel (w.1 z.1) z.2).
Proof.
move=>?? /= [??][??]; split=>/= H.
- by move=>?; apply: rel_not_not=>?; apply: H.
by move=>[?]; apply; apply: H.
Qed.

(** The predicate [valid p] is the Dialectica interpretation of [p]. It says that there is
   [w] such that [rel p w c] holds for any [c]. In terms of games semantics this means
   that [W] has a winning strategy (which amounts to a winning move [w]). *)

Structure Valid {X} (w : ⊢ X) := V { valid_spec : forall c : ⊣ X, rel w c }.

Definition app {X Y} : ⊢ X ⊸ Y -> ⊢ X -> ⊢ Y.
Proof. by move=>/= []. Defined.

Lemma Valid_app {X Y} : forall (f : ⊢ X ⊸ Y) x, Valid f -> Valid x -> Valid (app f x).
Proof.
move=>/=[??] x [Hf][?] /=; split=>b.
by move: (Hf (x,b)); rewrite rel_arr /=; apply.
Qed.

Definition identity {X} : ⊢ X ⊸ X.
Proof. by []. Defined.

Lemma Valid_id {X}: Valid (@identity X).
Proof. by split=>/= [[??]]; case. Qed.

Definition compose {X Y Z}: ⊢ X ⊸ Y -> ⊢ Y ⊸ Z -> ⊢ X ⊸ Z.
Proof.
move=>/=[fl fr][gl gr].
by split=>/=?; [apply/gl/fl|apply/fr/gr].
Defined.

Lemma Valid_compose {X Y Z}: forall (f : ⊢ X ⊸ Y) (g : ⊢ Y ⊸ Z),
  Valid f -> Valid g -> Valid (compose f g).
Proof.
move=>/=[fl ?][? gr][Hf][Hg]; split=>/= [[u z]].
move: (Hg (fl u, z)); move: (Hf (u, gr z)); rewrite !rel_arr /= =>H1 H2 [?]; apply.
by apply/H2/H1.
Qed.

Notation "t ; u" := (compose t u) (at level 60).

Lemma compose_id_l {X Y}: forall (f : ⊢ X ⊸ Y), identity; f = f.
Proof. by move=>/= []. Qed.

Lemma compose_id_r {X Y}: forall (f : ⊢ X ⊸ Y), f; identity = f.
Proof. by move=>/= []. Qed.

Lemma compose_assoc {P Q R S}: forall (f : ⊢ P ⊸ Q) (g : ⊢ Q ⊸ R) (h : ⊢ R ⊸ S),
  f; g; h = f; (g ; h).
Proof. by move=>/=[??][??][??]. Qed.

(** Tensoriality *)

Definition tns_fun {P Q R S}: ⊢ P ⊸ Q -> ⊢ R ⊸ S -> ⊢ P ⊗ R ⊸ Q ⊗ S.
Proof.
move=>/=[fl fr][gl gr]; split.
- by move=>[??]; split; [apply: fl|apply: gl].
by move=>[hl hr]; split=>?; [apply/gr/hl/fl|apply/fr/hr/gl].
Defined.

Lemma Valid_tns_fun {P Q R S}: forall (f : ⊢ P ⊸ Q) (g : ⊢ R ⊸ S),
  Valid f -> Valid g -> Valid (tns_fun f g).
Proof.
move=>/=[fl ?][gl ?][Hf][Hg]; split=>/=[[[u v][hl hr]]].
move: (Hf (u, hr (gl v))); move: (Hg (v, hl (fl u))); rewrite !rel_arr /= =>H1 H2 [[??]]; apply.
by split; [apply: H2|apply:H1].
Qed.

Definition tns_assoc {X Y Z} : ⊢ X ⊗ Y ⊗ Z ⊸ X ⊗ (Y ⊗ Z).
Proof.
split=>/=.
- by move=>[[??]?].
move=>[hl hr]; do!split.
- by move=>[??]; case: hl=>// +?; apply.
- by move=>?; case: hl=>// ?; apply.
by move=>?; apply: hr.
Defined.

Lemma Valid_tns_assoc {X Y Z}: Valid (@tns_assoc X Y Z).
Proof.
split=>/= [[[[u ?]?][hl ?]]] /=.
by case: (hl u)=>??[[[??]?]]; apply.
Qed.

(** *)

Definition lam {X Y Z}: ⊢ X ⊗ Y ⊸ Z -> ⊢ X ⊸ Y ⊸ Z.
Proof.
move=>/=[fl fr]; split.
- move=>?; split=>?; first by apply: fl.
  by case: fr=>// +?; apply.
by move=>[??]; case: fr=>// ?; apply.
Defined.

Lemma Valid_lam {X Y Z}: forall (f : ⊢ X ⊗ Y ⊸ Z), Valid f -> Valid (lam f).
Proof.
move=>/=[? fr][Hf].
split=>/=[[u [v z]]].
move: (Hf (u,v,z)); rewrite !rel_arr /=.
case: (fr z)=>?? H [?]; apply; case=>?; apply.
by apply: H.
Qed.

Lemma natural_lam {P Q R S}: forall (f : ⊢ P ⊸ Q) (g : ⊢ Q ⊗ R ⊸ S),
  f; lam g = lam (tns_fun f identity; g).
Proof.
move=>/=[??][? gr] /=; f_equal.
- apply: functional_extensionality=>?; f_equal.
  apply: functional_extensionality=>?; f_equal.
  by case: (gr _).
apply: functional_extensionality; case=>??; f_equal.
by case: (gr _).
Qed.

Definition eval {X Y} : ⊢ (X ⊸ Y) ⊗ X ⊸ Y.
Proof.
split=>/=.
- by move=>[[]].
by move=>?; do!split=>// [[?]]; apply.
Defined.

Lemma Valid_eval {X Y} : Valid (@eval X Y).
Proof.
split=>/= [[[[??]??]]][[H1 ?]?].
by apply: H1.
Qed.

(** Cartesian structure *)

Definition prd {X Y Z}: ⊢ Z ⊸ X -> ⊢ Z ⊸ Y -> ⊢ Z ⊸ X ＆ Y.
Proof.
move=>/=[fl fr][gl gr]; split.
- by move=>?; split; [apply: fl|apply: gl].
by case.
Defined.

Lemma Valid_prd {X Y Z}: forall (f : ⊢ Z ⊸ X) (g : ⊢ Z ⊸ Y),
  Valid f -> Valid g -> Valid (prd f g).
Proof.
move=>/=[fl ?][gl ?][Hf][Hg] /=; split.
case; rewrite -/W -/C =>z; case=>[x|y]; rewrite rel_arr /=.
- by move: (Hf (z,x)) => /= H ??; apply: H.
by move: (Hg (z,y)) => /= H ??; apply: H.
Qed.

Definition projl {X Y}: ⊢ X ＆ Y ⊸ X.
Proof. by split=>/=; [case|left]. Defined.

Lemma Valid_projl {X Y}: Valid (@projl X Y).
Proof. by split=>/=[[[??]?]][]. Qed.

Definition projr {X Y}: ⊢ X ＆ Y ⊸ Y.
Proof. by split=>/=; [case|right]. Defined.

Lemma Valid_projr {X Y}: Valid (@projr X Y).
Proof. by split=>/=[[[??]?]][]. Qed.

(** Exponentials *)

Definition wth_tns {X Y} : ⊢ !(X ＆ Y) ⊸ !X ⊗ !Y.
Proof.
split=>//= [[hl hr][u v]].
move: (hl u v)=>l; move: (hr v u)=>r.
by case: (relP v l)=>?; [left|right].
Defined.

Lemma Valid_wth_tns {X Y} : Valid (@wth_tns X Y).
Proof.
split=>/=[[[??][??]]] /=.
case: relP=>?[H1 H2]; apply: H1=>? //.
by apply: H2.
Qed.

Definition tns_wth {X Y} : ⊢ !X ⊗ !Y ⊸ !(X ＆ Y).
Proof.
split=>//= f; split=>u v.
- by case: (f (u,v))=>// ?; apply: C_member.
by case: (f (v,u))=>// ?; apply: C_member.
Defined.

Lemma Valid_tns_wth {X Y} : Valid (@tns_wth X Y).
Proof.
split=>/=[[[??]z]] /=.
by case: z; rewrite -/W -/C=>?[[??]]; apply; apply.
Qed.

Definition bng_fun {X Y}: ⊢ X ⊸ Y -> ⊢ !X ⊸ !Y.
Proof.
move=>/=[fl fr]; split=>//.
by move=>h ?; apply/fr/h/fl.
Defined.

Lemma Valid_bng_fun {X Y} : forall (f : ⊢ X ⊸ Y),
  Valid f -> Valid (bng_fun f).
Proof.
move=>/=[fl fr][Hf]; split=>/= [[u g]].
by move: (Hf (u,g (fl u))).
Qed.

Lemma compose_bng_fun {X Y Z} : forall (f : ⊢ X ⊸ Y) (g : ⊢ Y ⊸ Z),
  bng_fun (f; g) = bng_fun f; bng_fun g.
Proof. by move=>/=[??][??]. Qed.

Lemma id_bng_fun {X}: bng_fun (@identity X) = identity.
Proof. by []. Qed.

Definition bng_mon {X Y}: ⊢ !X ⊗ !Y ⊸ !(X ⊗ Y).
Proof.
split=>//= z; split.
- by move=>??; case: z=>// +?; apply.
by move=>??; case: z=>// ?; apply.
Defined.

Lemma Valid_bng_mon {X Y}: Valid (@bng_mon X Y).
Proof. by split=>/=[[[u v] y]]; case: (y (u,v))=>?? []. Qed.

Lemma natural_bng_mon {P Q R S}: forall (f : ⊢ P ⊸ R) (g : ⊢ Q ⊸ S),
  tns_fun (bng_fun f) (bng_fun g); bng_mon = bng_mon; bng_fun (tns_fun f g).
Proof.
move=>/=[fl fr][gl gr]/=; f_equal.
apply: functional_extensionality=>y; f_equal.
- apply: functional_extensionality=>u; apply: functional_extensionality=>v.
  by case: (y (fl u, gl v)).
apply: functional_extensionality=>v; apply: functional_extensionality=>u.
by case: (y (fl u, gl v)).
Qed.

Definition der {X}: ⊢ !X ⊸ X.
Proof. by split=>/=. Defined.

Lemma Valid_der {X}: Valid (@der X).
Proof. by split=>/=[[??]][]. Qed.

Lemma natural_der {X Y}: forall (f : ⊢ X ⊸ Y),
  der; f = bng_fun f; der.
Proof. by move=>/=[??]. Qed.

Definition dig {X} : ⊢ !X ⊸ !!X.
Proof.
split=>//=.
by move=>x ?; apply: x.
Defined.

Lemma Valid_dig {X} : Valid (@dig X).
Proof. by split=>/=[[??]][]. Qed.

Lemma natural_dig {X Y}: forall (f : ⊢ X ⊸ Y),
  dig; bng_fun (bng_fun f) = bng_fun f; dig.
Proof. by move=>/=[??]. Qed.

Lemma dig_der_id_1 {X}: @dig X; der = identity.
Proof. by []. Qed.

Lemma dig_der_id_2 {X}: @dig X; bng_fun der = identity.
Proof. by []. Qed.

Lemma dig_assoc {X}: @dig X; dig = dig; bng_fun dig.
Proof. by []. Qed.

Lemma der_mon {X Y}: @bng_mon X Y; der = tns_fun der der.
Proof. by move=>/=; f_equal; apply: functional_extensionality; case. Qed.

Lemma dig_mon {X Y}: @bng_mon X Y; dig = tns_fun dig dig; bng_mon; bng_fun bng_mon.
Proof. by move=>/=; f_equal; apply: functional_extensionality; case. Qed.

Definition dup {X} : ⊢ !X ⊸ !X ⊗ !X.
Proof.
split=>//= [[hl hr]] u.
move: (hl u u)=>l; move: (hr u u)=>r.
case: (relP u l)=>?; [|exact l].
case: (relP u r)=>?; [|exact r].
apply: C_member.
Defined.

Lemma Valid_dup {X} : Valid (@dup X).
Proof.
split=>/=[[u[hl hr]]].
case: relP.
- by case: relP=>??[?]; apply.
by move=>?[?].
Qed.

Lemma dup_coalg {X}: @dig X; bng_fun dup = dup; tns_fun dig dig; bng_mon.
Proof.
move=>/=; f_equal.
apply: functional_extensionality=>h; apply functional_extensionality=>u.
by case: (h (u,u)).
Qed.

Lemma dig_comon {X}: @dig X; dup = dup; tns_fun dig dig.
Proof.
move=>/=; f_equal.
apply: functional_extensionality=>[[??]]; apply functional_extensionality=>?.
do!case: relP=>//=.
by rewrite /C_member /=; case: (WC_member X).
Qed.

Lemma dup_mon_comm {P Q R S} : ⊢ (!P ⊗ !Q) ⊗ (!R ⊗ !S) ⊸ (!P ⊗ !R) ⊗ (!Q ⊗ !S).
Proof.
split=>/=.
- by move=>[[??][??]].
move=>[hl hr]; split; move=>[??]; split=>??.
- by case: hl=>// +?; apply.
- by case: hr=>// +?; apply.
- by case: hl=>// ?; apply.
by case: hr=>// ?; apply.
Defined.

Definition undual {X}: ⊢ ((X ⊸ [false]) ⊸ [false]) ⊸ X.
Proof. by split=>//= [[? g]]; case: g. Defined.

Lemma Valid_undual {X}: Valid (@undual X).
Proof.
split=>/= [[[? fr]?]].
case: (fr daimon)=>??[H1 ?]; apply: H1.
by split=>//; case.
Qed.

Definition wkn {A} : ⊢ A ⊸ [true].
Proof. by split=>//= ?; apply: C_member. Defined.

Lemma Valid_wkn {A}: Valid (@wkn A).
Proof. by split=>/= [[??]][]. Qed.

Definition absurd {X} : ⊢ [false] ⊸ X.
Proof. by split=>//= _; apply: W_member. Defined.

Lemma Valid_absurd {X}: Valid (@absurd X).
Proof. by split=>/= [[[] ?]][]. Qed.

Definition forall_intro {ty : Inhabited} (A : prp) (B : ty -> prp) :
  (forall x : ty, ⊢ A ⊸ B x) -> ⊢ A ⊸ ∀ x : ty, B x.
Proof.
move=>p; split=>/=.
- by move=>u ?; apply/app/u.
by move=>[x ?]; move: (p x)=>/=[?]; apply.
Defined.

Lemma Valid_forall_intro {ty A B f}:
  (forall t, Valid (f t)) -> Valid (@forall_intro ty A B f).
Proof.
move=>Hf; split=>/= [[u [x y]]]; move: (Hf x)=>[].
move: (f x)=>/=[??]H[? /= ?].
by apply: (H (u,y)).
Qed.

Definition forall_elim {ty : Inhabited} (t : ty) (A : ty -> prp) :
  ⊢ (∀ t : ty, A t) ⊸ A t.
Proof. by split=>//= ?; exists t. Defined.

Lemma Valid_forall_elim {ty t A}: Valid (@forall_elim ty t A).
Proof. by split=>/= [[??]][]. Qed.

Definition exists_intro {ty : Inhabited} (t : ty) (A : ty -> prp) :
  ⊢ A t ⊸ ∃ x : ty, A x.
Proof. by split=>//= ?; exists t. Defined.

Lemma Valid_exists_intro {ty t A} : Valid (@exists_intro ty t A).
Proof. by split=>/= [[??]][?]; apply. Qed.

(** This is the rule in which we need the dependency of counters in existential statements. *)

Definition exists_elim {ty : Inhabited} (A : prp) (B : ty -> prp)
                       (f : forall x : ty, ⊢ B x ⊸ A) :
 ⊢ (∃ x : ty, B x) ⊸ A.
Proof.
split=>/=.
- by move=>[x ?]; move: (f x)=>/= [+?]; apply.
by move=>? x; move: (f x)=>/= [?]; apply.
Defined.

Lemma Valid_exists_elim {ty A B f} :
  (forall x, Valid (f x)) -> Valid (@exists_elim ty A B f).
Proof.
move=>Hf; split=>/= [[[x v] u]]; move: (Hf x)=>[].
move: (f x)=>/= [??] H [??].
apply: (H (v,u)); split=>//.
by apply: rel_not_not.
Qed.

Lemma exists_id {ty : Inhabited} (A : ty -> prp) (B : prp) (t : ty)
                (f : forall t : ty, ⊢ A t ⊸ B) :
  @exists_intro ty t A; @exists_elim ty B A f = f t.
Proof. by move=>/=; move: (f t)=>/=[]. Qed.

Definition Exists_elim {ty : Inhabited} (A : prp) (B : ty -> prp)
                       (f : forall x : ty, ⊢ !(B x) ⊸ A) :
  ⊢ (∃ x : ty, !(B x)) ⊸ A.
Proof.
split=>/=.
- by move=>[x ?]; move: (f x)=>/=[+?]; apply.
by move=>? x ?; move: (f x)=>/=[?]; apply.
Defined.

Lemma Valid_Exists_elim {ty A B f}:
  (forall x, Valid (f x)) -> Valid (@Exists_elim ty A B f).
Proof.
move=>Hf; split=>/= [[[x v] u]]; move: (Hf x)=>[].
move: (f x)=>/=[??] H [??].
apply: (H (v,u)); split=>//.
by apply: rel_not_not.
Qed.

End LinDia.