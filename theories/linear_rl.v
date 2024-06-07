From Coq Require Import ssreflect ssrbool ssrfun Eqdep_dec FunctionalExtensionality.
From mathcomp Require Import ssrnat eqtype seq.
From Dialectica Require Import Rlist.

Set Bullet Behavior "None".
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Open Scope seq_scope.

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
   will be forced later on to introduce certain type dependencies where there are none in:
   the usual Dialectica interpretation. *)

Inductive prp : Type :=
  | atm : bool -> prp
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
Notation "x ⇒ y" := (arr (bng x) y) (at level 78, right associativity).
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

Inductive ctx := ctx_intro of list ctx.

Fixpoint W (p : prp) : Type :=
  match p with
    | atm p => unit
    | pls p1 p2 => W p1 + W p2
    | tns p1 p2 => W p1 * W p2
    | bng p => W p
    | opp p => C p
    | unv ty p' => forall x : ty, W (p' x)
  end

with C p :=
  match p with
    | atm p => ctx
    | pls p1 p2 => C p1 * C p2
    | tns p1 p2 => (W p1 -> C p2) * (W p2 -> C p1)
    | bng p => Rlist.t (W p) (C p)
    | opp p => W p
    | unv ty p' => { x : ty & C (p' x) }
  end.

Notation "⊢ A" := (W A) (at level 89).
Notation "⊣ A" := (C A) (at level 89).

Fixpoint run {A : prp} : W A -> C A -> ctx.
Proof.
case: A=>//=.
- by move=>A B; case=>?[??]; [apply: (run A)|apply: (run B)].
- move=>??[u v][? hr].
  by apply: (run _ u (hr v)).
- by move=>? u z; apply/ctx_intro/(seq.map (run _ u))/(Rlist.run z u).
- by move=>A ??; apply: (run A).
by move=>? p ?[t ?]; apply: (run (p t)).
Defined.

(** The relation [rel p w c] is what is usually written as [p_D] in the Dialectica
   interpretation, i.e., the matrix of the interpreted formula.

   In terms of games, [rel p w c] tells whether the player move [w] wins against the
   opponent move [c] in the game determined by the proposition [p].
*)

Definition rel_bng {A} (R : forall x, W x -> C x -> Prop) (u : W A) (z : Rlist (W A) (C A)) :=
  Rlist.fold_right (fun x P u => R A u x /\ P u) (fun _ => True) z u.

Definition rel_bng_node {A} (R : forall x, W x -> C x -> Prop) (u : W A) (z : Rnode (W A) (C A)) :=
  Rlist.fold_right_node (fun x P u => R A u x /\ P u) (fun _ => True) z u.

Lemma rel_bng_simpl {A R} : forall (u : W A) (z : W A -> Rnode (W A) (C A)),
  rel_bng R u (Rlist.rnode z) = @rel_bng_node A R u (z u).
Proof. by []. Qed.

Lemma rel_bng_nil {A R}: forall (u : W A),
  rel_bng_node R u rnil = True.
Proof. by []. Qed.

Lemma rel_bng_cons {A R} : forall (u : W A) (x : C A) (z : Rlist (W A) (C A)),
  rel_bng_node R u (Rlist.rcons x z) = (R A u x /\ rel_bng R u z).
Proof. by []. Qed.

Lemma rel_bng_inv {A} {R : forall x, W x -> C x -> Prop} : forall (u : W A) (z : Rlist (W A) (C A)),
  (forall v : C A, @R (opp (opp A)) u v -> @R A u v) -> @rel_bng (opp (opp A)) R u z -> rel_bng R u z
with rel_bng_node_inv {A} {R : forall x, W x -> C x -> Prop} : forall (u : W A) (z : Rnode (W A) (C A)),
  (forall v : C A, @R (opp (opp A)) u v -> @R A u v) -> @rel_bng_node (opp (opp A)) R u z -> rel_bng_node R u z.
Proof.
- by move=>?[?]; apply: rel_bng_node_inv.
move=>?; case.
- by rewrite !rel_bng_nil.
move=>?? H.
by rewrite !rel_bng_cons; case=>??; split; [apply: H | apply: rel_bng_inv].
Qed.

Lemma rel_bng_cat {A R} : forall (u : W A) (zl zr : Rlist (W A) (C A)),
  rel_bng R u (cat zl zr) <-> rel_bng R u zl /\ rel_bng R u zr
with rel_bng_app_node {A R} : forall (u : W A) (nl : Rnode (W A) (C A)) (zr : Rlist (W A) (C A)),
  rel_bng_node R u (cat_node nl zr u) <-> rel_bng_node R u nl /\ rel_bng R u zr.
Proof.
- move=>/= ?[?]?.
  by rewrite !rel_bng_simpl; exact: rel_bng_app_node.
move=>u; case=>/=.
- by case=>r; rewrite rel_bng_nil rel_bng_simpl; split=>// [[]].
move=>???; rewrite !rel_bng_cons rel_bng_cat.
by apply: iff_sym; exact: and_assoc.
Qed.

Fixpoint rel (A : prp) : W A -> C A -> Prop :=
  match A return W A -> C A -> Prop with
    | atm p => fun _ _ => p
    | pls X Y => fun w z => match w with
                 | inl u => rel u z.1
                 | inr v => rel v z.2
                 end
    | tns X Y => fun w z => match w, z with
                 | (u, v), (zl, zr) => rel u (zr v) /\ rel v (zl u)
                 end
    | bng X => @rel_bng X rel
    | opp X => fun x u => ~ rel u x
    | unv T X => fun w z => match z with
                 | existT t u => rel (w t) u
                 end
  end.

(** The [rel] relation is decidable. *)

Definition relb_bng {A} (R : forall x, W x -> C x -> bool) (u : W A) (z : Rlist (W A) (C A)) :=
  Rlist.fold_right (fun x P u => R A u x && P u) (fun _ => true) z u.

Definition relb_bng_node {A} (R : forall x, W x -> C x -> bool) (u : W A) (z : Rnode (W A) (C A)) :=
  Rlist.fold_right_node (fun x P u => R A u x && P u) (fun _ => true) z u.

Lemma relb_bng_simpl {A R} : forall (u : W A) (z : W A -> Rnode (W A) (C A)),
  relb_bng R u (Rlist.rnode z) = @relb_bng_node A R u (z u).
Proof. by []. Qed.

Lemma relb_bng_nil {A R}: forall (u : W A),
  relb_bng_node R u rnil = true.
Proof. by []. Qed.

Lemma relb_bng_cons {A R} : forall (u : W A) (x : C A) (z : Rlist (W A) (C A)),
  relb_bng_node R u (Rlist.rcons x z) = R A u x && relb_bng R u z.
Proof. by []. Qed.

Fixpoint relb (A : prp) : W A -> C A -> bool :=
  match A return W A -> C A -> bool with
    | atm p => fun _ _ => p
    | pls X Y => fun w z => match w with
                 | inl u => relb u z.1
                 | inr v => relb v z.2
                 end
    | tns X Y => fun w z => match w, z with
                 | (u, v), (zl, zr) => relb u (zr v) && relb v (zl u)
                 end
    | bng X => @relb_bng X relb
    | opp X => fun x u => ~~ relb u x
    | unv T X => fun w z => match z with
                 | existT t u => relb (w t) u
                 end
  end.

Lemma relbngP (p : prp) (a : W p) (b : Rlist (W p) (C p)) :
  (forall c : C p, reflect (rel a c) (relb a c)) -> reflect (rel_bng rel a b) (relb_bng relb a b)
with relbngnodeP (p : prp) (a : W p) (b : Rnode (W p) (C p)) :
  (forall c : C p, reflect (rel a c) (relb a c)) -> reflect (rel_bng_node rel a b) (relb_bng_node relb a b).
Proof.
- move=>?; case: b=>?; rewrite rel_bng_simpl relb_bng_simpl.
  by apply: relbngnodeP.
move=>H; case: b.
- by rewrite rel_bng_nil relb_bng_nil; exact: ReflectT.
move=>??.
rewrite rel_bng_cons relb_bng_cons.
case: relbngP=>//; last by rewrite andbC /= =>?; apply: ReflectF; case.
move=>?; case: H=>/= ?; last by apply: ReflectF; case.
by apply: ReflectT.
Qed.

Theorem relP (p : prp) (a : W p) (b : C p) : reflect (rel a b) (relb a b).
Proof.
elim: p a b=>/=.
- by move=>? _ _; exact: idP.
- by move=>? H1 ? H2; case=>??; [exact: H1|exact: H2].
- move=>? H1 ? H2 [??][??] /=; case: H1=>/=; last by move=>?; apply: ReflectF; case.
  by case: H2=>??; [apply: ReflectT | apply: ReflectF; case].
- by move=>????; apply: relbngP.
- by move=>? H ??; case: H=>/= ?; [apply: ReflectF|apply: ReflectT].
by move=>?? H ?[??] /=; apply: H.
Qed.

(** Of course, a decidable proposition is stable for double negation. *)

Lemma rel_not_not {A} (u : W A) (x : C A) : ~ ~ rel u x -> rel u x.
Proof. by move/classicP=>H; apply/relP/H => /relP. Qed.

Lemma rel_bng_not_not {A} (u : W A) (v : Rlist (W A) (C A)) : ~ ~ rel_bng rel u v -> rel_bng rel u v.
Proof.
pose R:=relP u.
move/classicP=>H.
by apply: relbngP=>//; apply: H=>/relbngP; apply.
Qed.

Lemma rel_arr {A B}: forall (w : W (A ⊸ B)) (z : C (A ⊸ B)),
  rel w z <-> (rel z.1 (w.2 z.2) -> rel (w.1 z.1) z.2).
Proof.
move=>/= [??][??]; split=>/= H.
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

Definition tns_comm {X Y} : ⊢ X ⊗ Y ⊸ Y ⊗ X.
Proof. by split=>/=; case. Defined.

Lemma Valid_tns_comm {X Y}: Valid (@tns_comm X Y).
Proof. by split=>/=[[[??][??]]][[??]]; apply. Qed.

Definition idl {X} : ⊢ [true] ⊗ X ⊸ X.
Proof.
split=>/=; first by case.
move=>?; split=>//.
by move=>_; exact: (ctx_intro [::]).
Defined.

Lemma Valid_idl {X}: Valid (@idl X).
Proof. by split=>/=[[[[]??]]][[]]. Qed.

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

Definition whn_opp {X}: ⊢ ¬!X ⊸ ?(¬X).
Proof. by []. Defined.

Lemma Valid_whn_opp {X}: Valid (@whn_opp X).
Proof.
split=>/=[[??]][H]; apply=>?; apply: H.
apply: rel_bng_inv=>//= ?.
by apply: rel_bng_not_not.
Qed.

Definition bng_fun {X Y}: ⊢ X ⊸ Y -> ⊢ !X ⊸ !Y.
Proof.
move=>/=[fl fr]; split=>//.
by move=>?; apply/(Rlist.set fl)/(Rlist.map fr).
Defined.

Lemma rel_set_map {X Y} (fl : W X -> W Y) (fr : C Y -> C X) (u : W X) (g : Rlist (W Y) (C Y)) :
  (forall c : C (X ⊸ Y), @rel (X ⊸ Y) (fl,fr) c) ->
  rel_bng rel u (set fl (map fr g)) ->
  rel_bng rel (fl u) g
with relnode_set_map {X Y} (fl : W X -> W Y) (fr : C Y -> C X) (u : W X) (g : Rnode (W Y) (C Y)) :
  (forall c : C (X ⊸ Y), @rel (X ⊸ Y) (fl,fr) c) ->
  rel_bng_node rel u (set_node fl (map_node fr g)) ->
  rel_bng_node rel (fl u) g.
Proof.
- move=>?; case: g=>?/=; rewrite !rel_bng_simpl /=.
  by exact: relnode_set_map.
move=>H; case: g=>/=; first by rewrite !rel_bng_nil.
move=>x ?; rewrite !rel_bng_cons =>[[??]]; split.
- apply: rel_not_not=>?.
  by move: (H (u,x))=>/=; apply.
by apply: rel_set_map.
Qed.

Lemma Valid_bng_fun {X Y} : forall (f : ⊢ X ⊸ Y),
  Valid f -> Valid (bng_fun f).
Proof.
move=>/=[??][?]; split=>/= [[??]][?]; apply.
by apply: rel_set_map.
Qed.

Lemma compose_bng_fun {X Y Z} : forall (f : ⊢ X ⊸ Y) (g : ⊢ Y ⊸ Z),
  bng_fun (f; g) = bng_fun f; bng_fun g.
Proof.
move=>/=[??][??]/=; rewrite pair_equal_spec; split=>//.
by apply: functional_extensionality=>?; rewrite map_set set_set map_map.
Qed.

Lemma id_bng_fun {X}: bng_fun (@identity X) = identity.
Proof.
rewrite /identity /= pair_equal_spec; split=>//.
by apply: functional_extensionality=>?; rewrite map_id set_id.
Qed.

Definition bng_mon {X Y} : ⊢ !X ⊗ !Y ⊸ !(X ⊗ Y).
Proof.
split=>//= z; split.
- move=>u.
  apply: (set (fun v => (u,v))).
  apply: (map (fun '(fl,_) => fl u)).
  by exact: z.
move=>v.
apply: (set (fun u => (u,v))).
apply: (map (fun '(_,fr) => fr v)).
by exact: z.
Defined.

Lemma rel_set_map_pair {X Y} (u : W X) (v : W Y) (z : Rlist (W X * W Y) ((W X -> C Y) * (W Y -> C X))) :
  rel_bng rel v (set (fun v => (u,v)) (map (fun '(fl, _) => fl u) z)) ->
  rel_bng rel u (set (fun u => (u,v)) (map (fun '(_, fr) => fr v) z)) ->
  @rel_bng (X ⊗ Y) rel (u,v) z
with relnode_set_map_pair {X Y} (u : W X) (v : W Y) (z : Rnode (W X * W Y) ((W X -> C Y) * (W Y -> C X))) :
  rel_bng_node rel v (set_node (fun v => (u,v)) (map_node (fun '(fl, _) => fl u) z)) ->
  rel_bng_node rel u (set_node (fun u => (u,v)) (map_node (fun '(_, fr) => fr v) z)) ->
  @rel_bng_node (X ⊗ Y) rel (u,v) z.
Proof.
- case: z=>? /=; rewrite !rel_bng_simpl.
  by apply: relnode_set_map_pair.
case: z=>/=; first by rewrite !rel_bng_nil.
move=>[??]?; rewrite !rel_bng_cons=>[[??][??]]; split=>//=.
by apply: rel_set_map_pair.
Qed.

Lemma Valid_bng_mon {X Y} : Valid (@bng_mon X Y).
Proof.
split=>/=[[[??]?]][[??]]; apply.
by apply: rel_set_map_pair.
Qed.

Lemma natural_bng_mon {P Q R S}: forall (f : ⊢ P ⊸ R) (g : ⊢ Q ⊸ S),
  tns_fun (bng_fun f) (bng_fun g); bng_mon = bng_mon; bng_fun (tns_fun f g).
Proof.
move=>/=[??][??]/=; rewrite pair_equal_spec; split=>//.
apply: functional_extensionality=>?; rewrite pair_equal_spec.
by split;
(apply: functional_extensionality=>?;
 rewrite !map_set !set_set !map_map;
 do!f_equal; apply: functional_extensionality; case).
Qed.

Definition bng_true : ⊢ [true] ⊸ ![true].
Proof.
split=>//= z.
by apply/ctx_intro/(Rlist.run z tt).
Defined.

Lemma rel_tt (l : Rlist unit ctx): @rel_bng [true] rel tt l
with relnode_tt (n : Rnode unit ctx): @rel_bng_node [true] rel tt n.
Proof.
- case: l=>?; rewrite !rel_bng_simpl.
  by apply: relnode_tt.
case: n=>/=; first by rewrite !rel_bng_nil.
by move=>??; rewrite rel_bng_cons.
Qed.

Lemma Valid_bng_true : Valid bng_true.
Proof.
split=>/=[[[]?]][_]; apply.
by exact: rel_tt.
Qed.

Definition der {X} : ⊢ !X ⊸ X.
Proof.
split=>//= x.
by exact: (lift x).
Defined.

Lemma Valid_der {X} : Valid (@der X).
Proof.
split=>/= [[??]][].
by rewrite rel_bng_simpl rel_bng_cons; case.
Qed.

Lemma natural_der {X Y}: forall (f : ⊢ X ⊸ Y),
  der; f = bng_fun f; der.
Proof. by move=>/=[]. Qed.

Definition dig {X} : ⊢ !X ⊸ !!X.
Proof. by split=>//= ?; apply: concat. Defined.

Lemma rel_concat {X} (u : W X) (v : Rlist (W X) (Rlist (W X) (C X))) :
 rel_bng rel u (concat v) -> @rel_bng !X rel u v
with relnode_concat {X} (u : W X) (v : Rnode (W X) (Rlist (W X) (C X))) :
 rel_bng_node rel u (concat_node v u) -> @rel_bng_node !X rel u v.
Proof.
- case: v=>?/=; rewrite !rel_bng_simpl.
  by exact: relnode_concat.
case: v=>/=; first by rewrite !rel_bng_nil.
move=>[n]z/=; rewrite rel_bng_cons /= rel_bng_simpl.
case: (n u)=>/=.
- rewrite rel_bng_nil=>H; split=>//.
  case: z H=>? /=; rewrite rel_bng_simpl.
  by exact: relnode_concat.
move=>??; rewrite !rel_bng_cons=>[[?]] /rel_bng_cat [??]; do!split=>//.
by apply: rel_concat.
Qed.

Lemma Valid_dig {X} : Valid (@dig X).
Proof.
split=>/=[[??]][?]; apply.
by apply: rel_concat.
Qed.

Lemma natural_dig {X Y}: forall (f : ⊢ X ⊸ Y),
  dig; bng_fun (bng_fun f) = bng_fun f; dig.
Proof.
move=>/=[??]/=; rewrite pair_equal_spec; split=>//.
apply: functional_extensionality=>?.
by rewrite map_concat set_concat -map_map.
Qed.

Lemma dig_der_id_1 {X}: @dig X; der = identity.
Proof.
rewrite /= pair_equal_spec; split=>//.
apply: functional_extensionality=>[[?]] /=.
by under eq_rnode=>? do rewrite cat_id_r_node.
Qed.

Lemma dig_der_id_2 {X}: @dig X; bng_fun der = identity.
Proof.
rewrite /= pair_equal_spec; split=>//.
apply: functional_extensionality=>l.
by rewrite set_id; apply: concat_lift.
Qed.

Lemma dig_assoc {X}: @dig X; dig = dig; bng_fun dig.
Proof.
rewrite /= pair_equal_spec; split=>//.
apply: functional_extensionality=>?.
by rewrite set_id concat_map.
Qed.

Lemma der_mon {X Y}: @bng_mon X Y; der = tns_fun der der.
Proof.
rewrite /= pair_equal_spec; split;
by apply: functional_extensionality=>[[]].
Qed.

Lemma dig_mon {X Y}: @bng_mon X Y; dig = tns_fun dig dig; bng_mon; bng_fun bng_mon.
Proof.
rewrite /= pair_equal_spec; split; first by apply: functional_extensionality=>[[]].
apply: functional_extensionality=>?; rewrite pair_equal_spec; split;
by apply: functional_extensionality=>?; rewrite map_concat set_concat map_set !map_map set_id.
Qed.

Definition wkn {X} : ⊢ !X ⊸ [true].
Proof.
split=>//=.
move=>?; exact: nil.
Defined.

Lemma Valid_wkn {X} : Valid (@wkn X).
Proof. by split=>/= [[??]][]. Qed.

Lemma natural_wkn {X Y}: forall (f : ⊢ X ⊸ Y), bng_fun f; (@wkn Y) = wkn.
Proof. by move=>/=[]. Qed.

Definition dup {X} : ⊢ !X ⊸ !X ⊗ !X.
Proof.
split=>//= [[xl xr]].
by exact: (cat (collapse xl) (collapse xr)).
Defined.

Lemma Valid_dup {X} : Valid (@dup X).
Proof.
split=>/=[[u [xl xr]]][]; rewrite /collapse rel_bng_simpl.
case: (xl u)=>? /=.
rewrite rel_bng_simpl=>/rel_bng_app_node [?]; rewrite rel_bng_simpl.
by case: (xr u)=>??; apply.
Qed.

Lemma natural_dup {X Y}: forall (f : ⊢ X ⊸ Y),
  bng_fun f; dup = dup; tns_fun (bng_fun f) (bng_fun f).
Proof.
move=>/=[fl fr]/=; rewrite pair_equal_spec; split=>//.
apply: functional_extensionality=>[[xl xr]] /=; apply: eq_rnode=>r.
rewrite /collapse /= map_cat_node set_cat_node /=.
case: (xl (fl r))=>/= ?; f_equal; apply: eq_rnode=>q /=.
by case: (xr (fl q)).
Qed.

Lemma dig_comon {X}: @dig X; dup = dup; tns_fun dig dig.
Proof.
rewrite /= pair_equal_spec; split=>//.
apply: functional_extensionality=>[[fl fr]]/=.
apply: eq_rnode=>r; rewrite /collapse concat_cat_node /=.
case: (fl r)=>? /=; f_equal; apply: eq_rnode=>q.
by case: (fr q).
Qed.

Definition dup_mon_comm {P Q R S} : ⊢ (P ⊗ Q) ⊗ (R ⊗ S) ⊸ (P ⊗ R) ⊗ (Q ⊗ S).
Proof.
split=>/=.
- by move=>[[??][??]].
by move=>[zl zr]; split; move=>[??]; (split=>?; [case: zl| case: zr]=>//);
[move=>+?|move=>+?|move=>?|move=>?]; apply.
Defined.

Lemma dup_mon {X Y}:
  @bng_mon X Y; dup = tns_fun dup dup; dup_mon_comm; tns_fun bng_mon bng_mon.
Proof.
rewrite /= pair_equal_spec; split=>//.
- by apply: functional_extensionality=>[[]].
apply: functional_extensionality=>[[fl fr]]/=.
rewrite pair_equal_spec; split=>//;
apply: functional_extensionality=>u; apply: eq_rnode=>v;
rewrite /collapse /= map_cat_node set_cat_node /=.
- case: (fl (u,v))=>? /=; f_equal; apply: eq_rnode=>w /=.
  by case: (fr (u,w)).
case: (fl (v,u))=>? /=; f_equal; apply: eq_rnode=>w /=.
by case: (fr (w,u)).
Qed.

(** Quantifiers *)

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
by move=>? x; move: (f x)=>/=[?]; apply.
Defined.

Lemma Valid_Exists_elim {ty A B f}:
  (forall x, Valid (f x)) -> Valid (@Exists_elim ty A B f).
Proof.
move=>Hf; split=>/= [[[x v] u]]; move: (Hf x)=>[].
move: (f x)=>/=[??] H [??].
apply: (H (v,u)); split=>//.
by apply: rel_bng_not_not.
Qed.
