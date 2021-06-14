From Coq Require Import ssreflect FunctionalExtensionality.
From mathcomp Require Import seq.

Set Bullet Behavior "None".
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Unset Elimination Schemes.

(* The result of combining the list monad transformer with the reader monad on type R *)
Inductive Rlist (R : Type) (A : Type) := rnode of (R -> Rnode R A)
with Rnode (R : Type) (A : Type) := rnil | rcons of A & Rlist R A.

Lemma eq_rnode {R A}:
  forall f1 f2 : R -> Rnode R A,
  (forall r, f1 r = f2 r) ->
  rnode f1 = rnode f2.
Proof. by move=>?? /functional_extensionality ->. Qed.

Definition t := Rlist.

Arguments rnode [_ _] f.
Arguments rnil {_ _}.
Arguments rcons [_ _] x l.

Definition nil {R A} : Rlist R A := rnode (fun _ => rnil).
Definition cons {R A} (x : R -> A) (l : Rlist R A) : Rlist R A :=
  rnode (fun r => rcons (x r) l).

Definition lift {R A} (x : A) := @rnode R A (fun _ => rcons x (rnode (fun _ => rnil))).

Fixpoint run {R A} (l : Rlist R A) (r : R) : seq A :=
  let: rnode n := l in
  run_node (n r) r

with run_node {R A} (n : Rnode R A) (r : R) : seq A :=
match n with
| rnil => [::]
| rcons x l => x :: run l r
end.

Fixpoint app {R A} (l1 l2 : Rlist R A) : Rlist R A :=
  let: rnode n := l1 in
  rnode (fun r => app_node (n r) l2 r)

with app_node {R A} (n : Rnode R A) (l2 : Rlist R A) : R -> Rnode R A :=
match n with
| rnil => fun r => match l2 with rnode n => n r end
| rcons x l1 => fun r => rcons x (app l1 l2)
end.

Lemma app_id_r {R A} : forall l : Rlist R A,
  app l nil = l
with app_id_r_node {R A} : forall (n : Rnode R A) r,
  app_node n nil r = n.
Proof.
- by case=>?/=; under eq_rnode=>? do rewrite app_id_r_node.
by case=>//= ???; rewrite app_id_r.
Qed.

Lemma app_id_l {R A} : forall l : Rlist R A,
  app nil l = l.
Proof. by case. Qed.

Lemma app_assoc {R A} : forall l1 l2 l3 : Rlist R A,
  app l1 (app l2 l3) = app (app l1 l2) l3
with app_assoc_node {R A} : forall (n1 : Rnode R A) (l2 l3 : Rlist R A) r,
  app_node n1 (app l2 l3) r = app_node (app_node n1 l2 r) l3 r.
Proof.
- by case=>???/=; under eq_rnode=>? do rewrite app_assoc_node.
case=>/=; first by case.
by move=>?????; rewrite app_assoc.
Qed.

Fixpoint map {R A B} (f : A -> B) (l : Rlist R A) : Rlist R B :=
  let: rnode n := l in
  rnode (fun r => map_node f (n r))
with map_node {R A B} (f : A -> B) (n : Rnode R A) :=
match n with
| rnil => rnil
| rcons x l => rcons (f x) (map f l)
end.

Lemma map_app {R A B}: forall (f : A -> B) (l1 l2 : Rlist R A),
  map f (app l1 l2) = app (map f l1) (map f l2)
with map_app_node {R A B}: forall (f : A -> B) (n1 : Rnode R A) l2 r,
  map_node f (app_node n1 l2 r) = app_node (map_node f n1) (map f l2) r.
Proof.
- by move=>?[?]?/=; under eq_rnode=>? do rewrite map_app_node.
move=>?; case=>/=; first by case.
by move=>????; rewrite map_app.
Qed.

Lemma map_map {R A B C} : forall (f : A -> B) (g : B -> C) (l : Rlist R A),
  map g (map f l) = map (fun x => g (f x)) l
with map_map_node {R A B C} : forall (f : A -> B) (g : B -> C) (n : Rnode R A),
  map_node g (map_node f n) = map_node (fun x => g (f x)) n.
Proof.
- by move=>??[?]/=; under eq_rnode=>? do rewrite map_map_node.
move=>??; case=>//=??.
by rewrite map_map.
Qed.

Lemma map_id {R A} : forall l : Rlist R A, map id l = l
with map_id_node {R A} : forall n : Rnode R A, map_node id n = n.
Proof.
- by case=>?/=; under eq_rnode=>? do rewrite map_id_node.
by case=>//=??; rewrite map_id.
Qed.

Fixpoint set {R S A} (g : S -> R) (l : Rlist R A) : Rlist S A :=
  let: rnode n := l in
  rnode (fun r => set_node g (n (g r)))
with set_node {R S A} (g : S -> R) (n : Rnode R A) :=
match n with
| rnil => rnil
| rcons x l => rcons x (set g l)
end.

Lemma set_app {R S A} : forall (g : S -> R) (l1 l2 : Rlist R A),
  set g (app l1 l2) = app (set g l1) (set g l2)
with set_app_node {R S A} : forall (g : S -> R) (n1 : Rnode R A) l2 r,
  set_node g (app_node n1 l2 (g r)) = app_node (set_node g n1) (set g l2) r.
Proof.
- by move=>?[?]?/=; under eq_rnode=>? do rewrite set_app_node.
move=>?; case=>/=; first by case.
by move=>????; rewrite set_app.
Qed.

Lemma map_set {R S A B} : forall (f : A -> B) (g : S -> R) l,
  map f (set g l) = set g (map f l)
with map_set_node {R S A B} : forall (f : A -> B) (g : S -> R) n,
  map_node f (set_node g n) = set_node g (map_node f n).
Proof.
- by move=>??[?]/=; under eq_rnode=>? do rewrite map_set_node.
move=>??; case=>//=??.
by rewrite map_set.
Qed.

Lemma set_set {R S T A} : forall (f : S -> R) (g : T -> S) (l : Rlist R A),
  set g (set f l) = set (fun r => f (g r)) l
with set_set_node {R S T A} : forall (f : S -> R) (g : T -> S) (n : Rnode R A),
  set_node g (set_node f n) = set_node (fun r => f (g r)) n.
Proof.
- by move=>??[?]/=; under eq_rnode=>? do rewrite set_set_node.
move=>??; case=>//=??.
by rewrite set_set.
Qed.

Lemma set_id {R A} : forall l : Rlist R A, set id l = l
with set_id_node {R A} : forall (n : Rnode R A), set_node id n = n.
Proof.
- by case=>?/=; under eq_rnode=>? do rewrite set_id_node.
by case=>//=??; rewrite set_id.
Qed.

Fixpoint concat {R A} (l : Rlist R (Rlist R A)) : Rlist R A :=
  let: rnode n := l in
  rnode (fun r => concat_node (n r) r)

with concat_node {R A} (n : Rnode R (Rlist R A)) : R -> Rnode R A :=
match n with
| rnil => fun _ => rnil
| rcons x l => fun r => let: rnode n := app x (concat l) in n r
end.

Lemma concat_app {R A} : forall l1 l2 : Rlist R (Rlist R A),
  concat (app l1 l2) = app (concat l1) (concat l2)
with concat_app_node {R A} : forall (n1 : Rnode R (Rlist R A)) l2 r,
  concat_node (app_node n1 l2 r) r = app_node (concat_node n1 r) (concat l2) r.
Proof.
- by case=>/=??; under eq_rnode=>? do rewrite concat_app_node.
case=>/=; case=>? // ???; rewrite concat_app /=.
by exact: app_assoc_node.
Qed.

Lemma concat_map {R A} : forall l : Rlist R (Rlist R (Rlist R A)),
  concat (concat l) = concat (map concat l)
with concat_map_node {R A} : forall (n : Rnode R (Rlist R (Rlist R A))) r,
  concat_node (concat_node n r) r = concat_node (map_node concat n) r.
Proof.
- by case=>?/=; under eq_rnode=>? do rewrite concat_map_node.
case=>//=; case=>???.
rewrite -concat_map /=.
by exact: concat_app_node.
Qed.

Lemma map_concat {R A B} : forall (f : A -> B) (l : Rlist R (Rlist R A)),
  map f (concat l) = concat (map (map f) l)
with map_concat_node {R A B} : forall (f : A -> B) (n : Rnode R (Rlist R A)) r,
  map_node f (concat_node n r) = concat_node (map_node (map f) n) r.
Proof.
- by move=>?[?]/=; under eq_rnode=>? do rewrite map_concat_node.
move=>?; case=>//=; case=>???/=.
by rewrite map_app_node map_concat.
Qed.

Lemma set_concat {R S A} : forall (g : S -> R) (l : Rlist R (Rlist R A)),
  set g (concat l) = concat (set g (map (set g) l))
with set_concat_node {R S A} : forall (g : S -> R) (n : Rnode R (Rlist R A)) r,
  set_node g (concat_node n (g r)) = concat_node (set_node g (map_node (set g) n)) r.
Proof.
- by move=>?[?]/=; under eq_rnode=>? do rewrite set_concat_node.
move=>?; case=>//=; case=>???/=.
by rewrite set_app_node set_concat.
Qed.

Definition collapse {R A} (f : R -> Rlist R A) : Rlist R A :=
  rnode (fun r => let: rnode n := f r in n r).

Lemma collapse_app {R A} : forall f g : R -> Rlist R A,
  collapse (fun r => app (f r) (collapse g)) = app (collapse f) (collapse g).
Proof.
move=>f ?; rewrite /collapse /=.
by apply: eq_rnode=>?; case: (f _).
Qed.

Fixpoint fold_right {R A B} (f : A -> (R -> B) -> (R -> B)) (accu : R -> B) (l : Rlist R A) (r : R) : B :=
let: rnode n := l in
fold_right_node f accu (n r) r

with fold_right_node {R A B} (f : A -> (R -> B) -> (R -> B)) (accu : R -> B) (n : Rnode R A) (r : R) : B :=
match n with
| rnil => accu r
| rcons x l => f x (fold_right f accu l) r
end.
