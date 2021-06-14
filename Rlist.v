From Coq Require Import ssreflect ssrfun FunctionalExtensionality.
From mathcomp Require Import seq.

Set Bullet Behavior "None".
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Unset Elimination Schemes.

(* The result of combining the list monad transformer with the reader monad on type R *)
Inductive Rlist (R : Type) (A : Type) := rnode of (R -> Rnode R A)
with Rnode (R : Type) (A : Type) := rnil | rcons of A & Rlist R A.

Definition unwrap {R A} (l : Rlist R A) : R -> Rnode R A :=
  let: rnode n := l in n.

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

Definition lift {R A} (x : A) := @rnode R A (fun _ => rcons x nil).

Fixpoint run {R A} (l : Rlist R A) (r : R) : seq A :=
  run_node (unwrap l r) r

with run_node {R A} (n : Rnode R A) (r : R) : seq A :=
match n with
| rnil => [::]
| rcons x l => x :: run l r
end.

Fixpoint cat {R A} (l1 l2 : Rlist R A) : Rlist R A :=
  rnode (fun r => cat_node (unwrap l1 r) l2 r)

with cat_node {R A} (n : Rnode R A) (l2 : Rlist R A) : R -> Rnode R A :=
match n with
| rnil => unwrap l2
| rcons x l1 => fun _ => rcons x (cat l1 l2)
end.

Lemma cat_id_r {R A} : forall l : Rlist R A,
  cat l nil = l
with cat_id_r_node {R A} : forall (n : Rnode R A) r,
  cat_node n nil r = n.
Proof.
- by case=>?/=; under eq_rnode=>? do rewrite cat_id_r_node.
by case=>//= ???; rewrite cat_id_r.
Qed.

Lemma cat_id_l {R A} : forall l : Rlist R A,
  cat nil l = l.
Proof. by case. Qed.

Lemma cat_assoc {R A} : forall l1 l2 l3 : Rlist R A,
  cat l1 (cat l2 l3) = cat (cat l1 l2) l3
with cat_assoc_node {R A} : forall (n1 : Rnode R A) (l2 l3 : Rlist R A) r,
  cat_node n1 (cat l2 l3) r = cat_node (cat_node n1 l2 r) l3 r.
Proof.
- by case=>???/=; under eq_rnode=>? do rewrite cat_assoc_node.
case=>/=; first by case.
by move=>?????; rewrite cat_assoc.
Qed.

Fixpoint map {R A B} (f : A -> B) (l : Rlist R A) : Rlist R B :=
  rnode (map_node f \o unwrap l)
with map_node {R A B} (f : A -> B) (n : Rnode R A) :=
match n with
| rnil => rnil
| rcons x l => rcons (f x) (map f l)
end.

Lemma map_cat {R A B}: forall (f : A -> B) (l1 l2 : Rlist R A),
  map f (cat l1 l2) = cat (map f l1) (map f l2)
with map_cat_node {R A B}: forall (f : A -> B) (n1 : Rnode R A) l2 r,
  map_node f (cat_node n1 l2 r) = cat_node (map_node f n1) (map f l2) r.
Proof.
- by move=>?[?]?/=; under eq_rnode=>? do rewrite /= map_cat_node.
move=>?; case=>/=; first by case.
by move=>????; rewrite map_cat.
Qed.

Lemma map_map {R A B C} : forall (f : A -> B) (g : B -> C) (l : Rlist R A),
  map g (map f l) = map (g \o f) l
with map_map_node {R A B C} : forall (f : A -> B) (g : B -> C) (n : Rnode R A),
  map_node g (map_node f n) = map_node (g \o f) n.
Proof.
- by move=>??[?]/=; under eq_rnode=>? do rewrite /= map_map_node.
move=>??; case=>//=??.
by rewrite map_map.
Qed.

Lemma map_id {R A} : forall l : Rlist R A, map id l = l
with map_id_node {R A} : forall n : Rnode R A, map_node id n = n.
Proof.
- by case=>?/=; under eq_rnode=>? do rewrite /= map_id_node.
by case=>//=??; rewrite map_id.
Qed.

Fixpoint set {R S A} (g : S -> R) (l : Rlist R A) : Rlist S A :=
  rnode (set_node g \o unwrap l \o g)
with set_node {R S A} (g : S -> R) (n : Rnode R A) :=
match n with
| rnil => rnil
| rcons x l => rcons x (set g l)
end.

Lemma set_cat {R S A} : forall (g : S -> R) (l1 l2 : Rlist R A),
  set g (cat l1 l2) = cat (set g l1) (set g l2)
with set_cat_node {R S A} : forall (g : S -> R) (n1 : Rnode R A) l2 r,
  set_node g (cat_node n1 l2 (g r)) = cat_node (set_node g n1) (set g l2) r.
Proof.
- by move=>?[?]?/=; under eq_rnode=>? do rewrite /= set_cat_node.
move=>?; case=>/=; first by case.
by move=>????; rewrite set_cat.
Qed.

Lemma map_set {R S A B} : forall (f : A -> B) (g : S -> R) l,
  map f (set g l) = set g (map f l)
with map_set_node {R S A B} : forall (f : A -> B) (g : S -> R) n,
  map_node f (set_node g n) = set_node g (map_node f n).
Proof.
- by move=>??[?]/=; under eq_rnode=>? do rewrite /= map_set_node.
move=>??; case=>//=??.
by rewrite map_set.
Qed.

Lemma set_set {R S T A} : forall (f : S -> R) (g : T -> S) (l : Rlist R A),
  set g (set f l) = set (f \o g) l
with set_set_node {R S T A} : forall (f : S -> R) (g : T -> S) (n : Rnode R A),
  set_node g (set_node f n) = set_node (f \o g) n.
Proof.
- by move=>??[?]/=; under eq_rnode=>? do rewrite /= set_set_node.
move=>??; case=>//=??.
by rewrite set_set.
Qed.

Lemma set_id {R A} : forall l : Rlist R A, set id l = l
with set_id_node {R A} : forall (n : Rnode R A), set_node id n = n.
Proof.
- by case=>?/=; under eq_rnode=>? do rewrite /= set_id_node.
by case=>//=??; rewrite set_id.
Qed.

Fixpoint concat {R A} (l : Rlist R (Rlist R A)) : Rlist R A :=
  rnode (fun r => concat_node (unwrap l r) r)

with concat_node {R A} (n : Rnode R (Rlist R A)) : R -> Rnode R A :=
match n with
| rnil => fun _ => rnil
| rcons x l => unwrap (cat x (concat l))
end.

Lemma concat_cat {R A} : forall l1 l2 : Rlist R (Rlist R A),
  concat (cat l1 l2) = cat (concat l1) (concat l2)
with concat_cat_node {R A} : forall (n1 : Rnode R (Rlist R A)) l2 r,
  concat_node (cat_node n1 l2 r) r = cat_node (concat_node n1 r) (concat l2) r.
Proof.
- by case=>/=??; under eq_rnode=>? do rewrite concat_cat_node.
case=>/=; case=>? // ???; rewrite concat_cat /=.
by exact: cat_assoc_node.
Qed.

Lemma concat_map {R A} : forall l : Rlist R (Rlist R (Rlist R A)),
  concat (concat l) = concat (map concat l)
with concat_map_node {R A} : forall (n : Rnode R (Rlist R (Rlist R A))) r,
  concat_node (concat_node n r) r = concat_node (map_node concat n) r.
Proof.
- by case=>?/=; under eq_rnode=>? do rewrite concat_map_node.
case=>//=; case=>???.
rewrite -concat_map /=.
by exact: concat_cat_node.
Qed.

Lemma map_concat {R A B} : forall (f : A -> B) (l : Rlist R (Rlist R A)),
  map f (concat l) = concat (map (map f) l)
with map_concat_node {R A B} : forall (f : A -> B) (n : Rnode R (Rlist R A)) r,
  map_node f (concat_node n r) = concat_node (map_node (map f) n) r.
Proof.
- by move=>?[?]/=; under eq_rnode=>? do rewrite /= map_concat_node.
move=>?; case=>//=; case=>???/=.
by rewrite map_cat_node map_concat.
Qed.

Lemma set_concat {R S A} : forall (g : S -> R) (l : Rlist R (Rlist R A)),
  set g (concat l) = concat (set g (map (set g) l))
with set_concat_node {R S A} : forall (g : S -> R) (n : Rnode R (Rlist R A)) r,
  set_node g (concat_node n (g r)) = concat_node (set_node g (map_node (set g) n)) r.
Proof.
- by move=>?[?]/=; under eq_rnode=>? do rewrite /= set_concat_node.
move=>?; case=>//=; case=>???/=.
by rewrite set_cat_node set_concat.
Qed.

Lemma concat_lift {R A} : forall (u : Rlist R A), concat (map lift u) = u
with concat_lift_node {R A} : forall (v : Rnode R A) (u : R), concat_node (map_node lift v) u = v.
Proof.
- case=>? /=.
  by under eq_rnode=>? do rewrite concat_lift_node.
case=>//= ? r /=; rewrite concat_lift.
by case: r.
Qed.

Definition collapse {R A} (f : R -> Rlist R A) : Rlist R A :=
  rnode (fun r => unwrap (f r) r).

Lemma collapse_cat {R A} : forall f g : R -> Rlist R A,
  collapse (fun r => cat (f r) (collapse g)) = cat (collapse f) (collapse g).
Proof.
move=>f ?; rewrite /collapse /=.
by apply: eq_rnode=>?; case: (f _).
Qed.

Fixpoint fold_right {R A B} (f : A -> (R -> B) -> (R -> B)) (accu : R -> B) (l : Rlist R A) (r : R) : B :=
fold_right_node f accu (unwrap l r) r

with fold_right_node {R A B} (f : A -> (R -> B) -> (R -> B)) (accu : R -> B) (n : Rnode R A) (r : R) : B :=
match n with
| rnil => accu r
| rcons x l => f x (fold_right f accu l) r
end.
