(* =========================================================== *)
(**
* Coq Proof for denotational and operational semantics equivalence on a formal interaction language for modelling distributed systems
Erwan Mahe - 2021

We use Coq to:
- formally encode an Interaction Language for modelling the behavior of distributed systems
- define a formal semantics in denotational style on this language
- define another formal semantics, this time in operational style
- prove the equivalence of those two semantics

This proof accompanies the manuscript of my thesis

The coq file itself is hosted on the following repository:
- #<a href="https://github.com/erwanM974/coq_hibou_label_sem_eq_dn_op">https://github.com/erwanM974/coq_hibou_label_sem_eq_dn_op</a># 

** Context

This formal semantics defines which are the behaviors that are specified by an interaction model 
(akin to Message Sequence Charts or UML Sequence Diagrams).
Those behaviors are described by traces which are sequences of atomic actions that can be observed 
on the interfaces of a distributed system's sub-systems.
Those atomic actions correspond to the occurence of communication events i.e. either the emission or the reception of
a given message on a given sub-system.

The definition of formal semantics on this interaction language is done here in two different styles:
- a _denotational-style_, which consists in constructing sets of accepted traces by _composition_ and using algebraic properties of some operators on sets of traces
- an _operational-style_, which consists in considering which actions can be immediately executed in a given interaction, constructing the interaction term that remains to be executed via term rewriting, and constructing the semantics using _recursion_ on the semantics of those remaining interactions

** Dependencies
Below are listed the libraries required for this Coq proof.
- "Coq.Lists.List." provides utilities on lists. I use lists - among other things - to represent traces.
- "Coq.Vectors.Fin." provides a means to represent finite sets indexed by {1,...,n}.
- "Psatz." is required for using the "lia" tactic to solve simple arithemtic problems.
- "Coq.Program.Equality." is required for using the "dependent induction" tactic with "generalizing", allowing the generalisation of some variables of the problem in the induction hypothesis.
- "Coq.Init.Logic." for (among other things) the "not_eq_sym" theorem
- "Coq.Init.Nat.", "Coq.Arith.PeanoNat." and "Coq.Arith.Peano_dec." for the manipulation of natural integers and the use of some lemmas
**)

Require Import Coq.Lists.List.
Require Coq.Vectors.Fin.
Require Import Psatz.
Require Import Coq.Program.Equality.
Require Import Coq.Init.Logic. 
Require Import Coq.Init.Nat.
Require Import Coq.Arith.PeanoNat.
Require Import Coq.Arith.Peano_dec.

(**
* Preliminaries

This section is dedicated to enoncing some basic types and properties on which the remainder of the proof will be based.

** Basic Properties

Let us start by stating some basic properties on integers and lists that will be usefull in the remainder of the proof:
- "eq_or_not_eq_nat" corresponds to the decidability of the equality for natural integers
- "non_empty_nat_is_succ" states that, if a natural integer is not zero then it has a predecessor
- "list_not_empty_is_cons" states that, if a list is not empty then it has a head and a tail
- "cons_eq_app" states that, if a list composed of a head and a tail is equal to the concatenation of two lists then either the first list is empty or it can be decomposed as the head and another tail
**)

Lemma eq_or_not_eq_nat (x y:nat) :
  (x = y) \/ (x<>y).
Proof.
pose proof (eq_nat_dec x y).
destruct H.
- destruct e.
  left. reflexivity.
- right. assumption.
Qed.

Lemma non_empty_nat_is_succ (x:nat) :
  (x <> 0)
  -> (exists n:nat, x = S n).
Proof.
intros.
induction x.
- contradiction.
- exists x. reflexivity.
Qed.

Lemma list_not_empty_is_cons (A:Type) (l:list A) :
 (l<>nil) -> (exists (a:A) (l':list A), l = a :: l').
Proof.
intros.
induction l.
- contradiction.
- exists a. exists l. reflexivity.
Qed.

Theorem cons_eq_app (A : Type) (l l1 l2:list A) (a:A) :
      (a :: l = l1 ++ l2) 
      -> 
       ( (l1 = nil /\ l2 = a::l)
         \/ (exists (l1':list A), l1 = a :: l1')
       ).
Proof.
intros H.
dependent induction l1.
- simpl in *.
  left.
  symmetry in H.
  split.
  + reflexivity.
  + assumption.
- simpl in *.
  right.
  inversion H.
  destruct H1.
  exists l1.
  reflexivity.
Qed.

(**
** Substitutions and eliminations of elements in lists

In the following, I define some functions to manipulate lists. 
To do so, I use Fixpoints and as a result those functions are checked by Coq's termination checker.

- "list_replace_nth" replaces the "n-th" element of a list by another element
- "list_remove_nth" removes the "n-th" element of a list

Some tests (defined as Lemmas) ascertain the effect of those functions

The "list_remove_keep_in" Lemma states that, if one were to find an element "x" in a list
resulting from the removal of another element, then this "x" element must also be in the original list.
**)

Fixpoint list_replace_nth (A:Type) (n:nat) (l:list A) (x:A) {struct l} : list A :=
    match n, l with
      | O, e :: l' => x :: l'
      | O, other => nil
      | S m, nil => nil
      | S m, e :: l' => e :: (list_replace_nth A m l' x)
    end.

Lemma test_list_replace_nth_1 :
  list_replace_nth nat 0 (12::nil) 1 = 1::nil.
Proof.
simpl. reflexivity.
Qed.

Lemma test_list_replace_nth_2 :
  list_replace_nth nat 1 (12::13::nil) 1 = 12::1::nil.
Proof.
simpl. reflexivity.
Qed.

Fixpoint list_remove_nth (A:Type) (n:nat) (l:list A) {struct l} : list A :=
    match n, l with
      | O, e :: l' => l'
      | O, other => nil
      | S m, nil => nil
      | S m, e :: l' => e :: (list_remove_nth A m l')
    end.

Lemma test_list_remove_nth_1 :
  list_remove_nth nat 0 (12::nil) = nil.
Proof.
simpl. reflexivity.
Qed.

Lemma test_list_remove_nth_2 :
  list_remove_nth nat 1 (12::13::nil) = 12::nil.
Proof.
simpl. reflexivity.
Qed.

Lemma list_remove_keep_in (A:Type) (n:nat) (l:list A) (x:A) :
   In x (list_remove_nth A n l) -> In x l.
Proof.
intros. 
dependent induction l generalizing n.
- induction n.
  + contradiction.
  + contradiction.
- simpl in *.
  destruct (eq_nat_dec n 0).
  + symmetry in e. destruct e.
    right. assumption.
  + apply non_empty_nat_is_succ in n0. 
    destruct n0. 
    symmetry in H0. destruct H0.
    simpl in H. destruct H.
    * left. assumption.
    * right. apply (IHl x0).
      assumption.
Qed.

(** 
** Signature & Actions

The interaction language that I define depends on a signature that is composed of:
- a set of "lifelines" L, which elements represent the individual sub-systems that can be found in the disctributed system (or some groups of sub-systems via abstraction/refinement)
- a set of "messages" M, which elements represent the individual distinguishable messages that can be exchanged (via asynchronous communication) within (i.e. internally) or without (i.e externally) the distributed system 

Given that I consider finitely many such lifelines and messages, I use finite vectors from "Coq.Vectors.Fin."
to model those sets.
**)

Parameter LCard : nat.
Parameter MCard : nat.

Definition L := Fin.t (S LCard).
Definition M := Fin.t (S MCard).

(**
To distinguish between emissions "a!m" and receptions "b?m" I encode the kind of action ({!,?}) with an inductive type "ActKind".
**)

Inductive ActKind : Set :=
  |ak_snd:ActKind
  |ak_rcv:ActKind.

(**
I can now define actions with the "Action" type via a cartesian product of types L, ActKind and M.

A utility function "lifeline" returns, for any action, the lifeline on which it occurs.
**)

Definition Action :Set:= L*ActKind*M.

Definition lifeline: Action -> L :=
  fun '(_ as l,_,_) => l.

Lemma exists_action_on_lifeline (l:L) :
  (exists a:Action, l = (lifeline a) ).
Proof.
Admitted.

(* =========================================================== *)
(**
* Trace Language (Semantic Domain)

This section is dedicated to the semantic domain of our interaction language i.e. the domain of definition of its semantics.
After defining this domain, I will study the properties of this domain,
notably how one can manipulate its elements through some operators and which are the properties of those operators.

As hinted at ealier, in this modelling framework:
- it is the expected behavior of distributed systems that is modelled
- this behavior is expressed in terms of accepted traces i.e. sequences of atomic actions that may be expressed

The semantic domain is therefore the universe of traces.

The "Trace" type is formally defined below as that of lists of actions ("Action" type).

Functions "list_replace_nth" and "subs_remove" that were defined above to replace and remove elements in generic lists
are aliased and specialised for use in lists of traces as "subs_replace" and "subs_remove"
**)

Definition Trace : Type := list Action.

(**
** Some consideration on the decidability of equalities

In the following I construct the decidability of the equality of traces in several steps:
- in "eq_or_not_eq_actkind" is proven the decidability of the equality for the "ActKind" type. It is immediate given the inductive nature of "ActKind"
- in "eq_or_not_eq_action" is proven the decidability of the equality for the "Action" type. It relies on that of its subtypes L, ActKind and M. We have proven the decidability property for ActKind juste before, and, for L and M, it is provided by the "eq_dec" Lemma from "Coq.Vectors.Fin.". 
- finally, in "eq_or_not_eq_trace" it is proven for the "Trace" type

This last proof relies on a custom induction principle defined and checked in the "double_trace_induction" Lemma.
**)

Lemma eq_or_not_eq_actkind (x y:ActKind) :
  (x = y) \/ (x <> y).
Proof.
induction x; induction y.
- left. reflexivity.
- right. intro. discriminate.
- right. intro. discriminate.
- left. reflexivity.
Qed.

Lemma eq_or_not_eq_action (x y:Action) :
  (x = y) \/ (x <> y).
Proof.
destruct x ; destruct y.
destruct p ; destruct p0.
pose proof (Fin.eq_dec m m0) as Hm.
pose proof (Fin.eq_dec l l0) as Hl.
pose proof (eq_or_not_eq_actkind a a0) as Ha.
destruct Hm ; destruct Hl ; destruct Ha.
- destruct e ; destruct e0 ; destruct H.
  left. reflexivity.
- right. intro. injection H0. intros. contradiction.
- right. intro. injection H0. intros. contradiction.
- right. intro. injection H0. intros. contradiction.
- right. intro. injection H0. intros. contradiction.
- right. intro. injection H0. intros. contradiction.
- right. intro. injection H0. intros. contradiction.
- right. intro. injection H0. intros. contradiction.
Qed.

Lemma double_trace_induction (P: Trace -> Trace -> Prop):
  (P nil nil)
  -> (forall t:Trace, (t<>nil) -> ((P t nil) /\ (P nil t)) ) 
  -> (forall (a1 a2:Action) (t1 t2:Trace), P t1 t2 -> P (a1::t1) (a2::t2) ) ->
    forall (t1 t2:Trace), P t1 t2.
Proof.
intros.
dependent induction t1.
- induction t2.
  + assumption.
  + specialize H0 with (t:=(a::t2)).
    apply H0. intro. discriminate.
- dependent induction t2.
  + specialize H0 with (t:=(a::t1)).
    apply H0. intro. discriminate.
  + apply H1. apply IHt1.
Qed.

Lemma eq_or_not_eq_trace (x y:Trace) :
  (x = y) \/ (x <> y).
Proof.
pose proof double_trace_induction.
specialize H with (P:= (fun x y:Trace => (x = y) \/ (x <> y))).
apply H.
- left. reflexivity. 
- intros. split. 
  + right. assumption.
  + right. apply not_eq_sym. assumption.
- intros. destruct H0.
  + destruct H0.
    pose proof (eq_or_not_eq_action a1 a2).
    destruct H0.
    * destruct H0. left. reflexivity.
    * right. intro. inversion H1. contradiction.
  + right. intro. inversion H1. contradiction.
Qed.


(**
As a side note, let us also remark the "not_eq_or_not_not_eq" Lemma on the decidability
of the unequality of lifelines, which will be usefull later. 
To prove it I use the "eq_dec" Lemma from "Coq.Vectors.Fin.".
**)

Lemma not_eq_or_not_not_eq (x y:L) :
  (x <> y) \/ (not(x<>y)).
Proof.
pose proof (Fin.eq_dec x y).
destruct H.
- right. intro. contradiction.
- left. assumption.
Qed.


(**
** Some operators on traces and some of their algebraic properties

In the following let us focus on four operators on traces:
- the classical concatenation of lists "++" which is extended to traces:
 - for any two traces t1 and t2, there is a single traces t such that t = t1 ++ t2
 - this traces t is defined as the concatenation of t1 and t2 as a single contiguous list
- an interleaving operator on traces
 - for any two traces t1 and t2, there can exist may traces t such that (is_interleaving t1 t2 t)
 - those traces correspond to potential interleavings of the actions from t1 and t2
 - within such a t, one must find all the actions from t1 and all the actions from t2 in the order in which they are found in t1 and t2 respectively
 - however actions from t1 can be put in any order w.r.t. the actions from t2 
- a weak sequencing operator on traces:
 - for any two traces t1 and t2, there can exist may traces t such that (is_weak_seq t1 t2 t)
 - weak sequencing allows some interleaving between the actions from t1 and t2
 - however it is a more restrictive operator than interleaving given that it onlt allows some interleavings and not all
 - the definition of what is allowed or not is reliant upon a conflict operator
 - in a certain prefix of the trace t:
  - actions from t1 can be added freely
  - actions from t2 can only be added if they do not enter into conflict with the actions from t1 that are waiting to be added
 - the notion of conflict correspond to the fact, for two actions, to occur on the same lifeline 
- a special merge operator which merges an ordered list of traces into a single merged trace.
I define this operator in such a way that is is configurable so as to act
as any of three different merge operators:
 - the merging of traces using classical concatenation
 - the merging of traces using the interleaving operator
 - the merging of traces using the weak sequenceing operator

In this section, those four operators will be defined (except for the concatenation which is already provided by Coq)
and some of their properties stated and proven.
**)

(**
*** Concatenation

For the concatenation operator "++", most interesting properties are already shipped with Coq
and can be used in proofs more or less direclty (with "simpl.", "inversion." and so on).

We only define the following two properties:
- "concat_nil_prop0", which states that, for any traces t1 and t2, if t1++t2 is not the empty trace, then either t1 or t2 is not empty
- "concat_split", which states that, for any traces t1, t2 and t, if t1++t2=a::t and t1 is not the empty trace, then it means that t1 begins with a as a head and has a certain tail t3
**)

Lemma concat_nil_prop0 (t1 t2:Trace) :
  (t1 ++ t2 <> nil)
  <-> ( (t1 <> nil) \/ (t2 <> nil) ).
Proof.
pose proof (eq_or_not_eq_trace t1 nil) as H1.
pose proof (eq_or_not_eq_trace t2 nil) as H2.
destruct H1 ; destruct H2.
- symmetry in H. destruct H.
  symmetry in H0. destruct H0.
  split ; intros.
  + simpl in H. contradiction.
  + destruct H ; contradiction.
- symmetry in H. destruct H. simpl.
  split ; intros.
  + right. assumption.
  + assumption.
- symmetry in H0. destruct H0. simpl.
  split ; intros.
  + left. assumption.
  + rewrite app_nil_r. assumption.
- split ; intros.
  + left. assumption.
  + intro. apply app_eq_nil in H2.
    destruct H2. contradiction.
Qed.

Lemma concat_split (a:Action) (t1 t2 t:Trace) :
  ( (t1 ++ t2 = a :: t) /\ (t1 <> nil) )
  -> (exists t3:Trace, (t1 = a :: t3) /\ (t = t3 ++ t2)).
Proof.
intros. destruct H.
induction t1.
- contradiction. 
- clear H0. inversion H. destruct H1.
  exists t1.
  split ; reflexivity.
Qed.


(**
*** Interleaving

I formalise the interleaving operator in Coq using an inductive predicate 
"is_interleaving" such that
"(is_interleaving t1 t2 t)" states the membership of a given trace t
into the set of interleavings between traces t1 and t2.

This inductive predicate can be inferred inductively using four construction rules:
- "interleaving_nil_left" which states that for any trace t, t is an interleaving of the empty trace and t
- "interleaving_nil_right" which states that for any trace t, t is an interleaving of t and the empty trace
- "interleaving_cons_left" which states that for any interleaving t of traces t1 and t2, (a::t) is an interleaving of (a::t1) and t2
- "interleaving_cons_right" which states that for any interleaving t of traces t1 and t2, (a::t) is an interleaving of t1 and (a::t2)

Those two last rules signify that, when constructing an interleaving, we can mix in actions from either traces in any order
**)

Inductive is_interleaving : Trace -> Trace -> Trace -> Prop :=
| interleaving_nil_left   : forall (t:Trace), 
                              (is_interleaving nil t t)
| interleaving_nil_right  : forall (t:Trace), 
                              (is_interleaving t nil t)
| interleaving_cons_left  : forall (t t1 t2:Trace) (a:Action),
                              (is_interleaving t1 t2 t) -> (is_interleaving (a::t1) t2 (a::t))
| interleaving_cons_right : forall (t t1 t2:Trace) (a:Action),
                              (is_interleaving t1 t2 t) -> (is_interleaving t1 (a::t2) (a::t)).

(**
Interesting properties of the "is_interleaving" that will be useful later on include:
- the guarantee of the existence of an interleaving t (at least one) for any traces t1 and t2 "is_interleaving_existence"
- "is_interleaving_nil_prop0" which is the same property as "concat_nil_prop0" but for the interleaving operator instead of the concatenation
- "is_interleaving_nil_prop1", which states that if the empty trace is an interleaving of t1 and t2, then both t1 and t2 must be empty
- "is_interleaving_nil_prop2", which states that if t is an interleaving of the empty trace and t2, then t=t2
- "is_interleaving_nil_prop3", which states that if t is an interleaving of t1 and the empty trace, then t=t1
- "is_interleaving_split" is a similar property as "concat_split" but for the interleaving operator instead of the concatenation
 - let us also note that, given that interleavings are allowed, in contrast to ++, the head action "a" can be found in either t1 or t2 instead of uniquely t1
**)

Lemma is_interleaving_existence (t1 t2:Trace) :
  exists t:Trace, is_interleaving t1 t2 t.
Proof.
dependent induction t1.
- exists t2. apply interleaving_nil_left.
- specialize IHt1 with (t2:=t2).
  destruct IHt1.
  exists (a::x).
  apply interleaving_cons_left.
  assumption.
Qed.

Lemma is_interleaving_nil_prop0 (t1 t2 t:Trace) :
  (is_interleaving t1 t2 t)
  -> (
        (t <> nil)
        <-> ( (t1 <> nil) \/ (t2 <> nil) )
     ).
Proof.
intros H.
dependent induction t generalizing t1 t2.
- inversion H.
  + destruct H0. destruct H1.
    symmetry in H2. destruct H2.
    split ; intros.
    * left. assumption.
    * destruct H0 ; assumption.
  + destruct H0. destruct H1.
    symmetry in H2. destruct H2.
    split ; intros.
    * left. assumption.
    * destruct H0 ; assumption.
- split ; intro.
  + inversion H.
    * right. intro. discriminate.
    * left. assumption.
    * left. intro. discriminate.
    * right. intro. discriminate.
  + intro. discriminate.
Qed.

Lemma is_interleaving_nil_prop1 (t1 t2: Trace) :
  (is_interleaving t1 t2 nil)
  -> ( (t1 = nil) /\ (t2 = nil) ).
Proof.
intros H.
inversion H ; split ; reflexivity.
Qed.

Lemma is_interleaving_nil_prop2 (t t2: Trace) :
  (is_interleaving nil t2 t)
  -> (t2 = t).
Proof.
intros H.
dependent induction H.
- reflexivity.
- reflexivity.
- assert (t2=t).
  { apply IHis_interleaving.
    trivial.
  }
  destruct H0.
  reflexivity.
Qed.

Lemma is_interleaving_nil_prop3 (t1 t: Trace) :
  (is_interleaving t1 nil t)
  -> (t1 = t).
Proof.
intros H.
dependent induction H.
- reflexivity.
- reflexivity.
- assert (t1=t).
  { apply IHis_interleaving.
    trivial.
  }
  destruct H0.
  reflexivity.
Qed.

Lemma is_interleaving_split (a:Action) (t1 t2 t:Trace) :
  (is_interleaving t1 t2 (a :: t))
  -> (
       (exists t3:Trace, (t2=a::t3)/\(is_interleaving t1 t3 t))
       \/ (exists t3:Trace, (t1=a::t3)/\(is_interleaving t3 t2 t))
     ).
Proof.
intros.
dependent induction H.
- left. exists t. split.
  + reflexivity.
  + apply interleaving_nil_left.
- right. exists t. split.
  + reflexivity.
  + apply interleaving_nil_right.
- right. exists t1. split.
  + reflexivity.
  + assumption.
- left. exists t2. split.
  + reflexivity.
  + assumption.
Qed. 

(**
*** Weak Sequencing

As explained earlier, the weak sequencing operator on traces relies upon a notion of "conflict" between actions.
To encode it in code, I define the "no_conflict" inductive predicate such that (no_conflict t a) 
states that there are not actions in t that occur on the same lifeline as action "a".

This predicate can be inferred inductively from the following two rules:
- "no_conflict_nil", which states that for any action "a", there can be no conflict between "a" and the empty trace
- "no_conflict_cons", which states that for any action "a" and trace (a'::t) which starts with action "a'" as its head, if "a" and "a'" occur on different lifelines and there is no conflict between "a" and "t" then there is no conflict between "a" and (a'::t)
**)

Inductive no_conflict : Trace -> Action -> Prop :=
| no_conflict_nil  : forall (a:Action), (no_conflict nil a)
| no_conflict_cons : forall (a a':Action) (t:Trace),
                        (
                          (not ((lifeline a) = (lifeline a')))
                          /\ (no_conflict t a)
                        ) -> (no_conflict (a'::t) a).

(**
As for the interleaving, I formalise the weak sequencing operator in Coq using an inductive predicate 
"is_weak_seq" such that
"(is_weak_seq t1 t2 t)" states the membership of a given trace t
into the set of weakly sequenced traces between traces t1 and t2.

This inductive predicate can be inferred inductively using four construction rules:
- "weak_seq_nil_left" which states that for any trace t, t is a weak sequence of the empty trace and t
- "weak_seq_nil_right" which states that for any trace t, t is a weak sequence of t and the empty trace
- "weak_seq_cons_left" which states that for any weak sequence t of traces t1 and t2, (a::t) is a weak sequence of (a::t1) and t2
- "weak_seq_cons_right" which states that for any weak sequence t of traces t1 and t2, if there is no conflict between "a" and t1 then (a::t) is a weak sequence of t1 and (a::t2)

Those two last rules signify that, when constructing a weak sequence:
- we can freely add actions from the left-hand side trace t1
- but we only allow the addition of events from t2 if they are not preempted by the occurence of events from t1
**)

Inductive is_weak_seq : Trace -> Trace -> Trace -> Prop :=
| weak_seq_nil_left   : forall (t:Trace), 
                              (is_weak_seq nil t t)
| weak_seq_nil_right  : forall (t:Trace), 
                              (is_weak_seq t nil t)
| weak_seq_cons_left  : forall (t t1 t2:Trace) (a:Action),
                              (is_weak_seq t1 t2 t) -> (is_weak_seq (a::t1) t2 (a::t))
| weak_seq_cons_right : forall (t t1 t2:Trace) (a:Action),
                              (is_weak_seq t1 t2 t)
                              -> (no_conflict t1 a) 
                              -> (is_weak_seq t1 (a::t2) (a::t)).

(**
In a similar fashion to what I did for the interleaving operator, I state and prove in the following some properties on the weak sequencing operator:
- the guarantee of the existence of a weak sequence t (at least one) for any traces t1 and t2 "is_weak_seq_existence"
- "is_weak_seq_nil_prop0"
- "is_weak_seq_nil_prop1", which states that if the empty trace is a weak sequence of t1 and t2, then both t1 and t2 must be empty
- "is_weak_seq_nil_prop2", which states that if t is a weak sequence of the empty trace and t2, then t=t2
- "is_weak_seq_nil_prop3", which states that if t is a weak sequence of t1 and the empty trace, then t=t1
- "is_weak_seq_split", which states that if (a :: t) is a weak sequence of t1 and t2, then either t1 starts with "a" or t2 starts with "a" and there is no conflict between t1 and "a"
**)


Lemma is_weak_seq_existence (t1 t2:Trace) :
  exists t:Trace, is_weak_seq t1 t2 t.
Proof.
dependent induction t1.
- exists t2. apply weak_seq_nil_left.
- specialize IHt1 with (t2:=t2).
  destruct IHt1.
  exists (a::x).
  apply weak_seq_cons_left.
  assumption.
Qed.

Lemma is_weak_seq_nil_prop0 (t1 t2 t:Trace) :
  (is_weak_seq t1 t2 t)
  -> (
        (t <> nil)
        <-> ( (t1 <> nil) \/ (t2 <> nil) )
     ).
Proof.
intros H.
dependent induction t generalizing t1 t2.
- inversion H.
  + destruct H0. destruct H1.
    symmetry in H2. destruct H2.
    split ; intros.
    * left. assumption.
    * destruct H0 ; assumption.
  + destruct H0. destruct H1.
    symmetry in H2. destruct H2.
    split ; intros.
    * left. assumption.
    * destruct H0 ; assumption.
- split ; intro.
  + inversion H.
    * right. intro. discriminate.
    * left. assumption.
    * left. intro. discriminate.
    * right. intro. discriminate.
  + intro. discriminate.
Qed.

Lemma is_weak_seq_nil_prop1 (t1 t2: Trace) :
  (is_weak_seq t1 t2 nil)
  -> ( (t1 = nil) /\ (t2 = nil) ).
Proof.
intros H.
inversion H ; split ; reflexivity.
Qed.

Lemma is_weak_seq_nil_prop2 (t1 t2: Trace) :
  (is_weak_seq nil t1 t2)
  -> (t1 = t2).
Proof.
intros H.
assert (H0:=H).
dependent induction H.
- reflexivity.
- reflexivity.
- assert (t2=t).
  { apply IHis_weak_seq.
    - trivial.
    - assumption.
  }
  destruct H2.
  reflexivity.
Qed.

Lemma is_weak_seq_nil_prop3 (t1 t2: Trace) :
  (is_weak_seq t1 nil t2)
  -> (t1 = t2).
Proof.
intros H.
dependent induction H.
- reflexivity.
- reflexivity.
- assert (t1=t).
  { apply IHis_weak_seq.
    trivial.
  }
  destruct H0.
  reflexivity.
Qed.

Lemma is_weak_seq_split (a:Action) (t1 t2 t:Trace) :
  (is_weak_seq t1 t2 (a :: t))
  -> (
       ( (no_conflict t1 a) /\ (exists t3:Trace, (t2=a::t3)/\(is_weak_seq t1 t3 t)) )
       \/ (exists t3:Trace, (t1=a::t3)/\(is_weak_seq t3 t2 t))
     ).
Proof.
intros.
dependent induction H.
- left. split.
  + apply no_conflict_nil.
  + exists t. split.
    * reflexivity.
    * apply weak_seq_nil_left.
- right. exists t. split.
  + reflexivity.
  + apply weak_seq_nil_right.
- right. exists t1. split.
  + reflexivity.
  + assumption.
- left. split.
  + assumption.
  + exists t2.
    split.
    * reflexivity.
    * assumption.
Qed.


(**
*** Remark on the notion of scheduling

The three previously mentioned operators... 
- concatenation (also called strict sequencing)
- weak sequencing
- interleaving

... can be understood as scheduling operators i.e. they allow or disallow some reordering of
events from traces t1 and t2 in the construction of a merged trace t

I encode this notion of a type of scheduling into the inductive type "ScheduleKind" defined below.

**)

Inductive ScheduleKind : Set :=
  |lstrict:ScheduleKind
  |lseq:ScheduleKind
  |lpar:ScheduleKind.


(**
*** Merge operator

The merge operator can be understood as a n-ary extension of the three previously defined scheduling operators.
For any list of traces [t1,t2,...,tn] and for any trace t_merge:
- saying that "t_merge is a merger of [t1,t2,...,tn] according to strict sequencing" signifies that t_merge is the concatenated trace t1++t2++...++tn
- saying that "t_merge is a merger of [t1,t2,...,tn] according to weak sequencing" signifies that t_merge verifies (is_weak_seq t1 t_remain t_merge) with t_remain being "a merger of [t2,...,tn] according to weak sequencing" and so on
- saying that "t_merge is a merger of [t1,t2,...,tn] according to interleaving" signifies that t_merge verifies (is_interleaving t1 t_remain t_merge) with t_remain being "a merger of [t2,...,tn] according to interleaving" and so on

I formalise the merge operator in Coq using an inductive predicate "n_merge_schedule"
such that for any schedule kind lk, for any list of non-empty traces "subs", and for any trace "t",
"(n_merge_schedule lk subs t)" states the membership of a given trace t into the set of mergers of traces from subs according to lk.

This inductive predicate can be inferred inductively using four construction rules:
- a construction rule "merge_zero" for the base case, which states that the empty trace is a merger of an empty list of traces
- and three construction rules, each dedicated to one of the three types of scheduling;
 - "merge_strict", which states that for any strict-merger t of traces from remain (a list of traces), then t1++t is a strict-merger of t1::remain
 - "merge_seq", which states that for any (weak) seq-merger t of traces from remain (a list of traces), then, for any trace t_merge verifying (is_weak_seq t1 t t_merge), we have that t_merge is a seq-merger of t1::remain
 - "merge_par", which states that for any par-merger t of traces from remain (a list of traces), then, for any trace t_merge verifying (is_interleaving t1 t t_merge), we have that t_merge is a par-merger of t1::remain
- let us note that for all three rules, we only allow the addition of non-empty traces in the list of traces to be merged. This is a modelisation choice.
**)
 
Inductive n_merge_schedule : 
  ScheduleKind -> list Trace -> Trace -> Prop :=
| merge_zero    : forall (lk:ScheduleKind),
                    (n_merge_schedule lk nil nil)
| merge_strict : forall (remain:list Trace) (t_first t_rep:Trace),
                    (t_first <> nil)
                    -> (n_merge_schedule lstrict remain t_rep)
                    -> (n_merge_schedule lstrict (t_first::remain) (t_first++t_rep))
| merge_seq    : forall (remain:list Trace) (t_first t_rep t_merge:Trace),
                    (t_first <> nil)
                    -> (n_merge_schedule lseq remain t_rep)
                    -> (is_weak_seq t_first t_rep t_merge)
                    -> (n_merge_schedule lseq (t_first::remain) t_merge)
| merge_par    : forall (remain:list Trace) (t_first t_rep t_merge:Trace),
                    (t_first <> nil)
                    -> (n_merge_schedule lpar remain t_rep)
                    -> (is_interleaving t_first t_rep t_merge)
                    -> (n_merge_schedule lpar (t_first::remain) t_merge).  

(**
In a similar fashion to what was done for the three scheduling operators, 
one can define an prove some properties for the merge operator:
- the guarantee of the existence of a merged trace t (at least one) for any list of traces "subs" "n_merge_schedule_existence"
- "n_merge_schedule_nil_prop0", which states that if the merger of a list of traces is non-empty then there exists a non empty trace in that list of traces
- "n_merge_schedule_nil_prop1", which states that if the empty trace is a merger of a list of traces, then this list of traces is empty
- "n_merge_schedule_nil_prop2", which states that if a trace is a merger of an empty list of traces, then it must be the empty trace
- "n_merge_schedule_nonil_prop0", which states that only non-empty traces are allowed within a list of traces that is used as entry for the merge operator
**)

Lemma n_merge_schedule_existence
  (lk:ScheduleKind) (subs:list Trace) :
   (forall t0:Trace, (In t0 subs) -> (t0<>nil) )
   -> (exists t:Trace, (n_merge_schedule lk subs t)).
Proof.
intros.
dependent induction subs.
- exists nil. apply merge_zero.
- destruct IHsubs.
  + intros. apply H. simpl. right. assumption.
  + destruct lk.
    { exists (a ++ x).
      apply merge_strict. 
      - apply H. simpl. left. reflexivity.
      - assumption.
    } 
    { pose proof (is_weak_seq_existence a x).
      destruct H1 as (t,H1). 
      exists t. 
      apply (merge_seq subs a x t).
      - apply H. simpl. left. reflexivity.
      - assumption.
      - assumption.
    }
    { pose proof (is_interleaving_existence a x).
      destruct H1 as (t,H1). 
      exists t. 
      apply (merge_par subs a x t).
      - apply H. simpl. left. reflexivity.
      - assumption.
      - assumption.
    }
Qed.

Lemma n_merge_schedule_nil_prop0 (lk:ScheduleKind) (subs:list Trace) (t:Trace) :
  (n_merge_schedule lk subs t)
  -> (
        (t <> nil)
        <-> (exists t0:Trace, (In t0 subs) /\ (t0 <> nil))
     ).
Proof.
intros.
split ; intros.
- dependent induction subs.
  + inversion H.
    destruct H3. contradiction.
  + inversion H.
    * destruct H2. destruct H1. destruct H3.
      destruct H5.
      { exists t_first.
        split. 
        - simpl. left. reflexivity.
        - assumption.
      }
    * destruct H2. destruct H1. destruct H4.
      destruct H6.
      { exists t_first.
        split. 
        - simpl. left. reflexivity.
        - assumption.
      }
    * destruct H2. destruct H1. destruct H4.
      destruct H6.
      { exists t_first.
        split. 
        - simpl. left. reflexivity.
        - assumption.
      }
- destruct H0 as (t0,Ht0).
  destruct Ht0 as (Hin,Ht0).
  dependent induction subs.
  + inversion H. contradiction.
  + inversion H.
    * destruct H1. destruct H0. destruct H2.
      destruct H4.
      simpl in *.
      destruct Hin.
      { destruct H0.
        apply (concat_nil_prop0 t_first t_rep).
        left. assumption.
      }
      { apply (concat_nil_prop0 t_first t_rep).
        left. assumption.
      }
    * destruct H1. destruct H0. destruct H3.
      destruct H5.
      simpl in *.
      destruct Hin.
      { destruct H0.
        apply (is_weak_seq_nil_prop0 t_first t_rep).
        - assumption.
        - left. assumption.
      }
      { apply (is_weak_seq_nil_prop0 t_first t_rep).
        - assumption.
        - left. assumption.
      }
    * destruct H1. destruct H0. destruct H3.
      destruct H5.
      simpl in *.
      destruct Hin.
      { destruct H0.
        apply (is_interleaving_nil_prop0 t_first t_rep).
        - assumption.
        - left. assumption.
      }
      { apply (is_interleaving_nil_prop0 t_first t_rep).
        - assumption.
        - left. assumption.
      }
Qed.

Lemma n_merge_schedule_nil_prop1 (lk:ScheduleKind) (subs:list Trace) :
  (n_merge_schedule lk subs nil)
  -> (subs=nil).
Proof.
intros.
inversion H.
- reflexivity.
- destruct H3. apply app_eq_nil in H0.
  destruct H0. symmetry in H3. destruct H3.
  rewrite app_nil_r in H1. contradiction.
- symmetry in H5. destruct H5. apply is_weak_seq_nil_prop1 in H2.
  destruct H2.
  symmetry in H2. destruct H2. contradiction.
- symmetry in H5. destruct H5. apply is_interleaving_nil_prop1 in H2.
  destruct H2.
  symmetry in H2. destruct H2. contradiction.
Qed.

Lemma n_merge_schedule_nil_prop2 (lk:ScheduleKind) (t_merge:Trace) :
  (n_merge_schedule lk nil t_merge)
  -> (t_merge=nil).
Proof.
intros.
dependent induction t_merge.
- reflexivity.
- inversion H.
Qed.

Lemma n_merge_schedule_nonil_prop0 (lk:ScheduleKind) (subs:list Trace) (t:Trace) :
  (n_merge_schedule lk subs t)
  ->(forall t0 : Trace, In t0 subs -> t0<>nil).
Proof.
intros.
dependent induction H.
- contradiction.
- inversion H1. 
  + destruct H2. assumption.
  + apply IHn_merge_schedule. assumption.
- inversion H2. 
  + destruct H3. assumption.
  + apply IHn_merge_schedule. assumption.
- inversion H2. 
  + destruct H3. assumption.
  + apply IHn_merge_schedule. assumption.
Qed.

(**
As I am going to manipulate lists of traces when dealing with the merge operator,
I adapt here below the previously defined functions to replace or remove the n-th element of a list
to lists of traces:
- "subs_replace" replaces the n-th element of list of traces "subs" by a trace "t"
- "subs_remove" removes the n-th element of a list of traces
- "subs_remove_keep_in" is a Lemma stating that if a certain trace is found in a list of traces in which we have remove some elements, then it has to be found in the original list of traces
**)

Definition subs_replace (n:nat) (subs:list Trace) (t:Trace) : list Trace 
  := list_replace_nth Trace n subs t. 

Definition subs_remove (n:nat) (subs:list Trace) : list Trace 
  := list_remove_nth Trace n subs. 

Lemma subs_remove_keep_in (n:nat) (subs:list Trace) (t:Trace) :
   In t (subs_remove n subs) -> In t subs.
Proof.
intros.
apply (list_remove_keep_in (Trace) n subs t).
unfold subs_remove in H.
assumption.
Qed.


(**
*** Some considerations on the distributivity of "no_conflict" w.r.t. the previous operators

In the following we demonstrate the distributive composition of the "no_conflict" function w.r.t. the three scheduling operators and the merge operator 
**)

Lemma no_conflict_concat (t1 t2:Trace) (a:Action) :
  ( (no_conflict t1 a) /\ (no_conflict t2 a) )
  <-> (no_conflict (t1++t2) a).
Proof.
split ; intros H.
- destruct H.
  dependent induction t1.
  + simpl. assumption.
  + simpl. apply no_conflict_cons.
    inversion H.
    destruct H4.
    split.
    * assumption.
    * apply IHt1.
      { assumption. }
      { assumption. }
- dependent induction t1.
  + simpl in H.
    split.
    * apply no_conflict_nil.
    * assumption.
  + simpl in H.
    inversion H.
    destruct H3.
    apply IHt1 in H4.
    destruct H4.
    split.
    * apply no_conflict_cons.
      split.
      { assumption. }
      { assumption. }
    * assumption.
Qed.

Lemma no_conflict_interleaving (t1 t2 t :Trace) (a:Action) :
  (is_interleaving t1 t2 t)
  -> (
       ( (no_conflict t1 a) /\ (no_conflict t2 a) )
       <-> (no_conflict t a)
     ).
Proof.
split ; intros H1. 
- destruct H1.
  dependent induction H.
  + assumption.
  + assumption.
  + apply no_conflict_cons.
    inversion H0. destruct H5.
    split.
    * assumption.
    * apply IHis_interleaving ; assumption.
  + apply no_conflict_cons.
    inversion H1. destruct H5.
    split.
    * assumption.
    * apply IHis_interleaving ; assumption.
- dependent induction H.
  + split.
    * apply no_conflict_nil.
    * assumption.
  + split.
    * assumption.
    * apply no_conflict_nil.
  + inversion H1.
    destruct H4. 
    apply IHis_interleaving in H5.
    destruct H5.
    split.
    * apply no_conflict_cons.
      split ; assumption.
    * assumption.
  + inversion H1.
    destruct H4. 
    apply IHis_interleaving in H5.
    destruct H5.
    split.
    * assumption.
    * apply no_conflict_cons.
      split ; assumption.
Qed.

Lemma no_conflict_weak_seq (t1 t2 t :Trace) (a:Action) :
  (is_weak_seq t1 t2 t)
  -> (
       ( (no_conflict t1 a) /\ (no_conflict t2 a) )
       <-> (no_conflict t a)
     ).
Proof.
split ; intros H1.
- destruct H1.
  dependent induction H.
  + assumption.
  + assumption.
  + apply no_conflict_cons.
    inversion H0. destruct H5.
    split.
    * assumption.
    * apply IHis_weak_seq ; assumption.
  + apply no_conflict_cons.
    inversion H2. destruct H6.
    split.
    * assumption.
    * apply IHis_weak_seq ; assumption.
- dependent induction H.
  + split.
    * apply no_conflict_nil.
    * assumption.
  + split.
    * assumption.
    * apply no_conflict_nil.
  + inversion H1.
    destruct H4. 
    apply IHis_weak_seq in H5.
    destruct H5.
    split.
    * apply no_conflict_cons.
      split ; assumption.
    * assumption.
  + inversion H1.
    destruct H5. 
    apply IHis_weak_seq in H6.
    destruct H6.
    split.
    * assumption.
    * apply no_conflict_cons.
      split ; assumption.
Qed.

Lemma no_conflict_n_merge (lk:ScheduleKind) (subs:list Trace) (t :Trace) (a:Action) :
  (n_merge_schedule lk subs t)
  -> (
       (no_conflict t a) 
       <-> (forall t0:Trace, (In t0 subs) -> (no_conflict t0 a))
     ).
Proof.
intros.
split ; intros.
- dependent induction subs.
  + contradiction.
  + inversion H.
    * destruct H2. destruct H3. destruct H4.
      destruct H6. simpl in *.
      apply (no_conflict_concat t_first t_rep a0) in H0.
      destruct H0.
      destruct H1.
      { destruct H1. assumption. }
      { apply (IHsubs t_rep) ; assumption. }
    * destruct H2. destruct H3. destruct H7.
      destruct H5. simpl in *.
      apply (no_conflict_weak_seq t_first t_rep) in H0.
      { destruct H0.
        destruct H1.
        - destruct H1. assumption.
        - apply (IHsubs t_rep) ; assumption.
      }
      { assumption. }
    * destruct H2. destruct H3. destruct H7.
      destruct H5. simpl in *.
      apply (no_conflict_interleaving t_first t_rep) in H0.
      { destruct H0.
        destruct H1.
        - destruct H1. assumption.
        - apply (IHsubs t_rep) ; assumption.
      }
      { assumption. }
- dependent induction subs.
  + inversion H. apply no_conflict_nil.
  + inversion H.
    * destruct H1. destruct H2. destruct H3.
      destruct H5.
      simpl in *.
      apply no_conflict_concat.
      split.
      { apply H0. left. reflexivity. }
      { apply IHsubs.
        - assumption.
        - intros t0 Ht0. 
          apply H0.
          right. assumption.
      }
    * destruct H1. destruct H2. destruct H4.
      destruct H6.
      simpl in *.
      apply (no_conflict_weak_seq t_first t_rep t_merge).
      { assumption. }
      { split.
        - apply H0. left. reflexivity.
        - apply IHsubs.
          + assumption.
          + intros t0 Ht0. 
            apply H0.
            right. assumption.
      }
    * destruct H1. destruct H2. destruct H4.
      destruct H6.
      simpl in *.
      apply (no_conflict_interleaving t_first t_rep t_merge).
      { assumption. }
      { split.
        - apply H0. left. reflexivity.
        - apply IHsubs.
          + assumption.
          + intros t0 Ht0. 
            apply H0.
            right. assumption.
      }
Qed.



(**
* An Interaction Language and its semantics 

This section is the core of the proof. It is dedicated to:
- the definition of the syntax of the interaction language. This syntax corresponds to the definition of a context-free grammar in which terms are build inductively from some basic terms and the application of some binary constructors to form more complex terms (as binary trees)
- the definition of a denotational-style semantics based on the composition of sets of traces using the previously defined operators on the semantic domain
- the definition of an operational-style semantics and the proof of its equivalence w.r.t. the denotational one

The proof will be introduced in two steps:
- at first we will prove that the operational semantics is included in the denotational semantics. Elements of this proof will be introduced progressively in the same time as we are defining the different functions that take part in the definition of the operational semantics. Once all of those intermediate functions are defined, we will define the operational semantics and its inclusion in the denotational semantics will be almost immediately inferred.
- in a second step, we will prove that the denotational semantics is included in the operational semantics.
**)


(**
** Syntax

We define the "Interaction" type, that inductively define interaction terms.
From basic building blocks which can either be the empty interaction "interaction_empty" or actions (of type "Action"), 
I then use different constructors to construct more complex interaction terms.

Let us describe the Coq definition, which includes 7 rules for the construction of the Interaction type:
- the "interaction_empty" constructor defines the empty interaction that can only express the empty trace nil
- the "interaction_act" cosntructor allows the construction of basic interactions that can only express a single trace (a::nil) for a given action "a"
- the "interaction_strict" constructor allows the construction of composed interactions of the form (interaction_strict i1 i2), where i1 and i2 are other (strictly smaller) interaction terms. (interaction_strict i1 i2) can express traces that are a strict sequencing of some trace expressed by i1 and some other expressed by i2
- likewise, (interaction_seq i1 i2) is an interaction that expresses traces that are weak sequences of traces expressed by i1 and i2
- also, (interaction_par i1 i2) is an interaction that expresses traces that are interleavings of traces expressed by i1 and i2
- the "interaction_alt" constructor allows the definition of interactions that can behave in a certain manner or (non-deterministically) in a certain other manner. Concretely, (interaction_alt i1 i2) expresses traces that are expressed either by i1 or by i2
- finally, the "interaction_loop" constructor allows the definition of interactions in which the behaviors of a given sub-interaction can be repeated an arbitraty number of times. This repetition is done according to one certain scheduling operator out of the three. Concretely:
 - a (interaction_loop lstrict i1) interaction expresses traces which are strict-mergers of traces that can be expressed by i1
 - a (interaction_loop lseq i1) interaction expresses traces which are seq-mergers of traces that can be expressed by i1
 - a (interaction_loop lpar i1) interaction expresses traces which are par-mergers of traces that can be expressed by i1
**)

Inductive Interaction : Set := 
  interaction_empty:Interaction 
  |interaction_act:Action->Interaction
  |interaction_strict:Interaction->Interaction->Interaction
  |interaction_seq:Interaction->Interaction->Interaction
  |interaction_par:Interaction->Interaction->Interaction
  |interaction_alt:Interaction->Interaction->Interaction
  |interaction_loop:ScheduleKind->Interaction->Interaction.


(**
** Denotational Semantics

Following the definition of the syntax, the informal description of the intended meaning of interaction terms,
and the previous preliminaries on the definition of operators for the semantic domain, we can immediately define the
denotational-style semantics as is done below.

We use a Fixpoint to define a function "sem_de" such that (sem_de i t) is a predicate which means that
the trace t can be expressed by the interaction i. 
In other words, this (sem_de i t) predicate states the membership of trace t into the semantics of interaction i.
**)
 
Fixpoint sem_de (i : Interaction) : (Trace -> Prop) :=
match i with
|interaction_empty          => fun t:Trace => 
                                  t = nil
|(interaction_act a)        => fun t:Trace => 
                                  t = a :: nil
|(interaction_alt i1 i2)    => fun t:Trace => 
                                  (sem_de i1 t) \/ (sem_de i2 t)
|(interaction_par i1 i2)    => fun t:Trace => 
                                  exists (t1 t2:Trace), 
                                    (sem_de i1 t1) /\ (sem_de i2 t2) /\ (is_interleaving t1 t2 t)
|(interaction_strict i1 i2) => fun t:Trace => 
                                  exists (t1 t2:Trace), 
                                    (sem_de i1 t1) /\ (sem_de i2 t2) /\ (t = t1 ++ t2)
|(interaction_seq i1 i2)    => fun t:Trace => 
                                  exists (t1 t2:Trace), 
                                    (sem_de i1 t1) /\ (sem_de i2 t2) /\ (is_weak_seq t1 t2 t)
|(interaction_loop lk i1)   => fun t:Trace => 
                                  exists (subs:list Trace),
                                    (forall (t0:Trace), (In t0 subs) -> (sem_de i1 t0) )
                                    /\ (n_merge_schedule lk subs t)
end.

(**
*** Some properties of "sem_de" w.r.t. loops

Let us remark the following:
- if an interaction "i" of the form "i = (interaction_loop lstrict i1)" accepts a trace t, and, if "i1" accepts a non-empty trace t1, then "i" must accept t1++t
- if an interaction "i" of the form "i = (interaction_loop lseq i1)" accepts a trace t, and, if "i1" accepts a non-empty trace t1, then, given a trace t_merge such that (is_weak_seq t1 t t_merge), "i" must accept t_merge
- if an interaction "i" of the form "i = (interaction_loop lpar i1)" accepts a trace t, and, if "i1" accepts a non-empty trace t1, then, given a trace t_merge such that (is_interleaving t1 t t_merge), "i" must accept t_merge

Those three properties are stated and proven in the three Lemmas below:
- "sem_de_loop_strict_concat"
- "sem_de_loop_seq_weak_seq"
- and "sem_de_loop_par_interleaving"
**)

Lemma sem_de_loop_strict_concat (i1:Interaction) (t1 t:Trace) :
  (sem_de (interaction_loop lstrict i1) t)
  -> (sem_de i1 t1) -> (t1<>nil)
  -> (sem_de (interaction_loop lstrict i1) (t1 ++ t)).
Proof.
intros.
simpl in *.
destruct H as (subs,H).
destruct H.
exists (t1::subs).
split.
- intros.
  simpl in H3.
  destruct H3.
  + destruct H3. assumption.
  + apply H. assumption.
- apply merge_strict.
  + assumption.
  + assumption.
Qed.

Lemma sem_de_loop_seq_weak_seq (i1:Interaction) (t1 t t_merge:Trace) :
  (is_weak_seq t1 t t_merge)
  -> (sem_de (interaction_loop lseq i1) t)
  -> (sem_de i1 t1) -> (t1<>nil)
  -> (sem_de (interaction_loop lseq i1) t_merge).
Proof.
intros.
simpl in *.
destruct H0 as (subs,H0).
destruct H0.
exists (t1::subs).
split.
- intros.
  simpl in H4.
  destruct H4.
  + destruct H4. assumption.
  + apply H0. assumption.
- apply (merge_seq subs t1 t t_merge).
  + assumption.
  + assumption.
  + assumption.
Qed.

Lemma sem_de_loop_par_interleaving (i1:Interaction) (t1 t t_merge:Trace) :
  (is_interleaving t1 t t_merge)
  -> (sem_de (interaction_loop lpar i1) t)
  -> (sem_de i1 t1) -> (t1<>nil)
  -> (sem_de (interaction_loop lpar i1) t_merge).
Proof.
intros.
simpl in *.
destruct H0 as (subs,H0).
destruct H0.
exists (t1::subs).
split.
- intros.
  simpl in H4.
  destruct H4.
  + destruct H4. assumption.
  + apply H0. assumption.
- apply (merge_par subs t1 t t_merge).
  + assumption.
  + assumption.
  + assumption.
Qed.





(**
** Operational Semantics

By contrast we have not yet laid the groundworks for the definition of the operational-style semantics.

In the following, we will progressively introduce the intermediate functions required for this definition.
In the meanwhile we will state some Lemmas which describe how the denotational-style semantics "sem_de" relates to those intermediate functions.
Those Lemmas will incidentaly constitute the main elements for the proof of the inclusion of the operational-style semantics
into the denotational-style semantics.

*** Static analysis of interaction terms

In the following we will introduce two propositional functions "terminates" and "avoids" which state some facts
about a certain interaction that is provided as entry. Those facts are inferred inductively from a static
analysis of the term structure of the interaction.

**** The "terminates" function

The "terminates" function can statically determine whether or not a given interaction can accept/express the empty trace
i.e. if it can allow the empty execution (nothing visibly happens).
Concretely, for any interaction "i", (terminates i) is a predicate that states whether or not "i" terminates.
Here the use of the word "terminate" relates to the ability to immediately reach a succesfull termination state.

The determination of (terminates i) is done inductively as so:
- the empty interaction can always terminate
- an interaction that corresponds to a single atomic action cannot terminate (the action must occur)
- an interaction that corresponds to a non-deterministic alternative between two sub-interaction can terminate if either of the alternative can
- an interaction that corresponds to the scheduling (using any of the three scheduling operator) of two sub-interactions can terminate iff both can
- an interaction that corresponds to the repetition of behaviors of a given sub-interaction can always terminate given that we can choose to repeat zero times
**)

Fixpoint terminates (i : Interaction) : Prop :=
  match i with
    |  interaction_empty         => True
    | (interaction_act a)        => False
    | (interaction_alt i1 i2)    => (terminates i1) \/ (terminates i2)
    | (interaction_par i1 i2)    => (terminates i1) /\ (terminates i2)
    | (interaction_strict i1 i2) => (terminates i1) /\ (terminates i2)
    | (interaction_seq i1 i2)    => (terminates i1) /\ (terminates i2)
    | (interaction_loop lk i1)   => True
  end.

(**
Let us now see how the denotational semantics "sem_de" relates to the "terminates" function.

Intuitively, if an interaction terminates then it means that it can express the empty behavior (nothing visibly occurs).
Reciprocally, if an interaction can express the empty behavior, then it means that it must terminate.

Those two observations are stated and proved in the following Lemmas:
- "terminates_implies_de_accept_nil"
- and "de_accept_nil_implies_terminates"
**)

Lemma terminates_implies_de_accept_nil (i : Interaction) :
  (terminates i) -> (sem_de i nil).
Proof.
intros H.
induction i.
- simpl. reflexivity.
- simpl in H. contradiction.
- simpl. exists nil. exists nil.
  simpl in H. destruct H as (H1,H2).
  split.
  + apply IHi1. assumption.
  + split.
    * apply IHi2. assumption.
    * simpl. reflexivity.
- simpl. exists nil. exists nil.
  simpl in H. destruct H as (H1,H2).
  split.
  + apply IHi1. assumption.
  + split.
    * apply IHi2. assumption.
    * apply weak_seq_nil_left.
- simpl. exists nil. exists nil.
  simpl in H. destruct H as (H1,H2).
  split.
  + apply IHi1. assumption.
  + split.
    * apply IHi2. assumption.
    * apply interleaving_nil_left.
- simpl. inversion H.
  + left. apply IHi1. assumption.
  + right. apply IHi2. assumption.
- simpl. exists nil.
  split.
  + simpl. intros t0 H0. contradiction.
  + apply merge_zero.
Qed.

Lemma de_accept_nil_implies_terminates (i : Interaction) :
  (sem_de i nil) -> (terminates i).
Proof.
intros H.
induction i.
- simpl. reflexivity.
- simpl in H. inversion H.
- simpl. simpl in H.
  destruct H as (t1,H).
  destruct H as (t2,H).
  destruct H. destruct H0.
  symmetry in H1.
  apply app_eq_nil in H1.
  destruct H1.
  symmetry in H1. destruct H1.
  symmetry in H2. destruct H2.
  split.
  + apply IHi1. assumption.
  + apply IHi2. assumption.
- simpl. simpl in H.
  destruct H as (t1,H).
  destruct H as (t2,H).
  destruct H. destruct H0.
  apply is_weak_seq_nil_prop1 in H1.
  destruct H1.
  symmetry in H1. destruct H1.
  symmetry in H2. destruct H2.
  split.
  + apply IHi1. assumption.
  + apply IHi2. assumption.
- simpl. simpl in H.
  destruct H as (t1,H).
  destruct H as (t2,H).
  destruct H. destruct H0.
  apply is_interleaving_nil_prop1 in H1.
  destruct H1.
  symmetry in H1. destruct H1.
  symmetry in H2. destruct H2.
  split.
  + apply IHi1. assumption.
  + apply IHi2. assumption.
- simpl. simpl in H.
  destruct H.
  + left. apply IHi1. assumption.
  + right. apply IHi2. assumption.
- simpl. trivial.
Qed.

(**
**** The "avoids" function

In a similar fashion as "terminates", the "avoids" function
can statically determine whether or not a given interaction accepts executions / traces that do not involve any action of a given lifeline
(i.e. it "avoids" the lifeline).

Concretely, for any interaction "i" and any lifeline "l", (avoids i l) is a predicate that states whether or not "i" avoids "l".

The determination of (avoids i l) is done inductively as so:
- the empty interaction can always avoid any lifeline
- an interaction that corresponds to a single atomic action can avoid a lifeline iff this action do not occur on the lifeline (this echoes back to the notion of having no conflict)
- an interaction that corresponds to a non-deterministic alternative between two sub-interaction can avoid a lifeline if either of the alternative can
- an interaction that corresponds to the scheduling (using any of the three scheduling operator) of two sub-interactions can avoid a lifeline iff both can
- an interaction that corresponds to the repetition of behaviors of a given sub-interaction can always avoid a lifeline given that we can choose to repeat zero times
**)

Fixpoint avoids
        (i : Interaction) 
        (l : L) 
        : Prop :=
  match i with
    |  interaction_empty         => True
    | (interaction_act a)        => not ((lifeline a) = l)
    | (interaction_alt i1 i2)    => (avoids i1 l) \/ (avoids i2 l)
    | (interaction_par i1 i2)    => (avoids i1 l) /\ (avoids i2 l)
    | (interaction_strict i1 i2) => (avoids i1 l) /\ (avoids i2 l)
    | (interaction_seq i1 i2)    => (avoids i1 l) /\ (avoids i2 l)
    | (interaction_loop lk i1)   => True
  end.

(**
Let us now state and prove some properties on "avoids":
- "avoids_decidability" states that the predicate (avoids i l) is, for any interaction "i" and lifeline "l", decidable. Indeed, the logic that is used in Coq is intuitionistic logic, which does not include the "Law of excluded middle". As a result, we must prove the decidability of propositions if we need to use it. Given that (avoids i l) is constructed inductively, one can decide whether or not it is held true, and, it cannot both be True or False at the same time.
- "terminates_implies_avoids" states that if an interaction terminates, then it can avoid any lifeline
**)


Lemma avoids_decidability (i : Interaction) (l : L) :
  (avoids i l) \/ (not (avoids i l)).
Proof.
dependent induction i ; simpl.
- left. trivial.
- apply not_eq_or_not_not_eq.
- specialize IHi1 with (l:=l).
  specialize IHi2 with (l:=l).
  destruct IHi1 ; destruct IHi2.
  + left. split ; assumption.
  + right. intro. destruct H1.
    contradiction.
  + right. intro. destruct H1.
    contradiction. 
  + right. intro. destruct H1.
    contradiction. 
- specialize IHi1 with (l:=l).
  specialize IHi2 with (l:=l).
  destruct IHi1 ; destruct IHi2.
  + left. split ; assumption.
  + right. intro. destruct H1.
    contradiction.
  + right. intro. destruct H1.
    contradiction. 
  + right. intro. destruct H1.
    contradiction. 
- specialize IHi1 with (l:=l).
  specialize IHi2 with (l:=l).
  destruct IHi1 ; destruct IHi2.
  + left. split ; assumption.
  + right. intro. destruct H1.
    contradiction.
  + right. intro. destruct H1.
    contradiction. 
  + right. intro. destruct H1.
    contradiction. 
- specialize IHi1 with (l:=l).
  specialize IHi2 with (l:=l).
  destruct IHi1 ; destruct IHi2.
  + left. left. assumption.
  + left. left. assumption.
  + left. right. assumption.
  + right. intro. 
    destruct H1 ; contradiction.
- left. trivial.
Qed.

Lemma terminates_implies_avoids (i : Interaction) (l : L) :
  (terminates i) -> (avoids i l).
Proof.
intros H.
dependent induction i ; simpl in *.
- trivial.
- contradiction.
- destruct H.
  split.
  + apply IHi1. assumption.
  + apply IHi2. assumption.
- destruct H.
  split.
  + apply IHi1. assumption.
  + apply IHi2. assumption.
- destruct H.
  split.
  + apply IHi1. assumption.
  + apply IHi2. assumption.
- destruct H.
  + left. apply IHi1. assumption.
  + right. apply IHi2. assumption.
- trivial.
Qed.

(**
With regards to the denotational semantics, I make the following remarks:
- if an interaction can express the empty trace, then it can avoid any lifeline. This is formalized in the "de_accept_nil_implies_avoids" Lemma which proof can be directly inferred from the previously proven "terminates_implies_avoids" and "de_accept_nil_implies_terminates" Lemmas.
- if an interaction accepts a trace, and that trace has no conflict w.r.t. a certain lifeline, then it must mean that the interaction can avoid that lifeline. This is formalized in the "de_accept_t_and_no_conflict_implies_avoids" Lemma.
**)

Lemma de_accept_nil_implies_avoids (i : Interaction) (l : L) :
  (sem_de i nil) -> (avoids i l).
Proof.
intros H.
apply terminates_implies_avoids.
apply de_accept_nil_implies_terminates.
assumption.
Qed.

Lemma de_accept_t_and_no_conflict_implies_avoids
  (i: Interaction) (a:Action) (t:Trace) :
    (sem_de i t)
    -> (no_conflict t a)
    -> (avoids i (lifeline a)).
Proof.
intros H H0.
dependent induction i.
- simpl in *. trivial.
- simpl in *. 
  symmetry in H. destruct H.
  inversion H0.
  destruct H3.
  apply not_eq_sym.
  assumption.
- simpl in *.
  destruct H as (t1,H).
  destruct H as (t2,H).
  destruct H as (H1,H).
  destruct H as (H2,H).
  symmetry in H. destruct H.
  apply no_conflict_concat in H0.
  destruct H0 as (Hn1,Hn2).
  split.
  + apply (IHi1 a t1) ; assumption.
  + apply (IHi2 a t2) ; assumption.
- simpl in *.
  destruct H as (t1,H).
  destruct H as (t2,H).
  destruct H as (H1,H).
  destruct H as (H2,H).
  pose proof (no_conflict_weak_seq t1 t2 t a) as Hn.
  apply Hn in H.
  apply H in H0.
  destruct H0 as (Hn1,Hn2).
  split.
  + apply (IHi1 a t1) ; assumption.
  + apply (IHi2 a t2) ; assumption.
- simpl in *.
  destruct H as (t1,H).
  destruct H as (t2,H).
  destruct H as (H1,H).
  destruct H as (H2,H).
  pose proof (no_conflict_interleaving t1 t2 t a) as Hn.
  apply Hn in H.
  apply H in H0.
  destruct H0 as (Hn1,Hn2).
  split.
  + apply (IHi1 a t1) ; assumption.
  + apply (IHi2 a t2) ; assumption.
- simpl in *.
  destruct H.
  + left. apply (IHi1 a t) ; assumption.
  + right. apply (IHi2 a t) ; assumption.
- simpl. trivial.
Qed.


(**
*** The pruning of interactions

In the following we are interested in the question of how to rewrite interaction terms (using some form of term rewriting)
that can avoid a certain lifeline so that all the trace that are expressed by the rewritten interaction have no conflicts w.r.t. the lifeline.

Indeed, if we suppose that a certain interaction avoids a lifeline, it only means it can express traces that do not involve the lifeline,
and it does not mean that all the traces it can express have no conflicts w.r.t. the lifeline.

However we can infer a rewritten version of this interaction which expresses exactly all the traces of the original interaction
that have no conflict w.r.t. the lifeline.

I call the inference of this rewritten interaction "pruning", and the rewritten interaction is the "pruned" interaction.

Concretely, for a given interaction "i" and for a given lifeline "l" such that the predicate "(avoids i l)" is held True,
the predicate "(is_prune_of i l i')" states whether or not an interaction "i'" is the pruned version of "i" w.r.t. "l".

This formulation as a predicate in fact corresponds to a certain "prune" function (not defined here)
which can statically compute a uniquely defined "pruned" interaction.
The existence of this "prune" function is congruent to having the "is_prune_of" predicate satisfying properties of existence and unicity.
**)

Inductive is_prune_of : Interaction -> L -> Interaction -> Prop :=
| prune_empty  : forall (l:L), 
                   (is_prune_of interaction_empty l interaction_empty)
| prune_act    : forall (a:Action) (l:L), 
                   (not (l = (lifeline a))) 
                     -> (is_prune_of (interaction_act a) l (interaction_act a))
| prune_alt_both : forall (i1 i2 i1' i2':Interaction) (l:L),
                     (avoids i1 l)
                     ->(avoids i2 l)
                     ->(is_prune_of i1 l i1')
                     ->(is_prune_of i2 l i2')
                     -> (is_prune_of (interaction_alt i1 i2) l (interaction_alt i1' i2'))
| prune_alt_left : forall (i1 i2 i1':Interaction) (l:L),
                     (not (avoids i2 l))
                     ->(avoids i1 l)
                     ->(is_prune_of i1 l i1')
                     ->(is_prune_of (interaction_alt i1 i2) l i1')
| prune_alt_right : forall (i1 i2 i2':Interaction) (l:L),
                     (not (avoids i1 l)) 
                     ->(avoids i2 l)
                     ->(is_prune_of i2 l i2')
                     ->(is_prune_of (interaction_alt i1 i2) l i2')
| prune_par  : forall (i1 i2 i1' i2':Interaction) (l:L),
                (is_prune_of i1 l i1')
                ->(is_prune_of i2 l i2')
                ->(is_prune_of (interaction_par i1 i2) l (interaction_par i1' i2'))
| prune_strict  : forall (i1 i2 i1' i2':Interaction) (l:L),
                (is_prune_of i1 l i1')
                ->(is_prune_of i2 l i2')
                  -> (is_prune_of (interaction_strict i1 i2) l (interaction_strict i1' i2'))
| prune_seq  : forall (i1 i2 i1' i2':Interaction) (l:L),
                (is_prune_of i1 l i1')
                ->(is_prune_of i2 l i2')
                  -> (is_prune_of (interaction_seq i1 i2) l (interaction_seq i1' i2'))
| prune_loop_select : forall (i1 i1':Interaction) (lk:ScheduleKind) (l:L),
                     (avoids i1 l)
                     -> (is_prune_of i1 l i1')
                     -> (is_prune_of (interaction_loop lk i1) l (interaction_loop lk i1'))
| prune_loop_elim : forall (i1:Interaction) (lk:ScheduleKind) (l:L),
                     (not (avoids i1 l))
                     -> (is_prune_of (interaction_loop lk i1) l interaction_empty)
.

(**
**** Inherent properties of the pruning 

As explained earlier, we will need the unicity property for the "is_prune_of" predicate.
This property is stated and proved in the "prune_unicity" Lemma below.

If, for any given interactions "i", "i1" and "i2" we have both (is_prune_of i l i1') and (is_prune_of i l i2'), then "i1" and "i2" are in fact the same interaction term.
**)

Lemma prune_unicity (i i1' i2':Interaction) (l:L):
  ( (is_prune_of i l i1') /\ (is_prune_of i l i2') )
  -> (i1'=i2').
Proof.
intros H. destruct H as (H1,H2).
dependent induction i.
- inversion H1. inversion H2. reflexivity.
- inversion H1. inversion H2. reflexivity.
- inversion H1. inversion H2.
  assert (i1'0 = i1'1).
  { apply (IHi1 i1'0 i1'1 l) ; assumption. }
  destruct H13.
  assert (i2'0 = i2'1).
  { apply (IHi2 i2'0 i2'1 l) ; assumption. }
  destruct H13.
  reflexivity.
- inversion H1. inversion H2.
  assert (i1'0 = i1'1).
  { apply (IHi1 i1'0 i1'1 l) ; assumption. }
  destruct H13.
  assert (i2'0 = i2'1).
  { apply (IHi2 i2'0 i2'1 l) ; assumption. }
  destruct H13.
  reflexivity.
- inversion H1. inversion H2.
  assert (i1'0 = i1'1).
  { apply (IHi1 i1'0 i1'1 l) ; assumption. }
  destruct H13.
  assert (i2'0 = i2'1).
  { apply (IHi2 i2'0 i2'1 l) ; assumption. }
  destruct H13.
  reflexivity.
- inversion H1 ; inversion H2.
  + assert (i1'0 = i1'1).
    { apply (IHi1 i1'0 i1'1 l) ; assumption. }
    destruct H17.
    assert (i2'0 = i2'1).
    { apply (IHi2 i2'0 i2'1 l) ; assumption. }
    destruct H17.
    reflexivity.
  + contradiction.
  + contradiction.
  + contradiction.
  + assert (i1' = i2').
    { apply (IHi1 i1' i2' l) ; assumption. }
    destruct H15.
    reflexivity.
  + contradiction.
  + contradiction.
  + contradiction.
  + assert (i1' = i2').
    { apply (IHi2 i1' i2' l) ; assumption. }
    destruct H15.
    reflexivity.
- inversion H1 ; inversion H2.
  + assert (i1'0 = i1'1).
    { apply (IHi i1'0 i1'1 l) ; assumption. }
    destruct H13.
    reflexivity.
  + contradiction.
  + contradiction.
  + reflexivity.
Qed.

(**
I also state and prove some properties linked to the relationship between pruning and avoiding:
- "prunable_implies_avoids" states that if an interaction can be rewritten (pruned) into a pruned version w.r.t. a lifeline "l", then it means it could avoid "l"
- "avoids_implies_prunable" states that if an interaction can avoid a certain lifeline "l", then it means it can be pruned w.r.t. "l" (this is the existence property of the predicate)
**)

Lemma prunable_implies_avoids (i:Interaction) (l:L):
 ( exists (i':Interaction), (is_prune_of i l i') )
 -> (avoids i l).
Proof.
intros H. destruct H as (i',H).
dependent induction H ; simpl in *.
- trivial.
- apply not_eq_sym. assumption.
- left. assumption.
- left. assumption.
- right. assumption.
- split ; assumption.
- split ; assumption.
- split ; assumption.
- trivial.
- trivial.
Qed.

Lemma avoids_implies_prunable (i:Interaction) (l:L):
 (avoids i l)
 ->( exists (i':Interaction), (is_prune_of i l i') ).
Proof.
dependent induction i.
- exists interaction_empty.
  apply prune_empty.
- exists (interaction_act a).
  apply prune_act.
  simpl in H.
  apply not_eq_sym. assumption.
- intro H.
  inversion H.
  apply IHi1 in H0.
  apply IHi2 in H1.
  destruct H1 as (i2',H2).
  destruct H0 as (i1',H1).
  exists (interaction_strict i1' i2').
  apply prune_strict ; assumption.
- intros H. inversion H.
  apply IHi1 in H0.
  apply IHi2 in H1.
  destruct H1 as (i2',H2).
  destruct H0 as (i1',H1).
  exists (interaction_seq i1' i2').
  apply prune_seq ; assumption.
- intros H. inversion H.
  apply IHi1 in H0.
  apply IHi2 in H1.
  destruct H1 as (i2',H2).
  destruct H0 as (i1',H1).
  exists (interaction_par i1' i2').
  apply prune_par ; assumption.
- intros H.
  pose proof (avoids_decidability i1 l) as H1.
  pose proof (avoids_decidability i2 l) as H2.
  destruct H1 ; destruct H2.
  + assert (Ha1:=H0).
    assert (Ha2:=H1).
    apply IHi1 in H0.
    destruct H0 as (i1',Hi1).
    apply IHi2 in H1.
    destruct H1 as (i2',Hi2).
    exists (interaction_alt i1' i2').
    apply prune_alt_both ; assumption.
  + assert (Ha1:=H0).  
    apply IHi1 in H0.
    destruct H0 as (i1',Hi1).
    exists i1'.
    apply prune_alt_left ; assumption.
  + assert (Ha2:=H1).  
    apply IHi2 in H1.
    destruct H1 as (i2',Hi2).
    exists i2'.
    apply prune_alt_right ; assumption.
  + inversion H ; contradiction.
- intros H.
  pose proof (avoids_decidability i l) as H1.
  destruct H1.
  + assert (Ha1:=H0).
    apply IHi in H0.
    destruct H0 as (i',Hi).
    exists (interaction_loop s i').
    apply prune_loop_select ; assumption.
  + exists interaction_empty.
    apply prune_loop_elim.
    assumption.
Qed.

(**
**** Properties of pruning w.r.t. the denotational semantics

In the following, I will state some properties of pruning w.r.t. the denotational semantics "sem_de".

Let us remark that if an interaction can express the empty trace, then it means it can be pruned w.r.t. any lifeline. 
This is formalized as the "de_accept_nil_implies_prunable" Lemma which proof is immediately inferred from previous Lemmas
"de_accept_nil_implies_prunable" and "avoids_implies_prunable".
**)

Lemma de_accept_nil_implies_prunable (i:Interaction) (l:L) :
  (sem_de i nil)
  -> exists (i':Interaction), (is_prune_of i l i').
Proof.
intros H.
apply (de_accept_nil_implies_avoids i l) in H.
apply avoids_implies_prunable.
assumption.
Qed.

(** 
Let us also remark that this can be generalized for the acceptation of any trace that has no conflict with the lifeline.
This is formalized as the "de_accept_t_and_no_conflict_implies_prunable" Lemma which proof is immediately inferred from previous Lemmas
"de_accept_t_and_no_conflict_implies_avoids" and "avoids_implies_prunable".
**)

Lemma de_accept_t_and_no_conflict_implies_prunable
  (i: Interaction) (a:Action) (t:Trace) :
    (sem_de i t)
    -> (no_conflict t a)
    -> exists (i':Interaction), (is_prune_of i (lifeline a) i').
Proof.
intros.
apply avoids_implies_prunable.
apply (de_accept_t_and_no_conflict_implies_avoids i a t) ; assumption.
Qed.

(**
Let us remark that
if an interaction "i" can be pruned into "i'" and if that "i'" accepts a trace "t",
then the original "i" must also accept "t". 
This property is crucial given that it means that the pruning transformation preserves the semantics. 
The semantics of the pruned version is included into that of the original interaction. 
In other words, the pruning selects a subset of the semantics and discards (prunes) the rest. 
No additional unwelcomed traces are introduced in the semantics of the pruned interaction.

This property is formalized in the "prune_kept_de" Lemma below.
**)

Lemma prune_kept_de (i i': Interaction) (l:L) (t:Trace) :
  (is_prune_of i l i') /\ (sem_de i' t)
    -> (sem_de i t).
Proof.
intros H.
destruct H.
dependent induction i.
- inversion H. destruct H3.
  inversion H0. simpl. reflexivity.
- inversion H. destruct H4.
  inversion H0. simpl. reflexivity.
- inversion H.
  symmetry in H1. destruct H1.
  symmetry in H4. destruct H4.
  symmetry in H2. destruct H2.
  destruct H5.
  simpl.
  inversion H0 as (t1,Hd).
  destruct Hd as (t2,Hd).
  destruct Hd as (Hi1,Hd).
  destruct Hd as (Hi2,Hconc).
  exists t1. exists t2.
  split.
  { apply (IHi1 i1' l) ; assumption. }
  { split.
    { apply (IHi2 i2' l) ; assumption. }
    { assumption. }
  }
- inversion H.
  symmetry in H1. destruct H1.
  symmetry in H4. destruct H4.
  symmetry in H2. destruct H2.
  simpl. destruct H5.
  inversion H0 as (t1,Hd).
  destruct Hd as (t2,Hd).
  destruct Hd as (Hi1,Hd).
  destruct Hd as (Hi2,Hconc).
  exists t1. exists t2.
  split.
  { apply (IHi1 i1' l) ; assumption. }
  { split.
    { apply (IHi2 i2' l) ; assumption. }
    { assumption. }
  }
- inversion H.
  symmetry in H1. destruct H1.
  symmetry in H4. destruct H4.
  symmetry in H2. destruct H2.
  simpl. destruct H5.
  inversion H0 as (t1,Hd).
  destruct Hd as (t2,Hd).
  destruct Hd as (Hi1,Hd).
  destruct Hd as (Hi2,Hconc).
  exists t1. exists t2.
  split.
  { apply (IHi1 i1' l) ; assumption. }
  { split.
    { apply (IHi2 i2' l) ; assumption. }
    { assumption. }
  }
- inversion H ;
  symmetry in H1 ; destruct H1 ;
  symmetry in H2 ; destruct H2 ;
  symmetry in H6 ; destruct H6.
  + destruct H7.
    simpl. simpl in H0.
    destruct H0.
    * left. apply (IHi1 i1' l) ; assumption.
    * right. apply (IHi2 i2' l) ; assumption.
  + simpl. destruct H5. 
    left. apply (IHi1 i' l0) ; assumption.
  + simpl. destruct H5.
    right. apply (IHi2 i' l0) ; assumption.
- inversion H.
  + destruct H1. destruct H2.
    destruct H4. destruct H5.
    simpl in H0.
    destruct H0 as (subs,H0).
    destruct H0.
    simpl. exists subs.
    split.
    { intros t0 Ht0.
      apply (IHi i1' l0).
      - assumption.
      - apply H0. assumption.
    }
    { assumption. }
  + destruct H4. inversion H0. 
    simpl. exists nil. split.
    * intros t0 Ht0. contradiction.
    * apply merge_zero.
Qed.

(**
With "prune_kept_de", we have proven that the semantics of the pruned version is included in that of the original.

We will now prove, in two steps, that the semantics of the pruned version is a minimal cut of that of the original.
What we mean to say is that the selection of the subset of the semantics that is operated by prune is minimal in so far
as we only eliminate traces that we need to eliminate so as to satisfy that the pruned version avoids a certain lifeline.
Traces that do not involve the lifeline w.r.t. which the pruning is done must be kept in the semantics.

This two-steps proof is done with Lemmas:
- "de_accept_nil_implies_pruned_de_accept_nil ", which states that if the original interaction accepts the empty trace, then the pruned version must also accept the empty trace
- "de_accept_cons_and_no_conflict_implies_prunable_and_keep_de", which states that if the original interaction accepts a non-empty trace that has no conflict with the lifeline against which we prune, then this trace must be found in the semantics of the pruned version.

Those two lemmas taken together in addition to the "prune_kept_de" Lemma state that
the semantics of the pruned version is exactly the subset of the semantics
of the original in which all traces have no conflict with the lifeline against which the pruning is done.
**)


(**
Let us make some additional remarks on the "de_accept_cons_and_no_conflict_implies_prunable_and_keep_de" Lemma.
This Lemma is formulated with an existential quantifier stating that: there exists a certain pruned version of the
original that accepts the trace t.
However we have previously seen that the property of unicity is proven for the "is_prune_of" predicate.
As a result, it is not "a pruned version" but "the pruned version".
**)

Lemma de_loop_accept_t_and_no_conflict_implies_nil_or_avoids 
  (i1:Interaction) (lk:ScheduleKind) (t:Trace) (a:Action) :
    (no_conflict t a)
    -> (sem_de (interaction_loop lk i1) t)
    -> ((t = nil) \/ (avoids i1 (lifeline a))).
Proof.
intros Hnoco Hsem.
simpl in Hsem.
destruct Hsem as (subs,H).
destruct H as (Hin,Hrep).
pose proof (eq_or_not_eq_trace t nil).
destruct H.
- left. assumption.
- right. 
 apply (n_merge_schedule_nil_prop0 lk subs t) in H.
  + destruct H as (t0,Ht0).
    destruct Ht0. assert (Hint0:=H).
    apply Hin in H.
    assert (Hr:=Hrep).
    apply (no_conflict_n_merge lk subs t a) in Hrep.
    destruct Hrep as (Hr1,Hr2).    
    apply (de_accept_t_and_no_conflict_implies_avoids i1 a t0).
    * assumption.
    * apply Hr1 ; assumption.
  + assumption.
Qed.


Lemma de_accept_t_and_no_conflict_implies_pruned_de_accept_t
  (i i': Interaction) (a:Action) (t:Trace) :
  (no_conflict t a)
  -> (sem_de i t)
  -> (is_prune_of i (lifeline a) i')
  -> (sem_de i' t).
Proof.
intros Hnoco H1 H2.
dependent induction i. 
- inversion H2.
  simpl.
  inversion H1.
  reflexivity.
- inversion H1.
  symmetry in H. destruct H.
  simpl in *.
  inversion H2.
  symmetry in H. destruct H.
  simpl.
  reflexivity.
- simpl in H1. 
  destruct H1 as (t1,H1).
  destruct H1 as (t2,H1).
  destruct H1.
  destruct H0.
  symmetry in H1. destruct H1.
  apply no_conflict_concat in Hnoco.
  destruct Hnoco.
  inversion H2.
  symmetry in H4. destruct H4.
  symmetry in H7. destruct H7.
  symmetry in H5. destruct H5.
  destruct H8.
  simpl.
  exists t1. exists t2.
  split ; try split.
  + apply (IHi1 i1' a t1) ; assumption.
  + apply (IHi2 i2' a t2) ; assumption.
  + reflexivity.
- simpl in H1. 
  destruct H1 as (t1,H1).
  destruct H1 as (t2,H1).
  destruct H1.
  destruct H0.
  inversion H2. 
  symmetry in H3. destruct H3.
  symmetry in H4. destruct H4.
  symmetry in H6. destruct H6.
  destruct H7.
  simpl.
  exists t1. exists t2.
  apply (no_conflict_weak_seq t1 t2) in Hnoco.
  { destruct Hnoco.
    split ; try split.
    - apply (IHi1 i1' a t1) ; assumption.
    - apply (IHi2 i2' a t2) ; assumption.
    - assumption. 
  }
  { assumption. }
- simpl in H1. 
  destruct H1 as (t1,H1).
  destruct H1 as (t2,H1).
  destruct H1.
  destruct H0.
  inversion H2. 
  symmetry in H3. destruct H3.
  symmetry in H4. destruct H4.
  symmetry in H6. destruct H6.
  destruct H7.
  simpl.
  exists t1. exists t2.
  apply (no_conflict_interleaving t1 t2) in Hnoco.
  { destruct Hnoco.
    split ; try split.
    - apply (IHi1 i1' a t1) ; assumption.
    - apply (IHi2 i2' a t2) ; assumption.
    - assumption. 
  }
  { assumption. }
- simpl in H1.  
  destruct H1 ; inversion H2 ;
  symmetry in H0 ; destruct H0 ;
  symmetry in H1 ; destruct H1.
  + destruct H7.
    simpl.
    apply (IHi1 i1' a t) in H.
    * left. assumption.
    * assumption.
    * assumption.
  + destruct H6.
    apply (IHi1 i1' a t) in H ; assumption.
  + destruct H6.
    assert (avoids i1 (lifeline a)).
    { apply (de_accept_t_and_no_conflict_implies_avoids i1 a t) ; assumption. }
    contradiction.
  + destruct H7.
    simpl.
    right.
    apply (IHi2 i2' a t) ; assumption.
  + destruct H6.
    assert (avoids i2 (lifeline a)).
    { apply (de_accept_t_and_no_conflict_implies_avoids i2 a t) ; assumption. }
    contradiction.
  + destruct H6.
    apply (IHi2 i2' a t) ; assumption.
- assert (Hsem:=H1). simpl in H1. 
  destruct H1 as (subs,H1).
  destruct H1 as (Hin,Hrep).
  inversion H2.
  + destruct H. destruct H0.
    symmetry in H3. destruct H3.
    destruct H4.
    simpl.
    exists subs. split.
    * intros t0 Ht0.
      { apply (IHi i1' a t0).
        - apply (no_conflict_n_merge lk subs t) ; assumption. 
        - apply Hin. assumption.
        - assumption.
      }
    * assumption.
  + destruct H. destruct H1.
    symmetry in H0. destruct H0.
    destruct H3.
    simpl.
    assert (t = nil \/ avoids i1 (lifeline a)).
    { apply (de_loop_accept_t_and_no_conflict_implies_nil_or_avoids i1 lk t a) ; assumption. }
    destruct H.
    * assumption.
    * contradiction.
Qed.

Lemma de_accept_nil_implies_pruned_de_accept_nil
  (i i': Interaction) (l:L) :
    (sem_de i nil)
    -> (is_prune_of i l i')
    -> (sem_de i' nil).
Proof.
intros H1 H2.
pose proof (exists_action_on_lifeline l).
destruct H as (a,H).
apply (de_accept_t_and_no_conflict_implies_pruned_de_accept_t i i' a nil).
- apply no_conflict_nil.
- assumption.
- destruct H. assumption.
Qed.

(**
A final Lemma on the relationship between pruning and the denotational semantics
relates to a previous remark. 
I have said that the semantics of the pruned version is the set of traces accepted by the original
that have no conflict with the lifeline against which the pruning is done.

Reciprocally, this means that the semantics of the pruned version only contain traces which have no conflict w.r.t.
said lifeline. This is formalized and proven in the "prune_removes_conflicts" Lemma.
**)

Lemma prune_removes_conflicts (i i':Interaction) (a:Action) (t:Trace):
  (is_prune_of i (lifeline a) i')
  -> (sem_de i' t)
  -> (no_conflict t a).
Proof.
intros H1 H2.
dependent induction H1 generalizing t.
- inversion H2.
  apply no_conflict_nil.
- inversion H2.
  apply no_conflict_cons.
  split.
  + assumption.
  + apply no_conflict_nil.
- simpl in H2.
  destruct H2.
  + apply IHis_prune_of1.
    * reflexivity.
    * assumption.
  + apply IHis_prune_of2.
    * reflexivity.
    * assumption.
- apply IHis_prune_of.
  + reflexivity.
  + assumption.
- apply IHis_prune_of.
  + reflexivity.
  + assumption.
- simpl in H2.
  destruct H2 as (t1,H).
  destruct H as (t2,H).
  destruct H as (Hi1,H).
  destruct H as (Hi2,H).
  apply (no_conflict_interleaving t1 t2 t).
  + assumption.
  + split.
    * apply IHis_prune_of1.
      { reflexivity. }
      { assumption. }
    * apply IHis_prune_of2.
      { reflexivity. }
      { assumption. }
- simpl in H2.
  destruct H2 as (t1,H).
  destruct H as (t2,H).
  destruct H as (Hi1,H).
  destruct H as (Hi2,H).
  symmetry in H. destruct H.
  apply no_conflict_concat.
  split.
  + apply IHis_prune_of1.
    { reflexivity. }
    { assumption. }
  + apply IHis_prune_of2.
    { reflexivity. }
    { assumption. }
- simpl in H2.
  destruct H2 as (t1,H).
  destruct H as (t2,H).
  destruct H as (Hi1,H).
  destruct H as (Hi2,H).
  apply (no_conflict_weak_seq t1 t2 t).
  + assumption.
  + split.
    * apply IHis_prune_of1.
      { reflexivity. }
      { assumption. }
    * apply IHis_prune_of2.
      { reflexivity. }
      { assumption. }
- simpl in H2.
  destruct H2 as (subs,H2).
  destruct H2. 
  apply (no_conflict_n_merge lk subs t a).
  + assumption.
  + intros t0 Ht0.
    apply IHis_prune_of.
    * reflexivity.
    * apply H0. assumption.
- inversion H2.
  apply no_conflict_nil.
Qed.

(**
*** The execution relation

The operational-style semantics relies on the definition of a "small-step" that corresponds
to the execution of an atomic action within an interaction and which result in a "remaining" or "follow-up" interaction
which exactly accepts all the suffixes (tails) of traces of the original that start with the given action
(uniquely determined by its position in the interaction term, even though there may be several occurences of the
same action in the interaction).

In Coq, I formalize this "small-step" or "execution relation" as an inductive predicate "is_next_of" such that,
for any interactions "i" and "i'" and any action "a", the predicate "(is_next_of i a i')" signifies that
action "a" can be immediately executed in "i" and this results in "i" being rewritten into interaction "i'"
that accepts all continuations of the executions of "i" that start with the execution of action "a"
(at a precise position in the term structure of "i").

Given that, in this Coq proof, I do not formalize the notion of uniquely identifying actions via their positions,
I do not have the unicity of "is_next_of". But it is not required in this Coq proof anyways.
Let us remark however that I have formalized this in another Coq proof
(for the correctness of a multi-trace analysis algorithm) available here:
#<a href="https://github.com/erwanM974/coq_hibou_label_multi_trace_analysis">https://github.com/erwanM974/coq_hibou_label_multi_trace_analysis</a># 

The "is_next_of" predicate can be inferred inductively via twelve construction rules:
- (1) "execute_at_leaf" states that an interaction that consists of a single action can immediately execute this action, and that the empty interaction remains to be executed
- (2) "execute_left_alt" states that if the left sub-interaction of an interaction "i" of the form (interaction_alt i1 i2) can execute an action a, then "i" can too and the remaining interaction can be inferred 
- (3) "execute_right_alt" states that if the right sub-interaction of an interaction "i" of the form (interaction_alt i1 i2) can execute an action a, then "i" can too and the remaining interaction can be inferred
- (4) "execute_left_par" states that if the left sub-interaction of an interaction "i" of the form (interaction_par i1 i2) can execute an action a, then "i" can too and the remaining interaction can be inferred
- (5) "execute_right_par" states that if the right sub-interaction of an interaction "i" of the form (interaction_par i1 i2) can execute an action a, then "i" can too and the remaining interaction can be inferred
- (6) "execute_left_strict" states that if the left sub-interaction of an interaction "i" of the form (interaction_strict i1 i2) can execute an action a, then "i" can too and the remaining interaction can be inferred
- (7) "execute_right_strict" states that if the right sub-interaction of an interaction "i" of the form (interaction_strict i1 i2) can execute an action a, then "i" can too and the remaining interaction can be inferred
- (8) "execute_left_seq" states that if the left sub-interaction of an interaction "i" of the form (interaction_seq i1 i2) can execute an action a, then "i" can too and the remaining interaction can be inferred
- (9) "execute_right_seq" states that if the right sub-interaction of an interaction "i" of the form (interaction_seq i1 i2) can execute an action a, then "i" can too and the remaining interaction can be inferred
- (10) "execute_loop_strict" states that if the sub-interaction of an interaction "i" of the form (interaction_loop lstrict i1) can execute an action a, then "i" can too and the remaining interaction can be inferred
- (11) "execute_loop_seq" states that if the sub-interaction of an interaction "i" of the form (interaction_loop lseq i1) can execute an action a, then "i" can too and the remaining interaction can be inferred
- (12) "execute_loop_par" states that if the sub-interaction of an interaction "i" of the form (interaction_loop lpar i1) can execute an action a, then "i" can too and the remaining interaction can be inferred
**)

Inductive is_next_of : Interaction -> Action -> Interaction -> Prop :=
|execute_at_leaf : forall (a:Action), 
                 (is_next_of (interaction_act a) a interaction_empty)
|execute_left_alt     : forall (a:Action) (i1 i2 i1' : Interaction),
                           (is_next_of i1 a i1') 
                              -> (is_next_of (interaction_alt i1 i2) a i1')
|execute_right_alt    : forall (a:Action) (i1 i2 i2' : Interaction),
                           (is_next_of i2 a i2') 
                              -> (is_next_of (interaction_alt i1 i2) a i2')
|execute_left_par     : forall (a:Action) (i1 i2 i1' : Interaction),
                           (is_next_of i1 a i1') 
                              -> (is_next_of 
                                        (interaction_par i1 i2)
                                        a 
                                        (interaction_par i1' i2)
                                 )
|execute_right_par    : forall (a:Action) (i1 i2 i2' : Interaction),
                           (is_next_of i2 a i2') 
                              -> (is_next_of 
                                        (interaction_par i1 i2)
                                        a 
                                        (interaction_par i1 i2')
                                 )
|execute_left_strict  : forall (a:Action) (i1 i2 i1' : Interaction),
                          (is_next_of i1 a i1') 
                             -> (is_next_of 
                                       (interaction_strict i1 i2)
                                       a
                                       (interaction_strict i1' i2)
                                )
|execute_right_strict : forall (a:Action) (i1 i2 i2' : Interaction),
                          (is_next_of i2 a i2')
                          -> (terminates i1)
                          -> (is_next_of (interaction_strict i1 i2) a i2')
|execute_left_seq     : forall (a:Action) (i1 i2 i1' : Interaction),
                          (is_next_of i1 a i1') 
                             -> (is_next_of 
                                       (interaction_seq i1 i2)
                                       a
                                       (interaction_seq i1' i2)
                                )
|execute_right_seq    : forall (a:Action) (i1 i2 i1' i2' : Interaction),
                          (is_next_of i2 a i2')
                          -> (is_prune_of i1 (lifeline a) i1')
                          -> (is_next_of (interaction_seq i1 i2) a (interaction_seq i1' i2'))
|execute_loop_strict : forall (a:Action) (i1 i1' : Interaction),
                          (is_next_of i1 a i1') 
                             -> (is_next_of 
                                       (interaction_loop lstrict i1)
                                       a
                                       (interaction_strict i1' (interaction_loop lstrict i1))
                                )
|execute_loop_seq    : forall (a:Action) (i1 i1' : Interaction),
                          (is_next_of i1 a i1') 
                             -> (is_next_of 
                                       (interaction_loop lseq i1)
                                       a
                                       (interaction_seq i1' (interaction_loop lseq i1))
                                )
|execute_loop_par    : forall (a:Action) (i1 i1' : Interaction),
                          (is_next_of i1 a i1') 
                             -> (is_next_of 
                                       (interaction_loop lpar i1)
                                       a
                                       (interaction_par i1' (interaction_loop lpar i1))
                                ).


(**
**** Properties w.r.t. the denotational semantics

In the following, I will state some properties of the execution relation w.r.t. the denotational semantics "sem_de".

Let us remark that the intuitive meaning of the "is_next_of" predicate is attached to the following property:
If (is_next_of i a i') and the remaining interaction i' accepts a trace t
then the original interaction i should accept the trace (a::t).

This property is formalized and proven in the "execute_keep_de" Lemma below.
**)

Lemma execute_keep_de (i i': Interaction) (a:Action) (t:Trace) :
  (is_next_of i a i') 
  -> (sem_de i' t)
  -> (sem_de i (a::t) ).
Proof.
intros H1 H2. 
dependent induction H1 generalizing t.
- simpl. inversion H2. reflexivity.
- simpl. left.
  apply IHis_next_of.
  assumption.
- simpl. right.
  apply IHis_next_of.
  assumption.
- simpl in *.
  destruct H2 as (t1,H).
  destruct H as (t2,H).
  destruct H as (Hi1,H).
  destruct H as (Hi2,H).
  exists (a::t1). exists t2.
  split.
  + apply IHis_next_of ; assumption.
  + split.
    { assumption. }
    { apply interleaving_cons_left. assumption. }
- simpl in *.
  destruct H2 as (t1,H).
  destruct H as (t2,H).
  destruct H as (Hi1,H).
  destruct H as (Hi2,H).
  exists t1. exists (a::t2).
  split.
  + assumption.
  + split.
    { apply IHis_next_of ; assumption. }
    { apply interleaving_cons_right. assumption. }
- simpl in *.
  destruct H2 as (t1,H).
  destruct H as (t2,H).
  destruct H as (Hi1,H).
  destruct H as (Hi2,H).
  exists (a::t1). exists t2.
  split.
  + apply IHis_next_of ; assumption.
  + split.
    { assumption. }
    { simpl. rewrite H. reflexivity. }
- simpl in *. 
  exists nil. exists (a::t).
  split.
  + apply terminates_implies_de_accept_nil. assumption.
  + split.
    * apply (IHis_next_of). assumption.
    * simpl. reflexivity.
- simpl in *.
  destruct H2 as (t1,H).
  destruct H as (t2,H).
  destruct H as (Hi1,H).
  destruct H as (Hi2,Hws).
  exists (a::t1). exists t2.
  split.
  + apply (IHis_next_of). assumption.
  + split.
    * assumption.
    * apply weak_seq_cons_left.
      assumption.
- simpl in *.
  destruct H2 as (t1,H2).
  destruct H2 as (t2,H2).
  destruct H2 as (Hi1,H2).
  destruct H2 as (Hi2,Hws).
  exists t1. exists (a::t2).
  split.
  + apply (prune_kept_de i1 i1' (lifeline a)).
    split ; assumption.
  + split.
    * apply IHis_next_of. assumption.
    * apply weak_seq_cons_right.
      { assumption. }
      { apply (prune_removes_conflicts i1 i1') ; assumption. }
- simpl in H2.
  destruct H2 as (t1,H).
  destruct H as (t2,H).
  destruct H as (Hi1,H).
  destruct H as (H,Hconc).
  destruct H as (subs,H).
  destruct H as (Hin,Hrep).
  simpl.
  exists ((a::t1)::subs).
  split.
  + intros t0 Ht0.
    inversion Ht0.
    * destruct H. apply IHis_next_of. assumption.
    * apply Hin. assumption.
  + symmetry in Hconc. destruct Hconc.
    apply (merge_strict subs (a::t1) t2).
    * intro. discriminate.
    * assumption.
- simpl in H2.
  destruct H2 as (t1,H).
  destruct H as (t2,H).
  destruct H as (Hi1,H).
  destruct H as (H,Hconc).
  destruct H as (subs,H).
  destruct H as (Hin,Hrep).
  simpl.
  exists ((a::t1)::subs).
  split.
  + intros t0 Ht0.
    inversion Ht0.
    * destruct H. apply IHis_next_of. assumption.
    * apply Hin. assumption.
  + apply (merge_seq subs (a::t1) t2 (a::t)).
    * intro. discriminate.
    * assumption.
    * apply weak_seq_cons_left. assumption.
- simpl in H2.
  destruct H2 as (t1,H).
  destruct H as (t2,H).
  destruct H as (Hi1,H).
  destruct H as (H,Hconc).
  destruct H as (subs,H).
  destruct H as (Hin,Hrep).
  simpl.
  exists ((a::t1)::subs).
  split.
  + intros t0 Ht0.
    inversion Ht0.
    * destruct H. apply IHis_next_of. assumption.
    * apply Hin. assumption.
  + apply (merge_par subs (a::t1) t2 (a::t)).
    * intro. discriminate.
    * assumption.
    * apply interleaving_cons_left. assumption.
Qed.

(**
*** Formal definition of the operational semantics

Now that I have laid the groundworks of this definition, via the formulation of the execution relation,
I can formally define the operational-style semantics "sem_op" in a similar fashion as "sem_de"
i.e. as a predicate such that, for any interaction i and any trace t,
(sem_op i t) is a predicate which states that trace t belongs to the semantics of interaction i.

Let us remark that the definition of "sem_de" was done using a Fixpoint.
By contrast, I will use an inductive predicate to define "sem_op".
The construction of this inductive predicate relies on two construction rules:
- "sem_op_empty", which is the base case and states that for any interaction, if it terminates then the empty trace is in its semantics
- "sem_op_event", which corresponds to the use of the small-step, states that if an interaction i can execute an action a and turn into interaction i', and, if interaction i' can express a trace t, then i can express (a::t)
**)

Inductive sem_op : Interaction -> Trace -> Prop :=
 | sem_op_empty  : forall (i:Interaction),
                      (terminates i)  
                      -> (sem_op i nil)
 | sem_op_event : forall (i i':Interaction) (a:Action) (t:Trace),
                      (is_next_of i a i')
                      -> (sem_op i' t)
                      -> (sem_op i (a::t) ).

(**
Now that we have defined "sem_op", we can immediately prove the inclusion of "sem_op" into "sem_de"
thanks to the Lemmas that we have proven relating to the relationship of "sem_de" w.r.t. the
intermediate functions (terminates, avoids, prune, is_next_of).

Notably, we have already proven that "sem_de" accepts the same two construction rules as "sem_op". Indeed:
- Lemma "terminates_implies_de_accept_nil" states that sem_de verifies the "sem_op_empty" rule
- Lemma "execute_keep_de" states that sem_de verifies the "sem_op_event" rule
**)


Theorem op_implies_de (i : Interaction) (t : Trace) :
  (sem_op i t) -> (sem_de i t).
intros H.
dependent induction t generalizing i.
- apply terminates_implies_de_accept_nil.
  inversion H. assumption.
- inversion H. 
  symmetry in H1. destruct H1.
  symmetry in H0. destruct H0.
  symmetry in H2. destruct H2.
  apply (execute_keep_de i i' a t).
  + assumption.
  + apply (IHt i').
    assumption.
Qed.

(**
What was discussed just above implies the inclusion of "sem_op" into "sem_de".

However it does not implies the reciprocate (i.e. whether or not "sem_de" is included in "sem_op").
Indeed, it may be so that, if it were formulated using construction rules,
"sem_de" would also verify some other construction rules in addition to "sem_op_empty" and "sem_op_event",
which would allow the acceptation of some more traces in the semantics.

The proof in that other direction is explained in the next section.
**)



(**
** Proof of the inclusion of "sem_de" into "sem_op"

*** Hypotheses de tri

The rest of the proof relies on some hypotheses on the fact that,
when computing the denotational semantics "sem_de" for loops
i.e. for interactions which root node is a loop operator,
the traces issued from each iteration of the sub-behavior are sorted
by order of occurence in the "subs" list of traces that is used for the merger.

Let us indeed recall the definition of "sem_de":

<<
Fixpoint sem_de (i : Interaction) : (Trace -> Prop) :=
match i with
|interaction_empty          => fun t:Trace => 
                                  t = nil
|(interaction_act a)        => fun t:Trace => 
                                  t = a :: nil
|(interaction_alt i1 i2)    => fun t:Trace => 
                                  (sem_de i1 t) \/ (sem_de i2 t)
|(interaction_par i1 i2)    => fun t:Trace => 
                                  exists (t1 t2:Trace), 
                                    (sem_de i1 t1) /\ (sem_de i2 t2) /\ (is_interleaving t1 t2 t)
|(interaction_strict i1 i2) => fun t:Trace => 
                                  exists (t1 t2:Trace), 
                                    (sem_de i1 t1) /\ (sem_de i2 t2) /\ (t = t1 ++ t2)
|(interaction_seq i1 i2)    => fun t:Trace => 
                                  exists (t1 t2:Trace), 
                                    (sem_de i1 t1) /\ (sem_de i2 t2) /\ (is_weak_seq t1 t2 t)
|(interaction_loop lk i1)   => fun t:Trace => 
                                  exists (subs:list Trace),
                                    (forall (t0:Trace), (In t0 subs) -> (sem_de i1 t0) )
                                    /\ (n_merge_schedule lk subs t)
>>

We can see that, for defining the semantics of loops, we use a certain list of traces "subs".
This list of (potentially disctinct) traces enumerates the successive iterations of the behaviors
of the sub(interaction "i1".
A trace is then accepted by the interaction if it is a merger of those traces.

However, as per the definition of the weak sequencing and interleaving operators on traces, nothing prevents
those traces to be put in any order within "subs".

The formal proof on Coq relies on a good faith hypothesis that the traces are inserted in "subs"
during the construction of the denotational semantics
in the same order as that of the instanciations of the sub-interactions i1' that are
operated by the operational semantics.
**)

Lemma n_merge_schedule_cons_strict_prop (subs:list Trace) (t:Trace) (a:Action):
  (n_merge_schedule lstrict subs (a :: t))
  -> ( exists (t0:Trace) (remain:list Trace),
        subs = (a::t0)::remain
     ).
Proof.
intros.
dependent induction subs.
- inversion H.
- inversion H. destruct H0.
  destruct H1. 
  symmetry in H2.
  apply (cons_eq_app Action) in H2.
  destruct H2.
  + destruct H0.
    symmetry in H0. destruct H0.
    contradiction. 
  + destruct H0 as (t1,H0).
    exists t1. exists remain.
    rewrite <- H0. reflexivity.
Qed.

Lemma hypothese_de_tri_strict 
  (t0 t t_merge_remain:Trace) (remain:list Trace) (a:Action) :
(n_merge_schedule lstrict ((a :: t0) :: remain) (a :: t))
-> (n_merge_schedule lstrict remain t_merge_remain)
-> (t = t0 ++ t_merge_remain).
Proof.
Admitted.

Lemma n_merge_schedule_cons_seq_prop (subs:list Trace) (t:Trace) (a:Action):
  (n_merge_schedule lseq subs (a :: t))
  -> ( exists (n:nat) (t0:Trace),
       (n<length subs) 
       /\ ( (a::t0) = (nth n subs nil) )
       /\ ( 
            ( 
                 (t0<>nil) 
                 /\ (n_merge_schedule lseq (subs_replace n subs t0) t)
            )
            \/ ( (t0=nil)
                 /\ (n_merge_schedule lseq (subs_remove n subs) t)
               )
          )
     ).
Proof.
Admitted.

Lemma hypothese_de_tri_weak_seq 
 (t0 t:Trace) (subs:list Trace) (n:nat) :
  (n < length subs)
  -> (n_merge_schedule lseq (subs_replace n subs t0) t)
  -> (exists t':Trace,
          (n_merge_schedule lseq (subs_remove n subs) t')
          /\ (is_weak_seq t0 t' t)
     ).
Proof.
Admitted.

Lemma n_merge_schedule_cons_par_prop (subs:list Trace) (t:Trace) (a:Action):
  (n_merge_schedule lpar subs (a :: t))
  -> ( exists (n:nat) (t0:Trace),
       (n<length subs) 
       /\ ( (a::t0) = (nth n subs nil) )
       /\ ( 
            ( 
                 (t0<>nil) 
                 /\ (n_merge_schedule lpar (subs_replace n subs t0) t)
            )
            \/ ( (t0=nil)
                 /\ (n_merge_schedule lpar (subs_remove n subs) t)
               )
          )
     ).
Proof.
Admitted.

Lemma hypothese_de_tri_interleaving 
 (t0 t:Trace) (subs:list Trace) (n:nat) :
  (n < length subs)
  -> (n_merge_schedule lpar (subs_replace n subs t0) t)
  -> (exists t':Trace,
          (n_merge_schedule lpar (subs_remove n subs) t')
          /\ (is_interleaving t0 t' t)
     ).
Proof.
Admitted. 

(**

*** Existence of a next interaction

Let us recall that the proof in the other direction relied on th definition of
the following Lemma:
<<
Lemma execute_keep_de (i i': Interaction) (a:Action) (t:Trace) :
  (is_next_of i a i') 
  -> (sem_de i' t)
  -> (sem_de i (a::t) ).
>>

In order to prove this direction, we would need some sort of reciprocate to "execute_keep_de".

This reciprocate take the following form:
<<
Lemma de_accept_cons_implies_execution_possible 
  (i : Interaction) (a:Action) (t:Trace) :
  (sem_de i (a::t) )
    -> (exists (i':Interaction), (is_next_of i a i') /\ (sem_de i' t) ).
>>

It states that if a given interaction "i" accepts a trace that starts with an action "a",
then there must exist some interaction "i'" that results from the execution of "a" in "i"
and this interaction "i'" must accept "t".

Let us remark that another added difficulty to this proof lies in the fact that we do not have
the unicity of the "i'" that can satisfy "(is_next_of i a i')".

Indeed, given that we do not uniquely identify the executions of actions via their positions
in the syntactic term "i", and because there can be several occurences of a leaf term "a"
in the tree-structure of "i", there can be several such "i'".
**)

Lemma de_accept_cons_implies_execution_possible 
  (i : Interaction) (a:Action) (t:Trace) :
  (sem_de i (a::t))
    -> (exists (i':Interaction), (is_next_of i a i') /\ (sem_de i' t) ).
Proof.
intros H.
dependent induction i. 
- simpl in H. inversion H.
- simpl in H. inversion H.
  symmetry in H1. destruct H1.
  symmetry in H2. destruct H2.
  exists interaction_empty. simpl.
  split.
  + apply execute_at_leaf.
  + reflexivity.
- simpl in H.
  destruct H as (t1,H).
  destruct H as (t2,H).
  destruct H.
  destruct H0.
  destruct t1.
  + simpl in H1. destruct H1.
    apply IHi2 in H0.
    destruct H0 as (i2',H0).
    destruct H0.
    exists i2'.
    split.
    * apply execute_right_strict.
      { assumption. }
      { apply de_accept_nil_implies_terminates.
        assumption. }
    * assumption.
  + inversion H1. 
    destruct H3.
    simpl in H1.
    apply IHi1 in H. 
    destruct H as (i1',H). 
    exists (interaction_strict i1' i2).
    destruct H.
    split.
    * apply execute_left_strict. assumption.
    * simpl. exists t1. exists t2.
      split.
      { assumption. }
      { split. 
        - assumption. 
        - reflexivity.
      }
- simpl in H.
  destruct H as (t1,H).
  destruct H as (t2,H).
  destruct H.
  destruct H0.
  destruct t1.
  + apply is_weak_seq_nil_prop2 in H1.
    symmetry in H1. destruct H1.
    apply IHi2 in H0.
    destruct H0 as (i2',H0).
    destruct H0.
    assert (H' := H). 
    apply (de_accept_nil_implies_prunable i1 (lifeline a)) in H.
    destruct H as (i1',H).
    exists (interaction_seq i1' i2').
    simpl. split.
    * apply execute_right_seq.
      { assumption. }
      { assumption. }
    * exists nil. exists t.
      split.
      { apply (de_accept_nil_implies_pruned_de_accept_nil i1 i1' (lifeline a)) ; assumption. }
      { split.
        - assumption.
        - apply weak_seq_nil_left.
      }
  + inversion H1.
    * symmetry in H2. destruct H2.
      destruct H3.
      symmetry in H5. destruct H5.
      symmetry in H6. destruct H6.
      apply IHi1 in H.
      destruct H as (i1',H).
      destruct H.
      exists (interaction_seq i1' i2).
      split.
      { apply execute_left_seq. assumption. }
      { simpl. exists t. exists nil.
        split.
        - assumption.
        - split.
          + assumption.
          + apply weak_seq_nil_right.
      }
   * symmetry in H2. destruct H2.
     symmetry in H6. destruct H6.
     symmetry in H3. destruct H3.
     symmetry in H4. destruct H4.
     symmetry in H7. destruct H7.
     apply IHi1 in H.
     destruct H as (i1',H).
      destruct H.
      exists (interaction_seq i1' i2).
      split.
      { apply execute_left_seq. assumption. }
      { simpl. exists t1. exists t2.
        split.
        - assumption.
        - split.
          + assumption.
          + assumption.
      }
   * symmetry in H2. destruct H2.
     symmetry in H3. destruct H3.
     symmetry in H4. destruct H4.
     destruct H5.
     apply IHi2 in H0. 
     destruct H0 as (i2',Hi2).
     destruct Hi2 as (Hi2,Hd2).
     pose proof (de_accept_t_and_no_conflict_implies_pruned_de_accept_t).
     assert (exists i' : Interaction, is_prune_of i1 (lifeline a) i'). 
     { apply (de_accept_t_and_no_conflict_implies_prunable i1 a (a0::t1)) ; assumption. }
     destruct H2 as (i1',Hp1).
     exists (interaction_seq i1' i2').
      split.
      { apply execute_right_seq ; assumption. }
      { simpl. exists (a0::t1).
        exists t4.
        split.
        - apply (de_accept_t_and_no_conflict_implies_pruned_de_accept_t i1 i1' a (a0::t1)).
          + assumption.
          + assumption.
          + assumption.
        - split ; assumption.
      }
- simpl in H.
  destruct H as (t1,H).
  destruct H as (t2,H).
  destruct H.
  destruct H0.
  destruct t1.
  + apply is_interleaving_nil_prop2 in H1.
    symmetry in H1. destruct H1.
    apply IHi2 in H0.
    destruct H0 as (i2',H0).
    destruct H0.
    exists (interaction_par i1 i2').
    simpl. split.
    * apply execute_right_par. 
      assumption.
    * exists nil. exists t.
      split.
      { assumption. }
      { split.
        - assumption. 
        - apply interleaving_nil_left.
      }
  + inversion H1.
    * symmetry in H2. destruct H2.
      destruct H3.
      symmetry in H5. destruct H5.
      symmetry in H6. destruct H6.
      apply IHi1 in H.
      destruct H as (i1',H).
      destruct H.
      exists (interaction_par i1' i2).
      split.
      { apply execute_left_par. assumption. }
      { simpl. exists t. exists nil.
        split.
        - assumption.
        - split.
          + assumption.
          + apply interleaving_nil_right.
      }
   * symmetry in H2. destruct H2.
     symmetry in H6. destruct H6.
     symmetry in H3. destruct H3.
     symmetry in H4. destruct H4.
     symmetry in H7. destruct H7.
     apply IHi1 in H.
     destruct H as (i1',H).
      destruct H.
      exists (interaction_par i1' i2).
      split.
      { apply execute_left_par. assumption. }
      { simpl. exists t1. exists t2.
        split.
        - assumption.
        - split.
          + assumption.
          + assumption.
      }
   * symmetry in H2. destruct H2.
     symmetry in H3. destruct H3.
     destruct H4.
     symmetry in H6. destruct H6.
     apply IHi2 in H0. 
     destruct H0 as (i2',Hi2).
     destruct Hi2 as (Hi2,Hd2).
     exists (interaction_par i1 i2').
      split.
      { apply execute_right_par.
        assumption.
      }
      { simpl. exists (a0::t1).
        exists t4.
        split.
        - assumption.
        - split ; assumption.
      }
- simpl in H. destruct H.
  + apply IHi1 in H.
    destruct H as (i1',H).
    destruct H.
    exists i1'.
    split.
    * apply execute_left_alt. assumption.
    * assumption.
  + apply IHi2 in H.
    destruct H as (i2',H).
    destruct H.
    exists i2'.
    split.
    * apply execute_right_alt. assumption.
    * assumption.
- simpl in H.
  destruct H as (subs,H).
  destruct H as (Hin,Hrep).
  destruct s.
  + assert (Hr:=Hrep).
    apply (n_merge_schedule_cons_strict_prop subs t a) in Hrep.
    destruct Hrep as (t0,H).
    destruct H as (remain,H).
    symmetry in H. destruct H.
    { assert (In (a::t0) ((a :: t0) :: remain) ).
      { simpl. left. reflexivity. }
      apply Hin in H.
      apply IHi in H.
      destruct H as (i',Hi').
      destruct Hi' as (Hnext,Hi').
      exists (interaction_strict i' (interaction_loop lstrict i)).
      split.
      { apply execute_loop_strict. assumption. }
      { simpl. exists t0.
        assert (exists t : Trace, n_merge_schedule lstrict remain t).
        { apply (n_merge_schedule_existence lstrict remain).
          intros. 
          apply (n_merge_schedule_nonil_prop0 lstrict ((a :: t0) :: remain) (a :: t)).
          - assumption.
          - simpl. right. assumption.
        }
        destruct H as (t_merge_remain,H).
        exists t_merge_remain.
        split.
        - assumption.
        - split.
          + exists remain.
            split.
            * intros. apply Hin. simpl. right. assumption. 
            * assumption.
          + apply (hypothese_de_tri_strict t0 t t_merge_remain remain a) ; assumption. 
      }
    }
  + assert (Hr:=Hrep).
    apply (n_merge_schedule_cons_seq_prop subs t a) in Hrep.
    destruct Hrep as (n,H). destruct H as (t0,H).
    destruct H. destruct H0. destruct H1.
    { destruct H1.
      assert (In (a::t0) subs).
      { rewrite H0. apply nth_In. assumption. }
      apply Hin in H3.
      apply IHi in H3.
      destruct H3 as (i',Hi').
      destruct Hi' as (Hnext,Hi').
      exists (interaction_seq i' (interaction_loop lseq i)).
      split.
      { apply execute_loop_seq. assumption. }
      { simpl. exists t0. 
        assert (exists t' : Trace, n_merge_schedule lseq (subs_remove n subs) t' 
                                   /\ is_weak_seq t0 t' t).
        { apply (hypothese_de_tri_weak_seq t0 t subs n) ; assumption. }
        destruct H3 as (t2,H3). destruct H3.
        exists t2.
        split.
        - assumption.
        - split.
          + exists (subs_remove n subs).
            split.
            * intros. apply subs_remove_keep_in in H5. apply Hin. assumption.
            * assumption.
          + assumption.
      }
    }
    { destruct H1. symmetry in H1. destruct H1.
      assert (In (a::nil) subs).
      { rewrite H0. apply nth_In. assumption. }
      apply Hin in H1.
      apply IHi in H1.
      destruct H1 as (i',Hi').
      destruct Hi' as (Hnext,Hi').
      exists (interaction_seq i' (interaction_loop lseq i)).
      split.
      { apply execute_loop_seq. assumption. }
      { simpl. exists nil. exists t.
        split.
        - assumption.
        - split.
          + exists (subs_remove n subs).
            split.
            * intros. apply Hin. apply subs_remove_keep_in in H1. assumption.
            * assumption.
          + apply weak_seq_nil_left.
      }
    }
  + assert (Hr:=Hrep).
    apply (n_merge_schedule_cons_par_prop subs t a) in Hrep.
    destruct Hrep as (n,H). destruct H as (t0,H).
    destruct H. destruct H0. destruct H1.
    { destruct H1.
      assert (In (a::t0) subs).
      { rewrite H0. apply nth_In. assumption. }
      apply Hin in H3.
      apply IHi in H3.
      destruct H3 as (i',Hi').
      destruct Hi' as (Hnext,Hi').
      exists (interaction_par i' (interaction_loop lpar i)).
      split.
      { apply execute_loop_par. assumption. }
      { simpl. exists t0. 
        assert (exists t' : Trace, n_merge_schedule lpar (subs_remove n subs) t' 
                                   /\ is_interleaving t0 t' t).
        { apply (hypothese_de_tri_interleaving t0 t subs n) ; assumption. }
        destruct H3 as (t2,H3). destruct H3.
        exists t2.
        split.
        - assumption.
        - split.
          + exists (subs_remove n subs).
            split.
            * intros. apply subs_remove_keep_in in H5. apply Hin. assumption.
            * assumption.
          +  assumption.
      }
    }
    { destruct H1. symmetry in H1. destruct H1.
      assert (In (a::nil) subs).
      { rewrite H0. apply nth_In. assumption. }
      apply Hin in H1.
      apply IHi in H1.
      destruct H1 as (i',Hi').
      destruct Hi' as (Hnext,Hi').
      exists (interaction_par i' (interaction_loop lpar i)).
      split.
      { apply execute_loop_par. assumption. }
      { simpl. exists nil. exists t.
        split.
        - assumption.
        - split.
          + exists (subs_remove n subs).
            split.
            * intros. apply Hin. apply subs_remove_keep_in in H1. assumption.
            * assumption.
          + apply interleaving_nil_left.
      }
    }
Qed.  


(**
We can finally prove the inclusion of "sem_de" into "sem_op".
**)

Theorem de_implies_op (i : Interaction) (t : Trace) :
  (sem_de i t) -> (sem_op i t).
intros H.
dependent induction t generalizing i. 
- apply sem_op_empty.
  apply de_accept_nil_implies_terminates.
  assumption.
- apply de_accept_cons_implies_execution_possible in H.
  destruct H as (i',H).
  destruct H.
  apply (sem_op_event i i').
  + assumption.
  + apply IHt. assumption.
Qed.

(**
* Conclusion

Finally we have proven the equivalence of both semantics,
as stated by the "sem_equivalence" Theorem.

**)
  
Theorem sem_equivalence (i : Interaction) (t : Trace) :
  (sem_op i t) <-> (sem_de i t).
Proof.
split.
- apply op_implies_de.
- apply de_implies_op.
Qed.





