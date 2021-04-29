(* =========================================================== *)
(**
* Coq Proof for the equivalence of three semantics defined on a formal language for modelling distributed systems
Erwan Mahe - 2021

We use Coq to:
- formally encode an Interaction Language for modelling the behavior of distributed systems
- define a formal semantics in denotational style on this language
- define another formal semantics, this time in operational style
- prove the equivalence between the denotational and operational semantics
- propose an algorithmization of the operational semantics that we call the execution semantics
- prove the equivalence between the execution and the operational semantics and therefore also w.r.t. the denotational semantics

This proof accompanies the manuscript of my thesis

** Context

The formal language that we consider is that of interactions.
Interactions can be described as a formalisation of graphical models such as Message Sequence Charts or UML Sequence Diagrams.

An interaction describes the behaviors that can be expressed by a distributed system.
Those behaviors take the form of sequences of obserable events (discrete events), that we call traces (traces of execution).
In a more practical setting, a trace can for instance correspond to a log file,
in which the occurence of some discrete events have been recorded progressively during an execution of the system.

The events that constitute traces are atomic communication actions that occur on the interfaces of the distributed
system's sub-systems.
Those atomic actions correspond to either the emission or the reception of
a given message on a given sub-system.

The semantic domain of interest is therefore that of traces. The semantics of a given interaction is a given set of traces.
In the following, we will propose three different manners to define the semantics of interactions, and we will prove the equivalence
of those definitions. Those three definitions correspond to:
- a _denotational-style_ semantics, which consists in constructing sets of accepted traces by _composition_ and using algebraic properties of some operators on sets of traces
- an _operational-style_ semantics, which consists in considering how can an interaction model be executed dynamically, and which behaviors it thus expresses. For a given interaction "i", it may be possible to transform it into interaction "i'" through the expression of an action. By considering all those possible transformations, we can construct the semantics of interaction "i" using _recursion_ on the semantics of those transformed "i'" interactions.
- an _execution_ semantics, which is an algorithmization of the _operational-style_ semantics that consists in separating the process described by the operational semantics into two parts. At first we identify which actions can be immediately executed in a given interaction. And then, we construct the interaction term that remains to be executed.

** Related works

*** Publications

- #<a href="https://link.springer.com/chapter/10.1007%2F978-3-030-45234-6_24">Revisiting Semantics of Interactions for Trace Validity Analysis</a># 
- #<a href="https://dl.acm.org/doi/10.1145/3412841.3442054">A small-step approach to multi-trace checking against interactions</a># 

*** Other Coq proves and tools

The coq file itself is hosted on the following repository:
- #<a href="https://github.com/erwanM974/coq_hibou_label_semantics_equivalence">https://github.com/erwanM974/coq_hibou_label_semantics_equivalence</a># 

A prototype tool, which implements some formal verification techniques using the execution semantics
is available on the following repository:
- #<a href="https://github.com/erwanM974/hibou_label">https://github.com/erwanM974/hibou_label</a># 

The nature of distributed systems makes so that it is often impossible to reorder globally the events that occured on distrinct sub-systems during an execution
of the system. Let us remark that this is related to the absence of a global clock.
In any case, what can be concretely logged during the execution of a distributed system is most oftentimes rather a set of locally defined log files.
In the semantic domain, this translates into having sets of locally observed traces, which we call multi-traces.
Another Coq proof, that is interested in the handling of multi-traces
and how one can test them w.r.t. the semantics (the Oracle problem for some form of a trace conformance relation / membership)
is available on the following repository:
- #<a href="https://github.com/erwanM974/coq_hibou_label_multi_trace_analysis">https://github.com/erwanM974/coq_hibou_label_multi_trace_analysis</a># 

** Dependencies
Below are listed the libraries required for this Coq proof.
- "Coq.Bool.Bool." provides utilities related to the manipulation of booleans
- "Coq.Lists.List." provides utilities on lists. I use lists - among other things - to represent traces.
- "Coq.Vectors.Fin." provides a means to represent finite sets indexed by {1,...,n}.
- "Psatz." is required for using the "lia" tactic to solve simple arithemtic problems.
- "Coq.Program.Equality." is required for using the "dependent induction" tactic with "generalizing", allowing the generalisation of some variables of the problem in the induction hypothesis.
- "Coq.Init.Logic." for (among other things) the "not_eq_sym" theorem
- "Coq.Init.Nat.", "Coq.Arith.PeanoNat." and "Coq.Arith.Peano_dec." for the manipulation of natural integers and the use of some lemmas
**)

Require Import Coq.Bool.Bool.
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
**)

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
Given that we will manipulate elements of "L" (lifelines)
for the proofs regarding the execution semantics,
we formulate the following three basic properties:
- "L_neqb", which states that the inequality "l <> l'" (as a proposition) is equivalent to the fact that the boolean "Fin.eqb l l'" is false
- "L_not_neq", which states that if a lifeline "l" is not different from a lifeline "l'" then "l=l'"
- "L_neq_or_not_neq", which is a Lemma on the decidability of the unequality of lifelines
**)

Lemma L_neqb :
  forall (l l':L),
    (l <> l') <-> (Fin.eqb l l' = false).
Proof.
Admitted.

Lemma L_not_neq :
  forall (l l':L),  
    (~ (l <> l'))
    -> (l = l').
Proof.
Admitted.

Lemma L_neq_or_not_neq (x y:L) :
  (x <> y) \/ (not(x<>y)).
Proof.
pose proof (Fin.eq_dec x y).
destruct H.
- right. intro. contradiction.
- left. assumption.
Qed.

(**
We denote by "l!m" the emission of message "m" (element of "M") from lifeline "l" (element of "L").
We denote by "l?m" the reception of message "m" (element of "M") by lifeline "l" (element of "L").
To distinguish between emissions and receptions I encode the kind of action
({!,?}) with an inductive type "ActKind".
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

For the concatenation operator "++", most interesting properties are already shipped in with Coq
and can be used in proofs more or less direclty (with "simpl.", "inversion." and so on).
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
Interesting properties of the "is_interleaving" that will be useful later on
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

Lemma is_interleaving_commutativity (t1 t2 t:Trace) :
  (is_interleaving t1 t2 t) <-> (is_interleaving t2 t1 t).
Proof.
dependent induction t generalizing t1 t2.
- split ; intros ; apply is_interleaving_nil_prop1 in H
  ; destruct H ; symmetry in H ; destruct H ; symmetry in H0 ; destruct H0
  ; apply interleaving_nil_left.
- split ; intros.
  + inversion H.
    * apply interleaving_nil_right.
    * apply interleaving_nil_left.
    * destruct H1. apply interleaving_cons_right.
      apply IHt. assumption.
    * destruct H2. apply interleaving_cons_left.
      apply IHt. assumption. 
  + inversion H.
    * apply interleaving_nil_right.
    * apply interleaving_nil_left.
    * destruct H1. apply interleaving_cons_right.
      apply IHt. assumption.
    * destruct H2. apply interleaving_cons_left.
      apply IHt. assumption. 
Qed.

Lemma is_interleaving_assoc (t1 t2 t3 tmA tmB t:Trace):
  (is_interleaving t1 t2 tmA)
  -> (is_interleaving t2 t3 tmB)
  -> ( (is_interleaving tmA t3 t) <-> (is_interleaving t1 tmB t)).
Proof.
Admitted.

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
In a similar fashion to what I did for the interleaving operator, I state some properties of the weak sequencing operator
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

Lemma is_weak_seq_assoc (t1 t2 t3 tmA tmB t:Trace):
  (is_weak_seq t1 t2 tmA)
  -> (is_weak_seq t2 t3 tmB)
  -> ( (is_weak_seq tmA t3 t) <-> (is_weak_seq t1 tmB t)).
Proof.
Admitted.

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
one can define an prove some properties for the merge operator
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
  -> (forall t0 : Trace, In t0 subs -> t0<>nil).
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

Lemma n_merge_schedule_single_merge (lk:ScheduleKind) (x t:Trace) :
  (n_merge_schedule lk (t :: nil) x)
  -> (t=x).
Proof.
Admitted.


Lemma n_merge_add_left (lk:ScheduleKind) (subs:list Trace) (t1 t:Trace) (a:Action):
  (n_merge_schedule lk (t1 :: subs) t)
  -> (n_merge_schedule lk ((a::t1) :: subs) (a::t)).
Proof.
Admitted.

Lemma n_merge_seq_reorder_prop1 (sub1 sub3 : list Trace) (t2 t : Trace) (a:Action):
  (n_merge_schedule lseq (sub1 ++ (t2::sub3)) t)
  -> (forall t1:Trace, (In t1 sub1) -> (no_conflict t1 a))
  -> (n_merge_schedule lseq (sub1 ++ ((a::t2)::sub3)) (a::t)).
Proof.
intros.
dependent induction sub1.
- simpl in *.
  apply n_merge_add_left. assumption.
- inversion H.
  destruct H1.
  symmetry in H6. destruct H6.
  apply (merge_seq (sub1 ++ (a0::t2)::sub3) t_first (a0::t_rep)).
  + assumption.
  + apply IHsub1.
    * assumption.
    * intros. apply H0. simpl. right. assumption.
  + apply weak_seq_cons_right.
    * assumption.
    * apply H0. simpl. left. reflexivity.
Qed.

Lemma n_merge_lseq_bi_assoc (sub1 sub2 : list Trace) (t1 t2 t : Trace):
  (n_merge_schedule lseq sub1 t1)
  -> (n_merge_schedule lseq sub2 t2)
  -> (is_weak_seq t1 t2 t)
  -> (n_merge_schedule lseq (sub1++sub2) t).
Proof.
intros.
dependent induction H generalizing sub2 t2 t.
- simpl.
  apply is_weak_seq_nil_prop2 in H1.
  destruct H1. assumption.
- pose proof (is_weak_seq_existence t_rep t2).
  destruct H4 as (t3,H4).
  apply (merge_seq (remain++sub2) t_first t3 t).
  + assumption.
  + apply (IHn_merge_schedule sub2 t2 t3).
    * reflexivity.
    * assumption.
    * assumption.
  + apply (is_weak_seq_assoc t_first t_rep t2 t_merge) ; assumption.
Qed.


Lemma n_merge_lseq_sandwich (sub1 sub3 : list Trace) (t1 t2 t3 tm t : Trace):
  (*(t2<>nil)
  ->*) (n_merge_schedule lseq sub1 t1)
  -> (n_merge_schedule lseq sub3 t3)
  -> (is_weak_seq t2 t3 tm)
  -> (is_weak_seq t1 tm t)
  -> (n_merge_schedule lseq (sub1 ++ t2 :: sub3) t).
Proof.
intros.
apply (n_merge_lseq_bi_assoc sub1 (t2::sub3) t1 tm).
- assumption.
- apply (merge_seq sub3 t2 t3 tm).
  + admit.
  + assumption.
  + assumption.
- assumption.
Admitted.

Lemma n_merge_lpar_bi_assoc (sub1 sub2 : list Trace) (t1 t2 t : Trace):
  (n_merge_schedule lpar sub1 t1)
  -> (n_merge_schedule lpar sub2 t2)
  -> (is_interleaving t1 t2 t)
  -> (n_merge_schedule lpar (sub1++sub2) t).
Proof.
intros.
dependent induction H generalizing sub2 t2 t.
- simpl.
  apply is_interleaving_nil_prop2 in H1.
  destruct H1. assumption.
- pose proof (is_interleaving_existence t_rep t2).
  destruct H4 as (t3,H4).
  apply (merge_par (remain++sub2) t_first t3 t).
  + assumption.
  + apply (IHn_merge_schedule sub2 t2 t3).
    * reflexivity.
    * assumption.
    * assumption.
  + apply (is_interleaving_assoc t_first t_rep t2 t_merge) ; assumption.
Qed.

(**
*** Some considerations on the distributivity of "no_conflict" w.r.t. the previous operators

In the following we demonstrate the distributive composition of the "no_conflict" function w.r.t.
the three scheduling operators and the merge operator 
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
- the definition of the syntax of the interaction language. This syntax corresponds to the definition of a context-free grammar in which terms are build inductively from some basic terms and the application of some unary and binary constructors to form more complex terms (as binary trees)
- the definition of a denotational-style semantics based on the composition of sets of traces using the previously defined operators on the semantic domain
- the definition of a structural operational semantics and the proof of its equivalence w.r.t. the denotational one
- the definition of an algorithmization of the operational semantics and the proof of its equivalence w.r.t. the operational semaantics
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
** Operational Semantics

By contrast we have not yet laid the groundworks for the definition of the operational-style semantics.

In the following, we will progressively introduce the intermediate functions required for this definition.
In the meanwhile we will state some Lemmas which describe how the denotational-style semantics "sem_de" relates to those intermediate functions.
Those Lemmas will incidentaly constitute elements for the proof of equivalence between
the operational-style semantics
and the denotational-style semantics.

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
- apply L_neq_or_not_neq.
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

In the following we are interested in the question of how to rewrite interaction terms
that can avoid a certain lifeline so that all the trace that are expressed by the rewritten interaction have no conflicts w.r.t. the lifeline.

Indeed, if we suppose that a certain interaction avoids a lifeline, it only means it can express traces that do not involve the lifeline,
and it does necessarily not mean that all the traces it can express have no conflicts w.r.t. the lifeline.

However we can infer a rewritten version of this interaction which expresses exactly all the traces of the original interaction
that have no conflict w.r.t. the lifeline.

I call the inference of this rewritten interaction "pruning", and the rewritten interaction is the "pruned" interaction.

Concretely, for a given interaction "i" and for a given lifeline "l" such that the predicate "(avoids i l)" is held True,
the predicate "(is_prune_of i l i')" states whether or not an interaction "i'" is the pruned version of "i" w.r.t. "l".

This formulation as a predicate in fact corresponds to a certain "prune" function (that will be defined for the third "execution semantics")
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
I state and prove some properties linked to the relationship between pruning and avoiding:
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

Lemma loops_always_prunable (lk:ScheduleKind) (i:Interaction) (l:L) :
  (exists i0' : Interaction, 
     is_prune_of (interaction_loop lk i) l i0'
  ).
Proof.
pose proof (avoids_decidability i l).
destruct H.
- assert (H1:=H). 
  apply (avoids_implies_prunable i l) in H.
  destruct H as (i',H).
  exists (interaction_loop lk i').
  apply prune_loop_select ; assumption.
- exists interaction_empty.
  apply prune_loop_elim ; assumption.
Qed.

(**
**** Properties of pruning w.r.t. the denotational semantics

In the following, I will state some properties of pruning w.r.t. the denotational semantics "sem_de".
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

We will now prove that the semantics of the pruned version is a minimal cut of that of the original.
What we mean to say is that the selection of the subset of the semantics that is operated by prune is minimal in so far
as we only eliminate traces that we need to eliminate so as to satisfy that the pruned version avoids a certain lifeline.
Traces that do not involve the lifeline w.r.t. which the pruning is done must be kept in the semantics.

This is done in the "de_accept_t_and_no_conflict_implies_pruned_de_accept_t" Lemma, which states that if a trace "t"
that has no conflict w.r.t. a certain lifeline "l"
is in the semantics of an interaction "i", then it is also in the semantics of the pruned version of "i" w.r.t. "l".

This Lemma, combined with "prune_kept_de" Lemma state that
the semantics of the pruned version is exactly the subset of the semantics
of the original in which all traces have no conflict with the lifeline against which the pruning is done.

A first Lemma, "de_loop_accept_t_and_no_conflict_implies_nil_or_avoids", is proven so as to faciliate the proof
of "de_accept_t_and_no_conflict_implies_pruned_de_accept_t".
It simply consists of the particular case of loops.
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

(**
A direct application of "de_accept_t_and_no_conflict_implies_pruned_de_accept_t", in the case where the trace "t" is the empty trace "nil"
is formulated in Lemma "de_accept_nil_implies_pruned_de_accept_nil" below.
**)

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
to the execution of an atomic action within an interaction and which results in a "remaining" or "follow-up" interaction
which exactly accepts all the suffixes (tails) of traces of the original that start with the given action
(uniquely determined by its position in the interaction term, even though there may be several occurences of the
same action in the interaction).

In Coq, I formalize this "small-step" or "execution relation" as an inductive predicate "is_next_of" such that,
for any interactions "i" and "i'" and any action "a", the predicate "(is_next_of i a i')" signifies that
action "a" can be immediately executed in "i" and this results in "i" being rewritten into interaction "i'"
that accepts all continuations of the executions of "i" that start with the execution of action "a"
(at a precise position in the term structure of "i").

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
|execute_loop_seq    : forall (a:Action) (i1 i1' i0': Interaction),
                          (is_next_of i1 a i1')
                          -> (is_prune_of (interaction_loop lseq i1) (lifeline a) i0')
                             -> (is_next_of 
                                       (interaction_loop lseq i1)
                                       a
                                       (interaction_seq i0' (interaction_seq i1' (interaction_loop lseq i1)))
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
  destruct H2 as (t0,H3).
  destruct H3 as (tm,H3).
  destruct H3 as (Hi0,H3).
  destruct H3 as (H3,Hmer).
  destruct H3 as (t1,H3).
  destruct H3 as (t2,H3).
  destruct H3 as (Hi1,H3).
  destruct H3 as (H3,Hmer2).
  destruct H3 as (subs,H3).
  destruct H3 as (Hin,Hrep).
  inversion H.
  { symmetry in H0. destruct H0.
    symmetry in H2. destruct H2.
    symmetry in H4. destruct H4.
    destruct H5.
    simpl in Hi0.
    destruct Hi0 as (sub0,Hi0).
    destruct Hi0 as (H0A,H0B).
    simpl.
    exists (sub0 ++ (a::t1)::subs).
    split.
    - intros t3 Ht3.
      apply in_app_or in Ht3.
      destruct Ht3.
      + apply H0A in H0.
        apply (prune_kept_de i1 i1'0 (lifeline a) t3).
        split ; assumption.
      + simpl in H0. destruct H0.
        * destruct H0. apply IHis_next_of. assumption.
        * apply Hin. assumption.
    - apply n_merge_seq_reorder_prop1.
      + apply (n_merge_lseq_sandwich sub0 subs t0 t1 t2 tm) ; assumption.
      + intros. apply (prune_removes_conflicts i1 i1'0).
        * assumption.
        * apply H0A. assumption.
  }
  { destruct H4.
    symmetry in H0. destruct H0.
    symmetry in H3. destruct H3.
    symmetry in H2. destruct H2.
    inversion Hi0. symmetry in H0. destruct H0.
    apply is_weak_seq_nil_prop2 in Hmer. 
    symmetry in Hmer. destruct Hmer.
    simpl.
    exists ((a::t1)::subs).
    split.
    - intros. simpl in H0. destruct H0.
      + destruct H0. apply IHis_next_of.
        assumption.
      + apply Hin. assumption.
    - apply (merge_seq subs (a::t1) t2 (a::t)).
      + intro. discriminate.
      + assumption.
      + apply weak_seq_cons_left. assumption.
  }
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
Proof.
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

**** Preliminaries
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


Lemma n_merge_strict_unicity
  (subs:list Trace) (t1 t2:Trace) :
    ( 
      (n_merge_schedule lstrict subs t1)
      /\(n_merge_schedule lstrict subs t2)
    )->(t1=t2).  
Proof.
dependent induction subs.
- intros. destruct H.
  apply n_merge_schedule_nil_prop2 in H.
  apply n_merge_schedule_nil_prop2 in H0.
  symmetry in H. destruct H.
  symmetry. assumption.
- intros. destruct H.
  inversion H. destruct H1. destruct H2.
  destruct H5.
  inversion H0. destruct H1. destruct H2.
  destruct H7.
  assert (t_rep=t_rep0).
  { apply IHsubs. split ; assumption. }
  destruct H1. reflexivity.
Qed.

Lemma n_merge_strict_strict_operational_characterization
  (t0 t t_merge_remain:Trace) (remain:list Trace) (a:Action) :
(n_merge_schedule lstrict ((a :: t0) :: remain) (a :: t))
-> (n_merge_schedule lstrict remain t_merge_remain)
-> (t = t0 ++ t_merge_remain).
Proof.
intros.
dependent induction remain generalizing t t_merge_remain t0.
- apply n_merge_schedule_nil_prop2 in H0.
  symmetry in H0. destruct H0.
  inversion H.
  apply n_merge_schedule_nil_prop2 in H4.
  rewrite H4. reflexivity.
- inversion H.
  destruct H3. 
  symmetry in H2. destruct H2.
  assert (t_rep=t_merge_remain).
  { apply (n_merge_strict_unicity (a::remain)).
    split ; assumption.
  } 
  destruct H2. reflexivity.
Qed.


Lemma n_merge_schedule_cons_seq_prop (subs:list Trace) (t:Trace) (a:Action):
  (n_merge_schedule lseq subs (a :: t))
  -> (  
        exists (sub1 sub3:list Trace) (t2:Trace),
         (forall t1:Trace, (In t1 sub1) -> (no_conflict t1 a)) /\
         (subs = sub1 ++ (a::t2)::sub3) /\
         (
            ( (t2 <> nil) /\ (n_merge_schedule lseq (sub1 ++ (t2::sub3)) t) )
            \/ ( (t2 = nil) /\ (n_merge_schedule lseq (sub1 ++ sub3) t) )
         )
     ).
Proof.
Admitted.

Lemma n_merge_schedule_cons_par_prop (subs:list Trace) (t:Trace) (a:Action):
  (n_merge_schedule lpar subs (a::t))
  -> (exists (subs':list Trace) (t0:Trace),
        (forall tx:Trace, (In tx ( (a::t0)::subs') ) <-> (In tx subs))
        /\ (n_merge_schedule lpar (t0::subs') t)
     ).
Proof.
Admitted.

Lemma n_merge_schedule_par_dichotomy (sub1 sub2 : list Trace) (t: Trace) :
  (n_merge_schedule lpar (sub1 ++ sub2) t)
  -> (exists (t1 t2:Trace),
       (n_merge_schedule lpar sub1 t1)
       /\ (n_merge_schedule lpar sub2 t2)
       /\ (is_interleaving t1 t2 t)
     ).
Proof.
Admitted.

Lemma n_merge_schedule_seq_dichotomy (sub1 sub2 : list Trace) (t: Trace) :
  (n_merge_schedule lseq (sub1 ++ sub2) t)
  -> (exists (t1 t2:Trace),
       (n_merge_schedule lseq sub1 t1)
       /\ (n_merge_schedule lseq sub2 t2)
       /\ (is_weak_seq t1 t2 t)
     ).
Proof.
Admitted.

(**
**** Proof
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
          + apply (n_merge_strict_strict_operational_characterization t0 t t_merge_remain remain a) ; assumption. 
      }
    }
  + assert (Hr:=Hrep).
    apply (n_merge_schedule_cons_seq_prop subs t a) in Hrep.
    destruct Hrep as (sub1,Hrep).
    destruct Hrep as (sub3,Hrep).
    destruct Hrep as (t2,Hrep).
    destruct Hrep. destruct H0.
    destruct H1.
    { destruct H1.
      assert (In (a::t2) subs).
      { rewrite H0. apply in_or_app. right. simpl. left. reflexivity. }
      apply Hin in H3.
      apply IHi in H3.
      destruct H3 as (i',Hi').
      destruct Hi' as (Hnext,Hi').
      pose proof (loops_always_prunable lseq i (lifeline a)).
      destruct H3 as (i0',H3).
      exists (interaction_seq i0' (interaction_seq i' (interaction_loop lseq i))).
      split.
      { apply execute_loop_seq ; assumption. }
      { apply n_merge_schedule_seq_dichotomy in H2.
        destruct H2 as (t1,H2).
        destruct H2 as (t3,H2).
        destruct H2.
        destruct H4. 
        simpl. exists t1. exists t3.
        split.
        - inversion H3.
          + destruct H10.
            symmetry in H9. destruct H9. symmetry in H7. destruct H7.
            symmetry in H6. destruct H6. simpl. exists sub1.
            split.
            * intros. 
              apply (de_accept_t_and_no_conflict_implies_pruned_de_accept_t i i1' a t0).
              { apply H. assumption. }
              { apply Hin. rewrite H0. apply in_or_app. left. assumption. }
              { assumption. }
            * assumption.
          + destruct H9. 
            symmetry in H7. destruct H7.
            symmetry in H6. destruct H6. symmetry in H8. destruct H8.
            simpl. inversion H2.
            * reflexivity.
            * destruct H11. destruct H12. assert (no_conflict t_first a).
              { apply H. simpl. left. reflexivity. }
              assert (avoids i (lifeline a)).
              { apply (de_accept_t_and_no_conflict_implies_avoids i a t_first).
                - apply Hin. rewrite H0. apply in_or_app. left. simpl. left. reflexivity.
                - assumption.
              }
              contradiction.
        - split.
          + exists t2.
            assert (exists t1 t4 : Trace,
       n_merge_schedule lseq (t2 :: nil) t1 /\
       n_merge_schedule lseq sub3 t4 /\ is_weak_seq t1 t4 t3).
            { apply (n_merge_schedule_seq_dichotomy (t2::nil) sub3 t3).
              simpl. assumption. }
            destruct H6. destruct H6 as (tX,H6). destruct H6. destruct H7.
            apply (n_merge_schedule_single_merge lseq) in H6. destruct H6.
            { exists tX. split.
              - assumption.
              - split.
                + exists sub3. split.
                  * intros. apply Hin. rewrite H0. apply in_or_app.
                    right. simpl. right. assumption.
                  * assumption.
                + assumption.
            }
          + assumption.
      }
    }
    { destruct H1.
      symmetry in H1. destruct H1.
      assert (In (a::nil) subs).
      { rewrite H0. apply in_or_app. right. simpl. left. reflexivity. }
      apply Hin in H1.
      apply IHi in H1.
      destruct H1 as (i',Hi').
      destruct Hi' as (Hnext,Hi').
      pose proof (loops_always_prunable lseq i (lifeline a)).
      destruct H1 as (i0',H1).
      exists (interaction_seq i0' (interaction_seq i' (interaction_loop lseq i))).
      split.
      { apply execute_loop_seq ; assumption. }
      { apply n_merge_schedule_seq_dichotomy in H2.
        destruct H2 as (t1,H2).
        destruct H2 as (t3,H2).
        destruct H2.
        destruct H3. 
        simpl. exists t1. exists t3.
        split.
        - inversion H1.
          + destruct H9.
            symmetry in H5. destruct H5. symmetry in H6. destruct H6.
            symmetry in H8. destruct H8. simpl. exists sub1.
            split.
            * intros. 
              apply (de_accept_t_and_no_conflict_implies_pruned_de_accept_t i i1' a t0).
              { apply H. assumption. }
              { apply Hin. rewrite H0. apply in_or_app. left. assumption. }
              { assumption. }
            * assumption.
          + destruct H8. 
            symmetry in H5. destruct H5.
            symmetry in H6. destruct H6. symmetry in H7. destruct H7.
            simpl. inversion H2.
            * reflexivity.
            * destruct H10. destruct H11. assert (no_conflict t_first a).
              { apply H. simpl. left. reflexivity. }
              assert (avoids i (lifeline a)).
              { apply (de_accept_t_and_no_conflict_implies_avoids i a t_first).
                - apply Hin. rewrite H0. apply in_or_app. left. simpl. left. reflexivity.
                - assumption.
              }
              contradiction.
        - split.
          + exists nil. exists t3.
            split.
            * assumption.
            * split.
              { exists sub3. split.  
                - intros. apply Hin. rewrite H0. apply in_or_app. right. simpl. right. assumption.
                - assumption. }
              { apply weak_seq_nil_left. }
          + assumption. 
      }
    }
  + assert (Hr:=Hrep).
    apply (n_merge_schedule_cons_par_prop subs t a) in Hrep.
    destruct Hrep as (subs',H). destruct H as (t0,H).
    destruct H. assert (In (a::t0) subs).
    { apply H. simpl. left. reflexivity. }
    apply Hin in H1. apply IHi in H1.
    destruct H1 as (i',H1). destruct H1.
    exists (interaction_par i' (interaction_loop lpar i)).
    split.
    * apply execute_loop_par. assumption.
    * simpl. exists t0. 
      assert (exists t1 t2 : Trace,
       n_merge_schedule lpar (t0 :: nil) t1 /\
       n_merge_schedule lpar subs' t2 /\ is_interleaving t1 t2 t).
      { apply (n_merge_schedule_par_dichotomy (t0::nil) subs' t). simpl. assumption. }
      destruct H3. destruct H3 as (t2,H3).
      destruct H3. destruct H4.
      apply (n_merge_schedule_single_merge lpar) in H3. destruct H3.
      exists t2.
      split.
      { assumption. }
      { split.
        - exists subs'. split.
          + intros. apply Hin.
            apply H. simpl. right. assumption.
          + assumption.
        - assumption.
      }
Qed.

(**
We can finally prove the inclusion of "sem_de" into "sem_op".
**)

Theorem de_implies_op (i : Interaction) (t : Trace) :
  (sem_de i t) -> (sem_op i t).
Proof.
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
** Equivalence of "sem_de" and "sem_op"

Finally we have proven the equivalence of both semantics,
as stated by the "sem_equivalence" Theorem.

**)
  
Theorem sem_equivalence_de_op (i : Interaction) (t : Trace) :
  (sem_op i t) <-> (sem_de i t).
Proof.
split.
- apply op_implies_de.
- apply de_implies_op.
Qed.

(**
** Execution Semantics

We will now define an algorithmization of the operational semantics.

*** Versions of the utility predicates using booleans

At first, I will define:
- "terminates_bool" which is a new version of the "terminates" predicate that returns a boolean rather than defines a Prop object
- "avoids_bool" which is a new version of the "avoids" predicate that returns a boolean rather than defines a Prop object

Of course, we then prove, on Lemmas "terminates_eq" and "avoids_eq" that both those definitions are equivalent.
**)


Fixpoint terminates_bool (i : Interaction) : bool :=
  match i with
    | interaction_empty => true
    | (interaction_act a) => false
    | (interaction_loop lk i1) => true
    | (interaction_alt i1 i2) => orb (terminates_bool i1) (terminates_bool i2)
    | (interaction_par i1 i2) => andb (terminates_bool i1) (terminates_bool i2)
    | (interaction_strict i1 i2) => andb (terminates_bool i1) (terminates_bool i2)
    | (interaction_seq i1 i2) => andb (terminates_bool i1) (terminates_bool i2)
  end.

Lemma terminates_eq :
  forall (i:Interaction),
     (terminates i) <-> (terminates_bool i = true).
Proof.
intros.
split ; intros.
{ dependent induction i.
- simpl. reflexivity.
- simpl in H. contradiction.
- simpl in H. destruct H.
  apply IHi1 in H.
  apply IHi2 in H0.
  simpl. rewrite H. rewrite H0.
  simpl. reflexivity.
- simpl in H. destruct H.
  apply IHi1 in H.
  apply IHi2 in H0.
  simpl. rewrite H. rewrite H0.
  simpl. reflexivity.
- simpl in H. destruct H.
  apply IHi1 in H.
  apply IHi2 in H0.
  simpl. rewrite H. rewrite H0.
  simpl. reflexivity.
- simpl in H. destruct H.
  + apply IHi1 in H.
    simpl. rewrite H. 
    simpl. reflexivity.
  + apply IHi2 in H.
    simpl. rewrite H.
    apply orb_true_iff.
    right. reflexivity.
- simpl. reflexivity.
}
{ dependent induction i.
- simpl. trivial.
- simpl in H. discriminate.
- simpl in H. 
  apply andb_true_iff in H. destruct H.
  apply IHi1 in H.
  apply IHi2 in H0.
  simpl. split ; assumption.
- simpl in H. 
  apply andb_true_iff in H. destruct H.
  apply IHi1 in H.
  apply IHi2 in H0.
  simpl. split ; assumption.
- simpl in H. 
  apply andb_true_iff in H. destruct H.
  apply IHi1 in H.
  apply IHi2 in H0.
  simpl. split ; assumption.
- simpl in H. 
  apply orb_true_iff in H. destruct H.
  + apply IHi1 in H.
    simpl.
    left. assumption.
  + apply IHi2 in H.
    simpl.
    right. assumption.
- simpl. trivial.
}
Qed.

Fixpoint avoids_bool
        (i : Interaction)
        (l : L)
        : bool :=
  match i with
    | interaction_empty => true
    | (interaction_act a) => negb (Fin.eqb (lifeline a) l)
    | (interaction_loop lk i1) => true
    | (interaction_alt i1 i2) => orb (avoids_bool i1 l) (avoids_bool i2 l)
    | (interaction_par i1 i2) => andb (avoids_bool i1 l) (avoids_bool i2 l)
    | (interaction_strict i1 i2) => andb (avoids_bool i1 l) (avoids_bool i2 l)
    | (interaction_seq i1 i2) => andb (avoids_bool i1 l) (avoids_bool i2 l)
  end.

Lemma avoids_eq :
  forall (i:Interaction) (l:L),
     (avoids i l) <-> (avoids_bool i l = true).
Proof.
intros.
split ; intros.
{ dependent induction i.
- simpl. reflexivity.
- simpl in H. simpl.
  apply negb_true_iff. 
  apply L_neqb.
  assumption.
- simpl in H. destruct H.
  apply IHi1 in H.
  apply IHi2 in H0.
  simpl. rewrite H. rewrite H0.
  simpl. reflexivity.
- simpl in H. destruct H.
  apply IHi1 in H.
  apply IHi2 in H0.
  simpl. rewrite H. rewrite H0.
  simpl. reflexivity.
- simpl in H. destruct H.
  apply IHi1 in H.
  apply IHi2 in H0.
  simpl. rewrite H. rewrite H0.
  simpl. reflexivity.
- simpl in H. destruct H.
  + apply IHi1 in H.
    simpl. rewrite H. 
    simpl. reflexivity.
  + apply IHi2 in H.
    simpl. rewrite H.
    apply orb_true_iff.
    right. reflexivity.
- simpl. reflexivity.
}
{ dependent induction i.
- simpl. trivial.
- simpl in H.
  apply negb_true_iff in H.
  simpl. apply L_neqb.
  assumption.
- simpl in H. 
  apply andb_true_iff in H. destruct H.
  apply IHi1 in H.
  apply IHi2 in H0.
  simpl. split ; assumption.
- simpl in H. 
  apply andb_true_iff in H. destruct H.
  apply IHi1 in H.
  apply IHi2 in H0.
  simpl. split ; assumption.
- simpl in H. 
  apply andb_true_iff in H. destruct H.
  apply IHi1 in H.
  apply IHi2 in H0.
  simpl. split ; assumption.
- simpl in H. 
  apply orb_true_iff in H. destruct H.
  + apply IHi1 in H.
    simpl.
    left. assumption.
  + apply IHi2 in H.
    simpl.
    right. assumption.
- simpl. trivial.
}
Qed.

(**
In addition to "avoids_eq", we also state and prove "avoids_neq" below.
**)

Lemma avoids_neq :
  forall (i:Interaction) (l:L),
     (not (avoids i l)) <-> (avoids_bool i l = false).
Proof.
intros.
split ; intros.
{ dependent induction i.
- simpl in H. contradiction.
- simpl in H. simpl.
  apply negb_false_iff.
  apply Fin.eqb_eq.
  apply L_not_neq.
  assumption.
- simpl in H.
  simpl. apply andb_false_iff.
  pose proof (avoids_decidability i1 l).
  destruct H0.
  + right. apply IHi2.
    pose proof (avoids_decidability i2 l).
    destruct H1.
    * unfold not in H.
      exfalso.
      apply H. split ; assumption.
    * assumption.
  + left. apply IHi1. assumption.
- simpl in H.
  simpl. apply andb_false_iff.
  pose proof (avoids_decidability i1 l).
  destruct H0.
  + right. apply IHi2.
    pose proof (avoids_decidability i2 l).
    destruct H1.
    * unfold not in H.
      exfalso.
      apply H. split ; assumption.
    * assumption.
  + left. apply IHi1. assumption.
- simpl in H.
  simpl. apply andb_false_iff.
  pose proof (avoids_decidability i1 l).
  destruct H0.
  + right. apply IHi2.
    pose proof (avoids_decidability i2 l).
    destruct H1.
    * unfold not in H.
      exfalso.
      apply H. split ; assumption.
    * assumption.
  + left. apply IHi1. assumption.
- simpl in H. unfold not in H.
  simpl. apply orb_false_iff.
  pose proof (avoids_decidability i1 l).
  destruct H0.
  + exfalso. apply H.
    left. assumption.
  + pose proof (avoids_decidability i2 l).
    destruct H1.
    * exfalso.
      apply H. 
      right. assumption.
    * split.
      { apply IHi1. assumption. }
      { apply IHi2. assumption. }
- simpl in H. contradiction.
}
{ dependent induction i.
- simpl in H. discriminate.
- simpl in H.
  apply negb_false_iff in H.
  apply Fin.eqb_eq in H.
  destruct H.
  simpl. intro. contradiction.
- simpl in H. 
  apply andb_false_iff in H. destruct H.
  + simpl. intro. destruct H0. apply IHi1 in H.
    contradiction.
  + simpl. intro. destruct H0. apply IHi2 in H.
    contradiction.
- simpl in H. 
  apply andb_false_iff in H. destruct H.
  + simpl. intro. destruct H0. apply IHi1 in H.
    contradiction.
  + simpl. intro. destruct H0. apply IHi2 in H.
    contradiction.
- simpl in H. 
  apply andb_false_iff in H. destruct H.
  + simpl. intro. destruct H0. apply IHi1 in H.
    contradiction.
  + simpl. intro. destruct H0. apply IHi2 in H.
    contradiction.
- simpl in H. 
  apply orb_false_iff in H. destruct H.
  apply IHi1 in H. apply IHi2 in H0.
  simpl. intro.
  destruct H1 ; contradiction.
- simpl in H. discriminate.
}
Qed.

(**
*** Determinization of the "is_prune_of" predicate into a "prune" fixpoint

If a precondition (avoids i l) is met on an interaction "i" and lifeline "l", then, the (is_prune_of i l _) function satisfies some interesting properties,
which are the existence of an interaction "i'" such that (is_prune_of i l i') and the unicity of this "i'" interaction.

As a result, in this context, the predicate corresponds to a specific
"prune" function that can be defined as a Fixpoint.

We define "prune" as a Fixpoint below. Let us notice that we do not specify the precondition that the input interaction "i"
must avoid the input lifeline "l".
This precondition will play a role when we will characterize this function, and is not included in its definition.
**)

Fixpoint prune
        (i : Interaction)
        (l : L)
        : Interaction :=
  match i with
    | interaction_empty => interaction_empty
    | (interaction_act a) => (interaction_act a)
    | (interaction_loop lk i1) => match (avoids_bool i1 l) with
                                  | true => interaction_loop lk (prune i1 l)
                                  | false => interaction_empty
                                  end
    | (interaction_alt i1 i2) => match (avoids_bool i1 l) with
                                  | true => match (avoids_bool i2 l) with
                                             | true => interaction_alt
                                                            (prune i1 l)
                                                            (prune i2 l)
                                             | false => prune i1 l
                                             end
                                  | false => prune i2 l
                                  end
    | (interaction_par i1 i2) => interaction_par (prune i1 l) (prune i2 l)
    | (interaction_strict i1 i2) => interaction_strict (prune i1 l) (prune i2 l)
    | (interaction_seq i1 i2) => interaction_seq (prune i1 l) (prune i2 l)
  end.

(**
As explained earlier, we will now characterize this "prune" function w.r.t. the "is_prune_of" predicate.
This characterisation correspond to the two following Lemmas:
- "prune_implication_1", which states that for any interactions "i" and "i'" and any lifeline "l", we have (is_prune_of i l i') -> (i' = (prune i l))
- "prune_implication_2", which states that, given the precondition "avoids i l", then we have (is_prune_of i l (prune i l))
**)

Lemma prune_implication_1 :
  forall (i i':Interaction) (l:L),
     (is_prune_of i l i') -> (prune i l = i').
Proof.
intros.
dependent induction i.
- simpl. inversion H. reflexivity.
- simpl. inversion H. reflexivity.
- simpl. inversion H.
  destruct H4. 
  apply IHi1 in H2. destruct H2.
  apply IHi2 in H5. destruct H5.
  reflexivity.
- simpl. inversion H.
  destruct H4. 
  apply IHi1 in H2. destruct H2.
  apply IHi2 in H5. destruct H5.
  reflexivity.
- simpl. inversion H.
  destruct H4. 
  apply IHi1 in H2. destruct H2.
  apply IHi2 in H5. destruct H5.
  reflexivity.
- simpl. inversion H.
  + apply avoids_eq in H2.
    rewrite H2.
    apply avoids_eq in H3.
    rewrite H3.
    apply IHi1 in H4.
    destruct H4.
    apply IHi2 in H7.
    destruct H7.
    reflexivity.
  + apply avoids_neq in H2.
    rewrite H2.
    apply avoids_eq in H3.
    rewrite H3.
    apply IHi1 in H6. assumption.
  + apply avoids_neq in H2.
    rewrite H2.
    apply IHi2 in H6. assumption.
- simpl. inversion H.
  + apply avoids_eq in H2.
    rewrite H2.
    apply IHi in H5. rewrite H5.
    reflexivity.
  + apply avoids_neq in H4.
    rewrite H4. reflexivity.
Qed.

Lemma prune_implication_2 :
  forall (i i':Interaction) (l:L),
     (avoids i l)
     -> (prune i l = i')
     -> (is_prune_of i l i').
Proof.
intros.
dependent induction i.
- simpl in H0. destruct H0.
  apply prune_empty.
- simpl in H0. destruct H0.
  apply prune_act.
  simpl in H. intro.
  destruct H0. contradiction.
- simpl in H0. destruct H0.
  simpl in H. destruct H.
  apply prune_strict.
  + apply IHi1.
    * assumption.
    * reflexivity.
  + apply IHi2.
    * assumption.
    * reflexivity.
- simpl in H0. destruct H0.
  simpl in H. destruct H.
  apply prune_seq.
  + apply IHi1.
    * assumption.
    * reflexivity.
  + apply IHi2.
    * assumption.
    * reflexivity.
- simpl in H0. destruct H0.
  simpl in H. destruct H.
  apply prune_par.
  + apply IHi1.
    * assumption.
    * reflexivity.
  + apply IHi2.
    * assumption.
    * reflexivity.
- simpl in H0.
  simpl in H.
  destruct H.
  + assert (H':=H).
    apply avoids_eq in H'.
    symmetry in H'. destruct H'.
    remember (avoids_bool i2 l) as AV2.
    destruct AV2.
    { symmetry in HeqAV2. apply avoids_eq in HeqAV2.
      destruct H0. apply prune_alt_both.
      - assumption.
      - assumption.
      - apply IHi1.
        + assumption.
        + reflexivity.
      - apply IHi2.
        + assumption.
        + reflexivity.
    }
    { symmetry in HeqAV2. apply avoids_neq in HeqAV2.
      destruct H0. apply prune_alt_left.
      - assumption. 
      - assumption. 
      - apply IHi1.
        + assumption.
        + reflexivity.
    }
  + assert (H':=H).
    apply avoids_eq in H'.
    symmetry in H'. destruct H'.
    remember (avoids_bool i1 l) as AV1.
    destruct AV1.
    { symmetry in HeqAV1. apply avoids_eq in HeqAV1.
      destruct H0. apply prune_alt_both.
      - assumption.
      - assumption.
      - apply IHi1.
        + assumption.
        + reflexivity.
      - apply IHi2.
        + assumption.
        + reflexivity.
    }
    { symmetry in HeqAV1. apply avoids_neq in HeqAV1.
      destruct H0. apply prune_alt_right.
      - assumption. 
      - assumption. 
      - apply IHi2.
        + assumption.
        + reflexivity.
    }
- simpl in H0.
  remember (avoids_bool i l) as AV.
  destruct AV.
  { symmetry in HeqAV. apply avoids_eq in HeqAV.
    destruct H0.
    apply prune_loop_select.
    - assumption.
    - apply IHi.
      + assumption.
      + reflexivity.
  }
  { symmetry in HeqAV. apply avoids_neq in HeqAV.
    destruct H0.
    apply prune_loop_elim.
    assumption.
  }
Qed.

(**
*** Managing positions with the Dewey Decimal Notation

Interaction terms have a structure which is that of a binary tree.
Indeed, constructors used to construct interactions have an arity of at most 2.
As a result, we can navigate within interaction terms using a position system in {1,2}^* akin to that of the Dewey Decimal Notation.
We define a "Position" inductive type which form words on {1,2}^* with:
- "epsilon" being the empty position
- "left" serving as the "1" letter
- "right" serving as the "2" letter
**)

Inductive Position : Set :=
  |epsilon:Position
  |left:Position->Position
  |right:Position->Position.

(**
Because there can be several instances of the same action within an interaction term, we will use their positions within the interaction
to designate them unambiguously.

The principle of the execution semantics is to decorrelate, within the operational semantics, a process which is that of determining which actions can be executed,
and a process which is that of computing which is the follow-up interaction after the execution of a specific action.

Given that it is both the nature of the action and its specific position within the interaction term that determines which will be the follow-up interaction
to its execution, we have to consider the positions of actions for both those processes.

*** Determining the frontier of execution

The frontier of execution of an interaction is the set of the positions of the actions that can be immediately executed within it.
We define the frontier using an inductive predicate "is_in_frontier" such that for any interaction "i", any position "p" and any action "a" we have
(is_in_frontier i p a) if action "a" is at position "p" within "i" and can be immediately executed.
**)

Inductive is_in_frontier : Interaction -> Position -> Action -> Prop :=
 | front_act          : forall (a:Action),
                          (is_in_frontier (interaction_act a) epsilon a)
 | front_loop         : forall (i:Interaction) (sk:ScheduleKind) (p:Position) (a:Action),
                          (is_in_frontier i p a) 
                          -> (is_in_frontier (interaction_loop sk i) (left p) a)
 | front_strict_left  : forall (i1 i2:Interaction) (p1:Position) (a:Action),
                          (is_in_frontier i1 p1 a)
                          -> (is_in_frontier (interaction_strict i1 i2) (left p1) a)
 | front_strict_right : forall (i1 i2:Interaction) (p2:Position) (a:Action),
                          (is_in_frontier i2 p2 a)
                          -> (terminates i1)
                          -> (is_in_frontier (interaction_strict i1 i2) (right p2) a)
 | front_seq_left     : forall (i1 i2:Interaction) (p1:Position) (a:Action),
                          (is_in_frontier i1 p1 a)
                          -> (is_in_frontier (interaction_seq i1 i2) (left p1) a)
 | front_seq_right    : forall (i1 i2:Interaction) (p2:Position) (a:Action),
                          (is_in_frontier i2 p2 a)
                          -> (avoids i1 (lifeline a))
                          -> (is_in_frontier (interaction_seq i1 i2) (right p2) a)
 | front_par_left     : forall (i1 i2:Interaction) (p1:Position) (a:Action),
                          (is_in_frontier i1 p1 a)
                          -> (is_in_frontier (interaction_par i1 i2) (left p1) a)
 | front_par_right     : forall (i1 i2:Interaction) (p2:Position) (a:Action),
                          (is_in_frontier i2 p2 a)
                          -> (is_in_frontier (interaction_par i1 i2) (right p2) a)
 | front_alt_left     : forall (i1 i2:Interaction) (p1:Position) (a:Action),
                          (is_in_frontier i1 p1 a)
                          -> (is_in_frontier (interaction_alt i1 i2) (left p1) a)
 | front_alt_right     : forall (i1 i2:Interaction) (p2:Position) (a:Action),
                          (is_in_frontier i2 p2 a)
                          -> (is_in_frontier (interaction_alt i1 i2) (right p2) a).

(**
*** Determinization of the "is_next_of" predicate into an "execute" fixpoint

In a similar manner to what we did for the "is_prune_of" predicate with the "prune" function,
we will now define an "execute" Fixpoint which corresponds to the execution relation "is_next_of".

If a precondition (is_in_frontier i p a) is met on an interaction "i", a position "p" and an action "a",
then the (is_next_of i a _) function satisfies an existence property which is that there exists an "i'" such that (is_next_of i a i').
We do not however have a unicity property given that the "is_next_of" predicate do not take into consideration the position of the action "a" that is executed.

In any case, we define an "execute" function as a Fixpoint below. 
Let us notice that we do not specify any precondition on the position "p" w.r.t. the interaction "i".
This precondition will play a role when we will characterize this function, and is not included in its definition.
**)

Fixpoint execute (i : Interaction) 
                         (p : Position)
                         (l:L)
            : Interaction :=
  match p with 
        | epsilon => interaction_empty
        | (left p1) => match i with
                  | (interaction_loop lk i1) => match lk with
                                      | lstrict => interaction_strict (execute i1 p1 l) i
                                      | lseq => interaction_seq (prune i l)
                                                                (interaction_seq (execute i1 p1 l) i)
                                      | lpar => interaction_par (execute i1 p1 l) i
                                    end
                  | (interaction_alt i1 i2)    => execute i1 p1 l
                  | (interaction_strict i1 i2) => interaction_strict (execute i1 p1 l) i2
                  | (interaction_seq i1 i2)    => interaction_seq (execute i1 p1 l) i2
                  | (interaction_par i1 i2)    => interaction_par (execute i1 p1 l) i2
                  | _ => interaction_empty (* should never be reached / how to force an undef here ? *)
                 end
        | (right p2) => match i with
                  | (interaction_alt i1 i2)    => execute i2 p2 l
                  | (interaction_strict i1 i2) => execute i2 p2 l
                  | (interaction_seq i1 i2)    => interaction_seq (prune i1 l) (execute i2 p2 l)
                  | (interaction_par i1 i2)    => interaction_par i1 (execute i2 p2 l)
                  | _ => interaction_empty (* should never be reached / how to force an undef here ? *)
                 end
      end.

(**
As explained earlier, we will now characterize this "execute" function w.r.t. the "is_next_of" predicate.
This characterisation correspond to the two following Lemmas:
- "execute_implication_1", which states that for any interactions "i" and "i'" and any action "a", if (is_next_of i a i') then there exists a position "p" in the frontier of "i" hosting that action "a" and we have "i' = execute i p (lifeline a)". 
- "execute_implication_2", which states that, given the precondition "(is_in_frontier i p a)", then we have (is_next_of i a (execute i p (lifeline a)))
**)

Lemma execute_implication_1 :
  forall (i i':Interaction) (a:Action),
     (is_next_of i a i') 
     -> (exists p:Position, 
          (is_in_frontier i p a)
          /\ (execute i p (lifeline a) = i')
        ).
Proof.
intros.
dependent induction i.
- inversion H.
- inversion H. destruct H2.
  destruct H0. symmetry in H1. destruct H1.
  exists epsilon.
  split.
  + apply front_act.
  + simpl. reflexivity.
- inversion H.
  { apply IHi1 in H4.
    destruct H4 as (p1,H4).
    destruct H4.
    exists (left p1).
    simpl. split.
    - apply front_strict_left. assumption.
    - destruct H5. reflexivity.
  }
  { apply IHi2 in H2.
    destruct H2 as (p2,H2).
    destruct H2.
    exists (right p2).
    simpl. split.
    - apply front_strict_right ; assumption.
    - destruct H6. reflexivity.
  }
- inversion H.
  { apply IHi1 in H4.
    destruct H4 as (p1,H4).
    destruct H4.
    exists (left p1).
    simpl. split.
    - apply front_seq_left. assumption.
    - destruct H5. reflexivity.
  }
  { apply IHi2 in H2.
    destruct H2 as (p2,H2).
    destruct H2.
    exists (right p2).
    simpl. split.
    - apply front_seq_right.
      + assumption.
      + apply prunable_implies_avoids.
        exists i1'. assumption.
    - destruct H6.
      apply prune_implication_1 in H5.
      destruct H5. reflexivity.
  }
- inversion H.
  { apply IHi1 in H4.
    destruct H4 as (p1,H4).
    destruct H4.
    exists (left p1).
    simpl. split.
    - apply front_par_left. assumption.
    - destruct H5. reflexivity.
  }
  { apply IHi2 in H4.
    destruct H4 as (p2,H4).
    destruct H4.
    exists (right p2).
    simpl. split.
    - apply front_par_right ; assumption.
    - destruct H5. reflexivity.
  }
- inversion H.
  { apply IHi1 in H4.
    destruct H4 as (p1,H4).
    destruct H4.
    exists (left p1).
    simpl. split.
    - apply front_alt_left. assumption.
    - destruct H5. reflexivity.
  }
  { apply IHi2 in H4.
    destruct H4 as (p2,H4).
    destruct H4.
    exists (right p2).
    simpl. split.
    - apply front_alt_right ; assumption.
    - destruct H5. reflexivity.
  }
- inversion H.
  + destruct H0. destruct H2. symmetry in H1. destruct H1.
    apply IHi in H4.
    destruct H4 as (p1,H4).
    destruct H4.
    exists (left p1).
    simpl. split.
    * apply front_loop. assumption.
    * destruct H1. reflexivity.
  + destruct H0. symmetry in H1. destruct H1.
    symmetry in H3. destruct H3.
    apply IHi in H2.
    destruct H2 as (p1,H2).
    destruct H2.
    exists (left p1).
    simpl. split.
    * apply front_loop. assumption.
    * destruct H1. inversion H5.
      { symmetry in H1. destruct H1.
        symmetry in H2. destruct H2.
        symmetry in H6. destruct H6.
        destruct H7.
        apply avoids_eq in H3. 
        symmetry in H3. destruct H3.
        apply prune_implication_1 in H8.
        destruct H8. reflexivity.
      } 
      { symmetry in H1. destruct H1.
        symmetry in H3. destruct H3.
        symmetry in H2. destruct H2.
        destruct H6.
        apply avoids_neq in H7. 
        symmetry in H7. destruct H7.
        reflexivity.
      }
  + destruct H0. destruct H2. symmetry in H1. destruct H1.
    apply IHi in H4.
    destruct H4 as (p1,H4).
    destruct H4.
    exists (left p1).
    simpl. split.
    * apply front_loop. assumption.
    * destruct H1. reflexivity.
Qed.

Lemma execute_implication_2 :
  forall (i:Interaction) (a:Action) (p:Position),
     (is_in_frontier i p a)
     -> (is_next_of i a (execute i p (lifeline a)) ).
Proof.
intros.
dependent induction i.
- inversion H.
- inversion H. simpl.
  apply execute_at_leaf.
- inversion H.
  + apply IHi1 in H4. apply execute_left_strict.
    assumption.
  + apply IHi2 in H2. apply execute_right_strict.
    * simpl. assumption.
    * assumption.
- inversion H.
  + apply IHi1 in H4. apply execute_left_seq.
    assumption.
  + apply IHi2 in H2. apply execute_right_seq.
    * simpl. assumption.
    * apply prune_implication_2.
      { assumption. }
      { reflexivity. }
- inversion H.
  + apply IHi1 in H4. apply execute_left_par.
    assumption.
  + apply IHi2 in H4. apply execute_right_par.
    assumption.
- inversion H.
  + apply IHi1 in H4. apply execute_left_alt.
    assumption.
  + apply IHi2 in H4. apply execute_right_alt.
    assumption.
- inversion H. destruct H0.
  destruct H1.
  symmetry in H2. destruct H2.
  symmetry in H3. destruct H3.
  destruct sk.
  + apply IHi in H4.
    apply execute_loop_strict. assumption.
  + apply IHi in H4. simpl.
    pose proof (avoids_decidability i (lifeline a)).
    destruct H0.
    { apply execute_loop_seq.
      - assumption.
      - assert (Ha:=H0). apply avoids_eq in H0. symmetry in H0. destruct H0.
        apply prune_loop_select.
        * assumption.
        * apply prune_implication_2.
          assumption. reflexivity.
    }
    { apply execute_loop_seq.
      - assumption.
      - assert (Ha:=H0). apply avoids_neq in H0. symmetry in H0. destruct H0.
        apply prune_loop_elim.
        assumption.
    }
  + apply IHi in H4.
    apply execute_loop_par. assumption.
Qed.

(**
*** Definition of the Execution Semantics

We can now define the execution semantics "sem_ex" below. 
Its definition is quite similar to that of the operational semantics, 
except that we use the definition of the frontier and of the execution.
**)

Inductive sem_ex : Interaction -> Trace -> Prop :=
 | sem_ex_empty : forall (i :Interaction),
                      (is_true (terminates_bool i))
                      -> (sem_ex i nil)
 | sem_ex_event : forall (i:Interaction) (p:Position) (a:Action) (t:Trace),
                      (is_in_frontier i p a)
                      -> (sem_ex (execute i p (lifeline a)) t)
                      -> (sem_ex i (cons a t) ).

(**
** Equivalence of "sem_op" and "sem_ex"

In the following we prove the equivalence of the execution semantics and the operational semantics.

**)


Theorem ex_implies_op (i : Interaction) (t : Trace) :
  (sem_ex i t) -> (sem_op i t).
Proof.
intros.
dependent induction t generalizing i.
- inversion H.
  unfold is_true in H0.
  apply terminates_eq in H0.
  apply sem_op_empty.
  assumption.
- inversion H.
  apply (sem_op_event i (execute i p (lifeline a)) a t).
  + apply execute_implication_2. assumption.
  + apply IHt. assumption.
Qed.

Theorem op_implies_ex (i : Interaction) (t : Trace) :
  (sem_op i t) -> (sem_ex i t).
Proof.
intros.
dependent induction t generalizing i.
- inversion H.
  apply terminates_eq in H0.
  apply sem_ex_empty.
  unfold is_true.
  assumption.
- inversion H.
  apply execute_implication_1 in H3.
  destruct H3 as (p,H3).
  destruct H3.
  apply (sem_ex_event i p a t).
  + assumption.
  + apply IHt. destruct H5. assumption.
Qed.

Theorem sem_equivalence_op_ex (i : Interaction) (t : Trace) :
  (sem_ex i t) <-> (sem_op i t).
Proof.
split.
- apply ex_implies_op.
- apply op_implies_ex.
Qed.

(**
* Conclusion

Let us conclude by expliciting that all three semantics are indeed equivalent.
**)

Theorem sem_equivalence_1 (i : Interaction) (t : Trace) :
  (sem_de i t) <-> (sem_op i t).
Proof.
symmetry.
apply sem_equivalence_de_op.
Qed.

Theorem sem_equivalence_2 (i : Interaction) (t : Trace) :
  (sem_op i t) <-> (sem_ex i t).
Proof.
symmetry.
apply sem_equivalence_op_ex.
Qed.

Theorem sem_equivalence_3 (i : Interaction) (t : Trace) :
  (sem_de i t) <-> (sem_ex i t).
Proof.
split ; intros.
- apply sem_equivalence_2. 
  apply sem_equivalence_1.
  assumption.
- apply sem_equivalence_1.
  apply sem_equivalence_2.
  assumption.
Qed.







