# Coq proof for the correctness of the operational semantics used in HIBOU LABEL

This repository hosts a proof written in the Gallina language.
We use the Coq automated theorem prover to prove the 
equivalence of an operational-style (small-step) semantics
with regards to a denotational-style semantics for a formal language of "interactions".

"Interactions" model the behavior of distributed systems and can be considered to be a
formalisation of UML Sequence Diagrams.

A web page (generated with coqdoc) presenting the proof can be accessed [here](https://erwanm974.github.io/coq_hibou_label_semantics_equivalence/).

A prototype tool, which makes use of the operational-style semantics
to implements various model-based testing features is available on [this repository](https://github.com/erwanM974/hibou_label).