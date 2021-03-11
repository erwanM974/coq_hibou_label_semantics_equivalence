# Coq proof for the equivalence of semantics defined on an interaction language

This repository hosts a proof written in the Gallina language.
We use the Coq automated theorem prover to prove the 
equivalence of three different semantics defined on a formal language of "interactions".

"Interactions" model the behavior of distributed systems and can be considered to be a
formalisation of UML Sequence Diagrams.

A web page (generated with coqdoc) presenting the proof can be accessed [here](https://erwanm974.github.io/coq_hibou_label_semantics_equivalence/).

A prototype tool, which makes use of one of the semantics
to implements various formal verification techniques is available on [this repository](https://github.com/erwanM974/hibou_label).