# What is this all about?

# Introduction to SSP

# Classic Reductions vs SSP-style reductions

# Example 1: KEM-DEM
Three hops similar to Paper or check Jonothon Katz book in classic reduction style.

# Code Equivalence
Why is automating checking code equivalence steps useful?
When the process is manual, it's very difficult and error-prone and with a tiny check to any code of any package, it should be revisited. Especially for big proofs and games.

Obligations of code equivalence:
If left and right games are started on the same random strings,
For each oracle exposed by the games, we have to prove on the same input given to the oracle
1. Both games output the same value(s) if they do not abort. (same-output given no-abort)
2. Both games abort. (equal-aborts)

Explain invariants:

# Install SSBee and cvc5

# Introduction to SSBee

# SSBee games (compositions) and packages vs SSP games and packages
Proof parameters/constants are free and arbitrary values and can be thought as if an universal quantifier quantifiers over them and the rest of proof.

# Where is the adversary in SSBee?

# Revisit KEM-DEM in SSBee
Notice the composition of KEM and Key package (although they are different depending on b parameter)
Notice how we bring the randomness into the scene

# Invariant Argument
Invariants hold in beginning. (i.e. invariants applied to left and right initial game states are satisfiable and has a model in SMT language)
Assuming the invariants hold on old game states and the games do not abort, invariants should be preserved and hold on new game states.
Now, we can safely assume invariants hold on old game states before the oracle calls.

# How does SSBee work internally?
Code transformations to be suitable for SMT code (let and ite syntax for total functions in SMT-LIB)
Package and game states
Oracle codes
equivalence proof obligations

# SSBee technicality
Remember ssp.toml in the root of project and proofs, games, packages directories.
VSCode extension for code highlighting and later on parsing and semantic highlighting and with the helper of language server and ssbee backend, there could be live errors shown on screen and proof steps checked on demand. (very much like lean)
File extensions (Games are compositions of packages so .comp.ssp)
Useful commands are : 
1. cargo run -p ssbee prove -t (t is for SMT transcript) -p (p is for prover backend, currently only cvc5, we need to work on Z3) : main command for running the whoel tool chain to type check, translating to SMT, and callign cvc5 step by step for each lemma and proof goal
2. cargo run -p ssbee latex : latex export with diagrams for games

# TLS 1.3 Key Schedule Security

Which Lemmata have the potential of formal verification?
Code equivalence of K -> L and Key -> Log packages (This is a good candidate for the workshop)
Codependence lemma
Lemma C.2
Lemma C.5
Injectivity Lemma
Code equivalence in the assumptions (appendix E)

# Example 2: SimplifiedMappingIntroductionLemma (Lemma C.2) from TLS 1.3 Key Schedule Security

# Challenges in TLS and SSBee and Possible Connections to Program Verification