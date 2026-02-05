# Angle

A reference implementation of a core version of the Angle query language used in [Glean](https://glean.software/)

This implementation supports recursion and semi-naive evaluation.

The semantics implemented in this repo most closely resembles a [denotational semantics based on sets](SetSemantics.md).

There is also [a proof-theoretic semantics for Angle](ProofSemantics.md), though it doesn't handle the constructs for sets.
