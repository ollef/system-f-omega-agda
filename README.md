# System Fω in Agda

This repository contains a formalization of the higher-order polymorphic lambda calculus known as System Fω, plus extensions, in Agda.

In summary, there's a bit of syntax, some semantics, typing, kinding, type soundness (progress and preservation), and a bunch of tedious proofs about substitutions.

The (admittedly admissible) extensions are: projectible products, matchable sums, and unpackable existential types.

It's been checked with Agda 2.7.0.1. Because I'm a masochist (or machochist?), this thing does not use the standard library, though the substitution module is partly stolen therefrom.

---

© 2025 Olle Fredriksson
