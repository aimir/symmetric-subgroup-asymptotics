/-
Copyright (c) 2026 Kenta.
Released under Apache-2.0 (provenance/CFSG/Apache-2.0.txt).
Adapted from KitaKen1/finite-simple-groups-lean at 7f09e33a9ceef6b59ce03e34cd4f0558c763e325.
Changes: publication import paths and isolated original-model namespace.
Original generators, certificate data, proof bodies and scoped proof settings are retained.
This actual permutation model is not identified here with the pinned presentation model.
Authors: Kenta
AI usage: Developed with assistance from Claude Code (Fable 5, 1M context,
high reasoning).
-/
import Mathlib.GroupTheory.Perm.Fin
import Mathlib.GroupTheory.Subgroup.Simple

/-!
# Basic namespace for the M23 experiment

This project formalizes the fourth sporadic group target: Mathieu's group
`M23`, represented as a subgroup of `Equiv.Perm (Fin 23)`.

The public API is intended to live in the namespace `Sporadic`.
-/

namespace CFSG.Certificates.Mathieu23

/-- The ambient permutation group for the degree-23 representation. -/
abbrev Perm23 : Type := Equiv.Perm (Fin 23)

end CFSG.Certificates.Mathieu23
