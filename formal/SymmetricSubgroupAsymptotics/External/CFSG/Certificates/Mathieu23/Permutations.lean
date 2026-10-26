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
import Mathlib.GroupTheory.Perm.Cycle.Concrete
import SymmetricSubgroupAsymptotics.External.CFSG.Certificates.Mathieu23.Basic

/-!
# Explicit degree-23 permutations

The first two generators are the `M22` generators `m22a`, `m22b` read on
`Fin 23` (they move only the points `0,…,21` and fix the new point `22`).
The third generator is a 23-cycle: an automorphism of the Steiner system
`S(4,7,23)` found by `scripts/build_m23.py`, which extends the repo's
`S(3,6,22)` by the weight-7 words of the binary Golay code `[23,12,7]`.
They are input data for certificates, not trusted mathematical facts: Lean
re-verifies the order and block certificates.
-/

namespace CFSG.Certificates.Mathieu23

open Equiv Equiv.Perm

/-- The first generator: `m22a` on 23 points (order 5, fixes `22`). -/
def m23a : Perm23 :=
  List.formPerm ([0, 11, 4, 5, 15] : List (Fin 23)) *
    List.formPerm ([1, 14, 21, 10, 18] : List (Fin 23)) *
    List.formPerm ([2, 7, 8, 16, 12] : List (Fin 23)) *
    List.formPerm ([3, 13, 9, 19, 20] : List (Fin 23))

/-- The second generator: `m22b` on 23 points (order 8, fixes `22`). -/
def m23b : Perm23 :=
  List.formPerm ([0, 17, 10, 19, 18, 8, 3, 1] : List (Fin 23)) *
    List.formPerm ([2, 14] : List (Fin 23)) *
    List.formPerm ([4, 7, 6, 15] : List (Fin 23)) *
    List.formPerm ([5, 21, 12, 13, 9, 11, 16, 20] : List (Fin 23))

/-- The third generator: a 23-cycle automorphism of `S(4,7,23)`. -/
def m23c : Perm23 :=
  List.formPerm
    ([0, 2, 17, 5, 3, 6, 14, 8, 11, 16, 22, 1, 21, 7, 18, 13, 10, 4, 20,
      15, 9, 12, 19] : List (Fin 23))

/-- Milestone sanity check: `m23a` is an equivalence, hence a permutation. -/
theorem m23a_bijective : Function.Bijective m23a :=
  m23a.bijective

/-- Milestone sanity check: `m23b` is an equivalence, hence a permutation. -/
theorem m23b_bijective : Function.Bijective m23b :=
  m23b.bijective

/-- Milestone sanity check: `m23c` is an equivalence, hence a permutation. -/
theorem m23c_bijective : Function.Bijective m23c :=
  m23c.bijective

end CFSG.Certificates.Mathieu23
