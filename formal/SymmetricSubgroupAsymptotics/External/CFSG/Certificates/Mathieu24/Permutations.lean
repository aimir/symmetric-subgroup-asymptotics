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
import SymmetricSubgroupAsymptotics.External.CFSG.Certificates.Mathieu24.Basic

/-!
# Explicit degree-24 permutations

The first three generators are the `M23` generators `m23a`, `m23b`, `m23c`
read on `Fin 24` (they move only the points `0,…,22` and fix the new point
`23`).  The fourth generator is an automorphism of the Steiner system
`S(5,8,24)` moving `23`, found by `scripts/build_m24.py`, which extends the
repo's `S(4,7,23)` by the weight-8 words of the extended binary Golay code
`[24,12,8]`.  They are input data for certificates, not trusted
mathematical facts: Lean re-verifies the order and block certificates.
-/

namespace CFSG.Certificates.Mathieu24

open Equiv Equiv.Perm

/-- The first generator: `m23a` on 24 points (order 5, fixes `22`, `23`). -/
def m24a : Perm24 :=
  List.formPerm ([0, 11, 4, 5, 15] : List (Fin 24)) *
    List.formPerm ([1, 14, 21, 10, 18] : List (Fin 24)) *
    List.formPerm ([2, 7, 8, 16, 12] : List (Fin 24)) *
    List.formPerm ([3, 13, 9, 19, 20] : List (Fin 24))

/-- The second generator: `m23b` on 24 points (order 8, fixes `22`, `23`). -/
def m24b : Perm24 :=
  List.formPerm ([0, 17, 10, 19, 18, 8, 3, 1] : List (Fin 24)) *
    List.formPerm ([2, 14] : List (Fin 24)) *
    List.formPerm ([4, 7, 6, 15] : List (Fin 24)) *
    List.formPerm ([5, 21, 12, 13, 9, 11, 16, 20] : List (Fin 24))

/-- The third generator: the 23-cycle `m23c` on 24 points (fixes `23`). -/
def m24c : Perm24 :=
  List.formPerm
    ([0, 2, 17, 5, 3, 6, 14, 8, 11, 16, 22, 1, 21, 7, 18, 13, 10, 4, 20,
      15, 9, 12, 19] : List (Fin 24))

/-- The fourth generator: an automorphism of `S(5,8,24)` moving `23`
(cycle type `14·7·2`). -/
def m24d : Perm24 :=
  List.formPerm
    ([0, 6, 5, 9, 11, 4, 7, 8, 16, 17, 21, 18, 10, 3] : List (Fin 24)) *
    List.formPerm ([1, 2, 19, 14, 13, 20, 23] : List (Fin 24)) *
    List.formPerm ([12, 15] : List (Fin 24))

/-- Milestone sanity check: `m24a` is an equivalence, hence a permutation. -/
theorem m24a_bijective : Function.Bijective m24a :=
  m24a.bijective

/-- Milestone sanity check: `m24b` is an equivalence, hence a permutation. -/
theorem m24b_bijective : Function.Bijective m24b :=
  m24b.bijective

/-- Milestone sanity check: `m24c` is an equivalence, hence a permutation. -/
theorem m24c_bijective : Function.Bijective m24c :=
  m24c.bijective

/-- Milestone sanity check: `m24d` is an equivalence, hence a permutation. -/
theorem m24d_bijective : Function.Bijective m24d :=
  m24d.bijective

end CFSG.Certificates.Mathieu24
