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
import SymmetricSubgroupAsymptotics.External.CFSG.Certificates.Mathieu24.GeneratedSubgroup

/-!
# Words in the M24 generators

This file defines the small, auditable word language that certificates use.
A certificate may contain words over `a`, `a⁻¹`, `b`, `b⁻¹`, `c`, `c⁻¹`,
`d`, and `d⁻¹`; Lean evaluates those words in `Equiv.Perm (Fin 24)` and
proves that their values belong to the generated subgroup.
-/

namespace CFSG.Certificates.Mathieu24
namespace M24Certificates

/-- Generator alphabet for the four-generator presentation. -/
inductive Gen where
  | a
  | aInv
  | b
  | bInv
  | c
  | cInv
  | d
  | dInv
  deriving DecidableEq, Repr

/-- A certificate word over the generator alphabet. -/
abbrev Word : Type :=
  List Gen

namespace Gen

/-- Interpret a generator letter as a degree-24 permutation. -/
def toPerm : Gen → Perm24
  | a => m24a
  | aInv => m24a⁻¹
  | b => m24b
  | bInv => m24b⁻¹
  | c => m24c
  | cInv => m24c⁻¹
  | d => m24d
  | dInv => m24d⁻¹

/-- Each generator letter evaluates to an element of the generated subgroup. -/
theorem toPerm_mem_M24Subgroup (g : Gen) : g.toPerm ∈ M24Subgroup := by
  cases g <;>
    simp [toPerm, m24a_mem_M24Subgroup, m24b_mem_M24Subgroup,
      m24c_mem_M24Subgroup, m24d_mem_M24Subgroup]

end Gen

namespace Word

/-- Evaluate a certificate word as a permutation. -/
def eval : Word → Perm24
  | [] => 1
  | g :: rest => eval rest * g.toPerm

@[simp]
theorem eval_nil : eval [] = (1 : Perm24) :=
  rfl

@[simp]
theorem eval_cons (g : Gen) (rest : Word) :
    eval (g :: rest) = eval rest * g.toPerm :=
  rfl

/-- A word always evaluates to an element of `M24Subgroup`. -/
theorem eval_mem_M24Subgroup : ∀ w : Word, eval w ∈ M24Subgroup
  | [] => by simp [eval]
  | g :: rest => by
      exact M24Subgroup.mul_mem (eval_mem_M24Subgroup rest)
        (Gen.toPerm_mem_M24Subgroup g)

/-- Interpret a word as an element of the generated group `M24`. -/
def toM24 (w : Word) : M24 :=
  ⟨eval w, eval_mem_M24Subgroup w⟩

@[simp]
theorem toM24_toPerm (w : Word) : (toM24 w).1 = eval w :=
  rfl

end Word

end M24Certificates
end CFSG.Certificates.Mathieu24
