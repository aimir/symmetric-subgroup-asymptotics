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
import SymmetricSubgroupAsymptotics.External.CFSG.Certificates.Mathieu23.GeneratedSubgroup

/-!
# Words in the M23 generators

This file defines the small, auditable word language that certificates use.
A certificate may contain words over `a`, `a⁻¹`, `b`, `b⁻¹`, `c`, and `c⁻¹`;
Lean evaluates those words in `Equiv.Perm (Fin 23)` and proves that their
values belong to the generated subgroup.
-/

namespace CFSG.Certificates.Mathieu23
namespace M23Certificates

/-- Generator alphabet for the three-generator presentation. -/
inductive Gen where
  | a
  | aInv
  | b
  | bInv
  | c
  | cInv
  deriving DecidableEq, Repr

/-- A certificate word over the generator alphabet. -/
abbrev Word : Type :=
  List Gen

namespace Gen

/-- Interpret a generator letter as a degree-23 permutation. -/
def toPerm : Gen → Perm23
  | a => m23a
  | aInv => m23a⁻¹
  | b => m23b
  | bInv => m23b⁻¹
  | c => m23c
  | cInv => m23c⁻¹

/-- Each generator letter evaluates to an element of the generated subgroup. -/
theorem toPerm_mem_M23Subgroup (g : Gen) : g.toPerm ∈ M23Subgroup := by
  cases g <;>
    simp [toPerm, m23a_mem_M23Subgroup, m23b_mem_M23Subgroup,
      m23c_mem_M23Subgroup]

end Gen

namespace Word

/-- Evaluate a certificate word as a permutation. -/
def eval : Word → Perm23
  | [] => 1
  | g :: rest => eval rest * g.toPerm

@[simp]
theorem eval_nil : eval [] = (1 : Perm23) :=
  rfl

@[simp]
theorem eval_cons (g : Gen) (rest : Word) :
    eval (g :: rest) = eval rest * g.toPerm :=
  rfl

/-- A word always evaluates to an element of `M23Subgroup`. -/
theorem eval_mem_M23Subgroup : ∀ w : Word, eval w ∈ M23Subgroup
  | [] => by simp [eval]
  | g :: rest => by
      exact M23Subgroup.mul_mem (eval_mem_M23Subgroup rest)
        (Gen.toPerm_mem_M23Subgroup g)

/-- Interpret a word as an element of the generated group `M23`. -/
def toM23 (w : Word) : M23 :=
  ⟨eval w, eval_mem_M23Subgroup w⟩

@[simp]
theorem toM23_toPerm (w : Word) : (toM23 w).1 = eval w :=
  rfl

end Word

end M23Certificates
end CFSG.Certificates.Mathieu23
