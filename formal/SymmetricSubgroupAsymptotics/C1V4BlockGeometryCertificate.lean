import SymmetricSubgroupAsymptotics.C1SparseSemidirectCertificate
import Mathlib.Data.Finset.Card

/-!
# Actual three-block V4 geometry for the bounded c=1 owners

This is the action-level supplement to a sparse semidirect certificate.
It retains the three literal four-point blocks, the nine nonidentity local
translations, their generation of the binary base, and the actual conjugation
action of the ternary complement.  Explicit words prove transitivity on the
nine translations.  Thus an abstract order or catalogue label cannot stand
in for the required original permutation geometry.
-/

set_option autoImplicit false
noncomputable section

namespace SymmetricSubgroupAsymptotics

structure C1V4BlockGeometryCertificate
    (C : C1SparseSemidirectCertificate (Equiv.Perm (Fin 12))) where
  blocks : Fin 3 → Finset (Fin 12)
  block_card : ∀ b, (blocks b).card = 4
  pointBlock : Fin 12 → Fin 3
  block_membership : ∀ b x, x ∈ blocks b ↔ b = pointBlock x
  coordinate : Fin 9 → Fin 3
  coordinate_card : ∀ b, (Finset.univ.filter fun i => coordinate i = b).card = 3
  localTranslations : Fin 9 → Equiv.Perm (Fin 12)
  local_ne_one : ∀ i, localTranslations i ≠ 1
  local_injective : Function.Injective localTranslations
  local_support : ∀ i x,
    localTranslations i x ≠ x ↔ x ∈ blocks (coordinate i)
  local_product : ∀ i j, coordinate i = coordinate j → i ≠ j →
    ∃ k, coordinate k = coordinate i ∧
      localTranslations i * localTranslations j = localTranslations k
  localInBase : BinaryNormalGeneratorWords localTranslations C.baseGenerators
  baseInLocal : BinaryNormalGeneratorWords C.baseGenerators localTranslations
  rows_exponent_two : ∀ i, (C.baseCayley.elements i) ^ 2 = 1
  actionGenerators : Fin C.complementGeneratorCount → Equiv.Perm (Fin 9)
  conjugation : ∀ c i,
    C.complementGenerators c * localTranslations i *
      (C.complementGenerators c)⁻¹ = localTranslations (actionGenerators c i)
  transitiveWord : Fin 9 → List (Fin C.complementGeneratorCount)
  transitive_from_zero : ∀ i,
    (((transitiveWord i).map actionGenerators).prod) 0 = i

namespace C1V4BlockGeometryCertificate

variable {C : C1SparseSemidirectCertificate (Equiv.Perm (Fin 12))}
    (D : C1V4BlockGeometryCertificate C)

theorem block_partition (x : Fin 12) : ∃! b : Fin 3, x ∈ D.blocks b := by
  refine ⟨D.pointBlock x, (D.block_membership (D.pointBlock x) x).2 rfl, ?_⟩
  intro b hb
  exact (D.block_membership b x).1 hb

theorem localClosure_eq_base :
    Subgroup.closure (Set.range D.localTranslations) = C.base :=
  le_antisymm D.localInBase.closure_le D.baseInLocal.closure_le

include D in
theorem base_exponent_two : ∀ x : C.base, x ^ 2 = 1 := by
  intro x
  apply Subtype.ext
  change (x : Equiv.Perm (Fin 12)) ^ 2 = 1
  obtain ⟨i, hi⟩ := (C.baseCayley.mem_closure_iff (x : Equiv.Perm (Fin 12))).mp x.property
  rw [← hi]
  exact D.rows_exponent_two i

theorem local_action_reaches (i : Fin 9) :
    ∃ w : List (Fin C.complementGeneratorCount),
      ((w.map D.actionGenerators).prod) 0 = i :=
  ⟨D.transitiveWord i, D.transitive_from_zero i⟩

end C1V4BlockGeometryCertificate

end SymmetricSubgroupAsymptotics
