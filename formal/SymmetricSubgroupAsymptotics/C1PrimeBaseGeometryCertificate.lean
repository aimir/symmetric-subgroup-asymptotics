import SymmetricSubgroupAsymptotics.C1SparseSemidirectCertificate
import Mathlib.Data.Finset.Card

/-!
# Actual four-block ternary geometry for the bounded c=1 owner

This is the action-level supplement for the full prime-base degree-twelve
owner.  It retains four literal three-point blocks, their eight nonidentity
local translations, generation of the elementary ternary base, and the
faithful order-twelve action induced by the retained complement on the four
blocks.  Thus the required `C3 wr A4` geometry is certified on the original
permutation set rather than inferred from a catalogue label.
-/

set_option autoImplicit false
noncomputable section

namespace SymmetricSubgroupAsymptotics

structure C1PrimeBaseGeometryCertificate
    (C : C1SparseSemidirectCertificate (Equiv.Perm (Fin 12))) where
  blocks : Fin 4 → Finset (Fin 12)
  block_card : ∀ b, (blocks b).card = 3
  pointBlock : Fin 12 → Fin 4
  block_membership : ∀ b x, x ∈ blocks b ↔ b = pointBlock x
  coordinate : Fin 8 → Fin 4
  coordinate_card : ∀ b, (Finset.univ.filter fun i => coordinate i = b).card = 2
  localTranslations : Fin 8 → Equiv.Perm (Fin 12)
  local_ne_one : ∀ i, localTranslations i ≠ 1
  local_injective : Function.Injective localTranslations
  local_support : ∀ i x,
    localTranslations i x ≠ x ↔ x ∈ blocks (coordinate i)
  local_inverse : ∀ i j, coordinate i = coordinate j → i ≠ j →
    localTranslations i * localTranslations j = 1
  localInBase : BinaryNormalGeneratorWords localTranslations C.baseGenerators
  baseInLocal : BinaryNormalGeneratorWords C.baseGenerators localTranslations
  rows_exponent_three : ∀ i, (C.baseCayley.elements i) ^ 3 = 1
  factor_intersection_rows : ∀ i j,
    C.baseCayley.elements i = C.complementCayley.elements j →
      C.baseCayley.elements i = 1
  topGenerators : Fin C.complementGeneratorCount → Equiv.Perm (Fin 4)
  topCayley : FiniteCayleyCertificate topGenerators 12
  topRowsInjective : Function.Injective topCayley.elements
  block_action : ∀ c x,
    pointBlock (C.complementGenerators c x) = topGenerators c (pointBlock x)
  transitiveWord : Fin 4 → List (Fin C.complementGeneratorCount)
  transitive_from_zero : ∀ b,
    (((transitiveWord b).map topGenerators).prod) 0 = b

namespace C1PrimeBaseGeometryCertificate

variable {C : C1SparseSemidirectCertificate (Equiv.Perm (Fin 12))}
    (D : C1PrimeBaseGeometryCertificate C)

theorem block_partition (x : Fin 12) : ∃! b : Fin 4, x ∈ D.blocks b := by
  refine ⟨D.pointBlock x, (D.block_membership (D.pointBlock x) x).2 rfl, ?_⟩
  intro b hb
  exact (D.block_membership b x).1 hb

theorem localClosure_eq_base :
    Subgroup.closure (Set.range D.localTranslations) = C.base :=
  le_antisymm D.localInBase.closure_le D.baseInLocal.closure_le

include D in
theorem base_exponent_three : ∀ x : C.base, x ^ 3 = 1 := by
  intro x
  apply Subtype.ext
  change (x : Equiv.Perm (Fin 12)) ^ 3 = 1
  obtain ⟨i, hi⟩ := (C.baseCayley.mem_closure_iff (x : Equiv.Perm (Fin 12))).mp x.property
  rw [← hi]
  exact D.rows_exponent_three i

include D in
theorem factor_intersection_trivial (x : Equiv.Perm (Fin 12))
    (hxBase : x ∈ C.base) (hxComplement : x ∈ C.complement) : x = 1 := by
  obtain ⟨i, hi⟩ := C.baseCayley.mem_closure_iff x |>.mp hxBase
  obtain ⟨j, hj⟩ := C.complementCayley.mem_closure_iff x |>.mp hxComplement
  rw [← hi]
  exact C1PrimeBaseGeometryCertificate.factor_intersection_rows D i j (hi.trans hj.symm)

include D in
theorem factors_disjoint : Disjoint C.base C.complement := by
  apply disjoint_iff_inf_le.mpr
  intro x hx
  rw [Subgroup.mem_bot]
  exact D.factor_intersection_trivial x hx.1 hx.2

def top : Subgroup (Equiv.Perm (Fin 4)) :=
  Subgroup.closure (Set.range D.topGenerators)

theorem top_card : Nat.card D.top = 12 :=
  D.topCayley.card_closure D.topRowsInjective

theorem top_action_reaches (b : Fin 4) :
    ∃ w : List (Fin C.complementGeneratorCount),
      ((w.map D.topGenerators).prod) 0 = b :=
  ⟨D.transitiveWord b, D.transitive_from_zero b⟩

end C1PrimeBaseGeometryCertificate

end SymmetricSubgroupAsymptotics
