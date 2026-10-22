import SymmetricSubgroupAsymptotics.CFSGOrthogonalBAutomorphismCardinality
import SymmetricSubgroupAsymptotics.CFSGOrthogonalBSpecialIsometryIndex
import SymmetricSubgroupAsymptotics.CFSGOuterCardinalityCancellation
import SymmetricSubgroupAsymptotics.CFSGOrthogonalBProjectiveEquiv
import SymmetricSubgroupAsymptotics.CFSGOrthogonalBProjectiveRealization
import Lean.Elab.Tactic.Omega
import SymmetricSubgroupAsymptotics.CFSGSimpleIndexTransport

/-! Actual inner/outer cancellation for the SAME odd-B projective
model. The checked polar reconstruction bounds Aut by SO times field
automorphisms; the checked actual SO/elementary index is at most two.
The actual elementary centre is trivial. No recognition callback or
extra scalar-kernel factor is assumed. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
namespace SymmetricSubgroupAsymptotics.CFSGOrthogonalBOuterCardinality
open CFSGOrthogonalBSerreMatrices CFSGOrthogonalBSpecialFormGroup
open PrimitiveSocleRawStructure
variable (K : Type) [Field K] [Finite K]

theorem outer_card_le_two_fieldAut_of_automorphism_bound
    (p : ℕ) [Fact p.Prime] [CharP K p] (h2 : (2 : K) ≠ 0) (s : ℕ)
    [IsSimpleGroup (elementaryProjective K (s + 3))]
    (hbound : Nat.card (MulAut (elementaryProjective K (s + 3))) ≤
      Nat.card (specialFormUnits K (s + 3)) * Nat.card (K ≃+* K)) :
    Nat.card (Outer (elementaryProjective K (s + 3))) ≤ 2 * Nat.card (K ≃+* K) := by
  let E := elementaryRootGroup K (s + 3)
  let G := elementaryProjective K (s + 3)
  let e : E ≃* G := oddProjectiveEquiv K p h2 (s + 2)
  letI oddBOuter_projectiveFinite : Finite G := Finite.of_surjective
    (QuotientGroup.mk' (Subgroup.center E)) (QuotientGroup.mk'_surjective _)
  letI oddBOuter_elementarySimple : IsSimpleGroup E := e.isSimpleGroup
  have hn : ¬ IsMulCommutative G := by
    intro hc
    have hcE : IsMulCommutative E := by
      apply isMulCommutative_iff.mpr
      intro x y
      apply e.injective
      rw [map_mul, map_mul]
      exact (isMulCommutative_iff.mp hc) (e x) (e y)
    have ht : Subgroup.center E = ⊤ := Subgroup.center_eq_top_iff.mpr hcE
    have hb : Subgroup.center E = ⊥ := CFSGOrthogonalBIndexCenter.center_eq_bot K p h2 (s + 2)
    exact bot_ne_top (hb.symm.trans ht)
  have hE : E ≤ specialFormUnits K (s + 3) := elementary_le_specialFormUnits K p h2 _
  let H := E.subgroupOf (specialFormUnits K (s + 3))
  have hH : Nat.card H = Nat.card E :=
    Nat.card_congr (Subgroup.subgroupOfEquivOfLe hE).toEquiv
  have hIndex : H.index ≤ 2 :=
    CFSGOrthogonalBSpecialIsometryIndex.elementary_index_le_two K p h2 (s + 2)
  have hSO : Nat.card (specialFormUnits K (s + 3)) ≤ Nat.card G * 2 := by
    calc
      Nat.card (specialFormUnits K (s + 3)) = Nat.card H * H.index := H.card_mul_index.symm
      _ ≤ Nat.card H * 2 := Nat.mul_le_mul_left _ hIndex
      _ = Nat.card G * 2 := by rw [hH, Nat.card_congr e.toEquiv]
  have hAut : Nat.card (MulAut G) ≤ Nat.card G * (2 * Nat.card (K ≃+* K)) := by
    calc
      Nat.card (MulAut G) ≤ Nat.card (specialFormUnits K (s + 3)) * Nat.card (K ≃+* K) := hbound
      _ ≤ (Nat.card G * 2) * Nat.card (K ≃+* K) := Nat.mul_le_mul_right _ hSO
      _ = Nat.card G * (2 * Nat.card (K ≃+* K)) := Nat.mul_assoc _ _ _
  exact CFSGOuterCardinalityCancellation.outer_card_le_of_automorphism_bound hn _ hAut

theorem outer_card_le_two_fieldAut
    (p : ℕ) [Fact p.Prime] [CharP K p] (h2 : (2 : K) ≠ 0) (s : ℕ)
    [IsSimpleGroup (elementaryProjective K (s + 3))] :
    Nat.card (Outer (elementaryProjective K (s + 3))) ≤ 2 * Nat.card (K ≃+* K) :=
  outer_card_le_two_fieldAut_of_automorphism_bound K p h2 s
    (CFSGOrthogonalBAutomorphismCardinality.automorphism_card_le_special_mul_field K p h2 s)

end SymmetricSubgroupAsymptotics.CFSGOrthogonalBOuterCardinality

namespace SymmetricSubgroupAsymptotics.CFSGReduction
open CFSGOrthogonalBSerreMatrices PrimitiveSocleRawStructure

theorem typeB_odd_outer_card_le (r : ℕ) (hr : 3 ≤ r) (q : CFSG.PrimePower)
    (h2 : (2 : q.Field) ≠ 0) [IsSimpleGroup (CFSG.Models.B r q)] :
    Nat.card (Outer (CFSG.Models.B r q)) ≤ 2 * Nat.card (q.Field ≃+* q.Field) := by
  obtain ⟨s, rfl⟩ : ∃ s : ℕ, r = s + 3 := ⟨r - 3, by omega⟩
  let e := serreProjectiveEquivElementaryProjective q.Field (s + 2) h2
  letI oddBOuter_modelProjectiveSimple : IsSimpleGroup (elementaryProjective q.Field (s + 3)) :=
    e.symm.isSimpleGroup
  rw [outer_card_congr e]
  exact CFSGOrthogonalBOuterCardinality.outer_card_le_two_fieldAut q.Field q.prime h2 s

end SymmetricSubgroupAsymptotics.CFSGReduction
