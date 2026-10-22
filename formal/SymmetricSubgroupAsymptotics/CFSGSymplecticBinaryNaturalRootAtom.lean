import SymmetricSubgroupAsymptotics.CFSGSymplecticNormalizerCenterAtoms
import Mathlib.Algebra.Group.Subgroup.Finite

/-! The original natural highest root is an intrinsic centre atom
also over the two-element field. Its actual order two makes any
nontrivial subgroup already the full root group. -/
set_option autoImplicit false
noncomputable section
namespace SymmetricSubgroupAsymptotics.CFSGSymplecticUnipotent
open CFSGSymplecticSerreMatrices CFSGSymplecticTransvectionGeometry
variable {K : Type} [Field K] [Finite K] [CharP K 2]

theorem binaryField_naturalRoot_is_normalizerCenterAtom (r : ℕ) (hr : 0 < r)
    (hq : Nat.card K = 2) :
    CFSGNormalizerCenterAtoms.IsAtom (unipotent K (r + 1))
      (actualNaturalRootLine r hr (Pi.single (Sum.inl (0 : Fin (r + 1))) 1)) := by
  have hv : (Pi.single (Sum.inl (0 : Fin (r + 1))) (1 : K) : Index (r + 1) → K) ≠ 0 := by
    intro h
    have he := congrFun h (Sum.inl 0)
    have hzero : (1 : K) = 0 := by
      simpa only [Pi.single_eq_same, Pi.zero_apply] using he
    exact one_ne_zero hzero
  have hcard : Nat.card (longCenterAxis (K := K) r hr) = 2 := by
    rw [longCenterAxis_eq_actualNaturalRootLine, actualNaturalRootLine_card r hr _ hv, hq]
  rw [← longCenterAxis_eq_actualNaturalRootLine r hr]
  refine ⟨longCenterAxis_ne_bot r hr, ?_, ?_, ?_⟩
  · change longCenterAxis r hr ≤ (Subgroup.center (unipotent K (r + 1))).map _
    rw [← centerToElementary_range r hr]
    exact longCenterAxis_le_range r hr
  · rw [normalizer_unipotent_eq_borel K r hr]
    exact borel_le_normalizer_longCenterAxis r hr
  · intro J hne hle _
    letI binaryNaturalAtom_nontrivial : Nontrivial J := (Subgroup.nontrivial_iff_ne_bot J).mpr hne
    have hj : 2 ≤ Nat.card J := Nat.succ_le_of_lt (Finite.one_lt_card_iff_nontrivial.mpr inferInstance)
    apply Subgroup.eq_of_le_of_card_ge hle
    rwa [hcard]

theorem binaryChar_naturalRoot_is_normalizerCenterAtom (r : ℕ) (hr : 0 < r) :
    CFSGNormalizerCenterAtoms.IsAtom (unipotent K (r + 1))
      (actualNaturalRootLine r hr (Pi.single (Sum.inl (0 : Fin (r + 1))) 1)) := by
  by_cases hq : Nat.card K = 2
  · exact binaryField_naturalRoot_is_normalizerCenterAtom r hr hq
  · have htwo : 1 < Nat.card K := Finite.one_lt_card_iff_nontrivial.mpr inferInstance
    exact naturalRoot_is_normalizerCenterAtom r hr (by omega)

end SymmetricSubgroupAsymptotics.CFSGSymplecticUnipotent
