import SymmetricSubgroupAsymptotics.CFSGSymplecticNormalizerCenterAtoms
import SymmetricSubgroupAsymptotics.CFSGNormalizerCenterAtomCount

/-! Intrinsic local choice bounds for the actual C Sylow: at most
two centre atoms for q>2 and at most three for q=2. The latter uses
only the actual centre order four and the generic disjointness bound. -/
set_option autoImplicit false
noncomputable section
namespace SymmetricSubgroupAsymptotics.CFSGSymplecticUnipotent
open CFSGSymplecticSerreMatrices CFSGNormalizerCenterAtoms
variable {K : Type} [Field K] [Finite K] [CharP K 2]

theorem binaryField_centerAtom_card_le_three (r : ℕ) (hr : 0 < r)
    (hq : Nat.card K = 2) :
    Nat.card {H : Subgroup (elementaryRootGroup K (r + 1)) // IsAtom (unipotent K (r + 1)) H} ≤ 3 := by
  have h := atom_card_le_center_sub_one (unipotent K (r + 1))
  rw [centerImage_card, binary_unipotent_center_card r hr, hq] at h
  exact h

theorem largerField_centerAtom_card_le_two (r : ℕ) (hr : 0 < r)
    (hq : 2 < Nat.card K) :
    Nat.card {H : Subgroup (elementaryRootGroup K (r + 1)) // IsAtom (unipotent K (r + 1)) H} ≤ 2 := by
  classical
  let L := longCenterAxis (K := K) r hr
  let f : {H : Subgroup (elementaryRootGroup K (r + 1)) // IsAtom (unipotent K (r + 1)) H} → Fin 2 :=
    fun H => if H.val = L then 0 else 1
  have hi : Function.Injective f := by
    intro H J he
    apply Subtype.ext
    have hH := (normalizerCenterAtom_iff_axis r hr hq H.val).mp H.property
    have hJ := (normalizerCenterAtom_iff_axis r hr hq J.val).mp J.property
    by_cases hL : H.val = L
    · have hJL : J.val = L := by
        by_contra hJL
        have hz : (0 : Fin 2) = 1 := by simpa only [f, if_pos hL, if_neg hJL] using he
        exact (by decide : (0 : Fin 2) ≠ 1) hz
      exact hL.trans hJL.symm
    · have hJL : J.val ≠ L := by
        intro hJL
        have hz : (1 : Fin 2) = 0 := by simpa only [f, if_neg hL, if_pos hJL] using he
        exact (by decide : (1 : Fin 2) ≠ 0) hz
      exact (hH.resolve_left hL).trans (hJ.resolve_left hJL).symm
  simpa only [Nat.card_fin] using Nat.card_le_card_of_injective f hi

end SymmetricSubgroupAsymptotics.CFSGSymplecticUnipotent
