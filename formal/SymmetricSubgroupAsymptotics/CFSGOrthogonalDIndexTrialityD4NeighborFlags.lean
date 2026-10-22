import SymmetricSubgroupAsymptotics.CFSGOrthogonalDIndexTrialityD4ThreeExtensions

/-! Neighbours of the original D4 root plane retain their actual
intersection line and their actual singular three-space. These are
literal submodules, before any quotient by twins or triality action. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
namespace SymmetricSubgroupAsymptotics.CFSGOrthogonalDIndexTrialityD4ResidualSpace
open CFSGOrthogonalDSerreMatrices CFSGOrthogonalDIndexBundledQuadratic
open CFSGOrthogonalDIndexTailCoordinates
variable (K : Type) [Field K]

theorem extension_bot_eq_rootPlane :
    extension K (⊥ : Submodule K (Index 2 → K)) = rootPlane K := by
  apply le_antisymm
  · intro x hx
    have hz : twiceTailRestriction K 2 x = 0 := hx.2.2
    have hd := twice_head_tail_decomposition K 2 x hx.1 hx.2.1
    change x = x (Sum.inl 0) • head0 K +
      x (Sum.inl (tailSecondIndex 2)) • head1 K +
      twiceTailExtension K 2 (twiceTailRestriction K 2 x) at hd
    rw [hz, map_zero, add_zero] at hd
    rw [hd]
    exact (rootPlane K).add_mem
      ((rootPlane K).smul_mem _ (Submodule.subset_span (Or.inl rfl)))
      ((rootPlane K).smul_mem _ (Submodule.subset_span (Or.inr rfl)))
  · exact rootPlane_le_extension K ⊥

theorem rootPlane_finrank : Module.finrank K (rootPlane K) = 2 := by
  rw [← extension_bot_eq_rootPlane, extension_finrank, finrank_bot, add_zero]

theorem rootPlane_singular : ∀ x ∈ rootPlane K, splitQuadraticForm K 4 x = 0 := by
  rw [← extension_bot_eq_rootPlane]
  apply extension_singular
  intro z hz
  have he : z = 0 := hz
  rw [he, map_zero]

abbrev RootPoints := {L : Submodule K (Index 4 → K) //
  Module.finrank K L = 1 ∧ L ≤ rootPlane K}

abbrev Neighbors := {S : Submodule K (Index 4 → K) //
  Module.finrank K S = 2 ∧
  Module.finrank K ↥(rootPlane K ⊓ S) = 1 ∧
  ∀ x ∈ rootPlane K ⊔ S, splitQuadraticForm K 4 x = 0}

def neighborPoint (S : Neighbors K) : RootPoints K :=
  ⟨rootPlane K ⊓ S.val, S.property.2.1, inf_le_left⟩

def neighborThreeSpace (S : Neighbors K) : ThreeExtensions K :=
  ⟨rootPlane K ⊔ S.val, by
    have hh := Submodule.finrank_sup_add_finrank_inf_eq (rootPlane K) S.val
    rw [rootPlane_finrank, S.property.1, S.property.2.1] at hh
    omega, S.property.2.2, le_sup_left⟩

def neighborOppositeParameters (S : Neighbors K) :=
  (threeExtensionRulingEquiv K).symm (neighborThreeSpace K S)

theorem neighbor_point_le (S : Neighbors K) : (neighborPoint K S).val ≤ S.val :=
  inf_le_right

theorem neighbor_le_threeSpace (S : Neighbors K) : S.val ≤ (neighborThreeSpace K S).val :=
  le_sup_right

theorem neighbor_ne_rootPlane (S : Neighbors K) : S.val ≠ rootPlane K := by
  intro he
  have hh := S.property.2.1
  rw [he, inf_idem, rootPlane_finrank] at hh
  omega

theorem neighbor_threeSpace_intersection (S : Neighbors K) :
    (neighborThreeSpace K S).val =
      (columnMaximalExtension K (neighborOppositeParameters K S).1).val ⊓
        (rowMaximalExtension K (neighborOppositeParameters K S).2).val := by
  have hh := threeExtensionRuling_intersection K
    (neighborOppositeParameters K S).1 (neighborOppositeParameters K S).2
  change ((threeExtensionRulingEquiv K)
    ((threeExtensionRulingEquiv K).symm (neighborThreeSpace K S))).val = _ at hh
  simpa only [Equiv.apply_symm_apply] using hh

end SymmetricSubgroupAsymptotics.CFSGOrthogonalDIndexTrialityD4ResidualSpace
