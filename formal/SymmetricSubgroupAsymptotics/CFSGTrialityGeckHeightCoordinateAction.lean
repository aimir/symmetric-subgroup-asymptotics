import SymmetricSubgroupAsymptotics.CFSGTrialityGeckWordCoordinateTwist

/-! The literal cyclic/field action is the ACTUAL height-image action.
The proof checks the real root-parameter single-coordinate generators
and uses the finite product universal property, with no action premise. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
open scoped Classical
namespace SymmetricSubgroupAsymptotics.CFSGTrialityGeckHeightCoordinateAction
open CFSGTrialityGeckPositiveTwist CFSGTrialityGeckHeightQuotientTwist
open CFSGTrialityGeckWordHeightCoordinates CFSGTrialityGeckWordCoordinateTwist
open CFSGTrialityGeckWordRootIndex CFSGNormTwoCoordinateRootHeightFiltration
open CFSGTrialityD4NormTwo

local instance actionTailNormal (K : Type) [Field K] (h : ℤ) : (TailInPositive K h).Normal :=
  heightTail_normal_in_positive (CartanMatrix.D 4) (CartanMatrix.D_diag 4)
    (CartanMatrix.D_transpose 4) D4_positive_definite (CartanMatrix.D_off_diag_nonpos 4) K h

theorem heightImage_twist (K : Type) [Field K] [Finite K] (σ : K ≃+* K) (h : ℤ) :
    (HeightImage K h).map (quotientTwist K σ h).toMonoidHom = HeightImage K h := by
  apply Subgroup.eq_of_le_of_card_ge
  · rintro x ⟨y, hy, rfl⟩
    obtain ⟨u, hu, rfl⟩ := hy
    change quotientTwist K σ h (QuotientGroup.mk' (TailInPositive K (h + 1)) u) ∈
      HeightImage K h
    rw [quotientTwist_mk]
    have hm : positiveTwist K σ u ∈ (TailInPositive K h).map (positiveTwist K σ).toMonoidHom :=
      ⟨u, hu, rfl⟩
    rw [tailInPositive_twist K σ h] at hm
    exact ⟨positiveTwist K σ u, hm, rfl⟩
  · exact (Nat.card_congr ((quotientTwist K σ h).subgroupMap (HeightImage K h)).toEquiv).le

def heightImageTwist (K : Type) [Field K] [Finite K] (σ : K ≃+* K) (h : ℤ) :
    MulAut (HeightImage K h) :=
  ((quotientTwist K σ h).subgroupMap (HeightImage K h)).trans
    (MulEquiv.subgroupCongr (heightImage_twist K σ h))

theorem heightImageTwist_val (K : Type) [Field K] [Finite K] (σ : K ≃+* K)
    (h : ℤ) (x : HeightImage K h) :
    (heightImageTwist K σ h x).val = quotientTwist K σ h x.val := rfl

theorem coordinate_intertwining (K : Type) [Field K] [Finite K] (σ : K ≃+* K)
    (h : ℤ) (hh : 0 < h) :
    (heightImageTwist K σ h).toMonoidHom.comp (wordHeightLayerEquiv K h hh).toMonoidHom =
      (wordHeightLayerEquiv K h hh).toMonoidHom.comp (coordinateTwist K σ h).toMonoidHom := by
  apply MonoidHom.pi_ext
  intro j t
  apply Subtype.ext
  change quotientTwist K σ h (wordHeightLayerEquiv K h hh (Pi.mulSingle j t)).val =
    (wordHeightLayerEquiv K h hh (coordinateTwist K σ h (Pi.mulSingle j t))).val
  rw [wordHeightLayerEquiv_mulSingle, coordinateTwist_mulSingle,
    wordHeightLayerEquiv_mulSingle, quotientTwist_mk]
  exact congrArg (QuotientGroup.mk' (TailInPositive K (h + 1)))
    (wordPositiveParameter_action K σ j.val t)

theorem wordHeightLayerEquiv_twist (K : Type) [Field K] [Finite K] (σ : K ≃+* K)
    (h : ℤ) (hh : 0 < h) (c : WordHeightIndex h → Multiplicative K) :
    heightImageTwist K σ h (wordHeightLayerEquiv K h hh c) =
      wordHeightLayerEquiv K h hh (coordinateTwist K σ h c) :=
  DFunLike.congr_fun (coordinate_intertwining K σ h hh) c

theorem fixed_iff_coordinates (K : Type) [Field K] [Finite K] (σ : K ≃+* K)
    (h : ℤ) (hh : 0 < h) (c : WordHeightIndex h → Multiplicative K) :
    heightImageTwist K σ h (wordHeightLayerEquiv K h hh c) = wordHeightLayerEquiv K h hh c ↔
      coordinateTwist K σ h c = c := by
  rw [wordHeightLayerEquiv_twist]
  exact (wordHeightLayerEquiv K h hh).injective.eq_iff

end SymmetricSubgroupAsymptotics.CFSGTrialityGeckHeightCoordinateAction
