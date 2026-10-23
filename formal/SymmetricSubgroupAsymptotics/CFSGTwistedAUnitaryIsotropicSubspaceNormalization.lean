import SymmetricSubgroupAsymptotics.CFSGTwistedAUnitarySmallIsotropicVectors
import SymmetricSubgroupAsymptotics.CFSGTwistedAUnitaryStandardSingularSpace
import SymmetricSubgroupAsymptotics.CFSGTwistedAUnitaryIsotropicPointCoverage

/-! Actual all-rank normalization of totally isotropic subspaces.
The word is built recursively: normalize one vector by the checked
literal root words, compress the subspace, and lift the smaller word
through the checked middle embedding. All finite fields are retained.
No ambient group recognition or Witt extension theorem is assumed. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
open scoped Matrix

namespace SymmetricSubgroupAsymptotics.CFSGTwistedAUnitaryCoordinates
open CFSGTwistedANaturalMatrices CFSGTwistedAUpperUnipotent

theorem unitaryMiddle_normalizes_compressed (q : CFSG.PrimePower) (s : ℕ)
    (S : Submodule (q.Extension 2) (Fin (s + 3) → q.Extension 2))
    (he : Pi.single (0 : Fin (s + 3)) 1 ∈ S)
    (hS : ∀ x ∈ S, ∀ y ∈ S, unitaryNaturalPair q (s + 2) x y = 0)
    (g : naturalFixed s q)
    (hg : ∀ v ∈ unitaryCompressedSpace q s S,
      unitaryNaturalLinearEquiv q s g v ∈ unitaryStandardSingularSpace q s) :
    ∀ x ∈ S, unitaryNaturalLinearEquiv q (s + 2) (naturalFixedMiddleHom q s g) x ∈
      unitaryStandardSingularSpace q (s + 2) := by
  intro x hx
  have hz : x (Fin.last (s + 2)) = 0 := by
    simpa only [unitaryNaturalPair_first] using hS _ he x hx
  have hv := unitary_middleProjection_mem q s S he hS x hx
  have hm := unitaryStandardSingularSpace_middle q s _ (hg _ hv)
  have hh := (unitaryStandardSingularSpace q (s + 2)).smul_mem (x 0)
    (unitaryStandardSingularSpace_head q (s + 2) (by omega))
  have hd := congrArg (unitaryNaturalLinearEquiv q (s + 2) (naturalFixedMiddleHom q s g))
    (unitary_vector_decomposition q s x hz)
  rw [map_add, map_smul, unitaryMiddle_action_head, unitaryMiddle_action_middle] at hd
  exact hd.symm ▸ (unitaryStandardSingularSpace q (s + 2)).add_mem hh hm

private theorem head_mem_image_of_axis (q : CFSG.PrimePower) (r : ℕ)
    (S : Submodule (q.Extension 2) (Fin (r + 1) → q.Extension 2))
    (v : Fin (r + 1) → q.Extension 2) (hv : v ∈ S)
    (g : naturalFixed r q) (a : q.Extension 2) (ha : a ≠ 0)
    (hg : unitaryNaturalLinearEquiv q r g v = a • Pi.single (0 : Fin (r + 1)) 1) :
    Pi.single (0 : Fin (r + 1)) 1 ∈ unitarySubspaceImage q r g S := by
  have hmem : a • Pi.single (0 : Fin (r + 1)) 1 ∈ unitarySubspaceImage q r g S :=
    ⟨v, hv, hg⟩
  have h := (unitarySubspaceImage q r g S).smul_mem a⁻¹ hmem
  simpa only [smul_smul, inv_mul_cancel₀ ha, one_smul] using h

theorem exists_unitary_subspace_normalization (q : CFSG.PrimePower) (r : ℕ)
    (S : Submodule (q.Extension 2) (Fin (r + 1) → q.Extension 2))
    (hS : ∀ x ∈ S, ∀ y ∈ S, unitaryNaturalPair q r x y = 0) :
    ∃ g : naturalFixed r q,
      ∀ x ∈ S, unitaryNaturalLinearEquiv q r g x ∈ unitaryStandardSingularSpace q r := by
  revert S
  induction r using Nat.strong_induction_on with
  | h r ih =>
    intro S hS
    by_cases hbot : S = ⊥
    · refine ⟨1, ?_⟩
      intro x hx
      have hx0 : x = 0 := (Submodule.mem_bot (q.Extension 2)).mp (hbot ▸ hx)
      rw [hx0, map_zero]
      exact (unitaryStandardSingularSpace q r).zero_mem
    · obtain ⟨v, hvS, hv⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hbot
      cases r with
      | zero =>
          exact (hbot (rank_zero_pair_zero_subspace q S hS)).elim
      | succ r =>
        cases r with
        | zero =>
            obtain ⟨g, a, ha, haxis⟩ := exists_rank_one_isotropic_vector_axis q v hv (hS v hvS v hvS)
            let T := unitarySubspaceImage q 1 g S
            have he : Pi.single (0 : Fin 2) 1 ∈ T := head_mem_image_of_axis q 1 S v hvS g a ha haxis
            have hT := unitarySubspaceImage_pair_zero q 1 g S hS
            refine ⟨g, ?_⟩
            intro x hx
            have hmem : unitaryNaturalLinearEquiv q 1 g x ∈ T := ⟨x, hx, rfl⟩
            apply (unitaryStandardSingularSpace_rank_one q _).mpr
            simpa only [unitaryNaturalPair_first] using hT _ he _ hmem
        | succ s =>
            obtain ⟨g, a, ha, haxis⟩ := exists_isotropic_vector_axis q s v hv (hS v hvS v hvS)
            let T := unitarySubspaceImage q (s + 2) g S
            have he : Pi.single (0 : Fin (s + 3)) 1 ∈ T :=
              head_mem_image_of_axis q (s + 2) S v hvS g a ha haxis
            have hT := unitarySubspaceImage_pair_zero q (s + 2) g S hS
            obtain ⟨m, hm⟩ := ih s (by omega) (unitaryCompressedSpace q s T)
              (unitary_compressed_pair_zero q s T hT)
            have hnorm := unitaryMiddle_normalizes_compressed q s T he hT m hm
            refine ⟨naturalFixedMiddleHom q s m * g, ?_⟩
            intro x hx
            have hmem : unitaryNaturalLinearEquiv q (s + 2) g x ∈ T := ⟨x, hx, rfl⟩
            have h := hnorm _ hmem
            have hcomp : unitaryNaturalLinearEquiv q (s + 2) (naturalFixedMiddleHom q s m * g) x =
                unitaryNaturalLinearEquiv q (s + 2) (naturalFixedMiddleHom q s m)
                  (unitaryNaturalLinearEquiv q (s + 2) g x) := by
              change (((naturalFixedMiddleHom q s m).val.val : Mat (q.Extension 2) (s + 2)) *
                (g.val.val : Mat (q.Extension 2) (s + 2))) *ᵥ x = _
              exact (Matrix.mulVec_mulVec _ _ _).symm
            exact hcomp.symm ▸ h

end SymmetricSubgroupAsymptotics.CFSGTwistedAUnitaryCoordinates
