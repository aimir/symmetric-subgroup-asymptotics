import SymmetricSubgroupAsymptotics.CFSGTrialityGeckRelativeRootGenerated
import SymmetricSubgroupAsymptotics.CFSGTrialityD4WordDiscriminant
import SymmetricSubgroupAsymptotics.CFSGNormTwoCoordinateOppositeWord
import Mathlib.Tactic.NormNum

/-! A literal relative opposition word acts as minus one on the D4
lattice and conjugates the actual fixed positive group to the actual
fixed negative group. Its matrix word belongs to their generated group. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
open scoped Classical Matrix
namespace SymmetricSubgroupAsymptotics.CFSGTrialityGeckRelativeOpposition
open CFSGTrialityD4NormTwo CFSGTrialityGeckDiagramCovariance
open CFSGTrialityRelativeWordLanguage CFSGTrialityGeckRelativeRootGenerated
open CFSGTrialityGeckMatrixTwist CFSGTrialityGeckPositiveTwist
open CFSGNormTwoCoordinateLatticeWord CFSGTrialityD4WordDiscriminant
open CFSGNormTwoGeckWeylLatticeLinear CFSGNormTwoGeckWeylWordDegree
open CFSGNormTwoGeckIntegralWord CFSGNormTwoRootPairing
open CFSGNormTwoCoordinateWeylRootMembership CFSGNormTwoCoordinateOppositeWord
open CFSGNormTwoGeckPositivePGroup CFSGNormTwoGeckOppositeIntersection
open CFSGNormTwoCoordinateHeight CFSGCentralTwistedCommutatorLift
open CFSGSignedCartanReflections

def oppositionRelativeWord : List Bool := [false, true, false, true, false, true]

def oppositionWord : List (Fin 4) := expandRelative oppositionRelativeWord

theorem opposition_lattice_neg : latticeWord (CartanMatrix.D 4) oppositionWord = -1 := by
  decide

theorem opposition_linear_neg (v : Fin 4 → ℤ) :
    wordLinear (CartanMatrix.D 4) (CartanMatrix.D_transpose 4)
      D4_positive_definite Base Index oppositionWord v = -v := by
  have h := LinearMap.congr_fun (latticeWord_linear (CartanMatrix.D 4) (CartanMatrix.D_diag 4)
    (CartanMatrix.D_transpose 4) D4_positive_definite (CartanMatrix.D_off_diag_nonpos 4)
    oppositionWord) v
  change latticeWord (CartanMatrix.D 4) oppositionWord *ᵥ v = _ at h
  rw [opposition_lattice_neg, Matrix.neg_mulVec, Matrix.one_mulVec] at h
  exact h.symm

theorem opposition_simple_nonpositive (i j : Fin 4) :
    (wordRoot (CartanMatrix.D 4) (CartanMatrix.D_transpose 4)
      D4_positive_definite Base Index oppositionWord (Index i)).val j ≤ 0 := by
  have h := (wordLinear_root (CartanMatrix.D 4) (CartanMatrix.D_transpose 4)
    D4_positive_definite Base Index oppositionWord (Index i)).symm.trans
      (opposition_linear_neg (Index i : Roots (CartanMatrix.D 4)).val)
  rw [h]
  change -(Pi.single i (1 : ℤ) : Fin 4 → ℤ) j ≤ 0
  simp only [Pi.single_apply]
  split_ifs <;> norm_num

def relativeOpposition (K : Type) [Field K] : (Matrix GeckIndex GeckIndex K)ˣ :=
  wordUnit (CartanMatrix.D 4) (CartanMatrix.D_transpose 4)
    D4_positive_definite Base Index K oppositionWord

theorem relativeOpposition_fixed (K : Type) [Field K] (sigma : K ≃+* K) :
    unitTwist K sigma (relativeOpposition K) = relativeOpposition K := by
  simpa only [relativeOpposition, oppositionWord, word_eq_canonicalWord] using
    relative_word_fixed K sigma oppositionRelativeWord

theorem relativeOpposition_mem_generated (K : Type) [Field K] (sigma : K ≃+* K) :
    relativeOpposition K ∈ fixedRootGenerated K sigma :=
  relativeWord_mem_generated K sigma oppositionRelativeWord

theorem positive_image_le_negative (K : Type) [Field K] :
    (Positive K).map (MulAut.conj (relativeOpposition K)).toMonoidHom ≤
      rootGroup (CartanMatrix.D 4) (CartanMatrix.D_transpose 4)
        D4_positive_definite Base Index K true := by
  apply Subgroup.map_le_iff_le_comap.mpr
  apply (Subgroup.closure_le _).mpr
  rintro _ ⟨⟨i, t⟩, rfl⟩
  exact negative_word_mem (CartanMatrix.D 4) (CartanMatrix.D_diag 4)
    (CartanMatrix.D_transpose 4) D4_positive_definite (CartanMatrix.D_off_diag_nonpos 4)
    K oppositionWord i t (opposition_simple_nonpositive i)

theorem positive_image_eq_negative (K : Type) [Field K] [Finite K] :
    (Positive K).map (MulAut.conj (relativeOpposition K)).toMonoidHom =
      rootGroup (CartanMatrix.D 4) (CartanMatrix.D_transpose 4)
        D4_positive_definite Base Index K true := by
  have hi : Positive K ⊓ (Positive K).map
      (MulAut.conj (relativeOpposition K)).toMonoidHom = ⊥ := by
    apply le_antisymm _ bot_le
    exact (inf_le_inf le_rfl (positive_image_le_negative K)).trans
      (le_of_eq (positive_inf_negative (CartanMatrix.D 4) (CartanMatrix.D_transpose 4)
        D4_positive_definite Base Index coordinateHeight
        (simple_height (CartanMatrix.D 4) (CartanMatrix.D_diag 4) (CartanMatrix.D_transpose 4)
          D4_positive_definite (CartanMatrix.D_off_diag_nonpos 4)) K))
  exact word_positive_map_eq_negative_of_disjoint (CartanMatrix.D 4) (CartanMatrix.D_diag 4)
    (CartanMatrix.D_transpose 4) D4_positive_definite (CartanMatrix.D_off_diag_nonpos 4)
    K oppositionWord hi

private theorem fixed_conjugation_map {G : Type*} [Group G]
    (tau : MulAut G) (W : G) (hW : tau W = W) :
    (fixedSubgroup tau).map (MulAut.conj W).toMonoidHom = fixedSubgroup tau := by
  ext x
  constructor
  · rintro ⟨y, hy, rfl⟩
    change tau (W * y * W⁻¹) = W * y * W⁻¹
    change tau y = y at hy
    rw [map_mul, map_mul, map_inv, hW, hy]
  · intro hx
    change tau x = x at hx
    refine ⟨W⁻¹ * x * W, ?_, ?_⟩
    · change tau (W⁻¹ * x * W) = W⁻¹ * x * W
      rw [map_mul, map_mul, map_inv, hW, hx]
    · change W * (W⁻¹ * x * W) * W⁻¹ = x
      group

theorem fixed_positive_image_eq_fixed_negative (K : Type) [Field K] [Finite K]
    (sigma : K ≃+* K) :
    (signedFixed K sigma false).map (MulAut.conj (relativeOpposition K)).toMonoidHom =
      signedFixed K sigma true := by
  change ((Positive K) ⊓ fixedSubgroup (unitTwist K sigma)).map
      (MulAut.conj (relativeOpposition K)).toMonoidHom = _
  rw [Subgroup.map_inf _ _ _ (MulAut.conj (relativeOpposition K)).injective,
    positive_image_eq_negative, fixed_conjugation_map _ _ (relativeOpposition_fixed K sigma)]
  rfl

end SymmetricSubgroupAsymptotics.CFSGTrialityGeckRelativeOpposition
