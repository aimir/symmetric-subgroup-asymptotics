import SymmetricSubgroupAsymptotics.CFSGTwistedAUnitarySubspaceCompression
import SymmetricSubgroupAsymptotics.CFSGTwistedAUnitaryRootOrthogonality

/-! The actual natural fixed group acts linearly on its literal
subspaces. Middle words fix the first axis and intertwine the literal
middle embedding. This is the action used in recursive isotropic-space
normalization, without an ambient isometry-extension hypothesis. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
open scoped Matrix BigOperators

namespace SymmetricSubgroupAsymptotics.CFSGTwistedAUnitaryCoordinates
open CFSGTwistedANaturalMatrices CFSGTwistedAUpperUnipotent
open CFSGTwistedAUnitaryUpperArrays CFSGHermitianHyperbolicCompression
open CFSGTwistedAUnitaryParameters CFSGSerreOrdinaryTwists

private def matrixUnitLinearEquiv {K I : Type*} [Field K] [Fintype I]
    [DecidableEq I] (g : (Matrix I I K)ˣ) : (I → K) ≃ₗ[K] (I → K) where
  toFun x := (g : Matrix I I K) *ᵥ x
  invFun x := ((g⁻¹ : (Matrix I I K)ˣ) : Matrix I I K) *ᵥ x
  left_inv x := by
    dsimp only
    rw [Matrix.mulVec_mulVec, Units.inv_mul, Matrix.one_mulVec]
  right_inv x := by
    dsimp only
    rw [Matrix.mulVec_mulVec, Units.mul_inv, Matrix.one_mulVec]
  map_add' x y := Matrix.mulVec_add _ x y
  map_smul' a x := Matrix.mulVec_smul _ a x

def unitaryNaturalLinearEquiv (q : CFSG.PrimePower) (r : ℕ) (g : naturalFixed r q) :
    (Fin (r + 1) → q.Extension 2) ≃ₗ[q.Extension 2] (Fin (r + 1) → q.Extension 2) :=
  matrixUnitLinearEquiv g.val.val

theorem unitaryNaturalLinearEquiv_apply (q : CFSG.PrimePower) (r : ℕ)
    (g : naturalFixed r q) (x : Fin (r + 1) → q.Extension 2) :
    unitaryNaturalLinearEquiv q r g x = (g.val.val : Mat (q.Extension 2) r) *ᵥ x := rfl

theorem unitaryNaturalLinearEquiv_pair (q : CFSG.PrimePower) (r : ℕ)
    (g : naturalFixed r q) (x y : Fin (r + 1) → q.Extension 2) :
    unitaryNaturalPair q r (unitaryNaturalLinearEquiv q r g x)
      (unitaryNaturalLinearEquiv q r g y) = unitaryNaturalPair q r x y :=
  hermitianPair_isometry _ _ _ (naturalFixed_signedForm q r g) x y

def unitarySubspaceImage (q : CFSG.PrimePower) (r : ℕ) (g : naturalFixed r q)
    (S : Submodule (q.Extension 2) (Fin (r + 1) → q.Extension 2)) :
    Submodule (q.Extension 2) (Fin (r + 1) → q.Extension 2) :=
  S.map (unitaryNaturalLinearEquiv q r g).toLinearMap

theorem unitarySubspaceImage_pair_zero (q : CFSG.PrimePower) (r : ℕ)
    (g : naturalFixed r q) (S : Submodule (q.Extension 2) (Fin (r + 1) → q.Extension 2))
    (hS : ∀ x ∈ S, ∀ y ∈ S, unitaryNaturalPair q r x y = 0) :
    ∀ x ∈ unitarySubspaceImage q r g S, ∀ y ∈ unitarySubspaceImage q r g S,
      unitaryNaturalPair q r x y = 0 := by
  rintro x ⟨v, hv, rfl⟩ y ⟨w, hw, rfl⟩
  exact (unitaryNaturalLinearEquiv_pair q r g v w).trans (hS v hv w hw)

private theorem middleArray_head {K J : Type*} [Field K] [Fintype J]
    (A : Matrix J J K) :
    middleArray A *ᵥ (headVector : Index J → K) = headVector := by
  ext (u | (i | u)) <;>
    simp [Matrix.mulVec, dotProduct, middleArray, headVector, Fintype.sum_sum_type]

private theorem middleArray_middle {K J : Type*} [Field K] [Fintype J]
    (A : Matrix J J K) (v : J → K) :
    middleArray A *ᵥ middleVector v = middleVector (A *ᵥ v) := by
  ext (u | (i | u)) <;>
    simp [Matrix.mulVec, dotProduct, middleArray, middleVector, Fintype.sum_sum_type]

theorem unitaryMiddle_action_head (q : CFSG.PrimePower) (s : ℕ)
    (g : naturalFixed s q) :
    unitaryNaturalLinearEquiv q (s + 2) (naturalFixedMiddleHom q s g)
      (Pi.single (0 : Fin (s + 3)) 1) = Pi.single 0 1 := by
  apply (unitarySplitLinearEquiv q s).injective
  ext p
  change ((naturalMiddleUnitHom (q.Extension 2) s g.val.val : Mat (q.Extension 2) (s + 2)) *ᵥ
    Pi.single (0 : Fin (s + 3)) 1) (splitEquiv s p) = _
  rw [naturalMiddleUnitHom_val, reindex_mulVec_apply]
  change (middleArray (g.val.val : Mat (q.Extension 2) s) *ᵥ
    (unitarySplitLinearEquiv q s (Pi.single (0 : Fin (s + 3)) 1))) p = _
  rw [unitarySplit_head, middleArray_head]

theorem unitaryMiddle_action_middle (q : CFSG.PrimePower) (s : ℕ)
    (g : naturalFixed s q) (v : Fin (s + 1) → q.Extension 2) :
    unitaryNaturalLinearEquiv q (s + 2) (naturalFixedMiddleHom q s g)
      (unitaryMiddleVector q s v) =
        unitaryMiddleVector q s (unitaryNaturalLinearEquiv q s g v) := by
  apply (unitarySplitLinearEquiv q s).injective
  have hs (w : Fin (s + 1) → q.Extension 2) :
      unitarySplitLinearEquiv q s (unitaryMiddleVector q s w) = middleVector w :=
    (unitarySplitLinearEquiv q s).apply_symm_apply _
  rw [hs]
  ext p
  change ((naturalMiddleUnitHom (q.Extension 2) s g.val.val : Mat (q.Extension 2) (s + 2)) *ᵥ
    unitaryMiddleVector q s v) (splitEquiv s p) = _
  rw [naturalMiddleUnitHom_val, reindex_mulVec_apply]
  change (middleArray (g.val.val : Mat (q.Extension 2) s) *ᵥ
    (unitarySplitLinearEquiv q s (unitaryMiddleVector q s v))) p = _
  rw [hs, middleArray_middle]
  rfl

end SymmetricSubgroupAsymptotics.CFSGTwistedAUnitaryCoordinates
