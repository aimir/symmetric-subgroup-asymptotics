import SymmetricSubgroupAsymptotics.CFSGHermitianHyperbolicCompression
import SymmetricSubgroupAsymptotics.CFSGTwistedAUnitaryRootAxisPairing
import SymmetricSubgroupAsymptotics.CFSGTwistedAUnitaryNaturalMiddle

/-! The hyperbolic compression on the SAME natural signed-reversal
coordinates. The compressed space uses the original smaller signed
form, with its displayed minus sign. These identities apply in every
characteristic, including binary fields. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
open scoped Matrix

namespace SymmetricSubgroupAsymptotics.CFSGTwistedAUnitaryCoordinates
open CFSGTwistedANaturalMatrices CFSGTwistedAUpperUnipotent
open CFSGTwistedAUnitaryUpperArrays CFSGTwistedAUnitaryParameters
open CFSGSerreOrdinaryTwists CFSGHermitianHyperbolicCompression
open CFSGTwistedAUnitaryNaturalRadical

def unitarySplitLinearEquiv (q : CFSG.PrimePower) (s : ℕ) :
    (Fin (s + 3) → q.Extension 2) ≃ₗ[q.Extension 2] (Index (Fin (s + 1)) → q.Extension 2) where
  toFun x := x ∘ splitEquiv s
  invFun x := x ∘ (splitEquiv s).symm
  left_inv x := by ext i; simp
  right_inv x := by ext i; simp
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

def unitaryMiddleVector (q : CFSG.PrimePower) (s : ℕ) :
    (Fin (s + 1) → q.Extension 2) →ₗ[q.Extension 2] (Fin (s + 3) → q.Extension 2) :=
  (unitarySplitLinearEquiv q s).symm.toLinearMap.comp middleVector

def unitaryMiddleProjection (q : CFSG.PrimePower) (s : ℕ) :
    (Fin (s + 3) → q.Extension 2) →ₗ[q.Extension 2] (Fin (s + 1) → q.Extension 2) :=
  middleProjection.comp (unitarySplitLinearEquiv q s).toLinearMap

theorem unitaryMiddleProjection_middleVector (q : CFSG.PrimePower) (s : ℕ)
    (v : Fin (s + 1) → q.Extension 2) :
    unitaryMiddleProjection q s (unitaryMiddleVector q s v) = v := by
  change middleProjection ((unitarySplitLinearEquiv q s)
    ((unitarySplitLinearEquiv q s).symm (middleVector v))) = v
  rw [LinearEquiv.apply_symm_apply]
  rfl

theorem unitaryMiddleVector_injective (q : CFSG.PrimePower) (s : ℕ) :
    Function.Injective (unitaryMiddleVector q s) := by
  intro v w h
  simpa only [unitaryMiddleProjection_middleVector] using
    congrArg (unitaryMiddleProjection q s) h

theorem unitarySplit_head (q : CFSG.PrimePower) (s : ℕ) :
    unitarySplitLinearEquiv q s (Pi.single (0 : Fin (s + 3)) 1) = headVector := by
  ext (u | (i | u))
  · cases u
    simp [unitarySplitLinearEquiv, headVector, splitEquiv, splitIndex]
  · have hn : (splitEquiv s) (.inr (.inl i)) ≠ 0 := by
      intro h
      have hv := congrArg (fun j : Fin (s + 3) => j.val) h
      change i.val + 1 = 0 at hv
      omega
    simp [unitarySplitLinearEquiv, headVector, hn]
  · cases u
    have hn : (Fin.last (s + 2) : Fin (s + 3)) ≠ 0 := by
      intro h
      have hv := congrArg (fun j : Fin (s + 3) => j.val) h
      change s + 2 = 0 at hv
      omega
    simp [unitarySplitLinearEquiv, headVector, splitEquiv, splitIndex, hn]

theorem unitaryNaturalPair_split (q : CFSG.PrimePower) (s : ℕ)
    (x y : Fin (s + 3) → q.Extension 2) :
    unitaryNaturalPair q (s + 2) x y =
      hermitianPair (definingFieldAutomorphism q 2)
        (blockForm (parity q s) (middleForm q s))
        (unitarySplitLinearEquiv q s x) (unitarySplitLinearEquiv q s y) := by
  have h := hermitianPair_reindex (definingFieldAutomorphism q 2) (splitEquiv s)
    (blockForm (parity q s) (middleForm q s)) x y
  dsimp only [parity, middleForm] at h
  rw [blockForm_reindex] at h
  exact h

theorem unitaryMiddleVector_pair (q : CFSG.PrimePower) (s : ℕ)
    (v w : Fin (s + 1) → q.Extension 2) :
    unitaryNaturalPair q (s + 2) (unitaryMiddleVector q s v) (unitaryMiddleVector q s w) =
      -unitaryNaturalPair q s v w := by
  rw [unitaryNaturalPair_split]
  change hermitianPair _ _
    ((unitarySplitLinearEquiv q s) ((unitarySplitLinearEquiv q s).symm (middleVector v)))
    ((unitarySplitLinearEquiv q s) ((unitarySplitLinearEquiv q s).symm (middleVector w))) = _
  rw [LinearEquiv.apply_symm_apply, LinearEquiv.apply_symm_apply, middle_pair]
  change dotProduct _ ((-(signedReversalUnit (q.Extension 2) s : Mat (q.Extension 2) s)) *ᵥ w) = _
  rw [Matrix.neg_mulVec, dotProduct_neg]
  rfl

theorem unitary_vector_decomposition (q : CFSG.PrimePower) (s : ℕ)
    (x : Fin (s + 3) → q.Extension 2) (hx : x (Fin.last (s + 2)) = 0) :
    x = x 0 • Pi.single (0 : Fin (s + 3)) 1 +
      unitaryMiddleVector q s (unitaryMiddleProjection q s x) := by
  apply (unitarySplitLinearEquiv q s).injective
  rw [map_add, map_smul, unitarySplit_head]
  change unitarySplitLinearEquiv q s x = x 0 • headVector +
    (unitarySplitLinearEquiv q s)
      ((unitarySplitLinearEquiv q s).symm
        (middleVector (middleProjection (unitarySplitLinearEquiv q s x))))
  rw [LinearEquiv.apply_symm_apply]
  exact vector_decomposition (unitarySplitLinearEquiv q s x) hx

def unitaryCompressedSpace (q : CFSG.PrimePower) (s : ℕ)
    (S : Submodule (q.Extension 2) (Fin (s + 3) → q.Extension 2)) :
    Submodule (q.Extension 2) (Fin (s + 1) → q.Extension 2) :=
  S.comap (unitaryMiddleVector q s)

theorem unitary_compressed_pair_zero (q : CFSG.PrimePower) (s : ℕ)
    (S : Submodule (q.Extension 2) (Fin (s + 3) → q.Extension 2))
    (hS : ∀ x ∈ S, ∀ y ∈ S, unitaryNaturalPair q (s + 2) x y = 0) :
    ∀ v ∈ unitaryCompressedSpace q s S, ∀ w ∈ unitaryCompressedSpace q s S,
      unitaryNaturalPair q s v w = 0 := by
  intro v hv w hw
  have h := hS (unitaryMiddleVector q s v) hv (unitaryMiddleVector q s w) hw
  rw [unitaryMiddleVector_pair] at h
  exact neg_eq_zero.mp h

theorem unitary_middleProjection_mem (q : CFSG.PrimePower) (s : ℕ)
    (S : Submodule (q.Extension 2) (Fin (s + 3) → q.Extension 2))
    (he : Pi.single (0 : Fin (s + 3)) 1 ∈ S)
    (hS : ∀ x ∈ S, ∀ y ∈ S, unitaryNaturalPair q (s + 2) x y = 0)
    (x : Fin (s + 3) → q.Extension 2) (hx : x ∈ S) :
    unitaryMiddleProjection q s x ∈ unitaryCompressedSpace q s S := by
  change unitaryMiddleVector q s (unitaryMiddleProjection q s x) ∈ S
  have hz : x (Fin.last (s + 2)) = 0 := by
    simpa only [unitaryNaturalPair_first] using hS _ he x hx
  have hmem := S.sub_mem hx (S.smul_mem (x 0) he)
  have heq : x - x 0 • Pi.single (0 : Fin (s + 3)) 1 =
      unitaryMiddleVector q s (unitaryMiddleProjection q s x) :=
    sub_eq_iff_eq_add.mpr ((unitary_vector_decomposition q s x hz).trans (add_comm _ _))
  rw [← heq]
  exact hmem

end SymmetricSubgroupAsymptotics.CFSGTwistedAUnitaryCoordinates
