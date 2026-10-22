import SymmetricSubgroupAsymptotics.CFSGTwistedDDerivedFixed
import SymmetricSubgroupAsymptotics.CFSGTwistedDNaturalQuadraticTwist

/-! The actual original Derived natural preimage acts on the literal
fixed-vector carrier. This follows from checked matrix fixedness, not
from a presumed identification with a nonsplit classical group. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
open scoped Matrix
namespace SymmetricSubgroupAsymptotics.CFSGTwistedDFixedVectorAction
open CFSGOrthogonalDSerreMatrices CFSGOrthogonalDGenerationForkTorus
open CFSGTwistedDNaturalFieldTwist CFSGTwistedDNaturalQuadraticTwist
open CFSGTwistedDDerivedPairedRoots

theorem mulVec_covariance (K : Type) [Field K] (s : ℕ) (σ : K ≃+* K)
    (M : Mat K (s + 2)) (v : Index (s + 2) → K) :
    matrixTwist K s σ M *ᵥ vectorTwist K s σ v = vectorTwist K s σ (M *ᵥ v) := by
  change (M.map σ).submatrix (CFSGOrthogonalDGenerationForkTorus.flip s).symm
      (CFSGOrthogonalDGenerationForkTorus.flip s).symm *ᵥ vectorTwist K s σ v = _
  rw [Matrix.submatrix_mulVec_equiv]
  have hc : vectorTwist K s σ v ∘ CFSGOrthogonalDGenerationForkTorus.flip s = σ ∘ v := by
    funext x
    simp only [Function.comp_apply, vectorTwist, CFSGOrthogonalDGenerationForkTorus.flip,
      Equiv.swap_apply_self]
  simp only [Equiv.symm_symm]
  rw [hc]
  funext x
  change (M.map σ *ᵥ (σ ∘ v)) ((CFSGOrthogonalDGenerationForkTorus.flip s).symm x) =
    σ ((M *ᵥ v) (CFSGOrthogonalDGenerationForkTorus.flip s x))
  rw [show (CFSGOrthogonalDGenerationForkTorus.flip s).symm =
      CFSGOrthogonalDGenerationForkTorus.flip s from Equiv.symm_swap _ _]
  exact (σ.toRingHom.map_mulVec M v _).symm

theorem fixed_matrix_preserves_fixed_vectors (K : Type) [Field K] (s : ℕ) (σ : K ≃+* K)
    (M : Mat K (s + 2)) (hM : matrixTwist K s σ M = M)
    (v : Index (s + 2) → K) (hv : vectorTwist K s σ v = v) :
    vectorTwist K s σ (M *ᵥ v) = M *ᵥ v := by
  have h := mulVec_covariance K s σ M v
  rw [hM, hv] at h
  exact h.symm

theorem derived_preserves_fixed_vectors (s : ℕ) (q : CFSG.PrimePower)
    (u : naturalDerivedPreimage s q) (v : Index (s + 4) → q.Extension 2)
    (hv : vectorTwist (q.Extension 2) (s + 2)
      (CFSGSerreOrdinaryTwists.definingFieldAutomorphism q 2) v = v) :
    vectorTwist (q.Extension 2) (s + 2) (CFSGSerreOrdinaryTwists.definingFieldAutomorphism q 2)
      ((u.val.val : Mat (q.Extension 2) (s + 4)) *ᵥ v) =
        (u.val.val : Mat (q.Extension 2) (s + 4)) *ᵥ v :=
  fixed_matrix_preserves_fixed_vectors (q.Extension 2) (s + 2)
    (CFSGSerreOrdinaryTwists.definingFieldAutomorphism q 2) _
    (CFSGTwistedDDerivedFixed.derived_preimage_matrix_fixed s q u) v hv

end SymmetricSubgroupAsymptotics.CFSGTwistedDFixedVectorAction
