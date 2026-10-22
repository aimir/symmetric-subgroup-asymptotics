import SymmetricSubgroupAsymptotics.CFSGTwistedDNaturalQuadraticTwist

/-! Every coordinate except the final paired coordinates is literally
fixed by the coefficient automorphism on the actual fixed-vector carrier. -/
set_option autoImplicit false
noncomputable section
namespace SymmetricSubgroupAsymptotics.CFSGTwistedDFixedVectorCoordinates
open CFSGOrthogonalDSerreMatrices CFSGOrthogonalDGenerationForkTorus
open CFSGTwistedDNaturalFork CFSGTwistedDNaturalQuadraticTwist

theorem positive_fixed (K : Type) [Field K] (s : ℕ) (σ : K ≃+* K)
    (v : Index (s + 2) → K) (hv : vectorTwist K s σ v = v)
    (i : Fin (s + 2)) (hi : i ≠ last s) :
    σ (v (Sum.inl i)) = v (Sum.inl i) := by
  have h := congrFun hv (Sum.inl i)
  change σ (v (CFSGOrthogonalDGenerationForkTorus.flip s (Sum.inl i))) = _ at h
  rw [flip_pos, if_neg hi] at h
  exact h

theorem negative_fixed (K : Type) [Field K] (s : ℕ) (σ : K ≃+* K)
    (v : Index (s + 2) → K) (hv : vectorTwist K s σ v = v)
    (i : Fin (s + 2)) (hi : i ≠ last s) :
    σ (v (Sum.inr i)) = v (Sum.inr i) := by
  have h := congrFun hv (Sum.inr i)
  change σ (v (CFSGOrthogonalDGenerationForkTorus.flip s (Sum.inr i))) = _ at h
  rw [flip_neg, if_neg hi] at h
  exact h

end SymmetricSubgroupAsymptotics.CFSGTwistedDFixedVectorCoordinates
