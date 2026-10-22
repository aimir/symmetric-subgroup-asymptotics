import SymmetricSubgroupAsymptotics.CFSGTwistedDNaturalFieldTwist
import SymmetricSubgroupAsymptotics.CFSGOrthogonalDIndexBundledQuadratic
import SymmetricSubgroupAsymptotics.CFSGTwistedAPairedFixedRoots

/-! The actual semilinear natural fork twist preserves the SAME split
quadratic form up to the coefficient automorphism. Its fixed last plane
has the explicit norm contribution t*sigma(t), including characteristic
two; no polar-zero replacement or fixed-group recognition is used. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
namespace SymmetricSubgroupAsymptotics.CFSGTwistedDNaturalQuadraticTwist
open CFSGOrthogonalDSerreMatrices CFSGOrthogonalDGenerationForkTorus
open CFSGTwistedDNaturalFork CFSGOrthogonalDIndexBundledQuadratic
open CFSGOrthogonalDIndexQuadraticForm
variable (K : Type) [Field K]

def vectorTwist (s : ℕ) (σ : K ≃+* K) (v : Index (s + 2) → K) : Index (s + 2) → K :=
  fun x => σ (v (CFSGOrthogonalDGenerationForkTorus.flip s x))

theorem vectorTwist_involutive (s : ℕ) (σ : K ≃+* K) (hσ : Function.Involutive σ) :
    Function.Involutive (vectorTwist K s σ) := by
  intro v
  funext x
  change σ (σ (v (CFSGOrthogonalDGenerationForkTorus.flip s
    (CFSGOrthogonalDGenerationForkTorus.flip s x)))) = v x
  simp only [CFSGOrthogonalDGenerationForkTorus.flip, Equiv.swap_apply_self]
  exact hσ (v x)

theorem quadratic_covariance (s : ℕ) (σ : K ≃+* K) (v : Index (s + 2) → K) :
    splitQuadraticForm K (s + 2) (vectorTwist K s σ v) =
      σ (splitQuadraticForm K (s + 2) v) := by
  simp only [splitQuadraticForm_apply]
  change (∑ i : Fin (s + 2),
    σ (v (CFSGOrthogonalDGenerationForkTorus.flip s (Sum.inl i))) *
      σ (v (CFSGOrthogonalDGenerationForkTorus.flip s (Sum.inr i)))) =
    σ (∑ i : Fin (s + 2), v (Sum.inl i) * v (Sum.inr i))
  rw [map_sum]
  apply Finset.sum_congr rfl
  intro i _
  rw [flip_pos, flip_neg, map_mul]
  by_cases hi : i = last s
  · simp only [if_pos hi, mul_comm]
  · simp only [if_neg hi]

theorem fixed_last_pair (s : ℕ) (σ : K ≃+* K) (v : Index (s + 2) → K)
    (hv : vectorTwist K s σ v = v) :
    v (Sum.inr (last s)) = σ (v (Sum.inl (last s))) := by
  have h := congrFun hv (Sum.inr (last s))
  change σ (v (CFSGOrthogonalDGenerationForkTorus.flip s (Sum.inr (last s)))) = _ at h
  rw [flip_neg, if_pos rfl] at h
  exact h.symm

theorem fixed_last_norm (s : ℕ) (σ : K ≃+* K) (v : Index (s + 2) → K)
    (hv : vectorTwist K s σ v = v) :
    v (Sum.inl (last s)) * v (Sum.inr (last s)) =
      v (Sum.inl (last s)) * σ (v (Sum.inl (last s))) := by
  rw [fixed_last_pair K s σ v hv]

theorem defining_vectorTwist_involutive (s : ℕ) (q : CFSG.PrimePower) :
    Function.Involutive (vectorTwist (q.Extension 2) s
      (CFSGSerreOrdinaryTwists.definingFieldAutomorphism q 2)) :=
  vectorTwist_involutive (q.Extension 2) s _
    (fun x => CFSGTwistedANaturalMatrices.extension_two_pow_twice q x)

end SymmetricSubgroupAsymptotics.CFSGTwistedDNaturalQuadraticTwist
