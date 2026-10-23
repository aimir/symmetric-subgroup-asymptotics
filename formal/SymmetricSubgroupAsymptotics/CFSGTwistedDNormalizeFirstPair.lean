import SymmetricSubgroupAsymptotics.CFSGTwistedDAllRankHyperbolicPairs
import SymmetricSubgroupAsymptotics.CFSGSplitQuadraticBasisParameters

/-! Actual defining-fixed quadratic isometries admit first-pair
normalization by literal relative-root words in every rank at least two. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
open scoped Matrix
namespace SymmetricSubgroupAsymptotics.CFSGTwistedDNormalizeFirstPair
open CFSGOrthogonalDSerreMatrices CFSGOrthogonalDGenerationForkTorus
open CFSGTwistedDRelativeElementaryGroup CFSGTwistedDNaturalQuadraticTwist
open CFSGTwistedDNaturalFieldTwist CFSGTwistedDNaturalFork CFSGSerreOrdinaryTwists
open CFSGOrthogonalDIndexQuadraticForm CFSGOrthogonalDIndexPolarForm
open CFSGOrthogonalDIndexBundledQuadratic CFSGOrthogonalDIndexPrefixPerpendicular

theorem fixed_basis (K : Type) [Field K] (n : ℕ) (σ : K ≃+* K)
    (i : Index (n + 2)) (hi : CFSGOrthogonalDGenerationForkTorus.flip n i = i) :
    vectorTwist K n σ (Pi.single i 1) = Pi.single i 1 := by
  funext x
  change σ ((Pi.single i (1 : K) : Index (n + 2) → K)
    (CFSGOrthogonalDGenerationForkTorus.flip n x)) =
      (Pi.single i (1 : K) : Index (n + 2) → K) x
  by_cases hx : x = i
  · subst x
    rw [hi]
    simp
  · have hf : CFSGOrthogonalDGenerationForkTorus.flip n x ≠ i := by
      intro h
      exact hx ((CFSGOrthogonalDGenerationForkTorus.flip n).injective (h.trans hi.symm))
    simp [Pi.single_apply, hx, hf]

theorem exists_normalize_first_pair (n : ℕ) (q : CFSG.PrimePower)
    (u : (Mat (q.Extension 2) (n + 2))ˣ)
    (hQ : u ∈ quadraticPreserving (q.Extension 2) (n + 2))
    (ht : unitTwist (q.Extension 2) n (definingFieldAutomorphism q 2) u = u) :
    ∃ a : relativeRootGroup n q,
      ((a.val * u : (Mat (q.Extension 2) (n + 2))ˣ) : Mat (q.Extension 2) (n + 2)) *ᵥ
        Pi.single (Sum.inl 0) 1 = Pi.single (Sum.inl 0) 1 ∧
      ((a.val * u : (Mat (q.Extension 2) (n + 2))ˣ) : Mat (q.Extension 2) (n + 2)) *ᵥ
        Pi.single (Sum.inr 0) 1 = Pi.single (Sum.inr 0) 1 := by
  let K := q.Extension 2
  let e : Index (n + 2) → K := Pi.single (Sum.inl 0) 1
  let f : Index (n + 2) → K := Pi.single (Sum.inr 0) 1
  have h0 : (0 : Fin (n + 2)) ≠ last n := by
    intro h
    have hv := congrArg Fin.val h
    change 0 = n + 1 at hv
    omega
  have hefix : vectorTwist K n (definingFieldAutomorphism q 2) e = e :=
    fixed_basis K n _ (Sum.inl 0) (by rw [flip_pos, if_neg h0])
  have hffix : vectorTwist K n (definingFieldAutomorphism q 2) f = f :=
    fixed_basis K n _ (Sum.inr 0) (by rw [flip_neg, if_neg h0])
  have hm := congrArg (fun g : (Mat K (n + 2))ˣ => (g : Mat K (n + 2))) ht
  have hue := CFSGTwistedDFixedVectorAction.fixed_matrix_preserves_fixed_vectors
    K n (definingFieldAutomorphism q 2) (u : Mat K (n + 2)) hm e hefix
  have huf := CFSGTwistedDFixedVectorAction.fixed_matrix_preserves_fixed_vectors
    K n (definingFieldAutomorphism q 2) (u : Mat K (n + 2)) hm f hffix
  have hQb (v : Index (n + 2) → K) :
      splitQuadraticForm K (n + 2) ((u : Mat K (n + 2)) *ᵥ v) = splitQuadraticForm K (n + 2) v := by
    rw [splitQuadraticForm_apply, splitQuadraticForm_apply]
    exact hQ v
  have heQ : splitQuadraticForm K (n + 2) e = 0 :=
    CFSGSplitQuadraticBasisParameters.positive_norm K 0 1
  have hfQ : splitQuadraticForm K (n + 2) f = 0 :=
    CFSGSplitQuadraticBasisParameters.negative_norm K 0 1
  have he0 : e ≠ 0 := by
    intro h
    have hv := congrFun h (Sum.inl 0)
    exact one_ne_zero (by simpa only [e, Pi.single_eq_same, Pi.zero_apply] using hv)
  have hue0 : (u : Mat K (n + 2)) *ᵥ e ≠ 0 := by
    intro h
    have hi := congrArg (fun v : Index (n + 2) → K => (↑(u⁻¹) : Mat K (n + 2)) *ᵥ v) h
    dsimp only at hi
    rw [Matrix.mulVec_mulVec, Units.inv_mul, Matrix.one_mulVec, Matrix.mulVec_zero] at hi
    exact he0 hi
  have hB (v w : Index (n + 2) → K) :
      polar K ((u : Mat K (n + 2)) *ᵥ v) ((u : Mat K (n + 2)) *ᵥ w) = polar K v w := by
    have h := hQ (v + w)
    rw [Matrix.mulVec_add, splitQ_add, splitQ_add, hQ v, hQ w] at h
    exact add_left_cancel h
  have hef : polar K ((u : Mat K (n + 2)) *ᵥ e) ((u : Mat K (n + 2)) *ᵥ f) = 1 := by
    rw [hB]
    change polar K (Pi.single (Sum.inl 0) 1) f = 1
    rw [polar_positive_basis]
    simp [f]
  obtain ⟨a, ha, hb⟩ := CFSGTwistedDAllRankHyperbolicPairs.exists_normalize_pair
    n q ((u : Mat K (n + 2)) *ᵥ e) ((u : Mat K (n + 2)) *ᵥ f)
    hue huf ((hQb e).trans heQ) ((hQb f).trans hfQ) hue0 hef
  refine ⟨a, ?_, ?_⟩
  · change ((a.val : Mat K (n + 2)) * (u : Mat K (n + 2))) *ᵥ e = e
    rw [← Matrix.mulVec_mulVec]
    exact ha
  · change ((a.val : Mat K (n + 2)) * (u : Mat K (n + 2))) *ᵥ f = f
    rw [← Matrix.mulVec_mulVec]
    exact hb

end SymmetricSubgroupAsymptotics.CFSGTwistedDNormalizeFirstPair
