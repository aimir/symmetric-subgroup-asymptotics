import SymmetricSubgroupAsymptotics.CFSGHermitianTwoByTwoCentroid

/-! Literal fixed-scalar rank-one root lines inside the actual Hermitian
coefficient group. Their common additive centroid is proved to be the
fixed-scalar endomorphisms, and conjugation by a root-line permutation
therefore transports actual scalars to actual scalars. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
open scoped Matrix

namespace SymmetricSubgroupAsymptotics.CFSGHermitianTwoByTwoRankOne
variable {K : Type*} [Field K]

theorem rankOneParameter_add (sigma : K ≃+* K) (hsigma : ∀ x, sigma (sigma x) = x)
    (a b : K) (ha : sigma a = a) (hb : sigma b = b) (v : Fin 2 → K) :
    rankOneParameter sigma hsigma (a + b) (by rw [map_add, ha, hb]) v =
      rankOneParameter sigma hsigma a ha v + rankOneParameter sigma hsigma b hb v := by
  apply Subtype.ext
  ext i j
  change (a + b) * v i * sigma (v j) = a * v i * sigma (v j) + b * v i * sigma (v j)
  ring

def rankOneLine (sigma : K ≃+* K) (hsigma : ∀ x, sigma (sigma x) = x)
    (v : Fin 2 → K) : AddSubgroup (parameters sigma) where
  carrier := {A | ∃ (a : K) (ha : sigma a = a), A = rankOneParameter sigma hsigma a ha v}
  zero_mem' := by
    refine ⟨0, map_zero sigma, ?_⟩
    apply Subtype.ext
    ext i j
    change 0 = 0 * v i * sigma (v j)
    ring
  add_mem' := by
    rintro A B ⟨a, ha, rfl⟩ ⟨b, hb, rfl⟩
    exact ⟨a + b, by rw [map_add, ha, hb], (rankOneParameter_add sigma hsigma a b ha hb v).symm⟩
  neg_mem' := by
    rintro A ⟨a, ha, rfl⟩
    refine ⟨-a, by rw [map_neg, ha], ?_⟩
    apply Subtype.ext
    ext i j
    change -(a * v i * sigma (v j)) = (-a) * v i * sigma (v j)
    ring

theorem fixedScaleHom_mem_rankOneLine (sigma : K ≃+* K)
    (hsigma : ∀ x, sigma (sigma x) = x) (c : K) (hc : sigma c = c)
    (v : Fin 2 → K) (A : parameters sigma) (hA : A ∈ rankOneLine sigma hsigma v) :
    fixedScaleHom sigma c hc A ∈ rankOneLine sigma hsigma v := by
  obtain ⟨a, ha, rfl⟩ := hA
  refine ⟨c * a, by rw [map_mul, hc, ha], ?_⟩
  apply Subtype.ext
  ext i j
  change c * (a * v i * sigma (v j)) = (c * a) * v i * sigma (v j)
  ring

theorem scalar_of_rankOneLine_invariant (sigma : K ≃+* K)
    (hsigma : ∀ x, sigma (sigma x) = x) (hnonfixed : ∃ t, sigma t ≠ t)
    (theta : K) (htheta : theta + sigma theta = 1)
    (psi : parameters sigma →+ parameters sigma)
    (hline : ∀ v A, A ∈ rankOneLine sigma hsigma v → psi A ∈ rankOneLine sigma hsigma v) :
    ∃ (c : K) (hc : sigma c = c), psi = fixedScaleHom sigma c hc := by
  apply scalar_of_rankOne_lines sigma hsigma hnonfixed theta htheta psi
  intro a ha v
  obtain ⟨b, hb, he⟩ := hline v (rankOneParameter sigma hsigma a ha v) ⟨a, ha, rfl⟩
  exact ⟨b, hb, he⟩

theorem rootLinePermutation_transports_scalars (sigma : K ≃+* K)
    (hsigma : ∀ x, sigma (sigma x) = x) (hnonfixed : ∃ t, sigma t ≠ t)
    (theta : K) (htheta : theta + sigma theta = 1)
    (E : parameters sigma ≃+ parameters sigma)
    (hback : ∀ v, ∃ w, (rankOneLine sigma hsigma v).map E.symm.toAddMonoidHom =
      rankOneLine sigma hsigma w)
    (a : K) (ha : sigma a = a) :
    ∃ (b : K) (hb : sigma b = b), ∀ A,
      E (fixedScaleHom sigma a ha A) = fixedScaleHom sigma b hb (E A) := by
  let psi : parameters sigma →+ parameters sigma := E.toAddMonoidHom.comp
    ((fixedScaleHom sigma a ha).comp E.symm.toAddMonoidHom)
  have hpsi : ∀ v A, A ∈ rankOneLine sigma hsigma v →
      psi A ∈ rankOneLine sigma hsigma v := by
    intro v A hA
    obtain ⟨w, hw⟩ := hback v
    have hi : E.symm A ∈ rankOneLine sigma hsigma w := by
      rw [← hw]
      exact ⟨A, hA, rfl⟩
    have hs := fixedScaleHom_mem_rankOneLine sigma hsigma a ha w (E.symm A) hi
    rw [← hw] at hs
    obtain ⟨B, hB, he⟩ := hs
    change E.symm B = fixedScaleHom sigma a ha (E.symm A) at he
    change E (fixedScaleHom sigma a ha (E.symm A)) ∈ rankOneLine sigma hsigma v
    rw [← he, AddEquiv.apply_symm_apply]
    exact hB
  obtain ⟨b, hb, he⟩ := scalar_of_rankOneLine_invariant sigma hsigma hnonfixed theta htheta psi hpsi
  refine ⟨b, hb, ?_⟩
  intro A
  have hh := congrArg (fun f : parameters sigma →+ parameters sigma => f (E A)) he
  change E (fixedScaleHom sigma a ha (E.symm (E A))) = fixedScaleHom sigma b hb (E A) at hh
  simpa only [AddEquiv.symm_apply_apply] using hh

end SymmetricSubgroupAsymptotics.CFSGHermitianTwoByTwoRankOne
