import SymmetricSubgroupAsymptotics.PermutationBinaryOrbitSection

/-!
# Orbit filtration from arbitrary local head bounds

Restriction to all literal orbits jointly separates a permutation
subrepresentation.  This file packages the resulting filtration without a
prime-power assumption: any supplied head bound on each transitive orbit
adds across the actual orbit partition.  A weighted local bound therefore
gives the same weighted bound for every trivial quotient.
-/

set_option autoImplicit false
noncomputable section
open scoped BigOperators Classical
attribute [local instance] Fintype.ofFinite

namespace SymmetricSubgroupAsymptotics

variable {k G X W : Type} [Field k] [Group G] [MulAction G X]
    [AddCommGroup W] [Module k W]

/-- Arbitrary transitive-orbit head bounds add for an original
subrepresentation, with all orbit restrictions retained simultaneously. -/
theorem permutationSubrepresentationHead_le_orbit_caps
    [Finite G] [Finite X]
    (cap : MulAction.orbitRel.Quotient G X → ℕ)
    (hcap : ∀ (o : MulAction.orbitRel.Quotient G X)
      (S : Subrepresentation (permutationFunctionRepresentation k G o.orbit)),
      Module.finrank k (S.toRepresentation.IntertwiningMap
        (Representation.trivial k G k)) ≤ cap o)
    (M : Subrepresentation (permutationFunctionRepresentation k G X)) :
    Module.finrank k (M.toRepresentation.IntertwiningMap
      (Representation.trivial k G k)) ≤ ∑ o, cap o := by
  apply representationHom_finrank_le_coordinates
    (fun o : MulAction.orbitRel.Quotient G X => o.orbit → k)
    M.toRepresentation (fun o => permutationFunctionRepresentation k G o.orbit)
    (Representation.trivial k G k) cap hcap
    (permutationSubrepresentationOrbitRestriction M)
    (permutationSubrepresentationOrbitRestriction_jointly_injective M)

/-- The same additive bound for a literal trivial quotient of an original
permutation subrepresentation. -/
theorem permutation_trivial_quotient_finrank_le_orbit_caps
    [Finite G] [Finite X]
    (cap : MulAction.orbitRel.Quotient G X → ℕ)
    (hcap : ∀ (o : MulAction.orbitRel.Quotient G X)
      (S : Subrepresentation (permutationFunctionRepresentation k G o.orbit)),
      Module.finrank k (S.toRepresentation.IntertwiningMap
        (Representation.trivial k G k)) ≤ cap o)
    (M : Subrepresentation (permutationFunctionRepresentation k G X))
    (q : M.toSubmodule →ₗ[k] W) (hq : Function.Surjective q)
    (htrivial : ∀ (g : G) (m : M.toSubmodule),
      q (M.toRepresentation g m) = q m) :
    Module.finrank k W ≤ ∑ o, cap o := by
  let q' : M.toRepresentation.Coinvariants →ₗ[k] W :=
    Representation.Coinvariants.lift M.toRepresentation q (by
      intro g
      apply LinearMap.ext
      exact htrivial g)
  have hq' : Function.Surjective q' := by
    intro w
    obtain ⟨m, hm⟩ := hq w
    exact ⟨Representation.Coinvariants.mk M.toRepresentation m, hm⟩
  have hdim := LinearMap.finrank_le_finrank_of_surjective hq'
  rw [← representationHead_finrank_eq_coinvariants] at hdim
  exact hdim.trans
    (permutationSubrepresentationHead_le_orbit_caps cap hcap M)

/-- A weighted local capacity on every actual orbit gives the identical
weighted capacity for every trivial quotient of the full permutation
subrepresentation. -/
theorem permutation_trivial_quotient_weighted_finrank_le
    [Finite G] [Finite X]
    (a b : ℕ)
    (cap : MulAction.orbitRel.Quotient G X → ℕ)
    (hcap : ∀ (o : MulAction.orbitRel.Quotient G X)
      (S : Subrepresentation (permutationFunctionRepresentation k G o.orbit)),
      Module.finrank k (S.toRepresentation.IntertwiningMap
        (Representation.trivial k G k)) ≤ cap o)
    (hweight : ∀ o : MulAction.orbitRel.Quotient G X,
      b * cap o ≤ a * Nat.card o.orbit)
    (M : Subrepresentation (permutationFunctionRepresentation k G X))
    (q : M.toSubmodule →ₗ[k] W) (hq : Function.Surjective q)
    (htrivial : ∀ (g : G) (m : M.toSubmodule),
      q (M.toRepresentation g m) = q m) :
    b * Module.finrank k W ≤ a * Nat.card X := by
  have hb := permutation_trivial_quotient_finrank_le_orbit_caps
    cap hcap M q hq htrivial
  have horbits :
      ∑ o : MulAction.orbitRel.Quotient G X, Nat.card o.orbit = Nat.card X := by
    rw [← Nat.card_sigma]
    exact Nat.card_congr (MulAction.selfEquivSigmaOrbits' G X).symm
  calc
    b * Module.finrank k W ≤ b * ∑ o, cap o := Nat.mul_le_mul_left b hb
    _ = ∑ o : MulAction.orbitRel.Quotient G X, b * cap o := by
      rw [Finset.mul_sum]
    _ ≤ ∑ o : MulAction.orbitRel.Quotient G X, a * Nat.card o.orbit :=
      Finset.sum_le_sum fun o _ => hweight o
    _ = a * ∑ o : MulAction.orbitRel.Quotient G X, Nat.card o.orbit := by
      rw [Finset.mul_sum]
    _ = a * Nat.card X := by rw [horbits]

end SymmetricSubgroupAsymptotics

end
