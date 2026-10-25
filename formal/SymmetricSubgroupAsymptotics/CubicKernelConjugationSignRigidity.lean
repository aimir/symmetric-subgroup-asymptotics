import SymmetricSubgroupAsymptotics.OddMarker

/-! Two genuine cubic coordinate homomorphisms with the SAME kernel
see the same binary sign of an ambient conjugator. The proof compares
its commutator with one actual element nontrivial in both coordinates;
no unrelated cubic generator, field action, or kernel independence is
introduced. Only two tiny natural-S3/binary scalar identities are finite. -/
set_option autoImplicit false
noncomputable section
namespace SymmetricSubgroupAsymptotics.CubicKernelConjugationSignRigidity

private theorem cubic_commutator_sign : ∀ a x : OddMarkerGroup,
    x^3 = 1 → x ≠ 1 →
      (a*x*a⁻¹*x⁻¹ = 1 ↔ oddMarkerSign a = 1) := by
  decide +kernel

private theorem binary_eq_of_one_iff : ∀ s t : Multiplicative (ZMod 2),
    (s = 1 ↔ t = 1) → s = t := by
  decide +kernel

theorem sign_eq_of_common_cubic_kernel {K : Type*} [Group K]
    (f g : K →* OddMarkerGroup) (hker : f.ker = g.ker)
    (hf : ∀ u : K, f u ^ 3 = 1) (hg : ∀ u : K, g u ^ 3 = 1)
    (hne : ∃ u : K, f u ≠ 1) (alpha : MulAut K) (a b : OddMarkerGroup)
    (hfa : ∀ u : K, f (alpha u) = a*f u*a⁻¹)
    (hgb : ∀ u : K, g (alpha u) = b*g u*b⁻¹) :
    oddMarkerSign a = oddMarkerSign b := by
  have hiff (u : K) : f u = 1 ↔ g u = 1 := by
    change u ∈ f.ker ↔ u ∈ g.ker
    rw [hker]
  obtain ⟨u,hu⟩ := hne
  have hgu : g u ≠ 1 := fun h => hu ((hiff u).mpr h)
  have hcomm : a*f u*a⁻¹*(f u)⁻¹ = 1 ↔ b*g u*b⁻¹*(g u)⁻¹ = 1 := by
    have hh := hiff (alpha u*u⁻¹)
    simpa only [map_mul,map_inv,hfa,hgb] using hh
  have hsign : oddMarkerSign a = 1 ↔ oddMarkerSign b = 1 :=
    (cubic_commutator_sign a (f u) (hf u) hu).symm.trans
      (hcomm.trans (cubic_commutator_sign b (g u) (hg u) hgu))
  exact binary_eq_of_one_iff _ _ hsign

end SymmetricSubgroupAsymptotics.CubicKernelConjugationSignRigidity
