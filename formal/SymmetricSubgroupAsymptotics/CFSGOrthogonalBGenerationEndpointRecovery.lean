import SymmetricSubgroupAsymptotics.CFSGOrthogonalBGenerationInitialExtraction
import SymmetricSubgroupAsymptotics.CFSGOrthogonalBGenerationCleanedOrbit

/-! The two purified short endpoints recover the initial long root
with its actual coefficient two, then recover the pure Coxeter word.
All subgroup witnesses remain ordinary words in the original pair. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
namespace SymmetricSubgroupAsymptotics.CFSGOrthogonalBGenerationEndpointRecovery
open CFSGOrthogonalBSerreMatrices CFSGOrthogonalBGenerationInitialElements
open CFSGOrthogonalBGenerationShortArrays CFSGOrthogonalBGenerationShortCommutator
open CFSGOrthogonalBGenerationCoxeter CFSGOrthogonalBGenerationInitialExtraction
open CFSGOrthogonalBGenerationCleanedOrbit
variable (K : Type) [Field K]

theorem endpoint_commutator (h2 : (2 : K) ≠ 0) (s : ℕ) (a : K) :
    betaUnit K s a * shortUnit K (s + 3) (Sum.inr (penIndex s)) (-(2 : K)⁻¹) *
        (betaUnit K s a)⁻¹ * (shortUnit K (s + 3) (Sum.inr (penIndex s)) (-(2 : K)⁻¹))⁻¹ =
      alphaUnit K s a := by
  have hh := short_commutator_val K (s + 3) (Sum.inl (lastIndex s)) (Sum.inr (penIndex s))
    (by intro he; cases he)
    (by
      change Sum.inl (lastIndex s) ≠ Sum.inl (penIndex s)
      exact fun he => (pen_ne_last s).symm (Sum.inl.inj he)) a (-(2 : K)⁻¹)
  have hc : -2 * a * (-(2 : K)⁻¹) = a := by
    field_simp [h2]
    all_goals ring
  have he : longArray K (s + 3) (Sum.inl (lastIndex s)) (Sum.inr (penIndex s)) =
      alphaArray K s := rfl
  have hv : ((betaUnit K s a * shortUnit K (s + 3) (Sum.inr (penIndex s)) (-(2 : K)⁻¹) *
      (betaUnit K s a)⁻¹ * (shortUnit K (s + 3) (Sum.inr (penIndex s)) (-(2 : K)⁻¹))⁻¹ :
        (Mat K (s + 3))ˣ) : Mat K (s + 3)) = 1 + a • alphaArray K s := by
    simpa only [betaUnit, hc, he] using hh
  exact Units.ext (hv.trans (alphaUnit_val K s a).symm)

theorem alpha_line_of_endpoints (h2 : (2 : K) ≠ 0) (s : ℕ)
    (H : Subgroup (Mat K (s + 3))ˣ) (hB : ∀ a, betaUnit K s a ∈ H)
    (hN : ∀ a, shortUnit K (s + 3) (Sum.inr (penIndex s)) a ∈ H) :
    ∀ a, alphaUnit K s a ∈ H := by
  intro a
  have hh := H.mul_mem (H.mul_mem (H.mul_mem (hB a) (hN (-(2 : K)⁻¹))) (H.inv_mem (hB a)))
    (H.inv_mem (hN (-(2 : K)⁻¹)))
  rw [endpoint_commutator K h2 s a] at hh
  exact hh

theorem initial_pair_short_and_weyl [Finite K] (h2 : (2 : K) ≠ 0)
    (hcard : 3 ≤ Nat.card K) (s : ℕ) (g : Kˣ) (hg : ∀ u : Kˣ, u ∈ Subgroup.zpowers g)
    (H : Subgroup (Mat K (s + 3))ˣ)
    (hT : (initialTorus K h2 s g).val ∈ H) (hY : (initialMixedWeyl K s).val ∈ H) :
    (∀ a, alphaUnit K s a ∈ H) ∧ (coxeterWeyl K (s + 2)).val ∈ H ∧
      (∀ a, betaUnit K s a ∈ H) := by
  obtain ⟨hB, hclean⟩ := beta_line_and_cleaned_word K h2 hcard s g hg H hT hY
  have hN := negative_lines_of_cleaned K s H hclean hB
  have hA := alpha_line_of_endpoints K h2 s H hB
    (hN (penIndex s) (by dsimp [penIndex]; omega))
  have hw := H.mul_mem (H.inv_mem (hA 1)) hclean
  have he : (alphaUnit K s 1)⁻¹ * (alphaUnit K s 1 * (coxeterWeyl K (s + 2)).val) =
      (coxeterWeyl K (s + 2)).val := by rw [← mul_assoc, inv_mul_cancel, one_mul]
  exact ⟨hA, he ▸ hw, hB⟩

end SymmetricSubgroupAsymptotics.CFSGOrthogonalBGenerationEndpointRecovery
