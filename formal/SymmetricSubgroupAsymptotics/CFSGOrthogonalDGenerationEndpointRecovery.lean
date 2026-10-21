import SymmetricSubgroupAsymptotics.CFSGOrthogonalDGenerationFirstEndpoint
import SymmetricSubgroupAsymptotics.CFSGOrthogonalDGenerationSecondExtraction

/-! Both actual endpoint geometries recover the original short line
and pure Weyl word. The temporary whole-subgroup conjugation in the second
case is undone on the short line by its own additive commutation law. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
namespace SymmetricSubgroupAsymptotics.CFSGOrthogonalDGenerationEndpointRecovery
open Matrix CFSGOrthogonalDSerreMatrices CFSGOrthogonalDBinaryElements
open CFSGOrthogonalDGenerationInitialElements CFSGOrthogonalDGenerationForkTorus
open CFSGOrthogonalDGenerationInitialRootMatrices CFSGOrthogonalDGenerationRootLineTransport
open CFSGOrthogonalDGenerationSignedRootConjugation CFSGOrthogonalDGenerationCleanedOrbit
open CFSGOrthogonalDGenerationFirstEndpoint CFSGOrthogonalDGenerationSecondEndpoint
open CFSGOrthogonalDGenerationSecondExtraction
variable (K : Type) [Field K] [Finite K]

theorem second_endpoint_recovery (s : ℕ) (hcard : 3 ≤ Nat.card K)
    (g : Kˣ) (hg : ∀ u : Kˣ, u ∈ Subgroup.zpowers g)
    (H : Subgroup (Mat K (s + 4))ˣ)
    (hY : (initialShortRoot K s 1).val * (coxeterWeyl K (s + 3)).val ∈ H)
    (hB : HasRootLine H (rootArray K (Sum.inl (second s)) (Sum.inr (last (s + 2)))))
    (hD : HasRootLine H
      (rootArray K (Sum.inr (0 : Fin (s + 4))) (Sum.inr (last (s + 2))))) :
    (∀ a, (initialShortRoot K s a).val ∈ H) ∧ (coxeterWeyl K (s + 3)).val ∈ H := by
  obtain ⟨hpos, hneg, hWA⟩ := second_endpoint_data K s H hY hB hD
  have hrec := star_data_extract_short K s hcard g hg (conjugatedSubgroup K s H) hpos hneg hWA
  have hA : ∀ a, (initialShortRoot K s a).val ∈ H := by
    intro a
    have ha := hrec.1 a
    change (initialShortRoot K s 1).val * (initialShortRoot K s a).val *
      (initialShortRoot K s 1).val⁻¹ ∈ H at ha
    have he : initialShortRoot K s 1 * initialShortRoot K s a =
        initialShortRoot K s a * initialShortRoot K s 1 := by
      rw [← initialShortRoot_add, ← initialShortRoot_add]
      exact congrArg (initialShortRoot K s) (add_comm (1 : K) a)
    have hc := congrArg Subtype.val he
    change (initialShortRoot K s 1).val * (initialShortRoot K s a).val =
      (initialShortRoot K s a).val * (initialShortRoot K s 1).val at hc
    rw [hc, mul_assoc, mul_inv_cancel, mul_one] at ha
    exact ha
  refine ⟨hA, ?_⟩
  have hw := H.mul_mem (H.inv_mem (hA 1)) hY
  simpa only [inv_mul_cancel_left] using hw

theorem recover_short_and_weyl (s : ℕ) (hcard : 3 ≤ Nat.card K)
    (g : Kˣ) (hg : ∀ u : Kˣ, u ∈ Subgroup.zpowers g)
    (H : Subgroup (Mat K (s + 4))ˣ)
    (hY : (initialShortRoot K s 1).val * (coxeterWeyl K (s + 3)).val ∈ H)
    (hB : HasRootLine H (rootArray K (Sum.inl (second s)) (Sum.inr (last (s + 2))))) :
    (∀ a, (initialShortRoot K s a).val ∈ H) ∧ (coxeterWeyl K (s + 3)).val ∈ H := by
  obtain ⟨side, hD⟩ := endpoint_line K s H hY hB
  cases side
  · exact first_endpoint_recovery K s H hY hB hD
  · exact second_endpoint_recovery K s hcard g hg H hY hB hD

end SymmetricSubgroupAsymptotics.CFSGOrthogonalDGenerationEndpointRecovery
