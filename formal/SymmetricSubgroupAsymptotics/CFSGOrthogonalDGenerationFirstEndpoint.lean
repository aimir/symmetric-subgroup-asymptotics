import SymmetricSubgroupAsymptotics.CFSGOrthogonalDGenerationCleanedOrbit
import SymmetricSubgroupAsymptotics.CFSGOrthogonalDGenerationRootLineCommutators

/-! In the first actual endpoint geometry the plus/minus root
commutator recovers the entire original short-root line. Cancellation
then recovers the pure original Weyl word inside the same subgroup. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
namespace SymmetricSubgroupAsymptotics.CFSGOrthogonalDGenerationFirstEndpoint
open Matrix CFSGOrthogonalDSerreMatrices CFSGOrthogonalDBinaryElements
open CFSGOrthogonalDGenerationInitialElements CFSGOrthogonalDGenerationForkTorus
open CFSGOrthogonalDGenerationInitialRootMatrices CFSGOrthogonalDGenerationRootArrays
open CFSGOrthogonalDGenerationSignedRootConjugation CFSGOrthogonalDBinaryCyclePermutation
open CFSGOrthogonalDGenerationRootLineTransport CFSGOrthogonalDGenerationRootLineCommutators
variable (K : Type) [Field K]

theorem endpoint_positive_array (s : ℕ) (a : K) :
    rootArray K (Sum.inr (0 : Fin (s + 4))) (Sum.inl (last (s + 2))) (-a) =
      minusArray (0 : Fin (s + 4)) (last (s + 2)) a := by
  ext x y
  simp only [rootArray, paired, minusArray, plusArray, Matrix.transpose_add,
    Matrix.transpose_sub, Matrix.transpose_one, Matrix.transpose_single,
    Matrix.add_apply, Matrix.sub_apply, Matrix.single_apply]
  split_ifs <;> ring

theorem first_endpoint_recovery (s : ℕ) (H : Subgroup (Mat K (s + 4))ˣ)
    (hY : (initialShortRoot K s 1).val * (coxeterWeyl K (s + 3)).val ∈ H)
    (hB : HasRootLine H (rootArray K (Sum.inl (second s)) (Sum.inr (last (s + 2)))))
    (hD : HasRootLine H
      (rootArray K (Sum.inr (0 : Fin (s + 4))) (Sum.inl (last (s + 2))))) :
    (∀ a, (initialShortRoot K s a).val ∈ H) ∧ (coxeterWeyl K (s + 3)).val ∈ H := by
  have hp : HasRootLine H (plusArray (second s) (last (s + 2))) := hB
  have hn : HasRootLine H (minusArray (0 : Fin (s + 4)) (last (s + 2))) := by
    intro a
    obtain ⟨g, hg, he⟩ := hD (-a)
    exact ⟨g, hg, he.trans (endpoint_positive_array K s a)⟩
  have hs := plus_minus_lines H (second s) 0 (last (s + 2))
    (second_ne_zero s) (second_ne_last s) (Ne.symm (last_ne_zero s)) hp hn
  have hA : ∀ a, (initialShortRoot K s a).val ∈ H := by
    intro a
    obtain ⟨g, hg, he⟩ := hs a
    have hm : g = (initialShortRoot K s a).val := by
      apply Units.ext
      exact he.trans (initialShortRoot_coe K s a).symm
    exact hm ▸ hg
  refine ⟨hA, ?_⟩
  have hw := H.mul_mem (H.inv_mem (hA 1)) hY
  simpa only [inv_mul_cancel_left] using hw

end SymmetricSubgroupAsymptotics.CFSGOrthogonalDGenerationFirstEndpoint
