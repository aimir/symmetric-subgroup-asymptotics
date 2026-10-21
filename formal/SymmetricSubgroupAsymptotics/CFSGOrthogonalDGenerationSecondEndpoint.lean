import SymmetricSubgroupAsymptotics.CFSGOrthogonalDGenerationCleanedOrbit
import SymmetricSubgroupAsymptotics.CFSGOrthogonalDGenerationCoxeterSigns

/-! The second endpoint geometry is handled by conjugating the WHOLE
actual subgroup by the original short root. It yields both literal star
root lines and the transformed generator W*A. The conjugating element
is never assumed to belong to the subgroup being classified. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
namespace SymmetricSubgroupAsymptotics.CFSGOrthogonalDGenerationSecondEndpoint
open Matrix CFSGOrthogonalDSerreMatrices CFSGOrthogonalDBinaryElements
open CFSGOrthogonalDGenerationInitialElements CFSGOrthogonalDGenerationForkTorus
open CFSGOrthogonalDGenerationInitialRootMatrices CFSGOrthogonalDGenerationRootArrays
open CFSGOrthogonalDGenerationSignedRootConjugation CFSGOrthogonalDBinaryCyclePermutation
open CFSGOrthogonalDGenerationRootLineTransport CFSGOrthogonalDGenerationCoxeterSigns
open CFSGOrthogonalDGenerationCoxeterMonomial
variable (K : Type) [Field K]

theorem negative_endpoint_conjugation (s : ℕ) (a : K) :
    ((coxeterWeyl K (s + 3)).val : Mat K (s + 4)) *
      rootArray K (Sum.inr (0 : Fin (s + 4))) (Sum.inr (last (s + 2))) a *
      (↑((coxeterWeyl K (s + 3)).val⁻¹) : Mat K (s + 4)) =
        ((initialStarRoot K s true a).val : Mat K (s + 4)) := by
  have h0 : coxeterColumnSign K (s + 2) (Sum.inr (0 : Fin (s + 4))) = 1 := by
    rw [coxeterColumnSign_profile]
    change (if (0 : Fin (s + 4)) = pen (s + 2) then (-1 : K) ^ (s + 3)
      else if 0 = last (s + 2) then -1 else 1) = 1
    simp [Ne.symm (pen_ne_zero s), Ne.symm (last_ne_zero s)]
  have hL : coxeterColumnSign K (s + 2) (Sum.inr (last (s + 2))) = -1 := by
    rw [coxeterColumnSign_profile]
    change (if last (s + 2) = pen (s + 2) then (-1 : K) ^ (s + 3)
      else if last (s + 2) = last (s + 2) then -1 else 1) = -1
    simp [Ne.symm (pen_ne_last (s + 2))]
  have hm : cyclePerm (s + 2) (Sum.inr (0 : Fin (s + 4))) = Sum.inr (second s) :=
    cyclePerm_shift (s + 2) true 0 (by omega)
  rw [coxeter_conjugation K (s + 2), hm]
  change rootArray K (Sum.inr (second s)) (cyclePerm (s + 2) (Sum.inr (last (s + 2))))
    (coxeterColumnSign K (s + 2) (Sum.inr (0 : Fin (s + 4))) * a /
      coxeterColumnSign K (s + 2) (Sum.inr (last (s + 2)))) = _
  rw [show cyclePerm (s + 2) (Sum.inr (last (s + 2))) = Sum.inl (last (s + 2)) from
    cyclePerm_negative_last (s + 2), h0, hL, initialStarRoot_coe]
  ext x y
  simp only [rootArray, paired, one_mul, div_neg, div_one, if_true,
    Matrix.add_apply, Matrix.sub_apply, Matrix.single_apply]
  split_ifs <;> ring

def conjugatedSubgroup (s : ℕ) (H : Subgroup (Mat K (s + 4))ˣ) :
    Subgroup (Mat K (s + 4))ˣ :=
  H.comap (MulAut.conj (initialShortRoot K s 1).val).toMonoidHom

theorem second_endpoint_data (s : ℕ) (H : Subgroup (Mat K (s + 4))ˣ)
    (hY : (initialShortRoot K s 1).val * (coxeterWeyl K (s + 3)).val ∈ H)
    (hB : HasRootLine H (rootArray K (Sum.inl (second s)) (Sum.inr (last (s + 2)))))
    (hD : HasRootLine H
      (rootArray K (Sum.inr (0 : Fin (s + 4))) (Sum.inr (last (s + 2))))) :
    (∀ a, (initialStarRoot K s false a).val ∈ conjugatedSubgroup K s H) ∧
    (∀ a, (initialStarRoot K s true a).val ∈ conjugatedSubgroup K s H) ∧
      (coxeterWeyl K (s + 3)).val * (initialShortRoot K s 1).val ∈ conjugatedSubgroup K s H := by
  have hp : ∀ a, (initialStarRoot K s false a).val ∈ H := by
    intro a
    obtain ⟨g, hg, he⟩ := hB a
    have hu : g = (initialStarRoot K s false a).val := by
      apply Units.ext
      exact he.trans (initialStarRoot_coe K s false a).symm
    exact hu ▸ hg
  refine ⟨?_, ?_, ?_⟩
  · intro a
    change (initialShortRoot K s 1).val * (initialStarRoot K s false a).val *
      (initialShortRoot K s 1).val⁻¹ ∈ H
    have hc := congrArg Subtype.val
      (CFSGOrthogonalDGenerationRootArrays.initial_lines_commute s (1 : K) a).eq
    change (initialShortRoot K s 1).val * (initialStarRoot K s false a).val =
      (initialStarRoot K s false a).val * (initialShortRoot K s 1).val at hc
    rw [hc, mul_assoc, mul_inv_cancel, mul_one]
    exact hp a
  · intro a
    obtain ⟨d, hd, he⟩ := hD a
    have hu : (coxeterWeyl K (s + 3)).val * d * (coxeterWeyl K (s + 3)).val⁻¹ =
        (initialStarRoot K s true a).val := by
      apply Units.ext
      change ((coxeterWeyl K (s + 3)).val : Mat K (s + 4)) * (d : Mat K (s + 4)) *
        (↑((coxeterWeyl K (s + 3)).val⁻¹) : Mat K (s + 4)) = _
      rw [he]
      exact negative_endpoint_conjugation K s a
    have hmem := H.mul_mem (H.mul_mem hY hd) (H.inv_mem hY)
    have hex : ((initialShortRoot K s 1).val * (coxeterWeyl K (s + 3)).val) * d *
        ((initialShortRoot K s 1).val * (coxeterWeyl K (s + 3)).val)⁻¹ =
      (initialShortRoot K s 1).val *
        ((coxeterWeyl K (s + 3)).val * d * (coxeterWeyl K (s + 3)).val⁻¹) *
          (initialShortRoot K s 1).val⁻¹ := by group
    rw [hex, hu] at hmem
    exact hmem
  · change (initialShortRoot K s 1).val *
      ((coxeterWeyl K (s + 3)).val * (initialShortRoot K s 1).val) *
        (initialShortRoot K s 1).val⁻¹ ∈ H
    simpa only [mul_assoc, mul_inv_cancel, mul_one] using hY

end SymmetricSubgroupAsymptotics.CFSGOrthogonalDGenerationSecondEndpoint
