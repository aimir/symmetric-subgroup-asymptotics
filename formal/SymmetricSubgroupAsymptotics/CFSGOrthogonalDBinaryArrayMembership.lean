import SymmetricSubgroupAsymptotics.CFSGOrthogonalDBinaryPairElements
import SymmetricSubgroupAsymptotics.CFSGSymplecticBinaryArrayMembership

/-! Sparse-array witnesses stay in the same actual matrix-unit subgroup
under the original D Coxeter word. The generic HasArray engine is reused. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
namespace SymmetricSubgroupAsymptotics.CFSGOrthogonalDBinaryArrayMembership
open CFSGOrthogonalDSerreMatrices CFSGOrthogonalDBinaryElements
open CFSGOrthogonalDBinaryConjugation CFSGOrthogonalDBinaryCyclePermutation
open CFSGSymplecticBinaryArrayMembership
variable {K : Type} [Field K] [CharP K 2]

theorem hasArray_conjugate (s : ℕ) (H : Subgroup ((Mat K (s + 2))ˣ))
    (hW : (coxeterWeyl K (s + 1)).val ∈ H) (a b : Index (s + 2))
    (ha : HasArray H (rootArray a b)) :
    HasArray H (rootArray (cyclePerm s a) (cyclePerm s b)) := by
  obtain ⟨g, hg, he⟩ := ha
  refine ⟨(coxeterWeyl K (s + 1)).val * g * (coxeterWeyl K (s + 1)).val⁻¹,
    H.mul_mem (H.mul_mem hW hg) (H.inv_mem hW), ?_⟩
  change ((coxeterWeyl K (s + 1)).val : Mat K (s + 2)) * (g : Mat K (s + 2)) *
    (↑((coxeterWeyl K (s + 1)).val⁻¹) : Mat K (s + 2)) = _
  rw [he, conjugation_rootArray]

theorem hasArray_inverse_conjugate (s : ℕ) (H : Subgroup ((Mat K (s + 2))ˣ))
    (hW : (coxeterWeyl K (s + 1)).val ∈ H) (a b : Index (s + 2))
    (ha : HasArray H (rootArray a b)) :
    HasArray H (rootArray ((cyclePerm s).symm a) ((cyclePerm s).symm b)) := by
  obtain ⟨g, hg, he⟩ := ha
  refine ⟨(coxeterWeyl K (s + 1)).val⁻¹ * g * (coxeterWeyl K (s + 1)).val,
    H.mul_mem (H.mul_mem (H.inv_mem hW) hg) hW, ?_⟩
  change (↑((coxeterWeyl K (s + 1)).val⁻¹) : Mat K (s + 2)) * (g : Mat K (s + 2)) *
    ((coxeterWeyl K (s + 1)).val : Mat K (s + 2)) = _
  rw [he, inverse_conjugation_rootArray]

end SymmetricSubgroupAsymptotics.CFSGOrthogonalDBinaryArrayMembership
