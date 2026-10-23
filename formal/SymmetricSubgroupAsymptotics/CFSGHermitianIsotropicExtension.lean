import SymmetricSubgroupAsymptotics.CFSGHermitianOrthogonalSpan
import Mathlib.Order.Minimal

/-! Actual totally isotropic spaces extend to maximal ones. A single
singular orthogonal witness separates a point from such an extension.
These lemmas use finite-dimensional linear algebra only. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
namespace SymmetricSubgroupAsymptotics.CFSGHermitianOrthogonalSpan
open CFSGTwistedAUnitaryParameters
variable {K I : Type*} [Field K] [Fintype I]

theorem orthogonal_sup_left_iff (sigma : K ≃+* K) (H : Matrix I I K)
    (S T U : Submodule K (I → K)) :
    Orthogonal sigma H (S ⊔ T) U ↔ Orthogonal sigma H S U ∧ Orthogonal sigma H T U := by
  simp only [orthogonal_iff_le_leftPerp, sup_le_iff]

theorem orthogonal_sup_right_iff (sigma : K ≃+* K) (H : Matrix I I K)
    (S T U : Submodule K (I → K)) :
    Orthogonal sigma H S (T ⊔ U) ↔ Orthogonal sigma H S T ∧ Orthogonal sigma H S U := by
  simp only [orthogonal_iff_le_rightPerp, sup_le_iff]

theorem orthogonal_span_right_iff (sigma : K ≃+* K) (H : Matrix I I K)
    (S : Submodule K (I → K)) (y : I → K) :
    Orthogonal sigma H S (K ∙ y) ↔ ∀ x ∈ S, hermitianPair sigma H x y = 0 := by
  rw [orthogonal_iff_le_rightPerp, Submodule.span_singleton_le_iff_mem]
  rfl

theorem orthogonal_span_left_iff (sigma : K ≃+* K) (H : Matrix I I K)
    (S : Submodule K (I → K)) (y : I → K) :
    Orthogonal sigma H (K ∙ y) S ↔ ∀ x ∈ S, hermitianPair sigma H y x = 0 := by
  rw [orthogonal_iff_le_leftPerp, Submodule.span_singleton_le_iff_mem]
  rfl

theorem span_orthogonal_self (sigma : K ≃+* K) (H : Matrix I I K)
    (y : I → K) (hy : hermitianPair sigma H y y = 0) :
    Orthogonal sigma H (K ∙ y) (K ∙ y) := by
  rw [orthogonal_span_left_iff]
  intro x hx
  obtain ⟨a, rfl⟩ := Submodule.mem_span_singleton.mp hx
  have hh := hermitianPair_smul sigma H 1 a y y
  simpa only [one_smul, map_one, one_mul, hy, mul_zero] using hh

theorem exists_maximalIsotropic_ge (sigma : K ≃+* K) (H : Matrix I I K)
    (S : Submodule K (I → K)) (hS : Orthogonal sigma H S S) :
    ∃ M, S ≤ M ∧ MaximalIsotropic sigma H M := by
  obtain ⟨M, hSM, hM⟩ := exists_maximal_ge_of_wellFoundedGT
    (fun T : Submodule K (I → K) => Orthogonal sigma H T T) S hS
  exact ⟨M, hSM, hM.1, fun T hT hMT => (hM.2 hT hMT).antisymm hMT⟩

theorem exists_maximalIsotropic_excluding_of_witness
    (sigma : K ≃+* K) (H : Matrix I I K) (S : Submodule K (I → K))
    (hS : Orthogonal sigma H S S) (x y : I → K)
    (hy : hermitianPair sigma H y y = 0)
    (hSy : ∀ z ∈ S, hermitianPair sigma H z y = 0)
    (hyS : ∀ z ∈ S, hermitianPair sigma H y z = 0)
    (hyx : hermitianPair sigma H y x ≠ 0) :
    ∃ M, MaximalIsotropic sigma H M ∧ S ≤ M ∧ x ∉ M := by
  have hjoin : Orthogonal sigma H (S ⊔ K ∙ y) (S ⊔ K ∙ y) := by
    rw [orthogonal_sup_left_iff, orthogonal_sup_right_iff, orthogonal_sup_right_iff]
    exact ⟨⟨hS, (orthogonal_span_right_iff sigma H S y).mpr hSy⟩,
      (orthogonal_span_left_iff sigma H S y).mpr hyS, span_orthogonal_self sigma H y hy⟩
  obtain ⟨M, hM, hmax⟩ := exists_maximalIsotropic_ge sigma H _ hjoin
  refine ⟨M, hmax, le_sup_left.trans hM, ?_⟩
  intro hx
  apply hyx
  have hyjoin : y ∈ S ⊔ K ∙ y :=
    (show K ∙ y ≤ S ⊔ K ∙ y from le_sup_right) (Submodule.mem_span_singleton_self y)
  exact hmax.1 y (hM hyjoin) x hx

end SymmetricSubgroupAsymptotics.CFSGHermitianOrthogonalSpan
