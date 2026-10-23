import SymmetricSubgroupAsymptotics.CFSGHermitianMixedMaximalSpace
import SymmetricSubgroupAsymptotics.CFSGHermitianPointFunctionals

/-! Literal orthogonal singular vectors lie in one actual maximal
singular subspace. The same local representative determines their image
coefficients from point membership, without an ambient extension. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
namespace SymmetricSubgroupAsymptotics.CFSGHermitianOrthogonalSpan
open CFSGTwistedAUnitaryParameters
variable {K I : Type*} [Field K] [Fintype I]

theorem exists_hermitian_maximal_contains_pair (sigma : K ≃+* K) (H : Matrix I I K)
    (hswap : ∀ x y, hermitianPair sigma H x y = 0 ↔ hermitianPair sigma H y x = 0)
    (z w : I → K) (hz : hermitianPair sigma H z z = 0)
    (hw : hermitianPair sigma H w w = 0) (hzw : hermitianPair sigma H z w = 0) :
    ∃ M : MaximalSpace sigma H, z ∈ M.val ∧ w ∈ M.val := by
  have hzw' : Orthogonal sigma H (K ∙ z) (K ∙ w) := by
    apply (orthogonal_span_left_iff sigma H _ z).mpr
    intro v hv
    obtain ⟨a,rfl⟩ := Submodule.mem_span_singleton.mp hv
    have hh := hermitianPair_smul sigma H 1 a z w
    simpa only [one_smul, map_one, one_mul, hzw, mul_zero] using hh
  have hwz' : Orthogonal sigma H (K ∙ w) (K ∙ z) := by
    intro v hv u hu
    exact (hswap u v).mp (hzw' u hu v hv)
  have hjoin : Orthogonal sigma H ((K ∙ z) ⊔ K ∙ w) ((K ∙ z) ⊔ K ∙ w) := by
    rw [orthogonal_sup_left_iff, orthogonal_sup_right_iff, orthogonal_sup_right_iff]
    exact ⟨⟨span_orthogonal_self sigma H z hz,hzw'⟩,hwz',span_orthogonal_self sigma H w hw⟩
  obtain ⟨M,hle,hM⟩ := exists_maximalIsotropic_ge sigma H _ hjoin
  exact ⟨⟨M,hM⟩,
    hle ((show K ∙ z ≤ (K ∙ z) ⊔ K ∙ w from le_sup_left) (Submodule.mem_span_singleton_self z)),
    hle ((show K ∙ w ≤ (K ∙ z) ⊔ K ∙ w from le_sup_right) (Submodule.mem_span_singleton_self w))⟩

theorem hermitian_piece_image_scalar (sigma : K ≃+* K) (H : Matrix I I K)
    (f : Equiv.Perm (SingularPoint sigma H)) (M : IsotropicSpace sigma H)
    (tau : K ≃+* K) (F : SemilinearPiece sigma H f M tau)
    (Q : SingularPoint sigma H) (z v : I → K)
    (hzM : z ∈ M.val) (hzQ : z ∈ Q.val) (hz0 : z ≠ 0)
    (hv : v ∈ (f Q).val) (hv0 : v ≠ 0) :
    ∃ a : K, a ≠ 0 ∧ F.map ⟨z,hzM⟩ = a • v := by
  have hzM0 : (⟨z,hzM⟩ : M.val) ≠ 0 := fun h => hz0 (congrArg Subtype.val h)
  have hF0 : F.map ⟨z,hzM⟩ ≠ 0 := by
    intro h
    exact hzM0 (F.injective (h.trans F.map.map_zero.symm))
  have hp := F.ray ⟨z,hzM⟩ hzM0
  rw [←singularRay_eq_projectiveInside sigma H M ⟨z,hzM⟩ hzM0] at hp
  have he : singularRay sigma H z hz0 (M.property z hzM z hzM) = Q :=
    Subtype.ext (singularPoint_span sigma H Q z hzQ hz0).symm
  rw [he] at hp
  have hm : F.map ⟨z,hzM⟩ ∈ (f Q).val := hp ▸ Submodule.mem_span_singleton_self _
  rw [singularPoint_span sigma H (f Q) v hv hv0] at hm
  obtain ⟨a,ha⟩ := Submodule.mem_span_singleton.mp hm
  refine ⟨a,?_,ha.symm⟩
  intro h
  exact hF0 (ha.symm.trans (by rw [h,zero_smul]))

end SymmetricSubgroupAsymptotics.CFSGHermitianOrthogonalSpan
