import SymmetricSubgroupAsymptotics.CFSGHermitianOpposedPieceFields
import SymmetricSubgroupAsymptotics.CFSGHermitianIsotropicExtension

/-! Disjoint maximal singular spaces have nondegenerate cross-pairing:
a singular vector orthogonal to a maximal space must already belong
to it. This uses literal maximality, including characteristic two,
without a Witt-index or ambient isometry-group recognition premise. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section

namespace SymmetricSubgroupAsymptotics.CFSGHermitianOrthogonalSpan
open CFSGTwistedAUnitaryParameters
variable {K I : Type*} [Field K] [Fintype I]

theorem singular_orthogonal_maximal_mem (sigma : K ≃+* K) (H : Matrix I I K)
    (hswap : ∀ x y, hermitianPair sigma H x y = 0 ↔ hermitianPair sigma H y x = 0)
    (S : Submodule K (I → K)) (hS : MaximalIsotropic sigma H S)
    (x : I → K) (hx : hermitianPair sigma H x x = 0)
    (hzero : ∀ y ∈ S, hermitianPair sigma H x y = 0) : x ∈ S := by
  have hreverse : ∀ y ∈ S, hermitianPair sigma H y x = 0 :=
    fun y hy => (hswap x y).mp (hzero y hy)
  have hjoin : Orthogonal sigma H (S ⊔ K ∙ x) (S ⊔ K ∙ x) := by
    rw [orthogonal_sup_left_iff, orthogonal_sup_right_iff, orthogonal_sup_right_iff]
    exact ⟨⟨hS.1, (orthogonal_span_right_iff sigma H S x).mpr hreverse⟩,
      (orthogonal_span_left_iff sigma H S x).mpr hzero, span_orthogonal_self sigma H x hx⟩
  have he : S ⊔ K ∙ x = S := hS.2 _ hjoin le_sup_left
  have hm : x ∈ S ⊔ K ∙ x :=
    (show K ∙ x ≤ S ⊔ K ∙ x from le_sup_right) (Submodule.mem_span_singleton_self x)
  exact he ▸ hm

theorem disjoint_maximal_cross_nondegenerate (sigma : K ≃+* K) (H : Matrix I I K)
    (hswap : ∀ x y, hermitianPair sigma H x y = 0 ↔ hermitianPair sigma H y x = 0)
    (P Z : Submodule K (I → K)) (hP : MaximalIsotropic sigma H P)
    (hZ : MaximalIsotropic sigma H Z) (hdis : Disjoint P Z)
    (x : I → K) (hx : x ∈ P)
    (hzero : ∀ y ∈ Z, hermitianPair sigma H x y = 0) : x = 0 := by
  have hxZ := singular_orthogonal_maximal_mem sigma H hswap Z hZ x (hP.1 x hx x hx) hzero
  exact (Submodule.disjoint_def.mp hdis) x hx hxZ

theorem semilinearPiece_fields_eq_of_disjoint_maximal_planes [Finite K]
    (sigma : K ≃+* K) (H : Matrix I I K)
    (hswap : ∀ x y, hermitianPair sigma H x y = 0 ↔ hermitianPair sigma H y x = 0)
    (f : Equiv.Perm (SingularPoint sigma H)) (hf : PreservesOrthogonality sigma H f)
    (P Z : Submodule K (I → K)) (hP : MaximalIsotropic sigma H P)
    (hZ : MaximalIsotropic sigma H Z) (hdis : Disjoint P Z)
    (hdP : Module.finrank K P = 2) (hdZ : Module.finrank K Z = 2)
    (tauP tauZ : K ≃+* K)
    (F : SemilinearPiece sigma H f ⟨P, hP.1⟩ tauP)
    (G : SemilinearPiece sigma H f ⟨Z, hZ.1⟩ tauZ) (hcomm : Function.Commute sigma tauZ) :
    tauP = tauZ := by
  apply semilinearPiece_fields_eq_of_opposed_planes sigma H f hf
    ⟨P, hP.1⟩ ⟨Z, hZ.1⟩ hdP hdZ _ tauP tauZ F G hcomm
  intro x hx
  apply Subtype.ext
  exact disjoint_maximal_cross_nondegenerate sigma H hswap P Z hP hZ hdis x.val x.property
    (fun y hy => hx ⟨y, hy⟩)

end SymmetricSubgroupAsymptotics.CFSGHermitianOrthogonalSpan
