import SymmetricSubgroupAsymptotics.CFSGHermitianLocalFieldCoherence

/-! Literal nonzero norm-zero vectors define the actual singular point
line. Their label agrees with every containing isotropic subspace's
projective coordinates. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
open scoped LinearAlgebra.Projectivization
namespace SymmetricSubgroupAsymptotics.CFSGHermitianOrthogonalSpan
open CFSGTwistedAUnitaryParameters
variable {K I : Type*} [Field K] [Fintype I]
variable (sigma : K ≃+* K) (H : Matrix I I K)

def singularRay (x : I → K) (hx : x ≠ 0) (hz : hermitianPair sigma H x x = 0) :
    SingularPoint sigma H :=
  ⟨K ∙ x, finrank_span_singleton hx, by
    intro y hy
    obtain ⟨a, rfl⟩ := Submodule.mem_span_singleton.mp hy
    rw [hermitianPair_smul, hz, mul_zero]⟩

theorem singularRay_val (x : I → K) (hx : x ≠ 0) (hz : hermitianPair sigma H x x = 0) :
    (singularRay sigma H x hx hz).val = K ∙ x := rfl

theorem singularRay_eq_projectiveInside (S : IsotropicSpace sigma H)
    (x : S.val) (hx : x ≠ 0) :
    singularRay sigma H x.val (fun h => hx (Subtype.ext h))
      (S.property x.val x.property x.val x.property) =
        (projectiveInside sigma H S (Projectivization.mk K x hx)).val := by
  apply Subtype.ext
  exact (projectiveInside_mk_submodule sigma H S x hx).symm

end SymmetricSubgroupAsymptotics.CFSGHermitianOrthogonalSpan
