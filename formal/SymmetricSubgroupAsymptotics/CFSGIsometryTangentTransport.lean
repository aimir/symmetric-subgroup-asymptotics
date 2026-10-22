import Mathlib.LinearAlgebra.BilinearForm.Basic

/-! An actual isometry transports the literal singular tangent cone.
This preserves both quadratic and mixed equations, rather than only the
ambient cardinality of the vector space. -/
set_option autoImplicit false
noncomputable section
namespace SymmetricSubgroupAsymptotics.CFSGIsometryTangentTransport
variable {K V : Type*} [CommRing K] [AddCommGroup V] [Module K V]

abbrev Tangent (B : LinearMap.BilinForm K V) (v : V) :=
  {w:V //B w w=0 ∧ B v w=0}

def tangentEquiv (B : LinearMap.BilinForm K V) (e : V≃ₗ[K]V)
    (he:∀x y,B (e x) (e y)=B x y) (v:V) : Tangent B v ≃ Tangent B (e v) where
  toFun w := ⟨e w.val,⟨(he w.val w.val).trans w.property.1,(he v w.val).trans w.property.2⟩⟩
  invFun w := ⟨e.symm w.val,⟨by
    have h:=he (e.symm w.val) (e.symm w.val)
    rw [e.apply_symm_apply] at h
    exact h.symm.trans w.property.1,by
      have h:=he v (e.symm w.val)
      rw [e.apply_symm_apply] at h
      exact h.symm.trans w.property.2⟩⟩
  left_inv w := Subtype.ext (e.symm_apply_apply w.val)
  right_inv w := Subtype.ext (e.apply_symm_apply w.val)

end SymmetricSubgroupAsymptotics.CFSGIsometryTangentTransport
