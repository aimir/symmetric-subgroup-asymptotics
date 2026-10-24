import Mathlib.Algebra.Group.Equiv.Basic
import Mathlib.Algebra.Group.Hom.Defs

/-! Small typed equivalence identities keep concrete quotient coordinate
proofs abstract while retaining their literal inclusions and actions. -/
set_option autoImplicit false
set_option Elab.async false
namespace SymmetricSubgroupAsymptotics.CFSGEquivCoordinateTransport

theorem composite_eq_one_iff {C Q V : Type*} [Group C] [Group Q] [Group V]
    (e : C≃*Q) (p : C≃*V) (x : Q) : p (e.symm x)=1 ↔ x=1 := by
  rw [p.map_eq_one_iff,e.symm.map_eq_one_iff]

theorem coordinates_of_underlying_intertwining {C Q R : Type*}
    [Group C] [Group Q] [Group R]
    (e : C≃*Q) (inc : Q→*R) (hinj : Function.Injective inc)
    (T : R→R) (F : C→C) (hinter : ∀c,T (inc (e c))=inc (e (F c)))
    (u v : Q) (hv : inc v=T (inc u)) : e.symm v=F (e.symm u) := by
  apply e.injective
  apply hinj
  rw [e.apply_symm_apply]
  calc
    inc v=T (inc u) := hv
    _=T (inc (e (e.symm u))) := by rw [e.apply_symm_apply]
    _=inc (e (F (e.symm u))) := hinter _

end SymmetricSubgroupAsymptotics.CFSGEquivCoordinateTransport
