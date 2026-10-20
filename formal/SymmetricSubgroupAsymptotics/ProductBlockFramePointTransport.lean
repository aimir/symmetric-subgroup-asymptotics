import SymmetricSubgroupAsymptotics.ProductBlockFrameGenerators

/-! Transport a physical product chart by an actual point equivalence and
its intertwining group equivalence. -/
set_option autoImplicit false
noncomputable section
namespace SymmetricSubgroupAsymptotics.ProductBlockFrame

variable {X Y I F : Type} {U : Subgroup (Equiv.Perm X)}
    {V : Subgroup (Equiv.Perm Y)}

/-- Both the points and the actual group action are transported together. -/
def ofPointEquiv (C : ProductBlockFrame U I F)
    (e : U ≃* V) (points : X ≃ Y)
    (he : ∀ (u : U) (x : X),
      points ((u : Equiv.Perm X) x) = (e u : Equiv.Perm Y) (points x)) :
    ProductBlockFrame V I F where
  frame := C.frame.trans points
  top := C.top.comp e.symm.toMonoidHom
  intertwine u p := by
    have hx : points.symm ((u : Equiv.Perm Y) (points (C.frame p))) =
        (e.symm u : Equiv.Perm X) (C.frame p) := by
      apply points.injective
      simpa only [points.apply_symm_apply,e.apply_symm_apply] using
        (he (e.symm u) (C.frame p)).symm
    change (C.frame.symm (points.symm
      ((u : Equiv.Perm Y) (points (C.frame p))))).1 = C.top (e.symm u) p.1
    rw [hx]
    exact C.intertwine (e.symm u) p

end SymmetricSubgroupAsymptotics.ProductBlockFrame
end
