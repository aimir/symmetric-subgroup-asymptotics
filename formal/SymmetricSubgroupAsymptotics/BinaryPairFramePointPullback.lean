import SymmetricSubgroupAsymptotics.BinaryPairFrameTransport

/-! Pull an actual pair frame back through a matching point equivalence
and group equivalence. Literal point equivariance is required; an abstract
group isomorphism alone does not transport a permutation action. -/
set_option autoImplicit false
noncomputable section
namespace SymmetricSubgroupAsymptotics.BinaryPairFrame
variable {X Y I : Type} {U : Subgroup (Equiv.Perm X)} {V : Subgroup (Equiv.Perm Y)}
  (e : X ≃ Y) (f : U ≃* V)
  (h : ∀ u : U,∀ x : X,e ((u : Equiv.Perm X) x)=(f u : Equiv.Perm Y) (e x))
  (R : BinaryPairFrame V I)

def pointPullback : BinaryPairFrame U I where
  frame := R.frame.trans e.symm
  top := R.top.comp f.toMonoidHom
  intertwine := by
    intro u p
    change (R.frame.symm (e ((u : Equiv.Perm X) (e.symm (R.frame p))))).1=R.top (f u) p.1
    rw [h,e.apply_symm_apply]
    exact R.intertwine (f u) p

@[simp] theorem pointPullback_top_range : (R.pointPullback e f h).top.range=R.top.range := by
  apply le_antisymm
  · rintro _ ⟨u,rfl⟩
    exact ⟨f u,rfl⟩
  · rintro _ ⟨v,rfl⟩
    obtain ⟨u,rfl⟩ := f.surjective v
    exact ⟨u,rfl⟩

end SymmetricSubgroupAsymptotics.BinaryPairFrame
