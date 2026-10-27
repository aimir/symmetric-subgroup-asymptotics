import Mathlib.Algebra.Group.Action.Pi
import Mathlib.GroupTheory.GroupAction.Quotient
import Mathlib.SetTheory.Cardinal.Finite

/-! Product geometry for the ACTUAL base action. This does not replace a
correlated cover subgroup by independent coordinate subgroups. -/
set_option autoImplicit false
noncomputable section
open scoped BigOperators
namespace SymmetricSubgroupAsymptotics.PointwiseProductOrbitEquiv
variable {J G X : Type*} [Group G] [MulAction G X]

/-- The original orbit of a tuple is the product of its coordinate orbits. -/
def orbitEquiv (x : J → X) :
    MulAction.orbit (J → G) x ≃ (∀ i : J, MulAction.orbit G (x i)) where
  toFun y i := ⟨(y : J → X) i, by
    obtain ⟨g,hg⟩ := MulAction.mem_orbit_iff.mp y.property
    exact MulAction.mem_orbit_iff.mpr ⟨g i,congrFun hg i⟩⟩
  invFun y := ⟨fun i => (y i).val, by
    classical
    have hy (i : J) : ∃ g : G, g • x i = (y i).val :=
      MulAction.mem_orbit_iff.mp (y i).property
    let g : J → G := fun i => Classical.choose (hy i)
    apply MulAction.mem_orbit_iff.mpr
    refine ⟨g,?_⟩
    funext i
    exact Classical.choose_spec (hy i)⟩
  left_inv y := Subtype.ext rfl
  right_inv y := by funext i; exact Subtype.ext rfl

theorem card_orbit [Fintype J] (x : J → X) :
    Nat.card (MulAction.orbit (J → G) x) =
      ∏ i : J, Nat.card (MulAction.orbit G (x i)) := by
  rw [Nat.card_congr (orbitEquiv x),Nat.card_pi]

end SymmetricSubgroupAsymptotics.PointwiseProductOrbitEquiv
