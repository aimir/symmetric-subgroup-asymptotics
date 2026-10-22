import Mathlib.Algebra.Group.TypeTags.Basic
import Mathlib.Algebra.Group.Subgroup.Basic
import Mathlib.Algebra.Group.Pi.Basic

/-! Literal additive coordinate axes, viewed multiplicatively for
compatibility with group abelianizations. -/
set_option autoImplicit false
noncomputable section
namespace SymmetricSubgroupAsymptotics.CFSGSimpleCoordinateAxes
variable {J K : Type*} [DecidableEq J] [AddCommGroup K]

def axis (i : J) : Subgroup (Multiplicative (J→K)) where
  carrier := {c | ∀j,j≠i→c.toAdd j=0}
  one_mem' := by intro j hj;rfl
  mul_mem' := by
    intro c d hc hd j hj
    change c.toAdd j+d.toAdd j=0
    rw [hc j hj,hd j hj,zero_add]
  inv_mem' := by
    intro c hc j hj
    change -c.toAdd j=0
    rw [hc j hj,neg_zero]

theorem single_mem_axis (i : J) (a : K) :
    Multiplicative.ofAdd (Pi.single i a : J→K)∈axis (K:=K) i := by
  intro j hj
  simp [Pi.single_apply,Ne.symm hj]

theorem mem_axis_iff (i : J) (c : Multiplicative (J→K)) :
    c∈axis i↔∃a : K,Multiplicative.ofAdd (Pi.single i a : J→K)=c := by
  constructor
  · intro hc
    refine ⟨c.toAdd i,?_⟩
    apply Multiplicative.toAdd.injective
    funext j
    by_cases hji : j=i
    · subst j
      simp [Pi.single_apply]
    · simpa [Pi.single_apply,Ne.symm hji] using (hc j hji).symm
  · rintro ⟨a,rfl⟩
    exact single_mem_axis i a

theorem axis_injective [Nontrivial K] : Function.Injective (axis (K:=K) (J:=J)) := by
  intro i j he
  by_contra hij
  obtain ⟨a,ha⟩ := exists_ne (0:K)
  have hmem : Multiplicative.ofAdd (Pi.single i a : J→K)∈axis (K:=K) j :=
    he ▸ single_mem_axis i a
  have hz := hmem i hij
  exact ha (by simpa [Pi.single_apply] using hz)

end SymmetricSubgroupAsymptotics.CFSGSimpleCoordinateAxes
