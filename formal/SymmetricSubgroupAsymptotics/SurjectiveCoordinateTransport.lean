import Mathlib.GroupTheory.QuotientGroup.Basic

/-! Exact coordinate maps descend through the SAME supplied surjection.
Kernel equality, rather than quotient order or dimension, gives injectivity. -/
set_option autoImplicit false
noncomputable section
namespace SymmetricSubgroupAsymptotics.SurjectiveCoordinateTransport
variable {G H C : Type} [Group G] [Group H] [Group C]
  (q : G →* H) (hq : Function.Surjective q) (j : G →* C) (hker : q.ker=j.ker)

def descend : H →* C := q.liftOfSurjective hq ⟨j,hker.le⟩

theorem descend_apply (g : G) : descend q hq j hker (q g)=j g := by
  simp only [descend,MonoidHom.liftOfSurjective,MonoidHom.liftOfRightInverse_comp_apply]

theorem descend_injective : Function.Injective (descend q hq j hker) := by
  intro x y hxy
  obtain ⟨g,rfl⟩ := hq x
  obtain ⟨h,rfl⟩ := hq y
  rw [descend_apply,descend_apply] at hxy
  have hm : g*h⁻¹∈j.ker := by
    change j (g*h⁻¹)=1
    rw [map_mul,map_inv,hxy,mul_inv_cancel]
  have hqone : q (g*h⁻¹)=1 := hker.ge hm
  rw [map_mul,map_inv] at hqone
  exact mul_inv_eq_one.mp hqone

end SymmetricSubgroupAsymptotics.SurjectiveCoordinateTransport
