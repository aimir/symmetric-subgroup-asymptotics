import Mathlib.Algebra.Group.TypeTags.Hom
import Mathlib.Algebra.Group.Subgroup.Basic
import Mathlib.Algebra.GroupWithZero.Units.Basic
import Mathlib.Tactic.FieldSimp

/-! An actual full unit-scaling root action saturates any nonzero root
parameter in a normal subgroup. No finite-field or generation claim is
hidden in this elementary field calculation. -/
set_option autoImplicit false
set_option Elab.async false
namespace SymmetricSubgroupAsymptotics.CFSGFieldRootNormalSaturation
variable {K G : Type*} [Field K] [Group G]

theorem root_range_le_normal_of_nonzero (φ : Multiplicative K→*G) (T : Kˣ→G)
    (hact : ∀t : Kˣ,∀b : K,T t*φ (Multiplicative.ofAdd b)*(T t)⁻¹=
      φ (Multiplicative.ofAdd (b*(t:K)))) (N : Subgroup G) [N.Normal]
    (a : K) (ha : a≠0) (hNa : φ (Multiplicative.ofAdd a)∈N) : φ.range≤N := by
  rintro x ⟨b,rfl⟩
  by_cases hb : b.toAdd=0
  · have hb' : b=1 := by
      change b=Multiplicative.ofAdd 0
      exact congrArg Multiplicative.ofAdd hb
    rw [hb',map_one]
    exact N.one_mem
  · let t : Kˣ := Units.mk0 (b.toAdd/a) (div_ne_zero hb ha)
    have he : a*(t:K)=b.toAdd := by
      change a*(b.toAdd/a)=b.toAdd
      field_simp
    have hn := (inferInstance : N.Normal).conj_mem (φ (Multiplicative.ofAdd a)) hNa (T t)
    rw [hact,he] at hn
    exact hn

end SymmetricSubgroupAsymptotics.CFSGFieldRootNormalSaturation
