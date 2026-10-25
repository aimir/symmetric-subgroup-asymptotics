import Mathlib.GroupTheory.GroupAction.Basic
import Mathlib.Algebra.Group.Subgroup.Defs

/-! A normal subgroup fixing one point fixes its whole group orbit.
This is an action statement, without any transitivity or faithfulness
assumption on the ambient action. -/
set_option autoImplicit false
set_option Elab.async false
namespace SymmetricSubgroupAsymptotics.NormalSubgroupOrbitFixed
variable {G X : Type*} [Group G] [MulAction G X]

theorem fixes_orbit (N : Subgroup G) [N.Normal] (x : X)
    (hN : ∀ n ∈ N, n • x = x) (n : G) (hn : n ∈ N) :
    ∀ y ∈ MulAction.orbit G x, n • y = y := by
  rintro y ⟨g,rfl⟩
  have hc : g⁻¹*n*g ∈ N := Subgroup.Normal.conj_mem' inferInstance n hn g
  have he := hN (g⁻¹*n*g) hc
  calc
    n • (g • x) = g • ((g⁻¹*n*g) • x) := by
      simp only [mul_smul,smul_inv_smul]
    _ = g • x := congrArg (fun z : X => g • z) he

end SymmetricSubgroupAsymptotics.NormalSubgroupOrbitFixed
