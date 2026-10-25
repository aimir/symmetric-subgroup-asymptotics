import Mathlib.Algebra.Group.Subgroup.Pointwise
import Mathlib.Tactic.Group

/-! Conjugation of an intersection with a central layer by the SAME join.
Only centralization of the normal subgroup is required; no complement or
linear action on the layer is chosen. -/
set_option autoImplicit false
set_option Elab.async false
namespace SymmetricSubgroupAsymptotics.CentralizingJoinIntersection
variable {G : Type*} [Group G]

theorem conjugate_mem (N M : Subgroup G) [N.Normal] (z : G) (hz : z ∈ M)
    (hc : ∀ n ∈ N, n*z=z*n) (g : G) (hg : g ∈ M ⊔ N) :
    g*z*g⁻¹ ∈ M := by
  obtain ⟨m,hm,n,hn,rfl⟩ := Subgroup.mem_sup_of_normal_right.mp hg
  have he : (m*n)*z*(m*n)⁻¹ = m*z*m⁻¹ := by
    calc
      (m*n)*z*(m*n)⁻¹ = m*(n*z)*n⁻¹*m⁻¹ := by group
      _ = m*(z*n)*n⁻¹*m⁻¹ := by rw [hc n hn]
      _ = m*z*m⁻¹ := by group
  rw [he]
  exact M.mul_mem (M.mul_mem hm hz) (M.inv_mem hm)

end SymmetricSubgroupAsymptotics.CentralizingJoinIntersection
