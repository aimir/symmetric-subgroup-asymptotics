import SymmetricSubgroupAsymptotics.FiniteSubgroupAdjunctionCoverage
import Mathlib.Algebra.Group.Subgroup.Ker

/-! Transport of actual subgroup conjugacy coverage through a specified
group equivalence. The image of each listed subgroup is retained. -/

set_option autoImplicit false
noncomputable section
open scoped Pointwise

namespace SymmetricSubgroupAsymptotics.FiniteSubgroupAdjunctionCoverage

variable {G H I : Type*} [Group G] [Group H]

theorem map_conjugate (e : G ≃* H) (c : G) (U : Subgroup G) :
    (MulAut.conj c • U).map e.toMonoidHom =
      MulAut.conj (e c) • U.map e.toMonoidHom := by
  change (U.map (MulAut.conj c).toMonoidHom).map e.toMonoidHom =
    (U.map e.toMonoidHom).map (MulAut.conj (e c)).toMonoidHom
  rw [Subgroup.map_map, Subgroup.map_map]
  apply congrArg (fun f : G →* H => U.map f)
  ext z
  change e (c * z * c⁻¹) = e c * e z * (e c)⁻¹
  simp only [map_mul, map_inv]

theorem covered_map (rows : I → Subgroup G) (e : G ≃* H)
    {U : Subgroup G} (h : Covered rows U) :
    Covered (fun i => (rows i).map e.toMonoidHom) (U.map e.toMonoidHom) := by
  obtain ⟨i, c, hc⟩ := h
  refine ⟨i, e c, ?_⟩
  rw [← map_conjugate, hc]

/-- The row model certificate covers subgroups of the actual original
group, without any abstract order-based identification. -/
theorem complete_of_equiv (rows : I → Subgroup G) (e : G ≃* H)
    (hcomplete : ∀ U : Subgroup G, Covered rows U) (K : Subgroup H) :
    Covered (fun i => (rows i).map e.toMonoidHom) K := by
  have h := covered_map rows e (hcomplete (K.comap e.toMonoidHom))
  rw [Subgroup.map_comap_eq_self_of_surjective e.surjective K] at h
  exact h

end SymmetricSubgroupAsymptotics.FiniteSubgroupAdjunctionCoverage

end
