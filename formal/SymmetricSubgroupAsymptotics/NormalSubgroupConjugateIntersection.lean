import Mathlib.GroupTheory.GroupAction.ConjAct

/-! Actual conjugation commutes with intersection inside a normal
subgroup. The conjugating element need not belong to that subgroup. -/
set_option autoImplicit false
namespace SymmetricSubgroupAsymptotics.NormalSubgroupConjugateIntersection
variable {G : Type*} [Group G]

/-- Retain the literal normal subgroup, ambient conjugating element,
and coordinate inclusion on both sides. -/
theorem map_comap_conj_normal (U D : Subgroup G) [D.Normal] (g : G) :
    (U.comap D.subtype).map (MulAut.conjNormal g).toMonoidHom =
      (U.map (MulAut.conj g).toMonoidHom).comap D.subtype := by
  apply le_antisymm
  · rintro _ ⟨u, hu, rfl⟩
    change g * u.val * g⁻¹ ∈ U.map (MulAut.conj g).toMonoidHom
    exact ⟨u.val, hu, rfl⟩
  · intro z hz
    change z.val ∈ U.map (MulAut.conj g).toMonoidHom at hz
    obtain ⟨u, hu, he⟩ := hz
    change g * u * g⁻¹ = z.val at he
    have huD : u ∈ D := by
      have hc := (inferInstance : D.Normal).conj_mem' _ z.property g
      rw [← he] at hc
      simpa only [mul_assoc, inv_mul_cancel_left, inv_mul_cancel, mul_one] using hc
    refine ⟨⟨u, huD⟩, hu, ?_⟩
    apply Subtype.ext
    change g * u * g⁻¹ = z.val
    exact he

end SymmetricSubgroupAsymptotics.NormalSubgroupConjugateIntersection
