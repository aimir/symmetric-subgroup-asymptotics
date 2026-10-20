import SymmetricSubgroupAsymptotics.ProductBlockFrameGenerators

/-! Propagate a physical matching-colour action from literal generators.
This records correlated local matching actions, not arbitrary-subgroup
inheritance from a wreath product. -/
set_option autoImplicit false
noncomputable section
namespace SymmetricSubgroupAsymptotics.ProductBlockFrame

variable {X I F : Type} [Zero F] (frame : I × F ≃ X)
    (colour : X → X → I)

def MatchingPreserves (u : Equiv.Perm X) (p : Equiv.Perm I) : Prop :=
  ∀ x y : X, (frame.symm x).1 = (frame.symm y).1 → x ≠ y →
    colour (u x) (u y) = p (colour x y)

theorem matchingPreserves_mul {u v : Equiv.Perm X} {p q : Equiv.Perm I}
    (hv : Preserves frame v q)
    (huC : MatchingPreserves frame colour u p)
    (hvC : MatchingPreserves frame colour v q) :
    MatchingPreserves frame colour (u*v) (p*q) := by
  intro x y hxy hne
  have hvx := hv (frame.symm x)
  have hvy := hv (frame.symm y)
  simp only [frame.apply_symm_apply] at hvx hvy
  have hsame : (frame.symm (v x)).1 = (frame.symm (v y)).1 := by
    rw [hvx,hvy,hxy]
  have hdiff : v x ≠ v y := fun h => hne (v.injective h)
  change colour (u (v x)) (u (v y)) = p (q (colour x y))
  rw [huC (v x) (v y) hsame hdiff,hvC x y hxy hne]

theorem matchingPreserves_inv {u : Equiv.Perm X} {p : Equiv.Perm I}
    (hu : Preserves frame u p)
    (huC : MatchingPreserves frame colour u p) :
    MatchingPreserves frame colour u⁻¹ p⁻¹ := by
  intro x y hxy hne
  have hi := preserves_inv frame hu
  have hix := hi (frame.symm x)
  have hiy := hi (frame.symm y)
  simp only [frame.apply_symm_apply] at hix hiy
  have hsame : (frame.symm (u⁻¹ x)).1 = (frame.symm (u⁻¹ y)).1 := by
    rw [hix,hiy,hxy]
  have hdiff : u⁻¹ x ≠ u⁻¹ y := fun h => hne (u.symm.injective h)
  have hc := huC (u⁻¹ x) (u⁻¹ y) hsame hdiff
  simp only [Equiv.Perm.inv_def,Equiv.apply_symm_apply] at hc
  apply p.injective
  simpa only [Equiv.Perm.inv_def,Equiv.apply_symm_apply] using hc.symm

def matchingPreserving : Subgroup (Equiv.Perm X) where
  carrier := {u | ∃ p, Preserves frame u p ∧ MatchingPreserves frame colour u p}
  one_mem' := ⟨1,by intro x; simp,by intro x y _ _; rfl⟩
  mul_mem' := by
    rintro u v ⟨p,hp,hpC⟩ ⟨q,hq,hqC⟩
    exact ⟨p*q,preserves_mul frame hp hq,
      matchingPreserves_mul frame colour hq hpC hqC⟩
  inv_mem' := by
    rintro u ⟨p,hp,hpC⟩
    exact ⟨p⁻¹,preserves_inv frame hp,matchingPreserves_inv frame colour hp hpC⟩

variable {ι : Type} (generators : ι → Equiv.Perm X)
    (tops : ι → Equiv.Perm I)
    (h : ∀ j, Preserves frame (generators j) (tops j))
    (hC : ∀ j, MatchingPreserves frame colour (generators j) (tops j))

include h hC in
theorem generated_le_matchingPreserving :
    Subgroup.closure (Set.range generators) ≤ matchingPreserving frame colour := by
  apply (Subgroup.closure_le _).mpr
  rintro _ ⟨j,rfl⟩
  exact ⟨tops j,h j,hC j⟩

include hC in
theorem ofGenerators_matching (u : Subgroup.closure (Set.range generators)) :
    MatchingPreserves frame colour (u : Equiv.Perm X)
      ((ofGenerators frame generators tops h).top u) := by
  obtain ⟨p,hp,hpC⟩ := generated_le_matchingPreserving frame colour
    generators tops h hC u.property
  have he : p = (ofGenerators frame generators tops h).top u :=
    preserves_unique frame hp ((ofGenerators frame generators tops h).intertwine u)
  simpa only [he] using hpC

end SymmetricSubgroupAsymptotics.ProductBlockFrame
end
