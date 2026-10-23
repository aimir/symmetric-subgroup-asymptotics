import SymmetricSubgroupAsymptotics.CFSGIndexFromSubgroupCosetCover

/-! A parameter group may cover the cosets of an actual subgroup even
when some parameters lie outside the ambient subgroup. Restricting to
the literal comap gives the same finite index bound. -/
set_option autoImplicit false
noncomputable section
namespace SymmetricSubgroupAsymptotics.CFSGIndexFromPartialParameterCover
variable {A G : Type*} [Group A] [Group G] [Finite A]

theorem index_le_of_partial_parameter_cover (H L : Subgroup G) (hHL : H ≤ L)
    (f : A →* G) (N : Subgroup A) (hN : ∀ a ∈ N, f a ∈ H)
    (hcover : ∀ g ∈ L, ∃ a, (f a)⁻¹ * g ∈ H) :
    (H.subgroupOf L).index ≤ N.index := by
  let B := L.comap f
  let fB : B →* G := f.comp B.subtype
  let NB := N.comap B.subtype
  have hfB (a : B) : fB a ∈ L := a.property
  have hNB (a : B) (ha : a ∈ NB) : fB a ∈ H := hN a.val ha
  have hc : ∀ g ∈ L, ∃ a : B, (fB a)⁻¹ * g ∈ H := by
    intro g hg
    obtain ⟨a, ha⟩ := hcover g hg
    have hfa : f a ∈ L := by
      have h := L.mul_mem hg (L.inv_mem (hHL ha))
      simpa only [mul_inv_rev, inv_inv, ← mul_assoc, mul_inv_cancel, one_mul] using h
    exact ⟨⟨a, hfa⟩, ha⟩
  have hb : NB.index ≤ N.index := by
    change (N.comap B.subtype).index ≤ N.index
    rw [Subgroup.index_comap]
    have hn : N.relIndex ⊤ ≠ 0 := by
      rw [Subgroup.relIndex_top_right]
      exact Subgroup.index_ne_zero_of_finite
    calc
      N.relIndex B.subtype.range ≤ N.relIndex ⊤ :=
        Subgroup.relIndex_le_of_le_right le_top hn
      _ = N.index := by rw [Subgroup.relIndex_top_right]
  exact (CFSGIndexFromSubgroupCosetCover.index_le_of_parameter_subgroup
    H L fB hfB NB hNB hc).trans hb

end SymmetricSubgroupAsymptotics.CFSGIndexFromPartialParameterCover
