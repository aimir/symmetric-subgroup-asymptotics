import SymmetricSubgroupAsymptotics.CFSGFiniteFixedFiltration

/-! Coordinate matching along a finite positive filtration proves
membership in a subgroup. Representatives are elements of the actual
filtration layer, and their coordinate equality is converted to a literal
next-layer residual. No exactness of fixed points is assumed. -/
set_option autoImplicit false
set_option Elab.async false
namespace SymmetricSubgroupAsymptotics.SubgroupFiltrationCoordinateDescent
variable {G : Type*} [Group G]

theorem mem_of_positive_coordinate_representatives
    (S : Subgroup G) (Tail : ℤ → Subgroup G)
    (C : ℤ → Type*) [∀ h, Group (C h)]
    (coordinate : ∀ h, Tail h →* C h)
    (B : ℕ) (hfirst : Tail 1 = ⊤) (hlast : Tail ((B : ℤ)+1) = ⊥)
    (hkernel : ∀ h, 0 < h → (coordinate h).ker ≤
      (Tail (h+1)).comap (Tail h).subtype)
    (representative : ∀ h, 0 < h → ∀ u : Tail h,
      ∃ v : Tail h, (v : G) ∈ S ∧ coordinate h v = coordinate h u)
    (u : G) : u ∈ S := by
  apply CFSGFiniteFixedFiltration.fixed_mem_of_positive_step
    (MulEquiv.refl G) S Tail B hfirst hlast ?_ u rfl
  intro h hh x hx _
  obtain ⟨v,hv,he⟩ := representative h hh ⟨x,hx⟩
  let w : Tail h := v⁻¹ * ⟨x,hx⟩
  have hw : w ∈ (coordinate h).ker := by
    change coordinate h (v⁻¹ * ⟨x,hx⟩) = 1
    rw [map_mul,map_inv,he,inv_mul_cancel]
  refine ⟨v.val,hv,w.val,hkernel h hh hw,rfl,?_⟩
  exact (mul_inv_cancel_left v.val x).symm

theorem eq_top_of_positive_coordinate_representatives
    (S : Subgroup G) (Tail : ℤ → Subgroup G)
    (C : ℤ → Type*) [∀ h, Group (C h)]
    (coordinate : ∀ h, Tail h →* C h)
    (B : ℕ) (hfirst : Tail 1 = ⊤) (hlast : Tail ((B : ℤ)+1) = ⊥)
    (hkernel : ∀ h, 0 < h → (coordinate h).ker ≤
      (Tail (h+1)).comap (Tail h).subtype)
    (representative : ∀ h, 0 < h → ∀ u : Tail h,
      ∃ v : Tail h, (v : G) ∈ S ∧ coordinate h v = coordinate h u) : S = ⊤ := by
  apply top_unique
  intro u _
  exact mem_of_positive_coordinate_representatives S Tail C coordinate B hfirst hlast
    hkernel representative u

end SymmetricSubgroupAsymptotics.SubgroupFiltrationCoordinateDescent
