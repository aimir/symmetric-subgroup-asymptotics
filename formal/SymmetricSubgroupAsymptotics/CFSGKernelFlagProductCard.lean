import SymmetricSubgroupAsymptotics.CFSGDisjointSubgroupProductCard

/-! An actual subgroup disjoint from a flag subgroup stays disjoint
and injective after a quotient whose kernel lies in that flag subgroup. -/
set_option autoImplicit false
noncomputable section

namespace SymmetricSubgroupAsymptotics.CFSGKernelFlagProductCard
variable {G H : Type*} [Group G] [Group H]

theorem injective_on_disjoint (f : G →* H) (B Q : Subgroup G)
    (hQB : Q ⊓ B = ⊥) (hk : f.ker ≤ B) :
    Function.Injective (f.comp Q.subtype) := by
  apply (f.comp Q.subtype).ker_eq_bot_iff.mp
  apply bot_unique
  intro x hx
  have hxB : x.val ∈ B := hk hx
  have hm : x.val ∈ Q ⊓ B := ⟨x.property, hxB⟩
  have he : x.val = 1 := by simpa only [hQB, Subgroup.mem_bot] using hm
  change x = 1
  exact Subtype.ext he

theorem disjoint_images (f : G →* H) (B Q : Subgroup G)
    (hQB : Q ⊓ B = ⊥) (hk : f.ker ≤ B) :
    Q.map f ⊓ B.map f = ⊥ := by
  apply bot_unique
  rintro x ⟨⟨q, hq, hqx⟩, b, hb, hbx⟩
  have he : f (q * b⁻¹) = 1 := by rw [map_mul, map_inv, hqx, hbx, mul_inv_cancel]
  have hqB : q ∈ B := by
    have hh := B.mul_mem (hk he) hb
    simpa only [mul_assoc, inv_mul_cancel, mul_one] using hh
  have hm : q ∈ Q ⊓ B := ⟨hq, hqB⟩
  have hone : q = 1 := by simpa only [hQB, Subgroup.mem_bot] using hm
  rw [hone, map_one] at hqx
  exact hqx.symm

theorem card_image (f : G →* H) (B Q : Subgroup G)
    (hQB : Q ⊓ B = ⊥) (hk : f.ker ≤ B) :
    Nat.card (Q.map f) = Nat.card Q := by
  have hrange : (f.comp Q.subtype).range = Q.map f := by
    rw [MonoidHom.range_comp, Q.range_subtype]
  rw [← hrange]
  exact (Nat.card_congr (MonoidHom.ofInjective
    (injective_on_disjoint f B Q hQB hk)).toEquiv).symm

theorem card_product_le [Finite H] (f : G →* H) (B Q : Subgroup G)
    (hQB : Q ⊓ B = ⊥) (hk : f.ker ≤ B) :
    Nat.card Q * Nat.card (B.map f) ≤ Nat.card H := by
  have hh := CFSGDisjointSubgroupProductCard.card_mul_le (Q.map f) (B.map f)
    (disjoint_images f B Q hQB hk)
  rwa [card_image f B Q hQB hk] at hh

end SymmetricSubgroupAsymptotics.CFSGKernelFlagProductCard
