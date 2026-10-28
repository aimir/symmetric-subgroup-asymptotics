import Mathlib.GroupTheory.PGroup
import Mathlib.GroupTheory.Commutator.Basic
import Mathlib.Tactic

/-! In a p-group of order p^5 and center order p², a subgroup disjoint
from the actual center has order at most p². Saturation of the elementary
product injection would make the group a central product with disjoint
factors, contradicting the nontrivial center of that subgroup. -/
set_option autoImplicit false
noncomputable section
namespace SymmetricSubgroupAsymptotics.PrimeFifthOrderCenterDisjointBound

variable {G : Type*} [Group G] [Finite G]

theorem central_product_injective (U : Subgroup G)
    (hinf : U ⊓ Subgroup.center G = ⊥) :
    Function.Injective (fun x : U × Subgroup.center G => (x.1 : G) * (x.2 : G)) := by
  rintro ⟨u, z⟩ ⟨v, w⟩ he
  have he' : (u : G) * (z : G) = (v : G) * (w : G) := he
  have hcross : (v : G)⁻¹ * (u : G) = (w : G) * (z : G)⁻¹ := by
    calc
      (v : G)⁻¹ * (u : G) = ((v : G)⁻¹ * ((u : G) * (z : G))) * (z : G)⁻¹ := by group
      _ = ((v : G)⁻¹ * ((v : G) * (w : G))) * (z : G)⁻¹ := by rw [he']
      _ = (w : G) * (z : G)⁻¹ := by group
  have hmem : (v : G)⁻¹ * (u : G) ∈ U ⊓ Subgroup.center G := by
    refine ⟨U.mul_mem (U.inv_mem v.property) u.property, ?_⟩
    rw [hcross]
    exact (Subgroup.center G).mul_mem w.property ((Subgroup.center G).inv_mem z.property)
  have hvu : (v : G)⁻¹ * (u : G) = 1 := by
    rw [hinf, Subgroup.mem_bot] at hmem
    exact hmem
  have huv : u = v := Subtype.ext (inv_mul_eq_one.mp hvu).symm
  subst v
  exact Prod.ext rfl (Subtype.ext (mul_left_cancel he'))

theorem card_le_prime_square {p : ℕ} (hp : p.Prime)
    (hG : Nat.card G = p ^ 5) (hZ : Nat.card (Subgroup.center G) = p ^ 2)
    (U : Subgroup G) (hinf : U ⊓ Subgroup.center G = ⊥) : Nat.card U ≤ p ^ 2 := by
  classical
  letI : Fact p.Prime := ⟨hp⟩
  let f : U × Subgroup.center G → G := fun x => (x.1 : G) * (x.2 : G)
  have hf : Function.Injective f := central_product_injective U hinf
  have hprod : Nat.card U * p ^ 2 ≤ p ^ 5 := by
    have h := Nat.card_le_card_of_injective f hf
    simpa only [Nat.card_prod, hZ, hG] using h
  have hcard : Nat.card U ≤ p ^ 3 := by
    apply Nat.le_of_mul_le_mul_right (c := p ^ 2) ?_ (pow_pos hp.pos 2)
    exact hprod.trans_eq (by ring)
  have hne : Nat.card U ≠ p ^ 3 := by
    intro hU
    have hsurj : Function.Surjective f :=
      (hf.bijective_of_nat_card_le (by
        rw [Nat.card_prod, hZ, hG, hU]
        exact (by ring : p ^ 5 = p ^ 3 * p ^ 2).le)).2
    letI : Nontrivial U := Finite.one_lt_card_iff_nontrivial.mp
      (by rw [hU]; exact hp.one_lt.trans_le (Nat.le_self_pow (by decide : (3 : ℕ) ≠ 0) p))
    letI : Nontrivial (Subgroup.center U) :=
      (IsPGroup.of_card hU).center_nontrivial
    obtain ⟨w, hw⟩ := exists_ne (1 : Subgroup.center U)
    have hwcenter : ((w : U) : G) ∈ Subgroup.center G := by
      apply Subgroup.mem_center_iff.mpr
      intro g
      obtain ⟨⟨u, z⟩, rfl⟩ := hsurj g
      have hu : (u : G) * ((w : U) : G) = ((w : U) : G) * (u : G) :=
        congrArg Subtype.val (Subgroup.mem_center_iff.mp w.property u)
      have hz : (z : G) * ((w : U) : G) = ((w : U) : G) * (z : G) :=
        (Subgroup.mem_center_iff.mp z.property ((w : U) : G)).symm
      change ((u : G) * (z : G)) * ((w : U) : G) =
        ((w : U) : G) * ((u : G) * (z : G))
      rw [mul_assoc, hz, ← mul_assoc, hu, mul_assoc]
    have hm : ((w : U) : G) ∈ U ⊓ Subgroup.center G := ⟨w.val.property, hwcenter⟩
    rw [hinf, Subgroup.mem_bot] at hm
    exact hw (Subtype.ext (Subtype.ext hm))
  obtain ⟨k, _, hk⟩ := (Nat.dvd_prime_pow hp).mp (hG ▸ U.card_subgroup_dvd_card)
  have hk3 : k ≤ 3 := (Nat.pow_le_pow_iff_right hp.one_lt).mp (hk ▸ hcard)
  have hk2 : k ≤ 2 := by
    have : k ≠ 3 := by intro he; exact hne (he ▸ hk)
    omega
  rw [hk]
  exact Nat.pow_le_pow_right hp.pos hk2

end SymmetricSubgroupAsymptotics.PrimeFifthOrderCenterDisjointBound
