import SymmetricSubgroupAsymptotics.CFSGSolubleNormalizerProduct
import Mathlib.Algebra.Group.Subgroup.Finite
import Mathlib.GroupTheory.OrderOfElement
import Mathlib.Data.Finite.Prod
import Mathlib.Data.ZMod.QuotientGroup

/-! In a finite ambient group, a power-conjugation relation makes one
literal cyclic subgroup normalize the other. Their actual join is soluble
and its cardinal is bounded by the two displayed period bounds. No group
recognition, multiplication table, or exact order premise is required. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
open scoped Pointwise
namespace SymmetricSubgroupAsymptotics.FiniteCyclicNormalizerProduct
variable {G : Type*} [Group G] [Finite G]

theorem powers_le_normalizer (r y : G) (k : ℕ) (h : y*r*y⁻¹=r^k) :
    Subgroup.zpowers y ≤ Subgroup.normalizer (Subgroup.zpowers r : Set G) := by
  apply Subgroup.zpowers_le.mpr
  have hpres : Subgroup.zpowers r ≤
      (Subgroup.zpowers r).comap (MulAut.conj y).toMonoidHom := by
    apply Subgroup.zpowers_le.mpr
    change y*r*y⁻¹ ∈ Subgroup.zpowers r
    rw [h]
    exact (Subgroup.zpowers r).pow_mem (Subgroup.mem_zpowers r) k
  apply Subgroup.mem_normalizer_fintype
  intro x hx
  exact hpres hx

private theorem product_cover (r y : G) (k : ℕ) (h : y*r*y⁻¹=r^k)
    (x : G) (hx : x ∈ Subgroup.zpowers r ⊔ Subgroup.zpowers y) :
    ∃ a ∈ Subgroup.zpowers r, ∃ b ∈ Subgroup.zpowers y, a*b=x := by
  have hm : x ∈ (Subgroup.zpowers r : Set G) * (Subgroup.zpowers y : Set G) := by
    rw [← Subgroup.coe_mul_of_right_le_normalizer_left _ _ (powers_le_normalizer r y k h)]
    exact hx
  exact hm

theorem join_solvable (r y : G) (k : ℕ) (h : y*r*y⁻¹=r^k) :
    IsSolvable ↥(Subgroup.zpowers r ⊔ Subgroup.zpowers y) := by
  letI : IsSolvable (Subgroup.zpowers r) := isSolvable_of_comm (fun a b => mul_comm' a b)
  letI : IsSolvable (Subgroup.zpowers y) := isSolvable_of_comm (fun a b => mul_comm' a b)
  exact CFSGSolubleNormalizerProduct.soluble_of_product_cover
    (Subgroup.zpowers r ⊔ Subgroup.zpowers y) (Subgroup.zpowers r) (Subgroup.zpowers y)
    le_sup_left le_sup_right (powers_le_normalizer r y k h) (product_cover r y k h)

theorem card_join_le_mul (r y : G) (k : ℕ) (h : y*r*y⁻¹=r^k)
    (a b : ℕ) (ha : 0<a) (hb : 0<b) (hr : r^a=1) (hy : y^b=1) :
    Nat.card ↥(Subgroup.zpowers r ⊔ Subgroup.zpowers y) ≤ a*b := by
  let F : Subgroup.zpowers r × Subgroup.zpowers y →
      ↥(Subgroup.zpowers r ⊔ Subgroup.zpowers y) := fun p =>
    ⟨p.1.val*p.2.val,(Subgroup.zpowers r ⊔ Subgroup.zpowers y).mul_mem
      (Subgroup.mem_sup_left p.1.property) (Subgroup.mem_sup_right p.2.property)⟩
  have hF : Function.Surjective F := by
    intro x
    obtain ⟨u,hu,v,hv,he⟩ := product_cover r y k h x.val x.property
    exact ⟨(⟨u,hu⟩,⟨v,hv⟩),Subtype.ext he⟩
  have hc := Nat.card_le_card_of_surjective F hF
  rw [Nat.card_prod,Nat.card_zpowers,Nat.card_zpowers] at hc
  exact hc.trans (Nat.mul_le_mul
    (Nat.le_of_dvd ha (orderOf_dvd_of_pow_eq_one hr))
    (Nat.le_of_dvd hb (orderOf_dvd_of_pow_eq_one hy)))

end SymmetricSubgroupAsymptotics.FiniteCyclicNormalizerProduct
