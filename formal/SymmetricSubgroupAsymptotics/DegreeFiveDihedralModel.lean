import SymmetricSubgroupAsymptotics.DegreeFiveAffineCoordinates

/-! # The literal dihedral subgroup of the natural degree-five affine group -/

set_option autoImplicit false
noncomputable section
open scoped Classical

namespace SymmetricSubgroupAsymptotics
namespace DegreeFiveDihedralModel

def reflection : F20.R := ⟨F20.scalar (-1), Subgroup.mem_top _⟩

theorem reflection_apply (v : AffineModel.V 5 1) :
    (reflection : AffineModel.GLV 5 1) v = -v := by
  ext i
  simp [reflection, F20.scalar_apply]

theorem reflection_sq : reflection * reflection = 1 := by
  apply Subtype.ext
  apply LinearEquiv.ext
  intro v
  change F20.scalar (-1) (F20.scalar (-1) v) = v
  simp [F20.scalar_apply]

theorem reflection_ne_one : reflection ≠ 1 := by
  intro h
  have hv := congrArg (fun r : F20.R => (r : AffineModel.GLV 5 1) F20.e0 0) h
  norm_num [reflection, F20.scalar_apply, F20.e0] at hv
  exact (by decide : (-1 : ZMod 5) ≠ 1) hv

/-- The normal forms use the convention `sr i = s * r i` of mathlib's
dihedral group. In affine coordinates this has translation coordinate `-i`.
-/
def map : DihedralGroup 5 →* F20.G where
  toFun
    | .r i => ⟨Multiplicative.ofAdd (fun _ => i), 1⟩
    | .sr i => ⟨Multiplicative.ofAdd (fun _ => -i), reflection⟩
  map_one' := by
    apply SemidirectProduct.ext
    · rfl
    · rfl
  map_mul' a b := by
    cases a with
    | r i =>
      cases b with
      | r j =>
        apply SemidirectProduct.ext
        · apply Multiplicative.toAdd.injective
          ext k
          simp [DihedralGroup.r_mul_r, SemidirectProduct.mul_left]
        · rfl
      | sr j =>
        apply SemidirectProduct.ext
        · apply Multiplicative.toAdd.injective
          ext k
          simp [DihedralGroup.r_mul_sr, SemidirectProduct.mul_left]
          ring
        · simp [SemidirectProduct.mul_right]
    | sr i =>
      cases b with
      | r j =>
        apply SemidirectProduct.ext
        · apply Multiplicative.toAdd.injective
          ext k
          simp [DihedralGroup.sr_mul_r, SemidirectProduct.mul_left,
            AffineModel.linAut_apply, reflection_apply]
          ring
        · simp [SemidirectProduct.mul_right]
      | sr j =>
        apply SemidirectProduct.ext
        · apply Multiplicative.toAdd.injective
          ext k
          simp [DihedralGroup.sr_mul_sr, SemidirectProduct.mul_left,
            AffineModel.linAut_apply, reflection_apply]
          ring
        · exact reflection_sq.symm

theorem map_injective : Function.Injective map := by
  intro a b hab
  cases a with
  | r i =>
    cases b with
    | r j =>
      have h := congrArg (fun g : F20.G => Multiplicative.toAdd g.left 0) hab
      exact congrArg DihedralGroup.r h
    | sr j =>
      exact False.elim (reflection_ne_one (congrArg SemidirectProduct.right hab).symm)
  | sr i =>
    cases b with
    | r j =>
      exact False.elim (reflection_ne_one (congrArg SemidirectProduct.right hab))
    | sr j =>
      have h := congrArg (fun g : F20.G => Multiplicative.toAdd g.left 0) hab
      have hij : i = j := neg_injective h
      exact congrArg DihedralGroup.sr hij

def half : Subgroup F20.G :=
  (powMonoidHom 2 : Multiplicative (ZMod 4) →* Multiplicative (ZMod 4)).ker.comap
    F20.topC4

theorem mem_half (g : F20.G) : g ∈ half ↔ F20.topC4 g ^ 2 = 1 := Iff.rfl

theorem map_mem_half (d : DihedralGroup 5) : map d ∈ half := by
  rw [mem_half]
  cases d with
  | r i =>
    change F20.c4Equiv (1 : AffineModel.GLV 5 1) ^ 2 = 1
    simp
  | sr i =>
    rw [← map_pow, ← map_pow, pow_two, DihedralGroup.sr_mul_self]
    simp

theorem half_ne_top : half ≠ ⊤ := by
  obtain ⟨g, hg⟩ := F20.topC4_surjective (Multiplicative.ofAdd (1 : ZMod 4))
  intro htop
  have hm : g ∈ half := htop ▸ Subgroup.mem_top g
  rw [mem_half, hg] at hm
  exact (by decide : (Multiplicative.ofAdd (1 : ZMod 4)) ^ 2 ≠ 1) hm

theorem map_range_card : Nat.card map.range = 10 := by
  rw [← Nat.card_congr (MonoidHom.ofInjective map_injective).toEquiv]
  exact DihedralGroup.nat_card

theorem half_card : Nat.card half = 10 := by
  have hle : map.range ≤ half := by
    rintro g ⟨d, rfl⟩
    exact map_mem_half d
  have hlo : 10 ≤ Nat.card half := by
    rw [← map_range_card]
    exact Nat.card_le_card_of_injective (Subgroup.inclusion hle)
      (Subgroup.inclusion_injective hle)
  have hdiv : Nat.card half ∣ 20 := by
    simpa only [F20.card_G] using Subgroup.card_subgroup_dvd_card half
  have hne : Nat.card half ≠ 20 := by
    intro hcard
    apply half_ne_top
    apply Subgroup.eq_of_le_of_card_ge (le_top)
    simp only [Subgroup.card_top]
    rw [F20.card_G]
    exact hcard.ge
  obtain ⟨k, hk⟩ := hdiv
  have hk_le : k ≤ 2 := by
    have hmul := Nat.mul_le_mul_right k hlo
    rw [← hk] at hmul
    omega
  interval_cases k <;> omega

theorem map_range_eq_half : map.range = half := by
  apply Subgroup.eq_of_le_of_card_ge
  · rintro g ⟨d, rfl⟩
    exact map_mem_half d
  · rw [map_range_card, half_card]

/-- The unique affine subgroup on which the cyclic quotient has exponent
two is the actual dihedral group of order ten. -/
def halfEquiv : half ≃* DihedralGroup 5 :=
  (MulEquiv.subgroupCongr map_range_eq_half.symm).trans
    (MonoidHom.ofInjective map_injective).symm

/-- Any order-ten subgroup of the natural degree-five affine group is this
same dihedral subgroup. -/
theorem subgroup_card_ten_eq_half (H : Subgroup F20.G)
    (hH : Nat.card H = 10) : H = half := by
  apply Subgroup.eq_of_le_of_card_ge
  · intro g hg
    rw [mem_half]
    have hten : orderOf (F20.topC4 g) ∣ 10 := by
      apply (orderOf_map_dvd (F20.topC4.comp H.subtype) (⟨g, hg⟩ : H)).trans
      simpa only [hH] using orderOf_dvd_natCard (⟨g, hg⟩ : H)
    have hfour : orderOf (F20.topC4 g) ∣ 4 := by
      simpa only [Nat.card_congr Multiplicative.toAdd, Nat.card_zmod] using
        orderOf_dvd_natCard (F20.topC4 g)
    apply orderOf_dvd_iff_pow_eq_one.mp
    simpa using Nat.dvd_gcd hten hfour
  · rw [hH, half_card]

end DegreeFiveDihedralModel
end SymmetricSubgroupAsymptotics

end
