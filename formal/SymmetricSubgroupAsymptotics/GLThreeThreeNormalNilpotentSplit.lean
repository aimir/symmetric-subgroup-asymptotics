import SymmetricSubgroupAsymptotics.GLThreeThreePrimeThirteenReduction
import SymmetricSubgroupAsymptotics.NormalNilpotentSylowImages
import Mathlib.NumberTheory.Divisors

/-! A normal nilpotent subgroup of an actual GL3(F3) subgroup is a
two-group, or supplies an actual normal subgroup of order13, once the
normal three-core has been excluded. -/
set_option autoImplicit false
noncomputable section
open scoped Classical
namespace SymmetricSubgroupAsymptotics.GLThreeThreeNormalNilpotentSplit
open StandardThreeDimensionalLinearGroups
local instance : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
local instance : Fact (Nat.Prime 13) := ⟨by decide⟩

private theorem two_power_receipt : ∀ m ∈ (11232 : ℕ).divisors,
    (¬3∣m) → (¬13∣m) → ∃ e : Fin 6,m=2^e.val := by decide +kernel

theorem two_group_or_normal_thirteen
    {G : Type} [Group G] [Finite G]
    (f : G →* GeneralThree 3) (hf : Function.Injective f)
    (hno3 : ∀ (N : Subgroup G),N.Normal → IsPGroup 3 N → N=⊥)
    (B : Subgroup G) [B.Normal] [Group.IsNilpotent B] :
    IsPGroup 2 B ∨ ∃ P : Subgroup G,P.Normal ∧ Nat.card P=13 := by
  have hBdvd : Nat.card B∣11232 :=
    B.card_subgroup_dvd_card.trans (GLThreeThreePrimeThirteenReduction.actual_order_dvd f hf)
  let P3 : Sylow 3 B := Classical.choice inferInstance
  have hP3 := hno3 ((P3 : Subgroup B).map B.subtype)
    (NormalNilpotentSylowImages.image_normal B P3)
    (NormalNilpotentSylowImages.image_isPGroup B P3)
  have hP3card : Nat.card P3=1 := by
    have hc := congrArg (fun H : Subgroup G => Nat.card H) hP3
    change Nat.card ((P3 : Subgroup B).map B.subtype)=Nat.card (⊥ : Subgroup G) at hc
    rw [NormalNilpotentSylowImages.image_card B P3,Subgroup.card_bot] at hc
    exact hc
  have h3 : ¬3∣Nat.card B := by
    intro hd
    have hv := Nat.prime_three.factorization_pos_of_dvd
      (Nat.card_pos (α := B)).ne' hd
    have hpdiv : 3∣Nat.card P3 := by
      rw [P3.card_eq_multiplicity]
      exact dvd_pow_self 3 hv.ne'
    rw [hP3card] at hpdiv
    norm_num at hpdiv
  by_cases h13 : 13∣Nat.card B
  · right
    let P13 : Sylow 13 B := Classical.choice inferInstance
    have hv : (Nat.card B).factorization 13=1 := by
      have hhi := (Nat.factorization_le_iff_dvd (Nat.card_pos (α := B)).ne'
        (by decide : (11232 : ℕ)≠0)).mpr hBdvd 13
      have hlo := (show Nat.Prime 13 by decide).factorization_pos_of_dvd
        (Nat.card_pos (α := B)).ne' h13
      have hconst : (11232 : ℕ).factorization 13=1 := by decide +kernel
      rw [hconst] at hhi
      omega
    refine ⟨(P13 : Subgroup B).map B.subtype,
      NormalNilpotentSylowImages.image_normal B P13,?_⟩
    rw [NormalNilpotentSylowImages.image_card B P13,P13.card_eq_multiplicity,hv]
    rfl
  · left
    obtain ⟨e,he⟩ := two_power_receipt (Nat.card B)
      (Nat.mem_divisors.mpr ⟨hBdvd,by decide⟩) h3 h13
    exact IsPGroup.of_card he

end SymmetricSubgroupAsymptotics.GLThreeThreeNormalNilpotentSplit
