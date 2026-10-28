import Mathlib.GroupTheory.IndexNormal
import Mathlib.GroupTheory.Commutator.Basic
import Mathlib.GroupTheory.SpecificGroups.Cyclic.Basic
import Mathlib.Data.Nat.Prime.Pow
import Mathlib.Tactic

/-! Subgroup facts for a group of prime-cube order whose derived subgroup
has prime order. These statements retain the literal group and subgroup;
no coordinate recognition or prescribed faithful action is used. -/
set_option autoImplicit false
noncomputable section
namespace SymmetricSubgroupAsymptotics.PrimeCubeCentralSubgroupBounds

variable {R : Type*} [Group R] [Finite R] {p : ℕ}

theorem commutator_le_of_index_prime (hp : p.Prime)
    (hR : Nat.card R = p ^ 3) (U : Subgroup R) (hU : U.index = p) :
    commutator R ≤ U := by
  letI : Fact p.Prime := ⟨hp⟩
  letI : U.Normal := Subgroup.normal_of_index_eq_minFac_card (by
    rw [hR, hp.pow_minFac (by decide : (3 : ℕ) ≠ 0)]
    exact hU)
  have hquot : Nat.card (R ⧸ U) = p := by
    simpa only [← U.index_eq_card] using hU
  letI : IsCyclic (R ⧸ U) := isCyclic_of_prime_card (p := p) hquot
  exact Subgroup.Normal.quotient_commutative_iff_commutator_le.mp inferInstance

theorem card_le_prime_of_not_contains_derived (hp : p.Prime)
    (hR : Nat.card R = p ^ 3) (Z U : Subgroup R)
    (hZ : commutator R = Z) (hnot : ¬ Z ≤ U) : Nat.card U ≤ p := by
  obtain ⟨e, he, hcard⟩ := (Nat.dvd_prime_pow hp).mp
    (hR ▸ U.card_subgroup_dvd_card)
  interval_cases e
  · simpa only [hcard, pow_zero] using hp.one_lt.le
  · simpa only [hcard, pow_one] using (le_refl p)
  · have hmul := U.card_mul_index
    rw [hcard, hR] at hmul
    have hidx : U.index = p := by
      apply Nat.eq_of_mul_eq_mul_left (pow_pos hp.pos 2)
      simpa only [pow_succ] using hmul
    exact (hnot (hZ ▸ commutator_le_of_index_prime hp hR U hidx)).elim
  · have htop : U = ⊤ := Subgroup.eq_top_of_card_eq U (hcard.trans hR.symm)
    exact (hnot (by rw [htop]; exact le_top)).elim

theorem inf_eq_bot_of_prime_center_not_le (hp : p.Prime)
    (Z U : Subgroup R) (hZ : Nat.card Z = p) (hnot : ¬ Z ≤ U) :
    U ⊓ Z = ⊥ := by
  have hd : Nat.card ↥(U ⊓ Z) ∣ p := hZ ▸ Subgroup.card_dvd_of_le
    (show U ⊓ Z ≤ Z from inf_le_right)
  rcases hp.eq_one_or_self_of_dvd _ hd with h | h
  · exact Subgroup.eq_bot_of_card_eq _ h
  · have heq : U ⊓ Z = Z := Subgroup.eq_of_le_of_card_ge inf_le_right
      (by rw [h, hZ])
    exact (hnot (heq ▸ inf_le_left)).elim

theorem sup_index_eq_prime (hp : p.Prime)
    (hR : Nat.card R = p ^ 3) (Z U : Subgroup R) [Z.Normal]
    (hZ : Nat.card Z = p) (hU : Nat.card U = p) (hinf : U ⊓ Z = ⊥) :
    (U ⊔ Z).index = p := by
  have hzrel : Z.relIndex (U ⊔ Z) = p := by
    rw [Subgroup.relIndex_sup_right,
      ← Subgroup.inf_relIndex_right Z U, inf_comm, hinf,
      Subgroup.relIndex_bot_left, hU]
  have hzcard : Nat.card (Z.subgroupOf (U ⊔ Z)) = p := by
    rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe
      (show Z ≤ U ⊔ Z from le_sup_right)).toEquiv, hZ]
  have hF : Nat.card ↥(U ⊔ Z) = p ^ 2 := by
    have hm := (Z.subgroupOf (U ⊔ Z)).card_mul_index
    change Nat.card (Z.subgroupOf (U ⊔ Z)) * Z.relIndex (U ⊔ Z) = _ at hm
    rw [hzcard, hzrel] at hm
    simpa only [pow_two] using hm.symm
  have hm := (U ⊔ Z).card_mul_index
  rw [hF, hR] at hm
  apply Nat.eq_of_mul_eq_mul_left (pow_pos hp.pos 2)
  simpa only [pow_succ] using hm

theorem normal_sup_of_derived_le (Z U : Subgroup R)
    (hZ : commutator R ≤ Z) : (U ⊔ Z).Normal :=
  Subgroup.Normal.of_commutator_le R (hZ.trans le_sup_right)

end SymmetricSubgroupAsymptotics.PrimeCubeCentralSubgroupBounds
