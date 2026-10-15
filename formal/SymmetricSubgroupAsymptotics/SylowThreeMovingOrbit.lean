import Mathlib.GroupTheory.Sylow
import Mathlib.GroupTheory.Perm.Finite
import Mathlib.Data.Finite.Perm

/-! Detect a moving original Sylow-three orbit through a faithful quotient
whose order is divisible by three. The four-point nonbinary specialization
uses only Lagrange and the prime factors of24, not an action catalogue. -/

set_option autoImplicit false
noncomputable section
open scoped Classical

namespace SymmetricSubgroupAsymptotics

local instance sylowMovingOrbit_primeThree : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩

theorem three_dvd_card_four_point_nonbinary
    {I : Type} [Finite I] (T : Subgroup (Equiv.Perm I))
    (hI : Nat.card I = 4) (hnon : ¬ IsPGroup 2 T) : 3 ∣ Nat.card T := by
  have hdiv : Nat.card T ∣ 24 := by
    have h := T.card_subgroup_dvd_card
    rw [Nat.card_perm, hI] at h
    norm_num at h ⊢
    exact h
  by_contra hthree
  have hcop : (Nat.card T).Coprime 3 :=
    (Nat.prime_three.coprime_iff_not_dvd.mpr hthree).symm
  have htwo : Nat.card T ∣ 2 ^ 3 :=
    hcop.dvd_of_dvd_mul_right (by norm_num; exact hdiv)
  obtain ⟨n, _, hn⟩ := (Nat.dvd_prime_pow Nat.prime_two).mp htwo
  exact hnon (IsPGroup.of_card hn)

/-- The moving orbit belongs to the original Sylow, not a newly selected
Sylow subgroup of the quotient image. -/
theorem sylow_three_exists_moving_orbit
    {G Q I : Type} [Group G] [Finite G] [Group Q] [Finite Q]
    [MulAction G I] [MulAction Q I] [FaithfulSMul Q I] [Finite I]
    (f : G →* Q) (hf : Function.Surjective f)
    (hact : ∀ (g : G) (i : I), g • i = f g • i)
    (hthree : 3 ∣ Nat.card Q) (P : Sylow 3 G) :
    ∃ i : I, 3 ≤ Nat.card (MulAction.orbit P i) := by
  let S : Sylow 3 Q := P.mapSurjective hf
  have hnotone : Nat.card S ≠ 1 := by
    intro hone
    have hc := (S : Subgroup Q).card_mul_index
    rw [hone, one_mul] at hc
    exact S.not_dvd_index (hc.symm ▸ hthree)
  letI : Nontrivial S := Finite.one_lt_card_iff_nontrivial.mp (by
    have hp : 0 < Nat.card S := Nat.card_pos
    omega)
  obtain ⟨q, hq⟩ := exists_ne (1 : S)
  have hmove : ∃ i : I, (q : Q) • i ≠ i := by
    by_contra hi
    push Not at hi
    apply hq
    apply Subtype.ext
    apply eq_of_smul_eq_smul (M := Q) (α := I)
    intro i
    change (q : Q) • i = (1 : Q) • i
    simpa only [one_smul] using hi i
  obtain ⟨i, hi⟩ := hmove
  obtain ⟨g, hg, he⟩ := q.2
  let a : P := ⟨g, hg⟩
  have hai : a • i ≠ i := by
    change g • i ≠ i
    rw [hact, he]
    exact hi
  letI : Nontrivial (MulAction.orbit P i) := ⟨⟨
    ⟨a • i, MulAction.mem_orbit i a⟩,
    ⟨i, MulAction.mem_orbit_self i⟩,
    fun h => hai (congrArg Subtype.val h)⟩⟩
  have hgt : 1 < Nat.card (MulAction.orbit P i) :=
    Finite.one_lt_card_iff_nontrivial.mpr inferInstance
  obtain ⟨n, hn⟩ := P.isPGroup'.card_orbit i
  have hpos : 1 ≤ n := by
    by_contra h
    have hz : n = 0 := by omega
    rw [hn, hz, pow_zero] at hgt
    omega
  refine ⟨i, ?_⟩
  rw [hn]
  simpa only [pow_one] using Nat.pow_le_pow_right (by decide : 0 < 3) hpos

end SymmetricSubgroupAsymptotics

end
