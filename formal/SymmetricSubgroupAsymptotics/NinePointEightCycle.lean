import Mathlib.Dynamics.PeriodicPts.Defs
import Mathlib.Data.Fintype.Card
import Mathlib.GroupTheory.Perm.Basic
import Mathlib.Tactic

/-! An order-eight permutation of a nine-point set fixing one point
acts freely on the other eight points. The proof uses one period-eight
orbit and cardinal saturation, not a permutation census. -/
set_option autoImplicit false
noncomputable section
namespace SymmetricSubgroupAsymptotics.NinePointEightCycle

variable {X : Type*} [Finite X]

theorem minimalPeriod_eq_eight (hX : Nat.card X = 9) (σ : Equiv.Perm X)
    (o : X) (ho : σ o = o) (h8 : σ ^ 8 = 1) (h4 : σ ^ 4 ≠ 1)
    (x : X) (hx : x ≠ o) : Function.minimalPeriod σ x = 8 := by
  classical
  have hpowo (n : ℕ) : (σ ^ n) o = o := by
    induction n with
    | zero => rfl
    | succ n ih => rw [pow_succ, Equiv.Perm.mul_apply, ho, ih]
  obtain ⟨z, hz⟩ : ∃ z : X, (σ ^ 4) z ≠ z := by
    by_contra! hfix
    exact h4 (Equiv.ext hfix)
  have hz0 : z ≠ o := by intro he; exact hz (he ▸ hpowo 4)
  have hperiod : Function.IsPeriodicPt σ 8 z := by
    change (σ ^ 8) z = z
    rw [h8]
    rfl
  have hd : Function.minimalPeriod σ z ∣ 2 ^ 3 := hperiod.minimalPeriod_dvd
  obtain ⟨e, he, heq⟩ := (Nat.dvd_prime_pow Nat.prime_two).mp hd
  have hmin : Function.minimalPeriod σ z = 8 := by
    interval_cases e
    · have hh : Function.IsPeriodicPt σ 4 z :=
        (Function.isPeriodicPt_iff_minimalPeriod_dvd).mpr (by rw [heq]; decide)
      exact (hz hh).elim
    · have hh : Function.IsPeriodicPt σ 4 z :=
        (Function.isPeriodicPt_iff_minimalPeriod_dvd).mpr (by rw [heq]; decide)
      exact (hz hh).elim
    · have hh : Function.IsPeriodicPt σ 4 z :=
        (Function.isPeriodicPt_iff_minimalPeriod_dvd).mpr (by rw [heq]; decide)
      exact (hz hh).elim
    · exact heq
  let f : Fin 8 → {y : X // y ≠ o} := fun i => ⟨(σ ^ i.val) z, by
    intro hi
    have hh : (σ ^ i.val) z = (σ ^ i.val) o := hi.trans (hpowo i.val).symm
    exact hz0 ((σ ^ i.val).injective hh)⟩
  have hf : Function.Injective f := by
    intro i j hij
    apply Fin.ext
    apply (Function.iterate_eq_iterate_iff_of_lt_minimalPeriod (f := σ) (x := z)
      (by simpa only [hmin] using i.isLt) (by simpa only [hmin] using j.isLt)).mp
    exact congrArg Subtype.val hij
  have hcard : Nat.card {y : X // y ≠ o} = 8 := by
    letI : Fintype X := Fintype.ofFinite X
    rw [Nat.card_eq_fintype_card, Fintype.card_subtype_compl (fun y : X => y = o),
      Fintype.card_subtype_eq, ← Nat.card_eq_fintype_card, hX]
  have hs : Function.Surjective f :=
    (hf.bijective_of_nat_card_le (by rw [hcard, Nat.card_fin])).2
  obtain ⟨i, hi⟩ := hs ⟨x, hx⟩
  have hval : (σ ^ i.val) z = x := congrArg Subtype.val hi
  rw [← hval]
  exact (Function.minimalPeriod_apply_iterate
    (Function.mk_mem_periodicPts (by decide : 0 < 8) hperiod) i.val).trans hmin

theorem no_short_nonzero_fixed (hX : Nat.card X = 9) (σ : Equiv.Perm X)
    (o : X) (ho : σ o = o) (h8 : σ ^ 8 = 1) (h4 : σ ^ 4 ≠ 1)
    (x : X) (hx : x ≠ o) (k : ℕ) (hk : 0 < k) (hk8 : k < 8) :
    (σ ^ k) x ≠ x := by
  intro he
  have hd : Function.minimalPeriod σ x ∣ k :=
    (show Function.IsPeriodicPt σ k x from he).minimalPeriod_dvd
  rw [minimalPeriod_eq_eight hX σ o ho h8 h4 x hx] at hd
  exact (not_le_of_gt hk8) (Nat.le_of_dvd hk hd)

end SymmetricSubgroupAsymptotics.NinePointEightCycle
