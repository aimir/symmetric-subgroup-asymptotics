import SymmetricSubgroupAsymptotics.CFSGReeFFourWeightedBruhatNumerics

/-! Arithmetic for the actual middle-parabolic index. Group and cell
cardinalities are separate structural inputs to the cancellation lemma;
neither is silently supplied by the numerical budget. -/
set_option autoImplicit false
namespace SymmetricSubgroupAsymptotics.CFSGReeFFourParabolicIndexNumerics

def indexUpper (q : ℕ) : ℕ := (1+q)*(1+q^3)*(1+q^6)

theorem index_le_of_card_bounds (q b index : ℕ) (hq : 2≤q)
    (hP : q^12*(q-1)^2*(1+q^2) ≤ b)
    (hG : b*index ≤ q^12*(q-1)^2*
      CFSGReeFFourWeightedBruhatNumerics.weightedMenu q) :
    index ≤ indexUpper q := by
  have hq0 : 0<q := by omega
  have hq1 : 0<q-1 := by omega
  have hfac : q^12*(q-1)^2*CFSGReeFFourWeightedBruhatNumerics.weightedMenu q =
      (q^12*(q-1)^2*(1+q^2))*indexUpper q := by
    rw [CFSGReeFFourWeightedBruhatNumerics.weightedMenu_factor]
    unfold indexUpper
    ring
  have h := (Nat.mul_le_mul_right index hP).trans hG
  rw [hfac] at h
  exact Nat.le_of_mul_le_mul_left h (by positivity)

theorem indexUpper_square_lt (q : ℕ) (hq : 4≤q) :
    (indexUpper q)^2 < q^24 := by
  have hq0 : 0<q := by omega
  have hq1 : 1≤q := by omega
  have hp (n : ℕ) : 1+q^n ≤ 2*q^n := by
    have := one_le_pow₀ hq1 (n := n)
    omega
  have hprod := Nat.mul_le_mul (Nat.mul_le_mul (hp 1) (hp 3)) (hp 6)
  have hb : indexUpper q ≤ 8*q^10 := by
    simpa only [pow_one,indexUpper] using hprod.trans_eq (by ring)
  have hsmall : 64<q^4 :=
    (by decide : 64<(4 : ℕ)^4).trans_le (Nat.pow_le_pow_left hq 4)
  calc
    (indexUpper q)^2 ≤ (8*q^10)^2 := Nat.pow_le_pow_left hb 2
    _ = 64*q^20 := by ring
    _ < q^4*q^20 := Nat.mul_lt_mul_of_pos_right hsmall (pow_pos hq0 _)
    _ = q^24 := by ring

end SymmetricSubgroupAsymptotics.CFSGReeFFourParabolicIndexNumerics
