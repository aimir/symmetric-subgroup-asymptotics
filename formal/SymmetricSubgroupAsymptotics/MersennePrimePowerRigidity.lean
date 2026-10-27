import Mathlib.NumberTheory.Multiplicity
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Linarith
import Lean.Elab.Tactic.Omega

/-! An unconditional arithmetic component of the exceptional PSL2 frontier.
An odd nontrivial perfect power cannot be one less than a power of two.
This proves arithmetic rigidity only, not an arbitrary-action classifier.
-/
set_option autoImplicit false
namespace SymmetricSubgroupAsymptotics.MersennePrimePowerRigidity

theorem exponent_eq_one_of_odd_pow_add_one_eq_two_pow
    (p e a : ℕ) (hp : 2≤p) (hpodd : Odd p) (he : 1≤e) (ha : 2≤a)
    (hsum : p^e+1=2^a) : e=1 := by
  have hpos : 0<p^e := pow_pos (by omega : 0<p) e
  have heodd : Odd e := by
    apply Nat.not_even_iff_odd.mp
    intro heven
    obtain ⟨k,hk⟩ := heven
    have hsquare : p^e=(p^k)^2 := by rw [hk,pow_add,pow_two]
    have hminus : 4∣p^e-1 := by
      rw [hsquare]
      exact dvd_trans (by decide : 4∣8)
        (Nat.eight_dvd_sq_sub_one_of_odd (hpodd.pow : Odd (p^k)))
    have hplus : 4∣p^e+1 := by
      rw [hsum]
      change (2 : ℕ)^2∣2^a
      exact pow_dvd_pow 2 ha
    have hd := Nat.dvd_sub hplus hminus
    have hh : (p^e+1)-(p^e-1)=2 := by omega
    rw [hh] at hd
    norm_num at hd
  have hpnot : ¬(2 : ℤ)∣(p : ℤ) := by exact_mod_cast hpodd.not_two_dvd_nat
  have henot : ¬(2 : ℤ)∣(e : ℤ) := by exact_mod_cast heodd.not_two_dvd_nat
  have hplusNat : 2∣p+1 := even_iff_two_dvd.mp (hpodd.add_odd odd_one)
  have hplusInt : (2 : ℤ)∣(p : ℤ)-(-1) := by
    have hh : (2 : ℤ)∣(p : ℤ)+1 := by exact_mod_cast hplusNat
    simpa only [sub_neg_eq_add] using hh
  have hvaluation : emultiplicity (2 : ℤ) ((p : ℤ)^e+1)=
      emultiplicity (2 : ℤ) ((p : ℤ)+1) := by
    have hh := emultiplicity_pow_sub_pow_of_prime (R := ℤ) Int.prime_two
      (x := (p : ℤ)) (y := (-1 : ℤ)) hplusInt hpnot (n := e) henot
    simpa only [heodd.neg_one_pow,sub_neg_eq_add] using hh
  have hsumInt : (p : ℤ)^e+1=(2 : ℤ)^a := by exact_mod_cast hsum
  have hdivLeft : (2 : ℤ)^a∣(p : ℤ)^e+1 := by
    simpa only [hsumInt] using (dvd_refl ((2 : ℤ)^a))
  have hdivRight : (2 : ℤ)^a∣(p : ℤ)+1 := by
    apply pow_dvd_iff_le_emultiplicity.mpr
    rw [←hvaluation]
    exact pow_dvd_iff_le_emultiplicity.mp hdivLeft
  have hdivNat : 2^a∣p+1 := by exact_mod_cast hdivRight
  have hle : 2^a≤p+1 := Nat.le_of_dvd (by omega : 0<p+1) hdivNat
  have hpowle : p^e≤p := by omega
  have he_le : e≤1 := by
    by_contra hlt
    have hs : p^2≤p^e := Nat.pow_le_pow_right (by omega : 0<p) (by omega : 2≤e)
    nlinarith
  omega

/-- The base need not itself be prime for the rigidity theorem above. -/
theorem exponent_eq_one_of_odd_mersenne_power
    (p e a : ℕ) (hp : 2≤p) (hpodd : Odd p) (he : 1≤e) (ha : 2≤a)
    (hpow : p^e=2^a-1) : e=1 := by
  have hone : 1≤2^a := Nat.one_le_pow _ _ (by decide : 0<2)
  have hsum : p^e+1=2^a := by rw [hpow,Nat.sub_add_cancel hone]
  exact exponent_eq_one_of_odd_pow_add_one_eq_two_pow p e a hp hpodd he ha hsum

end SymmetricSubgroupAsymptotics.MersennePrimePowerRigidity
