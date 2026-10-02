import SymmetricSubgroupAsymptotics.PrimitiveAffineProfileParity

/-!
# The finite prime-power split below degree 343

The affine socle theorem makes the primitive degree a prime power.  This
file proves the elementary arithmetic exhaustion used by the affine
consumer.  In particular, no finite permutation-group census is used to
produce the list of exceptional degrees.
-/

set_option autoImplicit false

namespace SymmetricSubgroupAsymptotics
namespace Non2UnipotentPrefixFiniteMenu

/-- A prime power between five and `342` is even, prime, or one of the ten
odd composite degrees which have separate profile-native consumers. -/
theorem primePower_lt343_classification
    {w p d : ℕ} (hp : p.Prime) (hdegree : w = p ^ d)
    (hw5 : 5 ≤ w) (hw343 : w < 343) :
    Even w ∨ w.Prime ∨
      w = 9 ∨ w = 25 ∨ w = 27 ∨ w = 49 ∨ w = 81 ∨
      w = 121 ∨ w = 125 ∨ w = 169 ∨ w = 243 ∨ w = 289 := by
  by_cases hp2 : p = 2
  · left
    subst p
    rw [hdegree, Nat.even_pow]
    constructor
    · norm_num
    · intro hd0
      subst d
      norm_num at hdegree
      omega
  by_cases hd1 : d = 1
  · right
    left
    simpa [hdegree, hd1] using hp
  have hd2 : 2 ≤ d := by
    have hd0 : d ≠ 0 := by
      intro h
      subst d
      norm_num [hdegree] at hw5
    omega
  have hp3 : 3 ≤ p := by
    have := hp.two_le
    omega
  have hpSq : p ^ 2 ≤ p ^ d :=
    Nat.pow_le_pow_right (by omega) hd2
  have hp19 : p < 19 := by
    have : p ^ 2 < 343 := hpSq.trans_lt (hdegree ▸ hw343)
    nlinarith
  have hd6 : d < 6 := by
    by_contra h
    have h6d : 6 ≤ d := by omega
    have hbase : 3 ^ 6 ≤ p ^ 6 := Nat.pow_le_pow_left hp3 6
    have hexp : p ^ 6 ≤ p ^ d :=
      Nat.pow_le_pow_right (by omega) h6d
    have : 729 ≤ w := by
      rw [hdegree]
      norm_num at hbase
      exact hbase.trans hexp
    omega
  subst w
  interval_cases p <;> interval_cases d
  all_goals norm_num at hp
  all_goals norm_num at hw343
  all_goals norm_num

/-- The even prime powers below degree `128` which can occur after the
width-five cutoff. -/
theorem twoPower_lt128_classification
    {w d : ℕ} (hdegree : w = 2 ^ d) (hw5 : 5 ≤ w) (hw128 : w < 128) :
    w = 8 ∨ w = 16 ∨ w = 32 ∨ w = 64 := by
  have hd3 : 3 ≤ d := by
    by_contra h
    have : d ≤ 2 := by omega
    interval_cases d <;> norm_num [hdegree] at hw5
  have hd7 : d < 7 := by
    by_contra h
    have h7 : 7 ≤ d := by omega
    have : 2 ^ 7 ≤ 2 ^ d := Nat.pow_le_pow_right (by norm_num) h7
    rw [← hdegree] at this
    norm_num at this
    omega
  interval_cases d <;> norm_num [hdegree]

end Non2UnipotentPrefixFiniteMenu
end SymmetricSubgroupAsymptotics
