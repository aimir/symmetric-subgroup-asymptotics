import SymmetricSubgroupAsymptotics.ComponentOrderCubeWreathNumerics

/-! Uniform field/rank ORDER-cube comparisons. Rank growth is controlled
by exponent doubling, while field growth retains the literal power gap.
Only small arithmetic starting inequalities are kernel evaluated; there
is no finite group, subgroup, or action enumeration. -/
set_option autoImplicit false
namespace SymmetricSubgroupAsymptotics.QuadraticRankOrderCubeNumerics

theorem pow_gap_mono (p q d : ℕ) (hpq : p ≤ q) :
    (p + 1) ^ d + q ^ d ≤ (q + 1) ^ d + p ^ d := by
  obtain ⟨t, rfl⟩ := Nat.exists_eq_add_of_le hpq
  induction d with
  | zero => simp
  | succ d ih =>
    have hm := Nat.mul_le_mul_left (p + t + 1) ih
    have h1 : t * p ^ d ≤ t * (p + 1) ^ d :=
      Nat.mul_le_mul_left t (Nat.pow_le_pow_left (by omega) d)
    have h2 : p ^ d ≤ (p + t) ^ d := Nat.pow_le_pow_left (by omega) d
    simp only [pow_succ]
    nlinarith

private theorem field_cube_step (q : ℕ) (hq : 4 ≤ q) : (q + 1) ^ 3 ≤ 2 * q ^ 3 := by
  have h1 := Nat.mul_le_mul_right (q ^ 2) hq
  have h2 := Nat.mul_le_mul_right q hq
  nlinarith

theorem field_tail (q₀ d A b : ℕ) (hq₀ : 4 ≤ q₀)
    (hsmall : 2 ^ A ≤ 5 ^ b) (hgap : q₀ ^ d + b ≤ (q₀ + 1) ^ d)
    (hbase : q₀ ^ (3 * A) ≤ 5 ^ (q₀ ^ d - 1))
    (q : ℕ) (hq : q₀ ≤ q) : q ^ (3 * A) ≤ 5 ^ (q ^ d - 1) := by
  induction q, hq using Nat.le_induction with
  | base => exact hbase
  | succ q hq ih =>
    have hg : q ^ d + b ≤ (q + 1) ^ d := by
      have hh := pow_gap_mono q₀ q d hq
      omega
    have hp : 0 < q ^ d := pow_pos (by omega) _
    have hexp : b + (q ^ d - 1) ≤ (q + 1) ^ d - 1 := by omega
    calc
      (q + 1) ^ (3 * A) = ((q + 1) ^ 3) ^ A := pow_mul _ _ _
      _ ≤ (2 * q ^ 3) ^ A := Nat.pow_le_pow_left (field_cube_step q (by omega)) A
      _ = 2 ^ A * q ^ (3 * A) := by rw [mul_pow, ←pow_mul]
      _ ≤ 5 ^ b * 5 ^ (q ^ d - 1) := Nat.mul_le_mul hsmall ih
      _ = 5 ^ (b + (q ^ d - 1)) := (pow_add _ _ _).symm
      _ ≤ 5 ^ ((q + 1) ^ d - 1) := Nat.pow_le_pow_right (by decide) hexp

theorem rank_tail (q : ℕ) (hq : 2 ≤ q) (E : ℕ → ℕ) (r₀ : ℕ)
    (hdouble : ∀ r, r₀ ≤ r → E (r + 1) ≤ 2 * E r)
    (hbase : q ^ (3 * E r₀) ≤ 5 ^ (q ^ r₀ - 1))
    (r : ℕ) (hr : r₀ ≤ r) : q ^ (3 * E r) ≤ 5 ^ (q ^ r - 1) := by
  induction r, hr using Nat.le_induction with
  | base => exact hbase
  | succ r hr ih =>
    have hexp : 2 * (q ^ r - 1) ≤ q ^ (r + 1) - 1 := by
      calc
        2 * (q ^ r - 1) ≤ 2 * q ^ r - 1 := by omega
        _ ≤ q * q ^ r - 1 := Nat.sub_le_sub_right (Nat.mul_le_mul_right _ hq) 1
        _ = q ^ (r + 1) - 1 := by rw [pow_succ, Nat.mul_comm]
    calc
      q ^ (3 * E (r + 1)) ≤ q ^ (3 * (2 * E r)) :=
        Nat.pow_le_pow_right (by omega) (Nat.mul_le_mul_left 3 (hdouble r hr))
      _ = (q ^ (3 * E r)) ^ 2 := by rw [←pow_mul]; congr 1; ring
      _ ≤ (5 ^ (q ^ r - 1)) ^ 2 := Nat.pow_le_pow_left ih 2
      _ = 5 ^ (2 * (q ^ r - 1)) := by rw [←pow_mul, Nat.mul_comm]
      _ ≤ 5 ^ (q ^ (r + 1) - 1) := Nat.pow_le_pow_right (by decide) hexp

def typeAExponent (r : ℕ) : ℕ := (r + 1) ^ 2 + 2 * r

def unitaryExponent (r : ℕ) : ℕ := 2 * (r + 1) ^ 2 + 2 * r

private theorem typeA_double (r : ℕ) (hr : 2 ≤ r) :
    typeAExponent (r + 1) ≤ 2 * typeAExponent r := by
  unfold typeAExponent
  nlinarith

private theorem unitary_double (r : ℕ) (hr : 2 ≤ r) :
    unitaryExponent (r + 1) ≤ 2 * unitaryExponent r := by
  unfold unitaryExponent
  nlinarith

private theorem typeA_large (q r : ℕ) (hq : 7 ≤ q) (hr : 2 ≤ r) :
    q ^ (3 * typeAExponent r) ≤ 5 ^ (q ^ r - 1) :=
  rank_tail q (by omega) typeAExponent 2 (fun r hr => typeA_double r hr)
    (field_tail 7 2 13 6 (by decide) (by decide) (by decide) (by decide) q hq) r hr

private theorem typeA_medium (q r : ℕ) (hq : 4 ≤ q) (hr : 3 ≤ r) :
    q ^ (3 * typeAExponent r) ≤ 5 ^ (q ^ r - 1) :=
  rank_tail q (by omega) typeAExponent 3 (fun r hr => typeA_double r (by omega))
    (field_tail 4 3 22 10 (by decide) (by decide) (by decide) (by decide) q hq) r hr

private theorem typeA_three (q r : ℕ) (hq : 3 ≤ q) (hr : 4 ≤ r) :
    q ^ (3 * typeAExponent r) ≤ 5 ^ (q ^ r - 1) := by
  by_cases he : q = 3
  · subst q
    exact rank_tail 3 (by decide) typeAExponent 4 (fun r hr => typeA_double r (by omega))
      (by decide) r hr
  · exact typeA_medium q r (by omega) (by omega)

theorem typeA_order_cube (q r : ℕ) (hq : 2 ≤ q) (hr : 2 ≤ r)
    (hcapacity : 7 ≤ q ∨ (4 ≤ q ∧ 3 ≤ r) ∨ (3 ≤ q ∧ 4 ≤ r) ∨ 7 ≤ r) :
    q ^ (3 * typeAExponent r) ≤ 5 ^ (q ^ r - 1) := by
  rcases hcapacity with h | ⟨h, h'⟩ | ⟨h, h'⟩ | h
  · exact typeA_large q r h hr
  · exact typeA_medium q r h h'
  · exact typeA_three q r h h'
  · by_cases he : q = 2
    · subst q
      exact rank_tail 2 (by decide) typeAExponent 7 (fun r hr => typeA_double r (by omega))
        (by decide) r h
    · exact typeA_three q r (by omega) (by omega)

private theorem unitary_large (q r : ℕ) (hq : 10 ≤ q) (hr : 2 ≤ r) :
    q ^ (3 * unitaryExponent r) ≤ 5 ^ (q ^ r - 1) :=
  rank_tail q (by omega) unitaryExponent 2 (fun r hr => unitary_double r hr)
    (field_tail 10 2 22 10 (by decide) (by decide) (by decide) (by decide) q hq) r hr

private theorem unitary_medium (q r : ℕ) (hq : 5 ≤ q) (hr : 3 ≤ r) :
    q ^ (3 * unitaryExponent r) ≤ 5 ^ (q ^ r - 1) :=
  rank_tail q (by omega) unitaryExponent 3 (fun r hr => unitary_double r (by omega))
    (field_tail 5 3 38 17 (by decide) (by decide) (by decide) (by decide) q hq) r hr

private theorem unitary_four (q r : ℕ) (hq : 4 ≤ q) (hr : 4 ≤ r) :
    q ^ (3 * unitaryExponent r) ≤ 5 ^ (q ^ r - 1) :=
  rank_tail q (by omega) unitaryExponent 4 (fun r hr => unitary_double r (by omega))
    (field_tail 4 4 58 26 (by decide) (by decide) (by decide) (by decide) q hq) r hr

private theorem unitary_three (q r : ℕ) (hq : 3 ≤ q) (hr : 5 ≤ r) :
    q ^ (3 * unitaryExponent r) ≤ 5 ^ (q ^ r - 1) := by
  by_cases he : q = 3
  · subst q
    exact rank_tail 3 (by decide) unitaryExponent 5 (fun r hr => unitary_double r (by omega))
      (by decide) r hr
  · exact unitary_four q r (by omega) (by omega)


private theorem unitary_two_seed : (2 : ℕ) ^ (3 * unitaryExponent 8) ≤ 5 ^ (2 ^ 8 - 1) := by
  change (2 : ℕ) ^ 534 ≤ 5 ^ 255
  calc
    (2 : ℕ) ^ 534 ≤ 2 ^ 540 := Nat.pow_le_pow_right (by decide) (by decide)
    _ = (2 ^ 9) ^ 60 := by rw [←pow_mul]
    _ ≤ (5 ^ 4) ^ 60 := Nat.pow_le_pow_left (by decide : (2 : ℕ) ^ 9 ≤ 5 ^ 4) 60
    _ = 5 ^ 240 := by rw [←pow_mul]
    _ ≤ 5 ^ 255 := Nat.pow_le_pow_right (by decide) (by decide)

theorem unitary_order_cube (q r : ℕ) (hq : 2 ≤ q) (hr : 2 ≤ r)
    (hcapacity : 10 ≤ q ∨ (5 ≤ q ∧ 3 ≤ r) ∨ (4 ≤ q ∧ 4 ≤ r) ∨
      (3 ≤ q ∧ 5 ≤ r) ∨ 8 ≤ r) :
    q ^ (3 * unitaryExponent r) ≤ 5 ^ (q ^ r - 1) := by
  rcases hcapacity with h | ⟨h, h'⟩ | ⟨h, h'⟩ | ⟨h, h'⟩ | h
  · exact unitary_large q r h hr
  · exact unitary_medium q r h h'
  · exact unitary_four q r h h'
  · exact unitary_three q r h h'
  · by_cases he : q = 2
    · subst q
      exact rank_tail 2 (by decide) unitaryExponent 8 (fun r hr => unitary_double r (by omega))
        unitary_two_seed r h
    · exact unitary_three q r (by omega) (by omega)

end SymmetricSubgroupAsymptotics.QuadraticRankOrderCubeNumerics
