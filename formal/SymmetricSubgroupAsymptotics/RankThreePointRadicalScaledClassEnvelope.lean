import SymmetricSubgroupAsymptotics.RankOneSharpOrderCubeNumerics

/-! A single rank-three field induction complements the already proved
rank-four-and-higher orthogonal envelope. The actual point-radical
index is retained in the exponent, rather than replaced by a field
power before the exponential comparison. -/
set_option autoImplicit false
set_option Elab.async false
namespace SymmetricSubgroupAsymptotics.RankThreePointRadicalScaledClassEnvelope

private def pointIndex (q : ℕ) : ℕ := (q^2-1)*q^2

private theorem index_identity (q : ℕ) (hq : 3 ≤ q) :
    pointIndex q+q^2=q^4 := by
  have hsub : q^2-1+1=q^2 := by
    have hp := Nat.one_le_pow 2 q (by omega : 1 ≤ q)
    omega
  change (q^2-1)*q^2+q^2=q^4
  calc
    _ = (q^2-1+1)*q^2 := by ring
    _ = q^2*q^2 := congrArg (fun n : ℕ => n*q^2) hsub
    _ = q^4 := by ring

private theorem power_budget (q : ℕ) (hq : 3 ≤ q) :
    25*q^66 ≤ 3^(pointIndex q) := by
  induction q,hq using Nat.le_induction with
  | base => decide +kernel
  | succ q hq ih =>
    have hs := RankOneSharpOrderCubeNumerics.polynomial_step (3^32) 66 3 q
      (by decide) hq (by decide +kernel)
    have hstep : pointIndex q+32 ≤ pointIndex (q+1) := by
      have h₀ := index_identity q hq
      have h₁ := index_identity (q+1) (by omega)
      have hq2 : 9 ≤ q^2 := (by decide : 9 ≤ (3:ℕ)^2).trans
        (Nat.pow_le_pow_left hq 2)
      nlinarith
    calc
      25*(q+1)^66 ≤ 25*(3^32*q^66) := Nat.mul_le_mul_left 25 hs
      _ = 3^32*(25*q^66) := by ring
      _ ≤ 3^32*3^(pointIndex q) := Nat.mul_le_mul_left _ ih
      _ = 3^(32+pointIndex q) := (pow_add _ _ _).symm
      _ ≤ 3^(pointIndex (q+1)) := Nat.pow_le_pow_right (by decide) (by omega)

private theorem class_equation_power (q : ℕ) (hq : 3 ≤ q) :
    (q^21/pointIndex q+1)*q^3 ≤ q^22 := by
  have hqpos : 0 < q := by omega
  have hq1 : 1 ≤ q := by omega
  have hden : q^3 ≤ pointIndex q := by
    have hquad : q ≤ q^2-1 := by
      have hh : q^2-1+1=q^2 := Nat.sub_add_cancel
        (Nat.one_le_pow 2 q hq1)
      nlinarith
    calc
      q^3 = q*q^2 := by ring
      _ ≤ (q^2-1)*q^2 := Nat.mul_le_mul_right _ hquad
      _ = pointIndex q := rfl
  have hdiv : q^21/pointIndex q ≤ q^18 := by
    calc
      _ ≤ q^21/q^3 := Nat.div_le_div_left hden (pow_pos hqpos _)
      _ = q^18 := by
        rw [show q^21=q^18*q^3 by ring,Nat.mul_div_cancel _ (pow_pos hqpos _)]
  have hadd : q^18+1 ≤ q^19 := by
    have hp : 1 ≤ q^18 := Nat.one_le_pow _ _ hq1
    have hh := Nat.mul_le_mul_right (q^18) (by omega : 2 ≤ q)
    rw [show q^19=q*q^18 from pow_succ' q 18]
    omega
  calc
    _ ≤ (q^18+1)*q^3 := Nat.mul_le_mul_right _ (Nat.add_le_add_right hdiv 1)
    _ ≤ q^19*q^3 := Nat.mul_le_mul_right _ hadd
    _ = q^22 := by ring

theorem scaled_class_equation_budget (q : ℕ) (hq : 3 ≤ q) :
    25*((q^21/((q^2-1)*q^2)+1)*q^3)^3 ≤ 3^((q^2-1)*q^2) := by
  have hp := Nat.mul_le_mul_left 25 (Nat.pow_le_pow_left (class_equation_power q hq) 3)
  have he : (q^22)^3=q^66 := by rw [←pow_mul]
  rw [he] at hp
  exact hp.trans (power_budget q hq)

end SymmetricSubgroupAsymptotics.RankThreePointRadicalScaledClassEnvelope
