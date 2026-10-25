import SymmetricSubgroupAsymptotics.ReeGTwoRectangularClassNumerics

/-! A scaled component cube at the actual rectangular small-Ree index.
The field exponent starts at three; one induction pays every larger
exponent, without a finite field or action menu. -/
set_option autoImplicit false
set_option Elab.async false
namespace SymmetricSubgroupAsymptotics.SmallReeScaledClassEnvelopeNumerics

private theorem exponent_le (f : ℕ) (hf : 3 ≤ f) :
    24*f+3 ≤ 3*3^f := by
  induction f,hf using Nat.le_induction with
  | base => norm_num
  | succ f hf ih =>
    calc
      24*(f+1)+3 ≤ 3*(24*f+3) := by omega
      _ ≤ 3*(3*3^f) := Nat.mul_le_mul_left 3 ih
      _ = 3*3^(f+1) := by rw [pow_succ]; ring

theorem scaled_component_cube (f : ℕ) (hf : 3 ≤ f) :
    25*((3^f)^8)^3 ≤ 3^(3*3^f) := by
  have hp : ((3^f)^8)^3=3^(24*f) := by
    rw [←pow_mul,←pow_mul]
    exact congrArg (fun z : ℕ => 3^z) (by ring)
  calc
    25*((3^f)^8)^3 ≤ 3^3*((3^f)^8)^3 :=
      Nat.mul_le_mul_right _ (by decide : (25:ℕ) ≤ 3^3)
    _ = 3^(24*f+3) := by
      rw [hp,←pow_add]
      exact congrArg (fun z : ℕ => 3^z) (Nat.add_comm 3 (24*f))
    _ ≤ 3^(3*3^f) := Nat.pow_le_pow_right (by decide) (exponent_le f hf)

end SymmetricSubgroupAsymptotics.SmallReeScaledClassEnvelopeNumerics
