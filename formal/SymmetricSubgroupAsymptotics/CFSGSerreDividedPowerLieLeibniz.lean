import SymmetricSubgroupAsymptotics.CFSGSerreDividedPowers
import SymmetricSubgroupAsymptotics.CFSGSerreLocalNilpotence

/-! The divided Leibniz identity is integral in its coefficients. It will
install the bracket on the original least divided-power-stable lattice,
without replacing that lattice by a convenient classical matrix lattice. -/
set_option autoImplicit false
noncomputable section
open scoped BigOperators
namespace SymmetricSubgroupAsymptotics.CFSGSerreDividedPowerLieLeibniz

private theorem factorial_coefficient (n i : ℕ) (hi : i ≤ n) :
    (n.factorial : ℚ)⁻¹ * (n.choose i : ℚ) =
      (i.factorial : ℚ)⁻¹ * ((n-i).factorial : ℚ)⁻¹ := by
  have hn : (n.factorial : ℚ) ≠ 0 := by exact_mod_cast Nat.factorial_ne_zero n
  have ha : (i.factorial : ℚ) ≠ 0 := by exact_mod_cast Nat.factorial_ne_zero i
  have hb : ((n-i).factorial : ℚ) ≠ 0 := by
    exact_mod_cast Nat.factorial_ne_zero (n-i)
  have hc : (n.choose i : ℚ) * (i.factorial : ℚ) *
      ((n-i).factorial : ℚ) = (n.factorial : ℚ) := by
    exact_mod_cast Nat.choose_mul_factorial_mul_factorial hi
  field_simp [hn, ha, hb]
  nlinarith [hc]

theorem derivation_dividedPower_lie {L : Type*} [LieRing L] [LieAlgebra ℚ L]
    (D : LieDerivation ℚ L L) (n : ℕ) (x y : L) :
    (n.factorial : ℚ)⁻¹ • (D.toLinearMap ^ n) ⁅x,y⁆ =
      ∑ i ∈ Finset.range (n+1),
        ⁅(i.factorial : ℚ)⁻¹ • (D.toLinearMap ^ i) x,
         ((n-i).factorial : ℚ)⁻¹ • (D.toLinearMap ^ (n-i)) y⁆ := by
  simp only [Module.End.pow_apply]
  change (n.factorial : ℚ)⁻¹ • D^[n] ⁅x,y⁆ = _
  rw [LieDerivation.iterate_apply_lie', Finset.smul_sum]
  apply Finset.sum_congr rfl
  intro i hi
  have hil : i ≤ n := by have := Finset.mem_range.mp hi; omega
  rw [← Nat.cast_smul_eq_nsmul ℚ, smul_smul, factorial_coefficient n i hil]
  simp only [smul_lie, lie_smul, smul_smul, mul_comm, LieDerivation.coeFn_coe]

open CFSG.Models.Chevalley
variable {r : ℕ} (A : Matrix (Fin r) (Fin r) ℤ)

theorem dividedPower_lie (negative : Bool) (i : Fin r) (k : ℕ)
    (x y : RationalLie A) :
    dividedPower A negative i k ⁅x,y⁆ =
      ∑ j ∈ Finset.range (k+1),
        ⁅dividedPower A negative i j x, dividedPower A negative i (k-j) y⁆ := by
  simpa only [dividedPower, LinearMap.restrictScalars_apply, LinearMap.smul_apply,
    CFSGSerreLocalNilpotence.adDerivation_toLinearMap] using
    derivation_dividedPower_lie
      (CFSGSerreLocalNilpotence.adDerivation (rootVector A negative i)) k x y

end SymmetricSubgroupAsymptotics.CFSGSerreDividedPowerLieLeibniz
