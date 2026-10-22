import SymmetricSubgroupAsymptotics.CFSGAffineComponentOrderCapacity
import SymmetricSubgroupAsymptotics.PrimitiveAffineImprimitivePrimeMargin

/-! Every prime local degree at least25 closes by its literal r(r−1)
order divisor. No primitive composition theorem or degree cutoff enters. -/
set_option autoImplicit false
noncomputable section
namespace SymmetricSubgroupAsymptotics

theorem cardFactors_le_log2 {n : ℕ} (hn : n ≠ 0) :
    ArithmeticFunction.cardFactors n ≤ Nat.log2 n := by
  rw [Nat.log2_eq_log_two]
  apply (Nat.le_log_iff_pow_le (by decide : 1<2) hn).2
  simpa only [ArithmeticFunction.cardFactors_apply, MarkedC4.AbelianSectionSize.omega] using
    MarkedC4.AbelianSectionSize.two_pow_omega_le hn

private theorem dyadic_prime_charge (k : ℕ) :
    54272*(k+5)+38400 ≤ 25575*2^(k+4) := by
  induction k with
  | zero => norm_num
  | succ k ih =>
      rw [show k.succ+4=k+4+1 by omega, pow_succ]
      nlinarith

theorem prime_component_integer_budget {r : ℕ} (hr : r.Prime) (hr25 : 25 ≤ r) :
    54272*ArithmeticFunction.cardFactors (r*(r-1))+38400 ≤ 25575*r := by
  have hpred : r-1 ≠ 0 := by omega
  have hc : ArithmeticFunction.cardFactors (r*(r-1)) ≤ Nat.log2 r+1 := by
    rw [ArithmeticFunction.cardFactors_mul hr.ne_zero hpred,
      ArithmeticFunction.cardFactors_apply_prime hr]
    have hm : Nat.log2 (r-1) ≤ Nat.log2 r := by
      simp only [Nat.log2_eq_log_two]
      exact Nat.log_mono_right (Nat.sub_le r 1)
    exact (Nat.add_le_add_left (cardFactors_le_log2 hpred) 1).trans (by omega)
  have hfour : 4 ≤ Nat.log2 r := by
    rw [Nat.log2_eq_log_two]
    apply (Nat.le_log_iff_pow_le (by decide : 1<2) hr.ne_zero).2
    norm_num
    omega
  obtain ⟨k,hk⟩ := Nat.exists_eq_add_of_le hfour
  have hd : 54272*(Nat.log2 r+1)+38400 ≤ 25575*2^Nat.log2 r := by
    rw [hk]
    simpa only [show 4+k+1=k+5 by omega, show 4+k=k+4 by omega] using dyadic_prime_charge k
  have hp : 2^Nat.log2 r ≤ r := by
    rw [Nat.log2_eq_log_two]
    exact Nat.pow_log_le_self 2 hr.ne_zero
  exact (Nat.add_le_add_right (Nat.mul_le_mul_left 54272 hc) 38400).trans
    (hd.trans (Nat.mul_le_mul_left 25575 hp))

namespace Non2UnipotentPrefixFiniteMenu.PrimitiveAffineImprimitiveBlockTransfer.ComponentSource

def of_prime_localDegree_ge_twentyFive_order
    {w : ℕ} {U : PreE7NonPairActionClass w} {basePoint : Fin w}
    (hHalf : TraceyAffineHalfInducedModuleInput) (hLog : TraceyAffineInducedModuleInput)
    (hRefined : TraceyRefinedInducedModuleInput) (hPerm : TraceyPermutationGeneratorInput)
    (block : OriginalMinimalBlock (A:=preE7NonPairAction w U) basePoint)
    (P : PrimitiveAffineProfile block.Component block.Fibre)
    (hr : (Nat.card block.Fibre).Prime) (hr25 : 25 ≤ Nat.card block.Fibre) :
    ComponentSource hHalf hLog hRefined hPerm block P :=
  of_integer_order_charge hHalf hLog hRefined hPerm block P
    (ArithmeticFunction.cardFactors (Nat.card block.Fibre*(Nat.card block.Fibre-1)))
    (trace_abelianLength_le_prime_mul_pred block P hHalf hLog hRefined hPerm hr)
    (prime_component_integer_budget hr hr25)

end Non2UnipotentPrefixFiniteMenu.PrimitiveAffineImprimitiveBlockTransfer.ComponentSource
end SymmetricSubgroupAsymptotics
