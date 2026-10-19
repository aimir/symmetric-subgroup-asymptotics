import SymmetricSubgroupAsymptotics.MarkedC4BoundedNilpotentTargetConvolution

/-! The literal zero-physical binary character moment is at most one.
This is distinct from the enlarged vertical subgroup family at the same
physical degree, whose Hall polynomial is paid once in the history bound. -/
set_option autoImplicit false
noncomputable section
open scoped Classical BigOperators
namespace SymmetricSubgroupAsymptotics.MarkedC4.ActualBinaryZero

theorem moment_le_one (C r : ℕ) :
    BoundedNilpotentTargetConvolution.binaryMoment C 0 r≤1 := by
  have hsub : Nat.card (BoundedNilpotentTargetConvolution.BinaryFamily C 0)≤1 := by
    exact Finite.card_le_one_iff_subsingleton.mpr inferInstance
  have hh : ∀ P : BoundedNilpotentTargetConvolution.BinaryFamily C 0,
      (Nat.card (P.val →* Multiplicative (ZMod 4)) : ℝ)^r≤1 := by
    intro P
    have hc : Nat.card (P.val →* Multiplicative (ZMod 4))≤1 :=
      Finite.card_le_one_iff_subsingleton.mpr inferInstance
    have hcR : (Nat.card (P.val →* Multiplicative (ZMod 4)) : ℝ)≤1 := by exact_mod_cast hc
    exact (pow_le_pow_left₀ (Nat.cast_nonneg _) hcR r).trans_eq (one_pow r)
  unfold BoundedNilpotentTargetConvolution.binaryMoment
  calc
    _ ≤ ∑ _P : BoundedNilpotentTargetConvolution.BinaryFamily C 0,(1 : ℝ) :=
      Finset.sum_le_sum (fun P _ => hh P)
    _ = (Nat.card (BoundedNilpotentTargetConvolution.BinaryFamily C 0) : ℝ) := by
      simp only [Finset.sum_const,Finset.card_univ,nsmul_eq_mul,mul_one,Nat.card_eq_fintype_card]
    _ ≤ 1 := by exact_mod_cast hsub

end SymmetricSubgroupAsymptotics.MarkedC4.ActualBinaryZero
