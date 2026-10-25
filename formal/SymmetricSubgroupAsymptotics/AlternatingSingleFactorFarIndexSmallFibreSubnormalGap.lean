import SymmetricSubgroupAsymptotics.PrimitiveAlternatingSharpSubnormalPartitionWreath
import SymmetricSubgroupAsymptotics.AlternatingSingleFactorFarIndexGapNumerics
import SymmetricSubgroupAsymptotics.SubnormalSmallFibreTopClassBound
import SymmetricSubgroupAsymptotics.PartitionFibonacciBound

/-! A single actual alternating socle factor at a degree at least
2m+2. The source group, original top descriptor and subnormal source
subgroup are unchanged. No action recognition or index gap is assumed. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
open scoped Classical
namespace SymmetricSubgroupAsymptotics.AlternatingSingleFactorFarIndexSmallFibreSubnormalGap
open PrimitiveSocleRawStructure OriginalBlockClassBound

variable {A Ω X : Type} [Group A] [MulAction A Ω] [MulAction A X]
    [Finite A] [Finite Ω] [Finite X] [FaithfulSMul A Ω]

theorem subnormal_class_cube_gap (b : Ω → X)
    (hb : ∀ (g : A) (ω : Ω), b (g • ω)=g • b ω)
    (c : ℕ) (hc : c=2 ∨ c=3)
    (hsize : ∀ x, Nat.card (originalBlockFibre b x)=c)
    (D : NonaffineData (Top (A := A) (X := X)) X)
    (m : ℕ) (hm : 5 ≤ m) (e : D.Simple ≃* alternatingGroup (Fin m))
    (hk : D.factorCount=1) (hfar : 2*m+2 ≤ Nat.card X)
    (H : Subgroup A) (hH : H.IsSubnormal) :
    Nat.card (ConjClasses H)^3 ≤ 5^(Nat.card Ω-2) := by
  have htop : ∀ L : Subgroup (Top (A := A) (X := X)), L.IsSubnormal →
      Nat.card (ConjClasses L) ≤ 4*Nat.fib (m+1) := by
    intro L hL
    have h := D.subnormal_class_card_le_sharp_partition_wreath m hm e L hL
    rw [hk,pow_one,Nat.factorial_one,mul_one] at h
    exact h.trans (Nat.mul_le_mul_left 4 (PartitionFibonacciBound.partition_card_le_fib m))
  have hbudget : ∀ x (L : Subgroup (Equiv.Perm (originalBlockFibre b x))),
      Nat.card (ConjClasses L) ≤ c := by
    rcases hc with rfl | rfl
    · exact fun x L => SmallPermutationClassBudgets.subgroup_class_card_le_two (hsize x).le L
    · exact fun x L => SmallPermutationClassBudgets.subgroup_class_card_le_three (hsize x).le L
  have hbound := SubnormalSmallFibreTopClassBound.subnormal_class_card_le_power_mul_top_budget
    b hb c hbudget _ htop H hH
  have hnum : (c^Nat.card X*(4*Nat.fib (m+1)))^3 ≤ 5^(c*Nat.card X-2) := by
    rcases hc with rfl | rfl
    · exact AlternatingSingleFactorFarIndexGapNumerics.binary_product_cube_gap m _ hm hfar
    · exact AlternatingSingleFactorFarIndexGapNumerics.ternary_product_cube_gap m _ hm hfar
  have hfinal := (Nat.pow_le_pow_left hbound 3).trans hnum
  have hd := GaronziMarotiLargeBlockReduction.card_eq_blocks_mul_fibre b c hsize
  simpa only [hd,Nat.mul_comm (Nat.card X) c] using hfinal

end SymmetricSubgroupAsymptotics.AlternatingSingleFactorFarIndexSmallFibreSubnormalGap
