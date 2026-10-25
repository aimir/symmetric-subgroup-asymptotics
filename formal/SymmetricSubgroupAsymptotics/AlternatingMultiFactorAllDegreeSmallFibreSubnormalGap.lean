import SymmetricSubgroupAsymptotics.PrimitiveAlternatingSharpSubnormalPartitionWreath
import SymmetricSubgroupAsymptotics.AlternatingSharpMultiFactorSmallFibreGapNumerics
import SymmetricSubgroupAsymptotics.LargeAlternatingSmallFibreSubnormalGap

/-! Every actual alternating top with at least two socle factors has a
binary/ternary subnormal class-cube reserve, at EVERY original degree.
The same D, actual source subgroup and original proper index are kept;
only m^factorCount<=actual degree is deduced. No natural action or
cutoff at 4096 is assumed. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
open scoped Classical
namespace SymmetricSubgroupAsymptotics.AlternatingMultiFactorAllDegreeSmallFibreSubnormalGap
open PrimitiveSocleRawStructure OriginalBlockClassBound

variable {A Ω X : Type} [Group A] [MulAction A Ω] [MulAction A X]
    [Finite A] [Finite Ω] [Finite X] [FaithfulSMul A Ω]

theorem subnormal_class_cube_gap (b : Ω → X)
    (hb : ∀ (g : A) (ω : Ω), b (g • ω) = g • b ω)
    (c : ℕ) (hc : c = 2 ∨ c = 3)
    (hsize : ∀ x, Nat.card (originalBlockFibre b x) = c)
    (D : NonaffineData (Top (A := A) (X := X)) X)
    (m : ℕ) (hm : 5 ≤ m) (e : D.Simple ≃* alternatingGroup (Fin m))
    (hk : 2 ≤ D.factorCount) (K : Subgroup D.Simple) (hK : K ≠ ⊤)
    (hdegree : Nat.card X = K.index ^ D.factorCount)
    (H : Subgroup A) (hH : H.IsSubnormal) :
    Nat.card (ConjClasses H) ^ 3 ≤ 5 ^ (Nat.card Ω - 2) := by
  have hell := CFSGReduction.leastProperIndex_of_mulEquiv e.symm m
    (CFSGAlternatingMinimumIndex.leastProperIndex_degree m hm)
  have hmlower : m ^ D.factorCount ≤ Nat.card X :=
    (Nat.pow_le_pow_left (hell.2 K hK) _).trans_eq hdegree.symm
  have htop : ∀ L : Subgroup (Top (A := A) (X := X)), L.IsSubnormal →
      Nat.card (ConjClasses L) ≤
        (4 * Nat.fib (m+1)) ^ D.factorCount * D.factorCount.factorial := by
    intro L hL
    exact (D.subnormal_class_card_le_sharp_partition_wreath m hm e L hL).trans
      (Nat.mul_le_mul_right _ (Nat.pow_le_pow_left
        (Nat.mul_le_mul_left 4 (PartitionFibonacciBound.partition_card_le_fib m)) _))
  have hbudget : ∀ x (L : Subgroup (Equiv.Perm (originalBlockFibre b x))),
      Nat.card (ConjClasses L) ≤ c := by
    rcases hc with rfl | rfl
    · exact fun x L => SmallPermutationClassBudgets.subgroup_class_card_le_two (hsize x).le L
    · exact fun x L => SmallPermutationClassBudgets.subgroup_class_card_le_three (hsize x).le L
  have hbound := SubnormalSmallFibreTopClassBound.subnormal_class_card_le_power_mul_top_budget
    b hb c hbudget _ htop H hH
  have hnum : (c ^ Nat.card X *
      ((4 * Nat.fib (m+1)) ^ D.factorCount * D.factorCount.factorial)) ^ 3 ≤
      5 ^ (c * Nat.card X - 2) := by
    rcases hc with rfl | rfl
    · exact AlternatingSharpMultiFactorSmallFibreGapNumerics.binary_product_cube_gap
        m D.factorCount (Nat.card X) hm hk hmlower
    · exact AlternatingSharpMultiFactorSmallFibreGapNumerics.ternary_product_cube_gap
        m D.factorCount (Nat.card X) hm hk hmlower
  have hfinal := (Nat.pow_le_pow_left hbound 3).trans hnum
  have hd := GaronziMarotiLargeBlockReduction.card_eq_blocks_mul_fibre b c hsize
  simpa only [hd,Nat.mul_comm (Nat.card X) c] using hfinal


end SymmetricSubgroupAsymptotics.AlternatingMultiFactorAllDegreeSmallFibreSubnormalGap
