import SymmetricSubgroupAsymptotics.LargeAlternatingSingleSmallFibreSubnormalGap
import SymmetricSubgroupAsymptotics.AlternatingMultiFactorSmallFibreGapNumerics

/-! The intermediate alternating-top subgroup gap for every original
socle factor count. The literal source subgroup remains subnormal and
the original proper index is only bounded below by the natural degree. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
open scoped Classical
namespace SymmetricSubgroupAsymptotics.LargeAlternatingSmallFibreSubnormalGap
open PrimitiveSocleRawStructure OriginalBlockClassBound

variable {A Ω X : Type} [Group A] [MulAction A Ω] [MulAction A X]
    [Finite A] [Finite Ω] [Finite X] [FaithfulSMul A Ω]

theorem subnormal_class_cube_gap_of_multi_top (b : Ω → X)
    (hb : ∀ (g : A) (ω : Ω), b (g • ω) = g • b ω)
    (c : ℕ) (hc : c = 2 ∨ c = 3)
    (hsize : ∀ x, Nat.card (originalBlockFibre b x) = c)
    (hn : 4096 ≤ Nat.card X)
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
        (8 * 2 ^ m) ^ D.factorCount * D.factorCount.factorial := by
    intro L hL
    exact (D.subnormal_class_card_le_partition_wreath m hm e L hL).trans
      (Nat.mul_le_mul_right _ (Nat.pow_le_pow_left
        (Nat.mul_le_mul_left 8 (BinaryPartitionBudget.partition_card_le_power m)) _))
  have hbudget : ∀ x (L : Subgroup (Equiv.Perm (originalBlockFibre b x))),
      Nat.card (ConjClasses L) ≤ c := by
    rcases hc with rfl | rfl
    · exact fun x L => SmallPermutationClassBudgets.subgroup_class_card_le_two (hsize x).le L
    · exact fun x L => SmallPermutationClassBudgets.subgroup_class_card_le_three (hsize x).le L
  have hbound := SubnormalSmallFibreTopClassBound.subnormal_class_card_le_power_mul_top_budget
    b hb c hbudget _ htop H hH
  have hnum : (c ^ Nat.card X *
      ((8 * 2 ^ m) ^ D.factorCount * D.factorCount.factorial)) ^ 3 ≤
      5 ^ (c * Nat.card X - 2) := by
    rcases hc with rfl | rfl
    · exact AlternatingMultiFactorSmallFibreGapNumerics.binary_product_cube_gap
        m D.factorCount (Nat.card X) hm hk hn hmlower
    · exact AlternatingMultiFactorSmallFibreGapNumerics.ternary_product_cube_gap
        m D.factorCount (Nat.card X) hm hk hn hmlower
  have hfinal := (Nat.pow_le_pow_left hbound 3).trans hnum
  have hd := GaronziMarotiLargeBlockReduction.card_eq_blocks_mul_fibre b c hsize
  simpa only [hd,Nat.mul_comm (Nat.card X) c] using hfinal

theorem subnormal_class_cube_gap (b : Ω → X)
    (hb : ∀ (g : A) (ω : Ω), b (g • ω) = g • b ω)
    (c : ℕ) (hc : c = 2 ∨ c = 3)
    (hsize : ∀ x, Nat.card (originalBlockFibre b x) = c)
    (hn : 4096 ≤ Nat.card X)
    (D : NonaffineData (Top (A := A) (X := X)) X)
    (m : ℕ) (hm : 5 ≤ m) (e : D.Simple ≃* alternatingGroup (Fin m))
    (K : Subgroup D.Simple) (hK : K ≠ ⊤)
    (hdegree : Nat.card X = K.index ^ D.factorCount)
    (H : Subgroup A) (hH : H.IsSubnormal) :
    Nat.card (ConjClasses H) ^ 3 ≤ 5 ^ (Nat.card Ω - 2) := by
  by_cases hk : 2 ≤ D.factorCount
  · exact subnormal_class_cube_gap_of_multi_top b hb c hc hsize hn D m hm e hk K hK hdegree H hH
  · have hk1 : D.factorCount = 1 := by have h := D.factorCount_pos; omega
    exact LargeAlternatingSingleSmallFibreSubnormalGap.subnormal_class_cube_gap
      b hb c hc hsize hn D m hm e hk1 K hK hdegree H hH

end SymmetricSubgroupAsymptotics.LargeAlternatingSmallFibreSubnormalGap
