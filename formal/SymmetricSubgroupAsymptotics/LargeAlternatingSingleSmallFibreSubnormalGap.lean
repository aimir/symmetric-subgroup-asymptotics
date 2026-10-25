import SymmetricSubgroupAsymptotics.SubnormalSmallFibreTopClassBound
import SymmetricSubgroupAsymptotics.PrimitiveAlternatingSubnormalPartitionWreath
import SymmetricSubgroupAsymptotics.PartitionFiveSeparatedEncoding
import SymmetricSubgroupAsymptotics.AlternatingSmallFibrePartitionGapNumerics

/-! A genuine subgroup gap over a one-factor alternating intermediate
top. The source subgroup is SUBNORMAL; its actual top image is counted
by the original socle/outer wreath theorem, not by top order or subgroup
class-number monotonicity. The degree-six factor eight is retained. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
open scoped Classical
namespace SymmetricSubgroupAsymptotics.LargeAlternatingSingleSmallFibreSubnormalGap
open PrimitiveSocleRawStructure OriginalBlockClassBound

theorem subnormal_class_cube_gap
    {A Ω X : Type} [Group A] [MulAction A Ω] [MulAction A X]
    [Finite A] [Finite Ω] [Finite X] [FaithfulSMul A Ω]
    (b : Ω → X) (hb : ∀ (g : A) (ω : Ω), b (g • ω) = g • b ω)
    (c : ℕ) (hc : c = 2 ∨ c = 3)
    (hsize : ∀ x, Nat.card (originalBlockFibre b x) = c)
    (hn : 4096 ≤ Nat.card X)
    (D : NonaffineData (Top (A := A) (X := X)) X)
    (m : ℕ) (hm : 5 ≤ m) (e : D.Simple ≃* alternatingGroup (Fin m))
    (hk : D.factorCount = 1) (K : Subgroup D.Simple) (hK : K ≠ ⊤)
    (hdegree : Nat.card X = K.index ^ D.factorCount)
    (H : Subgroup A) (hH : H.IsSubnormal) :
    Nat.card (ConjClasses H) ^ 3 ≤ 5 ^ (Nat.card Ω - 2) := by
  have hell := CFSGReduction.leastProperIndex_of_mulEquiv e.symm m
    (CFSGAlternatingMinimumIndex.leastProperIndex_degree m hm)
  have hmb : m ≤ Nat.card X := by
    have hd : Nat.card X = K.index := by simpa only [hk,pow_one] using hdegree
    exact (hell.2 K hK).trans_eq hd.symm
  have hp := PartitionFiveSeparatedEncoding.partition_card_le_separated m
  have hmono : (m + 1) ^ 4 * 6 ^ ((m + 4) / 5) ≤
      (Nat.card X + 1) ^ 4 * 6 ^ ((Nat.card X + 4) / 5) :=
    Nat.mul_le_mul (Nat.pow_le_pow_left (Nat.succ_le_succ hmb) 4)
      (Nat.pow_le_pow_right (by decide : 0 < (6 : ℕ))
        (Nat.div_le_div_right (Nat.add_le_add_right hmb 4)))
  have htop : ∀ L : Subgroup (Top (A := A) (X := X)), L.IsSubnormal →
      Nat.card (ConjClasses L) ≤
        8 * ((Nat.card X + 1) ^ 4 * 6 ^ ((Nat.card X + 4) / 5)) := by
    intro L hL
    have h : Nat.card (ConjClasses L) ≤ 8 * Nat.card (Nat.Partition m) := by
      simpa only [hk,pow_one,Nat.factorial_one,mul_one] using
        D.subnormal_class_card_le_partition_wreath m hm e L hL
    exact h.trans (Nat.mul_le_mul_left 8 (hp.trans hmono))
  have hbudget : ∀ x (L : Subgroup (Equiv.Perm (originalBlockFibre b x))),
      Nat.card (ConjClasses L) ≤ c := by
    rcases hc with rfl | rfl
    · exact fun x L => SmallPermutationClassBudgets.subgroup_class_card_le_two (hsize x).le L
    · exact fun x L => SmallPermutationClassBudgets.subgroup_class_card_le_three (hsize x).le L
  have hrec := SubnormalSmallFibreTopClassBound.subnormal_class_card_le_power_mul_top_budget
    b hb c hbudget _ htop H hH
  have hbound : Nat.card (ConjClasses H) ≤
      c ^ Nat.card X * 8 * (Nat.card X + 1) ^ 4 * 6 ^ ((Nat.card X + 4) / 5) :=
    hrec.trans_eq (by ac_rfl)
  have hnum : (c ^ Nat.card X * 8 * (Nat.card X + 1) ^ 4 *
      6 ^ ((Nat.card X + 4) / 5)) ^ 3 ≤ 5 ^ (c * Nat.card X - 2) := by
    rcases hc with rfl | rfl
    · exact AlternatingSmallFibrePartitionGapNumerics.binary_partition_envelope_cube_gap _ hn
    · exact AlternatingSmallFibrePartitionGapNumerics.ternary_partition_envelope_cube_gap _ hn
  have hfinal := (Nat.pow_le_pow_left hbound 3).trans hnum
  have hd := GaronziMarotiLargeBlockReduction.card_eq_blocks_mul_fibre b c hsize
  simpa only [hd,Nat.mul_comm (Nat.card X) c] using hfinal

end SymmetricSubgroupAsymptotics.LargeAlternatingSingleSmallFibreSubnormalGap
