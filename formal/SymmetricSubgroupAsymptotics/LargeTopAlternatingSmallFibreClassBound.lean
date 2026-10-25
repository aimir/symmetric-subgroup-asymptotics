import SymmetricSubgroupAsymptotics.LargeTopAlternatingMultiSmallFibreClassBound
import SymmetricSubgroupAsymptotics.PartitionFiveSeparatedEncoding
import SymmetricSubgroupAsymptotics.AlternatingSmallFibrePartitionTailNumerics

/-! Actual binary and ternary block actions with an alternating top.
The original proper index only bounds the natural alternating degree
from below. Four head counts and separated composition starts give the
one-factor class bound; the actual wreath bound handles several factors. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
open scoped Classical BigOperators
namespace SymmetricSubgroupAsymptotics.LargeTopAlternatingSmallFibreClassBound
open PrimitiveSocleRawStructure OriginalBlockClassBound SmallPermutationClassBudgets

variable {A Ω X : Type} [Group A] [MulAction A Ω] [MulAction A X]
    [Finite A] [Finite Ω] [Finite X] [FaithfulSMul A Ω]

theorem class_cube_le_of_alternating_single_top (b : Ω → X)
    (hb : ∀ (a : A) (ω : Ω), b (a • ω) = a • b ω)
    (c : ℕ) (hc : c = 2 ∨ c = 3)
    (hsize : ∀ x, Nat.card (originalBlockFibre b x) = c)
    (hn : 4096 ≤ Nat.card X)
    (D : NonaffineData (Top (A := A) (X := X)) X)
    (m : ℕ) (hm : 5 ≤ m) (e : D.Simple ≃* alternatingGroup (Fin m))
    (hk : D.factorCount = 1) (K : Subgroup D.Simple) (hK : K ≠ ⊤)
    (hdegree : Nat.card X = K.index ^ D.factorCount) :
    Nat.card (ConjClasses A) ^ 3 ≤ 5 ^ (Nat.card Ω - 1) := by
  letI : Fintype X := Fintype.ofFinite _
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
  have htop0 :=
    LargeTopAlternatingMultiSmallFibreClassBound.class_card_le_partition_wreath D m hm e
  have htop : Nat.card (ConjClasses (Top (A := A) (X := X))) ≤
      8 * ((Nat.card X + 1) ^ 4 * 6 ^ ((Nat.card X + 4) / 5)) := by
    have h : Nat.card (ConjClasses (Top (A := A) (X := X))) ≤
        8 * Nat.card (Nat.Partition m) := by
      simpa only [hk,pow_one,Nat.factorial_one,mul_one] using htop0
    exact h.trans (Nat.mul_le_mul_left 8 (hp.trans hmono))
  have hbudget : ∀ x (L : Subgroup (Equiv.Perm (originalBlockFibre b x))),
      Nat.card (ConjClasses L) ≤ c := by
    rcases hc with rfl | rfl
    · exact fun x L => subgroup_class_card_le_two (hsize x).le L
    · exact fun x L => subgroup_class_card_le_three (hsize x).le L
  have hrec := PermutationBlockClassReduction.class_card_le_product_mul_top b hb
    (fun _ => c) hbudget
  have hrec' : Nat.card (ConjClasses A) ≤ c ^ Nat.card X *
      Nat.card (ConjClasses (Top (A := A) (X := X))) := by
    simpa only [Finset.prod_const,Finset.card_univ,Nat.card_eq_fintype_card] using hrec
  have hbound : Nat.card (ConjClasses A) ≤
      c ^ Nat.card X * 8 * (Nat.card X + 1) ^ 4 * 6 ^ ((Nat.card X + 4) / 5) := by
    exact (hrec'.trans (Nat.mul_le_mul_left _ htop)).trans_eq (by ac_rfl)
  have hnum : (c ^ Nat.card X * 8 * (Nat.card X + 1) ^ 4 *
      6 ^ ((Nat.card X + 4) / 5)) ^ 3 ≤ 5 ^ (c * Nat.card X - 1) := by
    rcases hc with rfl | rfl
    · exact AlternatingSmallFibrePartitionTailNumerics.binary_partition_envelope_cube_le
        (Nat.card X) hn
    · exact AlternatingSmallFibrePartitionTailNumerics.ternary_partition_envelope_cube_le
        (Nat.card X) hn
  have hfinal := (Nat.pow_le_pow_left hbound 3).trans hnum
  have he := GaronziMarotiLargeBlockReduction.card_eq_blocks_mul_fibre b c hsize
  simpa only [he,Nat.mul_comm (Nat.card X) c] using hfinal

theorem class_cube_le_of_alternating_top (b : Ω → X)
    (hb : ∀ (a : A) (ω : Ω), b (a • ω) = a • b ω)
    (c : ℕ) (hc : c = 2 ∨ c = 3)
    (hsize : ∀ x, Nat.card (originalBlockFibre b x) = c)
    (hn : 4096 ≤ Nat.card X)
    (D : NonaffineData (Top (A := A) (X := X)) X)
    (m : ℕ) (hm : 5 ≤ m) (e : D.Simple ≃* alternatingGroup (Fin m))
    (K : Subgroup D.Simple) (hK : K ≠ ⊤)
    (hdegree : Nat.card X = K.index ^ D.factorCount) :
    Nat.card (ConjClasses A) ^ 3 ≤ 5 ^ (Nat.card Ω - 1) := by
  by_cases hk : 2 ≤ D.factorCount
  · exact LargeTopAlternatingMultiSmallFibreClassBound.class_cube_le_of_alternating_multi_top
      b hb c hc hsize hn D m hm e hk K hK hdegree
  · have hk1 : D.factorCount = 1 := by have hh := D.factorCount_pos; omega
    exact class_cube_le_of_alternating_single_top b hb c hc hsize hn D m hm e hk1 K hK hdegree

end SymmetricSubgroupAsymptotics.LargeTopAlternatingSmallFibreClassBound
