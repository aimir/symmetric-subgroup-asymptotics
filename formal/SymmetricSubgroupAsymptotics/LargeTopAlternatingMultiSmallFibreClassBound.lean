import SymmetricSubgroupAsymptotics.AlternatingMultiFactorSmallFibreClassNumerics
import SymmetricSubgroupAsymptotics.PrimitiveSocleAlternatingSubnormalClassBound
import SymmetricSubgroupAsymptotics.BinaryPartitionBudget
import SymmetricSubgroupAsymptotics.LargeTopSmallFibreClassBound

/-! The actual alternating top is counted through its original full
socle and outer-wreath embedding. Multiple factors need only the coarse
partition bound2^m. The original index is merely bounded BELOW by m;
it is never identified with the natural alternating degree. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
open scoped Classical BigOperators
namespace SymmetricSubgroupAsymptotics.LargeTopAlternatingMultiSmallFibreClassBound
open PrimitiveSocleRawStructure OriginalBlockClassBound SmallPermutationClassBudgets

variable {G Y : Type} [Group G] [Finite G] [Finite Y] [MulAction G Y]

private theorem alternating_component_class_bound (D : NonaffineData G Y)
    (m : ℕ) (hm : 5 ≤ m) (e : D.Simple ≃* alternatingGroup (Fin m)) :
    Nat.card (ConjClasses D.Simple) * Nat.card (Outer D.Simple) ≤
      8 * Nat.card (Nat.Partition m) := by
  letI : Nontrivial (Fin m) := Finite.one_lt_card_iff_nontrivial.mp (by simp; omega)
  have he : Nat.card (ConjClasses D.Simple) ≤
      Nat.card (ConjClasses (alternatingGroup (Fin m))) :=
    Nat.card_le_card_of_surjective (ConjClasses.map e.symm.toMonoidHom)
      (ConjClasses.map_surjective e.symm.surjective)
  have ha := ConjugacyClassSubgroupIndexBound.class_card_le_index_mul
    (alternatingGroup (Fin m))
  rw [alternatingGroup.index_eq_two] at ha
  have hp : Nat.card (ConjClasses (Equiv.Perm (Fin m))) ≤ Nat.card (Nat.Partition m) := by
    simpa only [Fintype.card_fin] using
      (SymmetricConjugacyPartitionBound.class_card_le_partitions (I := Fin m))
  have hs := he.trans (ha.trans (Nat.mul_le_mul_left 2 hp))
  have ho : Nat.card (Outer D.Simple) ≤ 4 := by
    rw [CFSGReduction.outer_card_congr e]
    exact CFSGAlternatingOuterBound.outer_card_le_four m hm
  exact (Nat.mul_le_mul hs ho).trans_eq (by ring)

theorem class_card_le_partition_wreath (D : NonaffineData G Y)
    (m : ℕ) (hm : 5 ≤ m) (e : D.Simple ≃* alternatingGroup (Fin m)) :
    Nat.card (ConjClasses G) ≤ (8 * Nat.card (Nat.Partition m)) ^ D.factorCount *
      D.factorCount.factorial := by
  have hn : (⊤ : Subgroup G).Normal := inferInstance
  have hs := D.subnormal_class_card_le_outer_wreath (⊤ : Subgroup G) hn.isSubnormal
  have he : Nat.card (ConjClasses G) ≤ Nat.card (ConjClasses (⊤ : Subgroup G)) :=
    Nat.card_le_card_of_surjective
      (ConjClasses.map (Subgroup.topEquiv : (⊤ : Subgroup G) ≃* G).toMonoidHom)
      (ConjClasses.map_surjective (Subgroup.topEquiv : (⊤ : Subgroup G) ≃* G).surjective)
  exact he.trans (hs.trans (Nat.mul_le_mul_right _
    (Nat.pow_le_pow_left (alternating_component_class_bound D m hm e) D.factorCount)))

variable {A Ω X : Type} [Group A] [MulAction A Ω] [MulAction A X]
    [Finite A] [Finite Ω] [Finite X] [FaithfulSMul A Ω]

theorem class_cube_le_of_alternating_multi_top (b : Ω → X)
    (hb : ∀ (a : A) (ω : Ω), b (a • ω) = a • b ω)
    (c : ℕ) (hc : c = 2 ∨ c = 3)
    (hsize : ∀ x, Nat.card (originalBlockFibre b x) = c)
    (hn : 4096 ≤ Nat.card X)
    (D : NonaffineData (Top (A := A) (X := X)) X)
    (m : ℕ) (hm : 5 ≤ m) (e : D.Simple ≃* alternatingGroup (Fin m))
    (hk : 2 ≤ D.factorCount) (K : Subgroup D.Simple) (hK : K ≠ ⊤)
    (hdegree : Nat.card X = K.index ^ D.factorCount) :
    Nat.card (ConjClasses A) ^ 3 ≤ 5 ^ (Nat.card Ω - 1) := by
  letI : Fintype X := Fintype.ofFinite _
  have hell := CFSGReduction.leastProperIndex_of_mulEquiv e.symm m
    (CFSGAlternatingMinimumIndex.leastProperIndex_degree m hm)
  have hmlower : m ^ D.factorCount ≤ Nat.card X :=
    (Nat.pow_le_pow_left (hell.2 K hK) _).trans_eq hdegree.symm
  have htop : Nat.card (ConjClasses (Top (A := A) (X := X))) ≤
      (8 * 2 ^ m) ^ D.factorCount * D.factorCount.factorial :=
    (class_card_le_partition_wreath D m hm e).trans
      (Nat.mul_le_mul_right _ (Nat.pow_le_pow_left
        (Nat.mul_le_mul_left 8 (BinaryPartitionBudget.partition_card_le_power m)) _))
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
  have hbound := hrec'.trans (Nat.mul_le_mul_left _ htop)
  have hnum : (c ^ Nat.card X *
      ((8 * 2 ^ m) ^ D.factorCount * D.factorCount.factorial)) ^ 3 ≤
      5 ^ (c * Nat.card X - 1) := by
    rcases hc with rfl | rfl
    · exact AlternatingMultiFactorSmallFibreClassNumerics.binary_product_cube_le
        m D.factorCount (Nat.card X) hm hk hn hmlower
    · exact AlternatingMultiFactorSmallFibreClassNumerics.ternary_product_cube_le
        m D.factorCount (Nat.card X) hm hk hn hmlower
  have hfinal := (Nat.pow_le_pow_left hbound 3).trans hnum
  have he := GaronziMarotiLargeBlockReduction.card_eq_blocks_mul_fibre b c hsize
  simpa only [he,Nat.mul_comm (Nat.card X) c] using hfinal

end SymmetricSubgroupAsymptotics.LargeTopAlternatingMultiSmallFibreClassBound
