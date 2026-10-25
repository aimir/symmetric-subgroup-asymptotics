import SymmetricSubgroupAsymptotics.PrimitiveAlternatingSubnormalPartitionWreath
import SymmetricSubgroupAsymptotics.AlternatingConjugacyPartitionBound

/-! Retain the actual full-socle subnormal class theorem, while using
the proved alternating partition bound directly. The uniform outer
budget remains four, including the degree-six exception. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
open scoped Classical
namespace SymmetricSubgroupAsymptotics.PrimitiveSocleRawStructure

variable {G X : Type} [Group G] [Finite G] [Finite X] [MulAction G X]

theorem NonaffineData.subnormal_class_card_le_sharp_partition_wreath
    (D : NonaffineData G X) (m : ℕ) (hm : 5 ≤ m)
    (e : D.Simple ≃* alternatingGroup (Fin m)) (H : Subgroup G) (hH : H.IsSubnormal) :
    Nat.card (ConjClasses H) ≤ (4 * Nat.card (Nat.Partition m)) ^ D.factorCount *
      D.factorCount.factorial := by
  have he : Nat.card (ConjClasses D.Simple) ≤
      Nat.card (ConjClasses (alternatingGroup (Fin m))) :=
    Nat.card_le_card_of_surjective (ConjClasses.map e.symm.toMonoidHom)
      (ConjClasses.map_surjective e.symm.surjective)
  have ha : Nat.card (ConjClasses (alternatingGroup (Fin m))) ≤
      Nat.card (Nat.Partition m) := by
    simpa only [Fintype.card_fin] using
      (AlternatingConjugacyPartitionBound.class_card_le_partitions
        (I := Fin m) (by simpa only [Fintype.card_fin] using (show 2 ≤ m by omega)))
  have ho : Nat.card (Outer D.Simple) ≤ 4 := by
    rw [CFSGReduction.outer_card_congr e]
    exact CFSGAlternatingOuterBound.outer_card_le_four m hm
  have hc : Nat.card (ConjClasses D.Simple) * Nat.card (Outer D.Simple) ≤
      4 * Nat.card (Nat.Partition m) :=
    (Nat.mul_le_mul (he.trans ha) ho).trans_eq (by ring)
  exact (D.subnormal_class_card_le_outer_wreath H hH).trans
    (Nat.mul_le_mul_right _ (Nat.pow_le_pow_left hc D.factorCount))

end SymmetricSubgroupAsymptotics.PrimitiveSocleRawStructure
