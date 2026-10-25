import SymmetricSubgroupAsymptotics.LargeTopAlternatingMultiSmallFibreClassBound

/-! The partition-wreath count for a SUBNORMAL subgroup of the original
primitive group. The actual full-socle coordinate theorem retains its
correlations. Factor eight includes the degree-six outer exception. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
open scoped Classical
namespace SymmetricSubgroupAsymptotics.PrimitiveSocleRawStructure

variable {G X : Type} [Group G] [Finite G] [Finite X] [MulAction G X]

theorem NonaffineData.subnormal_class_card_le_partition_wreath
    (D : NonaffineData G X) (m : ℕ) (hm : 5 ≤ m)
    (e : D.Simple ≃* alternatingGroup (Fin m)) (H : Subgroup G) (hH : H.IsSubnormal) :
    Nat.card (ConjClasses H) ≤ (8 * Nat.card (Nat.Partition m)) ^ D.factorCount *
      D.factorCount.factorial := by
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
  have hc : Nat.card (ConjClasses D.Simple) * Nat.card (Outer D.Simple) ≤
      8 * Nat.card (Nat.Partition m) :=
    (Nat.mul_le_mul hs ho).trans_eq (by ring)
  exact (D.subnormal_class_card_le_outer_wreath H hH).trans
    (Nat.mul_le_mul_right _ (Nat.pow_le_pow_left hc D.factorCount))

end SymmetricSubgroupAsymptotics.PrimitiveSocleRawStructure
