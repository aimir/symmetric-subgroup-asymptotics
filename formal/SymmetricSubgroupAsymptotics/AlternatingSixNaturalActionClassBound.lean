import SymmetricSubgroupAsymptotics.AlternatingSixClassBound
import SymmetricSubgroupAsymptotics.AlternatingPartitionCubeBudget
import SymmetricSubgroupAsymptotics.AlmostSimpleIndexTwoSubnormalClasses
import SymmetricSubgroupAsymptotics.SymmetricConjugacyPartitionBound

/-! A faithful original degree-six action containing 360 original
subgroup elements has the actual alternating group in its image: the
image subgroup has index two in S6. The original subnormal subgroup is
then counted in that image. This uses no Aut(A6)=S6 assertion. -/
set_option autoImplicit false
noncomputable section
namespace SymmetricSubgroupAsymptotics.AlternatingSixNaturalActionClassBound
open AlmostSimpleIndexTwoSubnormalClasses
variable {G : Type} [Group G] [Finite G]

theorem normal_image_eq_alternating (N : Subgroup G) (hN : Nat.card N = 360)
    (f : G →* Equiv.Perm (Fin 6)) (hf : Function.Injective f) :
    N.map f = alternatingGroup (Fin 6) := by
  have hcard : Nat.card (N.map f) = 360 :=
    (Nat.card_congr (N.equivMapOfInjective f hf).toEquiv).symm.trans hN
  have hperm : Nat.card (Equiv.Perm (Fin 6)) = 720 := by
    rw [Nat.card_perm, Nat.card_fin]
    decide
  have hmul := (N.map f).card_mul_index
  rw [hcard, hperm] at hmul
  exact Equiv.Perm.eq_alternatingGroup_of_index_eq_two (by omega)

theorem subnormal_image (N : Subgroup G) (hN : Nat.card N = 360)
    (f : G →* Equiv.Perm (Fin 6)) (hf : Function.Injective f)
    (H : Subgroup G) (hH : H.IsSubnormal) : (H.map f).IsSubnormal := by
  have hA : alternatingGroup (Fin 6) ≤ f.range := by
    rw [←normal_image_eq_alternating N hN f hf]
    exact Subgroup.map_le_range f N
  have hr : f.range.IsSubnormal := by
    rcases containing_simple_index_two _ _ alternatingGroup.index_eq_two hA with he | he
    · rw [he]
      exact Subgroup.Normal.isSubnormal inferInstance
    · rw [he]
      exact Subgroup.IsSubnormal.top
  have hi : ((H.map f.rangeRestrict).map f.range.subtype).IsSubnormal :=
    (hH.map f.rangeRestrict_surjective).trans' hr
  simpa only [Subgroup.map_map, MonoidHom.subtype_comp_rangeRestrict] using hi

theorem class_cube_le (N : Subgroup G) (hN : Nat.card N = 360)
    (f : G →* Equiv.Perm (Fin 6)) (hf : Function.Injective f)
    (H : Subgroup G) (hH : H.IsSubnormal) :
    Nat.card (ConjClasses H) ^ 3 ≤ 5 ^ 5 := by
  let eH := H.equivMapOfInjective f hf
  have htransport : Nat.card (ConjClasses H) ≤ Nat.card (ConjClasses (H.map f)) :=
    Nat.card_le_card_of_surjective (ConjClasses.map eH.symm.toMonoidHom)
      (ConjClasses.map_surjective eH.symm.surjective)
  apply (Nat.pow_le_pow_left htransport 3).trans
  rcases alternating_subnormal_trichotomy 6 (by decide) (H.map f)
      (subnormal_image N hN f hf H hH) with hs | ha | ht
  · have hc : Nat.card (ConjClasses (H.map f)) ≤ 2 :=
      (Nat.card_le_card_of_surjective (@ConjClasses.mk (H.map f) _)
        ConjClasses.mk_surjective).trans hs
    exact (Nat.pow_le_pow_left hc 3).trans (by decide)
  · rw [ha]
    exact (Nat.pow_le_pow_left AlternatingSixClassBound.alternating_six_class_card_le_seven 3).trans
      (by decide)
  · rw [ht]
    have hc : Nat.card (ConjClasses (⊤ : Subgroup (Equiv.Perm (Fin 6)))) ≤
        Nat.card (ConjClasses (Equiv.Perm (Fin 6))) :=
      Nat.card_le_card_of_surjective
        (ConjClasses.map (Subgroup.topEquiv : (⊤ : Subgroup (Equiv.Perm (Fin 6))) ≃*
          Equiv.Perm (Fin 6)).symm.toMonoidHom)
        (ConjClasses.map_surjective (Subgroup.topEquiv :
          (⊤ : Subgroup (Equiv.Perm (Fin 6))) ≃* Equiv.Perm (Fin 6)).symm.surjective)
    have hp : Nat.card (ConjClasses (Equiv.Perm (Fin 6))) ≤ Nat.card (Nat.Partition 6) := by
      simpa only [Fintype.card_fin] using
        SymmetricConjugacyPartitionBound.class_card_le_partitions (I := Fin 6)
    exact (Nat.pow_le_pow_left (hc.trans hp) 3).trans
      (AlternatingSubnormalFibonacciBudget.partition_cube_le 6 (by decide))

end SymmetricSubgroupAsymptotics.AlternatingSixNaturalActionClassBound
