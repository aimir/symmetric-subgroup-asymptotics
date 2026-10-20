import SymmetricSubgroupAsymptotics.PrimitiveAffineDegreeTwoPrimitiveSixteenRows16And17Complements
import SymmetricSubgroupAsymptotics.AlternatingSymmetricComplementChiefBounds

/-! Actual row16/17 source equivalences and all-chief bounds. Faithfulness
is bound to one original generator value, not the nominal group name. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
open scoped Classical
namespace SymmetricSubgroupAsymptotics.PrimitiveSixteenRows16And17ChiefBounds
open PrimitiveAffineDegreeTwoPrimitiveSixteenRows16And17Complements
open AlternatingSymmetricComplementChiefBounds
open Non2UnipotentPrefixFiniteMenu.PrimitiveAffineImprimitiveBlockTransfer

private theorem nontrivial16 : hom16 BinarySixDeletedRepresentation.alpha ≠ 1 := by
  intro h
  have hh : BinaryFourAffineImage.linearPerm (hom16 BinarySixDeletedRepresentation.alpha)=1 := by rw [h,map_one]
  rw [hom16_alpha_original] at hh
  exact (by decide +kernel : DegreeTwoPrimitiveSixteenInterfaces.row16Generators 0 1 ≠ 1)
    (congrArg (fun p : Equiv.Perm (Fin 16) => p 1) hh)

private theorem nontrivial17 : hom17 BinarySixDeletedRepresentation.alpha ≠ 1 := by
  intro h
  have hh : BinaryFourAffineImage.linearPerm (hom17 BinarySixDeletedRepresentation.alpha)=1 := by rw [h,map_one]
  rw [hom17_alpha_original] at hh
  exact (by decide +kernel : DegreeTwoPrimitiveSixteenInterfaces.row17Generators 0 1 ≠ 1)
    (congrArg (fun p : Equiv.Perm (Fin 16) => p 1) hh)

theorem complementMap16_injective : Function.Injective complementMap16 := by
  apply symmetric_hom_injective (n := 6) (by decide)
  refine ⟨⟨BinarySixDeletedRepresentation.alpha,SixPointAlternatingSymmetricGenerators.alpha_even⟩,?_⟩
  intro h
  exact nontrivial16 (congrArg Subtype.val h)

theorem complementMap17_injective : Function.Injective complementMap17 := by
  letI := alternatingGroup.isSimpleGroup (α := Fin 6) (by norm_num)
  apply simple_hom_injective
  refine ⟨⟨BinarySixDeletedRepresentation.alpha,SixPointAlternatingSymmetricGenerators.alpha_even⟩,?_⟩
  intro h
  exact nontrivial17 (congrArg Subtype.val h)

def complementEquiv16 : Equiv.Perm (Fin 6) ≃* R16 :=
  MulEquiv.ofBijective complementMap16 ⟨complementMap16_injective,complementMap16_surjective⟩
def complementEquiv17 : alternatingGroup (Fin 6) ≃* R17 :=
  MulEquiv.ofBijective complementMap17 ⟨complementMap17_injective,complementMap17_surjective⟩

theorem card16 : Nat.card R16=720 := by
  calc
    _=Nat.card (Equiv.Perm (Fin 6)) := Nat.card_congr complementEquiv16.symm.toEquiv
    _=720 := by norm_num [Nat.card_eq_fintype_card,Fintype.card_perm]

theorem card17 : Nat.card R17=360 := by
  calc
    _=Nat.card (alternatingGroup (Fin 6)) := Nat.card_congr complementEquiv17.symm.toEquiv
    _=360 := by simpa only [Nat.card_fin] using (nat_card_alternatingGroup (α := Fin 6))

theorem chief16 (s : ActualChiefSeries R16) : actualChiefSeriesAbelianLength s ≤ 1 :=
  symmetric_equiv_chief_bound 6 (by decide) complementEquiv16.symm s

theorem chief17 (s : ActualChiefSeries R17) : actualChiefSeriesAbelianLength s ≤ 0 :=
  alternating_equiv_chief_bound 6 (by decide) complementEquiv17.symm s

end SymmetricSubgroupAsymptotics.PrimitiveSixteenRows16And17ChiefBounds
