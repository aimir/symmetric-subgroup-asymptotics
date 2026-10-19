import SymmetricSubgroupAsymptotics.PrimitiveAffineDegreeTwoPrimitiveSixteenRows13And15Complements
import SymmetricSubgroupAsymptotics.AlternatingSymmetricComplementChiefBounds

/-! Actual row13/15 source equivalences and all-chief bounds. Faithfulness
is bound to one original generator value, not the nominal group name. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
open scoped Classical
namespace SymmetricSubgroupAsymptotics.PrimitiveSixteenRows13And15ChiefBounds
open PrimitiveAffineDegreeTwoPrimitiveSixteenRows13And15Complements
open AlternatingSymmetricComplementChiefBounds
open Non2UnipotentPrefixFiniteMenu.PrimitiveAffineImprimitiveBlockTransfer

private theorem nontrivial13 : hom13 sourceCycle ≠ 1 := by
  intro h
  have hh : BinaryFourAffineImage.linearPerm (hom13 sourceCycle)=1 := by rw [h,map_one]
  rw [hom13_alpha_original] at hh
  exact (by decide +kernel : DegreeTwoPrimitiveSixteenInterfaces.row13Generators 0 1 ≠ 1)
    (congrArg (fun p : Equiv.Perm (Fin 16) => p 1) hh)

private theorem nontrivial15 : hom15 sourceCycle ≠ 1 := by
  intro h
  have hh : BinaryFourAffineImage.linearPerm (hom15 sourceCycle)=1 := by rw [h,map_one]
  rw [hom15_alpha_original] at hh
  exact (by decide +kernel : DegreeTwoPrimitiveSixteenInterfaces.row15Generators 0 1 ≠ 1)
    (congrArg (fun p : Equiv.Perm (Fin 16) => p 1) hh)

theorem complementMap13_injective : Function.Injective complementMap13 := by
  apply symmetric_hom_injective (n := 5) (by decide)
  refine ⟨⟨sourceCycle,FivePointSixConfigurationAction.a_even⟩,?_⟩
  intro h
  exact nontrivial13 (congrArg Subtype.val h)

theorem complementMap15_injective : Function.Injective complementMap15 := by
  letI := alternatingGroup.isSimpleGroup (α := Fin 5) (by norm_num)
  apply simple_hom_injective
  refine ⟨⟨sourceCycle,FivePointSixConfigurationAction.a_even⟩,?_⟩
  intro h
  exact nontrivial15 (congrArg Subtype.val h)

def complementEquiv13 : Equiv.Perm (Fin 5) ≃* R13 :=
  MulEquiv.ofBijective complementMap13 ⟨complementMap13_injective,complementMap13_surjective⟩
def complementEquiv15 : alternatingGroup (Fin 5) ≃* R15 :=
  MulEquiv.ofBijective complementMap15 ⟨complementMap15_injective,complementMap15_surjective⟩

theorem card13 : Nat.card R13=120 := by
  calc
    _=Nat.card (Equiv.Perm (Fin 5)) := Nat.card_congr complementEquiv13.symm.toEquiv
    _=120 := by norm_num [Nat.card_eq_fintype_card,Fintype.card_perm]

theorem card15 : Nat.card R15=60 := by
  calc
    _=Nat.card (alternatingGroup (Fin 5)) := Nat.card_congr complementEquiv15.symm.toEquiv
    _=60 := by simpa only [Nat.card_fin] using (nat_card_alternatingGroup (α := Fin 5))

theorem chief13 (s : ActualChiefSeries R13) : actualChiefSeriesAbelianLength s ≤ 1 :=
  symmetric_equiv_chief_bound 5 (by decide) complementEquiv13.symm s

theorem chief15 (s : ActualChiefSeries R15) : actualChiefSeriesAbelianLength s ≤ 0 :=
  alternating_equiv_chief_bound 5 (by decide) complementEquiv15.symm s

end SymmetricSubgroupAsymptotics.PrimitiveSixteenRows13And15ChiefBounds
