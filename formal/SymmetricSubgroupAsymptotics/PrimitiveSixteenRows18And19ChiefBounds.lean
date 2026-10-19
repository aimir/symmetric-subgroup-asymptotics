import SymmetricSubgroupAsymptotics.PrimitiveAffineDegreeTwoPrimitiveSixteenRows18And19Complements
import SymmetricSubgroupAsymptotics.AlternatingSymmetricComplementChiefBounds

/-! Actual row18/19 source equivalences and all-chief bounds. Faithfulness
is bound to one original generator value, not the nominal group name. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
open scoped Classical
namespace SymmetricSubgroupAsymptotics.PrimitiveSixteenRows18And19ChiefBounds
open PrimitiveAffineDegreeTwoPrimitiveSixteenRows18And19Complements
open AlternatingSymmetricComplementChiefBounds BinaryFiveFrameRepresentation

private theorem cycle_image_nontrivial : hom cycle ≠ 1 := by
  intro h
  rw [hom_cycle] at h
  have hv := congrArg (fun r : LinearGroup => r (![1,0,0,0] : Vector)) h
  exact (by decide +kernel :
    PrimitiveAffineDegreeTwoPrimitiveSixteenRow1AffineSocles.cycle (![1,0,0,0] : Vector) ≠
      (![1,0,0,0] : Vector)) hv

theorem complementMap18_injective : Function.Injective complementMap18 := by
  apply symmetric_hom_injective (n := 5) (by decide)
  refine ⟨⟨cycle,cycle_even⟩,?_⟩
  intro h
  exact cycle_image_nontrivial (congrArg Subtype.val h)

theorem complementMap19_injective : Function.Injective complementMap19 := by
  letI := alternatingGroup.isSimpleGroup (α := Fin 5) (by norm_num)
  apply simple_hom_injective
  refine ⟨⟨cycle,cycle_even⟩,?_⟩
  intro h
  exact cycle_image_nontrivial (congrArg Subtype.val h)

def complementEquiv18 : Equiv.Perm (Fin 5) ≃* R18 :=
  MulEquiv.ofBijective complementMap18 ⟨complementMap18_injective,complementMap18_surjective⟩
def complementEquiv19 : alternatingGroup (Fin 5) ≃* R19 :=
  MulEquiv.ofBijective complementMap19 ⟨complementMap19_injective,complementMap19_surjective⟩

theorem card18 : Nat.card R18=120 := by
  calc
    _=Nat.card (Equiv.Perm (Fin 5)) := Nat.card_congr complementEquiv18.symm.toEquiv
    _=120 := by norm_num [Nat.card_eq_fintype_card,Fintype.card_perm]

theorem card19 : Nat.card R19=60 := by
  calc
    _=Nat.card (alternatingGroup (Fin 5)) := Nat.card_congr complementEquiv19.symm.toEquiv
    _=60 := by simpa only [Nat.card_fin] using (nat_card_alternatingGroup (α := Fin 5))

theorem chief18 (s : ActualChiefSeries R18) : actualChiefSeriesAbelianLength s ≤ 1 :=
  symmetric_equiv_chief_bound 5 (by decide) complementEquiv18.symm s

theorem chief19 (s : ActualChiefSeries R19) : actualChiefSeriesAbelianLength s ≤ 0 :=
  alternating_equiv_chief_bound 5 (by decide) complementEquiv19.symm s

end SymmetricSubgroupAsymptotics.PrimitiveSixteenRows18And19ChiefBounds
