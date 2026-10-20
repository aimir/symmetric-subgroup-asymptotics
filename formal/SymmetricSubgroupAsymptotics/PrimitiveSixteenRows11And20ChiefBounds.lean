import SymmetricSubgroupAsymptotics.PrimitiveAffineDegreeTwoPrimitiveSixteenRows11And20Complements
import SymmetricSubgroupAsymptotics.AlternatingSymmetricComplementChiefBounds

/-! Literal A8/A7 maps are faithful, by simplicity and one displayed
nonidentity four-bit value. Hence their exact orders and every-chief
abelian-length bounds follow without a finite group or normal census. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
open scoped Classical
namespace SymmetricSubgroupAsymptotics.PrimitiveSixteenRows11And20ChiefBounds
open PrimitiveAffineDegreeTwoPrimitiveSixteenRows11And20Complements
open BinaryFanoHeptadData BinaryFanoHeptadGenerators BinaryFanoHeptadRepresentation
open AlternatingSymmetricComplementChiefBounds

private theorem image11_nontrivial : complementMap11 b8 ≠ 1 := by
  intro h
  have hh : hom11 b8=1 := congrArg Subtype.val h
  rw [hom11_b8] at hh
  have hv := congrArg (fun r : BinaryFourAffineImage.LinearGroup =>
    r (![1,0,0,0] : BinaryFourAffineImage.Vector)) hh
  exact (by decide : a11 (![1,0,0,0] : BinaryFourAffineImage.Vector) ≠
    (![1,0,0,0] : BinaryFourAffineImage.Vector)) hv

private theorem image20_nontrivial : complementMap20 b7 ≠ 1 := by
  intro h
  have hh : hom7 b7=1 := congrArg Subtype.val h
  rw [hom7_b7] at hh
  have hv := congrArg (fun r : BinaryFourAffineImage.LinearGroup =>
    r (![1,0,0,0] : BinaryFourAffineImage.Vector)) hh
  exact (by decide : b20 (![1,0,0,0] : BinaryFourAffineImage.Vector) ≠
    (![1,0,0,0] : BinaryFourAffineImage.Vector)) hv

theorem complementMap11_injective : Function.Injective complementMap11 := by
  letI := alternatingGroup.isSimpleGroup (α := Fin 8) (by norm_num)
  exact simple_hom_injective complementMap11 ⟨b8,image11_nontrivial⟩

theorem complementMap20_injective : Function.Injective complementMap20 := by
  letI := alternatingGroup.isSimpleGroup (α := Fin 7) (by norm_num)
  exact simple_hom_injective complementMap20 ⟨b7,image20_nontrivial⟩

def complementEquiv11 : alternatingGroup (Fin 8) ≃* R11 :=
  MulEquiv.ofBijective complementMap11 ⟨complementMap11_injective,complementMap11_surjective⟩
def complementEquiv20 : alternatingGroup (Fin 7) ≃* R20 :=
  MulEquiv.ofBijective complementMap20 ⟨complementMap20_injective,complementMap20_surjective⟩

theorem card11 : Nat.card R11=20160 := by
  calc
    Nat.card R11=Nat.card (alternatingGroup (Fin 8)) := Nat.card_congr complementEquiv11.symm.toEquiv
    _=20160 := by simpa only [Nat.card_fin] using (nat_card_alternatingGroup (α := Fin 8))

theorem card20 : Nat.card R20=2520 := by
  calc
    Nat.card R20=Nat.card (alternatingGroup (Fin 7)) := Nat.card_congr complementEquiv20.symm.toEquiv
    _=2520 := by simpa only [Nat.card_fin] using (nat_card_alternatingGroup (α := Fin 7))

theorem chief11 (s : ActualChiefSeries R11) : actualChiefSeriesAbelianLength s ≤ 0 :=
  alternating_equiv_chief_bound 8 (by decide) complementEquiv11.symm s

theorem chief20 (s : ActualChiefSeries R20) : actualChiefSeriesAbelianLength s ≤ 0 :=
  alternating_equiv_chief_bound 7 (by decide) complementEquiv20.symm s

end SymmetricSubgroupAsymptotics.PrimitiveSixteenRows11And20ChiefBounds
