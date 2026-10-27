import SymmetricSubgroupAsymptotics.CFSGMathieuTwelveSelectedInvolutionOrbitComplete
import SymmetricSubgroupAsymptotics.FiniteConjugacyCentralizerCard
import SymmetricSubgroupAsymptotics.External.CFSG.Certificates.Mathieu12.Cardinality
import Mathlib.GroupTheory.Index

/-! Exact original centralizer cardinality from the independently certified
495-element class and original group order95040. No class-size/centralizer
premise, new membership converse, or abstract model identification is used. -/
set_option autoImplicit false
noncomputable section
namespace SymmetricSubgroupAsymptotics.CFSGMathieuTwelveSelectedInvolutionCentralizerCard
open CFSG.Certificates.Mathieu12 CFSGMathieuTwelvePresentationWords

theorem original_x_centralizer_card :
    Nat.card (Subgroup.centralizer ({x} : Set M12)) = 192 := by
  let C : Subgroup M12 := Subgroup.centralizer ({x} : Set M12)
  have hd : Nat.card C ∣ Nat.card M12 := ⟨C.index,C.card_mul_index.symm⟩
  have hmul : Nat.card {g : M12 // IsConj g x} * Nat.card C = Nat.card M12 := by
    rw [SymmetricSubgroupAsymptotics.isConj_card_eq_div_centralizer]
    exact Nat.div_mul_cancel hd
  rw [CFSGMathieuTwelveSelectedInvolutionOrbitComplete.selected_class_card,
    M12Cardinality.card_M12] at hmul
  change Nat.card C = 192
  omega

end SymmetricSubgroupAsymptotics.CFSGMathieuTwelveSelectedInvolutionCentralizerCard
