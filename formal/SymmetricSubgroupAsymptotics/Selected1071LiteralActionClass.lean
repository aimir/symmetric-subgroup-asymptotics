import SymmetricSubgroupAsymptotics.Selected1071ActualCentralRepeat
import SymmetricSubgroupAsymptotics.Selected1071OriginalTransitive
import SymmetricSubgroupAsymptotics.Non2TransitiveActionClasses
import SymmetricSubgroupAsymptotics.Non2PreE7NonPairPhysicalFrontier
import SymmetricSubgroupAsymptotics.BinaryPairFrameTransport

/-! The literal original action determines an actual pre-E7 action class.
Its chosen representative is bound by genuine point conjugacy. No catalogue
index or historical label is accepted as the group-equivalence witness. -/
set_option autoImplicit false
noncomputable section
open scoped Pointwise
namespace SymmetricSubgroupAsymptotics.Selected1071QuotientGraph
open Non2UnipotentPrefixFiniteMenu

 theorem original_not_binary : ¬IsPGroup 2 Original := by
  intro h
  have hC := h.of_surjective (ActualRepeatedAlternatingCentralCoordinates.top originalAlternating 0)
    original_top_surjective
  have hc : Nat.card CyclicThree=3 := by
    rw [Nat.card_congr Multiplicative.toAdd]
    simp
  rcases hC.card_eq_or_dvd with hh | hh <;> norm_num [hc] at hh

private def literalAction : Non2TransitiveAction (Fin 16) :=
  ⟨Original,original_not_binary,inferInstance⟩

def literalActionClass : Non2TransitiveActionClass (Fin 16) := Quotient.mk _ literalAction

private theorem conjugator_exists : ∃ c : Equiv.Perm (Fin 16),
    MulAut.conj c • literalActionClass.representative=Original := by
  have h := Quotient.mk_out (s := non2TransitiveActionSetoid (Fin 16)) literalAction
  exact h

def literalConjugator : Equiv.Perm (Fin 16) := Classical.choose conjugator_exists

theorem literalConjugator_spec :
    MulAut.conj literalConjugator • literalActionClass.representative=Original :=
  Classical.choose_spec conjugator_exists

def literalRepresentative : PreE7NonPairActionClass 16 :=
  ⟨⟨literalActionClass,by
    intro d hd
    cases d <;> norm_num [PairCountLabel.sourceDegree,PairCountLabel.pairCount] at hd⟩,by
    intro d hd _
    have hh := d.pairCount_ge_24
    omega⟩

private theorem literal_relabel :
    relabelSubgroup literalConjugator (preE7NonPairAction 16 literalRepresentative)=Original := by
  calc
    _ = MulAut.conj literalConjugator • literalActionClass.representative := by
      change literalActionClass.representative.map literalConjugator.permCongrHom.toMonoidHom=_
      rw [Subgroup.pointwise_smul_def]
      congr 1
    _ = Original := literalConjugator_spec

/-- The actual representative-to-original equivalence required by the
source consumer is derived from literal point conjugacy. -/
def literalRepresentativeEquiv : preE7NonPairAction 16 literalRepresentative ≃* Original :=
  (BinaryPairFrame.sourceRelabelEquiv
    (U := preE7NonPairAction 16 literalRepresentative) literalConjugator).trans
      (MulEquiv.subgroupCongr literal_relabel)

end SymmetricSubgroupAsymptotics.Selected1071QuotientGraph
