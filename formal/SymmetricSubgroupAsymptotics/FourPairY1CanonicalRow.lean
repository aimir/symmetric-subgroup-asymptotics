import SymmetricSubgroupAsymptotics.FourPairY1AllNormalSource
import SymmetricSubgroupAsymptotics.PrimitiveAffineEightTransitiveMatch
import SymmetricSubgroupAsymptotics.PrimitiveAffineDegreeTwoFourPairsClassification

/-! Actual canonical Y1/index11. The all-normal scalar-headed certificate
retains every original quotient under the match's point relabelling and
conjugator. The only extra argument is the existing explicit Zmud theorem. -/
set_option autoImplicit false
noncomputable section
namespace SymmetricSubgroupAsymptotics.FourPairY1CanonicalRow
open Non2UnipotentPrefixFiniteMenu
open Non2UnipotentPrefixFiniteMenu.PrimitiveAffineImprimitiveBlockTransfer

def sourceEquivOfMatch (p : PreE7PairActionClass 4)
    (M : DegreeEightCanonicalCatalogue.TransitiveLiteralMatch (preE7PairAction 4 p))
    (hindex : M.index=(11 : Fin 24)) :
    preE7PairAction 4 p ≃* FourPairY1ActualFrame.Original := by
  have heq : (DegreeTwoPairedEightSharedTops.interface M.index).top =
      FourPairY1ActualFrame.Original := by
    rw [hindex]
    rfl
  exact (PermutationStabilizerTransport.groupEquiv _ _ M.points M.conjugator M.matched).trans
    (MulEquiv.subgroupCongr heq)

def rowOfMatch (hZmud : ZmudFaithfulCharacterTupleInput)
    (p : PreE7PairActionClass 4)
    (M : DegreeEightCanonicalCatalogue.TransitiveLiteralMatch (preE7PairAction 4 p))
    (hindex : M.index=(11 : Fin 24)) :
    PublishedDegreeTwoFourPairRow (preE7FourPairNonPairAction p) := by
  let e := sourceEquivOfMatch p M hindex
  let C := FourPairY1AllNormalSource.actionCertificate hZmud
  let S : PreE7Y1SourceData 8 (preE7FourPairNonPairAction p) := {
    width_eq := rfl
    quotient N := by
      letI : N.1.Normal := N.2
      let K := N.1.map e.toMonoidHom
      have hK : K.Normal := N.2.map e.toMonoidHom e.surjective
      letI : K.Normal := hK
      exact (C.quotient ⟨K,hK⟩).comapEquiv (QuotientGroup.congr N.1 K e rfl) }
  exact .easy (.repeatedNaturalA4 S)

end SymmetricSubgroupAsymptotics.FourPairY1CanonicalRow
end
