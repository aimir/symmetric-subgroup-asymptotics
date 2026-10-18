import SymmetricSubgroupAsymptotics.FourPairY345CentralFrames
import SymmetricSubgroupAsymptotics.PrimitiveAffineEightTransitiveMatch

/-! Actual canonical original-source matches for the three remaining
central lifts. Only the already supplied point relabelling and conjugator
are used. Their target certificates remain separate until the selected
graph homomorphisms have actually checked. -/
set_option autoImplicit false
noncomputable section
open scoped Pointwise
namespace SymmetricSubgroupAsymptotics.FourPairY345CanonicalMatches
open Non2UnipotentPrefixFiniteMenu
open Non2UnipotentPrefixFiniteMenu.PrimitiveAffineImprimitiveBlockTransfer
open FourPairY345CentralFrames

/-- Y3/Y4/Y5 are retained top15/top16/top17, canonical entries8,39/40/44. -/
def canonicalIndex : Fin 3 → Fin 24 := ![14,15,16]

private theorem actual_top (k : Fin 3) :
    (DegreeTwoPairedEightSharedTops.interface (canonicalIndex k)).top = source k := by
  fin_cases k
  · change Subgroup.closure
      (Set.range PrimitiveAffineEightFrameTop15TopCertificate.generators) = source 0
    exact source_eq_top15.symm
  · change Subgroup.closure
      (Set.range PrimitiveAffineEightFrameTop16TopCertificate.generators) = source 1
    exact source_eq_top16.symm
  · change Subgroup.closure
      (Set.range PrimitiveAffineEightFrameTop17TopCertificate.generators) = source 2
    exact source_eq_top17.symm

/-- A canonical match on one of the actual three indices gives the same
original group, including the original literal action correspondence. -/
def sourceEquivOfMatch (k : Fin 3) (p : PreE7PairActionClass 4)
    (M : DegreeEightCanonicalCatalogue.TransitiveLiteralMatch (preE7PairAction 4 p))
    (hindex : M.index = canonicalIndex k) : preE7PairAction 4 p ≃* source k := by
  let A := preE7PairAction 4 p
  let B := relabelSubgroup M.points A
  have hconj : relabelSubgroup M.conjugator B = source k := by
    calc
      relabelSubgroup M.conjugator B = MulAut.conj M.conjugator • B := by
        change B.map M.conjugator.permCongrHom.toMonoidHom = _
        rw [Subgroup.pointwise_smul_def]
        congr 1
      _ = (DegreeTwoPairedEightSharedTops.interface M.index).top := M.matched
      _ = source k := by
        rw [hindex]
        exact actual_top k
  exact (BinaryPairFrame.sourceRelabelEquiv (U := A) M.points).trans
    ((BinaryPairFrame.sourceRelabelEquiv (U := B) M.conjugator).trans
      (MulEquiv.subgroupCongr hconj))

end SymmetricSubgroupAsymptotics.FourPairY345CanonicalMatches

end
