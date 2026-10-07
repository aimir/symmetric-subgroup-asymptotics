import SymmetricSubgroupAsymptotics.PrimitiveAffineEightFrameRow4ActualBinding
import SymmetricSubgroupAsymptotics.PrimitiveAffineEightFrameRow5ActualBinding
import SymmetricSubgroupAsymptotics.PrimitiveAffineEightFrameRow6ActualBinding
import SymmetricSubgroupAsymptotics.PrimitiveAffineEightFrameRow7ActualBinding

/-!
# Complete actual binding for the common order-288 eight-point top

The literal point stabilizer of the common top has exactly four eligible
order-three quotients.  The local catalogue selects one of them from the
actual affine component map.  This file dispatches that dependent selection
to the corresponding checked finite-frame row, so no external row label is
needed by the degree-four residual assembly.
-/

set_option autoImplicit false
set_option maxHeartbeats 800000
noncomputable section
open scoped Classical Pointwise

namespace SymmetricSubgroupAsymptotics
namespace Non2UnipotentPrefixFiniteMenu
namespace PrimitiveAffineImprimitiveBlockTransfer
namespace PrimitiveAffineEightFrameRows4To7ActualBinding

variable {w : ℕ} {U : PreE7NonPairActionClass w}
  {basePoint : Fin w}
  (block : OriginalMinimalBlock
    (A := preE7NonPairAction w U) basePoint)
  (P : PrimitiveAffineProfile block.Component block.Fibre)
  [Nontrivial block.Fibre]

local instance row4SourceGroup : Group
    PrimitiveAffineEightFrameRow4TopCertificate.Source :=
  PrimitiveAffineEightFrameRow4TopCertificate.group

/-- Every actual local component over the common order-288 literal top is
one of rows 4--7, and therefore has a checked five-slot capacity bound. -/
noncomputable def bounds
    (pointEquiv : block.Points ≃ Fin 8)
    (conjugator : Equiv.Perm (Fin 8))
    (hconjugated :
      MulAut.conj conjugator • relabelSubgroup pointEquiv block.Top =
        PrimitiveAffineEightFrameRows4To7LocalCatalogue.LiteralAction)
    (hr : Nat.card block.Fibre = 4)
    (hD : degreeFourTernaryCore block P = ⊥)
    (hs : Nat.card block.Points = 8) :
    DegreeFourZeroCoreFiniteFrameBounds block P 5 := by
  let selected :=
    PrimitiveAffineEightFrameRows4To7LocalCatalogue.selectExactActual
      block P
      PrimitiveAffineEightFrameRow4TopCertificate.originalEquiv.symm
      pointEquiv conjugator hconjugated hr hD
  obtain ⟨j, M⟩ := selected
  let dispatch : (j : Fin 4) →
      PrimitiveAffineEightFrameRows4To7LocalCatalogue.ExactActualMatch
        block P PrimitiveAffineEightFrameRow4TopCertificate.originalEquiv.symm
        pointEquiv conjugator hconjugated hr hD j →
      DegreeFourZeroCoreFiniteFrameBounds block P 5 :=
    Fin.cases
      (fun M => by
        letI := M
        exact PrimitiveAffineEightFrameRow4ActualBinding.bounds (M := M) block P
          pointEquiv conjugator hconjugated hr hD hs)
      (Fin.cases
        (fun M => by
          letI : PrimitiveAffineEightFrameRows4To7LocalCatalogue.ExactActualMatch
              block P
              PrimitiveAffineEightFrameRow4TopCertificate.originalEquiv.symm
              pointEquiv conjugator hconjugated hr hD (1 : Fin 4) := M
          exact PrimitiveAffineEightFrameRow5ActualBinding.bounds (M := M) block P
            pointEquiv conjugator hconjugated hr hD hs)
        (Fin.cases
          (fun M => by
            letI : PrimitiveAffineEightFrameRows4To7LocalCatalogue.ExactActualMatch
                block P
                PrimitiveAffineEightFrameRow4TopCertificate.originalEquiv.symm
                pointEquiv conjugator hconjugated hr hD (2 : Fin 4) := M
            exact PrimitiveAffineEightFrameRow6ActualBinding.bounds (M := M) block P
              pointEquiv conjugator hconjugated hr hD hs)
          (Fin.cases
            (fun M => by
              letI : PrimitiveAffineEightFrameRows4To7LocalCatalogue.ExactActualMatch
                  block P
                  PrimitiveAffineEightFrameRow4TopCertificate.originalEquiv.symm
                  pointEquiv conjugator hconjugated hr hD (3 : Fin 4) := M
              exact PrimitiveAffineEightFrameRow7ActualBinding.bounds (M := M) block P
                pointEquiv conjugator hconjugated hr hD hs)
            (fun i => Fin.elim0 i))))
  exact dispatch j M

end PrimitiveAffineEightFrameRows4To7ActualBinding
end PrimitiveAffineImprimitiveBlockTransfer
end Non2UnipotentPrefixFiniteMenu
end SymmetricSubgroupAsymptotics

end
