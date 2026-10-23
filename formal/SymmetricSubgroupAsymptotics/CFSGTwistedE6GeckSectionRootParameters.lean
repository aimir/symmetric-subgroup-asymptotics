import SymmetricSubgroupAsymptotics.CFSGTwistedE6GeckOriginalRootSections
import SymmetricSubgroupAsymptotics.CFSGNormTwoCoordinateWordParameterEquiv
import SymmetricSubgroupAsymptotics.CFSGNormTwoGeckIntegralWord

/-! Every actual positive E6 root line is parametrized by the negative
simple root-word chart of its constructed ORIGINAL fixed conjugator.
The same chart agrees with literal matrixTransport conjugation. This
provides local bijective coordinates for fixed-orbit peeling, rather than
assuming a diagram-stable ordered root list or source faithfulness. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
open scoped Classical
namespace SymmetricSubgroupAsymptotics.CFSGTwistedE6GeckSectionRootParameters
open CFSGTwistedE6GeckOriginalRootSections CFSGTwistedE6GeckDiagramCovariance
open CFSGTwistedE6GeckSourceWordAction CFSGTwistedE6FixedWordClassification
open CFSGExceptionalNormTwoBases CFSGExceptionalCartanPositiveDefinite CFSGNormTwoRootPairing
open CFSGNormTwoCoordinateRootSubgroup CFSGNormTwoCoordinateWordParameterEquiv
open CFSGNormTwoGeckWeylWordAlgebra CFSGNormTwoGeckIntegralWord
open CFSGSerreQuadraticMatrix CFSGSerreQuadraticWeylWord

abbrev RootLine (K : Type) [Field K] (k : Roots CartanMatrix.E₆) :=
  rootSubgroup CartanMatrix.E₆ CartanMatrix.E₆_diag CartanMatrix.E₆_transpose
    E6_positive_definite CartanMatrix.E₆_off_diag_nonpos K k

abbrev sectionWord (k : PositiveRoot) := inverseWord (expandRelative (sectionRelative k))

def sectionParameter (K : Type) [Field K] (k : PositiveRoot) (t : K) : RootLine K k.val :=
  wordParameter CartanMatrix.E₆ CartanMatrix.E₆_diag CartanMatrix.E₆_transpose
    E6_positive_definite CartanMatrix.E₆_off_diag_nonpos k.val (sectionWord k) (sectionNode k)
    (section_degree k) K t

def sectionParameterMulEquiv (K : Type) [Field K] [Finite K] (k : PositiveRoot) :
    Multiplicative K≃*RootLine K k.val :=
  wordParameterMulEquiv CartanMatrix.E₆ CartanMatrix.E₆_diag CartanMatrix.E₆_transpose
    E6_positive_definite CartanMatrix.E₆_off_diag_nonpos k.val (sectionWord k) (sectionNode k)
    (section_degree k) K

theorem sectionParameterMulEquiv_val (K : Type) [Field K] [Finite K]
    (k : PositiveRoot) (t : Multiplicative K) :
    (sectionParameterMulEquiv K k t).val=(sectionParameter K k t.toAdd).val := rfl

theorem matrixTransport_val (q : CFSG.PrimePower) (k : PositiveRoot) :
    (matrixTransport q k).val=canonicalWord rawData (q.Extension 2) (sectionWord k) := by
  change ((matrixWord (q.Extension 2) (expandRelative (sectionRelative k))).val)⁻¹=_
  rw [matrixWord_val]
  have hi := wordUnit_inverseWord CartanMatrix.E₆ CartanMatrix.E₆_transpose E6_positive_definite
    E6Base E6Index (q.Extension 2) (expandRelative (sectionRelative k))
  simpa only [word_eq_canonicalWord] using hi.symm

theorem conjugated_seed_parameter (q : CFSG.PrimePower) (k : PositiveRoot) (t : q.Extension 2) :
    (matrixTransport q k*canonicalElementaryRoot rawData (q.Extension 2) true (sectionNode k) t*
      (matrixTransport q k)⁻¹).val=(sectionParameter (q.Extension 2) k t).val := by
  simp only [Subgroup.coe_mul,Subgroup.coe_inv,matrixTransport_val]
  rfl

end SymmetricSubgroupAsymptotics.CFSGTwistedE6GeckSectionRootParameters
