import SymmetricSubgroupAsymptotics.CFSGTwistedE6GeckAmbientPositiveSylow
import SymmetricSubgroupAsymptotics.CFSGTwistedE6GeckRegularFixedPositive
import SymmetricSubgroupAsymptotics.CFSGNormTwoCoordinateRegularPositiveUniqueness
import SymmetricSubgroupAsymptotics.CFSGRegularElementSylowIntersection
import SymmetricSubgroupAsymptotics.CFSGCentralTwistedCommutatorLift

/-! The FULL fixed upper subgroup is a Sylow in the actual twist-fixed
E6 matrix group with soluble normalizer. A genuine fixed regular element
forces uniqueness of the ambient upper Sylow; whole generation is separate. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
open scoped Classical
namespace SymmetricSubgroupAsymptotics.CFSGTwistedE6GeckFixedPositiveSylow
open CFSGTwistedE6GeckAmbientPositiveSylow CFSGTwistedE6GeckRegularFixedPositive
open CFSGTwistedE6GeckSourceAction CFSGTwistedE6GeckPositiveTwist
open CFSGTwistedE6GeckMatrixTwist CFSGExceptionalCartanPositiveDefinite
open CFSGNormTwoCoordinateRegularPositiveUniqueness CFSGSerreOrdinaryTwists

local instance (q : CFSG.PrimePower) : Fact q.prime.Prime := ⟨q.prime_isPrime⟩

abbrev MatrixFixed (q : CFSG.PrimePower) :=
  CFSGCentralTwistedCommutatorLift.fixedSubgroup
    (matrixGroupTwist (q.Extension 2) (definingFieldAutomorphism q 2))

abbrev FixedUpper (q : CFSG.PrimePower) :=
  (AmbientPositive (q.Extension 2)).subgroupOf (MatrixFixed q)

theorem regular_unique_positive (K : Type) [Field K] [Finite K] (g : MatrixGroup K)
    (hg : g⁻¹*regularMatrix K*g∈AmbientPositive K) :
    g∈Subgroup.normalizer (AmbientPositive K : Set (MatrixGroup K)) := by
  have hn := mem_normalizer_of_regular_conjugate CartanMatrix.E₆ CartanMatrix.E₆_diag
    CartanMatrix.E₆_transpose E6_positive_definite CartanMatrix.E₆_off_diag_nonpos
    K g.val (regularMatrix K).val g.property (regularMatrix_positive K) (regularMatrix_leading K) hg
  apply Subgroup.mem_normalizer_iff.mpr
  intro x
  exact Subgroup.mem_normalizer_iff.mp hn x.val

def fixedPositiveSylow (q : CFSG.PrimePower) : Sylow q.prime (MatrixFixed q) :=
  CFSGRegularElementSylowIntersection.intersectionSylow
    (ambientPositiveSylow (q.Extension 2) q.prime) (MatrixFixed q) (regularMatrix (q.Extension 2))
    (regularMatrix_positive (q.Extension 2)) (regularMatrix_fixed q) (regular_unique_positive (q.Extension 2))

theorem fixedPositiveSylow_coe (q : CFSG.PrimePower) :
    (fixedPositiveSylow q : Subgroup (MatrixFixed q))=FixedUpper q := rfl

theorem fixed_upper_normalizer_soluble (q : CFSG.PrimePower) :
    IsSolvable (Subgroup.normalizer (FixedUpper q : Set (MatrixFixed q))) := by
  letI : IsSolvable (Subgroup.normalizer
      ((ambientPositiveSylow (q.Extension 2) q.prime : Subgroup (MatrixGroup (q.Extension 2))) :
        Set (MatrixGroup (q.Extension 2)))) := by
    rw [ambientPositiveSylow_coe]
    exact ambient_positive_normalizer_soluble (q.Extension 2)
  exact CFSGRegularElementSylowIntersection.normalizer_intersection_soluble
    (ambientPositiveSylow (q.Extension 2) q.prime) (MatrixFixed q) (regularMatrix (q.Extension 2))
    (regularMatrix_positive (q.Extension 2)) (regularMatrix_fixed q) (regular_unique_positive (q.Extension 2))

end SymmetricSubgroupAsymptotics.CFSGTwistedE6GeckFixedPositiveSylow
