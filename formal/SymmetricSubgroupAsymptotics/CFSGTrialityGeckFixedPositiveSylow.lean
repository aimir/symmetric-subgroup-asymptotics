import SymmetricSubgroupAsymptotics.CFSGTrialityGeckAmbientPositiveSylow
import SymmetricSubgroupAsymptotics.CFSGTrialityGeckRegularFixedPositive
import SymmetricSubgroupAsymptotics.CFSGNormTwoCoordinateRegularPositiveUniqueness
import SymmetricSubgroupAsymptotics.CFSGRegularElementSylowIntersection
import SymmetricSubgroupAsymptotics.CFSGCentralTwistedCommutatorLift

/-! The full fixed positive subgroup is a Sylow in the ACTUAL fixed
matrix group and has soluble normalizer. The fixed regular element at
parameter one forces ambient Sylow containment, including in
characteristics two and three. Full fixed ambient generation is not
assumed or asserted. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
open scoped Classical
namespace SymmetricSubgroupAsymptotics.CFSGTrialityGeckFixedPositiveSylow
open CFSGTrialityD4NormTwo CFSGTrialityGeckDiagramCovariance
open CFSGTrialityGeckSourceWordAction CFSGTrialityGeckMatrixGroupTwist
open CFSGTrialityGeckPositiveTwist CFSGTrialityGeckAmbientPositiveSylow
open CFSGTrialityGeckRegularFixedPositive CFSGNormTwoCoordinateRegularPositiveUniqueness

abbrev MatrixFixed (K : Type) [Field K] (σ : K ≃+* K) :=
  CFSGCentralTwistedCommutatorLift.fixedSubgroup (matrixGroupTwist K σ)

abbrev FixedUpper (K : Type) [Field K] (σ : K ≃+* K) :=
  (AmbientPositive K).subgroupOf (MatrixFixed K σ)

theorem regular_unique_positive (K : Type) [Field K] [Finite K] (g : MatrixGroup K)
    (hg : g⁻¹ * regularMatrix K * g ∈ AmbientPositive K) :
    g ∈ Subgroup.normalizer (AmbientPositive K : Set (MatrixGroup K)) := by
  have hn := mem_normalizer_of_regular_conjugate (CartanMatrix.D 4)
    (CartanMatrix.D_diag 4) (CartanMatrix.D_transpose 4) D4_positive_definite
    (CartanMatrix.D_off_diag_nonpos 4) K g.val (regularMatrix K).val g.property
    (regularMatrix_positive K) (regularMatrix_leading K) hg
  apply Subgroup.mem_normalizer_iff.mpr
  intro x
  exact Subgroup.mem_normalizer_iff.mp hn x.val

def fixedPositiveSylow (K : Type) [Field K] [Finite K] (σ : K ≃+* K)
    (p : ℕ) [Fact p.Prime] [CharP K p] : Sylow p (MatrixFixed K σ) :=
  CFSGRegularElementSylowIntersection.intersectionSylow
    (ambientPositiveSylow K p) (MatrixFixed K σ) (regularMatrix K)
    (regularMatrix_positive K) (regularMatrix_fixed K σ) (regular_unique_positive K)

theorem fixedPositiveSylow_subgroup (K : Type) [Field K] [Finite K] (σ : K ≃+* K)
    (p : ℕ) [Fact p.Prime] [CharP K p] :
    (fixedPositiveSylow K σ p : Subgroup (MatrixFixed K σ)) = FixedUpper K σ := rfl

theorem fixed_upper_normalizer_soluble (K : Type) [Field K] [Finite K] (σ : K ≃+* K)
    (p : ℕ) [Fact p.Prime] [CharP K p] :
    IsSolvable (Subgroup.normalizer (FixedUpper K σ : Set (MatrixFixed K σ))) := by
  letI : IsSolvable (Subgroup.normalizer
      ((ambientPositiveSylow K p : Subgroup (MatrixGroup K)) : Set (MatrixGroup K))) := by
    rw [ambientPositiveSylow_subgroup]
    exact ambient_positive_normalizer_soluble K
  exact CFSGRegularElementSylowIntersection.normalizer_intersection_soluble
    (ambientPositiveSylow K p) (MatrixFixed K σ) (regularMatrix K)
    (regularMatrix_positive K) (regularMatrix_fixed K σ) (regular_unique_positive K)

end SymmetricSubgroupAsymptotics.CFSGTrialityGeckFixedPositiveSylow
