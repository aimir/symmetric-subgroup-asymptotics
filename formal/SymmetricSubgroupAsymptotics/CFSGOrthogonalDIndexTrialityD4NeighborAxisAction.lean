import SymmetricSubgroupAsymptotics.CFSGOrthogonalDIndexTrialityD4LocalDirectionIndex
import SymmetricSubgroupAsymptotics.CFSGOrthogonalDIndexTrialityD4HammingPullbackAxisAction

/-! The ACTUAL original root-plane stabilizer sends whole original
neighbour-axis fibres according to its constructed direction hom. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
namespace SymmetricSubgroupAsymptotics.CFSGOrthogonalDIndexTrialityD4ResidualSpace
open CFSGOrthogonalDSerreMatrices CFSGOrthogonalDIndexTrialityD2Coordinates
open CFSGOrthogonalDIndexTrialityD4HammingEdges
variable (K : Type) [Field K] [Finite K]

local instance trialityD4AxisActionRootPointsNontrivial : Nontrivial (RootPoints K) :=
  rootPoints_nontrivial K
local instance trialityD4AxisActionRulingNontrivial : Nontrivial (RulingParameters K) := by
  have hc := rulingParameter_card K
  letI : Finite (RulingParameters K) := Nat.finite_of_card_ne_zero (by rw [hc]; omega)
  apply Finite.one_lt_card_iff_nontrivial.mp
  rw [hc]
  have hp : 0 < Nat.card K := Nat.card_pos
  omega

def neighborCoordinate (N : Neighbors K) : OriginalResidueCoordinates K :=
  tripleEquiv (RootPoints K) (RulingParameters K) (RulingParameters K) (neighborFlagMap K N)

theorem neighborCoordinate_surjective : Function.Surjective (neighborCoordinate K) :=
  (tripleEquiv (RootPoints K) (RulingParameters K) (RulingParameters K)).surjective.comp
    (neighborFlagMap_surjective K)

variable (p : ℕ) [Fact p.Prime] [CharP K p]

theorem neighborCoordinate_equivariant (f : originalRootStabilizer K p) (N : Neighbors K) :
    rootStabilizerCoordinatesHom K p f (neighborCoordinate K N) =
      neighborCoordinate K (rootStabilizerNeighborHom K p f N) := by
  let e := (neighborTwinQuotientEquiv K).trans
    (tripleEquiv (RootPoints K) (RulingParameters K) (RulingParameters K))
  let x : NeighborTwinQuotient K := Quotient.mk (neighborTwinSetoid K) N
  change e (rootStabilizerTwinHom K p f (e.symm (e x))) =
    neighborCoordinate K (rootStabilizerNeighborHom K p f N)
  rw [e.symm_apply_apply]
  rfl

theorem rootStabilizer_image_neighbor_axis (f : originalRootStabilizer K p)
    (x : OriginalResidueCoordinates K) (i : Fin 3) :
    (rootStabilizerNeighborHom K p f) '' (neighborCoordinate K ⁻¹' CoordinateAxis i x) =
      neighborCoordinate K ⁻¹' CoordinateAxis (rootStabilizerDirectionHom K p f i)
        (rootStabilizerCoordinatesHom K p f x) := by
  exact image_pullback_coordinateAxis (rootStabilizerNeighborHom K p f)
    (rootStabilizerCoordinatesHom K p f) (neighborCoordinate K)
    (neighborCoordinate_equivariant K p f) (rootStabilizerHammingHom K p f).property
    (originalResidueBase K) x i

end SymmetricSubgroupAsymptotics.CFSGOrthogonalDIndexTrialityD4ResidualSpace
