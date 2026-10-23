import SymmetricSubgroupAsymptotics.CFSGTrialityGeckMiddleFirstLayer
import SymmetricSubgroupAsymptotics.CFSGFiniteCoproductAdditiveCoordinates

/-! Independent actual cube-root coordinates in the genuine quotient R/Z.
The first-layer map reads their coefficients in eight distinct original
lattice-root degrees, so the product chart is injective in every field.
Surjectivity is a separate cardinality step. -/
set_option autoImplicit false
set_option Elab.async false
set_option backward.isDefEq.respectTransparency false
noncomputable section
open scoped Classical
namespace SymmetricSubgroupAsymptotics.CFSGTrialityGeckMiddleCubeCoordinates
open CFSGNormTwoRootPairing CFSGTrialityD4NormTwo CFSGTrialityD4MiddleCube
open CFSGTrialityGeckMiddleRadicalQuotient CFSGTrialityGeckMiddleFirstLayer
open CFSGNormTwoCoordinateRootBracketTransport CFSGNormTwoCoordinateRootCoefficientCoordinates
local notation "A" => CartanMatrix.D 4
local notation "hd" => CartanMatrix.D_diag 4
local notation "hs" => CartanMatrix.D_transpose 4
local notation "hp" => D4_positive_definite
local notation "ho" => CartanMatrix.D_off_diag_nonpos 4
local instance : DecidableEq (Roots A) := Classical.decEq _

abbrev cubeCoefficient (K : Type) [Field K] (a : Cube) : Mat K :=
  selectedFieldCoefficient A hd hs hp ho K (cubeRoot a)

theorem cube_coefficients_unique (K : Type) [Field K] (c d : Cube → K)
    (h : (∑ a, c a • cubeCoefficient K a) = ∑ a, d a • cubeCoefficient K a) : c = d :=
  root_family_coefficients_unique A hd hs hp ho K cubeRoot cubeRoot_injective c d h

def cubeParameter (K : Type) [Field K] (a : Cube) :
    Multiplicative K →* MiddleQuotient K :=
  quotientParameter K (cubeRoot a) (cubeRoot_positive a) (by rw [cubeRoot_middle])

def cubeProductHom (K : Type) [Field K] :
    (Cube → Multiplicative K) →* MiddleQuotient K :=
  MonoidHom.noncommPiCoprod (cubeParameter K) (by
    intro u v huv a b
    exact quotient_parameters_commute K (cubeRoot u) (cubeRoot v)
      (cubeRoot_positive u) (cubeRoot_positive v)
      (by rw [cubeRoot_middle]) (by rw [cubeRoot_middle]) a b)

theorem cubeProduct_firstLayer (K : Type) [Field K] (c : Cube → Multiplicative K) :
    (quotientFirstLayerHom K (cubeProductHom K c)).toAdd =
      ∑ a, (c a).toAdd • cubeCoefficient K a := by
  apply CFSGFiniteCoproductAdditiveCoordinates.coproduct_coordinates
    (quotientFirstLayerHom K) (cubeParameter K) _ (cubeCoefficient K) _ c
  intro a t
  change CFSGGradedMatrixGroupFirstLayer.firstLayer middleWeight
    (CFSGNormTwoCoordinateSelectedRootElement.selectedRootElement A hd hs hp ho K
      (cubeRoot a) t.toAdd) = t.toAdd • cubeCoefficient K a
  exact root_firstLayer K (cubeRoot a) (cubeRoot_middle a) t.toAdd

theorem cubeProduct_injective (K : Type) [Field K] :
    Function.Injective (cubeProductHom K) := by
  intro c d hcd
  have h := congrArg (fun x : MiddleQuotient K => (quotientFirstLayerHom K x).toAdd) hcd
  dsimp only at h
  rw [cubeProduct_firstLayer, cubeProduct_firstLayer] at h
  have hcoeff := cube_coefficients_unique K (fun a => (c a).toAdd) (fun a => (d a).toAdd) h
  funext a
  exact congrArg Multiplicative.ofAdd (congrFun hcoeff a)

end SymmetricSubgroupAsymptotics.CFSGTrialityGeckMiddleCubeCoordinates
