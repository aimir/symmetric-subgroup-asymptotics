import SymmetricSubgroupAsymptotics.CFSGNormTwoCoordinateDiagonalLeadingAction
import SymmetricSubgroupAsymptotics.CFSGNormTwoGeckBorelFactorization
import SymmetricSubgroupAsymptotics.CFSGNormTwoCoordinateRootLineNormalizers
import SymmetricSubgroupAsymptotics.CFSGE6GeckProductTorus

/-! The literal E6 product torus normalizes U, and scales every leading
coordinate by its already proved simple-root Cartan scalar. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
open scoped Classical
namespace SymmetricSubgroupAsymptotics.CFSGE6GeckProductTorusLeading
open CFSGTwistedE6GeckDiagramCovariance CFSGExceptionalNormTwoBases
open CFSGExceptionalCartanPositiveDefinite CFSGE6GeckProductTorus
open CFSGNormTwoGeckBorelFactorization CFSGNormTwoCoordinateRootLineNormalizers
open CFSGNormTwoCoordinateDiagonalLeadingAction CFSGDiagonalMatrixUnits
open CFSGNormTwoCoordinateLeadingFactor CFSGIntegerMatrixPowerHom
open CFSGIntegerMatrixPairing CFSGNormTwoRootPairing CFSGSerreQuadraticMatrix
open CFSGNormTwoGeckPositivePGroup
local notation "A" => CartanMatrix.E₆
local notation "hd" => CartanMatrix.E₆_diag
local notation "hs" => CartanMatrix.E₆_transpose
local notation "hp" => E6_positive_definite
local notation "ho" => CartanMatrix.E₆_off_diag_nonpos

theorem product_torus_normalizes_positive (K : Type) [Field K] (x : Fin 6→Kˣ) :
    rawProductTorus K x∈Subgroup.normalizer
      (rootGroup A hs hp E6Base E6Index K false : Set (Matrix GeckIndex GeckIndex K)ˣ) :=
  torusGroup_normalizes A hd hs hp ho K false (rawProductTorus_mem_torus K x)

theorem product_torus_leading_action (K : Type) [Field K] (x : Fin 6→Kˣ)
    (u : (Matrix GeckIndex GeckIndex K)ˣ) (i : Fin 6) :
    leadingCoordinates A hd hs hp ho K (rawProductTorus K x*u*(rawProductTorus K x)⁻¹) i=
      (powerHom (G := Kˣ) A x i : K)*leadingCoordinates A hd hs hp ho K u i := by
  obtain ⟨d,hdiag⟩ := torusGroup_le_diagonal A hs hp E6Base E6Index K
    (rawProductTorus_mem_torus K x)
  have hact := rawProductTorus_simple_action K x i 1
  simp only [one_mul] at hact
  rw [←hdiag] at hact ⊢
  exact diagonal_leading_of_simple_action A hd hs hp ho K d u i
    (powerHom (G := Kˣ) A x i : K) hact

end SymmetricSubgroupAsymptotics.CFSGE6GeckProductTorusLeading
