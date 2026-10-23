import SymmetricSubgroupAsymptotics.CFSGGTwoD4GeckIntegralCoefficients
import SymmetricSubgroupAsymptotics.CFSGNormTwoCoordinateOrthogonalTripleAdjoint
import SymmetricSubgroupAsymptotics.CFSGNormTwoCoordinateSingleRootAdjoint
import SymmetricSubgroupAsymptotics.CFSGNormTwoGeckGeneratedLieInvariance

/-! The actual folded short generator has adjoint fourth power zero on
the SAME original G2 rational image inside the D4 Geck Lie algebra.
The cubic coefficient is retained; no ambient matrix-cube assertion or
field reduction of a rational vector space is used. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
open scoped Classical BigOperators
namespace SymmetricSubgroupAsymptotics.CFSGGTwoD4GeckImageAdjoint
open CFSGGTwoD4GeckGenerators CFSGGTwoD4GeckSerreRepresentation
open CFSGGTwoD4GeckIntegralCoefficients CFSGTrialityD4NormTwo
open CFSGTrialityGeckDiagramCovariance CFSGTrialityFixedWeylWords
open CFSGNormTwoGeckTripleRootPolynomial CFSGNormTwoGeckGeneratedLieInvariance
open CFSGNormTwoRootPairing CFSGIntegerMatrixPairing CFSGGradedMatrixSupport
open CFSG.Models.Chevalley
open CFSGSerreQuadraticMatrix (fieldRoot)
local notation "A" => CartanMatrix.D 4
local notation "hs" => CartanMatrix.D_transpose 4
local notation "hp" => D4_positive_definite

private theorem raw_rational_root (neg : Bool) (i : Fin 4) :
    fieldRoot rawData ℚ neg i=if neg then d4F i else d4E i := by
  cases neg
  · exact CFSGGeckIntegralMatrices.map_E Base (Index i)
  · exact CFSGGeckIntegralMatrices.map_F Base (Index i)

theorem folded_root_ad_four (neg : Bool) (i : Fin 2) (x : RationalLie CartanMatrix.G₂) :
    (LieAlgebra.ad ℚ Mat (if neg then negative i else positive i)^4) (rationalRepresentation x)=0 := by
  have hx := rational_image_mem_geck x
  fin_cases i
  · let X : Fin 3→Mat := fun j=>if neg then d4F (outerNode j) else d4E (outerNode j)
    let a : Fin 3→Roots A := fun j=>signedSimpleRoot A hs hp Base Index neg (outerNode j)
    have hraw (j : Fin 3) : X j=fieldRoot rawData ℚ neg (outerNode j) :=
      (raw_rational_root neg (outerNode j)).symm
    have ha (j k : Fin 3) (hjk : j≠k) : integerPairing A (a j).val (a k).val=0 :=
      signed_orthogonal A hs hp Base Index neg _ _ (outer_orthogonal j k hjk)
    have hX (j : Fin 3) : X j∈RootPairing.GeckConstruction.lieAlgebra Base := by
      rw [hraw]
      exact root_mem_generated A hs hp Base Index neg (outerNode j)
    have hXa (j : Fin 3) : Supported (CFSGNormTwoGeckLatticeDegree.latticeWeight A hs hp Base)
        (fun v=>v+(a j).val) (X j) := by
      rw [hraw]
      exact root_signed_degree A hs hp Base Index ℚ neg (outerNode j)
    have hsum : (∑j,X j)=if neg then negative 0 else positive 0 := by
      cases neg <;> simp [X,negative,positive,Fin.sum_univ_succ,outerNode,add_assoc]
    have hz := CFSGNormTwoCoordinateOrthogonalTripleAdjoint.orthogonal_three_ad_four
      A (CartanMatrix.D_diag 4) hs hp (CartanMatrix.D_off_diag_nonpos 4) a
      (ha 0 1 (by decide)) (ha 0 2 (by decide)) (ha 1 2 (by decide))
      X hX hXa (rationalRepresentation x) hx
    change (LieAlgebra.ad ℚ Mat (if neg then negative 0 else positive 0)^4)
      (rationalRepresentation x)=0
    calc
      _=(LieAlgebra.ad ℚ Mat (∑j,X j)^4) (rationalRepresentation x) :=
        congrArg (fun Z : Mat=>(LieAlgebra.ad ℚ Mat Z^4) (rationalRepresentation x)) hsum.symm
      _=0 := hz
  · have hroot : (if neg then negative (1:Fin 2) else positive (1:Fin 2))=
        fieldRoot rawData ℚ neg 1 := by
      rw [raw_rational_root]
      cases neg <;> rfl
    change (LieAlgebra.ad ℚ Mat (if neg then negative 1 else positive 1)^4)
      (rationalRepresentation x)=0
    rw [hroot]
    have hc := CFSGNormTwoCoordinateSingleRootAdjoint.single_root_ad_cube
      A (CartanMatrix.D_diag 4) hs hp (CartanMatrix.D_off_diag_nonpos 4)
      (signedSimpleRoot A hs hp Base Index neg 1) (fieldRoot rawData ℚ neg 1)
      (root_mem_generated A hs hp Base Index neg 1)
      (root_signed_degree A hs hp Base Index ℚ neg 1) (rationalRepresentation x) hx
    change ⁅fieldRoot rawData ℚ neg 1,⁅fieldRoot rawData ℚ neg 1,
      ⁅fieldRoot rawData ℚ neg 1,⁅fieldRoot rawData ℚ neg 1,rationalRepresentation x⁆⁆⁆⁆=0
    exact (congrArg (fun y : Mat=>⁅fieldRoot rawData ℚ neg 1,y⁆) hc).trans (lie_zero _)

end SymmetricSubgroupAsymptotics.CFSGGTwoD4GeckImageAdjoint
