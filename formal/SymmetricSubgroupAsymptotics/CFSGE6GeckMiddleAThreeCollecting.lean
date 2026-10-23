import SymmetricSubgroupAsymptotics.CFSGTwistedE6GeckDiagramCovariance
import SymmetricSubgroupAsymptotics.CFSGNormTwoGeckParameterizedCollecting
import SymmetricSubgroupAsymptotics.CFSGNormTwoGeckOrthogonalWeyl
import Mathlib.GroupTheory.Commutator.Basic
import Mathlib.Tactic.Group

/-! Literal rank-three A3 collection on nodes 2--3--4 of E6. Three
independent parameters are retained. The highest factor has coefficient
abc and the two middle factors have coefficients bc and ac, with no
characteristic-dependent division or source-faithfulness assumption. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
open scoped Classical commutatorElement
namespace SymmetricSubgroupAsymptotics.CFSGE6GeckMiddleAThreeCollecting
open CFSGTwistedE6GeckDiagramCovariance CFSGExceptionalNormTwoBases
open CFSGExceptionalCartanPositiveDefinite CFSGSerreQuadraticMatrix
open CFSGNormTwoGeckParameterizedCollecting CFSGNormTwoGeckOrthogonalWeyl
local notation "A" => CartanMatrix.E₆
local notation "hs" => CartanMatrix.E₆_transpose
local notation "hp" => E6_positive_definite

def firstMiddle (K : Type) [CommRing K] (t : K) : (Matrix GeckIndex GeckIndex K)ˣ :=
  canonicalWeyl rawData K 2*canonicalRoot rawData K false 3 t*(canonicalWeyl rawData K 2)⁻¹

def secondMiddle (K : Type) [CommRing K] (t : K) : (Matrix GeckIndex GeckIndex K)ˣ :=
  canonicalWeyl rawData K 4*canonicalRoot rawData K false 3 t*(canonicalWeyl rawData K 4)⁻¹

def highestMiddle (K : Type) [CommRing K] (t : K) : (Matrix GeckIndex GeckIndex K)ˣ :=
  (canonicalWeyl rawData K 2*canonicalWeyl rawData K 4)*canonicalRoot rawData K false 3 t*
    (canonicalWeyl rawData K 2*canonicalWeyl rawData K 4)⁻¹

private theorem collect_product {G : Type*} [Group G] (a b c : G) :
    ⁅a*b,c⁆=(a*⁅b,c⁆*a⁻¹)*⁅a,c⁆ := by
  simp only [commutatorElement_def]
  group

theorem middle_conjugation_factor (K : Type) [CommRing K] (a t : K) :
    canonicalRoot rawData K false 2 a*secondMiddle K t*(canonicalRoot rawData K false 2 a)⁻¹=
      highestMiddle K (a*t)*secondMiddle K t := by
  let X := canonicalRoot rawData K false 2 a
  let V := canonicalWeyl rawData K 4
  let W := canonicalWeyl rawData K 2
  have hv : Commute V X := orthogonal_weyl_root A hs hp E6Base E6Index K 4 2
    (by rw [E6_cartan];decide) false a
  have hw : Commute V W := orthogonal_weyls A hs hp E6Base E6Index K 4 2
    (by rw [E6_cartan];decide)
  have hc : X*canonicalRoot rawData K false 3 t*X⁻¹=
      W*canonicalRoot rawData K false 3 (a*t)*W⁻¹*canonicalRoot rawData K false 3 t := by
    simpa only [mul_comm t a] using adjacent_conjugation_factor A hs hp E6Base E6Index K 2 3
      (by rw [E6_cartan];decide) a t
  change X*(V*canonicalRoot rawData K false 3 t*V⁻¹)*X⁻¹=
    (W*V)*canonicalRoot rawData K false 3 (a*t)*(W*V)⁻¹*
      (V*canonicalRoot rawData K false 3 t*V⁻¹)
  calc
    _=(X*V)*canonicalRoot rawData K false 3 t*(X*V)⁻¹ := by group
    _=(V*X)*canonicalRoot rawData K false 3 t*(V*X)⁻¹ := by rw [hv.eq]
    _=V*(X*canonicalRoot rawData K false 3 t*X⁻¹)*V⁻¹ := by group
    _=V*(W*canonicalRoot rawData K false 3 (a*t)*W⁻¹*
        canonicalRoot rawData K false 3 t)*V⁻¹ := by rw [hc]
    _=(V*W)*canonicalRoot rawData K false 3 (a*t)*(V*W)⁻¹*
        (V*canonicalRoot rawData K false 3 t*V⁻¹) := by group
    _=_ := by rw [hw.eq]

theorem middle_commutator (K : Type) [CommRing K] (a b c : K) :
    ⁅canonicalRoot rawData K false 2 a*canonicalRoot rawData K false 4 b,
      canonicalRoot rawData K false 3 c⁆=
      highestMiddle K (a*b*c)*secondMiddle K (b*c)*firstMiddle K (a*c) := by
  have h23 : ⁅canonicalRoot rawData K false 2 a,canonicalRoot rawData K false 3 c⁆=
      firstMiddle K (a*c) := by
    simpa only [firstMiddle,mul_comm c a] using adjacent_word A hs hp E6Base E6Index K 2 3
      (by rw [E6_cartan];decide) a c
  have h43 : ⁅canonicalRoot rawData K false 4 b,canonicalRoot rawData K false 3 c⁆=
      secondMiddle K (b*c) := by
    simpa only [secondMiddle,mul_comm c b] using adjacent_word A hs hp E6Base E6Index K 4 3
      (by rw [E6_cartan];decide) b c
  rw [collect_product,h43,h23,middle_conjugation_factor]
  simp only [mul_assoc]

end SymmetricSubgroupAsymptotics.CFSGE6GeckMiddleAThreeCollecting
