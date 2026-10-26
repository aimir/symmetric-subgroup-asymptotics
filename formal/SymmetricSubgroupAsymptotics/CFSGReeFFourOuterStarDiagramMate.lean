import SymmetricSubgroupAsymptotics.CFSGReeFFourOuterStarOriginalMiddle
import SymmetricSubgroupAsymptotics.CFSGFFourOriginalGeneratedEquivalence
import SymmetricSubgroupAsymptotics.CFSGTwistedE6GeckRelativeRootGenerated

/-! The literal diagram mate of the selected node-0 y/r conjugation
identity. The ACTUAL folded F4 image is identity-field diagram-fixed;
no automorphism of the derived group is lifted to the ambient group. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
open scoped Classical Matrix
namespace SymmetricSubgroupAsymptotics.CFSGReeFFourOuterStarDiagramMate
open CFSGReeFFourOuterStarOriginalMiddle CFSGReeFFourOuterStarConjugation
open CFSGReeFFourOuterStarColumns CFSGReeFFourMiddleSquareSelectedWordTransport
open CFSGReeFFourFieldParameters CFSGReeFFourFixedModelEquivalence
open CFSGReeFFourFixedPositiveFamilies CFSGReeFFourMiddleDerivedFiveWord
open CFSGTwistedE6GeckDiagramCovariance CFSGTwistedE6GeckMatrixTwist
open CFSGTwistedE6GeckRelativeRootGenerated CFSGTwistedE6GeckSourceAction
open CFSGFFourOriginalGeneratedEquivalence CFSGFFourOriginalMiddleWords
open CFSGExceptionalNormTwoBases CFSGExceptionalCartanPositiveDefinite
open CFSGNormTwoRootPairing CFSGNormTwoCoordinateSelectedRootElement
open CFSGSerreQuadraticMatrix
local notation "A" => CartanMatrix.E₆
local notation "hd" => CartanMatrix.E₆_diag
local notation "hs" => CartanMatrix.E₆_transpose
local notation "hp" => E6_positive_definite
local notation "ho" => CartanMatrix.E₆_off_diag_nonpos
private abbrev Mat (K : Type) := Matrix GeckIndex GeckIndex K

private theorem first_star_root : (leftStar.root 0).val=(E6Index 0 : Roots A) := by
  apply Subtype.ext
  funext j
  change leftStar.row 0 j=(Pi.single (0 : Fin 6) (1 : ℤ) : Fin 6→ℤ) j
  fin_cases j <;> rfl

private theorem parameter_zero (m : ℕ) :
    starHom (Field m) (Multiplicative.ofAdd (Pi.single 0 1))=
      canonicalRoot rawData (Field m) false 0 1 :=
  (starHom_single (Field m) 0 1).trans
    ((congrArg (fun k : Roots A=>selectedRootElement A hd hs hp ho (Field m) k 1)
      first_star_root).trans (simple_one (Field m) 0).symm)

theorem fixedRawHom_diagram_fixed (m : ℕ) (g : originalModelFixed m) :
    unitTwist (Field m) (RingEquiv.refl (Field m)) (fixedRawHom m g)=fixedRawHom m g := by
  have hg : rawHom (Field m) g.val∈
      fixedRootGenerated (Field m) (RingEquiv.refl (Field m)) :=
    (modelEquivGenerated (Field m) g.val).property
  exact fixedRootGenerated_le_fixed (Field m) (RingEquiv.refl (Field m)) hg

theorem node_zero_relation (m : ℕ) :
    fixedRawHom m (fourCycle m)*canonicalRoot rawData (Field m) false 0 1*
      (fixedRawHom m (fourCycle m))⁻¹=
    fixedRawHom m (fiveWord m)*canonicalRoot rawData (Field m) false 0 1*
      (fixedRawHom m (fiveWord m))⁻¹ := by
  have hparam := parameter_zero m
  calc
    _=fixedRawHom m (fourCycle m)*
        starHom (Field m) (Multiplicative.ofAdd (Pi.single 0 1))*
        (fixedRawHom m (fourCycle m))⁻¹ :=
      congrArg (fun u : (Mat (Field m))ˣ=>
        fixedRawHom m (fourCycle m)*u*(fixedRawHom m (fourCycle m))⁻¹) hparam.symm
    _=fixedRawHom m (fiveWord m)*
        starHom (Field m) (Multiplicative.ofAdd (Pi.single 0 1))*
        (fixedRawHom m (fiveWord m))⁻¹ := selected_original_parameter_relation m 1
    _=_ := congrArg (fun u : (Mat (Field m))ˣ=>
      fixedRawHom m (fiveWord m)*u*(fixedRawHom m (fiveWord m))⁻¹) hparam

private theorem fixed_conjugation_transport {G : Type*} [Group G]
    (tau : G→*G) (g r a b : G) (hg : tau g=g) (hr : tau r=r)
    (hab : tau a=b) (h : g*a*g⁻¹=r*a*r⁻¹) : g*b*g⁻¹=r*b*r⁻¹ := by
  have hh := congrArg tau h
  simpa only [map_mul,map_inv,hg,hr,hab] using hh

theorem node_five_relation (m : ℕ) :
    fixedRawHom m (fourCycle m)*canonicalRoot rawData (Field m) false 5 1*
      (fixedRawHom m (fourCycle m))⁻¹=
    fixedRawHom m (fiveWord m)*canonicalRoot rawData (Field m) false 5 1*
      (fixedRawHom m (fiveWord m))⁻¹ :=
  fixed_conjugation_transport
    (unitTwist (Field m) (RingEquiv.refl (Field m))).toMonoidHom
    _ _ (canonicalRoot rawData (Field m) false 0 1)
    (canonicalRoot rawData (Field m) false 5 1)
    (fixedRawHom_diagram_fixed m (fourCycle m))
    (fixedRawHom_diagram_fixed m (fiveWord m))
    (unitTwist_root (Field m) (RingEquiv.refl (Field m)) false 0 1)
    (node_zero_relation m)

end SymmetricSubgroupAsymptotics.CFSGReeFFourOuterStarDiagramMate
