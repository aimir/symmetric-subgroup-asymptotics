import SymmetricSubgroupAsymptotics.CFSGReeFFourMiddleGradedKernel
import SymmetricSubgroupAsymptotics.CFSGNormTwoCoordinateLeadingHom

/-! One literal first-layer entry of the WHOLE original fixed outer
parameter. All three original E6 factors are retained. This does not
identify the characteristic quotient or discard higher correction terms. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
open scoped Classical
namespace SymmetricSubgroupAsymptotics.CFSGReeFFourOuterFirstLayerEntry
open CFSGReeFFourMiddleGradedKernel CFSGReeFFourOuterFixedRoot
open CFSGReeFFourFieldParameters CFSGReeFFourFixedPositiveFamilies
open CFSGFFourOriginalFoldedEquivalence CFSGFFourE6FixedGeneratedGroup
open CFSGFFourOriginalMiddleWords
open CFSGTwistedE6GeckDiagramCovariance CFSGE6GeckMiddleRootSupport
open CFSGExceptionalNormTwoBases CFSGExceptionalCartanPositiveDefinite
open CFSGNormTwoCoordinateLeadingHom CFSGNormTwoCoordinateLeadingFactor
open CFSGNormTwoGeckHeightSupport CFSGNormTwoGeckColumns
open CFSGGradedMatrixGroupFirstLayer CFSGGradedMatrixLieFirstLayer
open CFSGSerreQuadraticMatrix
local notation "A" => CartanMatrix.E₆
local notation "hd" => CartanMatrix.E₆_diag
local notation "hs" => CartanMatrix.E₆_transpose
local notation "hp" => E6_positive_definite
local notation "ho" => CartanMatrix.E₆_off_diag_nonpos

private theorem middle_entry (K : Type) [Field K]
    (u : (Matrix GeckIndex GeckIndex K)ˣ) :
    firstLayer middleWeight u (Sum.inl (E6Index 0))
      (Sum.inr (negativeIndex A hs hp (E6Index 0)))=
      leadingCoordinates A hd hs hp ho K u 0 := by
  have hwt : middleWeight (Sum.inl (E6Index 0))=
      middleWeight (Sum.inr (negativeIndex A hs hp (E6Index 0)))+1 := by
    change 0=outsideHeight (negativeIndex A hs hp (E6Index 0)).val+1
    rw [negative_val,map_neg]
    change (0 : ℤ)= -1+1
    rfl
  rw [firstLayer,firstPart_apply,if_pos hwt]
  change (u : Matrix GeckIndex GeckIndex K) _ _-
      (1 : Matrix GeckIndex GeckIndex K) _ _=_
  simp only [Matrix.one_apply,Sum.inl_ne_inr,if_false,sub_zero]
  rfl

private theorem outer_raw_value (m : ℕ) (a : Field m) :
    rawHom (Field m) (outerWord m a)=
      (canonicalRoot rawData (Field m) false 0 a*
        canonicalRoot rawData (Field m) false 5 a)*
        canonicalRoot rawData (Field m) false 1 (alpha m a) := by
  simp only [outerWord,map_mul,rawHom_root,folded_root_eq_orbitParameter]
  rfl

theorem outer_firstLayer_entry (m : ℕ) (a : Field m) :
    firstLayer middleWeight (rawHom (Field m) (outerWord m a))
      (Sum.inl (E6Index 0))
      (Sum.inr (negativeIndex A hs hp (E6Index 0)))=a := by
  let u := (positiveRoot A hd hs hp ho (Field m) 0 a*
    positiveRoot A hd hs hp ho (Field m) 5 a)*
    positiveRoot A hd hs hp ho (Field m) 1 (alpha m a)
  have hraw : u.val=
      rawHom (Field m) (outerWord m a) := (outer_raw_value m a).symm
  have hlead := congrArg (fun v : Multiplicative (Fin 6→Field m) => v.toAdd 0)
    (show leadingHom A hd hs hp ho (Field m) u=
      (Multiplicative.ofAdd (Pi.single 0 a : Fin 6→Field m)*
        Multiplicative.ofAdd (Pi.single 5 a : Fin 6→Field m))*
        Multiplicative.ofAdd (Pi.single 1 (alpha m a) : Fin 6→Field m) from by
      simp only [u,map_mul,leadingHom_positiveRoot])
  have he : leadingCoordinates A hd hs hp ho (Field m) u.val 0=a := by
    change leadingCoordinates A hd hs hp ho (Field m) u.val 0=
      (Pi.single 0 a : Fin 6→Field m) 0+
        (Pi.single 5 a : Fin 6→Field m) 0+
        (Pi.single 1 (alpha m a) : Fin 6→Field m) 0 at hlead
    simpa [Pi.single_apply] using hlead
  exact (middle_entry (Field m) _).trans
    (Eq.mp (congrArg (fun v => leadingCoordinates A hd hs hp ho (Field m) v 0=a) hraw) he)

theorem outer_firstLayer_ne_zero (m : ℕ) (a : Field m) (ha : a≠0) :
    firstLayer middleWeight (rawHom (Field m) (outerWord m a))≠0 := by
  intro he
  have hz := congrArg (fun M : Matrix GeckIndex GeckIndex (Field m) =>
    M (Sum.inl (E6Index 0))
      (Sum.inr (negativeIndex A hs hp (E6Index 0)))) he
  exact ha ((outer_firstLayer_entry m a).symm.trans hz)

end SymmetricSubgroupAsymptotics.CFSGReeFFourOuterFirstLayerEntry
