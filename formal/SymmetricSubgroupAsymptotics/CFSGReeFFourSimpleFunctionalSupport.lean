import SymmetricSubgroupAsymptotics.CFSGNormTwoCoordinateFunctionalInversion
import SymmetricSubgroupAsymptotics.CFSGReeFFourOuterParabolicFlag
import SymmetricSubgroupAsymptotics.CFSGReeFFourPairedDescentPrefixes

/-! The two actual relative supports satisfy the structural functional-
inversion criterion. Only their three simple columns are evaluated;
all positive roots follow from the integer support cone, without a census. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
open scoped Classical Matrix
namespace SymmetricSubgroupAsymptotics.CFSGReeFFourSimpleFunctionalSupport
open CFSGReeFFourOuterParabolicFlag CFSGE6GeckMiddleRootSupport
open CFSGReeFFourPairedDescentPrefixes CFSGNormTwoCoordinateFunctionalInversion
open CFSGNormTwoRootPairing CFSGNormTwoCoordinatePositiveRootGenerators
open CFSGNormTwoGeckWeylWordDegree CFSGNormTwoGeckLatticeDegree CFSGNormTwoGeckHeightSupport
open CFSGNormTwoGeckPositivePGroup CFSGTwistedE6GeckPositiveTwist
open CFSGTwistedE6GeckDiagramCovariance CFSGExceptionalNormTwoBases
open CFSGExceptionalCartanPositiveDefinite CFSGSignedCartanReflections
open CFSGGradedMatrixTriangularUnits
local notation "A" => CartanMatrix.E₆
local notation "hd" => CartanMatrix.E₆_diag
local notation "hs" => CartanMatrix.E₆_transpose
local notation "hp" => E6_positive_definite
local notation "ho" => CartanMatrix.E₆_off_diag_nonpos
local instance : DecidableEq (Roots A) := Classical.decEq _

def simpleFunctional (middle : Bool) : (Fin 6→ℤ)→ₗ[ℤ]ℤ :=
  if middle then outsideHeight else insideHeight

theorem simpleFunctional_simple (middle : Bool) (i : Fin 6) :
    simpleFunctional middle (E6Index i : Roots A).val=
      if i∈pairedSupport middle then 0 else 1 := by
  cases middle <;> fin_cases i <;> rfl

theorem simpleFunctional_nonnegative (middle : Bool) (k : PositiveRoot A) :
    0≤simpleFunctional middle k.val.val := by
  cases middle
  · change 0≤k.val.val 2+k.val.val 3+k.val.val 4
    exact add_nonneg (add_nonneg (k.property 2) (k.property 3)) (k.property 4)
  · change 0≤k.val.val 0+k.val.val 1+k.val.val 5
    exact add_nonneg (add_nonneg (k.property 0) (k.property 1)) (k.property 5)

theorem zero_root_support (middle : Bool) (k : PositiveRoot A)
    (hk : simpleFunctional middle k.val.val=0) :
    ∀i,k.val.val i≠0→i∈pairedSupport middle := by
  cases middle
  · change k.val.val 2+k.val.val 3+k.val.val 4=0 at hk
    have h2 : k.val.val 2=0 := by have := k.property 2;have := k.property 3;have := k.property 4;omega
    have h3 : k.val.val 3=0 := by have := k.property 2;have := k.property 3;have := k.property 4;omega
    have h4 : k.val.val 4=0 := by have := k.property 2;have := k.property 3;have := k.property 4;omega
    intro i hi
    fin_cases i
    · decide
    · decide
    · exact False.elim (hi h2)
    · exact False.elim (hi h3)
    · exact False.elim (hi h4)
    · decide
  · change k.val.val 0+k.val.val 1+k.val.val 5=0 at hk
    have h0 : k.val.val 0=0 := by have := k.property 0;have := k.property 1;have := k.property 5;omega
    have h1 : k.val.val 1=0 := by have := k.property 0;have := k.property 1;have := k.property 5;omega
    have h5 : k.val.val 5=0 := by have := k.property 0;have := k.property 1;have := k.property 5;omega
    intro i hi
    fin_cases i
    · exact False.elim (hi h0)
    · exact False.elim (hi h1)
    · decide
    · decide
    · decide
    · exact False.elim (hi h5)

theorem simple_columns_nonpositive : ∀middle i,i∈pairedSupport middle→∀j,
    (latticeWord A (pairedWord middle)*ᵥ(Pi.single i (1:ℤ) : Fin 6→ℤ)) j≤0 := by
  decide

theorem simpleFunctional_zero_word : ∀middle i,i∈pairedWord middle→
    simpleFunctional middle (Pi.single i (1:ℤ) : Fin 6→ℤ)=0 := by
  decide

theorem positive_inf_simple_flag_le_inversion (K : Type) [_root_.Field K] (middle : Bool) :
    Positive K⊓triangularUnits (weight A hs hp E6Base (simpleFunctional middle))≤
      Positive K⊓(Negative K).comap
        (MulAut.conj (wordUnit A hs hp E6Base E6Index K (pairedWord middle))).toMonoidHom := by
  have hweight : (fun j=>simpleFunctional middle (latticeWeight A hs hp E6Base j))=
      weight A hs hp E6Base (simpleFunctional middle) := by
    funext j
    cases j <;> simp only [latticeWeight,weight,map_zero]
  rw [←hweight]
  exact positive_inf_flag_le_inversion A hd hs hp ho (simpleFunctional middle)
    {i | i∈pairedSupport middle} (pairedWord middle) (zero_root_support middle)
      (simple_columns_nonpositive middle) K (simpleFunctional_nonnegative middle)

end SymmetricSubgroupAsymptotics.CFSGReeFFourSimpleFunctionalSupport
