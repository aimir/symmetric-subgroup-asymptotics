import SymmetricSubgroupAsymptotics.CFSGFFourOriginalFiftyTwoFamily
import SymmetricSubgroupAsymptotics.CFSGFFourIntegralRealization
import SymmetricSubgroupAsymptotics.CFSGFFourE6NormQuotientStepEntries
import SymmetricSubgroupAsymptotics.CFSGNormTwoGeckIntegralStepColumns

/-! One selected integral image pivot for the original 52-vector family.
The first nonsimple path is [E_3,E_2], whose actual E6 matrix has a
coefficient minus one. This certifies an image entry; it does not reflect
matrix equality into the original source or assert source spanning. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
open scoped Matrix
namespace SymmetricSubgroupAsymptotics.CFSGFFourOriginalFirstMatrixPivot
open CFSG.Models.Chevalley CFSGSerreQuadraticMatrix
open CFSGFFourSerreMatrices CFSGFFourOriginalFiftyTwoFamily
open CFSGTwistedE6GeckDiagramCovariance CFSGFFourE6NormQuotientStepEntries
open CFSGNormTwoGeckIntegralStepColumns CFSGNormTwoRootPairing CFSGIntegerMatrixPairing
open CFSGExceptionalNormTwoBases CFSGExceptionalCartanPositiveDefinite
open CFSGNormTwoCoordinateDiagramIndices
local instance : DecidableEq (Roots CartanMatrix.E₆):=Classical.decEq _

def firstRoot : Roots CartanMatrix.E₆ :=
  ⟨![0,1,0,1,0,0],by decide +kernel⟩

def firstMatrix : IntMat := e6EZ 1*e6EZ 3-e6EZ 3*e6EZ 1

theorem integralRepresentation_first :
    integralRepresentation realizationData (rootVectors false 4)=firstMatrix := by
  change integralRepresentation realizationData
    (integralOperator CartanMatrix.F₄ false 3 1
      (CFSGSerreDiagram.latticeGenerator CartanMatrix.F₄ (.E 2)))=firstMatrix
  rw [integralRepresentation_operator,integralRepresentation_generator]
  rw [CFSGIntegralQuadraticRootOperators.operator_one]
  rfl

private theorem cartan_one_column (i:Fin 6) :
    e6EZ i*ᵥPi.single (Sum.inl (E6Index 1)) 1=
      |CartanMatrix.E₆ i 1| • Pi.single (Sum.inr (E6Index i:Roots CartanMatrix.E₆)) 1 := by
  have h:=E_cartan_column CartanMatrix.E₆ CartanMatrix.E₆_transpose E6_positive_definite
    E6Base (E6Index i) (E6Index 1)
  have hc:E6Base.cartanMatrix (E6Index i) (E6Index 1)=CartanMatrix.E₆ i 1 :=
    coordinate_cartan CartanMatrix.E₆ CartanMatrix.E₆_diag CartanMatrix.E₆_transpose
      E6_positive_definite CartanMatrix.E₆_off_diag_nonpos i 1
  rw [hc] at h
  exact h

private theorem root_column (i j:Fin 6)
    (hn:(E6Index j:Roots CartanMatrix.E₆).val≠ -(E6Index i:Roots CartanMatrix.E₆).val)
    (hsum:integerPairing CartanMatrix.E₆
      ((E6Index i:Roots CartanMatrix.E₆).val+(E6Index j:Roots CartanMatrix.E₆).val)
      ((E6Index i:Roots CartanMatrix.E₆).val+(E6Index j:Roots CartanMatrix.E₆).val)=2)
    (hr:(⟨(E6Index i:Roots CartanMatrix.E₆).val+(E6Index j:Roots CartanMatrix.E₆).val,hsum⟩:
      Roots CartanMatrix.E₆)=firstRoot) :
    e6EZ i*ᵥPi.single (Sum.inr (E6Index j:Roots CartanMatrix.E₆)) 1=
      Pi.single (Sum.inr firstRoot) 1 := by
  have h:=E_root_column CartanMatrix.E₆ CartanMatrix.E₆_transpose E6_positive_definite
    E6Base (E6Index i) (E6Index j:Roots CartanMatrix.E₆)
  simpa only [if_neg hn,dif_pos hsum,hr,zero_add] using h

private theorem one_three_column :
    e6EZ 1*ᵥPi.single (Sum.inr (E6Index 3:Roots CartanMatrix.E₆)) 1=
      Pi.single (Sum.inr firstRoot) 1 := by
  have hn:(E6Index 3:Roots CartanMatrix.E₆).val≠ -(E6Index 1:Roots CartanMatrix.E₆).val := by
    intro h
    have hh:=congrFun h (1:Fin 6)
    change (0:ℤ)= -1 at hh
    norm_num at hh
  have hs:(E6Index 1:Roots CartanMatrix.E₆).val+(E6Index 3:Roots CartanMatrix.E₆).val=
      firstRoot.val := by
    funext i
    fin_cases i <;> rfl
  have hsum:integerPairing CartanMatrix.E₆
      ((E6Index 1:Roots CartanMatrix.E₆).val+(E6Index 3:Roots CartanMatrix.E₆).val)
      ((E6Index 1:Roots CartanMatrix.E₆).val+(E6Index 3:Roots CartanMatrix.E₆).val)=2 := by
    rw [hs]
    exact firstRoot.property
  exact root_column 1 3 hn hsum (Subtype.ext hs)

private theorem three_one_column :
    e6EZ 3*ᵥPi.single (Sum.inr (E6Index 1:Roots CartanMatrix.E₆)) 1=
      Pi.single (Sum.inr firstRoot) 1 := by
  have hn:(E6Index 1:Roots CartanMatrix.E₆).val≠ -(E6Index 3:Roots CartanMatrix.E₆).val := by
    intro h
    have hh:=congrFun h (3:Fin 6)
    change (0:ℤ)= -1 at hh
    norm_num at hh
  have hs:(E6Index 3:Roots CartanMatrix.E₆).val+(E6Index 1:Roots CartanMatrix.E₆).val=
      firstRoot.val := by
    funext i
    fin_cases i <;> rfl
  have hsum:integerPairing CartanMatrix.E₆
      ((E6Index 3:Roots CartanMatrix.E₆).val+(E6Index 1:Roots CartanMatrix.E₆).val)
      ((E6Index 3:Roots CartanMatrix.E₆).val+(E6Index 1:Roots CartanMatrix.E₆).val)=2 := by
    rw [hs]
    exact firstRoot.property
  exact root_column 3 1 hn hsum (Subtype.ext hs)

theorem first_column :
    firstMatrix*ᵥPi.single (Sum.inl (E6Index 1)) 1=
      -(Pi.single (Sum.inr firstRoot) (1:ℤ):Index→ℤ) := by
  rw [firstMatrix,Matrix.sub_mulVec,←Matrix.mulVec_mulVec,←Matrix.mulVec_mulVec,
    cartan_one_column,cartan_one_column,Matrix.mulVec_smul,Matrix.mulVec_smul,
    one_three_column,three_one_column]
  change (1:ℤ) • (Pi.single (Sum.inr firstRoot) (1:ℤ):Index→ℤ)-
    (2:ℤ) • (Pi.single (Sum.inr firstRoot) (1:ℤ):Index→ℤ)=_
  module

theorem first_pivot : firstMatrix (Sum.inr firstRoot) (Sum.inl (E6Index 1))= -1 := by
  have h:=first_column
  rw [Matrix.mulVec_single_one] at h
  have he:=congrFun h (Sum.inr firstRoot)
  change firstMatrix (Sum.inr firstRoot) (Sum.inl (E6Index 1))=
    -((Pi.single (Sum.inr firstRoot) (1:ℤ):Index→ℤ) (Sum.inr firstRoot)) at he
  simpa only [Pi.single_eq_same] using he

end SymmetricSubgroupAsymptotics.CFSGFFourOriginalFirstMatrixPivot
