import SymmetricSubgroupAsymptotics.CFSGNormTwoCoordinateRootCoefficientCoordinates
import SymmetricSubgroupAsymptotics.CFSGNormTwoCoordinateSelectedRootElement
import SymmetricSubgroupAsymptotics.CFSGGradedMatrixHighLayerProducts
import SymmetricSubgroupAsymptotics.CFSGGradedQuadraticUnit
import SymmetricSubgroupAsymptotics.CFSGNormTwoCoordinateHeight

/-! Actual first nonzero height coefficient of EVERY selected positive
root word, in every field. The two original integral root coefficients
are kept in lattice degrees beta and 2beta before applying integer height.
No logarithm, field-valued weight character, or image injectivity premise. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
namespace SymmetricSubgroupAsymptotics.CFSGNormTwoCoordinateRootHeightLeading
open CFSGIntegerMatrixPairing CFSGNormTwoRootPairing CFSGIntegerHeightSign
open CFSGNormTwoGeckLatticeDegree CFSGNormTwoGeckNegativeWordCoefficients
open CFSGNormTwoGeckIntegralWord CFSGNormTwoCoordinateRootSubgroup
open CFSGNormTwoCoordinateRootBracketTransport CFSGNormTwoCoordinateRootCoefficientCoordinates
open CFSGNormTwoCoordinateSelectedRootElement CFSGNormTwoCoordinateHeight
open CFSGSerreQuadraticWordRootTransport CFSGGradedMatrixSupport
open CFSGGradedMatrixSingleDegreeSpan CFSGGradedMatrixHighLayerProducts
variable {r : ℕ} (A : Matrix (Fin r) (Fin r) ℤ) (hd : ∀i,A i i=2)
    (hs : A.transpose=A) (hp : (rationalMatrix A).PosDef)
    (ho : ∀i j,i≠j→A i j≤0)
    [Fintype (Roots A)] [DecidableEq (Roots A)]
    [(rootPairing A hs hp).IsReduced] [(rootPairing A hs hp).IsIrreducible]

local notation "b₀" => coordinateBase A hd hs hp ho
local notation "s₀" => coordinateIndexEquiv A hd hs hp ho
local notation "ell" => latticeWeight A hs hp b₀
private abbrev CoordMat (K : Type) := Matrix ((b₀).support⊕Roots A) ((b₀).support⊕Roots A) K

def heightWeight : (b₀).support⊕Roots A→ℤ := fun j=>height (ell j)

def selectedSecondCoefficient (K : Type) [Field K] (k : Roots A) : CoordMat A hd hs hp ho K :=
  secondCoefficient A hs hp b₀ s₀ K (rootWitness A hd hs hp ho k).val.1
    (rootWitness A hd hs hp ho k).val.2

theorem selectedSecondCoefficient_support (K : Type) [Field K] (k : Roots A) :
    Supported ell (fun v=>v+(k.val+k.val)) (selectedSecondCoefficient A hd hs hp ho K k) := by
  let p := rootWitness A hd hs hp ho k
  apply supported_congr (second_support A hs hp b₀ s₀ K p.val.1 p.val.2)
  intro v
  exact congrArg (fun d : Fin r→ℤ=>v+(d+d)) p.property.symm

theorem selectedRootElement_expansion (K : Type) [Field K] (k : Roots A) (a : K) :
    (selectedRootElement A hd hs hp ho K k a : CoordMat A hd hs hp ho K)=
      1+a • selectedFieldCoefficient A hd hs hp ho K k+
        a^2 • selectedSecondCoefficient A hd hs hp ho K k := by
  rw [selectedFieldCoefficient_eq_first]
  simpa only [selectedRootElement,rootWord,selectedSecondCoefficient,word_eq_canonicalWord] using
    word_expansion A hs hp b₀ s₀ K (rootWitness A hd hs hp ho k).val.1
      (rootWitness A hd hs hp ho k).val.2 a

theorem first_height_support (K : Type) [Field K] (k : Roots A) :
    Supported (heightWeight A hd hs hp ho) (fun w=>w+height k.val)
      (selectedFieldCoefficient A hd hs hp ho K k) :=
  CFSGGradedQuadraticUnit.support_apply_height ell k.val coordinateHeight.toAddMonoidHom _
    (selectedFieldCoefficient_support A hd hs hp ho K k)

theorem second_height_support (K : Type) [Field K] (k : Roots A) :
    Supported (heightWeight A hd hs hp ho) (fun w=>w+(height k.val+height k.val))
      (selectedSecondCoefficient A hd hs hp ho K k) := by
  have hh := CFSGGradedQuadraticUnit.support_apply_height ell (k.val+k.val)
    coordinateHeight.toAddMonoidHom _ (selectedSecondCoefficient_support A hd hs hp ho K k)
  change Supported (heightWeight A hd hs hp ho) (fun w=>w+height (k.val+k.val))
    (selectedSecondCoefficient A hd hs hp ho K k) at hh
  simpa only [height_add] using hh

theorem selected_root_cut_and_leading (K : Type) [Field K] (k : Roots A)
    (hh : 0<height k.val) (a : K) :
    BelowCut (heightWeight A hd hs hp ho) (height k.val)
      ((selectedRootElement A hd hs hp ho K k a : CoordMat A hd hs hp ho K)-1) ∧
      degreePart (heightWeight A hd hs hp ho) (height k.val)
        ((selectedRootElement A hd hs hp ho K k a : CoordMat A hd hs hp ho K)-1)=
        a • selectedFieldCoefficient A hd hs hp ho K k := by
  have hdev : (selectedRootElement A hd hs hp ho K k a : CoordMat A hd hs hp ho K)-1=
      a • selectedFieldCoefficient A hd hs hp ho K k+
        a^2 • selectedSecondCoefficient A hd hs hp ho K k := by
    rw [selectedRootElement_expansion]
    abel
  have hfirst := first_height_support A hd hs hp ho K k
  have hsecond := second_height_support A hd hs hp ho K k
  simp only [hdev]
  constructor
  · apply belowCut_add
    · intro i j hij
      have hne : heightWeight A hd hs hp ho i≠
          heightWeight A hd hs hp ho j+height k.val := by omega
      rw [Matrix.smul_apply,hfirst i j hne,smul_zero]
    · intro i j hij
      have hne : heightWeight A hd hs hp ho i≠
          heightWeight A hd hs hp ho j+(height k.val+height k.val) := by omega
      rw [Matrix.smul_apply,hsecond i j hne,smul_zero]
  · rw [map_add,map_smul,map_smul,
      degreePart_eq _ _ _ hfirst,
      degreePart_zero_of_other _ (height k.val) (height k.val+height k.val) _ hsecond (by omega),
      smul_zero,add_zero]

end SymmetricSubgroupAsymptotics.CFSGNormTwoCoordinateRootHeightLeading
