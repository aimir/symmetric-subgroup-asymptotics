import SymmetricSubgroupAsymptotics.CFSGNormTwoCoordinateRootWordString
import SymmetricSubgroupAsymptotics.CFSGUnitConjugationPolynomial
import SymmetricSubgroupAsymptotics.CFSGUnitConjugationNilpotence
import SymmetricSubgroupAsymptotics.CFSGSerreQuadraticRationalRootValues

/-! The selected rootWitness parametrization as an ACTUAL integral
root word, including its rational quadratic exponential and base change.
No new root-group law or normalization assumption is imposed. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
namespace SymmetricSubgroupAsymptotics.CFSGNormTwoCoordinateSelectedRootElement
open CFSGIntegerMatrixPairing CFSGNormTwoRootPairing CFSGSerreQuadraticMatrix
open CFSGNormTwoGeckIntegralRealization CFSGNormTwoGeckIntegralWord
open CFSGNormTwoGeckNegativeWordCoefficients CFSGNormTwoCoordinateRootSubgroup
open CFSGNormTwoCoordinateRootWordString CFSGSerreQuadraticWordRootTransport
open CFSGSerreQuadraticWeylWord
variable {r : ℕ} (A : Matrix (Fin r) (Fin r) ℤ) (hd : ∀i,A i i=2)
    (hs : A.transpose=A) (hp : (rationalMatrix A).PosDef)
    (ho : ∀i j,i≠j→A i j≤0)
    [Fintype (Roots A)] [DecidableEq (Roots A)]
    [(rootPairing A hs hp).IsReduced] [(rootPairing A hs hp).IsIrreducible]

local notation "b₀" => coordinateBase A hd hs hp ho
local notation "s₀" => coordinateIndexEquiv A hd hs hp ho
local notation "D" => realizationData A hs hp b₀ s₀
private abbrev CoordMat (K : Type) := Matrix ((b₀).support⊕Roots A) ((b₀).support⊕Roots A) K

def selectedRootElement (K : Type) [CommRing K] (k : Roots A) (a : K) :
    (CoordMat A hd hs hp ho K)ˣ :=
  rootWord D K (rootWitness A hd hs hp ho k).val.1 true
    (rootWitness A hd hs hp ho k).val.2 a

theorem selectedRootElement_inverse (K : Type) [CommRing K] (k : Roots A) (a : K) :
    (selectedRootElement A hd hs hp ho K k a)⁻¹=
      selectedRootElement A hd hs hp ho K k (-a) := by
  simp only [selectedRootElement,rootWord,mul_inv_rev,inv_inv,canonicalRoot_inverse,mul_assoc]

theorem selectedRootElement_mem (K : Type) [Field K] (k : Roots A) (a : K) :
    selectedRootElement A hd hs hp ho K k a∈rootSubgroup A hd hs hp ho K k := by
  exact (mem_wordRootSubgroup_iff A hd hs hp ho K
    (rootWitness A hd hs hp ho k).val.1 (rootWitness A hd hs hp ho k).val.2 _).mpr ⟨a,rfl⟩

theorem selectedCoefficient_conjugate (k : Roots A) :
    (canonicalWord D ℚ (rootWitness A hd hs hp ho k).val.1 : CoordMat A hd hs hp ho ℚ)*
      fieldRoot D ℚ true (rootWitness A hd hs hp ho k).val.2*
      (((canonicalWord D ℚ (rootWitness A hd hs hp ho k).val.1)⁻¹ :
        (CoordMat A hd hs hp ho ℚ)ˣ) : CoordMat A hd hs hp ho ℚ)=
      selectedCoefficient A hd hs hp ho k := by
  simp only [selectedCoefficient,firstCoefficient,
    CFSGAlgebraConjugationAction.action_apply,word_eq_canonicalWord]

theorem selectedRootElement_val_rational (k : Roots A) (a : ℚ) :
    (selectedRootElement A hd hs hp ho ℚ k a : CoordMat A hd hs hp ho ℚ)=
      1+a • selectedCoefficient A hd hs hp ho k+
        (a^2/2) • (selectedCoefficient A hd hs hp ho k)^2 := by
  change (canonicalWord D ℚ (rootWitness A hd hs hp ho k).val.1 : CoordMat A hd hs hp ho ℚ)*
    (canonicalRoot D ℚ true (rootWitness A hd hs hp ho k).val.2 a : CoordMat A hd hs hp ho ℚ)*
    (((canonicalWord D ℚ (rootWitness A hd hs hp ho k).val.1)⁻¹ :
      (CoordMat A hd hs hp ho ℚ)ˣ) : CoordMat A hd hs hp ho ℚ)=_
  rw [canonicalRoot_val_rational]
  exact CFSGUnitConjugationPolynomial.conjugate_quadratic _ _ _
    (selectedCoefficient_conjugate A hd hs hp ho k) a

theorem selectedCoefficient_cube (k : Roots A) : (selectedCoefficient A hd hs hp ho k)^3=0 :=
  CFSGUnitConjugationNilpotence.pow_eq_zero_of_conjugate
    (canonicalWord D ℚ (rootWitness A hd hs hp ho k).val.1) _ _
    (selectedCoefficient_conjugate A hd hs hp ho k) 3
    (fieldRoot_cube D ℚ true (rootWitness A hd hs hp ho k).val.2)

theorem map_selectedRootElement_val {K L : Type} [CommRing K] [CommRing L]
    (f : K→+*L) (k : Roots A) (a : K) :
    f.mapMatrix (selectedRootElement A hd hs hp ho K k a : CoordMat A hd hs hp ho K)=
      (selectedRootElement A hd hs hp ho L k (f a) : CoordMat A hd hs hp ho L) :=
  map_rootWord_val D f _ true _ a

end SymmetricSubgroupAsymptotics.CFSGNormTwoCoordinateSelectedRootElement
