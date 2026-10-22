import SymmetricSubgroupAsymptotics.CFSGNormTwoCoordinateRootWordString
import SymmetricSubgroupAsymptotics.CFSGNormTwoCoordinateGeneratedRootLine
import SymmetricSubgroupAsymptotics.CFSGNormTwoGeckIntegralWord
import SymmetricSubgroupAsymptotics.CFSGNormTwoGeckPrimitiveRootEntry
import SymmetricSubgroupAsymptotics.CFSGIntegralPrimitiveLineScalar

/-! The original selected rootWitness line is nonzero and primitive
integrally. Actual generated-Lie membership yields rational proportionality;
an arbitrary integral matrix on this line has an INTEGER scalar. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
namespace SymmetricSubgroupAsymptotics.CFSGNormTwoCoordinateSelectedRootLine
open CFSGIntegerMatrixPairing CFSGNormTwoRootPairing CFSGSerreQuadraticMatrix
open CFSGNormTwoGeckIntegralRealization CFSGNormTwoGeckLatticeDegree
open CFSGNormTwoGeckIntegralWord CFSGNormTwoGeckPrimitiveRootEntry
open CFSGNormTwoGeckNegativeWordCoefficients CFSGNormTwoCoordinateRootSubgroup
open CFSGNormTwoCoordinateRootWordString CFSGNormTwoGeckRationalWeylCollecting
open CFSGSerreQuadraticWeylWord CFSGGradedMatrixSupport
variable {r : ℕ} (A : Matrix (Fin r) (Fin r) ℤ) (hd : ∀i,A i i=2)
    (hs : A.transpose=A) (hp : (rationalMatrix A).PosDef)
    (ho : ∀i j,i≠j→A i j≤0)
    [Fintype (Roots A)] [DecidableEq (Roots A)]
    [(rootPairing A hs hp).IsReduced] [(rootPairing A hs hp).IsIrreducible]

local notation "b₀" => coordinateBase A hd hs hp ho
local notation "s₀" => coordinateIndexEquiv A hd hs hp ho
local notation "D" => realizationData A hs hp b₀ s₀
private abbrev CoordMat (K : Type) := Matrix ((b₀).support⊕Roots A) ((b₀).support⊕Roots A) K
local notation "MatQ" => CoordMat A hd hs hp ho ℚ
local notation "MatZ" => CoordMat A hd hs hp ho ℤ
local notation "ell" => latticeWeight A hs hp b₀

def integerSelectedCoefficient (k : Roots A) : MatZ :=
  let p := rootWitness A hd hs hp ho k
  (canonicalWord D ℤ p.val.1 : MatZ)*CFSGGeckIntegralMatrices.F b₀ (s₀ p.val.2)*
    (((canonicalWord D ℤ p.val.1)⁻¹ : (MatZ)ˣ) : MatZ)

theorem cast_integerSelectedCoefficient (k : Roots A) :
    (Int.castRingHom ℚ).mapMatrix (integerSelectedCoefficient A hd hs hp ho k)=
      selectedCoefficient A hd hs hp ho k := by
  simp only [integerSelectedCoefficient,selectedCoefficient,firstCoefficient,
    CFSGAlgebraConjugationAction.action_apply,map_mul,cast_integer_word,
    cast_integer_word_inverse,CFSGGeckIntegralMatrices.map_F,rational_F_eq,
    CFSGGeckSerreRepresentation.F]

theorem selectedCoefficient_ne_zero (k : Roots A) :
    selectedCoefficient A hd hs hp ho k≠0 :=
  first_ne_zero A hs hp b₀ s₀ ℚ
    (rootWitness A hd hs hp ho k).val.1 (rootWitness A hd hs hp ho k).val.2

theorem mem_selected_line (k : Roots A) (M : MatQ)
    (hM : M∈RootPairing.GeckConstruction.lieAlgebra b₀)
    (hdeg : Supported ell (fun v=>v+k.val) M) :
    ∃c : ℚ,M=c • selectedCoefficient A hd hs hp ho k := by
  let p := rootWitness A hd hs hp ho k
  rw [p.property] at hdeg
  obtain ⟨c,hc⟩ := CFSGNormTwoCoordinateGeneratedRootLine.word_degree_line A hd hs hp ho
    p.val.1 p.val.2 M hM hdeg
  refine ⟨c,?_⟩
  simpa only [selectedCoefficient,firstCoefficient,rational_F_eq] using hc

theorem selected_line_scalar_is_integer (k : Roots A) (M : MatZ) (c : ℚ)
    (hc : (Int.castRingHom ℚ).mapMatrix M=c • selectedCoefficient A hd hs hp ho k) :
    ∃n : ℤ,c=(n:ℚ) := by
  let p := rootWitness A hd hs hp ho k
  apply CFSGIntegralPrimitiveLineScalar.scalar_is_integer
    (canonicalWord D ℤ p.val.1) (CFSGGeckIntegralMatrices.F b₀ (s₀ p.val.2)) M
    (Sum.inl (s₀ p.val.2)) (Sum.inr (s₀ p.val.2:Roots A))
    (integer_F_unit_entry A hs hp b₀ (s₀ p.val.2)) c
  exact hc.trans (congrArg (fun N : MatQ=>c • N)
    (cast_integerSelectedCoefficient A hd hs hp ho k).symm)

end SymmetricSubgroupAsymptotics.CFSGNormTwoCoordinateSelectedRootLine
