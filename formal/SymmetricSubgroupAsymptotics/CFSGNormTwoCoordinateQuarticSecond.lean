import SymmetricSubgroupAsymptotics.CFSGNormTwoCoordinateQuarticColumn
import SymmetricSubgroupAsymptotics.CFSGNormTwoGeckNegativeLatticeDegree
import SymmetricSubgroupAsymptotics.CFSGNormTwoGeckRationalAdjointStrings
import SymmetricSubgroupAsymptotics.CFSGNormTwoGeckIntegralQuadratic
import SymmetricSubgroupAsymptotics.CFSGGradedMatrixLieDegree

/-! The actual adjacent-root quartic IS the negative second divided-power
matrix. Degree twice the simple root leaves only one possible entry,
and the checked Geck column computes it as minus one. Rational casting
is injective on the SAME integer matrices; no division survives here. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
open scoped Matrix
namespace SymmetricSubgroupAsymptotics.CFSGNormTwoCoordinateQuarticSecond
open CFSGIntegerMatrixPairing CFSGNormTwoRootPairing CFSGSerreQuadraticMatrix
open CFSGNormTwoGeckColumns CFSGNormTwoGeckLatticeDegree CFSGGradedMatrixSupport
open CFSGGradedMatrixLieDegree CFSGNormTwoGeckNegativeLatticeDegree
open CFSGNormTwoGeckIntegralRealization CFSGNormTwoGeckRationalAdjointStrings
open CFSGNormTwoGeckDoubleRootSupport CFSGNormTwoCoordinateQuarticColumn
open CFSGNormTwoGeckQuadratic CFSGNormTwoGeckIntegralQuadratic
variable {r : ℕ} (A : Matrix (Fin r) (Fin r) ℤ) (hd : ∀i,A i i=2)
    (hs : A.transpose=A) (hp : (rationalMatrix A).PosDef)
    (ho : ∀i j,i≠j→A i j≤0)
    [Fintype (Roots A)] [DecidableEq (Roots A)]
    [(rootPairing A hs hp).IsReduced] [(rootPairing A hs hp).IsIrreducible]
local notation "b₀" => coordinateBase A hd hs hp ho
local notation "s₀" => coordinateIndexEquiv A hd hs hp ho
private abbrev MatQ := Matrix ((b₀).support⊕Roots A) ((b₀).support⊕Roots A) ℚ

theorem rational_quartic_eq_negative_second (i j : Fin r) (hij : i≠j)
    (hA : A i j= -1) (hA' : A j i= -1) :
    (⁅(RootPairing.GeckConstruction.e (s₀ i) : MatQ A hd hs hp ho),
      RootPairing.GeckConstruction.e (s₀ j)⁆ * RootPairing.GeckConstruction.f (s₀ j))^2=
        -secondMatrix A hs hp b₀ (s₀ i) := by
  let X : MatQ A hd hs hp ho := RootPairing.GeckConstruction.e (s₀ i)
  let Y : MatQ A hd hs hp ho := RootPairing.GeckConstruction.e (s₀ j)
  let Z : MatQ A hd hs hp ho := RootPairing.GeckConstruction.f (s₀ j)
  let M : MatQ A hd hs hp ho := (⁅X,Y⁆*Z)^2
  have hX : Supported (latticeWeight A hs hp b₀) (fun v=>v+(s₀ i : Roots A).val) X := by
    simpa only [rational_E_eq,CFSGGeckSerreRepresentation.E] using
      field_E_lattice_support A hs hp b₀ s₀ ℚ i
  have hY : Supported (latticeWeight A hs hp b₀) (fun v=>v+(s₀ j : Roots A).val) Y := by
    simpa only [rational_E_eq,CFSGGeckSerreRepresentation.E] using
      field_E_lattice_support A hs hp b₀ s₀ ℚ j
  have hZ := rational_F_lattice_support A hs hp b₀ (s₀ j)
  have hCZ : Supported (latticeWeight A hs hp b₀) (fun v=>v+(s₀ i : Roots A).val) (⁅X,Y⁆*Z) := by
    apply supported_congr (supported_mul (supported_lie _ _ _ X Y hX hY) hZ)
    intro v
    dsimp only [Function.comp_apply]
    abel
  have hM : Supported (latticeWeight A hs hp b₀)
      (fun v=>v+(2:ℤ) • (s₀ i : Roots A).val) M := by
    dsimp only [M]
    rw [pow_two]
    apply supported_congr (supported_mul hCZ hCZ)
    intro v
    dsimp only [Function.comp_apply]
    rw [two_smul]
    abel
  have hsingle := double_root_supported_single A hs hp b₀ (s₀ i : Roots A) M hM
  have hentry : M (Sum.inr (s₀ i : Roots A))
      (Sum.inr (negativeIndex A hs hp (s₀ i)))= -1 := by
    have hc := quartic_negative_column A hd hs hp ho i j hij hA hA'
    change M*ᵥPi.single (Sum.inr (negativeIndex A hs hp (s₀ i))) (1:ℚ)=
      -Pi.single (Sum.inr (s₀ i : Roots A)) (1:ℚ) at hc
    rw [Matrix.mulVec_single_one] at hc
    have he := congrFun hc (Sum.inr (s₀ i : Roots A))
    change M (Sum.inr (s₀ i : Roots A)) (Sum.inr (negativeIndex A hs hp (s₀ i)))=
      -((Pi.single (Sum.inr (s₀ i : Roots A)) (1:ℚ) :
        ((b₀).support⊕Roots A)→ℚ) (Sum.inr (s₀ i : Roots A))) at he
    simpa [Pi.single_apply] using he
  change M= -secondMatrix A hs hp b₀ (s₀ i)
  calc
    M=Matrix.single (Sum.inr (s₀ i : Roots A))
      (Sum.inr (negativeIndex A hs hp (s₀ i)))
        (M (Sum.inr (s₀ i : Roots A)) (Sum.inr (negativeIndex A hs hp (s₀ i)))) := hsingle
    _= -secondMatrix A hs hp b₀ (s₀ i) := by
      rw [hentry]
      ext x y
      change (if Sum.inr (s₀ i : Roots A)=x ∧
          Sum.inr (negativeIndex A hs hp (s₀ i))=y then (-1:ℚ) else 0)=
        -(if Sum.inr (s₀ i : Roots A)=x ∧
          Sum.inr (negativeIndex A hs hp (s₀ i))=y then (1:ℚ) else 0)
      split_ifs <;> simp

theorem integral_quartic_eq_negative_second (i j : Fin r) (hij : i≠j)
    (hA : A i j= -1) (hA' : A j i= -1) :
    (⁅CFSGGeckIntegralMatrices.E b₀ (s₀ i),CFSGGeckIntegralMatrices.E b₀ (s₀ j)⁆ *
      CFSGGeckIntegralMatrices.F b₀ (s₀ j))^2= -positiveSecond A hs hp b₀ (s₀ i) := by
  apply CFSGSerreSquareZeroMatrix.integerCast_injective ((b₀).support⊕Roots A)
  change (Int.castRingHom ℚ).mapMatrix _=(Int.castRingHom ℚ).mapMatrix _
  simp only [map_pow,map_mul,Ring.lie_def,map_sub,map_neg,
    CFSGGeckIntegralMatrices.map_E,CFSGGeckIntegralMatrices.map_F,map_positiveSecond]
  exact rational_quartic_eq_negative_second A hd hs hp ho i j hij hA hA'

end SymmetricSubgroupAsymptotics.CFSGNormTwoCoordinateQuarticSecond
