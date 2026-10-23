import SymmetricSubgroupAsymptotics.CFSGNormTwoCoordinateWordTorusScaling
import SymmetricSubgroupAsymptotics.CFSGNormTwoCoordinateA2ReflectionLabels
import SymmetricSubgroupAsymptotics.CFSGNormTwoGeckSelfRootConjugation
import SymmetricSubgroupAsymptotics.CFSGNormTwoGeckTorusConjugation

/-! Actual torus scaling on both signs of the canonical simple roots.
The negative formula follows from the literal self-root Weyl reflection
and the integral degree of its reflected positive-word chart. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
namespace SymmetricSubgroupAsymptotics.CFSGNormTwoCoordinateSignedTorusConjugation
open CFSGIntegerMatrixPairing CFSGNormTwoRootPairing CFSGNormTwoGeckIntegralRealization
open CFSGNormTwoCoordinateWordTorusScaling CFSGNormTwoCoordinateA2ReflectionLabels
open CFSGNormTwoGeckSelfRootConjugation CFSGNormTwoGeckTorusConjugation
open CFSGNormTwoGeckParameterizedTorus CFSGNormTwoGeckWeylWordDegree
open CFSGSerreQuadraticMatrix CFSGSerreQuadraticWeylWord
open CFSGSerreQuadraticWordRootTransport
open CFSGNormTwoGeckColumns
variable {r : ℕ} (A : Matrix (Fin r) (Fin r) ℤ) (hd : ∀i,A i i=2)
    (hs : A.transpose=A) (hp : (rationalMatrix A).PosDef)
    (ho : ∀i j,i≠j→A i j≤0)
    [Fintype (Roots A)] [DecidableEq (Roots A)]
    [(rootPairing A hs hp).IsReduced] [(rootPairing A hs hp).IsIrreducible]
local notation "b₀" => coordinateBase A hd hs hp ho
local notation "s₀" => coordinateIndexEquiv A hd hs hp ho
local notation "D" => realizationData A hs hp b₀ s₀

theorem torus_conjugate_negative (K : Type) [Field K] (i j : Fin r) (t : Kˣ) (a : K) :
    parameterTorus A hs hp b₀ s₀ K i t*canonicalRoot D K true j a*
      (parameterTorus A hs hp b₀ s₀ K i t)⁻¹=
      canonicalRoot D K true j (a*(t : K)^(-integerPairing A (s₀ i : Roots A).val (s₀ j : Roots A).val)) := by
  have hchart (c : K) : rootWord D K [j] false j c=canonicalRoot D K true j (-c) := by
    change canonicalWord D K [j]*canonicalRoot D K false j c*(canonicalWord D K [j])⁻¹=_
    simp only [canonicalWord,mul_one]
    exact self_root_word A hs hp b₀ s₀ K j c
  have hdegree : integerPairing A (s₀ i : Roots A).val
      (wordRoot A hs hp b₀ s₀ [j] (s₀ j)).val=
      -integerPairing A (s₀ i : Roots A).val (s₀ j : Roots A).val := by
    rw [reflect_simple_self A hd hs hp ho j,negative_val]
    exact map_neg (integerPairing A (s₀ i : Roots A).val) (s₀ j : Roots A).val
  have he := torus_conjugate_positive_word A hd hs hp ho K i t [j] j (-a)
  rw [hdegree,hchart,hchart] at he
  simpa only [neg_neg,neg_mul] using he

theorem torus_conjugate_signed (K : Type) [Field K] (i j : Fin r) (t : Kˣ) (neg : Bool) (a : K) :
    parameterTorus A hs hp b₀ s₀ K i t*canonicalRoot D K neg j a*
      (parameterTorus A hs hp b₀ s₀ K i t)⁻¹=
      canonicalRoot D K neg j (a*(t : K)^
        (if neg then -integerPairing A (s₀ i : Roots A).val (s₀ j : Roots A).val
          else integerPairing A (s₀ i : Roots A).val (s₀ j : Roots A).val)) := by
  cases neg
  · exact torus_conjugate_positive A hs hp b₀ s₀ K i j t a
  · exact torus_conjugate_negative A hd hs hp ho K i j t a

end SymmetricSubgroupAsymptotics.CFSGNormTwoCoordinateSignedTorusConjugation
