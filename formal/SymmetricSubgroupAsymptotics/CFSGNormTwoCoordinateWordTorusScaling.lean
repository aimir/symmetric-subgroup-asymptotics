import SymmetricSubgroupAsymptotics.CFSGNormTwoCoordinateSimpleRootParametrization
import SymmetricSubgroupAsymptotics.CFSGNormTwoCoordinateWordRootElementSign
import SymmetricSubgroupAsymptotics.CFSGNormTwoCoordinateRootTorusConjugation

/-! Exact torus scaling on a displayed positive-simple Weyl-word chart.
Integral sign comparison with the selected root parametrization cancels
from the conjugation formula, leaving its actual lattice coroot weight.
No choice of signs or field-valued root recognition is assumed. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
namespace SymmetricSubgroupAsymptotics.CFSGNormTwoCoordinateWordTorusScaling
open CFSGIntegerMatrixPairing CFSGNormTwoRootPairing CFSGNormTwoGeckIntegralRealization
open CFSGNormTwoCoordinateSimpleRootParametrization CFSGNormTwoCoordinateWordRootElementSign
open CFSGNormTwoCoordinateRootTorusConjugation CFSGNormTwoGeckParameterizedTorus
open CFSGNormTwoCoordinateSelectedRootElement CFSGNormTwoGeckWeylWordDegree
open CFSGSerreQuadraticMatrix CFSGSerreQuadraticWeylWord CFSGSerreQuadraticWordRootTransport
variable {r : ℕ} (A : Matrix (Fin r) (Fin r) ℤ) (hd : ∀i,A i i=2)
    (hs : A.transpose=A) (hp : (rationalMatrix A).PosDef)
    (ho : ∀i j,i≠j→A i j≤0)
    [Fintype (Roots A)] [DecidableEq (Roots A)]
    [(rootPairing A hs hp).IsReduced] [(rootPairing A hs hp).IsIrreducible]
local notation "b₀" => coordinateBase A hd hs hp ho
local notation "s₀" => coordinateIndexEquiv A hd hs hp ho
local notation "D" => realizationData A hs hp b₀ s₀

theorem torus_conjugate_positive_word (K : Type) [Field K] (i : Fin r) (t : Kˣ)
    (w : List (Fin r)) (j : Fin r) (a : K) :
    parameterTorus A hs hp b₀ s₀ K i t*rootWord D K w false j a*
      (parameterTorus A hs hp b₀ s₀ K i t)⁻¹=
    rootWord D K w false j
      (a*(t : K)^(integerPairing A (s₀ i : Roots A).val (wordRoot A hs hp b₀ s₀ w (s₀ j)).val)) := by
  obtain ⟨eps,heps,hsimple⟩ := selected_simple_root_sign A hd hs hp ho j
  obtain ⟨eta,_,hword⟩ := word_selected_root_sign A hd hs hp ho w (s₀ j)
  have hepssq : (eps : K)*(eps : K)=1 := by
    rcases heps with rfl|rfl <;> norm_num
  have hchart (b : K) : rootWord D K w false j b=
      selectedRootElement A hd hs hp ho K (wordRoot A hs hp b₀ s₀ w (s₀ j))
        ((eta : K)*((eps : K)*b)) := by
    have hroot : canonicalRoot D K false j b=
        selectedRootElement A hd hs hp ho K (s₀ j) ((eps : K)*b) := by
      rw [hsimple K]
      rw [←mul_assoc,hepssq,one_mul]
    change canonicalWord D K w*canonicalRoot D K false j b*(canonicalWord D K w)⁻¹=_
    rw [hroot]
    exact hword K ((eps : K)*b)
  rw [hchart,torus_conjugate_selected_root,hchart]
  congr 1
  ring

end SymmetricSubgroupAsymptotics.CFSGNormTwoCoordinateWordTorusScaling
