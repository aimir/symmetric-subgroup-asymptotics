import SymmetricSubgroupAsymptotics.CFSGTrialityGeckSimpleOrbitFlags
import SymmetricSubgroupAsymptotics.CFSGTrialityGeckShortParameterWeyl
import SymmetricSubgroupAsymptotics.CFSGNormTwoGeckSelfRootConjugation

/-! Actual simple relative Weyl words exchange the full short and long
parameter charts with their opposite charts. The outer calculation
retains three independent parameters before restricting to Frobenius
triples, so it also controls the full ambient orbit-zero subgroup. -/
set_option autoImplicit false
set_option Elab.async false
set_option backward.isDefEq.respectTransparency false
noncomputable section
open scoped Classical
namespace SymmetricSubgroupAsymptotics.CFSGTrialityGeckSimpleChartWeyl
open CFSGTrialityD4NormTwo CFSGTrialityGeckDiagramCovariance CFSGTrialityFixedWeylWords
open CFSGTrialityGeckFixedRootWords CFSGTrialityGeckShortParameterWeyl
open CFSGTrialityGeckSimpleOrbitFlags CFSGNormTwoGeckOrthogonalWeyl
open CFSGNormTwoGeckSelfRootConjugation CFSGSerreQuadraticMatrix CFSGSerreQuadraticWeylWord
local notation "A" => CartanMatrix.D 4
local notation "hs" => CartanMatrix.D_transpose 4
local notation "hp" => D4_positive_definite
local instance : DecidableEq (CFSGNormTwoRootPairing.Roots A) := Classical.decEq _

private theorem outer_weyl_other (K : Type) [Field K] (i j : Fin 3) (hij : i≠j)
    (neg : Bool) (t : K) :
    canonicalWeyl rawData K (outerNode i)*canonicalRoot rawData K neg (outerNode j) t*
      (canonicalWeyl rawData K (outerNode i))⁻¹=canonicalRoot rawData K neg (outerNode j) t := by
  have hc : CFSGGeckSerreRepresentation.cartan Base Index (outerNode i) (outerNode j)=0 := by
    rw [CFSGTrialityD4NormTwo.cartan_eq]
    exact outerNode_cartan i j hij
  have hcW : Commute (canonicalWeyl rawData K (outerNode i))
      (canonicalRoot rawData K neg (outerNode j) t) :=
    orthogonal_weyl_root A hs hp Base Index K (outerNode i) (outerNode j) hc neg t
  rw [hcW.eq]
  group

private theorem outer_weyl_self (K : Type) [Field K] (i : Fin 3) (t : K) :
    canonicalWeyl rawData K (outerNode i)*canonicalRoot rawData K false (outerNode i) t*
      (canonicalWeyl rawData K (outerNode i))⁻¹=canonicalRoot rawData K true (outerNode i) (-t) :=
  self_root_word A hs hp Base Index K (outerNode i) t

theorem outer_word_conjugates_root (K : Type) [Field K] (j : Fin 3) (t : K) :
    CFSGTrialityGeckFixedRootWords.shortWeyl K*canonicalRoot rawData K false (outerNode j) t*(CFSGTrialityGeckFixedRootWords.shortWeyl K)⁻¹=
      canonicalRoot rawData K true (outerNode j) (-t) := by
  let W (i : Fin 3) := canonicalWeyl rawData K (outerNode i)
  have hw : CFSGTrialityGeckFixedRootWords.shortWeyl K=W 0*W 1*W 2 := by
    simp only [CFSGTrialityGeckFixedRootWords.shortWeyl,canonicalWord,mul_one,mul_assoc]
    rfl
  rw [hw]
  calc
    _=W 0*(W 1*(W 2*canonicalRoot rawData K false (outerNode j) t*(W 2)⁻¹)*
      (W 1)⁻¹)*(W 0)⁻¹ := by group
    _=_ := by
      dsimp only [W]
      rcases (show j=0 ∨ j=1 ∨ j=2 by fin_cases j <;> decide) with rfl|rfl|rfl
      · rw [outer_weyl_other K 2 0 (by decide),outer_weyl_other K 1 0 (by decide)]
        exact outer_weyl_self K 0 t
      · rw [outer_weyl_other K 2 1 (by decide),outer_weyl_self K 1 t]
        exact outer_weyl_other K 0 1 (by decide) true (-t)
      · rw [outer_weyl_self K 2 t,
          outer_weyl_other K 1 2 (by decide)]
        exact outer_weyl_other K 0 2 (by decide) true (-t)

theorem outer_word_conjugates_product (K : Type) [Field K] (a b c : K) :
    CFSGTrialityGeckFixedRootWords.shortWeyl K*(canonicalRoot rawData K false 0 a*canonicalRoot rawData K false 2 b*
      canonicalRoot rawData K false 3 c)*(CFSGTrialityGeckFixedRootWords.shortWeyl K)⁻¹=
      canonicalRoot rawData K true 0 (-a)*canonicalRoot rawData K true 2 (-b)*
        canonicalRoot rawData K true 3 (-c) := by
  let e := MulAut.conj (CFSGTrialityGeckFixedRootWords.shortWeyl K)
  change e (canonicalRoot rawData K false 0 a*canonicalRoot rawData K false 2 b*
    canonicalRoot rawData K false 3 c)=_
  rw [map_mul,map_mul]
  exact congrArg₂ (fun x y=>x*y)
    (congrArg₂ (fun x y=>x*y) (outer_word_conjugates_root K 0 a)
      (outer_word_conjugates_root K 1 b)) (outer_word_conjugates_root K 2 c)

theorem short_word_conjugates (K : Type) [Field K] (sigma : K≃+*K) (t : K) :
    canonicalWord rawData K (orbitWord false)*shortOrbit K sigma false t*
      (canonicalWord rawData K (orbitWord false))⁻¹=shortOrbit K sigma true (-t) := by
  change CFSGTrialityGeckFixedRootWords.shortWeyl K*shortOrbit K sigma false t*(CFSGTrialityGeckFixedRootWords.shortWeyl K)⁻¹=_
  simpa only [shortOrbit,map_neg] using outer_word_conjugates_product K t (sigma t) (sigma (sigma t))

theorem middle_word_conjugates (K : Type) [Field K] (t : K) :
    canonicalWord rawData K (orbitWord true)*canonicalRoot rawData K false 1 t*
      (canonicalWord rawData K (orbitWord true))⁻¹=canonicalRoot rawData K true 1 (-t) := by
  change (canonicalWeyl rawData K 1*1)*canonicalRoot rawData K false 1 t*
    (canonicalWeyl rawData K 1*1)⁻¹=_
  simp only [mul_one]
  exact self_root_word A hs hp Base Index K 1 t

end SymmetricSubgroupAsymptotics.CFSGTrialityGeckSimpleChartWeyl
