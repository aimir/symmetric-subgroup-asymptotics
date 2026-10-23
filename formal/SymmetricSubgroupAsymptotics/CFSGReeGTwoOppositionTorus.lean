import SymmetricSubgroupAsymptotics.CFSGGTwoOriginalWeylTorusAction
import SymmetricSubgroupAsymptotics.CFSGReeGTwoOriginalOpposition
import SymmetricSubgroupAsymptotics.CFSGReeGTwoOriginalTorus
import Mathlib.GroupTheory.Commutator.Basic

/-! The genuine fixed opposition inverts the genuine fixed torus.
Consequently every torus square is an explicit commutator in the
original fixed group, before taking its full central quotient. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
open scoped Matrix commutatorElement
namespace SymmetricSubgroupAsymptotics.CFSGReeGTwoOppositionTorus
open CFSGGTwoOriginalPositiveRootWords CFSGGTwoOriginalRankTwoTorus
open CFSGGTwoOriginalWeylTorusAction CFSGGTwoNaturalWeylTorusAction
open CFSGReeGTwoOriginalOpposition CFSGReeGTwoOriginalTorus
open CFSGReeGTwoFieldParameters CFSGReeGTwoFixedModelEquivalence

private theorem monomial_mulVec {I : Type*} [Fintype I] [DecidableEq I]
    {K : Type*} [Field K] (sigma : Equiv.Perm I) (d v : I → K) :
    CFSGTypeAMonomialMatrices.monomial sigma d *ᵥ v=fun i => d i*v (sigma i) := by
  funext i
  simp [Matrix.mulVec,dotProduct,CFSGTypeAMonomialMatrices.monomial_apply,ite_mul]

private theorem longest_apply (K : Type) [Field K]
    (v : CFSGGTwoSerreMatrices.Index → K) :
    (CFSGGTwoLongestWeylMonomial.longestUnit K : CFSGGTwoSerreMatrices.Mat K) *ᵥ v=
      fun i => -v (CFSGGTwoLongestWeylMonomial.oppositePermutation i) := by
  rw [CFSGGTwoLongestWeylMonomial.longestUnit_val,monomial_mulVec]
  simp only [neg_one_mul]

private theorem vec4_two {R : Type*} (a b c d : R) :
    (![a,b,c,d] : Fin 4 → R) 2 = c := rfl
private theorem vec4_three {R : Type*} (a b c d : R) :
    (![a,b,c,d] : Fin 4 → R) 3 = d := rfl

private theorem longest_torus_matrix (K : Type) [Field K] (t : Kˣ × Kˣ) :
    (CFSGGTwoLongestWeylMonomial.longestUnit K : CFSGGTwoSerreMatrices.Mat K)*
      ((CFSGGTwoNaturalRankTwoTorus.torusPair K t).val : CFSGGTwoSerreMatrices.Mat K)=
    ((CFSGGTwoNaturalRankTwoTorus.torusPair K t⁻¹).val : CFSGGTwoSerreMatrices.Mat K)*
      (CFSGGTwoLongestWeylMonomial.longestUnit K : CFSGGTwoSerreMatrices.Mat K) := by
  apply Matrix.ext_of_mulVec_single
  intro j
  rw [←Matrix.mulVec_mulVec,←Matrix.mulVec_mulVec,longest_apply,
    CFSGGTwoNaturalRankTwoTorus.torusPair_apply,CFSGGTwoNaturalRankTwoTorus.torusPair_apply,
    longest_apply]
  funext i
  rcases i with i | i <;> fin_cases i <;>
    simp [CFSGGTwoNaturalRankTwoTorus.pairAction,
      CFSGGTwoLongestWeylMonomial.oppositePermutation,CFSGGTwoSerreMatrices.pos,
      CFSGGTwoSerreMatrices.neg,vec4_two,vec4_three,mul_assoc]

theorem longestWord_torusPair (K : Type) [Field K] (t : Kˣ × Kˣ) :
    longestWord K*torusPair K t*(longestWord K)⁻¹=torusPair K t⁻¹ := by
  apply mul_inv_eq_iff_eq_mul.mpr
  apply (CFSGGTwoOriginalNaturalEquivalence.modelEquivNatural K).injective
  apply Subtype.ext
  apply Units.ext
  simpa only [map_mul,Subgroup.coe_mul,Units.val_mul,longestWord_native,torusPair_native]
    using longest_torus_matrix K t

theorem fixedOpposition_fixedTorus (m : ℕ) (t : (Field m)ˣ) :
    fixedOpposition m*fixedTorusHom m t*(fixedOpposition m)⁻¹=
      fixedTorusHom m t⁻¹ := by
  apply Subtype.ext
  change longestWord (Field m)*(fixedTorusHom m t).val*
    (longestWord (Field m))⁻¹=(fixedTorusHom m t⁻¹).val
  rw [fixedTorusHom_val,fixedTorusHom_val,longestWord_torusPair]
  exact congrArg (torusPair (Field m)) (by simp)

theorem fixedTorus_square_commutator (m : ℕ) (t : (Field m)ˣ) :
    ⁅fixedTorusHom m t,fixedOpposition m⁆=fixedTorusHom m (t^2) := by
  calc
    _ = fixedTorusHom m t*(fixedOpposition m*fixedTorusHom m t⁻¹*
        (fixedOpposition m)⁻¹) := by simp only [commutatorElement_def,map_inv,mul_assoc]
    _ = fixedTorusHom m t*fixedTorusHom m t := by rw [fixedOpposition_fixedTorus,inv_inv]
    _ = fixedTorusHom m (t^2) := by rw [pow_two,map_mul]

theorem fixedTorus_square_mem_commutator (m : ℕ) (t : (Field m)ˣ) :
    fixedTorusHom m (t^2)∈commutator (originalModelFixed m) := by
  rw [←fixedTorus_square_commutator,commutator_eq_closure]
  exact Subgroup.subset_closure (commutator_mem_commutatorSet _ _)

end SymmetricSubgroupAsymptotics.CFSGReeGTwoOppositionTorus
