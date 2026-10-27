import SymmetricSubgroupAsymptotics.CFSGMonsterE6SelectedReflectionWords
import SymmetricSubgroupAsymptotics.CFSGMonsterSelectedDerivedCube
import SymmetricSubgroupAsymptotics.E6BraidSystemDerivedNormalizerIndex
import SymmetricSubgroupAsymptotics.CFSGMonsterE6CentralizerOneCertificate
import SymmetricSubgroupAsymptotics.CFSGMonsterE6CentralizerTwoCertificate
import SymmetricSubgroupAsymptotics.CFSGMonsterE6CentralizerThreeCertificate
import SymmetricSubgroupAsymptotics.CFSGMonsterE6CentralizerFourCertificate
import SymmetricSubgroupAsymptotics.CFSGMonsterE6CentralizerFiveCertificate
import SymmetricSubgroupAsymptotics.CFSGMonsterE6PairZeroOneCertificate
import SymmetricSubgroupAsymptotics.CFSGMonsterE6PairZeroTwoCertificate
import SymmetricSubgroupAsymptotics.CFSGMonsterE6PairZeroThreeCertificate
import SymmetricSubgroupAsymptotics.CFSGMonsterE6PairZeroFourCertificate
import SymmetricSubgroupAsymptotics.CFSGMonsterE6PairZeroFiveCertificate
import SymmetricSubgroupAsymptotics.CFSGMonsterE6PairOneTwoCertificate
import SymmetricSubgroupAsymptotics.CFSGMonsterE6PairOneThreeCertificate
import SymmetricSubgroupAsymptotics.CFSGMonsterE6PairOneFourCertificate
import SymmetricSubgroupAsymptotics.CFSGMonsterE6PairOneFiveCertificate
import SymmetricSubgroupAsymptotics.CFSGMonsterE6PairTwoThreeCertificate
import SymmetricSubgroupAsymptotics.CFSGMonsterE6PairTwoFourCertificate
import SymmetricSubgroupAsymptotics.CFSGMonsterE6PairTwoFiveCertificate
import SymmetricSubgroupAsymptotics.CFSGMonsterE6PairThreeFourCertificate
import SymmetricSubgroupAsymptotics.CFSGMonsterE6PairThreeFiveCertificate
import SymmetricSubgroupAsymptotics.CFSGMonsterE6PairFourFiveCertificate

/-! Literal actual Monster E6 braid binding from the checked finite relations.
No System, root representation, compatible normalizer or capacity premise
is assumed. Every concrete relation is imported from its literal checked
certificate. The target is the ACTUAL derived node centralizer. -/
set_option autoImplicit false
noncomputable section
namespace SymmetricSubgroupAsymptotics.CFSGMonsterE6ActualNormalizerIndex
open CFSG.Models.MonsterConstruction
open CFSGMonsterE6SelectedReflectionWords
open InvolutionBraidPresentation
open CFSGYE6SelectedWords (adjacent)

 theorem reflection_mem_centralizer (i : Fin 6) : reflection i∈nodeCentralizer := by
  fin_cases i
  · exact zero_mem_centralizer
  · exact CFSGMonsterE6CentralizerOneCertificate.selected_mem_centralizer
  · exact CFSGMonsterE6CentralizerTwoCertificate.selected_mem_centralizer
  · exact CFSGMonsterE6CentralizerThreeCertificate.selected_mem_centralizer
  · exact CFSGMonsterE6CentralizerFourCertificate.selected_mem_centralizer
  · exact CFSGMonsterE6CentralizerFiveCertificate.selected_mem_centralizer

 def centralReflection (i : Fin 6) : nodeCentralizer := ⟨reflection i,reflection_mem_centralizer i⟩

private theorem period_of_lt (i j : Fin 6) (hij : i < j) :
    (reflection i*reflection j)^(if adjacent i j then 3 else 2)=1 := by
  fin_cases i <;> fin_cases j <;> norm_num at hij
  · simpa only [adjacent] using CFSGMonsterE6PairZeroOneCertificate.pair_period
  · simpa only [adjacent] using CFSGMonsterE6PairZeroTwoCertificate.pair_period
  · simpa only [adjacent] using CFSGMonsterE6PairZeroThreeCertificate.pair_period
  · simpa only [adjacent] using CFSGMonsterE6PairZeroFourCertificate.pair_period
  · simpa only [adjacent] using CFSGMonsterE6PairZeroFiveCertificate.pair_period
  · simpa only [adjacent] using CFSGMonsterE6PairOneTwoCertificate.pair_period
  · simpa only [adjacent] using CFSGMonsterE6PairOneThreeCertificate.pair_period
  · simpa only [adjacent] using CFSGMonsterE6PairOneFourCertificate.pair_period
  · simpa only [adjacent] using CFSGMonsterE6PairOneFiveCertificate.pair_period
  · simpa only [adjacent] using CFSGMonsterE6PairTwoThreeCertificate.pair_period
  · simpa only [adjacent] using CFSGMonsterE6PairTwoFourCertificate.pair_period
  · simpa only [adjacent] using CFSGMonsterE6PairTwoFiveCertificate.pair_period
  · simpa only [adjacent] using CFSGMonsterE6PairThreeFourCertificate.pair_period
  · simpa only [adjacent] using CFSGMonsterE6PairThreeFiveCertificate.pair_period
  · simpa only [adjacent] using CFSGMonsterE6PairFourFiveCertificate.pair_period

private theorem adjacent_symm (i j : Fin 6) : adjacent i j=adjacent j i := by
  fin_cases i <;> fin_cases j <;> rfl

private theorem pair_period_swap {K : Type*} [Group K] (x y : K) (hx : x*x=1) (hy : y*y=1)
    (m : ℕ) (h : (x*y)^m=1) : (y*x)^m=1 := by
  have hi : x⁻¹=x := inv_eq_of_mul_eq_one_right hx
  have hj : y⁻¹=y := inv_eq_of_mul_eq_one_right hy
  calc
    (y*x)^m=((x*y)⁻¹)^m := by rw [mul_inv_rev,hi,hj]
    _=1 := by rw [inv_pow,h,inv_one]

private theorem pair_period (i j : Fin 6) (hne : i≠j) :
    (reflection i*reflection j)^(if adjacent i j then 3 else 2)=1 := by
  by_cases hij : i < j
  · exact period_of_lt i j hij
  · have hji : j < i := by omega
    have h := period_of_lt j i hji
    rw [adjacent_symm j i] at h
    exact pair_period_swap _ _ (reflection_square j) (reflection_square i) _ h

private theorem commute_of_period_two {K : Type*} [Group K] (x y : K)
    (hx : x*x=1) (hy : y*y=1) (h : (x*y)^2=1) : x*y=y*x := by
  have hi : x⁻¹=x := inv_eq_of_mul_eq_one_right hx
  have hj : y⁻¹=y := inv_eq_of_mul_eq_one_right hy
  have hp : (x*y)⁻¹=x*y := inv_eq_of_mul_eq_one_right (by simpa only [pow_two] using h)
  have hh : y*x=x*y := by simpa only [mul_inv_rev,hi,hj] using hp
  exact hh.symm

private theorem braid_of_period_three {K : Type*} [Group K] (x y : K)
    (hx : x*x=1) (hy : y*y=1) (h : (x*y)^3=1) : x*y*x=y*x*y := by
  have hi : x⁻¹=x := inv_eq_of_mul_eq_one_right hx
  have hj : y⁻¹=y := inv_eq_of_mul_eq_one_right hy
  have hinv : (x*y*x)⁻¹=x*y*x := by simp only [mul_inv_rev,hi,hj,mul_assoc]
  have hm : (x*y*x)*(y*x*y)=1 := by
    simpa only [pow_succ,pow_zero,mul_one,one_mul,mul_assoc] using h
  calc
    _=(x*y*x)⁻¹ := hinv.symm
    _=(x*y*x)⁻¹*((x*y*x)*(y*x*y)) := by rw [hm,mul_one]
    _=_ := by group

 def system : System adjacent ↥nodeCentralizer where
  generator := centralReflection
  square i := by
    apply Subtype.ext
    exact reflection_square i
  commute i j hij := by
    apply Subtype.ext
    by_cases he : i=j
    · subst j
      rfl
    · apply commute_of_period_two _ _ (reflection_square i) (reflection_square j)
      simpa only [hij,Bool.false_eq_true,↓reduceIte] using pair_period i j he
  braid i j hij := by
    apply Subtype.ext
    have he : i≠j := by
      intro h
      subst j
      have hf : adjacent i i=false := by fin_cases i <;> rfl
      rw [hf] at hij
      cases hij
    apply braid_of_period_three _ _ (reflection_square i) (reflection_square j)
    simpa only [hij,↓reduceIte] using pair_period i j he

 theorem selected_cube_binding :
    E6BraidSystemDerivedWords.a system=CFSGMonsterSelectedDerivedCube.selectedCube := by
  apply Subtype.ext
  change E6BraidSystemWordAlgebra.a system=
    (CFSGMonsterSelectedDerivedCube.selectedCube : nodeCentralizer)
  rw [E6BraidSystemWordAlgebra.raw_a]
  apply Subtype.ext
  change reflection 1*reflection 2=
    (CFSGMonsterSelectedDerivedInvolution.centralArm 0 : Bimonster)*
      (CFSGMonsterSelectedDerivedInvolution.centralArm 1 : Bimonster)
  rw [first_anchor,second_anchor]

 theorem proper_index_ge_twentySeven [Finite CFSG.Models.Monster] [IsSimpleGroup CFSG.Models.Monster]
    (hn : ¬IsMulCommutative CFSG.Models.Monster)
    (H : Subgroup CFSG.Models.Monster) (hH : H≠⊤) : 27≤H.index := by
  apply E6BraidSystemDerivedNormalizerIndex.proper_index_ge_twentySeven system
  · rw [selected_cube_binding]
    exact CFSGMonsterSelectedDerivedCube.selected_ne_one hn
  · exact hH

end SymmetricSubgroupAsymptotics.CFSGMonsterE6ActualNormalizerIndex
