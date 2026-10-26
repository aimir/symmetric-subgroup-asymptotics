import SymmetricSubgroupAsymptotics.CFSGReeFFourBinaryMiddleSquareOpposition
import SymmetricSubgroupAsymptotics.CFSGReeFFourBinaryPositiveCentralWord
import SymmetricSubgroupAsymptotics.CFSGReeFFourBinaryDerivedGeneration

/-! Original-group rank-one data attached to the ACTUAL decoded centre
word. The opposed square is identified by proved inner normalization,
not a representation test. No automorphism is extended to the ambient
fixed group and no individual E6 parameter is assumed exceptional-fixed. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
namespace SymmetricSubgroupAsymptotics.CFSGReeFFourBinaryCentralReflection
open CFSGReeFFourBinaryMiddleSquareOpposition CFSGReeFFourBinaryPenultimateWeyl
open CFSGReeFFourBinaryPositiveCentralWord CFSGReeFFourMiddleDerivedFiveWord
open CFSGReeFFourFixedModelEquivalence CFSGReeFFourRelativePositiveSubgroups
open CFSGReeFFourOppositionFixedPositiveNegative CFSGReeFFourInversionPeelingWords
open CFSGReeFFourMinimalParabolics CFSGOpposedSubgroupPeelingChain
open CFSGReeFFourBinaryDerivedGeneration

private theorem step_eq_simple (m : ℕ) (head : Bool) (n : ℕ) :
    step m head n=simpleWeyl m (axis head n) := rfl

private theorem commute_conjugate {G : Type*} [Group G] (a b : G) (h : Commute a b) :
    a*b*a⁻¹=b := by rw [h.eq,mul_assoc,mul_inv_cancel,mul_one]

private theorem transport_opposition {G : Type*} [Group G] (o k w s : G)
    (hok : Commute o k) (hop : o*s*o⁻¹=w*s*w⁻¹) :
    o*(k*s*k⁻¹)*o⁻¹=
      (k*w*k⁻¹)*(k*s*k⁻¹)*(k*w*k⁻¹)⁻¹ := by
  have hk := commute_conjugate o k hok
  have hki := commute_conjugate o k⁻¹ hok.inv_right
  calc
    _=(o*k*o⁻¹)*(o*s*o⁻¹)*(o*k⁻¹*o⁻¹) := by group
    _=k*(w*s*w⁻¹)*k⁻¹ := by rw [hk,hop,hki]
    _=_ := by group

private theorem conjugate_square {G : Type*} [Group G] (k w : G) (hw : w^2=1) :
    (k*w*k⁻¹)^2=1 := by
  have h := congrArg (MulAut.conj k) hw
  simpa only [map_pow,map_one] using h

def centralConjugator : originalModelFixed 0 := (wordPrefix (step 0 true) 4)⁻¹

def centralReflection : originalModelFixed 0 :=
  centralConjugator*middleFixedWeyl 0*centralConjugator⁻¹

def negativeCentralWord : originalModelFixed 0 :=
  oppositionFixed 0*centralWord*(oppositionFixed 0)⁻¹

theorem centralWord_eq_conjugate :
    centralWord=centralConjugator*(fourCycle 0)^2*centralConjugator⁻¹ := by
  simp only [centralWord,centralConjugator,inv_inv]

theorem opposition_commute_prefix (n : ℕ) :
    Commute (oppositionFixed 0) (wordPrefix (step 0 true) n) := by
  induction n with
  | zero => exact Commute.one_right _
  | succ n ih =>
    have hs : Commute (oppositionFixed 0) (step 0 true n) := by
      rw [step_eq_simple]
      exact binary_opposition_commute_simple _
    exact hs.mul_right ih

theorem opposition_commute_centralConjugator :
    Commute (oppositionFixed 0) centralConjugator :=
  (opposition_commute_prefix 4).inv_right

theorem negativeCentralWord_eq :
    negativeCentralWord=centralReflection*centralWord*centralReflection⁻¹ := by
  dsimp only [negativeCentralWord,centralReflection]
  rw [centralWord_eq_conjugate]
  exact transport_opposition (oppositionFixed 0) centralConjugator
    (middleFixedWeyl 0) ((fourCycle 0)^2)
    opposition_commute_centralConjugator binary_opposition_middle_square

theorem centralReflection_square : centralReflection^2=1 :=
  conjugate_square centralConjugator (middleFixedWeyl 0) (middleWeyl_square 0)

theorem centralReflection_mem_derived :
    centralReflection∈commutator (originalModelFixed 0) :=
  (inferInstance : (commutator (originalModelFixed 0)).Normal).conj_mem
    _ (middle_weyl_mem_derived 0) centralConjugator

end SymmetricSubgroupAsymptotics.CFSGReeFFourBinaryCentralReflection
