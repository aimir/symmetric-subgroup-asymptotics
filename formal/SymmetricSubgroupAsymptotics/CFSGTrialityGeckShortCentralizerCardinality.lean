import SymmetricSubgroupAsymptotics.CFSGTrialityGeckShortSectionCentralizer
import SymmetricSubgroupAsymptotics.CFSGTrialityGeckOuterParameterChart
import SymmetricSubgroupAsymptotics.CFSGTrialityGeckFixedPositiveCardinality

/-! Each signed long root line has at least |K| centralizing elements
in the literal fixed positive group, where K is the cubic extension. -/
set_option autoImplicit false
set_option Elab.async false
set_option backward.isDefEq.respectTransparency false
noncomputable section
open scoped Classical
namespace SymmetricSubgroupAsymptotics.CFSGTrialityGeckShortCentralizerCardinality
open CFSGTrialityD4NormTwo CFSGTrialityGeckDiagramCovariance CFSGTrialityGeckShortSectionCentralizer
open CFSGTrialityGeckSectionHeightMembership CFSGTrialityGeckFixedRootSections
open CFSGTrialityGeckFixedRootWords CFSGTrialityGeckOuterParameterChart
open CFSGTrialityGeckFixedPositiveGeneration CFSGTrialityGeckSectionQuotientCoordinates
open CFSGTrialityGeckLongShortOrthogonality CFSGTrialityD4InvariantRoots
open CFSGSerreOrdinaryTwists CFSGTrialityGeckShortComplementFactor

local instance : DecidableEq (CFSGNormTwoRootPairing.Roots (CartanMatrix.D 4)) :=
  Classical.decEq _

theorem shortOrbit_injective (K : Type) [Field K] (sigma : K ≃+* K) :
    Function.Injective (shortOrbit K sigma false) := by
  intro t u he
  let a (v : K) : Fin 3 → Multiplicative K :=
    ![Multiplicative.ofAdd v, Multiplicative.ofAdd (sigma v),
      Multiplicative.ofAdd (sigma (sigma v))]
  have hp (v : K) : outerProductHom K (a v) = shortOrbit K sigma false v := by
    rw [outerProductHom_explicit]
    rfl
  have ha : a t = a u := outerProductHom_injective K
    ((hp t).trans (he.trans (hp u).symm))
  exact congrArg (fun b : Fin 3 → Multiplicative K => (b 0).toAdd) ha

theorem shortSection_injective (K : Type) [Field K] (sigma : K ≃+* K) (s : Fin 3) :
    Function.Injective (shortSection K sigma s false) := by
  intro t u he
  apply shortOrbit_injective K sigma
  exact (MulAut.conj (shortTransport K s)).injective he

def fixedPositiveInclusion (K : Type) [Field K] [Finite K] (sigma : K ≃+* K) :
    fixedPositive K sigma →* (Matrix GeckIndex GeckIndex K)ˣ :=
  (CFSGTrialityGeckPositiveTwist.Positive K).subtype.comp (fixedPositive K sigma).subtype

def longCentralizer (K : Type) [Field K] [Finite K] (sigma : K ≃+* K)
    (neg : Bool) (s : Fin 3) : Subgroup (fixedPositive K sigma) :=
  (Subgroup.centralizer {b : (Matrix GeckIndex GeckIndex K)ˣ | b ∈ RootLine K (signedLongRoot neg s)}).comap
    (fixedPositiveInclusion K sigma)

def shortFixedElement (K : Type) [Field K] [Finite K] (sigma : K ≃+* K)
    (horder : ∀ t, sigma (sigma (sigma t)) = t) (s : Fin 3) (t : K) :
    fixedPositive K sigma :=
  ⟨shortPositiveSection K sigma s (Multiplicative.ofAdd t),
    shortPositiveSection_fixed K sigma s (Multiplicative.ofAdd t) (horder t)⟩

theorem shortFixedElement_val (K : Type) [Field K] [Finite K] (sigma : K ≃+* K)
    (horder : ∀ t, sigma (sigma (sigma t)) = t) (s : Fin 3) (t : K) :
    fixedPositiveInclusion K sigma (shortFixedElement K sigma horder s t) =
      shortSection K sigma s false t :=
  shortPositiveSection_val K sigma s (Multiplicative.ofAdd t)

def centralizerParameter (K : Type) [Field K] [Finite K] (sigma : K ≃+* K)
    (horder : ∀ t, sigma (sigma (sigma t)) = t) (neg : Bool) (s : Fin 3) (t : K) :
    longCentralizer K sigma neg s := by
  refine ⟨shortFixedElement K sigma horder (centralizerShort s) t, ?_⟩
  change fixedPositiveInclusion K sigma
    (shortFixedElement K sigma horder (centralizerShort s) t) ∈
      Subgroup.centralizer {b : (Matrix GeckIndex GeckIndex K)ˣ |
        b ∈ RootLine K (signedLongRoot neg s)}
  rw [shortFixedElement_val]
  exact shortSection_mem_centralizer K sigma neg s t

theorem centralizerParameter_injective (K : Type) [Field K] [Finite K]
    (sigma : K ≃+* K) (horder : ∀ t, sigma (sigma (sigma t)) = t)
    (neg : Bool) (s : Fin 3) :
    Function.Injective (centralizerParameter K sigma horder neg s) := by
  intro t u he
  apply shortSection_injective K sigma (centralizerShort s)
  have h := congrArg (fun x : longCentralizer K sigma neg s =>
    fixedPositiveInclusion K sigma x.val) he
  change fixedPositiveInclusion K sigma
      (shortFixedElement K sigma horder (centralizerShort s) t) =
    fixedPositiveInclusion K sigma
      (shortFixedElement K sigma horder (centralizerShort s) u) at h
  simpa only [shortFixedElement_val] using h

theorem longCentralizer_card_lower (q : CFSG.PrimePower) (neg : Bool) (s : Fin 3) :
    q.order ^ 3 ≤ Nat.card (longCentralizer (q.Extension 3)
      (definingFieldAutomorphism q 3) neg s) := by
  have h := Nat.card_le_card_of_injective _
    (centralizerParameter_injective (q.Extension 3) (definingFieldAutomorphism q 3)
      (CFSGTrialityTripleFixedRoots.extension_three_pow_thrice q) neg s)
  simpa only [CFSGTrialityTripleFixedRoots.extension_three_card] using h

end SymmetricSubgroupAsymptotics.CFSGTrialityGeckShortCentralizerCardinality
