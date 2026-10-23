import SymmetricSubgroupAsymptotics.CFSGTrialityGeckHeightCoordinateAction

/-! Fixed classes in the actual height quotient have the literal
one-parameter Frobenius triples.  These equations use the checked action
on the word-root chart, including the cyclic reindexing of its top layer. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
open scoped Classical
namespace SymmetricSubgroupAsymptotics.CFSGTrialityGeckFixedCoordinateParameters
open CFSGTrialityGeckWordCoordinateTwist CFSGTrialityGeckWordRootIndex
open CFSGTrialityGeckHeightCoordinateAction CFSGTrialityGeckSectionRootLabels
open CFSGTrialityD4PositiveRootOrbits CFSGTrialityD4PositiveRootIndex CFSGIntegerHeightSign

def longHeightIndex (s : Fin 3) {h : ℤ} (hs : ![(1 : ℤ),4,5] s = h) :
    WordHeightIndex h :=
  ⟨Sum.inl s, (long_height s).trans hs⟩

def shortHeightIndex (s k : Fin 3) {h : ℤ} (hs : ![(1 : ℤ),2,3] s = h) :
    WordHeightIndex h :=
  ⟨Sum.inr (s,k), (short_label_height s k).trans hs⟩

theorem heightCycle_long (s : Fin 3) {h : ℤ} (hs : ![(1 : ℤ),4,5] s = h) :
    heightCycle h (longHeightIndex s hs) = longHeightIndex s hs := by
  apply Subtype.ext
  rfl

theorem heightCycle_short (s k : Fin 3) {h : ℤ} (hs : ![(1 : ℤ),2,3] s = h) :
    heightCycle h (shortHeightIndex s k hs) = shortHeightIndex s (cycle k) hs := by
  apply Subtype.ext
  rfl

theorem fixed_coordinate_step (K : Type) [Field K] (σ : K ≃+* K) (h : ℤ)
    (c : WordHeightIndex h → Multiplicative K) (hc : coordinateTwist K σ h c = c)
    (j : WordHeightIndex h) :
    c (heightCycle h j) = fieldParameterAut K σ (c j) := by
  have he := congrFun hc (heightCycle h j)
  change fieldParameterAut K σ (c ((heightCycle h).symm (heightCycle h j))) =
    c (heightCycle h j) at he
  rw [Equiv.symm_apply_apply] at he
  exact he.symm

theorem fixed_long_parameter (K : Type) [Field K] (σ : K ≃+* K) (h : ℤ)
    (c : WordHeightIndex h → Multiplicative K) (hc : coordinateTwist K σ h c = c)
    (s : Fin 3) (hs : ![(1 : ℤ),4,5] s = h) :
    σ (c (longHeightIndex s hs)).toAdd = (c (longHeightIndex s hs)).toAdd := by
  have he := fixed_coordinate_step K σ h c hc (longHeightIndex s hs)
  rw [heightCycle_long] at he
  exact (congrArg Multiplicative.toAdd he).symm

theorem fixed_short_parameter_step (K : Type) [Field K] (σ : K ≃+* K) (h : ℤ)
    (c : WordHeightIndex h → Multiplicative K) (hc : coordinateTwist K σ h c = c)
    (s k : Fin 3) (hs : ![(1 : ℤ),2,3] s = h) :
    (c (shortHeightIndex s (cycle k) hs)).toAdd =
      σ (c (shortHeightIndex s k hs)).toAdd := by
  have he := fixed_coordinate_step K σ h c hc (shortHeightIndex s k hs)
  rw [heightCycle_short] at he
  exact congrArg Multiplicative.toAdd he

theorem fixed_short_parameters (K : Type) [Field K] (σ : K ≃+* K) (h : ℤ)
    (c : WordHeightIndex h → Multiplicative K) (hc : coordinateTwist K σ h c = c)
    (s : Fin 3) (hs : ![(1 : ℤ),2,3] s = h) (k : Fin 3) :
    (c (shortHeightIndex s k hs)).toAdd =
      ![(c (shortHeightIndex s 0 hs)).toAdd,
        σ (c (shortHeightIndex s 0 hs)).toAdd,
        σ (σ (c (shortHeightIndex s 0 hs)).toAdd)] k := by
  have h0 := fixed_short_parameter_step K σ h c hc s 0 hs
  have h1 := fixed_short_parameter_step K σ h c hc s 1 hs
  change (c (shortHeightIndex s 1 hs)).toAdd =
    σ (c (shortHeightIndex s 0 hs)).toAdd at h0
  change (c (shortHeightIndex s 2 hs)).toAdd =
    σ (c (shortHeightIndex s 1 hs)).toAdd at h1
  fin_cases k
  · rfl
  · exact h0
  · exact h1.trans (congrArg σ h0)

theorem fixed_short_parameter_thrice (K : Type) [Field K] (σ : K ≃+* K) (h : ℤ)
    (c : WordHeightIndex h → Multiplicative K) (hc : coordinateTwist K σ h c = c)
    (s : Fin 3) (hs : ![(1 : ℤ),2,3] s = h) :
    σ (σ (σ (c (shortHeightIndex s 0 hs)).toAdd)) =
      (c (shortHeightIndex s 0 hs)).toAdd := by
  have he := fixed_short_parameter_step K σ h c hc s 2 hs
  change (c (shortHeightIndex s 0 hs)).toAdd =
    σ (c (shortHeightIndex s 2 hs)).toAdd at he
  rw [fixed_short_parameters K σ h c hc s hs 2] at he
  exact he.symm

end SymmetricSubgroupAsymptotics.CFSGTrialityGeckFixedCoordinateParameters
