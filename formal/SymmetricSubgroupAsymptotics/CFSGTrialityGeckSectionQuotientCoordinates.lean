import SymmetricSubgroupAsymptotics.CFSGTrialityGeckFixedCoordinateParameters

/-! The displayed fixed sections realize the Frobenius-triple coordinates
in the actual height quotient.  The representatives below are literal
positive-group elements, with their matrix values identified explicitly. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
open scoped Classical
namespace SymmetricSubgroupAsymptotics.CFSGTrialityGeckSectionQuotientCoordinates
open CFSGTrialityGeckFixedCoordinateParameters CFSGTrialityGeckWordCoordinateTwist
open CFSGTrialityGeckWordRootIndex CFSGTrialityGeckWordHeightCoordinates
open CFSGTrialityGeckPositiveTwist CFSGTrialityGeckHeightQuotientTwist
open CFSGTrialityGeckFixedRootSections CFSGTrialityGeckSectionHeightMembership
open CFSGTrialityGeckSectionAdditiveParameters CFSGTrialityGeckMatrixTwist
open CFSGNormTwoCoordinateRootHeightFiltration CFSGTrialityD4NormTwo

local instance sectionTailNormal (K : Type) [Field K] (h : ℤ) :
    (TailInPositive K h).Normal :=
  heightTail_normal_in_positive (CartanMatrix.D 4) (CartanMatrix.D_diag 4)
    (CartanMatrix.D_transpose 4) D4_positive_definite (CartanMatrix.D_off_diag_nonpos 4) K h

def shortPositiveSection (K : Type) [Field K] [Finite K] (σ : K ≃+* K)
    (s : Fin 3) (t : Multiplicative K) : Positive K :=
  wordPositiveParameterHom K (Sum.inr (s,0)) t *
    wordPositiveParameterHom K (Sum.inr (s,1)) (fieldParameterAut K σ t) *
    wordPositiveParameterHom K (Sum.inr (s,2))
      (fieldParameterAut K σ (fieldParameterAut K σ t))

theorem shortPositiveSection_val (K : Type) [Field K] [Finite K] (σ : K ≃+* K)
    (s : Fin 3) (t : Multiplicative K) :
    (shortPositiveSection K σ s t).val = shortSection K σ s false t.toAdd := by
  change shortFactor K s 0 t.toAdd * shortFactor K s 1 (σ t.toAdd) *
    shortFactor K s 2 (σ (σ t.toAdd)) = shortSection K σ s false t.toAdd
  dsimp only [shortSection, CFSGTrialityGeckFixedRootWords.shortOrbit, shortFactor]
  group <;> rfl

theorem shortPositiveSection_fixed (K : Type) [Field K] [Finite K] (σ : K ≃+* K)
    (s : Fin 3) (t : Multiplicative K) (ht : σ (σ (σ t.toAdd)) = t.toAdd) :
    positiveTwist K σ (shortPositiveSection K σ s t) = shortPositiveSection K σ s t := by
  apply Subtype.ext
  rw [positiveTwist_val, shortPositiveSection_val]
  exact shortSection_fixed K σ s false t.toAdd ht

theorem shortPositiveSection_mem_tail (K : Type) [Field K] [Finite K] (σ : K ≃+* K)
    (s : Fin 3) (t : Multiplicative K) :
    shortPositiveSection K σ s t ∈ TailInPositive K (![(1 : ℤ),2,3] s) := by
  change (shortPositiveSection K σ s t).val ∈
    CFSGTrialityGeckHeightTwist.HeightTail K (![(1 : ℤ),2,3] s)
  rw [shortPositiveSection_val]
  exact shortSection_mem_heightTail K σ s t.toAdd

def shortSectionCoordinates (K : Type) [Field K] (σ : K ≃+* K)
    (s : Fin 3) {h : ℤ} (hs : ![(1 : ℤ),2,3] s = h) (t : Multiplicative K) :
    WordHeightIndex h → Multiplicative K :=
  Pi.mulSingle (shortHeightIndex s 0 hs) t *
    Pi.mulSingle (shortHeightIndex s 1 hs) (fieldParameterAut K σ t) *
    Pi.mulSingle (shortHeightIndex s 2 hs)
      (fieldParameterAut K σ (fieldParameterAut K σ t))

theorem shortSectionCoordinates_image (K : Type) [Field K] [Finite K] (σ : K ≃+* K)
    (s : Fin 3) {h : ℤ} (hh : 0 < h) (hs : ![(1 : ℤ),2,3] s = h)
    (t : Multiplicative K) :
    (wordHeightLayerEquiv K h hh (shortSectionCoordinates K σ s hs t)).val =
      QuotientGroup.mk' (TailInPositive K (h + 1)) (shortPositiveSection K σ s t) := by
  simp only [shortSectionCoordinates, shortPositiveSection, map_mul, Subgroup.coe_mul,
    wordHeightLayerEquiv_mulSingle]
  rfl

def longPositiveSection (K : Type) [Field K] [Finite K]
    (s : Fin 3) (t : Multiplicative K) : Positive K :=
  wordPositiveParameterHom K (Sum.inl s) t

theorem longPositiveSection_val (K : Type) [Field K] [Finite K]
    (s : Fin 3) (t : Multiplicative K) :
    (longPositiveSection K s t).val = longSection K s false t.toAdd := rfl

theorem longPositiveSection_fixed (K : Type) [Field K] [Finite K] (σ : K ≃+* K)
    (s : Fin 3) (t : Multiplicative K) (ht : σ t.toAdd = t.toAdd) :
    positiveTwist K σ (longPositiveSection K s t) = longPositiveSection K s t := by
  apply Subtype.ext
  rw [positiveTwist_val, longPositiveSection_val]
  exact longSection_fixed K σ s false t.toAdd ht

theorem longPositiveSection_mem_tail (K : Type) [Field K] [Finite K]
    (s : Fin 3) (t : Multiplicative K) :
    longPositiveSection K s t ∈ TailInPositive K (![(1 : ℤ),4,5] s) :=
  longSection_mem_heightTail K s t.toAdd

theorem longSectionCoordinates_image (K : Type) [Field K] [Finite K]
    (s : Fin 3) {h : ℤ} (hh : 0 < h) (hs : ![(1 : ℤ),4,5] s = h)
    (t : Multiplicative K) :
    (wordHeightLayerEquiv K h hh (Pi.mulSingle (longHeightIndex s hs) t)).val =
      QuotientGroup.mk' (TailInPositive K (h + 1)) (longPositiveSection K s t) :=
  wordHeightLayerEquiv_mulSingle K h hh (longHeightIndex s hs) t

end SymmetricSubgroupAsymptotics.CFSGTrialityGeckSectionQuotientCoordinates
