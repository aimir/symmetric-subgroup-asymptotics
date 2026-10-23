import SymmetricSubgroupAsymptotics.CFSGReeGTwoPositiveDerivedKernel
import Mathlib.GroupTheory.QuotientGroup.Basic

/-! Concrete characteristic field layers and their mixed commutator.
The first quotient is the actual a-coordinate and the derived/centre
quotient is the actual c-coordinate. No automorphism of U3 is lifted
to an ambient group. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
namespace SymmetricSubgroupAsymptotics.CFSGReeGTwoPositiveCharacteristicLayers
open CFSGReeGTwoFieldParameters CFSGReeGTwoOriginalPositiveSubgroup
open CFSGReeGTwoPositiveCoordinates CFSGReeGTwoPositiveCentre
open CFSGReeGTwoPositiveFirstQuotient CFSGReeGTwoPositiveDerivedKernel
open scoped commutatorElement

local instance reeLayersFirstKernelNormal (m : ℕ) : (firstKernel m).Normal := by
  change (firstHom m).ker.Normal
  infer_instance

theorem mem_center_iff_coordinates (m : ℕ) (u : fixedPositiveGroup m) :
    u∈Subgroup.center (fixedPositiveGroup m) ↔ coordinates m u 0=0 ∧ coordinates m u 1=0 := by
  obtain ⟨x,rfl⟩ := fixedPositiveChart_surjective m u
  simpa only [coordinates_chart] using chart_mem_center_iff m x

def centerInFirst (m : ℕ) : Subgroup (firstKernel m) :=
  (Subgroup.center (fixedPositiveGroup m)).subgroupOf (firstKernel m)

local instance reeLayersCenterInFirstNormal (m : ℕ) : (centerInFirst m).Normal := by
  unfold centerInFirst
  infer_instance

theorem middleKer_eq_centerInFirst (m : ℕ) : (middleHom m).ker=centerInFirst m := by
  ext u
  have hu0 := (mem_firstKernel_iff m u.val).mp u.property
  change coordinates m u.val 1=0 ↔ u.val∈Subgroup.center (fixedPositiveGroup m)
  rw [mem_center_iff_coordinates]
  exact ⟨fun h => ⟨hu0,h⟩,fun h => h.2⟩

def firstQuotientEquiv (m : ℕ) :
    (fixedPositiveGroup m ⧸ firstKernel m) ≃* Multiplicative (Field m) :=
  QuotientGroup.quotientKerEquivOfSurjective (firstHom m) (firstHom_surjective m)

theorem firstQuotientEquiv_mk (m : ℕ) (u : fixedPositiveGroup m) :
    firstQuotientEquiv m (QuotientGroup.mk u)=Multiplicative.ofAdd (coordinates m u 0) := rfl

def abelianizationEquiv (m : ℕ) (hm : 1≤m) :
    (fixedPositiveGroup m ⧸ commutator (fixedPositiveGroup m)) ≃* Multiplicative (Field m) :=
  (QuotientGroup.quotientMulEquivOfEq (commutator_eq_firstKernel m hm)).trans (firstQuotientEquiv m)

theorem abelianizationEquiv_mk (m : ℕ) (hm : 1≤m) (u : fixedPositiveGroup m) :
    abelianizationEquiv m hm (QuotientGroup.mk u)=Multiplicative.ofAdd (coordinates m u 0) := rfl

def middleQuotientEquiv (m : ℕ) :
    (firstKernel m ⧸ centerInFirst m) ≃* Multiplicative (Field m) :=
  (QuotientGroup.quotientMulEquivOfEq (middleKer_eq_centerInFirst m).symm).trans
    (QuotientGroup.quotientKerEquivOfSurjective (middleHom m) (middleHom_surjective m))

theorem middleQuotientEquiv_mk (m : ℕ) (u : firstKernel m) :
    middleQuotientEquiv m (QuotientGroup.mk u)=Multiplicative.ofAdd (coordinates m u.val 1) := rfl

theorem chart_mixed_commutator (m : ℕ) (x y : Fin 3 → Field m) (hx : x 0=0) :
    ⁅fixedPositiveChart m x,fixedPositiveChart m y⁆=
      centralHom m (Multiplicative.ofAdd (-y 0*x 1)) := by
  have he : fixedPositiveChart m x*fixedPositiveChart m y=
      centralHom m (Multiplicative.ofAdd (-y 0*x 1))*(fixedPositiveChart m y*fixedPositiveChart m x) := by
    change fixedPositiveChart m x*fixedPositiveChart m y=
      fixedPositiveChart m ![0,0,-y 0*x 1]*(fixedPositiveChart m y*fixedPositiveChart m x)
    rw [chart_mul,chart_mul,chart_mul]
    apply congrArg (fixedPositiveChart m)
    funext i
    fin_cases i <;> simp [productCoordinates,hx] <;> ring
  rw [commutatorElement_def,he]
  group

theorem derived_mixed_commutator (m : ℕ) (u v : fixedPositiveGroup m)
    (hu : u∈commutator (fixedPositiveGroup m)) :
    ⁅u,v⁆=centralHom m (Multiplicative.ofAdd (-coordinates m v 0*coordinates m u 1)) := by
  obtain ⟨x,rfl⟩ := fixedPositiveChart_surjective m u
  obtain ⟨y,rfl⟩ := fixedPositiveChart_surjective m v
  have hx := (chart_mem_firstKernel_iff m x).mp (commutator_le_firstKernel m hu)
  simpa only [coordinates_chart] using chart_mixed_commutator m x y hx

end SymmetricSubgroupAsymptotics.CFSGReeGTwoPositiveCharacteristicLayers
