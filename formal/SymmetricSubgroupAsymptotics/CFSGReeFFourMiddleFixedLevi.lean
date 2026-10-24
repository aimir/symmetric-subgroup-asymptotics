import SymmetricSubgroupAsymptotics.CFSGReeFFourMiddleRootSections
import SymmetricSubgroupAsymptotics.CFSGReeFFourMiddlePositivePreserving
import SymmetricSubgroupAsymptotics.CFSGE6GeckFixedLeviSections
import SymmetricSubgroupAsymptotics.CFSGNormTwoCoordinateFunctionalRootTail
import SymmetricSubgroupAsymptotics.CFSGTwistedE6GeckRootSubgroupTwist

/-! Actual diagram-fixed elements preserving the middle functional
blocks have four original middle parameters. Strict-root normality and
the six genuine sections discharge every hypothesis of the shared
fixed-Levi lemma; no fixed-point coverage is assumed. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
open scoped Classical
namespace SymmetricSubgroupAsymptotics.CFSGReeFFourMiddleFixedLevi
open CFSGReeFFourMiddleRootSections CFSGReeFFourMiddlePositivePreserving
open CFSGReeFFourMiddlePositiveSubgroup CFSGReeFFourFieldParameters
open CFSGE6GeckFixedLeviSections CFSGE6GeckMiddleRootSupport
open CFSGTwistedE6GeckPositiveTwist CFSGTwistedE6GeckMatrixTwist
open CFSGTwistedE6GeckPositiveCoordinateLifts CFSGTwistedE6GeckSectionRootParameters
open CFSGTwistedE6GeckOriginalRootSections CFSGTwistedE6WeylChamber
open CFSGTwistedE6GeckDiagramCovariance CFSGTwistedE6GeckRootSubgroupTwist
open CFSGTwistedE6DiagramRootOrthogonality CFSGNormTwoCoordinateFunctionalRootTail
open CFSGNormTwoCoordinateRootSubgroup CFSGNormTwoCoordinateRootElementRange
open CFSGExceptionalNormTwoBases CFSGExceptionalCartanPositiveDefinite CFSGNormTwoRootPairing
open CFSGGradedMatrixSubgroups CFSGSerreDiagram
local notation "A" => CartanMatrix.E₆
local notation "hd" => CartanMatrix.E₆_diag
local notation "hs" => CartanMatrix.E₆_transpose
local notation "hp" => E6_positive_definite
local notation "ho" => CartanMatrix.E₆_off_diag_nonpos
local instance : DecidableEq (Roots A) := Classical.decEq _

private abbrev outsideTail (K : Type) [Field K] :=
  functionalTail A hd hs hp ho K outsideHeight 1
private abbrev outsideTailPositive (K : Type) [Field K] :=
  (outsideTail K).comap (Positive K).subtype

private theorem outsideHeight_diagram (k : Roots A) :
    outsideHeight (diagramRoot k).val = outsideHeight k.val := by
  rw [outsideHeight_apply,outsideHeight_apply,diagramRoot_coordinate,
    diagramRoot_coordinate,diagramRoot_coordinate]
  change k.val 5 + k.val 1 + k.val 0 = k.val 0 + k.val 1 + k.val 5
  omega

private theorem section_mem_tail (K : Type) [Field K] (k : PositiveRoot)
    (hk : outsideHeight k.val.val ≠ 0) (x : RootLine K k.val) :
    rootLinePositive K k x ∈ outsideTailPositive K := by
  have hn := outsideHeight_nonnegative k
  have hf : 1 ≤ outsideHeight k.val.val := by omega
  obtain ⟨a,ha⟩ := (mem_rootSubgroup_iff_selected A hd hs hp ho K k.val x.val).mp x.property
  change x.val ∈ outsideTail K
  rw [←ha]
  exact root_mem_functionalTail A hd hs hp ho K outsideHeight 1 k.val k.property hf a

private theorem mem_middle_of_raw (m : ℕ) (u : Positive (Field m))
    (hu : u.val ∈ (middlePositiveSubgroup m).map (Positive (Field m)).subtype) :
    u ∈ middlePositiveSubgroup m := by
  obtain ⟨v,hv,he⟩ := hu
  have h : v=u := Subtype.ext he
  exact h ▸ hv

theorem fixed_preserving_mem_middle (m : ℕ) (u : Positive (Field m))
    (hu : positiveTwist (Field m) (RingEquiv.refl (Field m)) u = u)
    (hpres : u.val ∈ preservingUnits middleWeight) : u ∈ middlePositiveSubgroup m := by
  have hMN : middlePositiveSubgroup m ≤
      Subgroup.normalizer (outsideTailPositive (Field m) : Set (Positive (Field m))) := by
    apply Subgroup.le_set_normalizer_iff.mpr
    intro v hv n hn
    have hvn := positive_le_normalizer_functionalTail A hd hs hp ho (Field m) outsideHeight 1
      outsideHeight_nonnegative v.property
    change v.val * n.val * v.val⁻¹ ∈ outsideTail (Field m)
    exact (Subgroup.mem_normalizer_iff.mp hvn n.val).mp hn
  have hN : (outsideTailPositive (Field m)).map (Positive (Field m)).subtype ≤
      strictUnits middleWeight := by
    rintro g ⟨v,hv,rfl⟩
    exact functionalTail_le_strict A hd hs hp ho (Field m) outsideHeight 1 (by decide) hv
  apply fixed_mem_right_of_sections (Field m) (outsideTailPositive (Field m))
    (middlePositiveSubgroup m) middleWeight hMN hN
    (middlePositiveSubgroup_le_preserving m) _ _ u hu hpres
  · intro k hk x hx
    by_cases hz : outsideHeight k.val.val = 0
    · exact Subgroup.mem_sup_right (mem_middle_of_raw m _ (singleton_section_mem m k hz hk x))
    · exact Subgroup.mem_sup_left (section_mem_tail (Field m) k hz x)
  · intro k hk x
    by_cases hz : outsideHeight k.val.val = 0
    · exact Subgroup.mem_sup_right (mem_middle_of_raw m _ (paired_section_mem m k hz hk x))
    · have ht : unitTwist (Field m) (RingEquiv.refl (Field m)) x.val ∈
          RootLine (Field m) (diagramRoot k.val) := by
        have h : unitTwist (Field m) (RingEquiv.refl (Field m)) x.val ∈
            (RootLine (Field m) k.val).map
              (unitTwist (Field m) (RingEquiv.refl (Field m))).toMonoidHom :=
          ⟨x.val,x.property,rfl⟩
        rw [root_subgroup_twist] at h
        exact h
      let kp : PositiveRoot := ⟨diagramRoot k.val,fun i => by
        rw [diagramRoot_coordinate]
        exact k.property _⟩
      let y : RootLine (Field m) kp.val :=
        ⟨unitTwist (Field m) (RingEquiv.refl (Field m)) x.val,ht⟩
      have hkp : outsideHeight kp.val.val ≠ 0 := by
        change outsideHeight (diagramRoot k.val).val ≠ 0
        rwa [outsideHeight_diagram]
      have hy := section_mem_tail (Field m) kp hkp y
      have he : rootLinePositive (Field m) kp y =
          positiveTwist (Field m) (RingEquiv.refl (Field m)) (rootLinePositive (Field m) k x) :=
        Subtype.ext rfl
      rw [he] at hy
      exact Subgroup.mem_sup_left ((outsideTailPositive (Field m)).mul_mem
        (section_mem_tail (Field m) k hz x) hy)

end SymmetricSubgroupAsymptotics.CFSGReeFFourMiddleFixedLevi
