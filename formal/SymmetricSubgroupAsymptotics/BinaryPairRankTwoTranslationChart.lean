import SymmetricSubgroupAsymptotics.BinaryAdditiveTwoOrbitChart
import SymmetricSubgroupAsymptotics.BinaryPairTranslationTwistCenter
import SymmetricSubgroupAsymptotics.PermutationBinaryTwoOrbitKernel

/-! Instantiation of the additive twist chart on the original residual.

The original pair-module theorem supplies the exact lower block
constants. The original orbit-image theorem supplies the actual V4
coordinates, and the top-order branch supplies the strict size needed
to exclude central orbit swaps. No chart equation, original normal
containment, or character criterion is an input.
-/
set_option autoImplicit false
noncomputable section
open scoped Classical

namespace SymmetricSubgroupAsymptotics.BinaryPairFrame

variable {X I : Type} {U : Subgroup (Equiv.Perm X)}
    (F : BinaryPairFrame U I) (N : Subgroup U) [N.Normal]
    [Finite X] [Finite I] [MulAction.IsPretransitive F.top.range I]
    (hU : IsPGroup 2 U) (hI : Nat.card I=8)
    (hres : F.EightPairRankTwoResidual N)

include hU hI hres in
/-- The literal ambient image of N∩K is the actual H-fixed function
space. This is not an assertion that the whole N lies in K. -/
theorem rankTwo_normalSpace_eq_fixed :
    (F.normalSpace N).map F.kernelSpace.subtype=
      (permutationFunctionRepresentation (ZMod 2) (F.sectionTopRepresentation N).ker I).invariants := by
  rcases hres with ⟨hd,_,_,⟨data⟩,_,_,_⟩
  have hnonempty : Nonempty I := (Nat.card_pos_iff.mp (by rw [hI]; decide)).1
  let i : I := Classical.choice hnonempty
  have he := (permutationBinary_twoBlockCharacter_original_kernel_eq
    (F.top_isPGroup hU) i hI (F.sectionTopRepresentation N)
    F.kernelTopPermutationSubrepresentation (F.sectionTopIntertwiner N)
    (F.normalSpace N).mkQ_surjective hd data).1
  change (F.normalSpace N).mkQ.ker.map F.kernelSpace.subtype=_ at he
  rw [Submodule.ker_mkQ] at he
  exact he

/-- Every field of this chart is constructed from the actual residual.
The top-order-eight case is handled separately by the checked original
target-order bound. -/
def rankTwoTranslationChart (hlarge : 8<Nat.card F.top.range) :
    BinaryAdditiveTwoOrbitChart (X := I) (F.sectionTopRepresentation N).ker := Classical.choice (by
  rcases hres with ⟨hd,_,_,⟨data⟩,hclasses,_,_⟩
  have hnonempty : Nonempty I := (Nat.card_pos_iff.mp (by rw [hI]; decide)).1
  let i : I := Classical.choice hnonempty
  obtain ⟨o₁,o₂,hne,hcover,_,_⟩ :=
    permutationBinary_twoBlockCharacter_original_module_eq
      (F.top_isPGroup hU) i hI (F.sectionTopRepresentation N)
      F.kernelTopPermutationSubrepresentation (F.sectionTopIntertwiner N)
      (F.normalSpace N).mkQ_surjective hd data
  let x₀ : o₁.orbit := ⟨o₁.nonempty_orbit.choose,o₁.nonempty_orbit.choose_spec⟩
  obtain ⟨hcard,hsquare,hregular⟩ :=
    permutationBinary_twoBlockCharacter_regular_orbit_images
      (F.top_isPGroup hU) i hI (F.sectionTopRepresentation N)
      F.kernelTopPermutationSubrepresentation (F.sectionTopIntertwiner N)
      (F.normalSpace N).mkQ_surjective hd data o₁
  have hHlarge : 4<Nat.card (F.sectionTopRepresentation N).ker := by
    have hc := (F.sectionTopRepresentation N).ker.card_mul_index
    rw [data.kernel_index] at hc
    omega
  exact ⟨BinaryAdditiveTwoOrbitChart.ofRegularOrbits
    (F.sectionTopRepresentation N).ker o₁ o₂ x₀ (hregular x₀) hne hcover
    data.kernel_index hclasses hcard hsquare hHlarge⟩)

variable (hlarge : 8<Nat.card F.top.range)

/-- First parity of actual original lifts, in the constructed reversible
additive point chart. The chosen lift is the original affine top lift. -/
def rankTwoTranslationParity (h : (F.sectionTopRepresentation N).ker) : ZMod 2 :=
  BinaryTranslationMoments.parity (BinaryTranslationMoments.leftFunction
    (F.rankTwoTranslationChart N hU hI hres hlarge).chart
    (F.affineTranslation (F.affineTopLift h)))

/-- The lower-module hypothesis of the twist argument is proved from
the literal original N∩K image and the actual original orbit action. -/
theorem rankTwoTranslationChart_lower
    (f : I → ZMod 2) (hf : f∈(F.normalSpace N).map F.kernelSpace.subtype)
    (v : BinaryRegularFourSpace) :
    f ((F.rankTwoTranslationChart N hU hI hres hlarge).chart (Sum.inl v))=
      f ((F.rankTwoTranslationChart N hU hI hres hlarge).chart (Sum.inl 0)) := by
  apply (F.rankTwoTranslationChart N hU hI hres hlarge).fixed_left f
  rw [← F.rankTwo_normalSpace_eq_fixed N hU hI hres]
  exact hf

/-- The nonzero-parity branch now has no supplied chart equations: the
original residual constructs every action and denominator input. The
whole original normal is recovered only at the end. -/
theorem rankTwo_nonzero_parity_normal_eq
    (hparity : ∃ h,F.rankTwoTranslationParity N hU hI hres hlarge h≠0) :
    N=N⊓F.top.ker := by
  let C := F.rankTwoTranslationChart N hU hI hres hlarge
  exact F.original_normal_eq_intersection_of_nonzero_translation_parity N
    (F.sectionTopRepresentation N).ker C.chart C.coordinate C.coordinate_surjective
    (by norm_num [BinaryRegularFourSpace,Nat.card_prod,Nat.card_zmod])
    C.normal_left C.central_diagonal
    (F.rankTwoTranslationChart_lower N hU hI hres hlarge) hparity hU

/-- On the same actual intermediate quotient, the center exclusion is
also available independently of the normal-center detection step. -/
theorem rankTwo_nonzero_parity_center_mem_kernel
    (hparity : ∃ h,F.rankTwoTranslationParity N hU hI hres hlarge h≠0)
    (u : U)
    (hu : QuotientGroup.mk' (N⊓F.top.ker) u∈
      Subgroup.center (U ⧸ (N⊓F.top.ker))) : u∈F.top.ker := by
  let C := F.rankTwoTranslationChart N hU hI hres hlarge
  exact F.central_intersection_quotient_mem_top_kernel N
    (F.sectionTopRepresentation N).ker C.chart C.coordinate C.coordinate_surjective
    (by norm_num [BinaryRegularFourSpace,Nat.card_prod,Nat.card_zmod])
    C.normal_left C.central_diagonal
    (F.rankTwoTranslationChart_lower N hU hI hres hlarge) hparity u hu

end SymmetricSubgroupAsymptotics.BinaryPairFrame
