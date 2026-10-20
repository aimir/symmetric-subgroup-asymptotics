import SymmetricSubgroupAsymptotics.PrimitiveAffineDegreeThreeFourBlockTwoSignSectionPairKernelAction

/-!
# Faithfulness of the literal pair kernel on every proper two-sign section

Each nontrivial pair-kernel element changes one of the two literal sign
components.  Triviality on a section would force the whole changed component
into the normal-space intersection.  The componentwise codimension-one
theorem rules this out.
-/

set_option autoImplicit false
noncomputable section
open scoped Classical

namespace SymmetricSubgroupAsymptotics
namespace Non2UnipotentPrefixFiniteMenu
namespace PrimitiveAffineImprimitiveBlockTransfer

open DiagonalInvariantSubmodules
open DiagonalIsotypeProjection
open OddMarkerTernaryChart

variable {w : ℕ} {U : PreE7NonPairActionClass w}
  {basePoint : Fin w}
  (block : OriginalMinimalBlock
    (A := preE7NonPairAction w U) basePoint)
  (P : PrimitiveAffineProfile block.Component block.Fibre)
  [Nontrivial block.Fibre]

local instance primitiveAffineDegreeThreeFourBlockTwoSignSectionPairKernelFaithful_localInstance1 : Fact P.p.Prime := (chart block P).primeFact

/-- A nontrivial literal pair-kernel element changes at least one of the two
actual scalar isotypes. -/
theorem degreeThreeFourBlockTwoSign_exists_isotype_ne_one
    (hr : Nat.card block.Fibre = 3)
    (hs : Nat.card block.Points = 4)
    (hcomponent : Nat.card block.Component = 6)
    (k : (degreeThreeFourBlockPairChart
      block P hr hs hcomponent).frame.top.ker)
    (hk : k ≠ 1) :
    ∃ a : Label (degreeThreeFourBlockTranslationScalar
        block P hr hs hcomponent),
      a.1 k ≠ 1 := by
  let C := degreeThreeFourBlockPairChart block P hr hs hcomponent
  let scalar := degreeThreeFourBlockTranslationScalar
    block P hr hs hcomponent
  by_contra h
  push Not at h
  have hbit : ∀ i : Fin 4, C.frame.bits k i = 0 := by
    intro i
    have hi := h (coordinateLabel scalar i)
    change degreeThreeFourBlockTranslationScalar
      block P hr hs hcomponent i k = 1 at hi
    have hi' := congrArg (degreeThreeScalarFieldEquiv block P hr) hi
    have hsign : signScalar
        (Multiplicative.ofAdd (C.frame.bits k i)) = 1 := by
      simpa only [degreeThreeFourBlockTranslationScalar,
        RingEquiv.apply_symm_apply, map_one, scalar, C] using hi'
    have hmul : Multiplicative.ofAdd (C.frame.bits k i) = 1 := by
      apply signScalar_injective
      simpa only [signScalar_one] using hsign
    simpa using congrArg Multiplicative.toAdd hmul
  apply hk
  apply C.frame.bitsHom_injective
  rw [map_one]
  apply congrArg Multiplicative.ofAdd
  funext i
  exact hbit i

/-- Scalarization carries a trivial section action to inclusion of every
changed ambient isotype in the corresponding normal-space isotype. -/
private theorem degreeThreeFourBlockTwoSignSection_encode_le_of_action_eq_one
    (hr : Nat.card block.Fibre = 3)
    (hs : Nat.card block.Points = 4)
    (hcomponent : Nat.card block.Component = 6)
    (N : TwoSignProperAxis (E block P))
    (k : (degreeThreeFourBlockPairChart
      block P hr hs hcomponent).frame.top.ker)
    (hk : degreeThreeFourBlockTwoSignSectionPairKernelRepresentation
      block P hr hs hcomponent N k = 1)
    (a : Label (degreeThreeFourBlockTranslationScalar
      block P hr hs hcomponent))
    (ha : a.1 k ≠ 1) :
    encode (degreeThreeFourBlockTranslationScalar
          block P hr hs hcomponent)
        (DegreeThreeFourBlockTwoSignAmbientScalarizedStable
          block P hr hs hcomponent) a ≤
      encode (degreeThreeFourBlockTranslationScalar
          block P hr hs hcomponent)
        (DegreeThreeFourBlockTwoSignSectionNormalScalarizedStable
          block P hr hs hcomponent N) a := by
  let scalar := degreeThreeFourBlockTranslationScalar
    block P hr hs hcomponent
  let A := degreeThreeFourBlockSignedTranslationCompatibility
    block P hr hs hcomponent
  let K := DegreeThreeFourBlockSignedTranslationCompatibility.stable
    (block := block) (P := P) A
  let e := degreeThreeFourBlockLocalScalarEquiv block P hr
  let E := pointwiseScalarEquiv (ι := Fin 4) e
  let KA := scalarizedStable scalar K e
  let W := degreeThreeFourBlockTwoSignSectionNormalSubrepresentation block P N
  let L := degreeThreeFourBlockReindexedSubrepresentationStable
    block P hr hs hcomponent W
  let KL := scalarizedStable scalar L e
  intro z hz
  let y : KA.1 := ⟨extension scalar a z, hz⟩
  rcases y.2 with ⟨x₀, hx₀, hxy⟩
  let x : degreeThreeFourBlockReindexedTranslationSubmodule block P hs :=
    ⟨x₀, hx₀⟩
  have hdisp :=
    degreeThreeFourBlockTwoSignSectionPairKernel_displacement_mem
      block P hr hs hcomponent N k hk x
  have hscalarDisp :
      diagonalOperator scalar k y.1 - y.1 ∈ KL.1 := by
    refine ⟨diagonalModuleOperator scalar k x.1 - x.1, hdisp, ?_⟩
    funext i
    have hxyi := congrFun hxy i
    change e (scalar i k • x.1 i - x.1 i) =
      scalar i k * y.1 i - y.1 i
    rw [map_sub, map_smul]
    change scalar i k * e (x.1 i) - e (x.1 i) = _
    have hxyi' : e (x.1 i) = y.1 i := by
      simpa only [E, pointwiseScalarEquiv_apply, x] using hxyi
    rw [hxyi']
  have hsupport : diagonalOperator scalar k y.1 - y.1 =
      (a.1 k - 1) • y.1 := by
    funext i
    by_cases hi : scalar i = a.1
    · change scalar i k * y.1 i - y.1 i =
        (a.1 k - 1) * y.1 i
      rw [hi, sub_mul, one_mul]
    · have hyi : y.1 i = 0 := by
        have hz0 : extension scalar a z i = 0 := by
          simp [DiagonalInvariantSubmodules.extension, hi]
        simpa only [y] using hz0
      change scalar i k * y.1 i - y.1 i =
        (a.1 k - 1) * y.1 i
      rw [hyi]
      simp
  have hc : a.1 k - 1 ≠ 0 := sub_ne_zero.mpr ha
  have hyKL : y.1 ∈ KL.1 := by
    have hscaled := KL.1.smul_mem (a.1 k - 1)⁻¹ hscalarDisp
    rw [hsupport, ← mul_smul, inv_mul_cancel₀ hc, one_smul] at hscaled
    exact hscaled
  change extension scalar a z ∈ KL.1
  exact hyKL

/-- The literal `C₂²` pair kernel acts faithfully on every retained
rank-two ternary section. -/
theorem degreeThreeFourBlockTwoSignSectionPairKernelRepresentation_injective
    (hr : Nat.card block.Fibre = 3)
    (hs : Nat.card block.Points = 4)
    (hcomponent : Nat.card block.Component = 6)
    (hbinary : IsPGroup 2
      (degreeThreeFourBlockPairChart block P hr hs hcomponent).action)
    (htwo : (degreeThreeFourBlockSignedIsotypeProfile
      block P hr hs hcomponent).isotypeCount = 2)
    (N : TwoSignProperAxis (E block P)) :
    Function.Injective
      (degreeThreeFourBlockTwoSignSectionPairKernelRepresentation
        block P hr hs hcomponent N) := by
  let scalar := degreeThreeFourBlockTranslationScalar
    block P hr hs hcomponent
  let KA := DegreeThreeFourBlockTwoSignAmbientScalarizedStable
    block P hr hs hcomponent
  let KL := DegreeThreeFourBlockTwoSignSectionNormalScalarizedStable
    block P hr hs hcomponent N
  have hker : ∀ k : (degreeThreeFourBlockPairChart
      block P hr hs hcomponent).frame.top.ker,
      degreeThreeFourBlockTwoSignSectionPairKernelRepresentation
          block P hr hs hcomponent N k = 1 → k = 1 := by
    intro k hk
    by_contra hk1
    obtain ⟨a, ha⟩ := degreeThreeFourBlockTwoSign_exists_isotype_ne_one
      block P hr hs hcomponent k hk1
    have hle : encode scalar KA a ≤ encode scalar KL a :=
      degreeThreeFourBlockTwoSignSection_encode_le_of_action_eq_one
        block P hr hs hcomponent N k hk a ha
    have hfin : Module.finrank (ZMod P.p) (encode scalar KA a) ≤
        Module.finrank (ZMod P.p) (encode scalar KL a) :=
      Submodule.finrank_mono hle
    have hcodim :=
      degreeThreeFourBlockTwoSignSection_isotype_codimension_one
        block P hr hs hcomponent hbinary htwo N a
    change Module.finrank (ZMod P.p) (encode scalar KA a) =
      Module.finrank (ZMod P.p) (encode scalar KL a) + 1 at hcodim
    omega
  intro x y hxy
  have hxy1 :
      degreeThreeFourBlockTwoSignSectionPairKernelRepresentation
          block P hr hs hcomponent N (x⁻¹ * y) = 1 := by
    rw [map_mul, ← hxy, ← map_mul, inv_mul_cancel, map_one]
  exact inv_mul_eq_one.mp (hker (x⁻¹ * y) hxy1)

/-- Hence the literal pair-kernel map into the actual section top is itself
injective. -/
theorem degreeThreeFourBlockTwoSignSectionPairKernelTopHom_injective
    (hr : Nat.card block.Fibre = 3)
    (hs : Nat.card block.Points = 4)
    (hcomponent : Nat.card block.Component = 6)
    (hbinary : IsPGroup 2
      (degreeThreeFourBlockPairChart block P hr hs hcomponent).action)
    (htwo : (degreeThreeFourBlockSignedIsotypeProfile
      block P hr hs hcomponent).isotypeCount = 2)
    (N : TwoSignProperAxis (E block P)) :
    Function.Injective
      (degreeThreeFourBlockTwoSignSectionPairKernelTopHom
        block P hr hs hcomponent N) := by
  intro x y hxy
  apply degreeThreeFourBlockTwoSignSectionPairKernelRepresentation_injective
    block P hr hs hcomponent hbinary htwo N
  change (degreeThreeFourBlockTwoSignSectionRepresentation block P N).ρ
      (degreeThreeFourBlockTwoSignSectionPairKernelTopHom
        block P hr hs hcomponent N x) =
    (degreeThreeFourBlockTwoSignSectionRepresentation block P N).ρ
      (degreeThreeFourBlockTwoSignSectionPairKernelTopHom
        block P hr hs hcomponent N y)
  rw [hxy]

end PrimitiveAffineImprimitiveBlockTransfer
end Non2UnipotentPrefixFiniteMenu
end SymmetricSubgroupAsymptotics

end
