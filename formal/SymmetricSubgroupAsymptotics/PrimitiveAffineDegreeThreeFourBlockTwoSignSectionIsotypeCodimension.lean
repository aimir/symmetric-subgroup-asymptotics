import SymmetricSubgroupAsymptotics.PrimitiveAffineDegreeThreeFourBlockTwoSignInvariantParity

/-!
# Isotype codimension in a proper two-sign ternary section

The literal two-sign translation module and every invariant normal-space
intersection have two equidimensional repeated-sign components.  The proper
section has rank two.  Consequently the normal space has codimension exactly
one in each of the two literal sign components.

This is the numerical input needed to show that no nontrivial element of the
literal pair kernel can act trivially on the retained section: a nontrivial
sign changes at least one component, while that component has not been killed
by the normal-space quotient.
-/

set_option autoImplicit false
noncomputable section
open scoped Classical

namespace SymmetricSubgroupAsymptotics
namespace Non2UnipotentPrefixFiniteMenu
namespace PrimitiveAffineImprimitiveBlockTransfer

open DiagonalInvariantSubmodules
open DiagonalIsotypeProjection

variable {w : ℕ} {U : PreE7NonPairActionClass w}
  {basePoint : Fin w}
  (block : OriginalMinimalBlock
    (A := preE7NonPairAction w U) basePoint)
  (P : PrimitiveAffineProfile block.Component block.Fibre)
  [Nontrivial block.Fibre]

local instance primitiveAffineDegreeThreeFourBlockTwoSignSectionIsotypeCodimension_localInstance1 : Fact P.p.Prime := (chart block P).primeFact

private abbrev QuotientRep :
    Representation (ZMod P.p)
      (preE7NonPairAction w U ⧸ E block P)
      (TranslationSubmodule block P) :=
  (elementaryChart block P).quotientRepresentation.ρ

/-- A fixed scalar coordinate on the one-dimensional local ternary module. -/
noncomputable def degreeThreeFourBlockLocalScalarEquiv
    (hr : Nat.card block.Fibre = 3) :
    (chart block P).V ≃ₗ[ZMod P.p] ZMod P.p :=
  LinearEquiv.ofFinrankEq _ _ (by
    have h := (degreeThree_translation_prime_dim block P hr).2
    change Module.finrank (ZMod P.p) (chart block P).V = 1 at h
    rw [h, Module.finrank_self])

/-- The scalarized literal correlated translation module. -/
abbrev DegreeThreeFourBlockTwoSignAmbientScalarizedStable
    (hr : Nat.card block.Fibre = 3)
    (hs : Nat.card block.Points = 4)
    (hcomponent : Nat.card block.Component = 6) :=
  scalarizedStable
    (degreeThreeFourBlockTranslationScalar block P hr hs hcomponent)
    (DegreeThreeFourBlockSignedTranslationCompatibility.stable
      (block := block) (P := P)
      (degreeThreeFourBlockSignedTranslationCompatibility
        block P hr hs hcomponent))
    (degreeThreeFourBlockLocalScalarEquiv block P hr)

/-- The invariant subrepresentation whose underlying module is the literal
normal-space intersection attached to a proper axis. -/
abbrev degreeThreeFourBlockTwoSignSectionNormalSubrepresentation
    (N : TwoSignProperAxis (E block P)) :
    Subrepresentation (QuotientRep block P) :=
  (elementaryChart block P).originalKernelChart.normalSubrepresentation
    (QuotientGroup.mk' (E block P))
    (QuotientGroup.mk'_surjective (E block P))
    (elementaryChart block P).quotientRepresentation
    (degreeThreeFourBlockTwoSignSectionAxis block P N)

/-- The preceding normal-space intersection, reindexed and scalarized in the
same literal sign coordinates as the ambient translation module. -/
abbrev DegreeThreeFourBlockTwoSignSectionNormalScalarizedStable
    (hr : Nat.card block.Fibre = 3)
    (hs : Nat.card block.Points = 4)
    (hcomponent : Nat.card block.Component = 6)
    (N : TwoSignProperAxis (E block P)) :=
  scalarizedStable
    (degreeThreeFourBlockTranslationScalar block P hr hs hcomponent)
    (degreeThreeFourBlockReindexedSubrepresentationStable
      block P hr hs hcomponent
      (degreeThreeFourBlockTwoSignSectionNormalSubrepresentation block P N))
    (degreeThreeFourBlockLocalScalarEquiv block P hr)

private theorem stable_finrank_eq_two_mul_component
    {k ι J : Type*} [Field k] [Fintype ι] [Nonempty ι]
    (scalar : ι → J → k)
    (K : Stable scalar)
    (htwo : Nat.card (Label scalar) = 2)
    (hequal : ∀ a b : Label scalar,
      Module.finrank k (encode scalar K a) =
        Module.finrank k (encode scalar K b))
    (a : Label scalar) :
    Module.finrank k K.1 = 2 * Module.finrank k (encode scalar K a) := by
  rw [finrank_eq_sum_encode scalar K]
  simp_rw [hequal _ a]
  rw [Finset.sum_const, nsmul_eq_mul, Finset.card_univ,
    Fintype.card_eq_nat_card, htwo]
  norm_num

/-- In every proper two-sign section, the normal-space intersection has
codimension one in each literal repeated-sign component. -/
theorem degreeThreeFourBlockTwoSignSection_isotype_codimension_one
    (hr : Nat.card block.Fibre = 3)
    (hs : Nat.card block.Points = 4)
    (hcomponent : Nat.card block.Component = 6)
    (hbinary : IsPGroup 2
      (degreeThreeFourBlockPairChart block P hr hs hcomponent).action)
    (htwo : (degreeThreeFourBlockSignedIsotypeProfile
      block P hr hs hcomponent).isotypeCount = 2)
    (N : TwoSignProperAxis (E block P))
    (a : Label (degreeThreeFourBlockTranslationScalar
      block P hr hs hcomponent)) :
    Module.finrank (ZMod P.p)
        (encode (degreeThreeFourBlockTranslationScalar
            block P hr hs hcomponent)
          (DegreeThreeFourBlockTwoSignAmbientScalarizedStable
            block P hr hs hcomponent) a) =
      Module.finrank (ZMod P.p)
        (encode (degreeThreeFourBlockTranslationScalar
            block P hr hs hcomponent)
          (DegreeThreeFourBlockTwoSignSectionNormalScalarizedStable
            block P hr hs hcomponent N) a) + 1 := by
  let scalar := degreeThreeFourBlockTranslationScalar
    block P hr hs hcomponent
  let A := degreeThreeFourBlockSignedTranslationCompatibility
    block P hr hs hcomponent
  let K := DegreeThreeFourBlockSignedTranslationCompatibility.stable
    (block := block) (P := P) A
  let e := degreeThreeFourBlockLocalScalarEquiv block P hr
  let KA := scalarizedStable scalar K e
  let W := degreeThreeFourBlockTwoSignSectionNormalSubrepresentation block P N
  let L := degreeThreeFourBlockReindexedSubrepresentationStable
    block P hr hs hcomponent W
  let KL := scalarizedStable scalar L e
  have hlabels : Nat.card (Label scalar) = 2 :=
    degreeThreeFourBlockTranslationScalarLabel_card_two
      block P hr hs hcomponent htwo
  have hAequal : ∀ x y : Label scalar,
      Module.finrank (ZMod P.p) (encode scalar KA x) =
        Module.finrank (ZMod P.p) (encode scalar KA y) := by
    intro x y
    exact degreeThreeFourBlockTwoSign_scalarized_components_equidimensional
      block P hr hs hcomponent e x y
  have hLequal : ∀ x y : Label scalar,
      Module.finrank (ZMod P.p) (encode scalar KL x) =
        Module.finrank (ZMod P.p) (encode scalar KL y) := by
    intro x y
    exact degreeThreeFourBlockTwoSign_subrepresentation_components_equidimensional
      block P hr hs hcomponent W e x y
  have hAtotal : Module.finrank (ZMod P.p) KA.1 =
      2 * Module.finrank (ZMod P.p) (encode scalar KA a) :=
    stable_finrank_eq_two_mul_component scalar KA hlabels hAequal a
  have hLtotal : Module.finrank (ZMod P.p) KL.1 =
      2 * Module.finrank (ZMod P.p) (encode scalar KL a) :=
    stable_finrank_eq_two_mul_component scalar KL hlabels hLequal a
  have hAtransport : Module.finrank (ZMod P.p) KA.1 =
      Module.finrank (ZMod P.p) (TranslationSubmodule block P) := by
    calc
      Module.finrank (ZMod P.p) KA.1 =
          Module.finrank (ZMod P.p) K.1 :=
        scalarizedStable_finrank scalar K e
      _ = Module.finrank (ZMod P.p) (TranslationSubmodule block P) :=
        (degreeThreeFourBlockReindexedTranslationEquiv block P hs).finrank_eq.symm
  have hLtransport : Module.finrank (ZMod P.p) KL.1 =
      Module.finrank (ZMod P.p)
        (degreeThreeFourBlockTwoSignSectionNormalSpace block P N) := by
    calc
      Module.finrank (ZMod P.p) KL.1 =
          Module.finrank (ZMod P.p) L.1 :=
        scalarizedStable_finrank scalar L e
      _ = Module.finrank (ZMod P.p) W.toSubmodule :=
        (degreeThreeFourBlockReindexedSubrepresentationEquiv
          block P hs W).finrank_eq.symm
      _ = Module.finrank (ZMod P.p)
          (degreeThreeFourBlockTwoSignSectionNormalSpace block P N) := rfl
  have hsection : Module.finrank (ZMod P.p)
      (DegreeThreeFourBlockTwoSignSectionModule block P N) = 2 :=
    degreeThreeFourBlockTwoSignSectionModule_finrank_eq_two
      block P hr hs hcomponent hbinary htwo N
  have hsum :=
    (degreeThreeFourBlockTwoSignSectionNormalSpace block P N).finrank_quotient_add_finrank
  change Module.finrank (ZMod P.p)
      (DegreeThreeFourBlockTwoSignSectionModule block P N) +
    Module.finrank (ZMod P.p)
      (degreeThreeFourBlockTwoSignSectionNormalSpace block P N) =
    Module.finrank (ZMod P.p) (TranslationSubmodule block P) at hsum
  change Module.finrank (ZMod P.p) (encode scalar KA a) =
    Module.finrank (ZMod P.p) (encode scalar KL a) + 1
  omega

end PrimitiveAffineImprimitiveBlockTransfer
end Non2UnipotentPrefixFiniteMenu
end SymmetricSubgroupAsymptotics

end
