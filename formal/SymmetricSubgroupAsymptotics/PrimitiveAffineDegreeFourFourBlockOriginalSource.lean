import SymmetricSubgroupAsymptotics.PrimitiveAffineDegreeFourFiveCharacterIntervalSource
import SymmetricSubgroupAsymptotics.CyclicSocleQuotientTools

/-!
The four-block residue needs a source only for the original zero-ternary
four-by-four action. A two-generator socle bound on its actual normal
quotients already fits the checked degree-four character interval. There
is no dependency on a source for every nonbinary degree-sixteen action.

The literal finite-row caller may supply an exact group equivalence. The
quotient used below remains the quotient by the original normal subgroup:
the composite epimorphism records its preimage in the literal row.
-/

set_option autoImplicit false
noncomputable section

namespace SymmetricSubgroupAsymptotics
namespace Non2UnipotentPrefixFiniteMenu.PrimitiveAffineImprimitiveBlockTransfer

variable {w : ℕ} {U : PreE7NonPairActionClass w} {basePoint : Fin w}
  (block : OriginalMinimalBlock (A := preE7NonPairAction w U) basePoint)
  (P : PrimitiveAffineProfile block.Component block.Fibre)
  [Nontrivial block.Fibre]

/-- Only the original retained translation interval is needed. The usual
literal all-quotient socle family supplies this premise by restriction. -/
noncomputable def degreeFourFourBlockSource_of_retainedSocles
    (hZmud : ZmudFaithfulCharacterTupleInput) (lit : PreE7CharacterLiterature)
    (hr : Nat.card block.Fibre = 4) (hs : Nat.card block.Points = 4)
    (hgen : ∀ N : {N : Subgroup (preE7NonPairAction w U) // N.Normal},
      ¬ E block P ≤ N.1 →
        SocleNormalGeneratorBound (preE7NonPairAction w U ⧸ N.1) 2) :
    PreE7RankTailSourceOrYonedaTopData w U := by
  apply degreeFourCharacterIntervalSource block P hZmud lit .acomp
    (fun N hN => ?_) hr (by omega) (by omega)
  simpa [hs, degreeFourSocleSlots] using hgen N hN

/-- Transport each actual original quotient through an exact literal
group chart. No arbitrary subgroup of an overgroup is used. -/
noncomputable def degreeFourFourBlockSource_of_literalSocles
    (hZmud : ZmudFaithfulCharacterTupleInput) (lit : PreE7CharacterLiterature)
    (hr : Nat.card block.Fibre = 4) (hs : Nat.card block.Points = 4)
    {G : Type} [Group G] [Finite G]
    (e : preE7NonPairAction w U ≃* G)
    (hall : ∀ N : {N : Subgroup G // N.Normal},
      SocleNormalGeneratorBound (G ⧸ N.1) 2) :
    PreE7RankTailSourceOrYonedaTopData w U := by
  apply degreeFourFourBlockSource_of_retainedSocles block P hZmud lit hr hs
  intro N _hN
  let pi : G →* preE7NonPairAction w U ⧸ N.1 :=
    (QuotientGroup.mk' N.1).comp e.symm.toMonoidHom
  have hpi : Function.Surjective pi :=
    (QuotientGroup.mk'_surjective N.1).comp e.symm.surjective
  exact CyclicSocleQuotientTools.socleBound_equiv
    (QuotientGroup.quotientKerEquivOfSurjective pi hpi)
    (hall ⟨pi.ker, inferInstance⟩)

end Non2UnipotentPrefixFiniteMenu.PrimitiveAffineImprimitiveBlockTransfer
end SymmetricSubgroupAsymptotics

end
