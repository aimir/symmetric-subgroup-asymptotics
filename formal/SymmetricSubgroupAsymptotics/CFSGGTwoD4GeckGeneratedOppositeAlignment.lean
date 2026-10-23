import SymmetricSubgroupAsymptotics.CFSGGTwoD4GeckFixedBruhatOppositeAlignment
import SymmetricSubgroupAsymptotics.CFSGTrialityGeckRootGeneratedPGroup
import SymmetricSubgroupAsymptotics.CFSGSubgroupConjugateRestriction
import SymmetricSubgroupAsymptotics.CFSGNormTwoGeckOppositeIntersection
import SymmetricSubgroupAsymptotics.CFSGTrialityGeckFixedRangePreimage

/-! The proved raw fixed opposite alignment restricts to the literal
generated identity-twist group J. Both signed root parts retain their
actual matrix images, and their intersection is genuinely trivial. -/
set_option autoImplicit false
set_option Elab.async false
set_option backward.isDefEq.respectTransparency false
noncomputable section
open scoped Classical
namespace SymmetricSubgroupAsymptotics.CFSGGTwoD4GeckGeneratedOppositeAlignment
open CFSGGTwoD4GeckFixedBruhatOppositeAlignment CFSGTrialityGeckRootGeneratedPGroup
open CFSGTrialityGeckRelativeRootGenerated CFSGTrialityGeckDiagramCovariance
open CFSGTrialityGeckSourceWordAction CFSGTrialityGeckPositiveTwist
open CFSGTrialityGeckNormalizerEnvelope
open CFSGTrialityGeckFixedRangePreimage
open CFSGNormTwoGeckIntegralRealization CFSGNormTwoGeckOppositeIntersection
open CFSGNormTwoCoordinateHeight CFSGTrialityD4NormTwo CFSGSubgroupConjugateRestriction
variable (K : Type) [Field K] [Finite K]
local notation "J" => fixedRootGenerated K (RingEquiv.refl K)

theorem rootPart_raw_image (isNegative : Bool) :
    (rootPart K (RingEquiv.refl K) isNegative).map
      (fixedRootGenerated K (RingEquiv.refl K)).subtype =
      signedFixed K (RingEquiv.refl K) isNegative :=
  Subgroup.map_subgroupOf_eq_of_le (signedFixed_le_generated K (RingEquiv.refl K) isNegative)

theorem rootParts_inf_eq_bot :
    rootPart K (RingEquiv.refl K) false ⊓ rootPart K (RingEquiv.refl K) true = ⊥ := by
  have hbot : Positive K ⊓ Negative K = ⊥ :=
    positive_inf_negative (CartanMatrix.D 4) (CartanMatrix.D_transpose 4) D4_positive_definite
      Base Index coordinateHeight (simple_height (CartanMatrix.D 4) (CartanMatrix.D_diag 4)
        (CartanMatrix.D_transpose 4) D4_positive_definite (CartanMatrix.D_off_diag_nonpos 4)) K
  apply bot_unique
  intro g hg
  apply Subgroup.mem_bot.mpr
  apply Subtype.ext
  have hm : g.val ∈ Positive K ⊓ Negative K := ⟨hg.1.1, hg.2.1⟩
  rw [hbot, Subgroup.mem_bot] at hm
  exact hm

theorem generated_opposite_conjugate_by_positive (g : J)
    (hdisj : rootPart K (RingEquiv.refl K) false ⊓
      (rootPart K (RingEquiv.refl K) false).map (MulAut.conj g).toMonoidHom = ⊥) :
    ∃ b ∈ rootPart K (RingEquiv.refl K) false,
      (rootPart K (RingEquiv.refl K) false).map (MulAut.conj g).toMonoidHom =
        (rootPart K (RingEquiv.refl K) true).map (MulAut.conj b).toMonoidHom := by
  have hraw : signedFixed K (RingEquiv.refl K) false ⊓
      (signedFixed K (RingEquiv.refl K) false).map (MulAut.conj g.val).toMonoidHom = ⊥ := by
    have hh := congrArg (fun S : Subgroup J =>
      S.map (fixedRootGenerated K (RingEquiv.refl K)).subtype) hdisj
    dsimp only at hh
    rwa [Subgroup.map_inf _ _ _ (fixedRootGenerated K (RingEquiv.refl K)).subtype_injective, map_conjugate,
      rootPart_raw_image, Subgroup.map_bot] at hh
  obtain ⟨u, hu, he⟩ := fixed_opposite_conjugate_by_positive K g.val
    (fixedRootGenerated_le_matrixGroup K (RingEquiv.refl K) g.property)
    (fixedRootGenerated_le_fixed K (RingEquiv.refl K) g.property) hraw
  let b : J := ⟨u, signedFixed_le_generated K (RingEquiv.refl K) false hu⟩
  refine ⟨b, hu, ?_⟩
  apply Subgroup.map_injective (f := (fixedRootGenerated K (RingEquiv.refl K)).subtype)
    (fixedRootGenerated K (RingEquiv.refl K)).subtype_injective
  rw [map_conjugate, map_conjugate, rootPart_raw_image, rootPart_raw_image]
  exact he

end SymmetricSubgroupAsymptotics.CFSGGTwoD4GeckGeneratedOppositeAlignment
