import SymmetricSubgroupAsymptotics.BinaryCharacterEnvelope
import SymmetricSubgroupAsymptotics.FusionWidthPhysical

/-! The checked character criterion enters original-weight fusion at
its actual even physical width. Arbitrary survival restrictions only
decrease the count; the complement and target automorphism factor remain.
This module does not assert a complete owner cover. -/
set_option autoImplicit false
noncomputable section
namespace SymmetricSubgroupAsymptotics

theorem BinaryNormalCharacterCriterion.fusion_gap
    {Q : Type} [Group Q] {w : ℕ} (C : BinaryNormalCharacterCriterion Q w)
    (hw : Even w) :
    binaryCharacterSlope C.dimension<(halfDegree w:ℝ)/4 := by
  obtain ⟨k,hk⟩ := hw
  have hh : 2*halfDegree w=w := by unfold halfDegree; omega
  have hhr : 2*(halfDegree w:ℝ)=(w:ℝ) := by exact_mod_cast hh
  have h := C.slope_gap
  linarith

theorem BinaryNormalCharacterCriterion.survival_envelope
    (hMaroti : NilpotentConjugacyClassInput)
    {Q : Type} [Group Q] [Finite Q] {w : ℕ} (C : BinaryNormalCharacterCriterion Q w)
    (hQ : IsPGroup 2 Q) (b : ℕ) (J : Subgroup (Equiv.Perm (Fin b)))
    (S : GroupEpimorphism J Q→Prop) :
    (Nat.card {f : GroupEpimorphism J Q // S f}:ℝ)≤(Nat.card (Q≃*Q):ℝ)*
      (2:ℝ)^(binaryCharacterSlope C.dimension*(b:ℝ)) := by
  letI : Finite (GroupEpimorphism J Q) := Finite.of_injective
    (fun f : GroupEpimorphism J Q=>(f.1:J→Q))
    (fun _ _ h=>Subtype.ext (DFunLike.coe_injective h))
  have hn := Nat.card_le_card_of_injective
    (Subtype.val : {f : GroupEpimorphism J Q // S f}→GroupEpimorphism J Q)
    Subtype.val_injective
  exact (by exact_mod_cast hn : (Nat.card {f : GroupEpimorphism J Q // S f}:ℝ)≤
    (Nat.card (GroupEpimorphism J Q):ℝ)).trans (C.original_envelope hMaroti hQ b J)

/-- One original literal normal axis receives its proved cold envelope.
Physical pointing and the original normalizer division happen later in
the complete stable sum, as required by fusionWidthPhysical_bound. -/
theorem binaryCharacter_physicalAxis_envelope
    (hMaroti : NilpotentConjugacyClassInput) {w b : ℕ}
    (U : Subgroup (Equiv.Perm (Fin w))) (hU : IsPGroup 2 U)
    (P : Subgroup (U×Equiv.Perm (Fin b))→Prop)
    (N : {N : Subgroup U // N.Normal})
    (C : BinaryNormalCharacterCriterion (U⧸N.1) w)
    (J : Subgroup (Equiv.Perm (Fin b))) :
    fusionSurvivingEpiCount U P N J≤(Nat.card ((U⧸N.1)≃*(U⧸N.1)):ℝ)*
      (2:ℝ)^(binaryCharacterSlope C.dimension*(b:ℝ)) := by
  exact C.survival_envelope hMaroti (hU.to_quotient N.1) b J
    (fun f=>P (fusionFullGoursatEncode N J f).1)

end SymmetricSubgroupAsymptotics
