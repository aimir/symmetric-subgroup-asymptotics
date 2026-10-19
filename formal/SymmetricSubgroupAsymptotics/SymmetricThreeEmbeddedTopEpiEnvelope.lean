import SymmetricSubgroupAsymptotics.SymmetricThreeSubgroupNormalGenerators
import SymmetricSubgroupAsymptotics.ZmudFaithfulCharacterInput

/-! Every actual top embedded in S3 has a one-character onto envelope.
This counts ALL concrete top maps on the same complete source. -/
set_option autoImplicit false
noncomputable section
open scoped Classical
namespace SymmetricSubgroupAsymptotics.SymmetricThreeEmbeddedTopEpiEnvelope
variable {T : Type} [Group T] [Finite T]
  (f : T →* Equiv.Perm (Fin 3)) (hf : Function.Injective f)

include hf in
theorem socle_singleton : SocleNormalGeneratorBound T 1 := by
  let e : T ≃* f.range := MulEquiv.ofBijective f.rangeRestrict
    ⟨fun _ _ h => hf (congrArg Subtype.val h),f.rangeRestrict_surjective⟩
  have hnormal := normal_generating_tuples_of_surjective e.symm.toMonoidHom
    e.symm.surjective
    (SymmetricThreeSubgroupNormalGenerators.normal_generating_singletons f.range)
  exact hnormal (finiteGroupSocle T) inferInstance

include f hf

/-- The same estimate works for cyclic-three and symmetric-three tops;
no per-top-map count is omitted. -/
theorem epi_card_le (hZmud : ZmudFaithfulCharacterTupleInput)
    (lit : PreE7CharacterLiterature) (b : ℕ)
    (J : Subgroup (Equiv.Perm (Fin b))) :
    (Nat.card (GroupEpimorphism J T) : ℝ) ≤
      (Nat.card (T ≃* T) : ℝ) *
        (2 : ℝ)^((Real.logb 2 5 / 3)*b) := by
  have h := (hZmud.generalCertificate (socle_singleton f hf)).envelope lit b J
  simpa only [ZmudFaithfulCharacterTupleInput.generalCertificate_slope,
    Nat.cast_one,one_mul] using h
end SymmetricSubgroupAsymptotics.SymmetricThreeEmbeddedTopEpiEnvelope
