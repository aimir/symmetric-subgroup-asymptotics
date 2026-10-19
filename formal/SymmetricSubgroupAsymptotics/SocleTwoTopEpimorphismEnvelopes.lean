import SymmetricSubgroupAsymptotics.ZmudFaithfulCharacterInput

/-! Independent complete-source bounds for the actual retained top.
Binary targets use actual Sylow restriction rather than two unrestricted
ordinary-character counts. -/
set_option autoImplicit false
noncomputable section
namespace SymmetricSubgroupAsymptotics

variable {Q : Type} [Group Q] [Finite Q]

/-- The actual binary target is the known prime group in the certificate. -/
def socleTwoBinaryCertificate (hZmud : ZmudFaithfulCharacterTupleInput)
    (hQ : IsPGroup 2 Q) (hsocle : SocleNormalGeneratorBound Q 2) :
    CharacterQuotientCertificate Q where
  mode := .knownPGroup
  tuple := hZmud.generalTuple hsocle
  prime := 2
  known := fun _ => ⟨Nat.prime_two,hQ⟩

theorem socleTwo_binary_epi_le
    (hZmud : ZmudFaithfulCharacterTupleInput) (lit : PreE7CharacterLiterature)
    (hQ : IsPGroup 2 Q) (hsocle : SocleNormalGeneratorBound Q 2)
    (b : ℕ) (J : Subgroup (Equiv.Perm (Fin b))) :
    (Nat.card (GroupEpimorphism J Q) : ℝ) ≤
      (Nat.card (Q ≃* Q) : ℝ) *
        (2 : ℝ)^((2*Real.logb 2 (38/25))*b) := by
  simpa only [CharacterQuotientCertificate.slope, socleTwoBinaryCertificate,
    ZmudFaithfulCharacterTupleInput.generalTuple_binaryCount,
    ZmudFaithfulCharacterTupleInput.generalTuple_linearCount,
    ZmudFaithfulCharacterTupleInput.generalTuple_generalCount,
    CharacterQuotientMode.generalSlope, Nat.cast_zero, Nat.cast_ofNat,
    zero_mul, zero_add] using
    (socleTwoBinaryCertificate hZmud hQ hsocle).envelope lit b J

theorem socleTwo_general_epi_le
    (hZmud : ZmudFaithfulCharacterTupleInput) (lit : PreE7CharacterLiterature)
    (hsocle : SocleNormalGeneratorBound Q 2)
    (b : ℕ) (J : Subgroup (Equiv.Perm (Fin b))) :
    (Nat.card (GroupEpimorphism J Q) : ℝ) ≤
      (Nat.card (Q ≃* Q) : ℝ) *
        (2 : ℝ)^((2*(Real.logb 2 5/3))*b) := by
  simpa only [ZmudFaithfulCharacterTupleInput.generalCertificate_slope,
    Nat.cast_ofNat] using (hZmud.generalCertificate hsocle).envelope lit b J

end SymmetricSubgroupAsymptotics
