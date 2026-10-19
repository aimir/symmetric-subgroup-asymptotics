import SymmetricSubgroupAsymptotics.ScalarFourCentralSymmetricCompleteQuotientEnvelopeTwo
import SymmetricSubgroupAsymptotics.PrimitiveAffineDegreeSixTailSource

/-! A socle-one target of order at most 2^12 has a uniform all-source
onto-map envelope. This counts actual maps, including automorphisms,
without introducing a cold-source condition. -/
set_option autoImplicit false
noncomputable section
namespace SymmetricSubgroupAsymptotics.SocleOneEpimorphismEnvelopeTwelve

variable {Q : Type} [Group Q] [Finite Q]

/-- The proper original central quotients use this literal-map bound. -/
theorem epi_card_le (hQ : Nat.card Q≤2^12) (hs : SocleNormalGeneratorBound Q 1)
    (hZmud : ZmudFaithfulCharacterTupleInput) (lit : PreE7CharacterLiterature)
    (b : ℕ) (J : Subgroup (Equiv.Perm (Fin b))) :
    (Nat.card (GroupEpimorphism J Q) : ℝ)≤
      (2 : ℝ)^(144 : ℕ)*(2 : ℝ)^((43/30 : ℝ)*(b : ℝ)) := by
  have h := (hZmud.generalCertificate hs).envelope lit b J
  simp only [ZmudFaithfulCharacterTupleInput.generalCertificate_slope,
    Nat.cast_one,one_mul] at h
  have haut : (Nat.card (Q ≃* Q) : ℝ)≤(2 : ℝ)^(144 : ℕ) := by
    exact_mod_cast mulEquiv_card_le_two_pow_sq_of_order 12 hQ
  have ht : Real.logb 2 5/3≤(43/30 : ℝ) := by
    have hh := ScalarFourCentralTopCoordinates.coldSlopeTwo_le_width_twelve
    unfold ScalarFourCentralTopCoordinates.coldSlopeTwo at hh
    linarith
  have hp : (2 : ℝ)^((Real.logb 2 5/3)*(b : ℝ))≤
      (2 : ℝ)^((43/30 : ℝ)*(b : ℝ)) :=
    Real.rpow_le_rpow_of_exponent_le (by norm_num : (1 : ℝ)≤2)
      (mul_le_mul_of_nonneg_right ht (Nat.cast_nonneg b))
  exact h.trans (mul_le_mul haut hp (by positivity) (by positivity))

end SymmetricSubgroupAsymptotics.SocleOneEpimorphismEnvelopeTwelve
