import SymmetricSubgroupAsymptotics.TernaryOddPartRelativeAnchor
import SymmetricSubgroupAsymptotics.TernaryOddPartNonbinaryQuotient

/-! A two-generator socle and odd part three give one ordinary anchor
and one relative character on the SAME actual quotient. -/
set_option autoImplicit false
noncomputable section
namespace SymmetricSubgroupAsymptotics
open Non2UnipotentPrefixFiniteMenu.PrimitiveAffineImprimitiveBlockTransfer

/-- Exact odd part of a nonbinary divisor, without enumerating normals. -/
theorem ternaryOddPart_exact_of_dvd_not_binary
    {Q : Type} [Group Q] [Finite Q] {a : ℕ}
    (hdiv : Nat.card Q ∣ 2^a*3) (hQ : ¬IsPGroup 2 Q) :
    ∃ r ≤ a, Nat.card Q=2^r*3 := by
  have hthree := ternaryOddPart_three_dvd_card_of_not_isPGroup_two hdiv hQ
  obtain ⟨m, hm⟩ := hthree
  have hmdiv : m ∣ 2^a := by
    apply (Nat.mul_dvd_mul_iff_left (by decide : 0<3)).mp
    simpa only [hm, Nat.mul_comm (2^a) 3] using hdiv
  obtain ⟨r, hr, hmr⟩ := (Nat.dvd_prime_pow Nat.prime_two).mp hmdiv
  exact ⟨r, hr, by rw [hm, hmr, Nat.mul_comm]⟩

/-- All top maps remain counted. The coefficient is the target's actual
 automorphism cardinal and the profile is ordinary one, relative one. -/
def ternaryOddPart_top_anchor_envelope
    (hZmud : ZmudFaithfulCharacterTupleInput) (lit : PreE7CharacterLiterature)
    {Q : Type} [Group Q] [Finite Q] {a : ℕ}
    (hdiv : Nat.card Q ∣ 2^a*3) (hQ : ¬IsPGroup 2 Q)
    (hsocle : SocleNormalGeneratorBound Q 2) :
    DegreeTwoPairRelativeQuotientEnvelope Q (degreeTwoPairOrdinaryRelativeProfile 1 1) := by
  let witness := ternaryOddPart_exact_of_dvd_not_binary hdiv hQ
  exact (DegreeTwoPairRelativeKernelAnchor.ofTernaryOddPartSocleGeneratorBound
    hZmud (r := 1) witness.choose_spec.2 hsocle).toQuotientEnvelope lit

/-- The envelope retains the actual automorphism coefficient. -/
theorem ternaryOddPart_top_anchor_epi_le
    (hZmud : ZmudFaithfulCharacterTupleInput) (lit : PreE7CharacterLiterature)
    {Q : Type} [Group Q] [Finite Q] {a : ℕ}
    (hdiv : Nat.card Q ∣ 2^a*3) (hQ : ¬IsPGroup 2 Q)
    (hsocle : SocleNormalGeneratorBound Q 2)
    (b : ℕ) (J : Subgroup (Equiv.Perm (Fin b))) :
    (Nat.card (GroupEpimorphism J Q) : ℝ) ≤ (Nat.card (Q ≃* Q) : ℝ)*
      (2 : ℝ)^((Real.logb 2 5/3+Real.logb 2 (38/25))*b) := by
  obtain ⟨r, _, hr⟩ := ternaryOddPart_exact_of_dvd_not_binary hdiv hQ
  let anchor := DegreeTwoPairRelativeKernelAnchor.ofTernaryOddPartSocleGeneratorBound
    hZmud (r := 1) hr hsocle
  have h := (anchor.toQuotientEnvelope lit).bound b J
  change (Nat.card (GroupEpimorphism J Q) : ℝ) ≤ (Nat.card (Q ≃* Q) : ℝ)*
    (2 : ℝ)^((degreeTwoPairOrdinaryRelativeProfile 1 1).slope*b) at h
  simpa [DegreeTwoPairRelativeProfile.slope,degreeTwoPairOrdinaryRelativeProfile] using h

end SymmetricSubgroupAsymptotics
