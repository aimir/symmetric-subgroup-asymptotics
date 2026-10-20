import SymmetricSubgroupAsymptotics.TwelvePointRemainingStructuralSchurSocles
import SymmetricSubgroupAsymptotics.TwelvePointRemainingStructuralCentralQuotients
import SymmetricSubgroupAsymptotics.TwelvePointRemainingStructuralSignedTopHead
import SymmetricSubgroupAsymptotics.TwelvePointRemainingStructuralAbelianizationCard
import SymmetricSubgroupAsymptotics.TwelvePointRemainingStructuralSymmetricAbelianization

/-! Shared original-quotient socle proof for the signed-S4 family.
The normal-image dichotomy supplies the central type; rank six and the
absence of a ternary quotient supply all other binary types. They share
two Schur slots, and the odd socle uses the same maximum. -/
set_option autoImplicit false
noncomputable section
namespace SymmetricSubgroupAsymptotics.TwelvePointRemainingStructural
local instance originalQuotientSocles_binaryPrimeFact : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩

variable {G X : Type} [Group G] [Finite G] [Finite X]
  [MulAction G X] [FaithfulSMul G X]

theorem quotientSocle_two_of_original_symmetricThree
    (hX : Nat.card X=12)
    (b : G →* Equiv.Perm (Fin 3)) (hb : Function.Surjective b)
    (hker : IsPGroup 2 b.ker)
    (hhead : ∀ (M : Subgroup G) [M.Normal],
      Module.finrank (ZMod 2) (primeRelativeCharacters 2 M) ≤ 2)
    (N : Subgroup G) [N.Normal] : SocleNormalGeneratorBound (G ⧸ N) 2 := by
  letI : IsSolvable G := isSolvable_of_binary_kernel_symmetricThree b hker
  let q := QuotientGroup.mk' N
  letI : IsSolvable (G ⧸ N) := solvable_of_surjective (QuotientGroup.mk'_surjective N)
  have hno : NoTernaryQuotient (G ⧸ N) :=
    (noTernaryQuotient_of_binary_kernel_symmetricThree b hb hker).of_surjective q
      (QuotientGroup.mk'_surjective N)
  have hsection := binarySectionalRankBound_of_faithful_permutation_quotient
    (X := X) q (QuotientGroup.mk'_surjective N)
  have hsection' : PrimeSectionalRankBound 2 (G ⧸ N) 6 := by
    simpa only [hX] using hsection
  have hcentral := centralOmega_quotient_finrank_le_allRelativeHeads 2 hhead N
  obtain ⟨a,ha⟩ := IsPGroup.iff_card.mp hker
  have hGcard : Nat.card G=2^(a+1)*3 := by
    have he := Nat.card_congr (QuotientGroup.quotientKerEquivOfSurjective b hb).toEquiv
    have hc := Subgroup.card_eq_card_quotient_mul_card_subgroup b.ker
    rw [he,ha,Nat.card_perm,Nat.card_fin] at hc
    norm_num at hc
    rw [hc,pow_succ]
    ring
  have hcard : Nat.card (G ⧸ N) ∣ 2^(a+1)*3 := by
    rw [← hGcard]
    exact Subgroup.card_quotient_dvd_card N
  exact socleNormalGeneratorBound_two_of_isSolvable_noTernaryQuotient
    hno hsection' hcentral hcard

theorem quotientSocle_two_of_signed_symmetricTop
    (hX : Nat.card X=12)
    (beta : G →* Equiv.Perm (Fin 4)) (hbeta : Function.Surjective beta)
    (hK : IsMulCommutative beta.ker) (hKtwo : IsPGroup 2 beta.ker)
    (hpow : ∀ k : beta.ker, (k : G)^2=1)
    (hkernel : ∀ (L : Subgroup G) [L.Normal], L ≤ beta.ker →
      Module.finrank (ZMod 2) (primeRelativeCharacters 2 L) ≤ 2)
    (hwhole : Module.finrank (ZMod 2) (primeRelativeCharacters 2 beta.ker) ≤ 1)
    (N : Subgroup G) [N.Normal] : SocleNormalGeneratorBound (G ⧸ N) 2 := by
  have hab : Nat.card (G ⧸ commutator G) ≤ 4 := by
    calc
      _ ≤ 2 ^ Module.finrank (ZMod 2) (primeRelativeCharacters 2 beta.ker) *
          Nat.card (Equiv.Perm (Fin 4) ⧸ commutator (Equiv.Perm (Fin 4))) :=
        abelianization_card_le_elementary_kernel_coinvariants beta hbeta hpow
      _ ≤ 2^1 * 2 := Nat.mul_le_mul
        (Nat.pow_le_pow_right (by decide : 0 < 2) hwhole) symmetric_abelianization_card_le_two
      _ = 4 := by decide
  have hhead := signed_symmetric_top_relative_head_le_two beta hbeta hK hkernel hab
  let b := NaturalS4.pairing.comp beta
  have hb : Function.Surjective b := NaturalS4.pairing_surjective.comp hbeta
  have hk : IsPGroup 2 NaturalS4.pairing.ker := by
    apply IsPGroup.of_card (n := 2)
    rw [NaturalS4.ker_pairing]
    exact NaturalS4.card_klein
  have hker : IsPGroup 2 b.ker := hk.comap_of_ker_isPGroup beta hKtwo
  exact quotientSocle_two_of_original_symmetricThree (X := X) hX b hb hker hhead N

end SymmetricSubgroupAsymptotics.TwelvePointRemainingStructural
