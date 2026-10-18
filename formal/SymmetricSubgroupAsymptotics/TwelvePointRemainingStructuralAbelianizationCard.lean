import SymmetricSubgroupAsymptotics.PrimeRelativeHeadChain
import SymmetricSubgroupAsymptotics.PrimeRelativeRadicalPresentation
import SymmetricSubgroupAsymptotics.OriginalRetainedTopQuotientEquiv

/-! Actual elementary kernel coinvariants and the actual top abelianization
share one order budget. This retains nonsplit extensions and avoids an
assumption about extending scalar characters across a central subgroup. -/
set_option autoImplicit false
noncomputable section
namespace SymmetricSubgroupAsymptotics.TwelvePointRemainingStructural
local instance abelianizationCard_binaryPrimeFact : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
variable {G B : Type} [Group G] [Finite G] [Group B] [Finite B]

theorem abelianization_card_le_elementary_kernel_coinvariants
    (beta : G →* B) (hbeta : Function.Surjective beta)
    (hpow : ∀ k : beta.ker, (k : G)^2=1) :
    Nat.card (G ⧸ commutator G) ≤
      2 ^ Module.finrank (ZMod 2) (primeRelativeCharacters 2 beta.ker) *
        Nat.card (B ⧸ commutator B) := by
  let K := beta.ker
  let D := commutator G
  let H := normalChainQuotient D K
  have hR : primeRelativeRadical 2 K ≤ D := by
    rw [primeRelativeRadical_eq_powerCommutator]
    apply sup_le
    · apply (Subgroup.closure_le D).mpr
      rintro _ ⟨k,rfl⟩
      change (k : G)^2 ∈ D
      rw [hpow k]
      exact D.one_mem
    · exact Subgroup.commutator_mono le_top le_rfl
  let a : K →* H := normalChainMap D K
  have hkill : primeRelativeRadicalKernel 2 K ≤ a.ker := by
    intro k hk
    apply MonoidHom.mem_ker.mpr
    apply Subtype.ext
    exact (QuotientGroup.eq_one_iff (N := D) (k : G)).mpr
      (hR ((coe_mem_primeRelativeRadical_iff 2 K k).mpr hk))
  letI : (primeRelativeRadicalKernel 2 K).Normal := by
    change (primeRelativeEvaluation 2 K).ker.Normal
    infer_instance
  let u : (K ⧸ primeRelativeRadicalKernel 2 K) →* H :=
    QuotientGroup.lift _ a hkill
  have hu : Function.Surjective u := by
    intro x
    obtain ⟨k,rfl⟩ := normalChainMap_surjective D K x
    exact ⟨QuotientGroup.mk' _ k,rfl⟩
  have hH : Nat.card H ≤ 2 ^ Module.finrank (ZMod 2) (primeRelativeCharacters 2 K) := by
    simpa only [primeRelativeRadical_quotient_card] using Nat.card_le_card_of_surjective u hu
  let e := QuotientGroup.quotientKerEquivOfSurjective beta hbeta
  have htop : (D.map (QuotientGroup.mk' K)).map e.toMonoidHom = commutator B := by
    rw [Subgroup.map_map]
    change (commutator G).map beta = commutator B
    rw [map_commutator_eq, MonoidHom.range_eq_top.mpr hbeta]
    rfl
  let et := OriginalRetainedTopQuotientEquiv.retainedTopEquiv K D e
  have hcard : Nat.card ((G ⧸ D) ⧸ H) = Nat.card (B ⧸ commutator B) := by
    exact (Nat.card_congr et.toEquiv).trans
      (Nat.card_congr (QuotientGroup.quotientMulEquivOfEq htop).toEquiv)
  have hc := Subgroup.card_eq_card_quotient_mul_card_subgroup H
  calc
    Nat.card (G ⧸ D) = Nat.card ((G ⧸ D) ⧸ H) * Nat.card H := hc
    _ = Nat.card (B ⧸ commutator B) * Nat.card H := by rw [hcard]
    _ ≤ Nat.card (B ⧸ commutator B) *
        2 ^ Module.finrank (ZMod 2) (primeRelativeCharacters 2 K) := Nat.mul_le_mul_left _ hH
    _ = _ := Nat.mul_comm _ _

end SymmetricSubgroupAsymptotics.TwelvePointRemainingStructural
