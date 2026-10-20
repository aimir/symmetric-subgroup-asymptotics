import SymmetricSubgroupAsymptotics.PrimeRelativeHeadChain
import SymmetricSubgroupAsymptotics.PrimeRelativeRadicalPresentation
import SymmetricSubgroupAsymptotics.OriginalRetainedTopQuotientEquiv
import Mathlib.GroupTheory.Abelianization.Finite

/-!
# Full abelianization orders along an actual extension

The image of the literal kernel in the full abelianization is bounded by
the kernel's full abelianization. If the kernel has exponent `p`, its image
is instead bounded by its original relative elementary head. The latter
step applies only to this exponent-`p` kernel; the top abelianization keeps
all higher prime-power exponents.
-/

set_option autoImplicit false
noncomputable section

namespace SymmetricSubgroupAsymptotics.PermutationAbelianQuotientOrderBound

variable {G B : Type} [Group G] [Finite G] [Group B]

omit [Finite G] in
private theorem card_le_of_kernel_image_bound
    (beta : G →* B) (hbeta : Function.Surjective beta) (r : ℕ)
    (himage : Nat.card (normalChainQuotient (commutator G) beta.ker) ≤ r) :
    Nat.card (Abelianization G) ≤ r * Nat.card (Abelianization B) := by
  let K := beta.ker
  let D := commutator G
  let H := normalChainQuotient D K
  let e := QuotientGroup.quotientKerEquivOfSurjective beta hbeta
  have htop : (D.map (QuotientGroup.mk' K)).map e.toMonoidHom = commutator B := by
    rw [Subgroup.map_map]
    change (commutator G).map beta = commutator B
    rw [map_commutator_eq, MonoidHom.range_eq_top.mpr hbeta]
    rfl
  let et := OriginalRetainedTopQuotientEquiv.retainedTopEquiv K D e
  have hcard : Nat.card ((G ⧸ D) ⧸ H) = Nat.card (Abelianization B) := by
    exact (Nat.card_congr et.toEquiv).trans
      (Nat.card_congr (QuotientGroup.quotientMulEquivOfEq htop).toEquiv)
  calc
    Nat.card (Abelianization G) = Nat.card ((G ⧸ D) ⧸ H) * Nat.card H :=
      Subgroup.card_eq_card_quotient_mul_card_subgroup H
    _ = Nat.card (Abelianization B) * Nat.card H := by rw [hcard]
    _ ≤ Nat.card (Abelianization B) * r := Nat.mul_le_mul_left _ himage
    _ = r * Nat.card (Abelianization B) := Nat.mul_comm _ _

/-- This controls the complete abelianization order, including arbitrary
prime-power cyclic factors, along the same original kernel and top. -/
theorem abelianization_card_extension
    (beta : G →* B) (hbeta : Function.Surjective beta) :
    Nat.card (Abelianization G) ≤
      Nat.card (Abelianization beta.ker) * Nat.card (Abelianization B) := by
  apply card_le_of_kernel_image_bound beta hbeta
  let D := commutator G
  let H := normalChainQuotient D beta.ker
  let a : beta.ker →* H := normalChainMap D beta.ker
  have hmap : (commutator beta.ker).map beta.ker.subtype ≤ D := by
    rw [map_commutator_eq]
    exact Subgroup.commutator_mono le_top le_top
  have hkill : commutator beta.ker ≤ a.ker := by
    intro k hk
    apply MonoidHom.mem_ker.mpr
    apply Subtype.ext
    exact (QuotientGroup.eq_one_iff (N := D) (k : G)).mpr (hmap ⟨k, hk, rfl⟩)
  let u : Abelianization beta.ker →* H := QuotientGroup.lift _ a hkill
  have hu : Function.Surjective u := by
    intro h
    obtain ⟨k, rfl⟩ := normalChainMap_surjective D beta.ker h
    exact ⟨Abelianization.of k, rfl⟩
  exact Nat.card_le_card_of_surjective u hu

/-- An exponent-`p` kernel contributes at most the order of its original
relative head; the top still contributes its full abelianization order. -/
theorem abelianization_card_elementary_kernel
    (p : ℕ) [Fact p.Prime]
    (beta : G →* B) (hbeta : Function.Surjective beta)
    (hpow : ∀ k : beta.ker, (k : G) ^ p = 1) :
    Nat.card (Abelianization G) ≤
      p ^ Module.finrank (ZMod p) (primeRelativeCharacters p beta.ker) *
        Nat.card (Abelianization B) := by
  apply card_le_of_kernel_image_bound beta hbeta
  let K := beta.ker
  let D := commutator G
  let H := normalChainQuotient D K
  have hR : primeRelativeRadical p K ≤ D := by
    rw [primeRelativeRadical_eq_powerCommutator]
    apply sup_le
    · apply (Subgroup.closure_le D).mpr
      rintro _ ⟨k, rfl⟩
      change (k : G) ^ p ∈ D
      rw [hpow k]
      exact D.one_mem
    · exact Subgroup.commutator_mono le_top le_rfl
  let a : K →* H := normalChainMap D K
  have hkill : primeRelativeRadicalKernel p K ≤ a.ker := by
    intro k hk
    apply MonoidHom.mem_ker.mpr
    apply Subtype.ext
    exact (QuotientGroup.eq_one_iff (N := D) (k : G)).mpr
      (hR ((coe_mem_primeRelativeRadical_iff p K k).mpr hk))
  letI : (primeRelativeRadicalKernel p K).Normal := by
    change (primeRelativeEvaluation p K).ker.Normal
    infer_instance
  let u : (K ⧸ primeRelativeRadicalKernel p K) →* H := QuotientGroup.lift _ a hkill
  have hu : Function.Surjective u := by
    intro x
    obtain ⟨k, rfl⟩ := normalChainMap_surjective D K x
    exact ⟨QuotientGroup.mk' _ k, rfl⟩
  simpa only [primeRelativeRadical_quotient_card] using Nat.card_le_card_of_surjective u hu

end SymmetricSubgroupAsymptotics.PermutationAbelianQuotientOrderBound

end
