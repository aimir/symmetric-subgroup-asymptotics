import SymmetricSubgroupAsymptotics.PermutationAbelianQuotientOrderBoundExtension
import SymmetricSubgroupAsymptotics.PGroupNormalGeneratorCharacterEquality
import Mathlib.Data.Fintype.EquivFin

/-! Equality in the full abelianization extension bound retains the exact
intersection with the derived subgroup. Higher cyclic factors in the top
are retained; only the literal kernel is assumed to have exponent p. -/
set_option autoImplicit false
noncomputable section
open scoped Classical
attribute [local instance] Fintype.ofFinite
namespace SymmetricSubgroupAsymptotics

variable {G Q : Type} [Group G] [Finite G] [Group Q] [Finite Q]

/-- The exact original kernel image in the full abelianization. -/
theorem abelianization_card_eq_top_mul_kernel_image
    (f : G →* Q) (hf : Function.Surjective f) :
    Nat.card (Abelianization G) = Nat.card (Abelianization Q) *
      Nat.card (normalChainQuotient (commutator G) f.ker) := by
  let K := f.ker
  let D := commutator G
  let H := normalChainQuotient D K
  let e := QuotientGroup.quotientKerEquivOfSurjective f hf
  have he : (D.map (QuotientGroup.mk' K)).map e.toMonoidHom = commutator Q := by
    rw [Subgroup.map_map]
    change (commutator G).map f = commutator Q
    rw [map_commutator_eq, MonoidHom.range_eq_top.mpr hf]
    rfl
  let et := OriginalRetainedTopQuotientEquiv.retainedTopEquiv K D e
  have hc : Nat.card ((G ⧸ D) ⧸ H) = Nat.card (Abelianization Q) :=
    (Nat.card_congr et.toEquiv).trans
      (Nat.card_congr (QuotientGroup.quotientMulEquivOfEq he).toEquiv)
  exact (Subgroup.card_eq_card_quotient_mul_card_subgroup H).trans
    (congrArg (fun n => n * Nat.card H) hc)

/-- Saturating the relative-head price makes every derived element of the
actual exponent-p kernel lie in its whole-ambient relative radical. -/
theorem primeRelativeRadical_eq_inf_commutator_of_abelianization_saturation
    (p : ℕ) [Fact p.Prime] (f : G →* Q) (hf : Function.Surjective f)
    (hpow : ∀ k : f.ker, (k : G) ^ p = 1)
    (hsat : Nat.card (Abelianization G) =
      p ^ Module.finrank (ZMod p) (primeRelativeCharacters p f.ker) *
        Nat.card (Abelianization Q)) :
    primeRelativeRadical p f.ker = f.ker ⊓ commutator G := by
  let K := f.ker
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
  have htop : 0 < Nat.card (Abelianization Q) := Nat.card_pos
  have hext := abelianization_card_eq_top_mul_kernel_image f hf
  have hc : Nat.card (K ⧸ primeRelativeRadicalKernel p K) = Nat.card H := by
    rw [primeRelativeRadical_quotient_card]
    change Nat.card (Abelianization G) = Nat.card (Abelianization Q) * Nat.card H at hext
    change Nat.card (Abelianization G) =
      p ^ Module.finrank (ZMod p) (primeRelativeCharacters p K) *
        Nat.card (Abelianization Q) at hsat
    nlinarith
  have hui : Function.Injective u :=
    (Fintype.bijective_iff_surjective_and_card u).mpr
      ⟨hu, by simpa only [← Nat.card_eq_fintype_card] using hc⟩ |>.1
  apply le_antisymm (le_inf (primeRelativeRadical_le p K) hR)
  intro x hx
  let k : K := ⟨x, hx.1⟩
  have hk : a k = 1 := Subtype.ext ((QuotientGroup.eq_one_iff x).mpr hx.2)
  have huq : u (QuotientGroup.mk' (primeRelativeRadicalKernel p K) k) = u 1 := by
    change a k = u 1
    rw [map_one, hk]
  have hq := hui huq
  exact (coe_mem_primeRelativeRadical_iff p K k).mpr
    ((QuotientGroup.eq_one_iff k).mp hq)

/-- Normal-generator formulation for a finite p-group ambient group. -/
theorem pGroup_relativeRadical_eq_inf_commutator_of_abelianization_saturation
    (p : ℕ) [Fact p.Prime] (hG : IsPGroup p G)
    (f : G →* Q) (hf : Function.Surjective f)
    (hpow : ∀ k : f.ker, (k : G) ^ p = 1)
    (hsat : Nat.card (Abelianization G) =
      p ^ MarkedC4.normalGen f.ker * Nat.card (Abelianization Q)) :
    primeRelativeRadical p f.ker = f.ker ⊓ commutator G := by
  apply primeRelativeRadical_eq_inf_commutator_of_abelianization_saturation p f hf hpow
  simpa only [pGroup_normalGen_eq_primeRelativeHead p hG f.ker] using hsat

end SymmetricSubgroupAsymptotics
