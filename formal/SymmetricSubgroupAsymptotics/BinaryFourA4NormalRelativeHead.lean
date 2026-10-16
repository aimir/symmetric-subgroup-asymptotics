import SymmetricSubgroupAsymptotics.BinaryKleinTernaryNormalChain
import SymmetricSubgroupAsymptotics.BinaryConjugateTripleRelativeHead
import SymmetricSubgroupAsymptotics.PrimeRelativeHeadChainCapacity
import SymmetricSubgroupAsymptotics.PrimeCharacterOrderDivisibility

/-! Every actual normal subgroup of the canonical A4 complement has zero
binary relative head. The literal Klein subgroup is killed by a cubic
conjugate norm; the remaining original quotient has odd order. -/
set_option autoImplicit false
noncomputable section
namespace SymmetricSubgroupAsymptotics.BinaryFourA4NormalRelativeHead
open BinaryFourBlockAugmentation BinaryKleinTernaryNormalChain SemidirectProduct
local instance : Fact (Nat.Prime 2) := ⟨by decide⟩
local instance : Fintype Klein :=
  Fintype.ofEquiv Local (Multiplicative.ofAdd : Local ≃ Klein)
local instance : DecidableEq Klein := fun x y =>
  if h : x.toAdd = y.toAdd then isTrue (Multiplicative.toAdd.injective h)
  else isFalse (fun he => h (congrArg Multiplicative.toAdd he))

private def cubic : Complement := inr (Multiplicative.ofAdd 1)

private theorem klein_head_zero :
    Module.finrank (ZMod 2) (primeRelativeCharacters 2 kleinKernel) = 0 := by
  apply binary_relativeHead_eq_zero_of_conjugate_triple kleinKernel cubic
  intro n
  have hd : ∀ p : Klein,
      ((inl p : Complement) * (cubic * inl p * cubic⁻¹) *
        (cubic * (cubic * inl p * cubic⁻¹) * cubic⁻¹)).left = 1 ∧
      ((inl p : Complement) * (cubic * inl p * cubic⁻¹) *
        (cubic * (cubic * inl p * cubic⁻¹) * cubic⁻¹)).right = 1 := by
    decide +kernel
  have hn : (inl (n : Complement).left : Complement) = n :=
    SemidirectProduct.ext rfl (show (n : Complement).right = 1 from n.2).symm
  apply Subtype.ext
  change (n : Complement) * (cubic * (n : Complement) * cubic⁻¹) *
    (cubic * (cubic * (n : Complement) * cubic⁻¹) * cubic⁻¹) = 1
  rw [← hn]
  exact SemidirectProduct.ext (hd _).1 (hd _).2

private theorem absolute_head_zero_of_card_dvd_three
    (H : Type) [Group H] [Finite H] (hH : Nat.card H ∣ 3) :
    Module.finrank (ZMod 2) (PrimeCharacters 2 H) = 0 := by
  let r := Module.finrank (ZMod 2) (PrimeCharacters 2 H)
  have hd : 2 ^ r ∣ 3 := (primeCharacters_pow_finrank_dvd_card 2 H).trans hH
  by_contra hr
  have hrpos : 0 < r := Nat.pos_of_ne_zero hr
  obtain ⟨k, hk⟩ := Nat.exists_eq_add_of_le hrpos
  have htwo : 2 ∣ 2 ^ r := by
    rw [hk, pow_add]
    exact dvd_mul_right 2 (2 ^ k)
  exact (by decide : ¬ 2 ∣ 3) (htwo.trans hd)

/-- No normal-subgroup census is used: the original normal chain through
Klein controls all actual normal subgroups at once. -/
theorem normal_relative_head_zero (N : Subgroup Complement) [N.Normal] :
    Module.finrank (ZMod 2) (primeRelativeCharacters 2 N) = 0 := by
  by_cases hN : N = ⊥
  · subst N
    letI : Subsingleton (primeRelativeCharacters 2 (⊥ : Subgroup Complement)) := ⟨by
      intro chi psi
      apply Subtype.ext
      apply AddMonoidHom.ext
      intro x
      have hx : x = 0 := Subsingleton.elim _ _
      rw [hx, map_zero, map_zero]⟩
    exact Module.finrank_zero_of_subsingleton
  have hKN := kleinKernel_le_normal N inferInstance hN
  have hquot : Nat.card (Complement ⧸ kleinKernel) = 3 := by
    change Nat.card (Complement ⧸ (SemidirectProduct.rightHom : Complement →* Ternary).ker) = 3
    rw [Nat.card_congr (QuotientGroup.quotientKerEquivOfSurjective
      (SemidirectProduct.rightHom : Complement →* Ternary)
      (fun z => ⟨inr z, rfl⟩)).toEquiv,
      Nat.card_congr (Multiplicative.toAdd : Ternary ≃ ZMod 3), Nat.card_zmod]
  have hcard : Nat.card (normalChainQuotient kleinKernel N) ∣ 3 := by
    simpa only [hquot] using
      (normalChainQuotient kleinKernel N).card_subgroup_dvd_card
  have hz := absolute_head_zero_of_card_dvd_three _ hcard
  have h := primeRelativeHead_chain_le_absolute kleinKernel N 2 hKN
  rw [klein_head_zero, hz, zero_add] at h
  exact Nat.eq_zero_of_le_zero h

end SymmetricSubgroupAsymptotics.BinaryFourA4NormalRelativeHead
