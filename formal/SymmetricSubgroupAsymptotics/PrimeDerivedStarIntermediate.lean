import SymmetricSubgroupAsymptotics.PrimeDerivedVanishingCenter
import SymmetricSubgroupAsymptotics.PrimeRelativeVanishingOrder
import SymmetricSubgroupAsymptotics.NormalSubgroupSaturationHeadBounds
import SymmetricSubgroupAsymptotics.StarAlternatingExactDimensions
import Lean.Elab.Tactic.Omega

/-! Exact proper-intermediate invariants for a complete original star
family. The full vanishing parameter space is retained. Actual nonempty
saturation proves the relative radical, including the original powers;
no mixed-commutator/parameter-space identification is postulated. -/
set_option autoImplicit false
noncomputable section

namespace SymmetricSubgroupAsymptotics

variable (p : ℕ) [Fact p.Prime] {G : Type*} [Group G] [Finite G]

/-- Simultaneous original-group invariants, parameterized by the actual
radical's order/head/normal-head and the star's horizontal dimension. -/
structure PrimeDerivedStarIntermediateInvariants
    (hker : (primeAbelianizationGroupMap p G).ker = commutator G)
    (N : Subgroup G) [N.Normal] (r a m d : ℕ) : Prop where
  relativeRadical_eq : primeRelativeRadical p N = primeRelativeRadical p (commutator G)
  head_pos : 1 ≤ Module.finrank (ZMod p) (primeRelativeCharacters p N)
  head_lt : Module.finrank (ZMod p) (primeRelativeCharacters p N) < d
  parameter_add_head : Module.finrank (ZMod p) (derivedCharactersVanishingOn p N) +
    Module.finrank (ZMod p) (primeRelativeCharacters p N) = d
  card_eq : Nat.card N = p ^ (r + Module.finrank (ZMod p) (primeRelativeCharacters p N))
  normalHeadMax_eq : primeNormalHeadMax p N =
    max m (Module.finrank (ZMod p) (primeRelativeCharacters p N))
  radicalHead_eq : Module.finrank (ZMod p)
    (primeRelativeCharacters p (primeRelativeRadical p N)) = a
  common_finrank : Module.finrank (ZMod p) (derivedVanishingCommonRadical p hker N) =
    Module.finrank (ZMod p) (primeRelativeCharacters p N)
  center_card : Nat.card (Subgroup.center (G ⧸ N)) = p ^ d
  derived_card : Nat.card (commutator (G ⧸ N)) =
    p ^ (d - Module.finrank (ZMod p) (primeRelativeCharacters p N))

private theorem relativeHead_congr (M N : Subgroup G) [M.Normal] [N.Normal] (h : M = N) :
    Module.finrank (ZMod p) (primeRelativeCharacters p M) =
      Module.finrank (ZMod p) (primeRelativeCharacters p N) := by
  subst N
  rfl

/-- Properness makes the entire vanishing space nonzero. Its exact star
dimension formula then identifies its common radical with the original
head dimension. The same literal N is canceled from both quotient orders. -/
theorem starDerived_intermediate_invariants
    (hker : (primeAbelianizationGroupMap p G).ker = commutator G)
    {U : Type*} [AddCommGroup U] [Module (ZMod p) U] [FiniteDimensional (ZMod p) U]
    (eChars : primeRelativeCharacters p (commutator G) ≃ₗ[ZMod p] Module.Dual (ZMod p) U)
    (eV : PrimeAbelianization p G ≃ₗ[ZMod p] U × ZMod p)
    (hform : ∀ χ x y, derivedEvaluationBilinearMap p hker χ x y =
      starAlternatingFamily (eChars χ) (eV x) (eV y))
    (d : ℕ) (hd : Module.finrank (ZMod p) U = d)
    {ι κ : Type*} {ambient : ι → G} {radicalGenerators : κ → G} {n : ℕ}
    (C : NormalSubgroupSaturationCertificate (commutator G)
      (primeRelativeRadical p (commutator G)) ambient radicalGenerators n)
    (hne : C.NonemptyWords) (r a m : ℕ)
    (hcardR : Nat.card (primeRelativeRadical p (commutator G)) = p ^ r)
    (hheadR : Module.finrank (ZMod p)
      (primeRelativeCharacters p (primeRelativeRadical p (commutator G))) = a)
    (hmaxR : primeNormalHeadMax p (primeRelativeRadical p (commutator G)) = m)
    (N : Subgroup G) [N.Normal]
    (hRN : primeRelativeRadical p (commutator G) < N) (hND : N < commutator G) :
    PrimeDerivedStarIntermediateInvariants p hker N r a m d := by
  let t := Module.finrank (ZMod p) (primeRelativeCharacters p N)
  let ell := Module.finrank (ZMod p) (derivedCharactersVanishingOn p N)
  have hrad : primeRelativeRadical p N = primeRelativeRadical p (commutator G) :=
    C.relativeRadical_eq p hne N hND.le (not_le_of_gt hRN)
  have hchars : Module.finrank (ZMod p) (primeRelativeCharacters p (commutator G)) = d := by
    simpa only [Subspace.dual_finrank_eq, hd] using eChars.finrank_eq
  have hsum : ell + t = d := by
    have h := primeRelativeVanishing_finrank_add_head_of_radical_eq p
      (commutator G) N hND.le hrad
    rw [hchars] at h
    exact h
  have hDcard : Nat.card (commutator G) = p ^ ell * Nat.card N :=
    primeRelativeVanishing_card_factorization p (commutator G) N hND.le hRN.le
  have ht0 : t ≠ 0 := by
    intro hz
    have hc := primeRelativeRadical_card_factorization p N
    change Nat.card N = p ^ t * Nat.card (primeRelativeRadical p N) at hc
    rw [hz, pow_zero, one_mul, hrad] at hc
    exact hRN.ne (Subgroup.eq_of_le_of_card_ge hRN.le hc.le)
  have hell0 : ell ≠ 0 := by
    intro hz
    rw [hz, pow_zero, one_mul] at hDcard
    exact hND.ne (Subgroup.eq_of_le_of_card_ge hND.le hDcard.le)
  have hP : derivedCharactersVanishingOn p N ≠ ⊥ := by
    intro hz
    apply hell0
    change Module.finrank (ZMod p) (derivedCharactersVanishingOn p N) = 0
    rw [hz, finrank_bot]
  have hcommon : Module.finrank (ZMod p) (derivedVanishingCommonRadical p hker N) = t := by
    have h := linearFamilyCommonRadical_finrank_add_parameter_eq_of_star
      (derivedEvaluationBilinearMap p hker) eChars eV hform
      (derivedCharactersVanishingOn p N) hP
    change ell + Module.finrank (ZMod p) (derivedVanishingCommonRadical p hker N) =
      Module.finrank (ZMod p) U at h
    rw [hd] at h
    omega
  have hcard : Nat.card N = p ^ (r + t) := by
    rw [primeRelativeRadical_card_factorization p N, hrad, hcardR,
      pow_add, Nat.mul_comm]
  have hmax : primeNormalHeadMax p N = max m t := by
    rw [C.normalHeadMax_eq_max p hne N hND.le (not_le_of_gt hRN), hmaxR]
  have hcenter : Nat.card (Subgroup.center (G ⧸ N)) = p ^ d := by
    have hc := quotientCenter_card_mul N
    rw [quotientCenterPreimage_vanishing_card p hker N hND.le hRN.le,
      hcommon, hDcard] at hc
    apply Nat.eq_of_mul_eq_mul_right (Nat.card_pos (α := N))
    calc
      Nat.card (Subgroup.center (G ⧸ N)) * Nat.card N =
          p ^ t * (p ^ ell * Nat.card N) := hc
      _ = p ^ (ell + t) * Nat.card N := by
        rw [pow_add]
        ac_rfl
      _ = p ^ d * Nat.card N := by rw [hsum]
  have hderived : Nat.card (commutator (G ⧸ N)) = p ^ (d - t) := by
    have hc := quotientCommutator_card_mul_inf N
    rw [inf_eq_left.mpr hND.le] at hc
    have he : Nat.card (commutator (G ⧸ N)) = p ^ ell :=
      Nat.eq_of_mul_eq_mul_right (Nat.card_pos (α := N)) (hc.trans hDcard)
    rwa [show ell = d - t by omega] at he
  exact ⟨hrad, by omega, by omega, hsum, hcard, hmax,
    (relativeHead_congr p _ _ hrad).trans hheadR, hcommon, hcenter, hderived⟩

end SymmetricSubgroupAsymptotics

