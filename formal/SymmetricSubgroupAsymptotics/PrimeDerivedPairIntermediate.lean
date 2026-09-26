import SymmetricSubgroupAsymptotics.LinearFamilyPairKernels
import SymmetricSubgroupAsymptotics.PrimeDerivedVanishingCenter
import SymmetricSubgroupAsymptotics.PrimeRelativeVanishingOrder
import SymmetricSubgroupAsymptotics.NormalSubgroupSaturationHeadBounds
import Lean.Elab.Tactic.Omega

/-! Exact invariants of arbitrary original normals strictly between the
relative derived radical and the derived group in a three-parameter pair
family. Complete vanishing subspaces and actual nonempty saturation words
replace any enumeration of intermediate planes. -/
set_option autoImplicit false
noncomputable section

namespace SymmetricSubgroupAsymptotics

variable (p : ℕ) [Fact p.Prime] {G : Type*} [Group G] [Finite G]

def pairIntermediateParameterDimension (N : Subgroup G) : ℕ :=
  Module.finrank (ZMod p) (derivedCharactersVanishingOn p N)

/-- All fields refer to the same original N and its original quotient.
The parameters r,a,m record actual order/head/normal-head of R_D. -/
structure PrimeDerivedPairIntermediateInvariants
    (hker : (primeAbelianizationGroupMap p G).ker = commutator G)
    (N : Subgroup G) [N.Normal] (r a m : ℕ) : Prop where
  parameter_cases : pairIntermediateParameterDimension p N = 1 ∨
    pairIntermediateParameterDimension p N = 2
  relativeRadical_eq : primeRelativeRadical p N = primeRelativeRadical p (commutator G)
  head_eq : Module.finrank (ZMod p) (primeRelativeCharacters p N) =
    3 - pairIntermediateParameterDimension p N
  card_eq : Nat.card N = p ^ (r + (3 - pairIntermediateParameterDimension p N))
  normalHeadMax_eq : primeNormalHeadMax p N =
    max m (3 - pairIntermediateParameterDimension p N)
  radicalHead_eq : Module.finrank (ZMod p)
    (primeRelativeCharacters p (primeRelativeRadical p N)) = a
  common_finrank : Module.finrank (ZMod p) (derivedVanishingCommonRadical p hker N) =
    if pairIntermediateParameterDimension p N = 1 then 2 else 0
  center_card : Nat.card (Subgroup.center (G ⧸ N)) =
    p ^ (pairIntermediateParameterDimension p N +
      if pairIntermediateParameterDimension p N = 1 then 2 else 0)
  derived_card : Nat.card (commutator (G ⧸ N)) =
    p ^ pairIntermediateParameterDimension p N

private theorem relativeHead_congr (M N : Subgroup G) [M.Normal] [N.Normal] (h : M = N) :
    Module.finrank (ZMod p) (primeRelativeCharacters p M) =
      Module.finrank (ZMod p) (primeRelativeCharacters p N) := by
  subst N
  rfl

/-- Nonempty saturation supplies the actual radical and all-normal
maximum. The dimension cases follow from strict subgroup containment and
actual cardinalities; no p-group premise or normal list is required. -/
theorem pairDerived_intermediate_invariants
    (hker : (primeAbelianizationGroupMap p G).ker = commutator G)
    (hchars : Module.finrank (ZMod p) (primeRelativeCharacters p (commutator G)) = 3)
    (hsingle : ∀ χ : primeRelativeCharacters p (commutator G), χ ≠ 0 →
      Module.finrank (ZMod p) (derivedEvaluationBilinearMap p hker χ).ker = 2)
    (hpair : ∀ v : Fin 2 → primeRelativeCharacters p (commutator G),
      LinearIndependent (ZMod p) v →
        (derivedEvaluationBilinearMap p hker (v 0)).ker ⊓
          (derivedEvaluationBilinearMap p hker (v 1)).ker = ⊥)
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
    PrimeDerivedPairIntermediateInvariants p hker N r a m := by
  let ell := pairIntermediateParameterDimension p N
  have hrad : primeRelativeRadical p N = primeRelativeRadical p (commutator G) :=
    C.relativeRadical_eq p hne N hND.le (not_le_of_gt hRN)
  have hsum : ell + Module.finrank (ZMod p) (primeRelativeCharacters p N) = 3 := by
    have h := primeRelativeVanishing_finrank_add_head_of_radical_eq p
      (commutator G) N hND.le hrad
    rw [hchars] at h
    exact h
  have hDcard : Nat.card (commutator G) = p ^ ell * Nat.card N :=
    primeRelativeVanishing_card_factorization p (commutator G) N hND.le hRN.le
  have hhead0 : Module.finrank (ZMod p) (primeRelativeCharacters p N) ≠ 0 := by
    intro hz
    have hc := primeRelativeRadical_card_factorization p N
    rw [hz, pow_zero, one_mul, hrad] at hc
    exact hRN.ne (Subgroup.eq_of_le_of_card_ge hRN.le hc.le)
  have hell0 : ell ≠ 0 := by
    intro hz
    rw [hz, pow_zero, one_mul] at hDcard
    exact hND.ne (Subgroup.eq_of_le_of_card_ge hND.le hDcard.le)
  have hcases : ell = 1 ∨ ell = 2 := by omega
  have hhead : Module.finrank (ZMod p) (primeRelativeCharacters p N) = 3 - ell := by
    omega
  have hcard : Nat.card N = p ^ (r + (3 - ell)) := by
    rw [primeRelativeRadical_card_factorization p N, hrad, hhead, hcardR,
      pow_add, Nat.mul_comm]
  have hmax : primeNormalHeadMax p N = max m (3 - ell) := by
    rw [C.normalHeadMax_eq_max p hne N hND.le (not_le_of_gt hRN), hmaxR, hhead]
  have hcommon : Module.finrank (ZMod p) (derivedVanishingCommonRadical p hker N) =
      if ell = 1 then 2 else 0 := by
    rcases hcases with h1 | h2
    · have h := linearFamily_iInf_ker_finrank_of_finrank_one
        (derivedEvaluationBilinearMap p hker) (derivedCharactersVanishingOn p N) 2 hsingle h1
      change Module.finrank (ZMod p) (derivedVanishingCommonRadical p hker N) = 2 at h
      simpa only [h1, if_pos rfl] using h
    · have hz := linearFamily_iInf_ker_eq_bot_of_two_le
        (derivedEvaluationBilinearMap p hker) (derivedCharactersVanishingOn p N) hpair
        (show 2 ≤ ell by omega)
      change derivedVanishingCommonRadical p hker N = ⊥ at hz
      rw [hz, finrank_bot]
      simp [h2]
  have hcenter : Nat.card (Subgroup.center (G ⧸ N)) =
      p ^ (ell + if ell = 1 then 2 else 0) := by
    have hc := quotientCenter_card_mul N
    rw [quotientCenterPreimage_vanishing_card p hker N hND.le hRN.le,
      hcommon, hDcard] at hc
    apply Nat.eq_of_mul_eq_mul_right (Nat.card_pos (α := N))
    calc
      Nat.card (Subgroup.center (G ⧸ N)) * Nat.card N =
          p ^ (if ell = 1 then 2 else 0) * (p ^ ell * Nat.card N) := hc
      _ = p ^ (ell + if ell = 1 then 2 else 0) * Nat.card N := by
        rw [pow_add]
        ac_rfl
  have hderived : Nat.card (commutator (G ⧸ N)) = p ^ ell := by
    have hc := quotientCommutator_card_mul_inf N
    rw [inf_eq_left.mpr hND.le] at hc
    exact Nat.eq_of_mul_eq_mul_right (Nat.card_pos (α := N)) (hc.trans hDcard)
  exact ⟨hcases, hrad, hhead, hcard, hmax,
    (relativeHead_congr p _ _ hrad).trans hheadR, hcommon, hcenter, hderived⟩

end SymmetricSubgroupAsymptotics
