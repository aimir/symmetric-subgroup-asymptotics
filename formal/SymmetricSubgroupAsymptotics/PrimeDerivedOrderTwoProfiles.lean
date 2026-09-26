import SymmetricSubgroupAsymptotics.NormalOrderTwo
import SymmetricSubgroupAsymptotics.NormalSubgroupSaturationCenter
import SymmetricSubgroupAsymptotics.PrimeDerivedIntersectionForms

/-! Two universal actual profiles below an order-two derived relative
radical. Original pair-form separation and nonempty commutator saturation
determine the original quotient-center preimages; cardinal identities
then retain the same normal subgroup in both quotient slopes. -/
set_option autoImplicit false
noncomputable section
open scoped commutatorElement

namespace SymmetricSubgroupAsymptotics.PrimeDerivedOrderTwoProfiles

variable {G : Type*} [Group G] [Finite G]

abbrev radical : Subgroup G := primeRelativeRadical 2 (commutator G)

/-- All six literal fields, independent of analytic carrier imports. -/
def profile (M : Subgroup G) [M.Normal] : ℕ × ℕ × ℕ × ℕ × ℕ × ℕ :=
  (Module.finrank (ZMod 2) (primeRelativeCharacters 2 M), Nat.log 2 (Nat.card M),
    primeNormalHeadMax 2 (M ⊓ commutator G),
    Module.finrank (ZMod 2) (primeRelativeCharacters 2 (primeRelativeRadical 2 M)),
    Nat.log 2 (Nat.card (Subgroup.center (G ⧸ M))),
    Nat.log 2 (Nat.card (commutator (G ⧸ M))))

private theorem head_congr (M N : Subgroup G) [M.Normal] [N.Normal] (h : M = N) :
    Module.finrank (ZMod 2) (primeRelativeCharacters 2 M) =
      Module.finrank (ZMod 2) (primeRelativeCharacters 2 N) := by
  subst N
  rfl

private theorem profile_of_fields (M : Subgroup G) [M.Normal] (hM : M ≤ commutator G)
    (k n m a c q : ℕ)
    (hk : Module.finrank (ZMod 2) (primeRelativeCharacters 2 M) = k)
    (hn : Nat.card M = 2 ^ n) (hm : primeNormalHeadMax 2 M = m)
    (ha : Module.finrank (ZMod 2) (primeRelativeCharacters 2 (primeRelativeRadical 2 M)) = a)
    (hc : Nat.card (Subgroup.center (G ⧸ M)) = 2 ^ c)
    (hq : Nat.card (commutator (G ⧸ M)) = 2 ^ q) :
    profile M = (k,n,m,a,c,q) := by
  unfold profile
  rw [hk, hn, inf_eq_left.mpr hM, hm, ha, hc, hq]
  simp only [Nat.log_pow (by decide : 1 < (2 : ℕ))]

theorem derived_head_add_one_eq (d : ℕ)
    (hD : Nat.card (commutator G) = 2 ^ d)
    (hR : Nat.card (radical (G := G)) = 2) :
    Module.finrank (ZMod 2) (primeRelativeCharacters 2 (commutator G)) + 1 = d := by
  have h : Nat.card (commutator G) =
      2 ^ Module.finrank (ZMod 2) (primeRelativeCharacters 2 (commutator G)) *
        Nat.card (radical (G := G)) := primeRelativeRadical_card_factorization 2 (commutator G)
  rw [hD, hR] at h
  apply Nat.pow_right_injective (by decide : 1 < (2 : ℕ))
  simpa only [pow_succ] using h.symm

variable (d : ℕ) (hD : Nat.card (commutator G) = 2 ^ d)
    (hR : Nat.card (radical (G := G)) = 2) (hd : 3 ≤ d)
    (hker : (primeAbelianizationGroupMap 2 G).ker = commutator G)
    (hpair : ∀ v : Fin 2 → primeRelativeCharacters 2 (commutator G),
      LinearIndependent (ZMod 2) v →
      (derivedEvaluationBilinearMap 2 hker (v 0)).ker ⊓
        (derivedEvaluationBilinearMap 2 hker (v 1)).ker = ⊥)

include hD hR hd hker hpair

/-- The lower bound on the full character dimension is proved from the
actual orders of D and R. Every character vanishes on any M≤R. -/
theorem centerPreimage_le_derived (M : Subgroup G) [M.Normal]
    (hM : M ≤ radical (G := G)) : quotientCenterPreimage M ≤ commutator G := by
  apply (primeDerivedImage_eq_bot_iff_le_commutator 2 hker _).mp
  by_contra hW
  have hle := Submodule.finrank_mono
    (derivedCharactersVanishingOn_le_center_joint 2 hker M)
  rw [derivedCharactersVanishingOn_eq_top_of_le_radical 2 M hM, finrank_top] at hle
  have hone := linearJointAnnihilator_finrank_le_one
    (derivedEvaluationBilinearMap 2 hker) (primeDerivedImage 2 (quotientCenterPreimage M))
    hpair hW
  have hrank := derived_head_add_one_eq d hD hR
  omega

theorem centerPreimage_radical_eq_derived :
    quotientCenterPreimage (radical (G := G)) = commutator G := by
  apply le_antisymm (centerPreimage_le_derived d hD hR hd hker hpair _ le_rfl)
  intro x hx
  apply (mem_quotientCenterPreimage_iff_all_commutators (radical (G := G)) x).mpr
  intro g
  exact commutator_mem_primeRelativeRadical 2 (commutator G) ⟨x,hx⟩ g

variable {ι κ : Type*} {ambient : ι → G} {generators : κ → G} {n : ℕ}
    (C : NormalSubgroupSaturationCertificate (commutator G) (radical (G := G))
      ambient generators n) (hne : C.NonemptyWords)
include C hne

/-- Saturation bounds the original center from above; normality and
order two give the matching original central subgroup from below. -/
theorem centerPreimage_bot_eq_radical :
    quotientCenterPreimage (⊥ : Subgroup G) = radical (G := G) := by
  have hnot : ¬ radical (G := G) ≤ (⊥ : Subgroup G) := by
    intro h
    have hc := Subgroup.card_le_of_le h
    rw [hR, Subgroup.card_bot] at hc
    omega
  apply le_antisymm
  · exact C.quotientCenterPreimage_le hne ⊥ hnot
      (centerPreimage_le_derived d hD hR hd hker hpair ⊥ bot_le)
  · intro x hx
    apply (mem_quotientCenterPreimage_iff_all_commutators (⊥ : Subgroup G) x).mpr
    intro g
    change ⁅x,g⁆ = 1
    apply commutatorElement_eq_one_iff_mul_comm.mpr
    exact (Subgroup.mem_center_iff.mp (NormalOrderTwo.le_center _ hR hx) g).symm

theorem profile_bot : profile (⊥ : Subgroup G) = (0,0,0,0,1,d) := by
  apply profile_of_fields ⊥ bot_le 0 0 0 0 1 d
    NormalOrderTwo.relativeHead_bot (by rw [Subgroup.card_bot]; rfl)
    NormalOrderTwo.normalHeadMax_bot
  · exact (head_congr _ _ NormalOrderTwo.relativeRadical_bot).trans NormalOrderTwo.relativeHead_bot
  · have h := quotientCenter_card_mul (⊥ : Subgroup G)
    rw [centerPreimage_bot_eq_radical d hD hR hd hker hpair C hne,
      hR, Subgroup.card_bot, mul_one] at h
    exact h
  · rw [quotientCommutator_card_eq_div_inf, inf_eq_left.mpr bot_le, Subgroup.card_bot, hD,
      Nat.div_one]

theorem profile_radical : profile (radical (G := G)) = (1,1,1,0,d-1,d-1) := by
  have hd1 : 1 ≤ d := by omega
  have hpow : 2 ^ d = 2 ^ (d-1) * 2 := by rw [← pow_succ, Nat.sub_add_cancel hd1]
  have hc : Nat.card (Subgroup.center (G ⧸ radical (G := G))) * 2 = 2 ^ d := by
    have h := quotientCenter_card_mul (radical (G := G))
    rw [centerPreimage_radical_eq_derived d hD hR hd hker hpair, hD, hR] at h
    exact h
  have hg : Nat.card (commutator (G ⧸ radical (G := G))) * 2 = 2 ^ d := by
    have h := quotientCommutator_card_mul_inf (radical (G := G))
    rw [inf_eq_left.mpr (primeRelativeRadical_le 2 (commutator G)), hD, hR] at h
    exact h
  apply profile_of_fields _ (primeRelativeRadical_le 2 (commutator G)) 1 1 1 0 (d-1) (d-1)
    (NormalOrderTwo.relativeHead_eq_one _ hR) hR (NormalOrderTwo.normalHeadMax_eq_one _ hR)
  · exact (head_congr _ _ (NormalOrderTwo.relativeRadical_eq_bot _ hR)).trans
      NormalOrderTwo.relativeHead_bot
  · exact Nat.eq_of_mul_eq_mul_right (by decide : 0 < (2 : ℕ)) (hc.trans hpow)
  · exact Nat.eq_of_mul_eq_mul_right (by decide : 0 < (2 : ℕ)) (hg.trans hpow)

/-- Exhaustive original-normal coverage follows from order two; no
finite normal catalogue or choice of a nonidentity generator is supplied. -/
theorem normal_profile (M : Subgroup G) [M.Normal] (hM : M ≤ radical (G := G)) :
    profile M = (0,0,0,0,1,d) ∨ profile M = (1,1,1,0,d-1,d-1) := by
  rcases NormalOrderTwo.subgroup_cases (radical (G := G)) hR M hM with h | h
  · subst M
    exact Or.inl (profile_bot d hD hR hd hker hpair C hne)
  · subst M
    exact Or.inr (profile_radical d hD hR hd hker hpair C hne)

end SymmetricSubgroupAsymptotics.PrimeDerivedOrderTwoProfiles
