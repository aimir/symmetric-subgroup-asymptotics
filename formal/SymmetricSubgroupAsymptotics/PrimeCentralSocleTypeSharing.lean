import SymmetricSubgroupAsymptotics.PrimeCentralSocleRelativeHead

/-!
# Sharing the central prime socle with all remaining types

This file performs the type-sharing part of the fixed-frame argument.  The
central `p`-primary minimal normal factors are separated from the
noncentral `p`-primary factors.  The latter have full commutator with the
ambient group, while the former centralize it, so the two families have no
common ambient normal quotient and share padded generator positions.  The
existing prime-primary split then shares the same positions with every
non-`p` socle type.
-/

set_option autoImplicit false
noncomputable section
open scoped Classical
open scoped commutatorElement

namespace SymmetricSubgroupAsymptotics

variable (p : ℕ) [Fact p.Prime]
variable {G : Type} [Group G] [Finite G]

/-- The noncentral `p`-primary ambient minimal-normal factors. -/
abbrev noncentralPrimeSoclePart (p : ℕ) (G : Type)
    [Group G] [Finite G] : Subgroup G :=
  minimalNormalSoclePart G
    (fun M ↦ ¬ M ≤ Subgroup.center G ∧ IsPGroup p M)

/-- A selected family of ambient minimal normal factors is partitioned by
any predicate on those factors. -/
theorem selectedSocleParts_sup_compl
    (R P : Subgroup G → Prop) :
    minimalNormalSoclePart G (fun M ↦ R M ∧ P M) ⊔
        minimalNormalSoclePart G (fun M ↦ R M ∧ ¬ P M) =
      minimalNormalSoclePart G R := by
  apply le_antisymm
  · apply sup_le
    · apply minimalNormalSoclePart_le_of
      intro M hM hMR
      exact minimalNormal_le_minimalNormalSoclePart R M hM hMR.1
    · apply minimalNormalSoclePart_le_of
      intro M hM hMR
      exact minimalNormal_le_minimalNormalSoclePart R M hM hMR.1
  · apply minimalNormalSoclePart_le_of
    intro M hM hMR
    by_cases hP : P M
    · exact (minimalNormal_le_minimalNormalSoclePart
          (fun K : Subgroup G ↦ R K ∧ P K) M hM ⟨hMR, hP⟩).trans
        le_sup_left
    · exact (minimalNormal_le_minimalNormalSoclePart
          (fun K : Subgroup G ↦ R K ∧ ¬ P K) M hM ⟨hMR, hP⟩).trans
        le_sup_right

omit [Fact p.Prime] in
/-- The central/noncentral split recovers the entire `p`-primary socle
part. -/
theorem centralPrimeSoclePart_sup_noncentralPrimeSoclePart :
    centralPrimeSoclePart p G ⊔ noncentralPrimeSoclePart p G =
      minimalNormalSoclePart G (fun M ↦ IsPGroup p M) := by
  have h := selectedSocleParts_sup_compl
    (G := G) (fun M ↦ IsPGroup p M) (fun M ↦ M ≤ Subgroup.center G)
  simpa only [centralPrimeSoclePart, noncentralPrimeSoclePart, and_comm] using h

omit [Fact p.Prime] in
/-- Every noncentral selected minimal-normal factor has full commutator
with the whole ambient group; minimality rules out the zero alternative. -/
theorem commutator_top_noncentralPrimeSoclePart :
    ⁅(⊤ : Subgroup G), noncentralPrimeSoclePart p G⁆ =
      noncentralPrimeSoclePart p G := by
  classical
  apply le_antisymm
  · exact Subgroup.commutator_le_right _ _
  · apply minimalNormalSoclePart_le_of
    intro M hM hdata
    letI : M.Normal := hM.1
    have hfull : ⁅(⊤ : Subgroup G), M⁆ = M := by
      rcases minimalNormal_commutator_full_or_trivial
        (⊤ : Subgroup G) M hM with h | h
      · exact h
      · exfalso
        apply hdata.1
        intro m hm
        apply Subgroup.mem_center_iff.mpr
        intro g
        have hcentral : M ≤ Subgroup.centralizer
            ((⊤ : Subgroup G) : Set G) := by
          rw [← Subgroup.commutator_eq_bot_iff_le_centralizer]
          simpa only [Subgroup.commutator_comm] using h
        exact Subgroup.mem_centralizer_iff.mp (hcentral hm) g
          (show g ∈ (⊤ : Subgroup G) from trivial)
    rw [← hfull]
    exact Subgroup.commutator_mono le_rfl
      (minimalNormal_le_minimalNormalSoclePart
        (fun K : Subgroup G ↦ ¬ K ≤ Subgroup.center G ∧ IsPGroup p K)
        M hM hdata)

omit [Fact p.Prime] in
/-- Central and noncentral `p`-primary types share generator positions by
the intrinsic ambient Goursat theorem. -/
theorem noCommonNormalQuotient_central_noncentralPrimeSocleParts :
    NoCommonNormalQuotient
      (noncentralPrimeSoclePart p G) (centralPrimeSoclePart p G) :=
  noCommonNormalQuotient_of_commutator_full_central
    (⊤ : Subgroup G) _ _
    (commutator_top_noncentralPrimeSoclePart p (G := G))
    ((centralPrimeSoclePart_le_center p (G := G)).trans
      (Subgroup.center_le_centralizer ((⊤ : Subgroup G) : Set G)))

omit [Fact p.Prime] in
/-- The `p`-primary socle costs the maximum of its central and noncentral
parts. -/
theorem normalGen_primePrimarySoclePart_le_max_central_noncentral :
    MarkedC4.normalGen
        (minimalNormalSoclePart G (fun M ↦ IsPGroup p M)) ≤
      max (MarkedC4.normalGen (centralPrimeSoclePart p G))
        (MarkedC4.normalGen (noncentralPrimeSoclePart p G)) := by
  rw [← centralPrimeSoclePart_sup_noncentralPrimeSoclePart p (G := G)]
  have h := normalGen_sup_le_max_of_noCommonNormalQuotient
    (noncentralPrimeSoclePart p G) (centralPrimeSoclePart p G)
    (noCommonNormalQuotient_central_noncentralPrimeSocleParts p (G := G))
  simpa only [sup_comm, max_comm] using h

/-- Three-way fixed-frame endpoint: central `p`, noncentral `p`, and all
non-`p` socle types share one tuple of the largest of their costs. -/
theorem normalGen_finiteGroupSocle_le_max_centralPrime_noncentralPrime_nonPrime :
    MarkedC4.normalGen (finiteGroupSocle G) ≤
      max
        (max (MarkedC4.normalGen (centralPrimeSoclePart p G))
          (MarkedC4.normalGen (noncentralPrimeSoclePart p G)))
        (MarkedC4.normalGen
          (minimalNormalSoclePart G (fun M ↦ ¬ IsPGroup p M))) := by
  refine (normalGen_finiteGroupSocle_le_max_primePrimaryParts p G).trans ?_
  exact max_le_max
    (normalGen_primePrimarySoclePart_le_max_central_noncentral p (G := G))
    le_rfl

end SymmetricSubgroupAsymptotics

end
