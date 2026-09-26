import SymmetricSubgroupAsymptotics.PGroupNormalIndexP

/-! Nonzero invariant characters on strict original normal intervals in
finite p-groups. A whole-ambient normal index-p top step provides the
actual character. Its mapped kernel contains the given lower subgroup.
In particular every proper original normal subgroup of G' is annihilated
by a nonzero whole-G invariant character of the actual G'. -/
set_option autoImplicit false
noncomputable section

namespace SymmetricSubgroupAsymptotics

variable {G : Type*} [Group G] [Finite G] {p : ℕ} [Fact p.Prime]

/-- A strict original normal interval has a nonzero whole-ambient invariant
character whose literal mapped kernel is an intermediate subgroup of
index p. Both interval endpoints and all conjugations remain in G. -/
theorem pGroup_normal_interval_character (hG : IsPGroup p G)
    (B M : Subgroup G) [B.Normal] [M.Normal] (hBM : B < M) :
    ∃ χ : primeRelativeCharacters p M, χ ≠ 0 ∧
      B ≤ (AddMonoidHom.toMultiplicativeRight χ.1).ker.map M.subtype ∧
      (AddMonoidHom.toMultiplicativeRight χ.1).ker.map M.subtype < M ∧
      ((AddMonoidHom.toMultiplicativeRight χ.1).ker.map M.subtype).relIndex M = p := by
  obtain ⟨J, hJ, hBJ, hJM, hindex⟩ :=
    pGroup_normal_interval_top_step hG B M hBM
  letI : J.Normal := hJ
  obtain ⟨χ, hχ, hker⟩ :=
    pGroup_normal_index_p_character hG J M hJM.le hindex
  refine ⟨χ, hχ, ?_, ?_, ?_⟩
  · rw [hker]
    exact hBJ
  · rw [hker]
    exact hJM
  · rw [hker]
    exact hindex

/-- The character vanishes on every original element of the lower
subgroup, with no replacement quotient or enumeration in the statement. -/
theorem pGroup_exists_nonzero_relativeCharacter_vanishing (hG : IsPGroup p G)
    (B M : Subgroup G) [B.Normal] [M.Normal] (hBM : B < M) :
    ∃ χ : primeRelativeCharacters p M, χ ≠ 0 ∧
      ∀ m : M, (m : G) ∈ B → χ.1 (Additive.ofMul m) = 0 := by
  obtain ⟨χ, hχ, hB, _, _⟩ := pGroup_normal_interval_character hG B M hBM
  refine ⟨χ, hχ, ?_⟩
  intro m hm
  obtain ⟨n, hn, he⟩ := hB hm
  have hnm : n = m := Subtype.ext he
  subst n
  exact hn

/-- A proper original normal subgroup of the actual derived group
admits a nonzero whole-G invariant derived character annihilating it. -/
theorem pGroup_exists_nonzero_derivedCharacter_vanishing (hG : IsPGroup p G)
    (B : Subgroup G) [B.Normal] (hBD : B < commutator G) :
    ∃ χ : primeRelativeCharacters p (commutator G), χ ≠ 0 ∧
      ∀ d : commutator G, (d : G) ∈ B → χ.1 (Additive.ofMul d) = 0 :=
  pGroup_exists_nonzero_relativeCharacter_vanishing hG B (commutator G) hBD

end SymmetricSubgroupAsymptotics
