import SymmetricSubgroupAsymptotics.BinaryCarrierRadicalCenter16T1547

/-! Four exact order profiles cover EVERY whole-original-group normal
subgroup inside the actual relative derived radical of 16T1547. They
follow from the central order-two subgroup, exact relative radicals, and
original quotient-center identities; no normal-plane menu is supplied. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
open scoped commutatorElement

namespace SymmetricSubgroupAsymptotics.BinaryCarrierRadicalProfiles16T1547

abbrev Original := BinaryCarrierRadicalStructure16T1547.Original
abbrev D := commutator Original
abbrev R := primeRelativeRadical 2 D
abbrev Z := BinaryCarrierRadicalStructure16T1547.Z
private abbrev g := BinaryActionData16.node1547Generators
private abbrev ambient := closureGenerators g

private theorem head_congr (M N : Subgroup Original) [M.Normal] [N.Normal] (h : M = N) :
    Module.finrank (ZMod 2) (primeRelativeCharacters 2 M) =
      Module.finrank (ZMod 2) (primeRelativeCharacters 2 N) := by
  subst N
  rfl

theorem radical_bot : primeRelativeRadical 2 (⊥ : Subgroup Original) = ⊥ :=
  le_antisymm (primeRelativeRadical_le 2 ⊥) bot_le

theorem radical_Z : primeRelativeRadical 2 Z = ⊥ := by
  apply le_antisymm _ bot_le
  apply primeRelativeRadical_le_of_finite_generator_tests 2 Z
    ambient (closureGenerators_full g) BinaryCarrierRadicalHead16T1547.centralGenerator rfl ⊥
  · intro i
    change BinaryCarrierDerivedRadical16T1547.elements 1 ^ 2 = 1
    exact BinaryCarrierRadicalStructure16T1547.rows_square 1
  · intro i j
    change ⁅BinaryCarrierDerivedRadical16T1547.elements 1, ambient j⁆ = 1
    apply commutatorElement_eq_one_iff_mul_comm.mpr
    exact (Subgroup.mem_center_iff.mp
      BinaryCarrierRadicalStructure16T1547.centralGenerator_mem_center (ambient j)).symm

theorem head_bot : Module.finrank (ZMod 2)
    (primeRelativeCharacters 2 (⊥ : Subgroup Original)) = 0 := by
  have h := primeRelativeRadical_card_factorization 2 (⊥ : Subgroup Original)
  rw [radical_bot, Subgroup.card_bot, mul_one] at h
  apply Nat.pow_right_injective (by decide : 1 < (2 : ℕ))
  exact h.symm

theorem head_Z : Module.finrank (ZMod 2) (primeRelativeCharacters 2 Z) = 1 := by
  have h := primeRelativeRadical_card_factorization 2 Z
  rw [radical_Z, BinaryCarrierRadicalHead16T1547.card_Z, Subgroup.card_bot, mul_one] at h
  apply Nat.pow_right_injective (by decide : 1 < (2 : ℕ))
  exact h.symm

theorem head_R : Module.finrank (ZMod 2) (primeRelativeCharacters 2 R) = 2 := by
  have h : Nat.card R =
      2 ^ Module.finrank (ZMod 2) (primeRelativeCharacters 2 R) *
        Nat.card (primeRelativeRadical 2 R) := primeRelativeRadical_card_factorization 2 R
  rw [BinaryCarrierRadicalStructure16T1547.relativeRadical_eq_Z,
    BinaryCarrierDerivedRadical16T1547.card_relative_radical,
    BinaryCarrierRadicalHead16T1547.card_Z] at h
  apply Nat.pow_right_injective (by decide : 1 < (2 : ℕ))
  change 2 ^ Module.finrank (ZMod 2) (primeRelativeCharacters 2 R) = 4
  omega

theorem normalHeadMax_bot : primeNormalHeadMax 2 (⊥ : Subgroup Original) = 0 := by
  apply Nat.eq_zero_of_le_zero
  exact (primeNormalHeadMax_le_log_card 2 (⊥ : Subgroup Original)).trans
    (by rw [Subgroup.card_bot]; decide)

theorem normalHeadMax_Z : primeNormalHeadMax 2 Z = 1 := by
  apply le_antisymm
  · exact (primeNormalHeadMax_le_log_card 2 Z).trans
      (by rw [BinaryCarrierRadicalHead16T1547.card_Z]; decide)
  · have h := primeRelativeHead_le_normalHeadMax 2 Z Z le_rfl
    rwa [head_Z] at h

theorem normalHeadMax_R : primeNormalHeadMax 2 R = 2 := by
  apply le_antisymm BinaryCarrierRadicalHead16T1547.normalHeadMax_le_two
  have h := primeRelativeHead_le_normalHeadMax 2 R R le_rfl
  rwa [head_R] at h

theorem eq_bot_or_eq_Z_of_le (M : Subgroup Original) (hM : M ≤ Z) : M = ⊥ ∨ M = Z := by
  have hc : Nat.card M ≤ 2 := by
    have h := Subgroup.card_le_of_le hM
    rwa [BinaryCarrierRadicalHead16T1547.card_Z] at h
  by_cases hsmall : Nat.card M ≤ 1
  · exact Or.inl (M.eq_bot_of_card_le hsmall)
  · exact Or.inr (Subgroup.eq_of_le_of_card_ge hM
      (by rw [BinaryCarrierRadicalHead16T1547.card_Z]; omega))

theorem normalHeadMax_eq_one_of_card_four (M : Subgroup Original) [M.Normal]
    (hM : M ≤ R) (hcard : Nat.card M = 4)
    (hhead : Module.finrank (ZMod 2) (primeRelativeCharacters 2 M) = 1) :
    primeNormalHeadMax 2 M = 1 := by
  apply le_antisymm
  · apply (primeNormalHeadMax_le_iff 2 M 1).mpr
    intro B _ hBM
    by_cases hBZ : B ≤ Z
    · have h := primeRelativeHead_le_normalHeadMax 2 Z B hBZ
      rwa [normalHeadMax_Z] at h
    · have hfactor : Nat.card B =
          2 ^ Module.finrank (ZMod 2) (primeRelativeCharacters 2 B) * 2 :=
        BinaryCarrierRadicalStructure16T1547.card_eq_pow_head_mul_two B (hBM.trans hM) hBZ
      have hbound := Subgroup.card_le_of_le hBM
      rw [hcard] at hbound
      by_contra hbad
      have hp : 2 ^ 2 ≤ 2 ^ Module.finrank (ZMod 2) (primeRelativeCharacters 2 B) :=
        Nat.pow_le_pow_right (by decide) (by omega)
      change 4 ≤ 2 ^ Module.finrank (ZMod 2) (primeRelativeCharacters 2 B) at hp
      omega
  · have h := primeRelativeHead_le_normalHeadMax 2 M M le_rfl
    rwa [hhead] at h

/-- The middle alternative describes every order-four normal plane at
once; neither its identity nor a list of planes is part of the input. -/
theorem normal_cases (M : Subgroup Original) [M.Normal] (hM : M ≤ R) :
    M = ⊥ ∨ M = Z ∨
      (Nat.card M = 4 ∧ Module.finrank (ZMod 2) (primeRelativeCharacters 2 M) = 1 ∧
        Z ≤ M ∧ ¬ R ≤ M ∧ ¬ M ≤ Z) ∨ M = R := by
  by_cases hMZ : M ≤ Z
  · rcases eq_bot_or_eq_Z_of_le M hMZ with h | h
    · exact Or.inl h
    · exact Or.inr (Or.inl h)
  · have hZM := (BinaryCarrierRadicalStructure16T1547.normal_comparable M hM).resolve_left hMZ
    have hfactor : Nat.card M =
        2 ^ Module.finrank (ZMod 2) (primeRelativeCharacters 2 M) * 2 :=
      BinaryCarrierRadicalStructure16T1547.card_eq_pow_head_mul_two M hM hMZ
    have hhead : Module.finrank (ZMod 2) (primeRelativeCharacters 2 M) ≤ 2 :=
      BinaryCarrierRadicalHead16T1547.relativeHead_le_two M hM
    have hnzero : Module.finrank (ZMod 2) (primeRelativeCharacters 2 M) ≠ 0 := by
      intro hz
      rw [hz] at hfactor
      have he : Z = M := Subgroup.eq_of_le_of_card_ge hZM
        (by rw [BinaryCarrierRadicalHead16T1547.card_Z, hfactor]; decide)
      exact hMZ he.symm.le
    have hcases : Module.finrank (ZMod 2) (primeRelativeCharacters 2 M) = 1 ∨
        Module.finrank (ZMod 2) (primeRelativeCharacters 2 M) = 2 := by omega
    rcases hcases with h1 | h2
    · have hc : Nat.card M = 4 := by rw [h1] at hfactor; exact hfactor
      have hnot : ¬ R ≤ M := by
        intro hRM
        have h := Subgroup.card_le_of_le hRM
        rw [BinaryCarrierDerivedRadical16T1547.card_relative_radical, hc] at h
        omega
      exact Or.inr (Or.inr (Or.inl ⟨hc, h1, hZM, hnot, hMZ⟩))
    · have hc : Nat.card M = 8 := by rw [h2] at hfactor; exact hfactor
      exact Or.inr (Or.inr (Or.inr (Subgroup.eq_of_le_of_card_ge hM
        (by rw [BinaryCarrierDerivedRadical16T1547.card_relative_radical, hc]))))

/-- These are exactly the six original fields, kept independent of the
analytic carrier-peel imports. In particular m uses M∩G′. -/
def profile (M : Subgroup Original) [M.Normal] : ℕ × ℕ × ℕ × ℕ × ℕ × ℕ :=
  (Module.finrank (ZMod 2) (primeRelativeCharacters 2 M), Nat.log 2 (Nat.card M),
    primeNormalHeadMax 2 (M ⊓ D),
    Module.finrank (ZMod 2) (primeRelativeCharacters 2 (primeRelativeRadical 2 M)),
    Nat.log 2 (Nat.card (Subgroup.center (Original ⧸ M))),
    Nat.log 2 (Nat.card (commutator (Original ⧸ M))))

private theorem profile_of_fields (M : Subgroup Original) [M.Normal] (hM : M ≤ R)
    (k n m a c q : ℕ)
    (hk : Module.finrank (ZMod 2) (primeRelativeCharacters 2 M) = k)
    (hn : Nat.card M = 2 ^ n) (hm : primeNormalHeadMax 2 M = m)
    (ha : Module.finrank (ZMod 2) (primeRelativeCharacters 2 (primeRelativeRadical 2 M)) = a)
    (hc : Nat.card (Subgroup.center (Original ⧸ M)) = 2 ^ c)
    (hq : Nat.card (commutator (Original ⧸ M)) = 2 ^ q) :
    profile M = (k,n,m,a,c,q) := by
  have hMD := hM.trans (primeRelativeRadical_le 2 D)
  unfold profile
  rw [hk, hn, inf_eq_left.mpr hMD, hm, ha, hc, hq]
  simp only [Nat.log_pow (by decide : 1 < (2 : ℕ))]

private theorem quotient_derived_card (M : Subgroup Original) [M.Normal] (hM : M ≤ R) :
    Nat.card (commutator (Original ⧸ M)) = 64 / Nat.card M := by
  rw [quotientCommutator_card_eq_div_inf,
    inf_eq_left.mpr (hM.trans (primeRelativeRadical_le 2 D)),
    BinaryCarrierDerivedOrder16T1547.card_commutator]

theorem profile_bot : profile (⊥ : Subgroup Original) = (0,0,0,0,1,6) := by
  apply profile_of_fields ⊥ bot_le 0 0 0 0 1 6 head_bot
    (by rw [Subgroup.card_bot]; rfl) normalHeadMax_bot
  · exact (head_congr _ _ radical_bot).trans head_bot
  · have h := quotientCenter_card_mul (⊥ : Subgroup Original)
    rw [BinaryCarrierRadicalCenter16T1547.centerPreimage_bot_eq_Z,
      BinaryCarrierRadicalHead16T1547.card_Z, Subgroup.card_bot, mul_one] at h
    exact h
  · rw [quotient_derived_card ⊥ bot_le, Subgroup.card_bot]
    rfl

theorem profile_Z : profile Z = (1,1,1,0,2,5) := by
  have hZR := BinaryCarrierRadicalHead16T1547.Z_le_radical
  have hnot : ¬ R ≤ Z := by
    intro h
    have hc := Subgroup.card_le_of_le h
    rw [BinaryCarrierDerivedRadical16T1547.card_relative_radical,
      BinaryCarrierRadicalHead16T1547.card_Z] at hc
    omega
  apply profile_of_fields Z hZR 1 1 1 0 2 5 head_Z
    BinaryCarrierRadicalHead16T1547.card_Z normalHeadMax_Z
  · exact (head_congr _ _ radical_Z).trans head_bot
  · have h : Nat.card (Subgroup.center (Original ⧸ Z)) * Nat.card Z = 8 :=
      BinaryCarrierRadicalCenter16T1547.center_card_mul_of_between Z hZR le_rfl hnot
    rw [BinaryCarrierRadicalHead16T1547.card_Z] at h
    change Nat.card (Subgroup.center (Original ⧸ Z)) = 4
    omega
  · rw [quotient_derived_card Z hZR, BinaryCarrierRadicalHead16T1547.card_Z]
    rfl

theorem profile_R : profile R = (2,3,2,1,3,3) := by
  apply profile_of_fields R le_rfl 2 3 2 1 3 3 head_R
    BinaryCarrierDerivedRadical16T1547.card_relative_radical normalHeadMax_R
  · exact (head_congr _ _ BinaryCarrierRadicalStructure16T1547.relativeRadical_eq_Z).trans head_Z
  · have h := quotientCenter_card_mul R
    rw [BinaryCarrierRadicalCenter16T1547.centerPreimage_radical_eq_derived,
      BinaryCarrierDerivedOrder16T1547.card_commutator,
      BinaryCarrierDerivedRadical16T1547.card_relative_radical] at h
    omega
  · rw [quotient_derived_card R le_rfl, BinaryCarrierDerivedRadical16T1547.card_relative_radical]
    rfl

theorem profile_of_card_four (M : Subgroup Original) [M.Normal] (hM : M ≤ R)
    (hcard : Nat.card M = 4)
    (hhead : Module.finrank (ZMod 2) (primeRelativeCharacters 2 M) = 1)
    (hZM : Z ≤ M) (hnot : ¬ R ≤ M) (hMZ : ¬ M ≤ Z) :
    profile M = (1,2,1,1,1,4) := by
  apply profile_of_fields M hM 1 2 1 1 1 4 hhead hcard
    (normalHeadMax_eq_one_of_card_four M hM hcard hhead)
  · exact (head_congr _ _
      (BinaryCarrierRadicalStructure16T1547.relativeRadical_eq_Z_of_not_le M hM hMZ)).trans head_Z
  · have h : Nat.card (Subgroup.center (Original ⧸ M)) * Nat.card M = 8 :=
      BinaryCarrierRadicalCenter16T1547.center_card_mul_of_between M hM hZM hnot
    rw [hcard] at h
    change Nat.card (Subgroup.center (Original ⧸ M)) = 2
    omega
  · rw [quotient_derived_card M hM, hcard]
    rfl

/-- Universal actual coverage by four exact profiles, not a selected
normal menu or an assertion that all six normals were enumerated. -/
theorem normal_profile (M : Subgroup Original) [M.Normal] (hM : M ≤ R) :
    profile M = (0,0,0,0,1,6) ∨ profile M = (1,1,1,0,2,5) ∨
      profile M = (1,2,1,1,1,4) ∨ profile M = (2,3,2,1,3,3) := by
  rcases normal_cases M hM with h | h | h | h
  · subst M
    exact Or.inl profile_bot
  · subst M
    exact Or.inr (Or.inl profile_Z)
  · exact Or.inr (Or.inr (Or.inl (profile_of_card_four M hM h.1 h.2.1
      h.2.2.1 h.2.2.2.1 h.2.2.2.2)))
  · subst M
    exact Or.inr (Or.inr (Or.inr profile_R))

end SymmetricSubgroupAsymptotics.BinaryCarrierRadicalProfiles16T1547
