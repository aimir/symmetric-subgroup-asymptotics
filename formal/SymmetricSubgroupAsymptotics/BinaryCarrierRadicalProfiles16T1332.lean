import SymmetricSubgroupAsymptotics.BinaryCarrierRadicalCenter16T1332

/-! Every original normal subgroup inside the four-element relative
radical of16T1332 is1, its central order-two subgroup, or the radical
itself. Exact same-subgroup capacity profiles follow without normal
subgroup enumeration. -/
set_option autoImplicit false
noncomputable section
open scoped commutatorElement

namespace SymmetricSubgroupAsymptotics.BinaryCarrierRadicalProfiles16T1332

abbrev Original := BinaryCarrierRadicalStructure16T1332.Original
abbrev D := commutator Original
abbrev R := primeRelativeRadical 2 D
abbrev Z := BinaryCarrierRadicalStructure16T1332.Z
private abbrev g := BinaryActionData16.node1332Generators
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
    ambient (closureGenerators_full g) BinaryCarrierRadicalHead16T1332.centralGenerator rfl ⊥
  · intro i
    change BinaryCarrierDerivedRadical16T1332.elements 1 ^ 2 = 1
    exact BinaryCarrierRadicalStructure16T1332.rows_square 1
  · intro i j
    change ⁅BinaryCarrierDerivedRadical16T1332.elements 1, ambient j⁆ = 1
    apply commutatorElement_eq_one_iff_mul_comm.mpr
    exact (Subgroup.mem_center_iff.mp
      BinaryCarrierRadicalStructure16T1332.centralGenerator_mem_center (ambient j)).symm

theorem head_bot : Module.finrank (ZMod 2)
    (primeRelativeCharacters 2 (⊥ : Subgroup Original)) = 0 := by
  have h := primeRelativeRadical_card_factorization 2 (⊥ : Subgroup Original)
  rw [radical_bot, Subgroup.card_bot, mul_one] at h
  apply Nat.pow_right_injective (by decide : 1 < (2 : ℕ))
  exact h.symm

theorem head_Z : Module.finrank (ZMod 2) (primeRelativeCharacters 2 Z) = 1 := by
  have h := primeRelativeRadical_card_factorization 2 Z
  rw [radical_Z, BinaryCarrierRadicalHead16T1332.card_Z, Subgroup.card_bot, mul_one] at h
  apply Nat.pow_right_injective (by decide : 1 < (2 : ℕ))
  exact h.symm

theorem head_R : Module.finrank (ZMod 2) (primeRelativeCharacters 2 R) = 1 := by
  have h : Nat.card R =
      2 ^ Module.finrank (ZMod 2) (primeRelativeCharacters 2 R) *
        Nat.card (primeRelativeRadical 2 R) := primeRelativeRadical_card_factorization 2 R
  rw [BinaryCarrierRadicalStructure16T1332.relativeRadical_eq_Z,
    BinaryCarrierDerivedRadical16T1332.card_relative_radical,
    BinaryCarrierRadicalHead16T1332.card_Z] at h
  apply Nat.pow_right_injective (by decide : 1 < (2 : ℕ))
  change 2 ^ Module.finrank (ZMod 2) (primeRelativeCharacters 2 R) = 2
  omega

theorem normalHeadMax_bot : primeNormalHeadMax 2 (⊥ : Subgroup Original) = 0 := by
  apply Nat.eq_zero_of_le_zero
  exact (primeNormalHeadMax_le_log_card 2 (⊥ : Subgroup Original)).trans
    (by rw [Subgroup.card_bot]; decide)

theorem normalHeadMax_Z : primeNormalHeadMax 2 Z = 1 := by
  apply le_antisymm
  · exact (primeNormalHeadMax_le_log_card 2 Z).trans
      (by rw [BinaryCarrierRadicalHead16T1332.card_Z]; decide)
  · have h := primeRelativeHead_le_normalHeadMax 2 Z Z le_rfl
    rwa [head_Z] at h

theorem normalHeadMax_R : primeNormalHeadMax 2 R = 1 := by
  apply le_antisymm BinaryCarrierRadicalHead16T1332.normalHeadMax_le_one
  have h := primeRelativeHead_le_normalHeadMax 2 R R le_rfl
  rwa [head_R] at h

theorem eq_bot_or_eq_Z_of_le (M : Subgroup Original) (hM : M ≤ Z) : M = ⊥ ∨ M = Z := by
  have hc : Nat.card M ≤ 2 := by
    have h := Subgroup.card_le_of_le hM
    rwa [BinaryCarrierRadicalHead16T1332.card_Z] at h
  by_cases hsmall : Nat.card M ≤ 1
  · exact Or.inl (M.eq_bot_of_card_le hsmall)
  · exact Or.inr (Subgroup.eq_of_le_of_card_ge hM
      (by rw [BinaryCarrierRadicalHead16T1332.card_Z]; omega))

theorem normal_cases (M : Subgroup Original) [M.Normal] (hM : M ≤ R) :
    M = ⊥ ∨ M = Z ∨ M = R := by
  by_cases hMZ : M ≤ Z
  · rcases eq_bot_or_eq_Z_of_le M hMZ with h | h
    · exact Or.inl h
    · exact Or.inr (Or.inl h)
  · have hZM := (BinaryCarrierRadicalStructure16T1332.normal_comparable M hM).resolve_left hMZ
    have hfactor : Nat.card M =
        2 ^ Module.finrank (ZMod 2) (primeRelativeCharacters 2 M) * 2 :=
      BinaryCarrierRadicalStructure16T1332.card_eq_pow_head_mul_two M hM hMZ
    have hhead : Module.finrank (ZMod 2) (primeRelativeCharacters 2 M) ≤ 1 :=
      BinaryCarrierRadicalHead16T1332.relativeHead_le_one M hM
    have hnzero : Module.finrank (ZMod 2) (primeRelativeCharacters 2 M) ≠ 0 := by
      intro hz
      rw [hz] at hfactor
      have he : Z = M := Subgroup.eq_of_le_of_card_ge hZM
        (by rw [BinaryCarrierRadicalHead16T1332.card_Z, hfactor]; decide)
      exact hMZ he.symm.le
    have h1 : Module.finrank (ZMod 2) (primeRelativeCharacters 2 M) = 1 := by omega
    have hc : Nat.card M = 4 := by rw [h1] at hfactor; exact hfactor
    exact Or.inr (Or.inr (Subgroup.eq_of_le_of_card_ge hM
      (by rw [BinaryCarrierDerivedRadical16T1332.card_relative_radical, hc])))

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
    BinaryCarrierDerivedOrder16T1332.card_commutator]

theorem profile_bot : profile (⊥ : Subgroup Original) = (0,0,0,0,1,6) := by
  apply profile_of_fields ⊥ bot_le 0 0 0 0 1 6 head_bot
    (by rw [Subgroup.card_bot]; rfl) normalHeadMax_bot
  · exact (head_congr _ _ radical_bot).trans head_bot
  · have h := quotientCenter_card_mul (⊥ : Subgroup Original)
    rw [BinaryCarrierRadicalCenter16T1332.centerPreimage_bot_eq_Z,
      BinaryCarrierRadicalHead16T1332.card_Z, Subgroup.card_bot, mul_one] at h
    exact h
  · rw [quotient_derived_card ⊥ bot_le, Subgroup.card_bot]
    rfl

theorem profile_Z : profile Z = (1,1,1,0,1,5) := by
  have hZR := BinaryCarrierRadicalHead16T1332.Z_le_radical
  have hnot : ¬ R ≤ Z := by
    intro h
    have hc := Subgroup.card_le_of_le h
    rw [BinaryCarrierDerivedRadical16T1332.card_relative_radical,
      BinaryCarrierRadicalHead16T1332.card_Z] at hc
    omega
  apply profile_of_fields Z hZR 1 1 1 0 1 5 head_Z
    BinaryCarrierRadicalHead16T1332.card_Z normalHeadMax_Z
  · exact (head_congr _ _ radical_Z).trans head_bot
  · have h : Nat.card (Subgroup.center (Original ⧸ Z)) * Nat.card Z = 4 :=
      BinaryCarrierRadicalCenter16T1332.center_card_mul_of_between Z hZR le_rfl hnot
    rw [BinaryCarrierRadicalHead16T1332.card_Z] at h
    change Nat.card (Subgroup.center (Original ⧸ Z)) = 2
    omega
  · rw [quotient_derived_card Z hZR, BinaryCarrierRadicalHead16T1332.card_Z]
    rfl

theorem profile_R : profile R = (1,2,1,1,4,4) := by
  apply profile_of_fields R le_rfl 1 2 1 1 4 4 head_R
    BinaryCarrierDerivedRadical16T1332.card_relative_radical normalHeadMax_R
  · exact (head_congr _ _ BinaryCarrierRadicalStructure16T1332.relativeRadical_eq_Z).trans head_Z
  · have h := quotientCenter_card_mul R
    rw [BinaryCarrierRadicalCenter16T1332.centerPreimage_radical_eq_derived,
      BinaryCarrierDerivedOrder16T1332.card_commutator,
      BinaryCarrierDerivedRadical16T1332.card_relative_radical] at h
    omega
  · rw [quotient_derived_card R le_rfl, BinaryCarrierDerivedRadical16T1332.card_relative_radical]
    rfl

theorem normal_profile (M : Subgroup Original) [M.Normal] (hM : M ≤ R) :
    profile M = (0,0,0,0,1,6) ∨ profile M = (1,1,1,0,1,5) ∨
      profile M = (1,2,1,1,4,4) := by
  rcases normal_cases M hM with h | h | h
  · subst M
    exact Or.inl profile_bot
  · subst M
    exact Or.inr (Or.inl profile_Z)
  · subst M
    exact Or.inr (Or.inr profile_R)

end SymmetricSubgroupAsymptotics.BinaryCarrierRadicalProfiles16T1332
