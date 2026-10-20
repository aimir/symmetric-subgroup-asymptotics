import SymmetricSubgroupAsymptotics.External.SubgroupBounds.GroupMain
import SymmetricSubgroupAsymptotics.Non2PreE7Sns2MenuMass

/-!
# Checked binary normal-subgroup bound

The stronger Palcoux--Spiga interval theorem bounds all subgroups.  Injecting
normal subgroups into the interval above the identity gives the deliberately
weak Fusari--Spiga consequence used by the SNS2 menu, without a literature
hypothesis.
-/
set_option autoImplicit false
noncomputable section

namespace SymmetricSubgroupAsymptotics.Non2UnipotentPrefixFiniteMenu
open SharpIntermediateSubgroupBounds

/-- The former binary subgroup-count input is a proved theorem. -/
theorem fusariSpigaBinaryNormalSubgroup : FusariSpigaBinaryNormalSubgroupInput := by
  intro G _ _ hG
  classical
  letI : Fintype G := Fintype.ofFinite G
  obtain ⟨l, hl⟩ := hG.exists_card_eq
  have hlog : Nat.log 2 (Nat.card G) = l := by
    rw [hl, Nat.log_pow (by norm_num)]
  have hinj : Nat.card {N : Subgroup G // N.Normal} ≤
      Nat.card (interval (⊥ : Subgroup G)) :=
    Nat.card_le_card_of_injective
      (fun N => (⟨N.1, bot_le⟩ : interval (⊥ : Subgroup G)))
      (by
        intro A B h
        apply Subtype.ext
        exact congrArg (fun K : interval (⊥ : Subgroup G) => K.1) h)
  have hbound : (Nat.card {N : Subgroup G // N.Normal} : ℝ) ≤
      8 * (2 : ℝ) ^ ((l : ℝ) ^ 2 / 4) := by
    by_cases htriv : Nat.card G = 1
    · letI : Subsingleton G := (Nat.card_eq_one_iff_unique.mp htriv).1
      letI : Nonempty {N : Subgroup G // N.Normal} := ⟨⟨⊥, inferInstance⟩⟩
      have hn : Nat.card {N : Subgroup G // N.Normal} ≤ 1 := by
        rw [Nat.card_unique]
      have hp : (1 : ℝ) ≤ (2 : ℝ) ^ ((l : ℝ) ^ 2 / 4) :=
        Real.one_le_rpow (by norm_num) (by positivity)
      have hcast : (Nat.card {N : Subgroup G // N.Normal} : ℝ) ≤ 1 := by
        exact_mod_cast hn
      exact hcast.trans (by nlinarith)
    · have hn : 1 < (⊥ : Subgroup G).index := by
        rw [Subgroup.index_bot]
        have := Nat.card_pos (α := G)
        omega
      have h := interval_card_lt_universal_decimal hn
      rw [Subgroup.index_bot, hl] at h
      have hrealLog : indexLog 2 (2 ^ l) = (l : ℝ) := by
        unfold indexLog
        rw [Nat.cast_pow, Nat.cast_ofNat, Real.log_pow]
        exact mul_div_cancel_right₀ _ (Real.log_ne_zero_of_pos_of_ne_one (by norm_num) (by norm_num))
      rw [hrealLog] at h
      have hscale : ((2 ^ l : ℕ) : ℝ) ^ ((l : ℝ) / 4) =
          (2 : ℝ) ^ ((l : ℝ) ^ 2 / 4) := by
        rw [Nat.cast_pow, Nat.cast_ofNat, ← Real.rpow_natCast, ← Real.rpow_mul (by norm_num)]
        congr 1
        ring
      rw [hscale] at h
      have hsmall : (3685984401 : ℝ) / 500000000 ≤ 8 := by norm_num
      have hcast : (Nat.card {N : Subgroup G // N.Normal} : ℝ) ≤
          (Nat.card (interval (⊥ : Subgroup G)) : ℝ) := by exact_mod_cast hinj
      exact hcast.trans (h.le.trans
        (mul_le_mul_of_nonneg_right hsmall (by positivity)))
  rw [hlog]
  calc
    _ ≤ (8 * (2 : ℝ) ^ ((l : ℝ) ^ 2 / 4)) *
        (2 : ℝ) ^ (-((l : ℝ) ^ 2 / 4)) :=
      mul_le_mul_of_nonneg_right hbound (by positivity)
    _ = 8 := by
      rw [mul_assoc, ← Real.rpow_add (by norm_num)]
      simp
    _ ≤ 8 * (2 : ℝ) ^ (2 * (l : ℝ)) :=
      le_mul_of_one_le_right (by norm_num)
        (Real.one_le_rpow (by norm_num) (by positivity))

end SymmetricSubgroupAsymptotics.Non2UnipotentPrefixFiniteMenu
