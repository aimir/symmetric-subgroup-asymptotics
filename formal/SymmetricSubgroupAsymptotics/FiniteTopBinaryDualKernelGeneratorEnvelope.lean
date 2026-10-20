import SymmetricSubgroupAsymptotics.FiniteTopBinaryDualKernelGeneratorColdCount
import SymmetricSubgroupAsymptotics.ScalarFourCentralRawSummedCountOfCold
import SymmetricSubgroupAsymptotics.Non2PreE7SmallModelNumerics
import SymmetricSubgroupAsymptotics.PrimitiveAffineDegreeSixTailSource
import SymmetricSubgroupAsymptotics.BinaryKernelRankTailNumerics

/-! A bounded target with an actual binary kernel uses top generators
in its cold coefficient, and the complete finite-index kernel rank tail
on its hot sources. No epimorphism or top-map multiplicity is omitted. -/
set_option autoImplicit false
noncomputable section
open scoped Classical BigOperators
namespace SymmetricSubgroupAsymptotics.FiniteTopBinaryDualKernelGeneratorEnvelope
open Non2UnipotentPrefixFiniteMenu

variable {Q T : Type} [Group Q] [Group T] [Finite Q] [Finite T]

theorem coefficient_le (hQ : Nat.card Q ≤ 2^24) (hT : Nat.card T ≤ 2^16) :
    ((Nat.card Q^Nat.log 2 (Nat.card T) : ℕ) : ℝ) * (Nat.card (T ≃* T) : ℝ) ≤
      (2 : ℝ)^(640 : ℕ) := by
  have hlog : Nat.log 2 (Nat.card T) ≤ 16 := by
    have hh : Nat.card T < 2^17 := hT.trans_lt (by norm_num)
    have hl := Nat.log_lt_of_lt_pow (Nat.card_pos (α := T)).ne' hh
    omega
  have hp : Nat.card Q^Nat.log 2 (Nat.card T) ≤ 2^384 := by
    calc
      _ ≤ (2^24)^Nat.log 2 (Nat.card T) := Nat.pow_le_pow_left hQ _
      _ ≤ (2^24)^16 := Nat.pow_le_pow_right (by norm_num) hlog
      _ = _ := by rw [←pow_mul]
  have ha : Nat.card (T ≃* T) ≤ 2^256 :=
    mulEquiv_card_le_two_pow_sq_of_order 16 hT
  have hn := Nat.mul_le_mul hp ha
  have he : (2^384 : ℕ)*2^256=2^640 := by rw [←pow_add]
  rw [he] at hn
  exact_mod_cast hn

variable (top : Q →* T) (htop : Function.Surjective top)
    (A : Rep.{0} (ZMod 2) T) (E : OriginalKernelModuleChart top A)

include htop E in
theorem cold_card_le {H : ℕ}
    (hgen : RepresentationGeneratedBy A.ρ.dual H)
    (hQ : Nat.card Q ≤ 2^24) (hT : Nat.card T ≤ 2^16)
    (theta : ℝ)
    (hcost : ∀ (b : ℕ) (J : Subgroup (Equiv.Perm (Fin b))),
      (Nat.card (GroupEpimorphism J T) : ℝ) *
        (2 : ℝ)^(((51/200 : ℝ)*H)*b) ≤
      (Nat.card (T ≃* T) : ℝ)*(2 : ℝ)^(theta*b))
    (b : ℕ) (J : Subgroup (Equiv.Perm (Fin b)))
    (hJ : ¬FiniteTopKernelRankHot T (51/200) J) :
    (Nat.card (GroupEpimorphism J Q) : ℝ) ≤
      (2 : ℝ)^(640 : ℕ)*(2 : ℝ)^(theta*b) := by
  have h := FiniteTopBinaryDualKernelGeneratorColdCount.cold_card_le
    top htop A E hgen b J hJ
  have he : (Nat.card (GroupEpimorphism J T) : ℝ)*
      (Nat.card Q^Nat.log 2 (Nat.card T) : ℕ)*(2 : ℝ)^(((51/200 : ℝ)*H)*b) =
      (Nat.card Q^Nat.log 2 (Nat.card T) : ℕ)*
        ((Nat.card (GroupEpimorphism J T) : ℝ)*(2 : ℝ)^(((51/200 : ℝ)*H)*b)) := by ring
  rw [he] at h
  apply h.trans
  calc
    _ ≤ (Nat.card Q^Nat.log 2 (Nat.card T) : ℕ)*
        ((Nat.card (T ≃* T) : ℝ)*(2 : ℝ)^(theta*b)) :=
      mul_le_mul_of_nonneg_left (hcost b J) (by positivity)
    _ ≤ _ := by
      rw [←mul_assoc]
      exact mul_le_mul_of_nonneg_right (coefficient_le hQ hT) (by positivity)

include htop E in
theorem raw_sum_le {H : ℕ}
    (hgen : RepresentationGeneratedBy A.ρ.dual H)
    (hQ : Nat.card Q ≤ 2^24) (hT : Nat.card T ≤ 2^16)
    (theta : ℝ)
    (hcost : ∀ (b : ℕ) (J : Subgroup (Equiv.Perm (Fin b))),
      (Nat.card (GroupEpimorphism J T) : ℝ) *
        (2 : ℝ)^(((51/200 : ℝ)*H)*b) ≤
      (Nat.card (T ≃* T) : ℝ)*(2 : ℝ)^(theta*b))
    (b : ℕ) :
    (∑ J : Subgroup (Equiv.Perm (Fin b)),(Nat.card (GroupEpimorphism J Q) : ℝ)) ≤
      BinaryKernelRankTailNumerics.raw 1 65560 b+
        (subgroupCount b : ℝ)*((2 : ℝ)^(640 : ℕ)*(2 : ℝ)^(theta*b)) := by
  have hh := ScalarFourCentralTopCoordinates.raw_summed_count_of_cold (T := T)
    ((2 : ℝ)^(640 : ℕ)) theta (by positivity)
    (fun b J hJ => cold_card_le top htop A E hgen hQ hT theta hcost b J hJ) 24 hQ b
  have ht : 24+Nat.card T ≤ 65560 := by norm_num at hT; omega
  apply hh.trans
  apply add_le_add _ le_rfl
  change (b.factorial : ℝ)^(24+Nat.card T)*_ ≤ (1 : ℝ)*(b.factorial : ℝ)^65560*_
  rw [one_mul]
  apply mul_le_mul_of_nonneg_right _ (by positivity)
  apply pow_le_pow_right₀ _ ht
  exact_mod_cast (Nat.succ_le_iff.mpr (Nat.factorial_pos b) : 1≤b.factorial)

end SymmetricSubgroupAsymptotics.FiniteTopBinaryDualKernelGeneratorEnvelope
