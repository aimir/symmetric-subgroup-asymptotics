import SymmetricSubgroupAsymptotics.FiniteTopBinaryDualKernelGeneratorColdCount
import SymmetricSubgroupAsymptotics.ScalarFourCentralRawSummedCountOfCold
import SymmetricSubgroupAsymptotics.BinaryKernelRankTailNumerics
import SymmetricSubgroupAsymptotics.PrimitiveTwelveActualQuotientEpimorphisms

/-! The actual twelve-pair kernel costs four binary dual generators.
Every top map is counted, with the slope5/3 estimate applied to its actual
residual top. The exceptional summand retains every hot source map. -/
set_option autoImplicit false
noncomputable section
open scoped Classical BigOperators
namespace SymmetricSubgroupAsymptotics.TwelvePairFiniteTopEnvelope
open Non2UnipotentPrefixFiniteMenu
variable {Q T : Type} [Group Q] [Group T] [Finite Q] [Finite T]

theorem coordinate_coefficient_le (hQ : Nat.card Q ≤ 2^41) (hT : Nat.card T ≤ 2^29) :
    ((Nat.card Q^Nat.log 2 (Nat.card T) : ℕ) : ℝ) ≤ (2 : ℝ)^(1189 : ℕ) := by
  have hlog : Nat.log 2 (Nat.card T) ≤ 29 := by
    have hh : Nat.card T < 2^30 := hT.trans_lt (by norm_num)
    have hl := Nat.log_lt_of_lt_pow (Nat.card_pos (α := T)).ne' hh
    omega
  have hp : Nat.card Q^Nat.log 2 (Nat.card T) ≤ 2^1189 := calc
    _ ≤ (2^41)^Nat.log 2 (Nat.card T) := Nat.pow_le_pow_left hQ _
    _ ≤ (2^41)^29 := Nat.pow_le_pow_right (by norm_num) hlog
    _ = _ := by rw [←pow_mul]
  exact_mod_cast hp

variable (top : Q →* T) (htop : Function.Surjective top)
    (A : Rep.{0} (ZMod 2) T) (E : OriginalKernelModuleChart top A)

include htop E in
theorem cold_card_le
    (hgen : RepresentationGeneratedBy A.ρ.dual 4)
    (hQ : Nat.card Q ≤ 2^41) (hT : Nat.card T ≤ 2^29)
    (hcost : ∀ (b : ℕ) (J : Subgroup (Equiv.Perm (Fin b))),
      (Nat.card (GroupEpimorphism J T) : ℝ) ≤
        (2 : ℝ)^(841 : ℕ)*(2 : ℝ)^((5/3 : ℝ)*b))
    (b : ℕ) (J : Subgroup (Equiv.Perm (Fin b)))
    (hJ : ¬FiniteTopKernelRankHot T (51/200) J) :
    (Nat.card (GroupEpimorphism J Q) : ℝ) ≤
      (2 : ℝ)^(2030 : ℕ)*(2 : ℝ)^((403/150 : ℝ)*b) := by
  have h := FiniteTopBinaryDualKernelGeneratorColdCount.cold_card_le
    top htop A E hgen b J hJ
  calc
    _ ≤ ((2 : ℝ)^(841 : ℕ)*(2 : ℝ)^((5/3 : ℝ)*b))*
        (2 : ℝ)^(1189 : ℕ)*(2 : ℝ)^(((51/200 : ℝ)*4)*b) :=
      h.trans (mul_le_mul_of_nonneg_right
        (mul_le_mul (hcost b J) (coordinate_coefficient_le hQ hT)
          (by positivity) (by positivity)) (by positivity))
    _ = _ := by
      rw [show (2030 : ℕ)=841+1189 by decide,pow_add,
        show (403/150 : ℝ)*b=(5/3 : ℝ)*b+((51/200 : ℝ)*4)*b by ring,
        Real.rpow_add (by norm_num : (0 : ℝ)<2)]
      ring

include htop E in
theorem raw_sum_le
    (hgen : RepresentationGeneratedBy A.ρ.dual 4)
    (hQ : Nat.card Q ≤ 2^41) (hT : Nat.card T ≤ 2^29)
    (hcost : ∀ (b : ℕ) (J : Subgroup (Equiv.Perm (Fin b))),
      (Nat.card (GroupEpimorphism J T) : ℝ) ≤
        (2 : ℝ)^(841 : ℕ)*(2 : ℝ)^((5/3 : ℝ)*b))
    (b : ℕ) :
    (∑ J : Subgroup (Equiv.Perm (Fin b)),(Nat.card (GroupEpimorphism J Q) : ℝ)) ≤
      BinaryKernelRankTailNumerics.raw 1 536870953 b+
        (subgroupCount b : ℝ)*((2 : ℝ)^(2030 : ℕ)*(2 : ℝ)^((403/150 : ℝ)*b)) := by
  have hh := ScalarFourCentralTopCoordinates.raw_summed_count_of_cold (T := T)
    ((2 : ℝ)^(2030 : ℕ)) (403/150) (by positivity)
    (fun b J hJ => cold_card_le top htop A E hgen hQ hT hcost b J hJ) 41 hQ b
  have ht : 41+Nat.card T ≤ 536870953 := by norm_num at hT; omega
  apply hh.trans
  apply add_le_add _ le_rfl
  change (b.factorial : ℝ)^(41+Nat.card T)*_ ≤ (1 : ℝ)*(b.factorial : ℝ)^536870953*_
  rw [one_mul]
  apply mul_le_mul_of_nonneg_right _ (by positivity)
  apply pow_le_pow_right₀ _ ht
  exact_mod_cast (Nat.succ_le_iff.mpr (Nat.factorial_pos b) : 1≤b.factorial)

end SymmetricSubgroupAsymptotics.TwelvePairFiniteTopEnvelope
