import SymmetricSubgroupAsymptotics.FiniteGroupBinaryOrderGenerators
import SymmetricSubgroupAsymptotics.CoprimeNilpotentProductGenerators
import Mathlib.GroupTheory.PGroup

/-! A binary kernel above an actual quotient whose order is divisible by
four has order at most two if sixteen does not divide the original source
order. Ordinary extension generation then costs only one above that SAME
quotient. No Sylow maximum-generator theorem is used. -/
set_option autoImplicit false
noncomputable section
namespace SymmetricSubgroupAsymptotics.BinaryKernelFourDivisorOrdinary

variable {G Q : Type} [Group G] [Finite G] [Group Q] [Finite Q]

theorem kernel_card_le_two (f : G →* Q) (hf : Function.Surjective f)
    (hker : IsPGroup 2 f.ker) (hfour : 4 ∣ Nat.card Q)
    (hnotSixteen : ¬16 ∣ Nat.card G) : Nat.card f.ker ≤ 2 := by
  letI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨a,ha⟩ := hker.exists_card_eq
  have haSmall : a ≤ 1 := by
    by_contra hlarge
    have haTwo : 2 ≤ a := by omega
    have hkfour : 4 ∣ Nat.card f.ker := by
      rw [ha]
      exact Nat.pow_dvd_pow 2 haTwo
    have hmul := f.ker.card_mul_index
    rw [Subgroup.index_ker,MonoidHom.range_eq_top.mpr hf,Subgroup.card_top] at hmul
    have hdiv := Nat.mul_dvd_mul hkfour hfour
    apply hnotSixteen
    simpa only [show 4*4 = 16 by decide,hmul] using hdiv
  rw [ha]
  exact (Nat.pow_le_pow_right (by decide : 0 < 2) haSmall).trans_eq (pow_one 2)

theorem genRank_le_one_add_quotient (f : G →* Q) (hf : Function.Surjective f)
    (hker : IsPGroup 2 f.ker) (hfour : 4 ∣ Nat.card Q)
    (hnotSixteen : ¬16 ∣ Nat.card G) :
    MarkedC4.genRank G ≤ 1 + MarkedC4.genRank Q := by
  have hk : MarkedC4.genRank f.ker ≤ 1 :=
    FiniteGroupBinaryOrderGenerators.genRank_le_of_card_le_two_pow f.ker 1
      (by simpa only [pow_one] using kernel_card_le_two f hf hker hfour hnotSixteen)
  have hh := MarkedC4.genRank_le_of_normal f.ker
  rw [CoprimeNilpotentProductGenerators.genRank_mulEquiv
    (QuotientGroup.quotientKerEquivOfSurjective f hf)] at hh
  exact hh.trans (Nat.add_le_add_right hk _)

end SymmetricSubgroupAsymptotics.BinaryKernelFourDivisorOrdinary
