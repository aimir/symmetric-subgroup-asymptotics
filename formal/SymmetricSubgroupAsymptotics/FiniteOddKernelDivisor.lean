import Mathlib.GroupTheory.Index
import Mathlib.Algebra.Group.Subgroup.Finite
import Mathlib.GroupTheory.Coset.Card
import Mathlib.Data.Fintype.Units

/-! An odd element makes a sign-valued homomorphism onto. Its kernel
therefore pays exactly a factor two in finite cardinal divisibility. -/
set_option autoImplicit false
noncomputable section
namespace SymmetricSubgroupAsymptotics.FiniteOddKernelDivisor

theorem kernel_card_mul_two {A : Type*} [Group A] [Finite A]
    (sign : A →* ℤˣ) (s : A) (hs : sign s = -1) :
    Nat.card sign.ker * 2 = Nat.card A := by
  have hsurj : Function.Surjective sign := by
    intro z
    rcases Int.units_eq_one_or z with h | h
    · exact ⟨1,(map_one sign).trans h.symm⟩
    · exact ⟨s,hs.trans h.symm⟩
  have hh : Nat.card sign.ker * Nat.card sign.range = Nat.card A := by
    rw [←Subgroup.index_ker,sign.ker.card_mul_index]
  rw [MonoidHom.range_eq_top.mpr hsurj,Subgroup.card_top] at hh
  simpa only [Nat.card_eq_fintype_card,Fintype.card_units_int] using hh

theorem card_dvd_of_injective_to_odd_kernel
    {A B : Type*} [Group A] [Finite A] [Group B] [Finite B]
    (sign : A →* ℤˣ) (s : A) (hs : sign s = -1)
    (f : B →* sign.ker) (hf : Function.Injective f)
    (C : ℕ) (hA : Nat.card A ∣ 2*C) : Nat.card B ∣ C := by
  have hk : Nat.card sign.ker ∣ C := by
    have hh := kernel_card_mul_two sign s hs
    have hd : 2 * Nat.card sign.ker ∣ 2*C := by
      rw [←hh] at hA
      simpa only [Nat.mul_comm] using hA
    exact (Nat.mul_dvd_mul_iff_left (by decide : 0 < 2)).mp hd
  exact (Subgroup.card_dvd_of_injective f hf).trans hk

end SymmetricSubgroupAsymptotics.FiniteOddKernelDivisor
