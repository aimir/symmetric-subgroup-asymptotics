import SymmetricSubgroupAsymptotics.NormalChainSocleGenerators
import Mathlib.GroupTheory.SpecificGroups.Dihedral
import Mathlib.Data.ZMod.Basic
import Mathlib.Algebra.Field.ZMod

/-!
# The normal chain of the dihedral group of order ten

A nonidentity rotation generates the prime-order rotation group. A normal
subgroup containing a reflection also contains its commutator with a
rotation, hence all rotations and then all reflections. This classifies
the normal subgroups without a subgroup enumeration.
-/

set_option autoImplicit false
noncomputable section
open scoped Classical

namespace SymmetricSubgroupAsymptotics
namespace DihedralFiveNormalChain

open DihedralGroup

abbrev G := DihedralGroup 5
def rotations : Subgroup G := Subgroup.zpowers (r 1)

theorem rotation_eq_pow (i : ZMod 5) : (r (1 : ZMod 5)) ^ i.val = r i := by
  rw [r_one_pow, ZMod.natCast_zmod_val]

theorem rotation_mem_of_ne_one (N : Subgroup G) (hN : N.Normal)
    (x : G) (hx : x ∈ N) (hxne : x ≠ 1) : r (1 : ZMod 5) ∈ N := by
  letI : Fact (Nat.Prime 5) := ⟨Nat.prime_five⟩
  cases x with
  | r i =>
    have hi : i ≠ 0 := by
      intro h
      apply hxne
      rw [h, r_zero]
    have hpow : (r i : G) ^ (i⁻¹).val = r 1 := by
      rw [r_pow, ZMod.natCast_zmod_val, mul_inv_cancel₀ hi]
    exact hpow ▸ N.pow_mem hx (i⁻¹).val
  | sr i =>
    have hcomm := N.mul_mem (hN.conj_mem (sr i) hx (r 1)) (N.inv_mem hx)
    have hformula : (r 1 : G) * sr i * (r 1)⁻¹ * (sr i)⁻¹ = r 2 := by
      simp only [r_mul_sr, inv_r, sr_mul_r, inv_sr, sr_mul_sr]
      congr 1
      ring
    have htwo : r (2 : ZMod 5) ∈ N := hformula ▸ hcomm
    have hpow : (r (2 : ZMod 5)) ^ 3 = r 1 := by decide +kernel
    exact hpow ▸ N.pow_mem htwo 3

theorem normal_eq_bot_or_rotations_or_top (N : Subgroup G) (hN : N.Normal) :
    N = ⊥ ∨ N = rotations ∨ N = ⊤ := by
  by_cases hbot : N = ⊥
  · exact Or.inl hbot
  right
  obtain ⟨x, hx, hxne⟩ := N.bot_or_exists_ne_one.resolve_left hbot
  have hone := rotation_mem_of_ne_one N hN x hx hxne
  have hrot (i : ZMod 5) : r i ∈ N :=
    rotation_eq_pow i ▸ N.pow_mem hone i.val
  by_cases hreflect : ∃ i : ZMod 5, sr i ∈ N
  · right
    obtain ⟨i, hi⟩ := hreflect
    apply top_unique
    intro y _hy
    cases y with
    | r j => exact hrot j
    | sr j =>
      have heq : (sr i : G) * r (j - i) = sr j := by
        rw [sr_mul_r]
        congr 1
        ring
      exact heq ▸ N.mul_mem hi (hrot (j - i))
  · left
    apply le_antisymm
    · intro y hy
      cases y with
      | r i =>
        exact rotation_eq_pow i ▸ Subgroup.npow_mem_zpowers (r 1) i.val
      | sr i => exact (hreflect ⟨i, hy⟩).elim
    · exact Subgroup.zpowers_le.mpr hone

theorem normal_total (A B : Subgroup G) (hA : A.Normal) (hB : B.Normal) :
    A ≤ B ∨ B ≤ A := by
  rcases normal_eq_bot_or_rotations_or_top A hA with hA | hA | hA
  · left
    rw [hA]
    exact bot_le
  · rcases normal_eq_bot_or_rotations_or_top B hB with hB | hB | hB
    · right
      rw [hB]
      exact bot_le
    · left
      simpa only [hA, hB] using (le_rfl : rotations ≤ rotations)
    · left
      rw [hB]
      exact le_top
  · right
    rw [hA]
    exact le_top

end DihedralFiveNormalChain
end SymmetricSubgroupAsymptotics

end
