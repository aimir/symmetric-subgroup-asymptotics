import SymmetricSubgroupAsymptotics.DihedralFiveNormalChain
import SymmetricSubgroupAsymptotics.FiniteNormalChainGenerators

/-! Every odd-prime dihedral group has the normal chain consisting of
the bottom subgroup, rotations, and the whole group. This uniform version
uses a nonzero rotation commutator and no normal-subgroup census. -/

set_option autoImplicit false
noncomputable section
open scoped Classical

namespace SymmetricSubgroupAsymptotics
namespace OddPrimeDihedralNormalChain

open DihedralGroup
variable {p : ℕ} [Fact p.Prime]

def rotations : Subgroup (DihedralGroup p) := Subgroup.zpowers (r 1)

theorem rotation_eq_pow (i : ZMod p) : (r (1 : ZMod p)) ^ i.val = r i := by
  rw [r_one_pow, ZMod.natCast_zmod_val]

theorem rotation_mem_of_ne_one (hp : 2 < p)
    (N : Subgroup (DihedralGroup p)) (hN : N.Normal)
    (x : DihedralGroup p) (hx : x ∈ N) (hxne : x ≠ 1) : r (1 : ZMod p) ∈ N := by
  cases x with
  | r i =>
    have hi : i ≠ 0 := by
      intro h
      apply hxne
      rw [h, r_zero]
    have hpow : (r i : DihedralGroup p) ^ (i⁻¹).val = r 1 := by
      rw [r_pow, ZMod.natCast_zmod_val, mul_inv_cancel₀ hi]
    exact hpow ▸ N.pow_mem hx (i⁻¹).val
  | sr i =>
    have hcomm := N.mul_mem (hN.conj_mem (sr i) hx (r 1)) (N.inv_mem hx)
    have hformula : (r 1 : DihedralGroup p) * sr i * (r 1)⁻¹ * (sr i)⁻¹ = r 2 := by
      simp only [r_mul_sr, inv_r, sr_mul_r, inv_sr, sr_mul_sr]
      congr 1
      ring
    have htwo : r (2 : ZMod p) ∈ N := hformula ▸ hcomm
    have htwo_ne : (2 : ZMod p) ≠ 0 := by
      intro h
      have hd : p ∣ 2 := (ZMod.natCast_eq_zero_iff 2 p).mp h
      have hle := Nat.le_of_dvd (by decide : 0 < 2) hd
      omega
    have hpow : (r (2 : ZMod p)) ^ ((2 : ZMod p)⁻¹).val = r 1 := by
      rw [r_pow, ZMod.natCast_zmod_val, mul_inv_cancel₀ htwo_ne]
    exact hpow ▸ N.pow_mem htwo ((2 : ZMod p)⁻¹).val

theorem normal_eq_bot_or_rotations_or_top (hp : 2 < p)
    (N : Subgroup (DihedralGroup p)) (hN : N.Normal) :
    N = ⊥ ∨ N = rotations ∨ N = ⊤ := by
  by_cases hbot : N = ⊥
  · exact Or.inl hbot
  right
  obtain ⟨x, hx, hxne⟩ := N.bot_or_exists_ne_one.resolve_left hbot
  have hone := rotation_mem_of_ne_one hp N hN x hx hxne
  have hrot (i : ZMod p) : r i ∈ N :=
    rotation_eq_pow i ▸ N.pow_mem hone i.val
  by_cases hreflect : ∃ i : ZMod p, sr i ∈ N
  · right
    obtain ⟨i, hi⟩ := hreflect
    apply top_unique
    intro y _hy
    cases y with
    | r j => exact hrot j
    | sr j =>
      have heq : (sr i : DihedralGroup p) * r (j - i) = sr j := by
        rw [sr_mul_r]
        congr 1
        ring
      exact heq ▸ N.mul_mem hi (hrot (j - i))
  · left
    apply le_antisymm
    · intro y hy
      cases y with
      | r i => exact rotation_eq_pow i ▸ Subgroup.npow_mem_zpowers (r 1) i.val
      | sr i => exact (hreflect ⟨i, hy⟩).elim
    · exact Subgroup.zpowers_le.mpr hone

theorem normal_total (hp : 2 < p) (A B : Subgroup (DihedralGroup p))
    (hA : A.Normal) (hB : B.Normal) : A ≤ B ∨ B ≤ A := by
  rcases normal_eq_bot_or_rotations_or_top hp A hA with hA | hA | hA
  · left; rw [hA]; exact bot_le
  · rcases normal_eq_bot_or_rotations_or_top hp B hB with hB | hB | hB
    · right; rw [hB]; exact bot_le
    · left; simpa only [hA, hB] using (le_rfl : (rotations (p := p)) ≤ rotations)
    · left; rw [hB]; exact le_top
  · right; rw [hA]; exact le_top

theorem normal_generating_singletons (hp : 2 < p) :
    ∀ N : Subgroup (DihedralGroup p), N.Normal →
      ∃ x : Fin 1 → DihedralGroup p, Subgroup.normalClosure (Set.range x) = N :=
  normal_generating_singletons_of_finite_normal_total (normal_total hp)

end OddPrimeDihedralNormalChain
end SymmetricSubgroupAsymptotics

end
