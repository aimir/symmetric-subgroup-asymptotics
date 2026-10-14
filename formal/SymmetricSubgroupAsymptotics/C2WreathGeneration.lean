import SymmetricSubgroupAsymptotics.C2WreathNormalCover

/-! A full first local factor and the block exchange generate the actual
two-block wreath product. No finite group table is needed. -/

set_option autoImplicit false
noncomputable section

namespace SymmetricSubgroupAsymptotics
namespace C2Wreath

open SemidirectProduct

variable {A : Type} [Group A]

theorem mem_of_first_and_swap (K : Subgroup (W A))
    (hfirst : ∀ a : A, firstFactor a ∈ K)
    (hswap : (inr gen : W A) ∈ K) (g : W A) : g ∈ K := by
  have hsecond (a : A) : (inl (1, a) : W A) ∈ K := by
    have h := K.mul_mem (K.mul_mem hswap (hfirst a)) (K.inv_mem hswap)
    change (inr gen : W A) * inl (a, 1) * (inr gen)⁻¹ ∈ K at h
    rw [← map_inv, ← inl_aut, swapAut_gen] at h
    exact h
  have hbase (v : A × A) : (inl v : W A) ∈ K := by
    have h := K.mul_mem (hfirst v.1) (hsecond v.2)
    change (inl (v.1, 1) : W A) * inl (1, v.2) ∈ K at h
    rw [← map_mul] at h
    simpa only [Prod.mk_mul_mk, mul_one, one_mul, Prod.eta] using h
  have htop (c : Multiplicative (ZMod 2)) : (inr c : W A) ∈ K := by
    rcases cases c with rfl | rfl
    · simpa only [map_one] using K.one_mem
    · exact hswap
  rw [← inl_left_mul_inr_right g]
  exact K.mul_mem (hbase g.left) (htop g.right)

end C2Wreath
end SymmetricSubgroupAsymptotics

end
