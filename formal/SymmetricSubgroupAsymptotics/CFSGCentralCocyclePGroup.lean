import Mathlib.GroupTheory.PGroup
import Mathlib.GroupTheory.Subgroup.Center
import Mathlib.Tactic.Group

/-! Projectively fixed p-subgroups lift to literal fixed elements when
the centre has order prime to p. The central difference is an ACTUAL
homomorphism, not a presumed vanishing cocycle. -/
set_option autoImplicit false
noncomputable section
namespace SymmetricSubgroupAsymptotics.CFSGCentralCocyclePGroup
variable {E : Type*} [Group E]

def centralDifferenceHom (alpha : MulAut E) (L : Subgroup E)
    (hcentral : ∀ u : L, u.val⁻¹ * alpha u.val ∈ Subgroup.center E) :
    L →* Subgroup.center E where
  toFun u := ⟨u.val⁻¹ * alpha u.val, hcentral u⟩
  map_one' := by apply Subtype.ext; simp
  map_mul' x y := by
    apply Subtype.ext
    change (x.val * y.val)⁻¹ * alpha (x.val * y.val) =
      (x.val⁻¹ * alpha x.val) * (y.val⁻¹ * alpha y.val)
    have hm : y.val⁻¹ * (x.val⁻¹ * alpha x.val) = (x.val⁻¹ * alpha x.val) * y.val⁻¹ :=
      Subgroup.mem_center_iff.mp (hcentral x) y.val⁻¹
    calc
      _ = y.val⁻¹ * (x.val⁻¹ * alpha x.val) * alpha y.val := by
        rw [map_mul, mul_inv_rev]
        group
      _ = _ := by rw [hm]; group

theorem central_p_element_eq_one_of_coprime {p : ℕ}
    (hcoprime : p.Coprime (Nat.card (Subgroup.center E)))
    (z : Subgroup.center E) (hz : ∃ k : ℕ, z ^ p ^ k = 1) : z = 1 := by
  obtain ⟨k, hk⟩ := hz
  have hd := orderOf_dvd_of_pow_eq_one hk
  have he : orderOf z = 1 := Nat.eq_one_of_dvd_coprimes (hcoprime.pow_left k)
    hd (orderOf_dvd_natCard z)
  exact orderOf_eq_one_iff.mp he

theorem fixed_on_pSubgroup_of_central_difference (alpha : MulAut E) (L : Subgroup E)
    {p : ℕ} (hL : IsPGroup p L)
    (hcentral : ∀ u : L, u.val⁻¹ * alpha u.val ∈ Subgroup.center E)
    (hcoprime : p.Coprime (Nat.card (Subgroup.center E))) :
    ∀ u : L, alpha u.val = u.val := by
  intro u
  let c := centralDifferenceHom alpha L hcentral
  obtain ⟨k, hk⟩ := hL u
  have hc : (c u) ^ p ^ k = 1 := by rw [← map_pow, hk, map_one]
  have he := central_p_element_eq_one_of_coprime hcoprime (c u) ⟨k, hc⟩
  have hh : u.val⁻¹ * alpha u.val = 1 := congrArg Subtype.val he
  exact (inv_mul_eq_one.mp hh).symm

end SymmetricSubgroupAsymptotics.CFSGCentralCocyclePGroup
