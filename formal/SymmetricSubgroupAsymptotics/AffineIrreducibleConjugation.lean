import SymmetricSubgroupAsymptotics.AffineIrreducibleNormalGenerators

/-! Irreducibility transfers through an explicit linear change of basis
and inclusion into the actual target linear subgroup. -/

set_option autoImplicit false
noncomputable section
open scoped Classical

namespace SymmetricSubgroupAsymptotics
namespace AffineModel

theorem irreducible_of_conjugate_le {p d : ℕ} [Fact p.Prime]
    (R S : Subgroup (GLV p d)) (e : GLV p d) (hR : Irreducible R)
    (hle : R.map (MulAut.conj e).toMonoidHom ≤ S) : Irreducible S := by
  intro T hT
  let U : AddSubgroup (V p d) := T.comap e.toAddEquiv.toAddMonoidHom
  have hU : ∀ r ∈ R, ∀ x ∈ U, r x ∈ U := by
    intro r hr x hx
    have hm : (MulAut.conj e) r ∈ S := hle ⟨r, hr, rfl⟩
    have hh := hT ((MulAut.conj e) r) hm (e x) hx
    change e (r (e.symm (e x))) ∈ T at hh
    change e (r x) ∈ T
    simpa only [LinearEquiv.symm_apply_apply] using hh
  rcases hR U hU with hb | ht
  · left
    apply le_antisymm _ bot_le
    intro y hy
    have hx : e.symm y ∈ U := by
      change e (e.symm y) ∈ T
      simpa only [LinearEquiv.apply_symm_apply] using hy
    rw [hb] at hx
    have he : e.symm y = 0 := AddSubgroup.mem_bot.mp hx
    apply AddSubgroup.mem_bot.mpr
    calc
      y = e (e.symm y) := (e.apply_symm_apply y).symm
      _ = 0 := by rw [he, map_zero]
  · right
    apply top_unique
    intro y _hy
    have hx : e.symm y ∈ U := by rw [ht]; exact AddSubgroup.mem_top _
    change e (e.symm y) ∈ T at hx
    simpa only [LinearEquiv.apply_symm_apply] using hx

end AffineModel
end SymmetricSubgroupAsymptotics

end
