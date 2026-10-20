import SymmetricSubgroupAsymptotics.FiniteSymmetricChains

/-! Symmetric-chain coordinates transport along an actual order-preserving
equivalence and a displayed equality of original rank functions. -/
set_option autoImplicit false
noncomputable section
namespace SymmetricSubgroupAsymptotics.FiniteSymmetricChains

variable {I J : Type} [Preorder I] [Preorder J] {rI : I → ℕ} {K : ℕ}

def transport (D : FiniteSymmetricChains I rI K) (e : I ≃ J)
    (hle : ∀ x y, e x≤e y ↔ x≤y) (rJ : J → ℕ) (hrank : ∀ x, rJ (e x)=rI x) :
    FiniteSymmetricChains J rJ K where
  Colour := D.Colour
  finiteColour := D.finiteColour
  colour := fun y => D.colour (e.symm y)
  start := D.start
  start_bound := D.start_bound
  rank_bounds := by
    intro y
    have hy : rJ y=rI (e.symm y) := by simpa only [Equiv.apply_symm_apply] using hrank (e.symm y)
    rw [hy]
    exact D.rank_bounds _
  rank_unique := by
    intro y z hc hr
    apply e.symm.injective
    apply D.rank_unique _ _ hc
    have hy : rJ y=rI (e.symm y) := by simpa only [Equiv.apply_symm_apply] using hrank (e.symm y)
    have hz : rJ z=rI (e.symm z) := by simpa only [Equiv.apply_symm_apply] using hrank (e.symm z)
    exact hy.symm.trans (hr.trans hz)
  rank_surjective := by
    intro c t hlo hhi
    obtain ⟨x,hx,hxr⟩ := D.rank_surjective c t hlo hhi
    exact ⟨e x,by simpa only [Equiv.symm_apply_apply] using hx,(hrank x).trans hxr⟩
  chain_le := by
    intro y z hc hr
    have hy : rJ y=rI (e.symm y) := by simpa only [Equiv.apply_symm_apply] using hrank (e.symm y)
    have hz : rJ z=rI (e.symm z) := by simpa only [Equiv.apply_symm_apply] using hrank (e.symm z)
    have h := (hle _ _).mpr (D.chain_le _ _ hc (hy.symm.trans_le (hr.trans_eq hz)))
    simpa only [Equiv.apply_symm_apply] using h

end SymmetricSubgroupAsymptotics.FiniteSymmetricChains
