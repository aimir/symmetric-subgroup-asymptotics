import SymmetricSubgroupAsymptotics.IrreducibleAbelianSemidirectNormalGenerators

/-! A displayed polynomial in a two-block action extracts the second
block. Local irreducibility and an actual block swap then imply global
irreducibility, without an invariant-subgroup classification. -/

set_option autoImplicit false
noncomputable section
open scoped Classical

namespace SymmetricSubgroupAsymptotics

theorem twoBlock_irreducible_of_projection
    {V R H : Type} [CommGroup V] [Group R] [Group H]
    (φ : R →* MulAut V) (ψ : H →* MulAut (V × V))
    (hirr : IrreducibleAbelianSemidirect.Irreducible φ)
    (lift : R → H)
    (hlift : ∀ r v, ψ (lift r) (v, 1) = (φ r v, 1))
    (swap : H) (hswap : ∀ v : V × V, ψ swap v = (v.2, v.1))
    (s : H)
    (hprojection : ∀ v : V × V,
      ψ (s ^ 4) v * ψ (s ^ 2) v * ψ s v = (1, v.2)) :
    IrreducibleAbelianSemidirect.Irreducible ψ := by
  intro S hSinv
  by_cases hSb : S = ⊥
  · exact Or.inl hSb
  right
  have hsecond (v : V × V) (hv : v ∈ S) : (1, v.2) ∈ S := by
    rw [← hprojection v]
    exact S.mul_mem (S.mul_mem (hSinv (s ^ 4) v hv) (hSinv (s ^ 2) v hv))
      (hSinv s v hv)
  have hfirst (v : V × V) (hv : v ∈ S) : (v.1, 1) ∈ S := by
    have h := S.mul_mem hv (S.inv_mem (hsecond v hv))
    change (v.1 * 1⁻¹, v.2 * v.2⁻¹) ∈ S at h
    simpa only [inv_one, mul_one, mul_inv_cancel] using h
  let L : Subgroup V := S.comap (MonoidHom.inl V V)
  have hLinv : ∀ r v, v ∈ L → φ r v ∈ L := by
    intro r v hv
    change (φ r v, 1) ∈ S
    rw [← hlift r v]
    exact hSinv (lift r) (v, 1) hv
  have hLb : L ≠ ⊥ := by
    obtain ⟨v, hv, hv1⟩ := S.bot_or_exists_ne_one.resolve_left hSb
    by_cases hfst : v.1 = 1
    · have hswapv : (v.2, v.1) ∈ S := hswap v ▸ hSinv swap v hv
      have hvL : v.2 ∈ L := hfirst (v.2, v.1) hswapv
      intro hL
      have hsnd : v.2 = 1 := Subgroup.mem_bot.mp (hL ▸ hvL)
      exact hv1 (Prod.ext hfst hsnd)
    · have hvL : v.1 ∈ L := hfirst v hv
      intro hL
      exact hfst (Subgroup.mem_bot.mp (hL ▸ hvL))
  have hLtop : L = ⊤ := (hirr L hLinv).resolve_left hLb
  apply top_unique
  intro v _
  have hfst : (v.1, 1) ∈ S := by
    have h : v.1 ∈ L := by rw [hLtop]; exact Subgroup.mem_top _
    exact h
  have hsnd : (1, v.2) ∈ S := by
    have h : v.2 ∈ L := by rw [hLtop]; exact Subgroup.mem_top _
    have h' := hSinv swap (v.2, 1) h
    rw [hswap] at h'
    exact h'
  simpa only [Prod.mk_mul_mk, mul_one, one_mul, Prod.eta] using S.mul_mem hfst hsnd

end SymmetricSubgroupAsymptotics

end
