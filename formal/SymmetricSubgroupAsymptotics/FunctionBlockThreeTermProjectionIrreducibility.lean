import SymmetricSubgroupAsymptotics.FunctionBlockProjectionIrreducibility

/-! A three-term coordinate projector gives the same actual-image
irreducibility criterion as the two-term projector. In characteristic two,
an order-three map acting on every block except one yields this projector
as the sum of the identity and its first two powers. -/

set_option autoImplicit false
noncomputable section
open scoped Classical

namespace SymmetricSubgroupAsymptotics

theorem functionBlock_irreducible_of_three_term_projection
    {V R H I : Type} [CommGroup V] [Group R] [Group H]
    [Finite I] [DecidableEq I]
    (φ : R →* MulAut V) (ψ : H →* MulAut (I → V))
    (hirr : IrreducibleAbelianSemidirect.Irreducible φ)
    (lift : I → R → H)
    (hlift : ∀ i r v, ψ (lift i r) (Pi.mulSingle i v) = Pi.mulSingle i (φ r v))
    (hmove : ∀ i j : I, ∃ (g : H) (f : MulAut V),
      ∀ v, ψ g (Pi.mulSingle i v) = Pi.mulSingle j (f v))
    (s : I → H)
    (hprojection : ∀ i v,
      v * ψ (s i) v * ψ ((s i)^2) v = Pi.mulSingle i (v i)) :
    IrreducibleAbelianSemidirect.Irreducible ψ := by
  intro S hS
  by_cases hSb : S = ⊥
  · exact Or.inl hSb
  right
  obtain ⟨v,hv,hv1⟩ := S.bot_or_exists_ne_one.resolve_left hSb
  have hi : ∃ i, v i ≠ 1 := by
    by_contra hn
    push Not at hn
    exact hv1 (funext hn)
  obtain ⟨i,hi⟩ := hi
  have hsingle : Pi.mulSingle i (v i) ∈ S := by
    rw [← hprojection i v]
    exact S.mul_mem (S.mul_mem hv (hS (s i) v hv)) (hS ((s i)^2) v hv)
  let L : Subgroup V := S.comap (MonoidHom.mulSingle (fun _ : I => V) i)
  have hLinv : ∀ r u, u ∈ L → φ r u ∈ L := by
    intro r u hu
    change Pi.mulSingle i (φ r u) ∈ S
    rw [← hlift i r u]
    exact hS (lift i r) _ hu
  have hLb : L ≠ ⊥ := by
    intro hb
    exact hi (Subgroup.mem_bot.mp (hb ▸ (show v i ∈ L from hsingle)))
  have hLtop : L = ⊤ := (hirr L hLinv).resolve_left hLb
  have hall (j : I) (u : V) : Pi.mulSingle j u ∈ S := by
    obtain ⟨g,f,hg⟩ := hmove i j
    have hu : f.symm u ∈ L := by rw [hLtop]; exact Subgroup.mem_top _
    have h := hS g (Pi.mulSingle i (f.symm u)) hu
    rwa [hg,MulEquiv.apply_symm_apply] at h
  apply top_unique
  intro w _
  exact Subgroup.pi_mem_of_mulSingle_mem w (fun j => hall j (w j))

end SymmetricSubgroupAsymptotics

end
