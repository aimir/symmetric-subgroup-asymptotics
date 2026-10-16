import SymmetricSubgroupAsymptotics.FunctionBlockThreeTermProjectionIrreducibility

/-! A three-term coordinate projector together with transitivity on each
nonidentity local orbit gives irreducibility. Local maps need not agree
between coordinates, so inverse Singer orientations are allowed. -/

set_option autoImplicit false
noncomputable section
open scoped Classical

namespace SymmetricSubgroupAsymptotics

theorem functionBlock_irreducible_of_three_term_projection_and_local_orbits
    {V H I : Type} [CommGroup V] [Group H] [Finite I] [DecidableEq I]
    (ψ : H →* MulAut (I → V))
    (hlocal : ∀ (i : I) (u v : V), u ≠ 1 → v ≠ 1 →
      ∃ g : H, ψ g (Pi.mulSingle i u) = Pi.mulSingle i v)
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
  have hall (j : I) (u : V) : Pi.mulSingle j u ∈ S := by
    by_cases hu : u = 1
    · subst u
      simpa only [Pi.mulSingle_one] using S.one_mem
    obtain ⟨g,f,hg⟩ := hmove i j
    have hfu : f.symm u ≠ 1 := by
      intro h
      apply hu
      calc
        u = f (f.symm u) := (f.apply_symm_apply u).symm
        _ = f 1 := congrArg f h
        _ = 1 := f.map_one
    obtain ⟨k,hk⟩ := hlocal i (v i) (f.symm u) hi hfu
    have hki : Pi.mulSingle i (f.symm u) ∈ S := by
      rw [← hk]
      exact hS k _ hsingle
    have h := hS g _ hki
    rwa [hg,MulEquiv.apply_symm_apply] at h
  apply top_unique
  intro w _
  exact Subgroup.pi_mem_of_mulSingle_mem w (fun j => hall j (w j))

end SymmetricSubgroupAsymptotics

end
