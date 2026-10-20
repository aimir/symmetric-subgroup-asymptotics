import SymmetricSubgroupAsymptotics.FiniteTwoNormalSocleGenerators
import Mathlib.GroupTheory.QuotientGroup.Basic

/-! Equivalence transport and normal-cover tools for explicit quotient alternatives. -/

set_option autoImplicit false
noncomputable section
open scoped Classical

namespace SymmetricSubgroupAsymptotics
namespace CyclicSocleQuotientTools

variable {G H R : Type} [Group G] [Group H] [Group R]

theorem minimal_map_equiv (e : G ≃* H) (M : Subgroup G)
    (hM : IsMinimalNormalSubgroup M) : IsMinimalNormalSubgroup (e.mapSubgroup M) := by
  let E : Subgroup G ≃o Subgroup H := e.mapSubgroup
  refine ⟨hM.1.map e.toMonoidHom e.surjective, ?_, ?_⟩
  · intro hbot
    apply hM.2.1
    apply E.injective
    simpa only [map_bot] using hbot
  · intro K hK hKne hKM
    let L : Subgroup G := E.symm K
    have hLne : L ≠ ⊥ := by
      intro hL
      apply hKne
      have h := congrArg E hL
      simpa only [L, E.apply_symm_apply, map_bot] using h
    have hLM : L ≤ M := by
      apply E.le_iff_le.mp
      simpa only [L, E.apply_symm_apply] using hKM
    have hLNormal : L.Normal := by
      have hback := hK.map e.symm.toMonoidHom e.symm.surjective
      change (E.symm K).Normal at hback
      exact hback
    have hLeq : L = M := hM.2.2 L hLNormal hLne hLM
    exact (E.apply_symm_apply K).symm.trans (congrArg E hLeq)

theorem socle_map_le (e : G ≃* H) :
    (finiteGroupSocle G).map e.toMonoidHom ≤ finiteGroupSocle H := by
  apply Subgroup.map_le_iff_le_comap.mpr
  apply Subgroup.normalClosure_le_normal
  rintro x ⟨M, hM, hx⟩
  exact Subgroup.subset_normalClosure
    ⟨e.mapSubgroup M, minimal_map_equiv e M hM, ⟨x, hx, rfl⟩⟩

theorem socle_map_equiv (e : G ≃* H) :
    (finiteGroupSocle G).map e.toMonoidHom = finiteGroupSocle H := by
  apply le_antisymm (socle_map_le e)
  intro y hy
  have hx : e.symm y ∈ finiteGroupSocle G :=
    socle_map_le e.symm ⟨y, hy, rfl⟩
  exact ⟨e.symm y, hx, e.apply_symm_apply y⟩

theorem socleBound_equiv (e : G ≃* H) {t : ℕ}
    (h : SocleNormalGeneratorBound G t) : SocleNormalGeneratorBound H t := by
  obtain ⟨x, hx⟩ := h
  let y : Fin t → H := fun i ↦ e (x i)
  refine ⟨y, ?_⟩
  have himage : e.toMonoidHom '' Set.range x = Set.range y := by
    ext z
    constructor
    · rintro ⟨_, ⟨i, rfl⟩, rfl⟩
      exact ⟨i, rfl⟩
    · rintro ⟨i, rfl⟩
      exact ⟨x i, Set.mem_range_self i, rfl⟩
  calc
    Subgroup.normalClosure (Set.range y) =
        (Subgroup.normalClosure (Set.range x)).map e.toMonoidHom := by
      rw [Subgroup.map_normalClosure _ _ e.surjective, himage]
    _ = (finiteGroupSocle G).map e.toMonoidHom := by rw [hx]
    _ = finiteGroupSocle H := socle_map_equiv e

/-- A nontrivial normal subgroup contained in every nontrivial normal
subgroup is the unique minimal normal subgroup. -/
theorem socleBound_of_normal_cover (V : Subgroup G) [V.Normal]
    (hV : V ≠ ⊥)
    (hcover : ∀ N : Subgroup G, N.Normal → N ≠ ⊥ → V ≤ N) :
    SocleNormalGeneratorBound G 1 := by
  have hmin : IsMinimalNormalSubgroup V :=
    ⟨inferInstance, hV, fun N hN hNb hNV ↦ le_antisymm hNV (hcover N hN hNb)⟩
  have hsocle : finiteGroupSocle G = V := by
    apply le_antisymm
    · apply Subgroup.normalClosure_le_normal
      rintro x ⟨N, hN, hx⟩
      have hNV : V = N := hN.2.2 V inferInstance hV (hcover N hN.1 hN.2.1)
      exact hNV.symm ▸ hx
    · intro x hx
      exact Subgroup.subset_normalClosure ⟨V, hmin, hx⟩
  obtain ⟨x, hx, hxne⟩ := V.bot_or_exists_ne_one.resolve_left hV
  let W := Subgroup.normalClosure (Set.range (fun _ : Fin 1 ↦ x))
  have hWV : W ≤ V := by
    apply Subgroup.normalClosure_le_normal
    rintro _ ⟨i, rfl⟩
    exact hx
  have hWne : W ≠ ⊥ := by
    intro hbot
    apply hxne
    apply Subgroup.mem_bot.mp
    rw [← hbot]
    exact Subgroup.subset_normalClosure (Set.mem_range_self (0 : Fin 1))
  exact ⟨fun _ ↦ x, (hmin.2.2 W inferInstance hWne hWV).trans hsocle.symm⟩

/-- Descend an epimorphism through another epimorphism whose kernel it kills. -/
theorem exists_surjective_factor (p : G →* R) (hp : Function.Surjective p)
    (q : G →* H) (hq : Function.Surjective q) (hker : p.ker ≤ q.ker) :
    ∃ f : R →* H, Function.Surjective f ∧ f.comp p = q := by
  let f : R →* H := p.liftOfSurjective hp ⟨q, hker⟩
  have hf : f.comp p = q :=
    p.liftOfRightInverse_comp (Function.surjInv hp)
      (Function.rightInverse_surjInv hp) ⟨q, hker⟩
  refine ⟨f, ?_, hf⟩
  intro h
  obtain ⟨g, hg⟩ := hq h
  refine ⟨p g, ?_⟩
  exact (DFunLike.congr_fun hf g).trans hg

end CyclicSocleQuotientTools
end SymmetricSubgroupAsymptotics

end
