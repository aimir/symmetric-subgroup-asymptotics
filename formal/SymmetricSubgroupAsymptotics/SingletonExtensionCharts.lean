import SymmetricSubgroupAsymptotics.SingletonExtension

/-! Changing a singleton complement chart only conjugates the original
subgroup. For a genuinely relabelling-closed source family this identifies
the union over every chart with the fixed deletion-chart family exactly.
-/
set_option autoImplicit false
noncomputable section
open scoped Classical

namespace SymmetricSubgroupAsymptotics.SingletonExtension

variable {α X F : Type*}

/-- Two charts deleting the same point differ by an actual permutation
of the original complement. This identity holds for every original H. -/
theorem exists_chart_relabel (e e₀ : X ≃ Option α) (x : X)
    (he : e x = none) (he₀ : e₀ x = none) :
    ∃ a : Equiv.Perm α, ∀ H : Subgroup (Equiv.Perm α),
      H.map (extensionHom e) =
        (H.map a.permCongrHom.toMonoidHom).map (extensionHom e₀) := by
  let t : Equiv.Perm (Option α) := e.symm.trans e₀
  have ht : t none = none := by
    change e₀ (e.symm none) = none
    have hx : e.symm none = x := by
      rw [← he, Equiv.symm_apply_apply]
    rw [hx, he₀]
  let a : Equiv.Perm α := Equiv.removeNone t
  have ha : a.optionCongr = t := by
    dsimp only [a]
    rw [map_equiv_removeNone, ht, Equiv.swap_self]
    exact one_mul t
  have hchart (y : X) : e₀ y = a.optionCongr (e y) := by
    rw [ha]
    change e₀ y = e₀ (e.symm (e y))
    rw [Equiv.symm_apply_apply]
  have hcompose (z : Option α) : e₀ (e.symm z) = a.optionCongr z := by
    rw [ha]
    rfl
  have hmaps : (extensionHom e₀).comp a.permCongrHom.toMonoidHom = extensionHom e := by
    apply MonoidHom.ext
    intro g
    apply Equiv.ext
    intro y
    apply e₀.injective
    change e₀ (e₀.symm (Option.map (a.permCongr g) (e₀ y))) =
      e₀ (e.symm (Option.map g (e y)))
    rw [Equiv.apply_symm_apply, hchart y, hcompose]
    cases hy : e y <;>
      simp only [Equiv.optionCongr_apply, Option.map_none, Option.map_some,
        Equiv.permCongr_apply, Equiv.symm_apply_apply]
  refine ⟨a, ?_⟩
  intro H
  rw [Subgroup.map_map, hmaps]

/-- All original singleton extension charts, with the chart and source
witnesses forgotten. The distinguished fixed point is `e.symm none`. -/
abbrev AllChartsFamily (value : F → Subgroup (Equiv.Perm α)) :=
  {K : Subgroup (Equiv.Perm X) //
    ∃ e : X ≃ Option α, ∃ f : F, (value f).map (extensionHom e) = K}

/-- A genuine closure property of the same original source values is
enough. This property is independent of any subgroup-count estimate. -/
theorem allCharts_iff (charts : X → X ≃ Option α)
    (hcharts : ∀ x, charts x x = none) (value : F → Subgroup (Equiv.Perm α))
    (hclosed : ∀ a : Equiv.Perm α, ∀ f : F,
      ∃ f' : F, value f' = (value f).map a.permCongrHom.toMonoidHom)
    (K : Subgroup (Equiv.Perm X)) :
    (∃ e : X ≃ Option α, ∃ f : F, (value f).map (extensionHom e) = K) ↔
      (∃ x : X, ∃ f : F, (value f).map (extensionHom (charts x)) = K) := by
  constructor
  · rintro ⟨e,f,hf⟩
    let x : X := e.symm none
    obtain ⟨a,ha⟩ := exists_chart_relabel e (charts x) x
      (e.apply_symm_apply none) (hcharts x)
    obtain ⟨f',hf'⟩ := hclosed a f
    refine ⟨x,f',?_⟩
    rw [hf']
    exact (ha (value f)).symm.trans hf
  · rintro ⟨x,f,hf⟩
    exact ⟨charts x,f,hf⟩

/-- The equivalence is the identity on actual ambient subgroups. Thus
changing charts does not add a factorial or duplicate physical objects. -/
def allChartsEquiv (charts : X → X ≃ Option α)
    (hcharts : ∀ x, charts x x = none) (value : F → Subgroup (Equiv.Perm α))
    (hclosed : ∀ a : Equiv.Perm α, ∀ f : F,
      ∃ f' : F, value f' = (value f).map a.permCongrHom.toMonoidHom) :
    AllChartsFamily (X := X) value ≃ Family charts value where
  toFun K := ⟨K.1, (allCharts_iff charts hcharts value hclosed K.1).mp K.2⟩
  invFun K := ⟨K.1, (allCharts_iff charts hcharts value hclosed K.1).mpr K.2⟩
  left_inv _ := rfl
  right_inv _ := rfl

theorem card_allChartsFamily_le [Finite X] [Finite F] (charts : X → X ≃ Option α)
    (hcharts : ∀ x, charts x x = none) (value : F → Subgroup (Equiv.Perm α))
    (hclosed : ∀ a : Equiv.Perm α, ∀ f : F,
      ∃ f' : F, value f' = (value f).map a.permCongrHom.toMonoidHom) :
    Nat.card (AllChartsFamily (X := X) value) ≤ Nat.card X * Nat.card F := by
  rw [Nat.card_congr (allChartsEquiv charts hcharts value hclosed)]
  exact card_family_le charts value

end SymmetricSubgroupAsymptotics.SingletonExtension
