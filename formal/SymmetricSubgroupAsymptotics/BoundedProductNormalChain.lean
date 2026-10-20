import SymmetricSubgroupAsymptotics.BoundedNormalChains

/-! A faithful map to bounded finite factors supplies an actual normal
chain with bounded indices. Consequently every chief section of every
subgroup and quotient has bounded order, with all original correlations
retained. -/
set_option autoImplicit false
noncomputable section
open scoped Classical

namespace SymmetricSubgroupAsymptotics.MarkedC4.OrdinaryNilpotentGeneration

variable {G : Type} [Group G] [Finite G] {B m : ℕ}
    (F : Fin m → Type) [∀ i, Group (F i)] [∀ i, Finite (F i)]

private def prefixKernel (f : G →* ∀ i, F i) (j : ℕ) : Subgroup G :=
  ⨅ i : Fin m, ⨅ (_ : i.val < j),
    ((Pi.evalMonoidHom F i).comp f).ker

omit [Finite G] [∀ i, Finite (F i)] in
private theorem mem_prefixKernel (f : G →* ∀ i, F i) (j : ℕ) (g : G) :
    g ∈ prefixKernel F f j ↔ ∀ i : Fin m, i.val < j → f g i = 1 := by
  simp only [prefixKernel, Subgroup.mem_iInf, MonoidHom.mem_ker,
    MonoidHom.comp_apply, Pi.evalMonoidHom_apply]

/-- The same original coordinate kernels form the bounded chain. No
surjectivity to the factors or abstract product replacement is assumed. -/
def boundedProductNormalChain (f : G →* ∀ i, F i)
    (hf : Function.Injective f) (hF : ∀ i, Nat.card (F i) ≤ B) :
    BoundedNormalChain B G where
  length := m
  layer := prefixKernel F f
  normal j := Subgroup.normal_iInf_normal (fun _ =>
    Subgroup.normal_iInf_normal (fun _ => inferInstance))
  first := by
    apply top_unique
    intro g _
    rw [mem_prefixKernel]
    intro i hi
    omega
  last := by
    apply bot_unique
    intro g hg
    apply Subgroup.mem_bot.mpr
    apply hf
    rw [map_one]
    funext i
    exact (mem_prefixKernel F f m g).mp hg i i.isLt
  decreasing j _ := by
    intro g hg
    rw [mem_prefixKernel] at hg ⊢
    intro i hi
    exact hg i (by omega)
  bound j hj := by
    let i : Fin m := ⟨j, hj⟩
    let c : G →* F i := (Pi.evalMonoidHom F i).comp f
    have heq : prefixKernel F f (j+1) = prefixKernel F f j ⊓ c.ker := by
      ext g
      rw [Subgroup.mem_inf, mem_prefixKernel, mem_prefixKernel]
      constructor
      · intro hg
        exact ⟨fun k hk => hg k (by omega), hg i (by change j < j+1; omega)⟩
      · rintro ⟨hg, hc⟩ k hk
        by_cases hl : k.val < j
        · exact hg k hl
        · have hki : k = i := Fin.ext (by change k.val = j; omega)
          subst k
          exact hc
    calc
      (prefixKernel F f (j+1)).relIndex (prefixKernel F f j) =
          c.ker.relIndex (prefixKernel F f j) := by
            rw [heq, Subgroup.inf_relIndex_left]
      _ = Nat.card ((prefixKernel F f j).map c) := Subgroup.relIndex_ker _ _
      _ ≤ Nat.card (F i) := Nat.card_le_card_of_injective Subtype.val Subtype.val_injective
      _ ≤ B := hF i

/-- Uniform chief-section order control in every original subgroup and
quotient follows from the faithful bounded-factor coordinates. -/
theorem boundedChiefSections_of_faithful_product (f : G →* ∀ i, F i)
    (hf : Function.Injective f) (hF : ∀ i, Nat.card (F i) ≤ B) :
    BoundedChiefSections B G :=
  (boundedProductNormalChain F f hf hF).chiefSections

end SymmetricSubgroupAsymptotics.MarkedC4.OrdinaryNilpotentGeneration
