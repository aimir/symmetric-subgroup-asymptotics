import SymmetricSubgroupAsymptotics.ImprimitiveBlockEvaluation

/-! Literal block components do not change when an action is pulled
back along a surjective source homomorphism. Stabilizer elements are
lifted in the original group before comparing their fibre permutations. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
namespace SymmetricSubgroupAsymptotics.BlockComponentSurjectiveSource

theorem component_eq
    {G H Ω X : Type} [Group G] [Group H]
    [MulAction G Ω] [MulAction H Ω] [MulAction G X] [MulAction H X]
    (φ : G →* H) (hφ : Function.Surjective φ)
    (hΩ : ∀ (g : G) (ω : Ω), φ g • ω = g • ω)
    (hX : ∀ (g : G) (x : X), φ g • x = g • x)
    (b : Ω → X)
    (hbG : ∀ (g : G) (ω : Ω), b (g • ω) = g • b ω)
    (hbH : ∀ (h : H) (ω : Ω), b (h • ω) = h • b ω) (x : X) :
    originalBlockComponent (A := G) b hbG x = originalBlockComponent (A := H) b hbH x := by
  ext σ
  constructor
  · rintro ⟨g,he⟩
    let h : MulAction.stabilizer H x := ⟨φ g.val,by
      change φ g.val • x = x
      rw [hX]
      exact g.property⟩
    refine ⟨h,?_⟩
    apply Eq.trans _ he
    apply Equiv.ext
    intro ω
    apply Subtype.ext
    exact hΩ g.val ω.val
  · rintro ⟨h,he⟩
    obtain ⟨g,hg⟩ := hφ h.val
    have hfix : g • x = x := by rw [← hX g x,hg]; exact h.property
    let g' : MulAction.stabilizer G x := ⟨g,hfix⟩
    refine ⟨g',?_⟩
    apply Eq.trans _ he
    apply Equiv.ext
    intro ω
    apply Subtype.ext
    change g • ω.val = h.val • ω.val
    rw [← hΩ g ω.val,hg]

end SymmetricSubgroupAsymptotics.BlockComponentSurjectiveSource
