import SymmetricSubgroupAsymptotics.CFSGConnectedBipartiteOrientation

/-! A reusable incidence-geometry orientation lemma. Common neighbours
connect the point side, and every hyperplane has a point. Every incidence
automorphism then either preserves both sides or exchanges them globally. -/
set_option autoImplicit false
noncomputable section
open scoped Classical
namespace SymmetricSubgroupAsymptotics.CFSGIncidenceOrientation
variable {P H : Type*}

def incidenceGraph (R : P → H → Prop) : SimpleGraph (P ⊕ H) where
  Adj x y := match x, y with
    | .inl p, .inr h => R p h
    | .inr h, .inl p => R p h
    | _, _ => False
  symm := by
    intro x y h
    cases x <;> cases y <;> exact h
  loopless := by
    constructor
    intro x
    cases x <;> exact not_false

def sideColoring (R : P → H → Prop) : (incidenceGraph R).Coloring Bool :=
  SimpleGraph.Coloring.mk (Sum.elim (fun _ => false) (fun _ => true)) (by
    intro x y h
    cases x <;> cases y <;> simp_all [incidenceGraph])

theorem connected [Nonempty P] (R : P → H → Prop)
    (hPP : ∀ p q : P, ∃ h : H, R p h ∧ R q h)
    (hHP : ∀ h : H, ∃ p : P, R p h) : (incidenceGraph R).Connected := by
  let p₀ : P := Classical.choice inferInstance
  have hreach (p q : P) : (incidenceGraph R).Reachable (.inl p) (.inl q) := by
    obtain ⟨h, hp, hq⟩ := hPP p q
    exact (show (incidenceGraph R).Adj (.inl p) (.inr h) from hp).reachable.trans
      (show (incidenceGraph R).Adj (.inr h) (.inl q) from hq).reachable
  apply (SimpleGraph.connected_iff_exists_forall_reachable (incidenceGraph R)).mpr
  refine ⟨Sum.inl p₀, ?_⟩
  rintro (p | h)
  · exact hreach p₀ p
  · obtain ⟨p, hp⟩ := hHP h
    exact (hreach p₀ p).trans
      (show (incidenceGraph R).Adj (.inl p) (.inr h) from hp).reachable

theorem automorphism_preserves_or_exchanges [Nonempty P] (R : P → H → Prop)
    (hPP : ∀ p q : P, ∃ h : H, R p h ∧ R q h)
    (hHP : ∀ h : H, ∃ p : P, R p h)
    (e : incidenceGraph R ≃g incidenceGraph R) :
    ((∀ p, sideColoring R (e (.inl p)) = false) ∧
      (∀ h, sideColoring R (e (.inr h)) = true)) ∨
    ((∀ p, sideColoring R (e (.inl p)) = true) ∧
      (∀ h, sideColoring R (e (.inr h)) = false)) := by
  let c := sideColoring R
  let d : (incidenceGraph R).Coloring Bool := c.comp e.toHom
  rcases CFSGConnectedBipartiteOrientation.eq_or_global_complement
    (connected R hPP hHP) c d with heq | hflip
  · left
    constructor
    · intro p
      exact (congrArg (fun z : (incidenceGraph R).Coloring Bool => z (.inl p)) heq).symm
    · intro h
      exact (congrArg (fun z : (incidenceGraph R).Coloring Bool => z (.inr h)) heq).symm
  · right
    constructor
    · intro p
      exact hflip (.inl p)
    · intro h
      exact hflip (.inr h)

end SymmetricSubgroupAsymptotics.CFSGIncidenceOrientation
