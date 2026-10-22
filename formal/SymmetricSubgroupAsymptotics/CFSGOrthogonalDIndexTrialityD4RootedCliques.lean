import Mathlib.Data.Set.Basic

/-! Maximal cliques through a vertex are exactly maximal cliques in
its original neighbourhood. This retains vertices and does not pass
to a twin quotient. -/
set_option autoImplicit false
namespace SymmetricSubgroupAsymptotics.CFSGOrthogonalDIndexTrialityD4RootedCliques
variable {X : Type*} (R : X → X → Prop)

def Clique (S : Set X) : Prop := ∀ a ∈ S, ∀ b ∈ S, a = b ∨ R a b

def MaximalClique (S : Set X) : Prop :=
  Clique R S ∧ ∀ T, Clique R T → S ⊆ T → T ⊆ S

def RootExtension (x : X) (S : Set {y : X // R x y}) : Set X :=
  {y | y = x ∨ ∃ h : R x y, (⟨y, h⟩ : {y : X // R x y}) ∈ S}

theorem rootExtension_clique (hsym : ∀ {a b}, R a b → R b a) (x : X)
    (S : Set {y : X // R x y})
    (hS : Clique (fun a b : {y : X // R x y} => R a.val b.val) S) :
    Clique R (RootExtension R x S) := by
  intro a ha b hb
  rcases ha with rfl | ⟨ha, haS⟩
  · rcases hb with rfl | ⟨hb, _⟩
    · exact Or.inl rfl
    · exact Or.inr hb
  · rcases hb with rfl | ⟨hb, hbS⟩
    · exact Or.inr (hsym ha)
    · rcases hS ⟨a, ha⟩ haS ⟨b, hb⟩ hbS with he | hr
      · exact Or.inl (congrArg Subtype.val he)
      · exact Or.inr hr

theorem rootExtension_mono (x : X) {S T : Set {y : X // R x y}} (h : S ⊆ T) :
    RootExtension R x S ⊆ RootExtension R x T := by
  intro a ha
  rcases ha with ha | ⟨ha, haS⟩
  · exact Or.inl ha
  · exact Or.inr ⟨ha, h haS⟩

theorem mem_rootExtension_iff (x : X) (hirr : ¬ R x x)
    (S : Set {y : X // R x y}) (y : {y : X // R x y}) :
    y.val ∈ RootExtension R x S ↔ y ∈ S := by
  constructor
  · rintro (he | ⟨hy, hyS⟩)
    · have hh : R x x := by
        have hy := y.property
        rw [he] at hy
        exact hy
      exact False.elim (hirr hh)
    · exact hyS
  · intro hy
    exact Or.inr ⟨y.property, hy⟩

theorem maximal_rootExtension_iff (hsym : ∀ {a b}, R a b → R b a)
    (x : X) (hirr : ¬ R x x) (S : Set {y : X // R x y}) :
    MaximalClique R (RootExtension R x S) ↔
      MaximalClique (fun a b : {y : X // R x y} => R a.val b.val) S := by
  constructor
  · intro h
    refine ⟨?_, ?_⟩
    · intro a ha b hb
      have hh := h.1 a.val ((mem_rootExtension_iff R x hirr S a).mpr ha)
        b.val ((mem_rootExtension_iff R x hirr S b).mpr hb)
      rcases hh with he | hr
      · exact Or.inl (Subtype.ext he)
      · exact Or.inr hr
    · intro T hT hST y hy
      have hm := h.2 (RootExtension R x T) (rootExtension_clique R hsym x T hT)
        (rootExtension_mono R x hST)
      exact (mem_rootExtension_iff R x hirr S y).mp
        (hm ((mem_rootExtension_iff R x hirr T y).mpr hy))
  · intro h
    refine ⟨rootExtension_clique R hsym x S h.1, ?_⟩
    intro T hT hST y hy
    have hx : x ∈ T := hST (Or.inl rfl)
    let U : Set {y : X // R x y} := {z | z.val ∈ T}
    have hU : Clique (fun a b : {y : X // R x y} => R a.val b.val) U := by
      intro a ha b hb
      rcases hT a.val ha b.val hb with he | hr
      · exact Or.inl (Subtype.ext he)
      · exact Or.inr hr
    have hSU : S ⊆ U := fun z hz => hST ((mem_rootExtension_iff R x hirr S z).mpr hz)
    have hm := h.2 U hU hSU
    rcases hT x hx y hy with he | hr
    · exact Or.inl he.symm
    · exact Or.inr ⟨hr, hm hy⟩

theorem clique_eq_rootExtension (x : X) (T : Set X) (hT : Clique R T) (hx : x ∈ T) :
    T = RootExtension R x {y : {y : X // R x y} | y.val ∈ T} := by
  apply Set.Subset.antisymm
  · intro y hy
    rcases hT x hx y hy with he | hr
    · exact Or.inl he.symm
    · exact Or.inr ⟨hr, hy⟩
  · rintro y (rfl | ⟨_, hy⟩)
    · exact hx
    · exact hy

end SymmetricSubgroupAsymptotics.CFSGOrthogonalDIndexTrialityD4RootedCliques
