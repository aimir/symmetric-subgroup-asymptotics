import SymmetricSubgroupAsymptotics.CFSGConnectedBipartiteOrientation
import Mathlib.GroupTheory.Index

/-! The subgroup preserving the two sides of a connected bipartite geometry
has index at most two. The action is literal, and its kernel need not be
trivial. This separates the orientation factor from subsequent collineation
counts. -/
set_option autoImplicit false
noncomputable section
open scoped Classical
namespace SymmetricSubgroupAsymptotics.CFSGColorOrientationIndex
variable {G V : Type*} [Group G] [MulAction G V] {Γ : SimpleGraph V}

def colorStabilizer (c : Γ.Coloring Bool) : Subgroup G where
  carrier := {g | ∀ v, c (g • v) = c v}
  one_mem' := by simp
  mul_mem' := by
    intro g h hg hh v
    rw [mul_smul, hg, hh]
  inv_mem' := by
    intro g hg v
    simpa using (hg (g⁻¹ • v)).symm

def translateColoring (c : Γ.Coloring Bool)
    (hact : ∀ g : G, ∀ v w, Γ.Adj v w → Γ.Adj (g • v) (g • w))
    (g : G) : Γ.Coloring Bool :=
  SimpleGraph.Coloring.mk (fun v => c (g⁻¹ • v)) (by
    intro v w hvw
    exact c.valid (hact g⁻¹ v w hvw))

def cosetColoring (c : Γ.Coloring Bool)
    (hact : ∀ g : G, ∀ v w, Γ.Adj v w → Γ.Adj (g • v) (g • w)) :
    G ⧸ colorStabilizer c → Γ.Coloring Bool :=
  Quotient.lift (translateColoring c hact) (by
    intro g h hrel
    have hh : ∀ v, c ((g⁻¹ * h) • v) = c v :=
      (QuotientGroup.leftRel_apply.mp hrel)
    ext v
    simpa [translateColoring, mul_smul] using hh (h⁻¹ • v))

theorem cosetColoring_injective (c : Γ.Coloring Bool)
    (hact : ∀ g : G, ∀ v w, Γ.Adj v w → Γ.Adj (g • v) (g • w)) :
    Function.Injective (cosetColoring c hact) := by
  intro x y
  refine Quotient.inductionOn₂ x y ?_
  intro g h heq
  apply Quotient.sound
  apply QuotientGroup.leftRel_apply.mpr
  intro v
  have hv := congrArg (fun z : Γ.Coloring Bool => z (h • v)) heq
  change c (g⁻¹ • (h • v)) = c (h⁻¹ • (h • v)) at hv
  simpa [mul_smul] using hv

theorem index_le_two (hΓ : Γ.Connected) (c : Γ.Coloring Bool)
    (hact : ∀ g : G, ∀ v w, Γ.Adj v w → Γ.Adj (g • v) (g • w)) :
    (colorStabilizer (G := G) c).index ≤ 2 := by
  obtain ⟨v₀⟩ := hΓ.nonempty
  letI : Finite (Γ.Coloring Bool) := Finite.of_injective
    (fun d : Γ.Coloring Bool => d v₀)
    (CFSGConnectedBipartiteOrientation.evaluation_injective hΓ v₀)
  exact (Nat.card_le_card_of_injective (cosetColoring c hact)
    (cosetColoring_injective c hact)).trans
      (CFSGConnectedBipartiteOrientation.card_colorings_le_two hΓ)

theorem card_le_two_mul_stabilizer (hΓ : Γ.Connected) (c : Γ.Coloring Bool)
    (hact : ∀ g : G, ∀ v w, Γ.Adj v w → Γ.Adj (g • v) (g • w)) :
    Nat.card G ≤ 2 * Nat.card (colorStabilizer (G := G) c) := by
  rw [← (colorStabilizer (G := G) c).card_mul_index]
  exact (Nat.mul_le_mul_left _ (index_le_two hΓ c hact)).trans_eq (Nat.mul_comm _ _)

end SymmetricSubgroupAsymptotics.CFSGColorOrientationIndex
