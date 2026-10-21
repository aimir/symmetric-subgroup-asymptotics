import Mathlib.GroupTheory.PresentedGroup
import Mathlib.GroupTheory.Subgroup.Centralizer
import Mathlib.GroupTheory.Commutator.Basic

/-!
# The Monster from the Y555 presentation of the bimonster

Source: Conway–Norton–Soicher (1988), pp. 27–50; completion by Ivanov
(1992), pp. 46–62, and Norton (1992), pp. 63–76. The exact diagram and
spider word are reproduced in Allcock, *A monstrous proposal*, §2, pp. 3–4.
See `docs/PILOTS.md` for the mathematical identification and its trust boundary.
-/

namespace CFSG.Models.MonsterConstruction

/-- One central node and three arms of five nodes each. -/
abbrev Node := Option (Fin 3 × Fin 5)

/-- Adjacency in Y555: a—bᵢ—cᵢ—dᵢ—eᵢ—fᵢ. -/
def Adjacent : Node → Node → Prop
  | none, some (_, d) => d = 0
  | some (_, d), none => d = 0
  | some (i, d), some (j, e) => i = j ∧ (d.val + 1 = e.val ∨ e.val + 1 = d.val)
  | none, none => False

/-- The nine-letter word a b₁ c₁ a b₂ c₂ a b₃ c₃. -/
def spider : FreeGroup Node :=
  FreeGroup.of none * FreeGroup.of (some (0, 0)) * FreeGroup.of (some (0, 1)) *
  FreeGroup.of none * FreeGroup.of (some (1, 0)) * FreeGroup.of (some (1, 1)) *
  FreeGroup.of none * FreeGroup.of (some (2, 0)) * FreeGroup.of (some (2, 1))

/-- All Coxeter relators, together with the spider relator. -/
def relations : Set (FreeGroup Node) :=
  {w | (∃ i, w = FreeGroup.of i ^ 2) ∨
       (∃ i j, i ≠ j ∧ Adjacent i j ∧ w = (FreeGroup.of i * FreeGroup.of j) ^ 3) ∨
       (∃ i j, i ≠ j ∧ ¬ Adjacent i j ∧ w = (FreeGroup.of i * FreeGroup.of j) ^ 2) ∨
       w = spider ^ 10}

/-- Explicit presented group; no existence hypothesis is used. -/
abbrev Bimonster := PresentedGroup relations

/-- Distinguished central node in the presented group. -/
def nodeA : Bimonster := PresentedGroup.of none

/-- Centralizer of the distinguished node (not of the whole generating set). -/
def nodeCentralizer : Subgroup Bimonster := Subgroup.centralizer {nodeA}

/-- The derived subgroup of that centralizer. Mathematically it is the Monster. -/
abbrev Model := ↥(commutator ↥nodeCentralizer)

end CFSG.Models.MonsterConstruction

namespace CFSG.Models
abbrev Monster := MonsterConstruction.Model
end CFSG.Models
