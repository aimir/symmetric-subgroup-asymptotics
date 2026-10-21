import Mathlib.GroupTheory.PresentedGroup
import Mathlib.GroupTheory.Commutator.Basic
import Mathlib.GroupTheory.QuotientGroup.Basic
import Mathlib.Data.Fin.VecNotation

/-!
# Smaller Y presentations

Ivanov, *Y-groups via transitive extension*, J. Algebra 218 (1999),
412–435: definition p. 413, Table I p. 414, §§3.5–3.8.
Use the derived subgroup and then its center quotient: this removes the
central factors and, for Y442, the outer involution, without conflating Fi24
with its simple derived subgroup Fi24′.
-/

namespace CFSG.Models.YGroups

structure Arms where
  length : Fin 3 → ℕ
  atLeastTwo : ∀ i, 2 ≤ length i

abbrev Node (arms : Arms) := Option ((i : Fin 3) × Fin (arms.length i))

def Adjacent (arms : Arms) : Node arms → Node arms → Prop
  | none, some ⟨_, d⟩ => d.val = 0
  | some ⟨_, d⟩, none => d.val = 0
  | some ⟨i, d⟩, some ⟨j, e⟩ => i = j ∧ (d.val + 1 = e.val ∨ e.val + 1 = d.val)
  | none, none => False

def near (arms : Arms) (i : Fin 3) (d : Fin 2) : Node arms :=
  some ⟨i, ⟨d.val, lt_of_lt_of_le d.isLt (arms.atLeastTwo i)⟩⟩

def spider (arms : Arms) : FreeGroup (Node arms) :=
  FreeGroup.of none * FreeGroup.of (near arms 0 0) * FreeGroup.of (near arms 0 1) *
  FreeGroup.of none * FreeGroup.of (near arms 1 0) * FreeGroup.of (near arms 1 1) *
  FreeGroup.of none * FreeGroup.of (near arms 2 0) * FreeGroup.of (near arms 2 1)

def relations (arms : Arms) : Set (FreeGroup (Node arms)) :=
  {w | (∃ i, w = FreeGroup.of i ^ 2) ∨
       (∃ i j, i ≠ j ∧ Adjacent arms i j ∧ w = (FreeGroup.of i * FreeGroup.of j) ^ 3) ∨
       (∃ i j, i ≠ j ∧ ¬ Adjacent arms i j ∧ w = (FreeGroup.of i * FreeGroup.of j) ^ 2) ∨
       w = spider arms ^ 10}

abbrev Group (arms : Arms) := PresentedGroup (relations arms)
abbrev SimpleSection (arms : Arms) :=
  let D := ↥(commutator (Group arms))
  D ⧸ Subgroup.center D

def arms332 : Arms := ⟨![3, 3, 2], by decide⟩
def arms432 : Arms := ⟨![4, 3, 2], by decide⟩
def arms442 : Arms := ⟨![4, 4, 2], by decide⟩
def arms433 : Arms := ⟨![4, 3, 3], by decide⟩

end CFSG.Models.YGroups

namespace CFSG.Models
abbrev Fischer22 := YGroups.SimpleSection YGroups.arms332
abbrev Fischer23 := YGroups.SimpleSection YGroups.arms432
abbrev Fischer24Prime := YGroups.SimpleSection YGroups.arms442
abbrev BabyMonster := YGroups.SimpleSection YGroups.arms433
end CFSG.Models
