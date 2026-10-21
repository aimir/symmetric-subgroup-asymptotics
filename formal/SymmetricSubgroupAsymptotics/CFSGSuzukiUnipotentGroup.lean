import SymmetricSubgroupAsymptotics.CFSGSuzukiUnipotentLaw
import Mathlib.GroupTheory.Nilpotent

/-! The actual Suzuki unipotent subgroup, with its exact parameter chart,
cardinality, exponent-four bound and soluble two-group structure. -/
set_option autoImplicit false
noncomputable section
open scoped Classical
namespace SymmetricSubgroupAsymptotics.CFSGSuzukiUnipotent
open CFSG.Models.SuzukiConstruction CFSGSuzukiFieldParameters

def unipotentSubgroup (m : ℕ) : Subgroup (Ambient m) where
  carrier := {g | ∃ a b, g = unipotentElement m a b}
  one_mem' := ⟨0, 0, (unipotentElement_zero m).symm⟩
  mul_mem' := by
    rintro g h ⟨a, b, rfl⟩ ⟨c, d, rfl⟩
    exact ⟨a + c, b + d + theta m a * c, unipotentElement_mul m a b c d⟩
  inv_mem' := by
    rintro g ⟨a, b, rfl⟩
    exact ⟨a, b + theta m a * a, unipotentElement_inv m a b⟩

@[simp] theorem mem_unipotentSubgroup (m : ℕ) (g : Ambient m) :
    g ∈ unipotentSubgroup m ↔ ∃ a b, g = unipotentElement m a b := Iff.rfl

theorem unipotentSubgroup_le_model (m : ℕ) : unipotentSubgroup m ≤ subgroup m := by
  rintro g ⟨a, b, rfl⟩
  exact unipotentElement_mem_model m a b

def parameterEquiv (m : ℕ) :
    (CFSG.Models.SuzukiConstruction.Field m × CFSG.Models.SuzukiConstruction.Field m) ≃
      unipotentSubgroup m :=
  Equiv.ofBijective (fun ab => ⟨unipotentElement m ab.1 ab.2, ⟨ab.1, ab.2, rfl⟩⟩) (by
    constructor
    · intro ab cd h
      exact unipotentElement_injective m (congrArg Subtype.val h)
    · rintro ⟨g, a, b, hg⟩
      exact ⟨(a, b), Subtype.ext hg.symm⟩)

theorem unipotentSubgroup_card (m : ℕ) :
    Nat.card (unipotentSubgroup m) = Nat.card (CFSG.Models.SuzukiConstruction.Field m) ^ 2 := by
  rw [Nat.card_congr (parameterEquiv m).symm, Nat.card_prod, pow_two]

theorem unipotentSubgroup_card_eq (m : ℕ) :
    Nat.card (unipotentSubgroup m) = 2 ^ (2 * (2 * m + 1)) := by
  rw [unipotentSubgroup_card, field_card, ← pow_mul]
  congr 1
  omega

theorem unipotentSubgroup_isPGroup (m : ℕ) : IsPGroup 2 (unipotentSubgroup m) := by
  intro g
  refine ⟨2, ?_⟩
  apply Subtype.ext
  obtain ⟨a, b, hg⟩ := g.property
  change g.val ^ 4 = 1
  rw [hg]
  exact unipotentElement_four m a b

theorem unipotentSubgroup_soluble (m : ℕ) : IsSolvable (unipotentSubgroup m) := by
  letI suzukiUnipotent_nilpotent : Group.IsNilpotent (unipotentSubgroup m) :=
    (unipotentSubgroup_isPGroup m).isNilpotent
  infer_instance

end SymmetricSubgroupAsymptotics.CFSGSuzukiUnipotent
