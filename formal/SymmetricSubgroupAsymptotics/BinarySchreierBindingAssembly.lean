import SymmetricSubgroupAsymptotics.BinarySchreierActionAdapter

/-!
# Bounded assembly of exact original-family bindings

Each slice supplies a typed binding at every consecutive original index.
Joining two adjacent slices uses dependent finite case analysis, with no
missing-index fallback or assumed action-coverage theorem.
-/
set_option autoImplicit false
noncomputable section
namespace SymmetricSubgroupAsymptotics

variable {w N : ℕ}

def binarySchreierBindingIndex (start count : ℕ) (bound : start+count ≤ N)
    (i : Fin count) : Fin N :=
  ⟨start+i.val, (Nat.add_lt_add_left i.isLt start).trans_le bound⟩

def BinarySchreierBindingSlice
    (actions : Fin N → Subgroup (Equiv.Perm (Fin w)))
    (start count : ℕ) (bound : start+count ≤ N) :=
  ∀ i : Fin count, BinarySchreierActionBinding actions
    (binarySchreierBindingIndex start count bound i)

/-- Adjacent slices account for every index in their union exactly once. -/
def binarySchreierBindingSlice_add
    (actions : Fin N → Subgroup (Equiv.Perm (Fin w)))
    (start m n : ℕ) (bound : start+(m+n) ≤ N)
    (left : BinarySchreierBindingSlice actions start m (by omega))
    (right : BinarySchreierBindingSlice actions (start+m) n (by omega)) :
    BinarySchreierBindingSlice actions start (m+n) bound := by
  unfold BinarySchreierBindingSlice
  refine Fin.addCases ?_ ?_
  · intro i
    simpa only [binarySchreierBindingIndex, Fin.val_castAdd] using left i
  · intro i
    simpa only [binarySchreierBindingIndex, Fin.val_natAdd, Nat.add_assoc] using right i

/-- A slice covering the entire common family supplies the exact universal
binding function required by the actual Sylow-root completeness theorem. -/
def binarySchreierBindings_of_fullSlice
    (actions : Fin N → Subgroup (Equiv.Perm (Fin w)))
    (bindings : BinarySchreierBindingSlice actions 0 N (by omega)) :
    ∀ i, BinarySchreierActionBinding actions i := by
  intro i
  simpa only [binarySchreierBindingIndex, Nat.zero_add] using bindings i

end SymmetricSubgroupAsymptotics
