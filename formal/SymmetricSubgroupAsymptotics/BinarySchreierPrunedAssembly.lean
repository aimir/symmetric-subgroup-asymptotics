import SymmetricSubgroupAsymptotics.BinarySchreierBindingAssembly
import SymmetricSubgroupAsymptotics.BinarySchreierPrunedAdapter

/-! Bounded assembly of original-action Schreier bindings with proved
order stops. A slice supplies a typed binding at each literal consecutive
index. Adjacent joins preserve that index, including whether its proof is
a source order stop or a complete local Schreier certificate.

Global coverage is concluded only after a full slice and equality with an
actual Sylow subgroup are supplied. No catalogue order or classification
assertion is a premise of a local binding or a substitute for a proof.
-/
set_option autoImplicit false
noncomputable section

namespace SymmetricSubgroupAsymptotics

variable {w N : ℕ}

def BinarySchreierPrunedBindingSlice
    (actions : Fin N → Subgroup (Equiv.Perm (Fin w))) (cap : ℕ)
    (start count : ℕ) (bound : start+count ≤ N) :=
  ∀ i : Fin count, BinarySchreierPrunedBinding actions cap
    (binarySchreierBindingIndex start count bound i)

/-- Each position of the joined slice has exactly its original Fin index;
there is no missing-position fallback. -/
def binarySchreierPrunedBindingSlice_add
    (actions : Fin N → Subgroup (Equiv.Perm (Fin w))) (cap : ℕ)
    (start m n : ℕ) (bound : start+(m+n) ≤ N)
    (left : BinarySchreierPrunedBindingSlice actions cap start m (by omega))
    (right : BinarySchreierPrunedBindingSlice actions cap (start+m) n (by omega)) :
    BinarySchreierPrunedBindingSlice actions cap start (m+n) bound := by
  unfold BinarySchreierPrunedBindingSlice
  refine Fin.addCases ?_ ?_
  · intro i
    simpa only [binarySchreierBindingIndex, Fin.val_castAdd] using left i
  · intro i
    simpa only [binarySchreierBindingIndex, Fin.val_natAdd, Nat.add_assoc] using right i

/-- A complete slice supplies all original-source bindings without a
separate finite classification hypothesis. -/
def binarySchreierPrunedBindings_of_fullSlice
    (actions : Fin N → Subgroup (Equiv.Perm (Fin w))) (cap : ℕ)
    (bindings : BinarySchreierPrunedBindingSlice actions cap 0 N (by omega)) :
    ∀ i, BinarySchreierPrunedBinding actions cap i := by
  intro i
  simpa only [binarySchreierBindingIndex, Nat.zero_add] using bindings i

/-- Every local child above the actual order cap is resolved by its
literal binding. Sources stopped by an order proof are treated by the
same checked local interface as sources with Schreier word proofs. -/
theorem binaryActionChildrenAboveOrder_of_fullSlice
    (actions : Fin N → Subgroup (Equiv.Perm (Fin w))) (cap : ℕ)
    (bindings : BinarySchreierPrunedBindingSlice actions cap 0 N (by omega)) :
    ∀ i, BinaryActionChildrenCoveredAboveOrder actions cap (actions i) :=
  fun i => (binarySchreierPrunedBindings_of_fullSlice actions cap bindings i).children

/-- A complete slice and an actual Sylow root give the original global
small-or-covered conclusion. The Sylow equality is explicit and is not
inferred from a catalogue root label or declared group order. -/
theorem binary_schreier_pruned_registry_complete_of_fullSlice
    (actions : Fin N → Subgroup (Equiv.Perm (Fin w))) (cap : ℕ)
    (P : Sylow 2 (Equiv.Perm (Fin w))) (root : Fin N)
    (hroot : actions root = (P : Subgroup (Equiv.Perm (Fin w))))
    (bindings : BinarySchreierPrunedBindingSlice actions cap 0 N (by omega))
    (H : Subgroup (Equiv.Perm (Fin w))) (hH : IsPGroup 2 H)
    (ht : PermutationSubgroupTransitive H) :
    Nat.card H ≤ cap ∨ ActionRegistryCovered actions H :=
  binary_schreier_pruned_registry_complete actions cap P root hroot
    (binarySchreierPrunedBindings_of_fullSlice actions cap bindings) H hH ht

end SymmetricSubgroupAsymptotics
