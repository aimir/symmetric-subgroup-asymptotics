import SymmetricSubgroupAsymptotics.MarkedC4ActualSubdirectFiltration
import SymmetricSubgroupAsymptotics.MarkedC4ActualSelectedOrderPrefix
import SymmetricSubgroupAsymptotics.MarkedC4FiniteMonotoneChainCount
import Mathlib.Data.SetLike.Fintype
import Mathlib.Data.Fintype.Powerset
import Mathlib.Data.Fintype.Perm

/-! Fixed finite menus for ACTUAL bounded quotient factors. No transitive
action is asserted for a quotient. Only its actual group order is used; the
original physical degree remains an independent retained weight. -/
set_option autoImplicit false
noncomputable section
open scoped Classical BigOperators
namespace SymmetricSubgroupAsymptotics.MarkedC4.ActualQuotientTableauMenus
open ActualSubdirectFiltration FiniteMonotoneChainCount

variable {t : ℕ} (F : Fin t → Type) [∀ i,Group (F i)] [∀ i,Finite (F i)]
local instance (i : Fin t) : Fintype (F i) := Fintype.ofFinite _
local instance (i : Fin t) : Fintype (Subgroup (F i)) := Fintype.ofFinite _

def RowMenu := ∀ i : Fin t,Chain t (Subgroup (F i))
instance : Fintype (RowMenu F) := by unfold RowMenu; infer_instance

theorem prefix_mono_of_le (H : Subgroup (∀ i,F i)) {m n : ℕ} (hmn : m≤n) :
    «prefix» F H m≤«prefix» F H n := by
  intro h hh
  apply (mem_prefix F H n h).mpr
  intro i hi
  exact (mem_prefix F H m h).mp hh i (hmn.trans hi)

/-- Every actual upper prefix tableau belongs to this fixed finite menu. -/
def actualRows (H : Subgroup (∀ i,F i)) : RowMenu F := fun i =>
  ⟨fun j : Fin t => («prefix» F H (j.val+1)).map (coordinate F H i),by
    intro j k hjk
    exact Subgroup.map_mono (prefix_mono_of_le F H (by omega))⟩

/-- Selected orders do not change the fixed physical row menus. Columns
follow the selected order while rows retain their ORIGINAL factor types. -/
def orderedRows (e : Equiv.Perm (Fin t)) (H : Subgroup (∀ i,F i)) : RowMenu F :=
  fun i => ⟨fun j : Fin t =>
    (ActualSelectedOrderPrefix.orderedPrefix e F H (j.val+1)).map (coordinate F H i),by
      intro j k hjk
      apply Subgroup.map_mono
      intro h hh
      apply (ActualSelectedOrderPrefix.mem_orderedPrefix e F H (k.val+1) h).mpr
      intro p hp
      exact (ActualSelectedOrderPrefix.mem_orderedPrefix e F H (j.val+1) h).mp hh p (by omega)⟩

theorem subgroup_menu_le (K : ℕ) (hK : ∀ i,Nat.card (F i)≤K) (i : Fin t) :
    Fintype.card (Subgroup (F i))≤2^K := by
  have h := Fintype.card_le_of_injective
    (fun U : Subgroup (F i) => (U : Set (F i))) SetLike.coe_injective
  rw [Fintype.card_set] at h
  have hi : Fintype.card (F i)≤K := by simpa only [Nat.card_eq_fintype_card] using hK i
  exact h.trans (pow_le_pow_right₀ (by omega : 1≤(2 : ℕ)) hi)

/-- Uniform r-independent normal-tableau menu cost for literal quotients. -/
theorem card_rowMenu_le (K : ℕ) (hK : ∀ i,Nat.card (F i)≤K) :
    Fintype.card (RowMenu F)≤(t+1)^((2^K)*t) := by
  change Fintype.card (∀ i : Fin t,Chain t (Subgroup (F i)))≤_
  rw [Fintype.card_pi]
  calc
    _ ≤ ∏ _i : Fin t,(t+1)^(2^K) := by
      apply Finset.prod_le_prod'
      intro i _
      exact (card_chain_le t (Subgroup (F i))).trans
        (pow_le_pow_right₀ (by omega : 1≤t+1) (subgroup_menu_le F K hK i))
    _ = ((t+1)^(2^K))^t := by
      simp only [Finset.prod_const,Finset.card_univ,Fintype.card_fin]
    _ = (t+1)^((2^K)*t) := (pow_mul _ _ _).symm

/-- The selected physical order and its actual row tableau have this one
finite alphabet, depending only on physical factors and cutoff, never r. -/
theorem card_order_rows_le (K : ℕ) (hK : ∀ i,Nat.card (F i)≤K) :
    Fintype.card (Equiv.Perm (Fin t) × RowMenu F)≤
      t.factorial*(t+1)^((2^K)*t) := by
  rw [Fintype.card_prod,Fintype.card_perm,Fintype.card_fin]
  exact Nat.mul_le_mul_left _ (card_rowMenu_le F K hK)

end SymmetricSubgroupAsymptotics.MarkedC4.ActualQuotientTableauMenus
