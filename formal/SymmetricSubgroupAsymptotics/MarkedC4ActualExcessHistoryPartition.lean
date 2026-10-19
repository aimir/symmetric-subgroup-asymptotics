import SymmetricSubgroupAsymptotics.MarkedC4ActualExcessHistorySelection

/-! One global partition by the ACTUAL excessive peel order and ORIGINAL
normal chains. This menu is charged once for the entire raw history; its
fibres retain the same actual marked subgroup for subsequent decoding. -/
set_option autoImplicit false
noncomputable section
open scoped Classical BigOperators
namespace SymmetricSubgroupAsymptotics.MarkedC4.ActualExcessHistoryPartition
open ActualFullPhysicalWordPeel ActualPeelNormalChains ActualExcessHistorySelection

variable {t : ℕ} (degree : Fin t → ℕ)
  (G : ∀ i,Subgroup (Equiv.Perm (Fin (degree i))))
  (M : Type) [Group M]

def full (J : Family (fun i => ↥(G i)) M) (i : Fin t) :
    Function.Surjective (ActualPeelNormalChains.coordinate (fun i => ↥(G i)) J.val i) := J.property i

def selectedList (J : Family (fun i => ↥(G i)) M) : List (Fin t) :=
  Classical.choose (ActualExcessHistorySelection.exists_plan degree G M J.val (full degree G M J) Finset.univ)

theorem selectedPlan (J : Family (fun i => ↥(G i)) M) :
    ActualTableauPeeling.Plan
      (fun i S => (priority degree G M J.val (full degree G M J) S i : ℝ))
      Finset.univ (selectedList degree G M J) :=
  Classical.choose_spec (ActualExcessHistorySelection.exists_plan degree G M J.val
    (full degree G M J) Finset.univ)

/-- The order follows the peel list head-first. It is not reversed as in
the Case-I density tableau: its tails are the actual recursive sources. -/
def selectedOrder (J : Family (fun i => ↥(G i)) M) : Equiv.Perm (Fin t) :=
  (finCongr (show t=(selectedList degree G M J).length by
    simpa only [Finset.card_univ,Fintype.card_fin] using
      (ActualTableauPeeling.Plan.length (selectedPlan degree G M J)).symm)).trans
    (List.Nodup.getEquivOfForallMemList (selectedList degree G M J)
      (ActualSelectedOrderPrefix.Plan.nodup (selectedPlan degree G M J)) (by
        intro i
        apply List.mem_toFinset.mp
        rw [ActualTableauPeeling.Plan.labels (selectedPlan degree G M J)]
        exact Finset.mem_univ i))

abbrev Key := Equiv.Perm (Fin t) × ActualQuotientTableauMenus.RowMenu (fun i => ↥(G i))

def key (J : Family (fun i => ↥(G i)) M) : Key degree G :=
  ⟨selectedOrder degree G M J,
    normalChains (fun i => ↥(G i)) J.val (selectedOrder degree G M J)⟩

def Fibre (q : Key degree G) := {J : Family (fun i => ↥(G i)) M // key degree G M J=q}

/-- The complete history menu partition is an equivalence of actual
objects, not a supplied numerical partition or a recurrence callback. -/
def partitionEquiv : Family (fun i => ↥(G i)) M ≃ Σ q : Key degree G,Fibre degree G M q where
  toFun J := ⟨key degree G M J,J,rfl⟩
  invFun p := p.2.val
  left_inv _ := rfl
  right_inv p := by
    rcases p with ⟨q,J,hJ⟩
    subst q
    rfl

instance fibreFinite [Finite M] (q : Key degree G) : Finite (Fibre degree G M q) := by
  unfold Fibre
  infer_instance

theorem card_eq_sum [Finite M] :
    Nat.card (Family (fun i => ↥(G i)) M)=∑ q : Key degree G,Nat.card (Fibre degree G M q) := by
  letI : Fintype (Family (fun i => ↥(G i)) M) := Fintype.ofFinite _
  letI : ∀ q : Key degree G,Fintype (Fibre degree G M q) := fun _ => Fintype.ofFinite _
  rw [Nat.card_congr (partitionEquiv degree G M),Nat.card_eq_fintype_card,Fintype.card_sigma]
  simp only [Nat.card_eq_fintype_card]

/-- The WHOLE order/normal-chain alphabet has this r-independent cost.
In particular the bound is not multiplied anew at each peel depth. -/
theorem card_key_le (K : ℕ) (hK : ∀ i,Nat.card (G i)≤K) :
    Nat.card (Key degree G)≤t.factorial*(t+1)^((2^K)*t) := by
  simpa only [Nat.card_eq_fintype_card] using
    ActualQuotientTableauMenus.card_order_rows_le (fun i => ↥(G i)) K hK

end SymmetricSubgroupAsymptotics.MarkedC4.ActualExcessHistoryPartition
