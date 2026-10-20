import SymmetricSubgroupAsymptotics.MarkedC4ActualHistoryOrderTransport
import SymmetricSubgroupAsymptotics.MarkedC4ActualChosenHistorySchedule

/-! Construct the structural chosen schedule from the ACTUAL finite
excess-priority plan, retaining original permutation factors under the
selected physical order. No chosen-order hypothesis is supplied. -/
set_option autoImplicit false
noncomputable section
open scoped Classical
namespace SymmetricSubgroupAsymptotics.MarkedC4.ActualSelectedHistoryData
open ActualExcessHistoryPartition ActualPeelNormalChains ActualHistoryOrderTransport
open ActualChosenHistorySchedule ActualHistoryPriority ActualExcessHistorySelection

private theorem remaining_eq_drop {t : ℕ} (l : List (Fin t)) (hlen : l.length=t)
    (e : Equiv.Perm (Fin t))
    (he : ∀ k : Fin t,e k=l[k.val]'(by rw [hlen]; exact k.isLt)) (m : ℕ) :
    remaining e m=(l.drop m).toFinset := by
  ext i
  constructor
  · intro hi
    have hm : m ≤ (e.symm i).val := (Finset.mem_filter.mp hi).2
    apply List.mem_toFinset.mpr
    apply List.mem_drop_iff_getElem.mpr
    refine ⟨(e.symm i).val-m,by omega,?_⟩
    have hidx : m+((e.symm i).val-m)=(e.symm i).val := by omega
    simpa only [hidx] using (he (e.symm i)).symm.trans (e.apply_symm_apply i)
  · intro hi
    obtain ⟨j,hj,hget⟩ := List.mem_drop_iff_getElem.mp (List.mem_toFinset.mp hi)
    let k : Fin t := ⟨m+j,by omega⟩
    have hek : e k=i := (he k).trans hget
    apply Finset.mem_filter.mpr
    refine ⟨Finset.mem_univ _,?_⟩
    rw [← hek,e.symm_apply_apply]
    change m ≤ m+j
    omega

variable {t : ℕ} (n : Fin t → ℕ)
  (G : ∀ i,Subgroup (Equiv.Perm (Fin (n i))))
  (M : Type) [Group M]
  (J : ActualFullPhysicalWordPeel.Family (fun i => ↥(G i)) M)

theorem selectedOrder_get (k : Fin t) :
    selectedOrder n G M J k=(selectedList n G M J)[k.val]'(by
      have hh := ActualTableauPeeling.Plan.length (selectedPlan n G M J)
      have hlen : (selectedList n G M J).length=t := by
        simpa only [Finset.card_univ,Fintype.card_fin] using hh
      rw [hlen]
      exact k.isLt) := by
  rfl

theorem selected_remaining (m : ℕ) :
    remaining (selectedOrder n G M J) m=((selectedList n G M J).drop m).toFinset := by
  have hlen : (selectedList n G M J).length=t := by
    simpa only [Finset.card_univ,Fintype.card_fin] using
      ActualTableauPeeling.Plan.length (selectedPlan n G M J)
  exact remaining_eq_drop (selectedList n G M J) hlen
    (selectedOrder n G M J) (selectedOrder_get n G M J) m

def data : Data (fun i => n (selectedOrder n G M J i))
    (fun i => G (selectedOrder n G M J i)) where
  rows := rowsReindex (fun i => ↥(G i)) (selectedOrder n G M J)
    (normalChains (fun i => ↥(G i)) J.val (selectedOrder n G M J))
  normal i m := normalChains_normal (fun i => ↥(G i)) J.val J.property
    (selectedOrder n G M J) (selectedOrder n G M J i) m

theorem chosen : Chosen (data n G M J) := by
  intro m i hmi
  have hlen : (selectedList n G M J).length=t := by
    simpa only [Finset.card_univ,Fintype.card_fin] using
      ActualTableauPeeling.Plan.length (selectedPlan n G M J)
  have hm : m.val<(selectedList n G M J).length := by rw [hlen]; exact m.isLt
  have hmax := ActualSelectedOrderPrefix.Plan.tail_maximum (selectedPlan n G M J) m.val hm
  have hmem : selectedOrder n G M J i∈((selectedList n G M J).drop m.val).toFinset := by
    rw [← selected_remaining]
    apply Finset.mem_filter.mpr
    exact ⟨Finset.mem_univ _,by simpa only [(selectedOrder n G M J).symm_apply_apply] using hmi⟩
  have hh := hmax (selectedOrder n G M J i) hmem
  rw [← selected_remaining] at hh
  have hhead := (selectedOrder_get n G M J m).symm
  rw [hhead] at hh
  rw [priority_eq_normal,priority_eq_normal] at hh
  exact_mod_cast hh

theorem reordered_mem :
    normalChains (fun i => ↥(G (selectedOrder n G M J i)))
      (ActualHistoryOrderTransport.code (fun i => ↥(G i)) M (selectedOrder n G M J) J).val 1=
        (data n G M J).rows :=
  chains_transport (fun i => ↥(G i)) M (selectedOrder n G M J) J.val

end SymmetricSubgroupAsymptotics.MarkedC4.ActualSelectedHistoryData
