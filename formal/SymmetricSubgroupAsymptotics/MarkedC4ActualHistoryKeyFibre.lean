import SymmetricSubgroupAsymptotics.MarkedC4ActualSelectedHistoryData
import SymmetricSubgroupAsymptotics.MarkedC4ActualFixedHistoryBound

/-! A single original order/normal-chain key determines a chosen history.
Every object in its fibre is injected into the SAME reordered schedule;
this is the actual global partition binding, with no supplied count. -/
set_option autoImplicit false
noncomputable section
open scoped Classical BigOperators
namespace SymmetricSubgroupAsymptotics.MarkedC4.ActualHistoryKeyFibre
open ActualExcessHistoryPartition ActualPeelNormalChains ActualChosenHistorySchedule
open RDTOriginalWordStructure RDTNormalFInterface

variable {t : ℕ} (n : Fin t → ℕ)
  (G : ∀ i,Subgroup (Equiv.Perm (Fin (n i)))) (M : Type) [Group M]
  (q : Key n G) (J₀ : Fibre n G M q)

/-- Fixed physical reordering for the whole key fibre, retaining one mark. -/
def code (J : Fibre n G M q) :
    Family (ActualSelectedHistoryData.data n G M J₀.val) M := by
  let e := selectedOrder n G M J₀.val
  refine ⟨ActualHistoryOrderTransport.code (fun i => ↥(G i)) M e J.val,?_⟩
  have hk : key n G M J.val=key n G M J₀.val := J.property.trans J₀.property.symm
  have he : selectedOrder n G M J.val=e := congrArg Prod.fst hk
  have hr : normalChains (fun i => ↥(G i)) J.val.val e=
      normalChains (fun i => ↥(G i)) J₀.val.val e := by
    have hh := congrArg Prod.snd hk
    change normalChains (fun i => ↥(G i)) J.val.val (selectedOrder n G M J.val)=
      normalChains (fun i => ↥(G i)) J₀.val.val e at hh
    rw [he] at hh
    exact hh
  change normalChains (fun i => ↥(G (e i)))
    (ActualHistoryOrderTransport.image (fun i => ↥(G i)) M e J.val.val) 1=_
  exact (ActualHistoryOrderTransport.chains_transport (fun i => ↥(G i)) M e J.val.val).trans
    (congrArg (ActualHistoryOrderTransport.rowsReindex (fun i => ↥(G i)) e) hr)

theorem code_injective : Function.Injective (code n G M q J₀) := by
  intro J K h
  apply Subtype.ext
  apply ActualHistoryOrderTransport.code_injective (fun i => ↥(G i)) M
    (selectedOrder n G M J₀.val)
  exact congrArg (fun z : Family (ActualSelectedHistoryData.data n G M J₀.val) M => z.val) h

/-- The actual key fibre inherits the fixed-history bound from its own
selected representative. There is no external chosen-order premise. -/
theorem card_le (r : ℕ)
    (q₀ : Key n G)
    (J₁ : Fibre n G (ActualGlobalMarkGeneratorRank.Marks r) q₀)
    (hKP : KovacsPraegerBinaryAbelianQuotientBound) (h55 : PublishedTheorem55Binary)
    (h53 : ActualCaseIITargetStructure.PublishedProposition53Binary)
    (h57 : RDTExcessStructure.PublishedTheorem57Binary)
    (h8 : RDTDegreeEightExceptional.PublishedDegreeEightExceptional)
    (hderived : RDTDerivedNormalQuarter.PublishedDerivedNormalQuarterBinary)
    (lit : RDTTheorem46BinaryInput) (C B : ℕ)
    (hpositive : ∀ i,0<n i) (hcut : ∀ i,n i≤C)
    (hG : ∀ i,IsPGroup 2 (G i))
    (htrans : ∀ i,∀ x y : Fin (n i),∃ g : G i,g.val x=y)
    (hB : (∑ i : Fin t,n i)≤B) :
    (Nat.card (Fibre n G (ActualGlobalMarkGeneratorRank.Marks r) q₀) : ℝ) ≤
      ActualFixedHistoryBound.envelope lit C B r t *
        (2 : ℝ)^markedF (∑ i : Fin t,(n i : ℝ)) r := by
  let e := selectedOrder n G (ActualGlobalMarkGeneratorRank.Marks r) J₁.val
  have hi : (Nat.card (Fibre n G (ActualGlobalMarkGeneratorRank.Marks r) q₀) : ℝ) ≤
      Nat.card (Family (ActualSelectedHistoryData.data n G (ActualGlobalMarkGeneratorRank.Marks r) J₁.val)
        (ActualGlobalMarkGeneratorRank.Marks r)) := by
    exact_mod_cast Nat.card_le_card_of_injective _
      (code_injective n G (ActualGlobalMarkGeneratorRank.Marks r) q₀ J₁)
  have hsum : (∑ i : Fin t,n (e i))=∑ i : Fin t,n i :=
    Fintype.sum_equiv e (fun i => n (e i)) n (fun _ => rfl)
  have hsumR : (∑ i : Fin t,(n (e i) : ℝ))=∑ i : Fin t,(n i : ℝ) :=
    Fintype.sum_equiv e (fun i => (n (e i) : ℝ)) (fun i => (n i : ℝ)) (fun _ => rfl)
  have hb := ActualFixedHistoryBound.card_le hKP h55 h53 h57 h8 hderived lit C B r t
    (fun i => n (e i)) (fun i => G (e i))
    (ActualSelectedHistoryData.data n G (ActualGlobalMarkGeneratorRank.Marks r) J₁.val)
    (ActualSelectedHistoryData.chosen n G (ActualGlobalMarkGeneratorRank.Marks r) J₁.val)
    (fun i => hpositive (e i)) (fun i => hcut (e i)) (fun i => hG (e i))
    (fun i => htrans (e i)) (by rw [hsum]; exact hB)
  rw [hsumR] at hb
  exact hi.trans hb

end SymmetricSubgroupAsymptotics.MarkedC4.ActualHistoryKeyFibre
