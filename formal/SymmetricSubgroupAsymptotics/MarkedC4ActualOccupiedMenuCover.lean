import SymmetricSubgroupAsymptotics.MarkedC4ActualGlobalMenuCover

/-! Only menus actually selected by some source are retained. This is
essential: their representative supplies the greedy density inequalities
for the whole fixed-tableau family; arbitrary unused menus need not do so. -/
set_option autoImplicit false
noncomputable section
open scoped Classical
namespace SymmetricSubgroupAsymptotics.MarkedC4.ActualOccupiedMenuCover
open ActualWordMenuPartition

variable {t : ℕ} (F : Fin t → Type) [∀ i,Group (F i)] [∀ i,Finite (F i)]
  (weight : Fin t → ℕ)

abbrev Occupied := {q : Menu F // ∃ H : Family F,key F weight H=q}
def representative (q : Occupied F weight) : Family F := Classical.choose q.property
theorem representative_key (q : Occupied F weight) :
    key F weight (representative F weight q)=q.val := Classical.choose_spec q.property

abbrev Cover (E : Type) [CommGroup E] := Σ q : Occupied F weight,
  Σ U : MenuFamily F q.val,AbelianProductGraphClassification.FullSecond E U.val.val

def forget (E : Type) [CommGroup E] (z : Cover F weight E) :
    ActualGlobalMenuCover.MenuCover F E := ⟨z.1.val,z.2⟩

def code (E : Type) [CommGroup E] (z : ActualGlobalMenuCover.ActualFamily F E) :
    Cover F weight E :=
  ⟨⟨key F weight z.1,⟨z.1,rfl⟩⟩,(ActualGlobalMenuCover.code F weight E z).2⟩

theorem code_injective (E : Type) [CommGroup E] : Function.Injective (code F weight E) := by
  intro z w h
  apply ActualGlobalMenuCover.code_injective F weight E
  exact congrArg (forget F weight E) h

theorem card_le_cover (E : Type) [CommGroup E] [Finite E] :
    Nat.card (ActualGlobalMenuCover.ActualFamily F E)≤Nat.card (Cover F weight E) :=
  Nat.card_le_card_of_injective (code F weight E) (code_injective F weight E)

theorem occupied_menu_card_le (K : ℕ) (hK : ∀ i,Nat.card (F i)≤K) :
    Nat.card (Occupied F weight)≤t.factorial*(t+1)^((2^K)*t) := by
  have h := Nat.card_le_card_of_injective
    (fun q : Occupied F weight => q.val) Subtype.val_injective
  apply h.trans
  simpa only [Nat.card_eq_fintype_card] using
    ActualQuotientTableauMenus.card_order_rows_le F K hK

end SymmetricSubgroupAsymptotics.MarkedC4.ActualOccupiedMenuCover
