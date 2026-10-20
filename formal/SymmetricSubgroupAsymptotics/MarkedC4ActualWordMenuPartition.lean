import SymmetricSubgroupAsymptotics.MarkedC4ActualQuotientTableauMenus
import SymmetricSubgroupAsymptotics.MarkedC4ActualHallSourceTransport
import SymmetricSubgroupAsymptotics.MarkedC4ActualSelectedTableauPacket

/-! A literal global partition of the actual physical subdirect family by
its constructed greedy order and r-independent tableau menu. -/
set_option autoImplicit false
noncomputable section
open scoped Classical
namespace SymmetricSubgroupAsymptotics.MarkedC4.ActualWordMenuPartition
open ActualSubdirectFiltration ActualQuotientTableauMenus ActualOrderedSubdirectTransport

variable {t : ℕ} (F : Fin t → Type) [∀ i,Group (F i)] [∀ i,Finite (F i)]

abbrev Family := {H : Subgroup (∀ i,F i) //
  (∀ i,Function.Surjective (coordinate F H i)) ∧ Group.IsNilpotent H}

def selectedList (weight : Fin t → ℕ) (H : Family F) : List (Fin t) :=
  Classical.choose (ActualTableauPeeling.exists_plan
    (ActualLogPeelingAndSelfCost.density F H.val weight) Finset.univ)

theorem selectedPlan (weight : Fin t → ℕ) (H : Family F) :
    ActualTableauPeeling.Plan (ActualLogPeelingAndSelfCost.density F H.val weight)
      Finset.univ (selectedList F weight H) :=
  Classical.choose_spec (ActualTableauPeeling.exists_plan
    (ActualLogPeelingAndSelfCost.density F H.val weight) Finset.univ)

theorem selectedLength (weight : Fin t → ℕ) (H : Family F) :
    (selectedList F weight H).length=t := by
  simpa only [Finset.card_univ,Fintype.card_fin] using (selectedPlan F weight H).length

def selectedOrder (weight : Fin t → ℕ) (H : Family F) : Equiv.Perm (Fin t) :=
  (finCongr (selectedLength F weight H).symm).trans
    (ActualSelectedOrderPrefix.reverseOrder (selectedPlan F weight H))

abbrev Menu := Equiv.Perm (Fin t) × RowMenu F

def key (weight : Fin t → ℕ) (H : Family F) : Menu F :=
  ⟨selectedOrder F weight H,orderedRows F (selectedOrder F weight H) H.val⟩

abbrev menuFactors (q : Menu F) := Factors q.1 F
def menuDiagonal (q : Menu F) (i : Fin t) : Subgroup (menuFactors F q i) :=
  (q.2 (q.1 i)).val i
def menuTableau (q : Menu F) (i j : Fin t) : Subgroup (menuFactors F q j) :=
  (q.2 (q.1 j)).val i

abbrev MenuFamily (q : Menu F) := ActualTableauRowIncidence.TableauFamily
  (menuFactors F q) (menuDiagonal F q) (menuTableau F q)

def toMenu (weight : Fin t → ℕ) (H : Family F) : MenuFamily F (key F weight H) := by
  let e := selectedOrder F weight H
  letI : Group.IsNilpotent H.val := H.property.2
  refine ⟨⟨image e F H.val,subdirect e F H.val H.property.1,
    Group.nilpotent_of_mulEquiv (sourceEquiv e F H.val),?_⟩,?_⟩
  · intro i
    exact (diagonal_eq_entry e F H.val i).trans
      (ActualSelectedOrderPrefix.ordered_entry e F H.val (i.val+1) i).symm
  · intro i j
    exact (ActualSelectedTableauPacket.entry_transport F H.val e i j).trans
      (ActualSelectedOrderPrefix.ordered_entry e F H.val (i.val+1) j).symm

/-- Reordering at a fixed menu recovers the SAME original physical subgroup. -/
theorem image_injective (e : Equiv.Perm (Fin t)) :
    Function.Injective (image e F) := by
  intro H K he
  apply (Subgroup.map_injective (f := (physicalEquiv e F).toMonoidHom)
    (physicalEquiv e F).injective)
  exact he

def fibreMap (weight : Fin t → ℕ) (q : Menu F)
    (H : {H : Family F // key F weight H=q}) : MenuFamily F q :=
  H.property ▸ toMenu F weight H.val

theorem fibreMap_injective (weight : Fin t → ℕ) (q : Menu F) :
    Function.Injective (fibreMap F weight q) := by
  intro H K he
  apply Subtype.ext
  apply Subtype.ext
  apply image_injective F q.1
  have hh : (fibreMap F weight q H).val.val=image q.1 F H.val.val := by
    rcases H with ⟨H,rfl⟩
    rfl
  have hk : (fibreMap F weight q K).val.val=image q.1 F K.val.val := by
    rcases K with ⟨K,rfl⟩
    rfl
  exact hh.symm.trans ((congrArg (fun J : MenuFamily F q => J.val.val) he).trans hk)

def fibreSourceEquiv (weight : Fin t → ℕ) (q : Menu F)
    (H : {H : Family F // key F weight H=q}) :
    H.val.val ≃* (fibreMap F weight q H).val.val := by
  rcases H with ⟨H,rfl⟩
  exact sourceEquiv (selectedOrder F weight H) F H.val

/-- All actual Hall fibres in one menu inject into the complete actual
tableau Hall family. The source equivalence preserves every global mark. -/
def hallFibreMap (weight : Fin t → ℕ) (q : Menu F) (E : Type) [CommGroup E]
    (z : Σ H : {H : Family F // key F weight H=q},
      AbelianProductGraphClassification.FullSecond E H.val.val) :
    Σ U : MenuFamily F q,AbelianProductGraphClassification.FullSecond E U.val.val :=
  ⟨fibreMap F weight q z.1,
    ActualHallSourceTransport.fibreEquiv E (fibreSourceEquiv F weight q z.1) z.2⟩

theorem hallFibreMap_injective (weight : Fin t → ℕ) (q : Menu F)
    (E : Type) [CommGroup E] : Function.Injective (hallFibreMap F weight q E) := by
  rintro ⟨H,J⟩ ⟨K,L⟩ he
  have hHK : H=K := fibreMap_injective F weight q (congrArg Sigma.fst he)
  subst K
  have hJL : J=L := (ActualHallSourceTransport.fibreEquiv E
    (fibreSourceEquiv F weight q H)).injective (by
      simpa only [hallFibreMap,Sigma.mk.inj_iff,heq_eq_eq,true_and] using he)
  subst L
  rfl

theorem hall_fibre_card_le (weight : Fin t → ℕ) (q : Menu F)
    (E : Type) [CommGroup E] [Finite E] :
    Nat.card (Σ H : {H : Family F // key F weight H=q},
      AbelianProductGraphClassification.FullSecond E H.val.val)≤
    Nat.card (Σ U : MenuFamily F q,
      AbelianProductGraphClassification.FullSecond E U.val.val) :=
  Nat.card_le_card_of_injective (hallFibreMap F weight q E)
    (hallFibreMap_injective F weight q E)

end SymmetricSubgroupAsymptotics.MarkedC4.ActualWordMenuPartition
