import SymmetricSubgroupAsymptotics.MarkedC4ActualEfficientLiftMultiplicity
import Mathlib.Data.SetLike.Fintype

/-! A literal finite row inequality for all nilpotent subdirect subgroups
with a prescribed tuple of actual diagonals. The denominator multiplicities
come from ALL recovering lifts, and the numerator consists of triangular
arrays in the original physical product. This retains the diagonal tuple
for subsequent correlated Hall summation. -/
set_option autoImplicit false
noncomputable section
open scoped Classical BigOperators
namespace SymmetricSubgroupAsymptotics.MarkedC4.ActualEfficientRowIncidence
open ActualSubdirectFiltration ActualEfficientLiftRecovery
open ActualEfficientLiftMultiplicity

variable {t : ℕ} (F : Fin t → Type) [∀ i,Group (F i)] [∀ i,Finite (F i)]
  (D : ∀ i,Subgroup (F i))

abbrev Family := {H : Subgroup (∀ i,F i) //
  (∀ i,Function.Surjective (coordinate F H i)) ∧
  Group.IsNilpotent H ∧ ∀ i,diagonal F H i=D i}

local instance familyFintype : Fintype (Family F D) := Fintype.ofFinite _

def labels (H : Family F D) (i : Fin t) :
    {q : F i // q∈normalGenerators F H.val H.property.1 i} ≃
      Fin (normalGen (D i)) :=
  Finite.equivFinOfCardEq (by
    rw [Nat.card_eq_fintype_card,Fintype.card_coe,
      (normalGenerators_spec F H.val H.property.1 i).1,H.property.2.2 i])

/-- Every row is supported on its original initial physical coordinates. -/
abbrev Target := ∀ i : Fin t,Fin (normalGen (D i)) →
  {x : ∀ j,F j // ∀ j : Fin t,i.val<j.val → x j=1}

def code (z : Σ H : Family F D,LiftArray F H.val H.property.1) : Target F D :=
  fun i k =>
    ⟨(z.2 i ((labels F D z.1 i).symm k)).val.val,by
      intro j hj
      exact (mem_prefix F z.1.val (i.val+1)
        (z.2 i ((labels F D z.1 i).symm k)).val).mp
          (z.2 i ((labels F D z.1 i).symm k)).property.1 j (by omega)⟩

def values (a : Target F D) : (Σ i : Fin t,Fin (normalGen (D i))) → ∀ j,F j :=
  fun p => (a p.1 p.2).val

theorem range_code (H : Family F D) (a : LiftArray F H.val H.property.1) :
    Set.range (values F D (code F D ⟨H,a⟩))=
      Set.range (ambientArray F H.val H.property.1 a) := by
  ext x
  constructor
  · rintro ⟨⟨i,k⟩,rfl⟩
    exact ⟨⟨i,(labels F D H i).symm k⟩,rfl⟩
  · rintro ⟨⟨i,q⟩,rfl⟩
    refine ⟨⟨i,labels F D H i q⟩,?_⟩
    exact congrArg (fun q' => (a i q').val.val) ((labels F D H i).symm_apply_apply q)

theorem recover_code (H : Family F D) (a : LiftArray F H.val H.property.1) :
    Subgroup.closure (Set.range (values F D (code F D ⟨H,a⟩)))=H.val := by
  letI : Group.IsNilpotent H.val := H.property.2.1
  rw [range_code F D H a]
  exact ActualEfficientLiftRecovery.recover F H.val H.property.1 a

/-- Distinct actual subgroups have disjoint recovering triangular arrays,
and forgetting proof fields does not collapse arrays inside one fibre. -/
theorem code_injective : Function.Injective (code F D) := by
  rintro ⟨H,a⟩ ⟨K,b⟩ he
  have hHK : H=K := by
    apply Subtype.ext
    exact (recover_code F D H a).symm.trans
      ((congrArg (fun c => Subgroup.closure (Set.range (values F D c))) he).trans
        (recover_code F D K b))
  cases hHK
  have hab : a=b := by
    funext i q
    apply Subtype.ext
    apply Subtype.ext
    have h := congrArg Subtype.val (congrFun (congrFun he i) (labels F D H i q))
    have hq := (labels F D H i).symm_apply_apply q
    exact (congrArg (fun q' => (a i q').val.val) hq).symm.trans
      (h.trans (congrArg (fun q' => (b i q').val.val) hq))
  cases hab
  rfl

/-- Actual fixed-diagonal row incidence. This is an enumeration inequality,
not an encoding hypothesis: all maps and recovery are constructed above. -/
theorem weighted_card_le :
    (∑ H : Family F D,
      ∏ i : Fin t,Nat.card («prefix» F H.val i.val)^normalGen (D i)) ≤
      ∏ i : Fin t,Nat.card
        {x : ∀ j,F j // ∀ j : Fin t,i.val<j.val → x j=1}^normalGen (D i) := by
  have h := Nat.card_le_card_of_injective (code F D) (code_injective F D)
  rw [Nat.card_sigma] at h
  have hleft : (∑ H : Family F D,Nat.card (LiftArray F H.val H.property.1))=
      ∑ H : Family F D,
        ∏ i : Fin t,Nat.card («prefix» F H.val i.val)^normalGen (D i) := by
    apply Finset.sum_congr rfl
    intro H _
    rw [card_liftArray F H.val H.property.1]
    apply Finset.prod_congr rfl
    intro i _
    rw [H.property.2.2 i]
  rw [hleft] at h
  have hright : Nat.card (Target F D)=
      ∏ i : Fin t,Nat.card
        {x : ∀ j,F j // ∀ j : Fin t,i.val<j.val → x j=1}^normalGen (D i) := by
    change Nat.card (∀ i : Fin t,Fin (normalGen (D i)) →
      {x : ∀ j,F j // ∀ j : Fin t,i.val<j.val → x j=1})=_
    rw [Nat.card_pi]
    apply Finset.prod_congr rfl
    intro i _
    rw [Nat.card_fun,Nat.card_fin]
  rw [hright] at h
  exact h

end SymmetricSubgroupAsymptotics.MarkedC4.ActualEfficientRowIncidence
