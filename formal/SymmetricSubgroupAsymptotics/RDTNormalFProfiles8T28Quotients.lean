import SymmetricSubgroupAsymptotics.RDTNormalFProfiles8T28Derived
import SymmetricSubgroupAsymptotics.FiniteQuotientInvariantMasks

/-! Exact center and derived orders of all 13 original 8T28 quotients.
Selected by export_lean_carrier_profiles_selected.py. Stored carrier profiles
are not proof inputs; every mask is bound to the same original elements. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
open scoped commutatorElement
namespace SymmetricSubgroupAsymptotics.RDTBinaryNormal8T28
local instance quotientProfilesSourceGroup : Group Source := BinaryMenuCayley8T28.group

def centerMask (i : Fin 13) (x : Fin 64) : Bool :=
  ((if i.val < 6 then (if i.val < 3 then (if i.val < 1 then #[false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,true,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,true] else (if i.val < 2 then #[false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,true,false,false,false,true,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,true,false,false,false,true] else #[false,false,false,false,false,false,false,false,true,true,false,false,true,true,false,false,false,false,false,false,false,false,false,false,false,false,true,true,false,false,true,true,false,false,false,false,false,false,false,false,true,true,false,false,true,true,false,false,false,false,false,false,false,false,false,false,false,false,true,true,false,false,true,true])) else (if i.val < 4 then #[true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true] else (if i.val < 5 then #[false,false,false,false,false,false,false,false,true,true,false,false,true,true,false,false,false,false,false,false,false,false,false,false,false,false,true,true,false,false,true,true,false,false,false,false,false,false,false,false,true,true,false,false,true,true,false,false,false,false,false,false,false,false,false,false,false,false,true,true,false,false,true,true] else #[false,false,false,false,false,false,false,false,true,true,false,false,true,true,false,false,false,false,false,false,false,false,false,false,false,false,true,true,false,false,true,true,false,false,false,false,false,false,false,false,true,true,false,false,true,true,false,false,false,false,false,false,false,false,false,false,false,false,true,true,false,false,true,true]))) else (if i.val < 9 then (if i.val < 7 then #[true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true] else (if i.val < 8 then #[true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true] else #[true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true])) else (if i.val < 11 then (if i.val < 10 then #[true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true] else #[true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true]) else (if i.val < 12 then #[true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true] else #[true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true])))) : Array Bool)[x.val]!

def intersectionMask (i : Fin 13) (x : Fin 64) : Bool :=
  normalMask i x && normalMask 3 x

def centerLog (i : Fin 13) : ℕ := (if i.val < 6 then (if i.val < 3 then (if i.val < 1 then 1 else (if i.val < 2 then 1 else 2)) else (if i.val < 4 then 3 else (if i.val < 5 then 1 else 1))) else (if i.val < 9 then (if i.val < 7 then 2 else (if i.val < 8 then 2 else 2)) else (if i.val < 11 then (if i.val < 10 then 1 else 1) else (if i.val < 12 then 1 else 0))))
def derivedLog (i : Fin 13) : ℕ := (if i.val < 6 then (if i.val < 3 then (if i.val < 1 then 3 else (if i.val < 2 then 2 else 1)) else (if i.val < 4 then 0 else (if i.val < 5 then 1 else 1))) else (if i.val < 9 then (if i.val < 7 then 0 else (if i.val < 8 then 0 else 0)) else (if i.val < 11 then (if i.val < 10 then 0 else 0) else (if i.val < 12 then 0 else 0))))
def intersectionOrder (i : Fin 13) : ℕ := (if i.val < 6 then (if i.val < 3 then (if i.val < 1 then 1 else (if i.val < 2 then 2 else 4)) else (if i.val < 4 then 8 else (if i.val < 5 then 4 else 4))) else (if i.val < 9 then (if i.val < 7 then 8 else (if i.val < 8 then 8 else 8)) else (if i.val < 11 then (if i.val < 10 then 8 else 8) else (if i.val < 12 then 8 else 8))))

private theorem centerMask_checked0 : ∀ x : Fin 64,
    centerMask 0 x = true ↔ ∀ j : Fin 3,
      normalMask 0 (⁅(⟨x⟩ : Source), generators j⁆).index = true :=
  (Fin.addCases (m := 32) (n := 32) (Fin.addCases (m := 16) (n := 16) (by decide +kernel) (by decide +kernel)) (Fin.addCases (m := 16) (n := 16) (by decide +kernel) (by decide +kernel)))

private theorem centerMask_card0 :
    Fintype.card {x : Fin 64 // centerMask 0 x = true} = 2 := by
  decide +kernel

private theorem intersectionMask_card0 :
    Fintype.card {x : Fin 64 // intersectionMask 0 x = true} = 1 := by
  decide +kernel

private theorem centerMask_checked1 : ∀ x : Fin 64,
    centerMask 1 x = true ↔ ∀ j : Fin 3,
      normalMask 1 (⁅(⟨x⟩ : Source), generators j⁆).index = true :=
  (Fin.addCases (m := 32) (n := 32) (Fin.addCases (m := 16) (n := 16) (by decide +kernel) (by decide +kernel)) (Fin.addCases (m := 16) (n := 16) (by decide +kernel) (by decide +kernel)))

private theorem centerMask_card1 :
    Fintype.card {x : Fin 64 // centerMask 1 x = true} = 4 := by
  decide +kernel

private theorem intersectionMask_card1 :
    Fintype.card {x : Fin 64 // intersectionMask 1 x = true} = 2 := by
  decide +kernel

private theorem centerMask_checked2 : ∀ x : Fin 64,
    centerMask 2 x = true ↔ ∀ j : Fin 3,
      normalMask 2 (⁅(⟨x⟩ : Source), generators j⁆).index = true :=
  (Fin.addCases (m := 32) (n := 32) (Fin.addCases (m := 16) (n := 16) (by decide +kernel) (by decide +kernel)) (Fin.addCases (m := 16) (n := 16) (by decide +kernel) (by decide +kernel)))

private theorem centerMask_card2 :
    Fintype.card {x : Fin 64 // centerMask 2 x = true} = 16 := by
  decide +kernel

private theorem intersectionMask_card2 :
    Fintype.card {x : Fin 64 // intersectionMask 2 x = true} = 4 := by
  decide +kernel

private theorem centerMask_checked3 : ∀ x : Fin 64,
    centerMask 3 x = true ↔ ∀ j : Fin 3,
      normalMask 3 (⁅(⟨x⟩ : Source), generators j⁆).index = true :=
  (Fin.addCases (m := 32) (n := 32) (Fin.addCases (m := 16) (n := 16) (by decide +kernel) (by decide +kernel)) (Fin.addCases (m := 16) (n := 16) (by decide +kernel) (by decide +kernel)))

private theorem centerMask_card3 :
    Fintype.card {x : Fin 64 // centerMask 3 x = true} = 64 := by
  decide +kernel

private theorem intersectionMask_card3 :
    Fintype.card {x : Fin 64 // intersectionMask 3 x = true} = 8 := by
  decide +kernel

private theorem centerMask_checked4 : ∀ x : Fin 64,
    centerMask 4 x = true ↔ ∀ j : Fin 3,
      normalMask 4 (⁅(⟨x⟩ : Source), generators j⁆).index = true :=
  (Fin.addCases (m := 32) (n := 32) (Fin.addCases (m := 16) (n := 16) (by decide +kernel) (by decide +kernel)) (Fin.addCases (m := 16) (n := 16) (by decide +kernel) (by decide +kernel)))

private theorem centerMask_card4 :
    Fintype.card {x : Fin 64 // centerMask 4 x = true} = 16 := by
  decide +kernel

private theorem intersectionMask_card4 :
    Fintype.card {x : Fin 64 // intersectionMask 4 x = true} = 4 := by
  decide +kernel

private theorem centerMask_checked5 : ∀ x : Fin 64,
    centerMask 5 x = true ↔ ∀ j : Fin 3,
      normalMask 5 (⁅(⟨x⟩ : Source), generators j⁆).index = true :=
  (Fin.addCases (m := 32) (n := 32) (Fin.addCases (m := 16) (n := 16) (by decide +kernel) (by decide +kernel)) (Fin.addCases (m := 16) (n := 16) (by decide +kernel) (by decide +kernel)))

private theorem centerMask_card5 :
    Fintype.card {x : Fin 64 // centerMask 5 x = true} = 16 := by
  decide +kernel

private theorem intersectionMask_card5 :
    Fintype.card {x : Fin 64 // intersectionMask 5 x = true} = 4 := by
  decide +kernel

private theorem centerMask_checked6 : ∀ x : Fin 64,
    centerMask 6 x = true ↔ ∀ j : Fin 3,
      normalMask 6 (⁅(⟨x⟩ : Source), generators j⁆).index = true :=
  (Fin.addCases (m := 32) (n := 32) (Fin.addCases (m := 16) (n := 16) (by decide +kernel) (by decide +kernel)) (Fin.addCases (m := 16) (n := 16) (by decide +kernel) (by decide +kernel)))

private theorem centerMask_card6 :
    Fintype.card {x : Fin 64 // centerMask 6 x = true} = 64 := by
  decide +kernel

private theorem intersectionMask_card6 :
    Fintype.card {x : Fin 64 // intersectionMask 6 x = true} = 8 := by
  decide +kernel

private theorem centerMask_checked7 : ∀ x : Fin 64,
    centerMask 7 x = true ↔ ∀ j : Fin 3,
      normalMask 7 (⁅(⟨x⟩ : Source), generators j⁆).index = true :=
  (Fin.addCases (m := 32) (n := 32) (Fin.addCases (m := 16) (n := 16) (by decide +kernel) (by decide +kernel)) (Fin.addCases (m := 16) (n := 16) (by decide +kernel) (by decide +kernel)))

private theorem centerMask_card7 :
    Fintype.card {x : Fin 64 // centerMask 7 x = true} = 64 := by
  decide +kernel

private theorem intersectionMask_card7 :
    Fintype.card {x : Fin 64 // intersectionMask 7 x = true} = 8 := by
  decide +kernel

private theorem centerMask_checked8 : ∀ x : Fin 64,
    centerMask 8 x = true ↔ ∀ j : Fin 3,
      normalMask 8 (⁅(⟨x⟩ : Source), generators j⁆).index = true :=
  (Fin.addCases (m := 32) (n := 32) (Fin.addCases (m := 16) (n := 16) (by decide +kernel) (by decide +kernel)) (Fin.addCases (m := 16) (n := 16) (by decide +kernel) (by decide +kernel)))

private theorem centerMask_card8 :
    Fintype.card {x : Fin 64 // centerMask 8 x = true} = 64 := by
  decide +kernel

private theorem intersectionMask_card8 :
    Fintype.card {x : Fin 64 // intersectionMask 8 x = true} = 8 := by
  decide +kernel

private theorem centerMask_checked9 : ∀ x : Fin 64,
    centerMask 9 x = true ↔ ∀ j : Fin 3,
      normalMask 9 (⁅(⟨x⟩ : Source), generators j⁆).index = true :=
  (Fin.addCases (m := 32) (n := 32) (Fin.addCases (m := 16) (n := 16) (by decide +kernel) (by decide +kernel)) (Fin.addCases (m := 16) (n := 16) (by decide +kernel) (by decide +kernel)))

private theorem centerMask_card9 :
    Fintype.card {x : Fin 64 // centerMask 9 x = true} = 64 := by
  decide +kernel

private theorem intersectionMask_card9 :
    Fintype.card {x : Fin 64 // intersectionMask 9 x = true} = 8 := by
  decide +kernel

private theorem centerMask_checked10 : ∀ x : Fin 64,
    centerMask 10 x = true ↔ ∀ j : Fin 3,
      normalMask 10 (⁅(⟨x⟩ : Source), generators j⁆).index = true :=
  (Fin.addCases (m := 32) (n := 32) (Fin.addCases (m := 16) (n := 16) (by decide +kernel) (by decide +kernel)) (Fin.addCases (m := 16) (n := 16) (by decide +kernel) (by decide +kernel)))

private theorem centerMask_card10 :
    Fintype.card {x : Fin 64 // centerMask 10 x = true} = 64 := by
  decide +kernel

private theorem intersectionMask_card10 :
    Fintype.card {x : Fin 64 // intersectionMask 10 x = true} = 8 := by
  decide +kernel

private theorem centerMask_checked11 : ∀ x : Fin 64,
    centerMask 11 x = true ↔ ∀ j : Fin 3,
      normalMask 11 (⁅(⟨x⟩ : Source), generators j⁆).index = true :=
  (Fin.addCases (m := 32) (n := 32) (Fin.addCases (m := 16) (n := 16) (by decide +kernel) (by decide +kernel)) (Fin.addCases (m := 16) (n := 16) (by decide +kernel) (by decide +kernel)))

private theorem centerMask_card11 :
    Fintype.card {x : Fin 64 // centerMask 11 x = true} = 64 := by
  decide +kernel

private theorem intersectionMask_card11 :
    Fintype.card {x : Fin 64 // intersectionMask 11 x = true} = 8 := by
  decide +kernel

private theorem centerMask_checked12 : ∀ x : Fin 64,
    centerMask 12 x = true ↔ ∀ j : Fin 3,
      normalMask 12 (⁅(⟨x⟩ : Source), generators j⁆).index = true :=
  (Fin.addCases (m := 32) (n := 32) (Fin.addCases (m := 16) (n := 16) (by decide +kernel) (by decide +kernel)) (Fin.addCases (m := 16) (n := 16) (by decide +kernel) (by decide +kernel)))

private theorem centerMask_card12 :
    Fintype.card {x : Fin 64 // centerMask 12 x = true} = 64 := by
  decide +kernel

private theorem intersectionMask_card12 :
    Fintype.card {x : Fin 64 // intersectionMask 12 x = true} = 8 := by
  decide +kernel

theorem centerMask_test (i : Fin 13) (x : Fin 64) :
    centerMask i x = true ↔ ∀ j : Fin 3,
      ⁅(⟨x⟩ : Source), generators j⁆ ∈ (states i).kernel := by
  have h : centerMask i x = true ↔ ∀ j : Fin 3,
      normalMask i (⁅(⟨x⟩ : Source), generators j⁆).index = true := by
    fin_cases i
    · exact centerMask_checked0 x
    · exact centerMask_checked1 x
    · exact centerMask_checked2 x
    · exact centerMask_checked3 x
    · exact centerMask_checked4 x
    · exact centerMask_checked5 x
    · exact centerMask_checked6 x
    · exact centerMask_checked7 x
    · exact centerMask_checked8 x
    · exact centerMask_checked9 x
    · exact centerMask_checked10 x
    · exact centerMask_checked11 x
    · exact centerMask_checked12 x
  exact h.trans (forall_congr' (fun j => normalMask_mem i _))

theorem intersectionMask_mem (i : Fin 13) (x : Fin 64) :
    intersectionMask i x = true ↔
      (⟨x⟩ : Source) ∈ (states i).kernel ⊓ commutator Source := by
  rw [source_derived_eq]
  change (normalMask i x && normalMask 3 x) = true ↔ _
  rw [Bool.and_eq_true]
  exact and_congr (normalMask_mem i ⟨x⟩) (normalMask_mem 3 ⟨x⟩)

theorem centerMask_card (i : Fin 13) :
    Nat.card {x : Fin 64 // centerMask i x = true} =
      2 ^ centerLog i * Nat.card (states i).kernel := by
  rw [Nat.card_eq_fintype_card]
  fin_cases i
  · change Fintype.card {x : Fin 64 // centerMask 0 x = true} =
      2 ^ 1 * Nat.card N0.kernel
    rw [N0.kernel_card]
    exact centerMask_card0
  · change Fintype.card {x : Fin 64 // centerMask 1 x = true} =
      2 ^ 1 * Nat.card N1.kernel
    rw [N1.kernel_card]
    exact centerMask_card1
  · change Fintype.card {x : Fin 64 // centerMask 2 x = true} =
      2 ^ 2 * Nat.card N2.kernel
    rw [N2.kernel_card]
    exact centerMask_card2
  · change Fintype.card {x : Fin 64 // centerMask 3 x = true} =
      2 ^ 3 * Nat.card N3.kernel
    rw [N3.kernel_card]
    exact centerMask_card3
  · change Fintype.card {x : Fin 64 // centerMask 4 x = true} =
      2 ^ 1 * Nat.card N4.kernel
    rw [N4.kernel_card]
    exact centerMask_card4
  · change Fintype.card {x : Fin 64 // centerMask 5 x = true} =
      2 ^ 1 * Nat.card N5.kernel
    rw [N5.kernel_card]
    exact centerMask_card5
  · change Fintype.card {x : Fin 64 // centerMask 6 x = true} =
      2 ^ 2 * Nat.card N6.kernel
    rw [N6.kernel_card]
    exact centerMask_card6
  · change Fintype.card {x : Fin 64 // centerMask 7 x = true} =
      2 ^ 2 * Nat.card N7.kernel
    rw [N7.kernel_card]
    exact centerMask_card7
  · change Fintype.card {x : Fin 64 // centerMask 8 x = true} =
      2 ^ 2 * Nat.card N8.kernel
    rw [N8.kernel_card]
    exact centerMask_card8
  · change Fintype.card {x : Fin 64 // centerMask 9 x = true} =
      2 ^ 1 * Nat.card N9.kernel
    rw [N9.kernel_card]
    exact centerMask_card9
  · change Fintype.card {x : Fin 64 // centerMask 10 x = true} =
      2 ^ 1 * Nat.card N10.kernel
    rw [N10.kernel_card]
    exact centerMask_card10
  · change Fintype.card {x : Fin 64 // centerMask 11 x = true} =
      2 ^ 1 * Nat.card N11.kernel
    rw [N11.kernel_card]
    exact centerMask_card11
  · change Fintype.card {x : Fin 64 // centerMask 12 x = true} =
      2 ^ 0 * Nat.card N12.kernel
    rw [N12.kernel_card]
    exact centerMask_card12

theorem intersectionMask_card (i : Fin 13) :
    Nat.card {x : Fin 64 // intersectionMask i x = true} = intersectionOrder i := by
  rw [Nat.card_eq_fintype_card]
  fin_cases i
  · exact intersectionMask_card0
  · exact intersectionMask_card1
  · exact intersectionMask_card2
  · exact intersectionMask_card3
  · exact intersectionMask_card4
  · exact intersectionMask_card5
  · exact intersectionMask_card6
  · exact intersectionMask_card7
  · exact intersectionMask_card8
  · exact intersectionMask_card9
  · exact intersectionMask_card10
  · exact intersectionMask_card11
  · exact intersectionMask_card12

theorem source_intersection_card (i : Fin 13) :
    Nat.card ↥((states i).kernel ⊓ commutator Source) = intersectionOrder i := by
  let e := sourceIndexEquiv.subtypeEquiv (intersectionMask_mem i)
  exact (Nat.card_congr e).symm.trans (intersectionMask_card i)

theorem source_quotient_center_card (i : Fin 13) :
    Nat.card (Subgroup.center (Source ⧸ (states i).kernel)) = 2 ^ centerLog i :=
  quotientCenter_card_of_mask (states i).kernel generators generators_full sourceIndexEquiv
    (fun x => centerMask i x = true) (centerMask_test i) _ (centerMask_card i)

theorem source_quotient_derived_card (i : Fin 13) :
    Nat.card (commutator (Source ⧸ (states i).kernel)) = 2 ^ derivedLog i := by
  apply quotientCommutator_card_of_inf_card
  rw [source_derived_card, source_intersection_card]
  fin_cases i <;> decide +kernel

end SymmetricSubgroupAsymptotics.RDTBinaryNormal8T28
