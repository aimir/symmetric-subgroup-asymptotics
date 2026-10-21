import SymmetricSubgroupAsymptotics.GeneratedRDTNormal8T28.Registry
import SymmetricSubgroupAsymptotics.DerivedGeneratorWords
import SymmetricSubgroupAsymptotics.FiniteQuotientInvariantCertificates

/-! Literal membership masks and the actual derived subgroup of 8T28.
Selected by export_lean_carrier_profiles_selected.py. Stored carrier profiles
are not proof inputs; every mask is bound to the same original elements. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
open scoped commutatorElement
namespace SymmetricSubgroupAsymptotics.RDTBinaryNormal8T28
local instance derivedMasksSourceGroup : Group Source := BinaryMenuCayley8T28.group

def derivedIndex : Fin 13 := 3

def sourceIndexEquiv : Fin 64 ≃ Source where
  toFun i := ⟨i⟩
  invFun x := x.index
  left_inv _ := rfl
  right_inv _ := rfl

/-- Membership in the same accepted 13 literal normal subgroups. -/
def normalMask (i : Fin 13) (x : Fin 64) : Bool :=
  ((if i.val < 6 then (if i.val < 3 then (if i.val < 1 then #[false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,true] else (if i.val < 2 then #[false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,true,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,true] else #[false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,true,false,false,false,true,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,true,false,false,false,true])) else (if i.val < 4 then #[false,false,false,false,false,false,false,false,true,false,false,false,true,false,false,false,false,false,false,false,false,false,false,false,false,false,true,false,false,false,true,false,false,false,false,false,false,false,false,false,false,true,false,false,false,true,false,false,false,false,false,false,false,false,false,false,false,false,false,true,false,false,false,true] else (if i.val < 5 then #[false,false,false,false,false,false,false,false,false,true,false,false,false,true,false,false,false,false,false,false,false,false,false,false,false,false,true,false,false,false,true,false,false,false,false,false,false,false,false,false,true,false,false,false,true,false,false,false,false,false,false,false,false,false,false,false,false,false,false,true,false,false,false,true] else #[false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,true,true,false,false,true,true,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,true,true,false,false,true,true]))) else (if i.val < 9 then (if i.val < 7 then #[false,false,false,false,false,false,false,false,true,true,false,false,true,true,false,false,false,false,false,false,false,false,false,false,false,false,true,true,false,false,true,true,false,false,false,false,false,false,false,false,true,true,false,false,true,true,false,false,false,false,false,false,false,false,false,false,false,false,true,true,false,false,true,true] else (if i.val < 8 then #[false,false,false,false,false,false,false,false,true,false,true,false,true,false,true,false,false,false,false,false,false,false,false,false,true,false,true,false,true,false,true,false,false,false,false,false,false,false,false,false,false,true,false,true,false,true,false,true,false,false,false,false,false,false,false,false,false,true,false,true,false,true,false,true] else #[false,false,false,false,false,false,false,false,true,false,false,true,true,false,false,true,false,false,false,false,false,false,false,false,false,true,true,false,false,true,true,false,false,false,false,false,false,false,false,false,false,true,true,false,false,true,true,false,false,false,false,false,false,false,false,false,true,false,false,true,true,false,false,true])) else (if i.val < 11 then (if i.val < 10 then #[true,true,false,false,true,true,false,false,true,true,false,false,true,true,false,false,false,false,true,true,false,false,true,true,false,false,true,true,false,false,true,true,true,true,false,false,true,true,false,false,true,true,false,false,true,true,false,false,false,false,true,true,false,false,true,true,false,false,true,true,false,false,true,true] else #[false,false,true,true,false,false,true,true,true,true,false,false,true,true,false,false,true,true,false,false,true,true,false,false,false,false,true,true,false,false,true,true,false,false,true,true,false,false,true,true,true,true,false,false,true,true,false,false,true,true,false,false,true,true,false,false,false,false,true,true,false,false,true,true]) else (if i.val < 12 then #[false,false,false,false,false,false,false,false,true,true,true,true,true,true,true,true,false,false,false,false,false,false,false,false,true,true,true,true,true,true,true,true,false,false,false,false,false,false,false,false,true,true,true,true,true,true,true,true,false,false,false,false,false,false,false,false,true,true,true,true,true,true,true,true] else #[true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true])))) : Array Bool)[x.val]!

private theorem normalMask_checked0 : ∀ x : Fin 64,
    normalMask 0 x = true ↔ ∃ j : Fin 1,
      N0.normalCertificate.rows j = x :=
  (Fin.addCases (m := 32) (n := 32) (Fin.addCases (m := 16) (n := 16) (by decide +kernel) (by decide +kernel)) (Fin.addCases (m := 16) (n := 16) (by decide +kernel) (by decide +kernel)))

private theorem normalMask_checked1 : ∀ x : Fin 64,
    normalMask 1 x = true ↔ ∃ j : Fin 2,
      N1.normalCertificate.rows j = x :=
  (Fin.addCases (m := 32) (n := 32) (Fin.addCases (m := 16) (n := 16) (by decide +kernel) (by decide +kernel)) (Fin.addCases (m := 16) (n := 16) (by decide +kernel) (by decide +kernel)))

private theorem normalMask_checked2 : ∀ x : Fin 64,
    normalMask 2 x = true ↔ ∃ j : Fin 4,
      N2.normalCertificate.rows j = x :=
  (Fin.addCases (m := 32) (n := 32) (Fin.addCases (m := 16) (n := 16) (by decide +kernel) (by decide +kernel)) (Fin.addCases (m := 16) (n := 16) (by decide +kernel) (by decide +kernel)))

private theorem normalMask_checked3 : ∀ x : Fin 64,
    normalMask 3 x = true ↔ ∃ j : Fin 8,
      N3.normalCertificate.rows j = x :=
  (Fin.addCases (m := 32) (n := 32) (Fin.addCases (m := 16) (n := 16) (by decide +kernel) (by decide +kernel)) (Fin.addCases (m := 16) (n := 16) (by decide +kernel) (by decide +kernel)))

private theorem normalMask_checked4 : ∀ x : Fin 64,
    normalMask 4 x = true ↔ ∃ j : Fin 8,
      N4.normalCertificate.rows j = x :=
  (Fin.addCases (m := 32) (n := 32) (Fin.addCases (m := 16) (n := 16) (by decide +kernel) (by decide +kernel)) (Fin.addCases (m := 16) (n := 16) (by decide +kernel) (by decide +kernel)))

private theorem normalMask_checked5 : ∀ x : Fin 64,
    normalMask 5 x = true ↔ ∃ j : Fin 8,
      N5.normalCertificate.rows j = x :=
  (Fin.addCases (m := 32) (n := 32) (Fin.addCases (m := 16) (n := 16) (by decide +kernel) (by decide +kernel)) (Fin.addCases (m := 16) (n := 16) (by decide +kernel) (by decide +kernel)))

private theorem normalMask_checked6 : ∀ x : Fin 64,
    normalMask 6 x = true ↔ ∃ j : Fin 16,
      N6.normalCertificate.rows j = x :=
  (Fin.addCases (m := 32) (n := 32) (Fin.addCases (m := 16) (n := 16) (by decide +kernel) (by decide +kernel)) (Fin.addCases (m := 16) (n := 16) (by decide +kernel) (by decide +kernel)))

private theorem normalMask_checked7 : ∀ x : Fin 64,
    normalMask 7 x = true ↔ ∃ j : Fin 16,
      N7.normalCertificate.rows j = x :=
  (Fin.addCases (m := 32) (n := 32) (Fin.addCases (m := 16) (n := 16) (by decide +kernel) (by decide +kernel)) (Fin.addCases (m := 16) (n := 16) (by decide +kernel) (by decide +kernel)))

private theorem normalMask_checked8 : ∀ x : Fin 64,
    normalMask 8 x = true ↔ ∃ j : Fin 16,
      N8.normalCertificate.rows j = x :=
  (Fin.addCases (m := 32) (n := 32) (Fin.addCases (m := 16) (n := 16) (by decide +kernel) (by decide +kernel)) (Fin.addCases (m := 16) (n := 16) (by decide +kernel) (by decide +kernel)))

private theorem normalMask_checked9 : ∀ x : Fin 64,
    normalMask 9 x = true ↔ ∃ j : Fin 32,
      N9.normalCertificate.rows j = x :=
  (Fin.addCases (m := 32) (n := 32) (Fin.addCases (m := 16) (n := 16) (by decide +kernel) (by decide +kernel)) (Fin.addCases (m := 16) (n := 16) (by decide +kernel) (by decide +kernel)))

private theorem normalMask_checked10 : ∀ x : Fin 64,
    normalMask 10 x = true ↔ ∃ j : Fin 32,
      N10.normalCertificate.rows j = x :=
  (Fin.addCases (m := 32) (n := 32) (Fin.addCases (m := 16) (n := 16) (by decide +kernel) (by decide +kernel)) (Fin.addCases (m := 16) (n := 16) (by decide +kernel) (by decide +kernel)))

private theorem normalMask_checked11 : ∀ x : Fin 64,
    normalMask 11 x = true ↔ ∃ j : Fin 32,
      N11.normalCertificate.rows j = x :=
  (Fin.addCases (m := 32) (n := 32) (Fin.addCases (m := 16) (n := 16) (by decide +kernel) (by decide +kernel)) (Fin.addCases (m := 16) (n := 16) (by decide +kernel) (by decide +kernel)))

private theorem normalMask_checked12 : ∀ x : Fin 64,
    normalMask 12 x = true ↔ ∃ j : Fin 64,
      N12.normalCertificate.rows j = x :=
  (Fin.addCases (m := 32) (n := 32) (Fin.addCases (m := 16) (n := 16) (by decide +kernel) (by decide +kernel)) (Fin.addCases (m := 16) (n := 16) (by decide +kernel) (by decide +kernel)))

theorem normalMask_mem (i : Fin 13) (x : Source) :
    normalMask i x.index = true ↔ x ∈ (states i).kernel := by
  fin_cases i
  · exact (normalMask_checked0 x.index).trans
      (N0.normalCertificate.mem_closure_iff x).symm
  · exact (normalMask_checked1 x.index).trans
      (N1.normalCertificate.mem_closure_iff x).symm
  · exact (normalMask_checked2 x.index).trans
      (N2.normalCertificate.mem_closure_iff x).symm
  · exact (normalMask_checked3 x.index).trans
      (N3.normalCertificate.mem_closure_iff x).symm
  · exact (normalMask_checked4 x.index).trans
      (N4.normalCertificate.mem_closure_iff x).symm
  · exact (normalMask_checked5 x.index).trans
      (N5.normalCertificate.mem_closure_iff x).symm
  · exact (normalMask_checked6 x.index).trans
      (N6.normalCertificate.mem_closure_iff x).symm
  · exact (normalMask_checked7 x.index).trans
      (N7.normalCertificate.mem_closure_iff x).symm
  · exact (normalMask_checked8 x.index).trans
      (N8.normalCertificate.mem_closure_iff x).symm
  · exact (normalMask_checked9 x.index).trans
      (N9.normalCertificate.mem_closure_iff x).symm
  · exact (normalMask_checked10 x.index).trans
      (N10.normalCertificate.mem_closure_iff x).symm
  · exact (normalMask_checked11 x.index).trans
      (N11.normalCertificate.mem_closure_iff x).symm
  · exact (normalMask_checked12 x.index).trans
      (N12.normalCertificate.mem_closure_iff x).symm

private def derivedWord0 : DerivedGeneratorWord (Fin 3) := .one
private def derivedWord1 : DerivedGeneratorWord (Fin 3) := .comm 0 1
private def derivedWord2 : DerivedGeneratorWord (Fin 3) := .comm 0 2
private def derivedWord3 : DerivedGeneratorWord (Fin 3) := .comm 1 2
private def derivedWord4 : DerivedGeneratorWord (Fin 3) := .mul derivedWord1 derivedWord2
private def derivedWord5 : DerivedGeneratorWord (Fin 3) := .mul derivedWord1 derivedWord3
private def derivedWord6 : DerivedGeneratorWord (Fin 3) := .mul derivedWord2 derivedWord3
private def derivedWord7 : DerivedGeneratorWord (Fin 3) := .conj 0 derivedWord3

private def derivedWords (j : Fin 3) : DerivedGeneratorWord (Fin 3) :=
  (if j.val < 1 then derivedWord4 else (if j.val < 2 then derivedWord2 else derivedWord7))

private theorem derivedWords_checked : ∀ j : Fin 3,
    (derivedWords j).eval generators = N3.normalGenerators j := by
  intro j
  fin_cases j <;> decide +kernel

private def generatorCommutatorRow (i j : Fin 3) : Fin 8 :=
  ((if i.val < 1 then #[7,6,3] else (if i.val < 2 then #[6,7,5] else #[3,5,7])) : Array (Fin 8))[j.val]!

private theorem generatorCommutators_checked : ∀ i j : Fin 3,
    ⁅generators i, generators j⁆ =
      (⟨N3.normalCertificate.rows (generatorCommutatorRow i j)⟩ : Source) := by
  decide +kernel

/-- N3 is identified with the actual derived subgroup in both directions. -/
theorem source_derived_eq : commutator Source = N3.kernel := by
  apply le_antisymm
  · apply commutator_le_of_generator_commutators N3.kernel generators generators_full
    intro i j
    rw [generatorCommutators_checked]
    exact binaryNormalRow_mem N3.normalCertificate _
  · change Subgroup.closure (Set.range N3.normalGenerators) ≤ commutator Source
    apply (Subgroup.closure_le _).mpr
    rintro _ ⟨j, rfl⟩
    rw [← derivedWords_checked j]
    exact (derivedWords j).eval_mem_commutator generators

theorem source_derived_state_eq : commutator Source = (states derivedIndex).kernel :=
  source_derived_eq

theorem source_derived_card : Nat.card (commutator Source) = 8 := by
  rw [source_derived_eq]
  exact N3.kernel_card

end SymmetricSubgroupAsymptotics.RDTBinaryNormal8T28
