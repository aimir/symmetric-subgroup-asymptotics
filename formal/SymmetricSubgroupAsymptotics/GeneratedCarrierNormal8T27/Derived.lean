import SymmetricSubgroupAsymptotics.GeneratedCarrierNormal8T27.States
import SymmetricSubgroupAsymptotics.DerivedGeneratorWords
import SymmetricSubgroupAsymptotics.FiniteQuotientInvariantCertificates

/-! Literal membership masks and the actual derived subgroup of J.
Selected by export_lean_carrier_j_quotients.py. Stored carrier profiles
are not proof inputs; every mask is bound to the same original elements. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
open scoped commutatorElement
namespace SymmetricSubgroupAsymptotics.BinaryCarrierNormal8T27
local instance derivedMasksSourceGroup : Group Source := BinaryMenuCayley8T27.group

def sourceIndexEquiv : Fin 64 ≃ Source where
  toFun i := ⟨i⟩
  invFun x := x.index
  left_inv _ := rfl
  right_inv _ := rfl

/-- Membership in the same accepted 13 literal normal subgroups. -/
def normalMask (i : Fin 13) (x : Fin 64) : Bool :=
  ((if i.val < 6 then (if i.val < 3 then (if i.val < 1 then #[false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,true] else (if i.val < 2 then #[false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,true,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,true] else #[false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,true,false,false,false,false,true,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,true,false,false,false,false,true])) else (if i.val < 4 then #[false,false,false,false,false,false,false,false,false,false,false,true,false,false,true,false,false,false,false,false,false,false,false,false,true,false,false,false,false,true,false,false,false,false,false,false,false,false,false,false,false,true,false,false,true,false,false,false,false,false,false,false,false,false,false,false,false,false,true,false,false,false,false,true] else (if i.val < 5 then #[false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,true,false,false,true,false,true,true,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,true,true,false,true,false,false,true] else #[false,false,false,false,false,false,false,false,false,true,true,false,true,false,false,true,false,false,false,false,false,false,false,false,true,false,false,true,false,true,true,false,false,false,false,false,false,false,false,false,true,false,false,true,false,true,true,false,false,false,false,false,false,false,false,false,false,true,true,false,true,false,false,true]))) else (if i.val < 9 then (if i.val < 7 then #[false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,true,true,true,true,true,true,true,true,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,true,true,true,true,true,true,true,true] else (if i.val < 8 then #[false,false,false,false,false,false,false,false,true,false,false,false,false,true,false,false,false,false,false,false,false,false,false,false,true,false,false,false,false,true,false,false,false,false,false,false,false,false,false,false,false,false,true,false,false,false,false,true,false,false,false,false,false,false,false,false,false,false,true,false,false,false,false,true] else #[false,false,false,false,false,false,false,false,true,false,false,true,false,true,true,false,false,false,false,false,false,false,false,false,true,false,false,true,false,true,true,false,false,false,false,false,false,false,false,false,false,true,true,false,true,false,false,true,false,false,false,false,false,false,false,false,false,true,true,false,true,false,false,true])) else (if i.val < 11 then (if i.val < 10 then #[false,true,true,false,true,false,false,true,true,false,false,true,false,true,true,false,false,true,true,false,true,false,false,true,true,false,false,true,false,true,true,false,true,false,false,true,false,true,true,false,false,true,true,false,true,false,false,true,true,false,false,true,false,true,true,false,false,true,true,false,true,false,false,true] else #[false,false,false,false,false,false,false,false,true,true,true,true,true,true,true,true,false,false,false,false,false,false,false,false,true,true,true,true,true,true,true,true,false,false,false,false,false,false,false,false,true,true,true,true,true,true,true,true,false,false,false,false,false,false,false,false,true,true,true,true,true,true,true,true]) else (if i.val < 12 then #[true,false,false,true,false,true,true,false,true,false,false,true,false,true,true,false,true,false,false,true,false,true,true,false,true,false,false,true,false,true,true,false,false,true,true,false,true,false,false,true,false,true,true,false,true,false,false,true,false,true,true,false,true,false,false,true,false,true,true,false,true,false,false,true] else #[true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true])))) : Array Bool)[x.val]!

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
    normalMask 5 x = true ↔ ∃ j : Fin 16,
      N5.normalCertificate.rows j = x :=
  (Fin.addCases (m := 32) (n := 32) (Fin.addCases (m := 16) (n := 16) (by decide +kernel) (by decide +kernel)) (Fin.addCases (m := 16) (n := 16) (by decide +kernel) (by decide +kernel)))

private theorem normalMask_checked6 : ∀ x : Fin 64,
    normalMask 6 x = true ↔ ∃ j : Fin 16,
      N6.normalCertificate.rows j = x :=
  (Fin.addCases (m := 32) (n := 32) (Fin.addCases (m := 16) (n := 16) (by decide +kernel) (by decide +kernel)) (Fin.addCases (m := 16) (n := 16) (by decide +kernel) (by decide +kernel)))

private theorem normalMask_checked7 : ∀ x : Fin 64,
    normalMask 7 x = true ↔ ∃ j : Fin 8,
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

private def derivedWord0 : DerivedGeneratorWord (Fin 2) := .one
private def derivedWord1 : DerivedGeneratorWord (Fin 2) := .comm 0 1
private def derivedWord2 : DerivedGeneratorWord (Fin 2) := .conj 1 derivedWord1
private def derivedWord3 : DerivedGeneratorWord (Fin 2) := .conjInv 1 derivedWord1
private def derivedWord4 : DerivedGeneratorWord (Fin 2) := .mul derivedWord2 derivedWord1
private def derivedWord5 : DerivedGeneratorWord (Fin 2) := .conj 1 derivedWord2
private def derivedWord6 : DerivedGeneratorWord (Fin 2) := .mul derivedWord3 derivedWord1
private def derivedWord7 : DerivedGeneratorWord (Fin 2) := .mul derivedWord5 derivedWord1

private def derivedWords (j : Fin 3) : DerivedGeneratorWord (Fin 2) :=
  (if j.val < 1 then derivedWord3 else (if j.val < 2 then derivedWord4 else derivedWord6))

private theorem derivedWords_checked : ∀ j : Fin 3,
    (derivedWords j).eval generators = N4.normalGenerators j := by
  intro j
  fin_cases j <;> decide +kernel

private def generatorCommutatorRow (i j : Fin 2) : Fin 8 :=
  ((if i.val < 1 then #[7,3] else #[3,7]) : Array (Fin 8))[j.val]!

private theorem generatorCommutators_checked : ∀ i j : Fin 2,
    ⁅generators i, generators j⁆ =
      (⟨N4.normalCertificate.rows (generatorCommutatorRow i j)⟩ : Source) := by
  decide +kernel

/-- N4 is identified with the actual derived subgroup in both directions. -/
theorem source_derived_eq : commutator Source = N4.kernel := by
  apply le_antisymm
  · apply commutator_le_of_generator_commutators N4.kernel generators generators_full
    intro i j
    rw [generatorCommutators_checked]
    exact binaryNormalRow_mem N4.normalCertificate _
  · change Subgroup.closure (Set.range N4.normalGenerators) ≤ commutator Source
    apply (Subgroup.closure_le _).mpr
    rintro _ ⟨j, rfl⟩
    rw [← derivedWords_checked j]
    exact (derivedWords j).eval_mem_commutator generators

theorem source_derived_card : Nat.card (commutator Source) = 8 := by
  rw [source_derived_eq]
  exact N4.kernel_card

end SymmetricSubgroupAsymptotics.BinaryCarrierNormal8T27
