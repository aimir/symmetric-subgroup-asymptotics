import SymmetricSubgroupAsymptotics.GeneratedCarrierNormal8T35.States
import SymmetricSubgroupAsymptotics.DerivedGeneratorWords
import SymmetricSubgroupAsymptotics.FiniteQuotientInvariantCertificates

/-! Literal membership masks and the actual derived subgroup of 8T35.
Selected by export_lean_carrier_profiles_selected.py. Stored carrier profiles
are not proof inputs; every mask is bound to the same original elements. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
open scoped commutatorElement
namespace SymmetricSubgroupAsymptotics.BinaryCarrierNormal8T35
local instance derivedMasksSourceGroup : Group Source := BinaryMenuCayley8T35.group

def derivedIndex : Fin 28 := 12

def sourceIndexEquiv : Fin 128 ≃ Source where
  toFun i := ⟨i⟩
  invFun x := x.index
  left_inv _ := rfl
  right_inv _ := rfl

/-- Membership in the same accepted 28 literal normal subgroups. -/
def normalMask (i : Fin 28) (x : Fin 128) : Bool :=
  ((if i.val < 14 then (if i.val < 7 then (if i.val < 3 then (if i.val < 1 then #[false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,true] else (if i.val < 2 then #[false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,true,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,true] else #[false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,true,false,false,false,false,false,false,false,false,true,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,true,false,false,false,false,false,false,false,false,true])) else (if i.val < 5 then (if i.val < 4 then #[false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,true,false,false,false,false,false,false,true,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,true,false,false,false,false,false,false,false,false,true,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,true,false,false,false,false,false,false,true,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,true,false,false,false,false,false,false,false,false,true] else #[false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,true,false,false,true,false,false,false,false,false,true,true,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,true,true,false,false,false,false,false,true,false,false,true]) else (if i.val < 6 then #[false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,true,false,true,false,false,false,false,true,false,true,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,true,false,true,false,false,false,false,false,false,true,false,true,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,true,false,false,false,false,false,true,true,false,false,false,false,false,true,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,true,false,false,false,false,false,true,false,false,true,false,false,false,false,false,true] else #[false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,true,false,false,true,false,false,false,true,false,false,false,false,true,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,true,false,false,true,false,false,false,true,false,false,false,false,true,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,true,false,false,true,false,false,false,true,false,false,false,false,true,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,true,false,false,true,false,false,false,true,false,false,false,false,true]))) else (if i.val < 10 then (if i.val < 8 then #[false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,true,true,false,false,false,false,false,true,false,false,true,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,true,false,false,true,false,false,false,false,false,true,true,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,true,false,false,true,false,false,false,false,false,true,true,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,true,true,false,false,false,false,false,true,false,false,true] else (if i.val < 9 then #[false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,true,true,true,true,false,false,false,false,true,true,true,true,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,true,true,true,true,false,false,false,false,true,true,true,true] else #[false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,true,false,false,false,false,false,false,false,false,true,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,true,false,false,false,false,false,false,false,false,true,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,true,false,false,false,false,false,false,false,false,true,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,true,false,false,false,false,false,false,false,false,true])) else (if i.val < 12 then (if i.val < 11 then #[false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,true,false,false,false,false,false,false,true,false,true,false,false,false,false,true,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,true,true,false,false,false,false,false,true,false,false,true,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,true,false,false,true,false,false,false,false,false,true,true,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,true,false,false,false,false,true,false,true,false,false,false,false,false,false,true] else #[false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,true,false,false,false,true,false,false,false,false,true,false,false,false,true,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,true,false,false,false,true,false,false,false,false,true,false,false,false,true,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,true,false,false,false,true,false,false,false,false,true,false,false,false,true,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,true,false,false,false,true,false,false,false,false,true,false,false,false,true]) else (if i.val < 13 then #[false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,true,false,false,true,false,false,false,false,false,true,true,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,true,false,false,true,false,false,false,false,false,true,true,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,true,true,false,false,false,false,false,true,false,false,true,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,true,true,false,false,false,false,false,true,false,false,true] else #[false,true,true,false,false,false,false,false,true,false,false,true,false,false,false,false,true,false,false,true,false,false,false,false,false,true,true,false,false,false,false,false,false,false,false,false,false,true,true,false,false,false,false,false,true,false,false,true,false,false,false,false,true,false,false,true,false,false,false,false,false,true,true,false,true,false,false,true,false,false,false,false,false,true,true,false,false,false,false,false,false,true,true,false,false,false,false,false,true,false,false,true,false,false,false,false,false,false,false,false,true,false,false,true,false,false,false,false,false,true,true,false,false,false,false,false,false,true,true,false,false,false,false,false,true,false,false,true])))) else (if i.val < 21 then (if i.val < 17 then (if i.val < 15 then #[false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,true,false,false,true,false,true,true,false,false,true,true,false,true,false,false,true,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,true,true,false,true,false,false,true,true,false,false,true,false,true,true,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,true,true,false,true,false,false,true,true,false,false,true,false,true,true,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,true,false,false,true,false,true,true,false,false,true,true,false,true,false,false,true] else (if i.val < 16 then #[true,false,false,true,false,false,false,false,false,true,true,false,false,false,false,false,true,false,false,true,false,false,false,false,false,true,true,false,false,false,false,false,false,false,false,false,true,false,false,true,false,false,false,false,false,true,true,false,false,false,false,false,true,false,false,true,false,false,false,false,false,true,true,false,false,true,true,false,false,false,false,false,true,false,false,true,false,false,false,false,false,true,true,false,false,false,false,false,true,false,false,true,false,false,false,false,false,false,false,false,false,true,true,false,false,false,false,false,true,false,false,true,false,false,false,false,false,true,true,false,false,false,false,false,true,false,false,true] else #[false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,true,false,false,true,true,false,false,true,false,true,true,false,false,true,true,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,true,false,false,true,true,false,false,true,false,true,true,false,false,true,true,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,true,true,false,false,true,true,false,true,false,false,true,true,false,false,true,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,true,true,false,false,true,true,false,true,false,false,true,true,false,false,true])) else (if i.val < 19 then (if i.val < 18 then #[false,false,false,false,false,true,true,false,false,false,false,false,true,false,false,true,true,false,false,true,false,false,false,false,false,true,true,false,false,false,false,false,false,true,true,false,false,false,false,false,true,false,false,true,false,false,false,false,false,false,false,false,true,false,false,true,false,false,false,false,false,true,true,false,false,false,false,false,true,false,false,true,false,false,false,false,false,true,true,false,false,true,true,false,false,false,false,false,true,false,false,true,false,false,false,false,true,false,false,true,false,false,false,false,false,true,true,false,false,false,false,false,false,false,false,false,false,true,true,false,false,false,false,false,true,false,false,true] else #[false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,true,true,true,true,false,false,false,false,true,true,true,true,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,true,true,true,true,false,false,false,false,true,true,true,true,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,true,true,true,true,false,false,false,false,true,true,true,true,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,true,true,true,true,false,false,false,false,true,true,true,true]) else (if i.val < 20 then #[true,false,false,true,false,true,true,false,false,true,true,false,true,false,false,true,true,false,false,true,false,true,true,false,false,true,true,false,true,false,false,true,false,true,true,false,true,false,false,true,true,false,false,true,false,true,true,false,false,true,true,false,true,false,false,true,true,false,false,true,false,true,true,false,false,true,true,false,true,false,false,true,true,false,false,true,false,true,true,false,false,true,true,false,true,false,false,true,true,false,false,true,false,true,true,false,true,false,false,true,false,true,true,false,false,true,true,false,true,false,false,true,true,false,false,true,false,true,true,false,false,true,true,false,true,false,false,true] else #[true,true,true,true,false,false,false,false,true,true,true,true,false,false,false,false,true,true,true,true,false,false,false,false,true,true,true,true,false,false,false,false,false,false,false,false,true,true,true,true,false,false,false,false,true,true,true,true,false,false,false,false,true,true,true,true,false,false,false,false,true,true,true,true,true,true,true,true,false,false,false,false,true,true,true,true,false,false,false,false,true,true,true,true,false,false,false,false,true,true,true,true,false,false,false,false,false,false,false,false,true,true,true,true,false,false,false,false,true,true,true,true,false,false,false,false,true,true,true,true,false,false,false,false,true,true,true,true]))) else (if i.val < 24 then (if i.val < 22 then #[false,true,true,false,false,true,true,false,true,false,false,true,true,false,false,true,true,false,false,true,true,false,false,true,false,true,true,false,false,true,true,false,false,true,true,false,false,true,true,false,true,false,false,true,true,false,false,true,true,false,false,true,true,false,false,true,false,true,true,false,false,true,true,false,true,false,false,true,true,false,false,true,false,true,true,false,false,true,true,false,false,true,true,false,false,true,true,false,true,false,false,true,true,false,false,true,true,false,false,true,true,false,false,true,false,true,true,false,false,true,true,false,false,true,true,false,false,true,true,false,true,false,false,true,true,false,false,true] else (if i.val < 23 then #[false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true] else #[false,false,false,false,true,false,false,true,false,false,false,false,false,true,true,false,true,false,false,true,false,false,false,false,false,true,true,false,false,false,false,false,true,false,false,true,false,false,false,false,false,true,true,false,false,false,false,false,false,false,false,false,true,false,false,true,false,false,false,false,false,true,true,false,false,false,false,false,false,true,true,false,false,false,false,false,true,false,false,true,false,true,true,false,false,false,false,false,true,false,false,true,false,false,false,false,false,true,true,false,false,false,false,false,true,false,false,true,false,false,false,false,false,false,false,false,false,true,true,false,false,false,false,false,true,false,false,true])) else (if i.val < 26 then (if i.val < 25 then #[false,true,true,false,true,false,false,true,true,false,false,true,false,true,true,false,true,false,false,true,false,true,true,false,false,true,true,false,true,false,false,true,true,false,false,true,false,true,true,false,false,true,true,false,true,false,false,true,false,true,true,false,true,false,false,true,true,false,false,true,false,true,true,false,true,false,false,true,false,true,true,false,false,true,true,false,true,false,false,true,false,true,true,false,true,false,false,true,true,false,false,true,false,true,true,false,false,true,true,false,true,false,false,true,true,false,false,true,false,true,true,false,true,false,false,true,false,true,true,false,false,true,true,false,true,false,false,true] else #[true,false,false,true,true,false,false,true,false,true,true,false,false,true,true,false,true,false,false,true,true,false,false,true,false,true,true,false,false,true,true,false,true,false,false,true,true,false,false,true,false,true,true,false,false,true,true,false,true,false,false,true,true,false,false,true,false,true,true,false,false,true,true,false,false,true,true,false,false,true,true,false,true,false,false,true,true,false,false,true,false,true,true,false,false,true,true,false,true,false,false,true,true,false,false,true,false,true,true,false,false,true,true,false,true,false,false,true,true,false,false,true,false,true,true,false,false,true,true,false,true,false,false,true,true,false,false,true]) else (if i.val < 27 then #[false,false,false,false,true,true,true,true,false,false,false,false,true,true,true,true,true,true,true,true,false,false,false,false,true,true,true,true,false,false,false,false,true,true,true,true,false,false,false,false,true,true,true,true,false,false,false,false,false,false,false,false,true,true,true,true,false,false,false,false,true,true,true,true,false,false,false,false,true,true,true,true,false,false,false,false,true,true,true,true,true,true,true,true,false,false,false,false,true,true,true,true,false,false,false,false,true,true,true,true,false,false,false,false,true,true,true,true,false,false,false,false,false,false,false,false,true,true,true,true,false,false,false,false,true,true,true,true] else #[true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true]))))) : Array Bool)[x.val]!

private theorem normalMask_checked0 : ∀ x : Fin 128,
    normalMask 0 x = true ↔ ∃ j : Fin 1,
      N0.normalCertificate.rows j = x :=
  (Fin.addCases (m := 64) (n := 64) (Fin.addCases (m := 32) (n := 32) (Fin.addCases (m := 16) (n := 16) (by decide +kernel) (by decide +kernel)) (Fin.addCases (m := 16) (n := 16) (by decide +kernel) (by decide +kernel))) (Fin.addCases (m := 32) (n := 32) (Fin.addCases (m := 16) (n := 16) (by decide +kernel) (by decide +kernel)) (Fin.addCases (m := 16) (n := 16) (by decide +kernel) (by decide +kernel))))

private theorem normalMask_checked1 : ∀ x : Fin 128,
    normalMask 1 x = true ↔ ∃ j : Fin 2,
      N1.normalCertificate.rows j = x :=
  (Fin.addCases (m := 64) (n := 64) (Fin.addCases (m := 32) (n := 32) (Fin.addCases (m := 16) (n := 16) (by decide +kernel) (by decide +kernel)) (Fin.addCases (m := 16) (n := 16) (by decide +kernel) (by decide +kernel))) (Fin.addCases (m := 32) (n := 32) (Fin.addCases (m := 16) (n := 16) (by decide +kernel) (by decide +kernel)) (Fin.addCases (m := 16) (n := 16) (by decide +kernel) (by decide +kernel))))

private theorem normalMask_checked2 : ∀ x : Fin 128,
    normalMask 2 x = true ↔ ∃ j : Fin 4,
      N2.normalCertificate.rows j = x :=
  (Fin.addCases (m := 64) (n := 64) (Fin.addCases (m := 32) (n := 32) (Fin.addCases (m := 16) (n := 16) (by decide +kernel) (by decide +kernel)) (Fin.addCases (m := 16) (n := 16) (by decide +kernel) (by decide +kernel))) (Fin.addCases (m := 32) (n := 32) (Fin.addCases (m := 16) (n := 16) (by decide +kernel) (by decide +kernel)) (Fin.addCases (m := 16) (n := 16) (by decide +kernel) (by decide +kernel))))

private theorem normalMask_checked3 : ∀ x : Fin 128,
    normalMask 3 x = true ↔ ∃ j : Fin 8,
      N3.normalCertificate.rows j = x :=
  (Fin.addCases (m := 64) (n := 64) (Fin.addCases (m := 32) (n := 32) (Fin.addCases (m := 16) (n := 16) (by decide +kernel) (by decide +kernel)) (Fin.addCases (m := 16) (n := 16) (by decide +kernel) (by decide +kernel))) (Fin.addCases (m := 32) (n := 32) (Fin.addCases (m := 16) (n := 16) (by decide +kernel) (by decide +kernel)) (Fin.addCases (m := 16) (n := 16) (by decide +kernel) (by decide +kernel))))

private theorem normalMask_checked4 : ∀ x : Fin 128,
    normalMask 4 x = true ↔ ∃ j : Fin 8,
      N4.normalCertificate.rows j = x :=
  (Fin.addCases (m := 64) (n := 64) (Fin.addCases (m := 32) (n := 32) (Fin.addCases (m := 16) (n := 16) (by decide +kernel) (by decide +kernel)) (Fin.addCases (m := 16) (n := 16) (by decide +kernel) (by decide +kernel))) (Fin.addCases (m := 32) (n := 32) (Fin.addCases (m := 16) (n := 16) (by decide +kernel) (by decide +kernel)) (Fin.addCases (m := 16) (n := 16) (by decide +kernel) (by decide +kernel))))

private theorem normalMask_checked5 : ∀ x : Fin 128,
    normalMask 5 x = true ↔ ∃ j : Fin 16,
      N5.normalCertificate.rows j = x :=
  (Fin.addCases (m := 64) (n := 64) (Fin.addCases (m := 32) (n := 32) (Fin.addCases (m := 16) (n := 16) (by decide +kernel) (by decide +kernel)) (Fin.addCases (m := 16) (n := 16) (by decide +kernel) (by decide +kernel))) (Fin.addCases (m := 32) (n := 32) (Fin.addCases (m := 16) (n := 16) (by decide +kernel) (by decide +kernel)) (Fin.addCases (m := 16) (n := 16) (by decide +kernel) (by decide +kernel))))

private theorem normalMask_checked6 : ∀ x : Fin 128,
    normalMask 6 x = true ↔ ∃ j : Fin 16,
      N6.normalCertificate.rows j = x :=
  (Fin.addCases (m := 64) (n := 64) (Fin.addCases (m := 32) (n := 32) (Fin.addCases (m := 16) (n := 16) (by decide +kernel) (by decide +kernel)) (Fin.addCases (m := 16) (n := 16) (by decide +kernel) (by decide +kernel))) (Fin.addCases (m := 32) (n := 32) (Fin.addCases (m := 16) (n := 16) (by decide +kernel) (by decide +kernel)) (Fin.addCases (m := 16) (n := 16) (by decide +kernel) (by decide +kernel))))

private theorem normalMask_checked7 : ∀ x : Fin 128,
    normalMask 7 x = true ↔ ∃ j : Fin 16,
      N7.normalCertificate.rows j = x :=
  (Fin.addCases (m := 64) (n := 64) (Fin.addCases (m := 32) (n := 32) (Fin.addCases (m := 16) (n := 16) (by decide +kernel) (by decide +kernel)) (Fin.addCases (m := 16) (n := 16) (by decide +kernel) (by decide +kernel))) (Fin.addCases (m := 32) (n := 32) (Fin.addCases (m := 16) (n := 16) (by decide +kernel) (by decide +kernel)) (Fin.addCases (m := 16) (n := 16) (by decide +kernel) (by decide +kernel))))

private theorem normalMask_checked8 : ∀ x : Fin 128,
    normalMask 8 x = true ↔ ∃ j : Fin 16,
      N8.normalCertificate.rows j = x :=
  (Fin.addCases (m := 64) (n := 64) (Fin.addCases (m := 32) (n := 32) (Fin.addCases (m := 16) (n := 16) (by decide +kernel) (by decide +kernel)) (Fin.addCases (m := 16) (n := 16) (by decide +kernel) (by decide +kernel))) (Fin.addCases (m := 32) (n := 32) (Fin.addCases (m := 16) (n := 16) (by decide +kernel) (by decide +kernel)) (Fin.addCases (m := 16) (n := 16) (by decide +kernel) (by decide +kernel))))

private theorem normalMask_checked9 : ∀ x : Fin 128,
    normalMask 9 x = true ↔ ∃ j : Fin 8,
      N9.normalCertificate.rows j = x :=
  (Fin.addCases (m := 64) (n := 64) (Fin.addCases (m := 32) (n := 32) (Fin.addCases (m := 16) (n := 16) (by decide +kernel) (by decide +kernel)) (Fin.addCases (m := 16) (n := 16) (by decide +kernel) (by decide +kernel))) (Fin.addCases (m := 32) (n := 32) (Fin.addCases (m := 16) (n := 16) (by decide +kernel) (by decide +kernel)) (Fin.addCases (m := 16) (n := 16) (by decide +kernel) (by decide +kernel))))

private theorem normalMask_checked10 : ∀ x : Fin 128,
    normalMask 10 x = true ↔ ∃ j : Fin 16,
      N10.normalCertificate.rows j = x :=
  (Fin.addCases (m := 64) (n := 64) (Fin.addCases (m := 32) (n := 32) (Fin.addCases (m := 16) (n := 16) (by decide +kernel) (by decide +kernel)) (Fin.addCases (m := 16) (n := 16) (by decide +kernel) (by decide +kernel))) (Fin.addCases (m := 32) (n := 32) (Fin.addCases (m := 16) (n := 16) (by decide +kernel) (by decide +kernel)) (Fin.addCases (m := 16) (n := 16) (by decide +kernel) (by decide +kernel))))

private theorem normalMask_checked11 : ∀ x : Fin 128,
    normalMask 11 x = true ↔ ∃ j : Fin 16,
      N11.normalCertificate.rows j = x :=
  (Fin.addCases (m := 64) (n := 64) (Fin.addCases (m := 32) (n := 32) (Fin.addCases (m := 16) (n := 16) (by decide +kernel) (by decide +kernel)) (Fin.addCases (m := 16) (n := 16) (by decide +kernel) (by decide +kernel))) (Fin.addCases (m := 32) (n := 32) (Fin.addCases (m := 16) (n := 16) (by decide +kernel) (by decide +kernel)) (Fin.addCases (m := 16) (n := 16) (by decide +kernel) (by decide +kernel))))

private theorem normalMask_checked12 : ∀ x : Fin 128,
    normalMask 12 x = true ↔ ∃ j : Fin 16,
      N12.normalCertificate.rows j = x :=
  (Fin.addCases (m := 64) (n := 64) (Fin.addCases (m := 32) (n := 32) (Fin.addCases (m := 16) (n := 16) (by decide +kernel) (by decide +kernel)) (Fin.addCases (m := 16) (n := 16) (by decide +kernel) (by decide +kernel))) (Fin.addCases (m := 32) (n := 32) (Fin.addCases (m := 16) (n := 16) (by decide +kernel) (by decide +kernel)) (Fin.addCases (m := 16) (n := 16) (by decide +kernel) (by decide +kernel))))

private theorem normalMask_checked13 : ∀ x : Fin 128,
    normalMask 13 x = true ↔ ∃ j : Fin 32,
      N13.normalCertificate.rows j = x :=
  (Fin.addCases (m := 64) (n := 64) (Fin.addCases (m := 32) (n := 32) (Fin.addCases (m := 16) (n := 16) (by decide +kernel) (by decide +kernel)) (Fin.addCases (m := 16) (n := 16) (by decide +kernel) (by decide +kernel))) (Fin.addCases (m := 32) (n := 32) (Fin.addCases (m := 16) (n := 16) (by decide +kernel) (by decide +kernel)) (Fin.addCases (m := 16) (n := 16) (by decide +kernel) (by decide +kernel))))

private theorem normalMask_checked14 : ∀ x : Fin 128,
    normalMask 14 x = true ↔ ∃ j : Fin 32,
      N14.normalCertificate.rows j = x :=
  (Fin.addCases (m := 64) (n := 64) (Fin.addCases (m := 32) (n := 32) (Fin.addCases (m := 16) (n := 16) (by decide +kernel) (by decide +kernel)) (Fin.addCases (m := 16) (n := 16) (by decide +kernel) (by decide +kernel))) (Fin.addCases (m := 32) (n := 32) (Fin.addCases (m := 16) (n := 16) (by decide +kernel) (by decide +kernel)) (Fin.addCases (m := 16) (n := 16) (by decide +kernel) (by decide +kernel))))

private theorem normalMask_checked15 : ∀ x : Fin 128,
    normalMask 15 x = true ↔ ∃ j : Fin 32,
      N15.normalCertificate.rows j = x :=
  (Fin.addCases (m := 64) (n := 64) (Fin.addCases (m := 32) (n := 32) (Fin.addCases (m := 16) (n := 16) (by decide +kernel) (by decide +kernel)) (Fin.addCases (m := 16) (n := 16) (by decide +kernel) (by decide +kernel))) (Fin.addCases (m := 32) (n := 32) (Fin.addCases (m := 16) (n := 16) (by decide +kernel) (by decide +kernel)) (Fin.addCases (m := 16) (n := 16) (by decide +kernel) (by decide +kernel))))

private theorem normalMask_checked16 : ∀ x : Fin 128,
    normalMask 16 x = true ↔ ∃ j : Fin 32,
      N16.normalCertificate.rows j = x :=
  (Fin.addCases (m := 64) (n := 64) (Fin.addCases (m := 32) (n := 32) (Fin.addCases (m := 16) (n := 16) (by decide +kernel) (by decide +kernel)) (Fin.addCases (m := 16) (n := 16) (by decide +kernel) (by decide +kernel))) (Fin.addCases (m := 32) (n := 32) (Fin.addCases (m := 16) (n := 16) (by decide +kernel) (by decide +kernel)) (Fin.addCases (m := 16) (n := 16) (by decide +kernel) (by decide +kernel))))

private theorem normalMask_checked17 : ∀ x : Fin 128,
    normalMask 17 x = true ↔ ∃ j : Fin 32,
      N17.normalCertificate.rows j = x :=
  (Fin.addCases (m := 64) (n := 64) (Fin.addCases (m := 32) (n := 32) (Fin.addCases (m := 16) (n := 16) (by decide +kernel) (by decide +kernel)) (Fin.addCases (m := 16) (n := 16) (by decide +kernel) (by decide +kernel))) (Fin.addCases (m := 32) (n := 32) (Fin.addCases (m := 16) (n := 16) (by decide +kernel) (by decide +kernel)) (Fin.addCases (m := 16) (n := 16) (by decide +kernel) (by decide +kernel))))

private theorem normalMask_checked18 : ∀ x : Fin 128,
    normalMask 18 x = true ↔ ∃ j : Fin 32,
      N18.normalCertificate.rows j = x :=
  (Fin.addCases (m := 64) (n := 64) (Fin.addCases (m := 32) (n := 32) (Fin.addCases (m := 16) (n := 16) (by decide +kernel) (by decide +kernel)) (Fin.addCases (m := 16) (n := 16) (by decide +kernel) (by decide +kernel))) (Fin.addCases (m := 32) (n := 32) (Fin.addCases (m := 16) (n := 16) (by decide +kernel) (by decide +kernel)) (Fin.addCases (m := 16) (n := 16) (by decide +kernel) (by decide +kernel))))

private theorem normalMask_checked19 : ∀ x : Fin 128,
    normalMask 19 x = true ↔ ∃ j : Fin 64,
      N19.normalCertificate.rows j = x :=
  (Fin.addCases (m := 64) (n := 64) (Fin.addCases (m := 32) (n := 32) (Fin.addCases (m := 16) (n := 16) (by decide +kernel) (by decide +kernel)) (Fin.addCases (m := 16) (n := 16) (by decide +kernel) (by decide +kernel))) (Fin.addCases (m := 32) (n := 32) (Fin.addCases (m := 16) (n := 16) (by decide +kernel) (by decide +kernel)) (Fin.addCases (m := 16) (n := 16) (by decide +kernel) (by decide +kernel))))

private theorem normalMask_checked20 : ∀ x : Fin 128,
    normalMask 20 x = true ↔ ∃ j : Fin 64,
      N20.normalCertificate.rows j = x :=
  (Fin.addCases (m := 64) (n := 64) (Fin.addCases (m := 32) (n := 32) (Fin.addCases (m := 16) (n := 16) (by decide +kernel) (by decide +kernel)) (Fin.addCases (m := 16) (n := 16) (by decide +kernel) (by decide +kernel))) (Fin.addCases (m := 32) (n := 32) (Fin.addCases (m := 16) (n := 16) (by decide +kernel) (by decide +kernel)) (Fin.addCases (m := 16) (n := 16) (by decide +kernel) (by decide +kernel))))

private theorem normalMask_checked21 : ∀ x : Fin 128,
    normalMask 21 x = true ↔ ∃ j : Fin 64,
      N21.normalCertificate.rows j = x :=
  (Fin.addCases (m := 64) (n := 64) (Fin.addCases (m := 32) (n := 32) (Fin.addCases (m := 16) (n := 16) (by decide +kernel) (by decide +kernel)) (Fin.addCases (m := 16) (n := 16) (by decide +kernel) (by decide +kernel))) (Fin.addCases (m := 32) (n := 32) (Fin.addCases (m := 16) (n := 16) (by decide +kernel) (by decide +kernel)) (Fin.addCases (m := 16) (n := 16) (by decide +kernel) (by decide +kernel))))

private theorem normalMask_checked22 : ∀ x : Fin 128,
    normalMask 22 x = true ↔ ∃ j : Fin 64,
      N22.normalCertificate.rows j = x :=
  (Fin.addCases (m := 64) (n := 64) (Fin.addCases (m := 32) (n := 32) (Fin.addCases (m := 16) (n := 16) (by decide +kernel) (by decide +kernel)) (Fin.addCases (m := 16) (n := 16) (by decide +kernel) (by decide +kernel))) (Fin.addCases (m := 32) (n := 32) (Fin.addCases (m := 16) (n := 16) (by decide +kernel) (by decide +kernel)) (Fin.addCases (m := 16) (n := 16) (by decide +kernel) (by decide +kernel))))

private theorem normalMask_checked23 : ∀ x : Fin 128,
    normalMask 23 x = true ↔ ∃ j : Fin 32,
      N23.normalCertificate.rows j = x :=
  (Fin.addCases (m := 64) (n := 64) (Fin.addCases (m := 32) (n := 32) (Fin.addCases (m := 16) (n := 16) (by decide +kernel) (by decide +kernel)) (Fin.addCases (m := 16) (n := 16) (by decide +kernel) (by decide +kernel))) (Fin.addCases (m := 32) (n := 32) (Fin.addCases (m := 16) (n := 16) (by decide +kernel) (by decide +kernel)) (Fin.addCases (m := 16) (n := 16) (by decide +kernel) (by decide +kernel))))

private theorem normalMask_checked24 : ∀ x : Fin 128,
    normalMask 24 x = true ↔ ∃ j : Fin 64,
      N24.normalCertificate.rows j = x :=
  (Fin.addCases (m := 64) (n := 64) (Fin.addCases (m := 32) (n := 32) (Fin.addCases (m := 16) (n := 16) (by decide +kernel) (by decide +kernel)) (Fin.addCases (m := 16) (n := 16) (by decide +kernel) (by decide +kernel))) (Fin.addCases (m := 32) (n := 32) (Fin.addCases (m := 16) (n := 16) (by decide +kernel) (by decide +kernel)) (Fin.addCases (m := 16) (n := 16) (by decide +kernel) (by decide +kernel))))

private theorem normalMask_checked25 : ∀ x : Fin 128,
    normalMask 25 x = true ↔ ∃ j : Fin 64,
      N25.normalCertificate.rows j = x :=
  (Fin.addCases (m := 64) (n := 64) (Fin.addCases (m := 32) (n := 32) (Fin.addCases (m := 16) (n := 16) (by decide +kernel) (by decide +kernel)) (Fin.addCases (m := 16) (n := 16) (by decide +kernel) (by decide +kernel))) (Fin.addCases (m := 32) (n := 32) (Fin.addCases (m := 16) (n := 16) (by decide +kernel) (by decide +kernel)) (Fin.addCases (m := 16) (n := 16) (by decide +kernel) (by decide +kernel))))

private theorem normalMask_checked26 : ∀ x : Fin 128,
    normalMask 26 x = true ↔ ∃ j : Fin 64,
      N26.normalCertificate.rows j = x :=
  (Fin.addCases (m := 64) (n := 64) (Fin.addCases (m := 32) (n := 32) (Fin.addCases (m := 16) (n := 16) (by decide +kernel) (by decide +kernel)) (Fin.addCases (m := 16) (n := 16) (by decide +kernel) (by decide +kernel))) (Fin.addCases (m := 32) (n := 32) (Fin.addCases (m := 16) (n := 16) (by decide +kernel) (by decide +kernel)) (Fin.addCases (m := 16) (n := 16) (by decide +kernel) (by decide +kernel))))

private theorem normalMask_checked27 : ∀ x : Fin 128,
    normalMask 27 x = true ↔ ∃ j : Fin 128,
      N27.normalCertificate.rows j = x :=
  (Fin.addCases (m := 64) (n := 64) (Fin.addCases (m := 32) (n := 32) (Fin.addCases (m := 16) (n := 16) (by decide +kernel) (by decide +kernel)) (Fin.addCases (m := 16) (n := 16) (by decide +kernel) (by decide +kernel))) (Fin.addCases (m := 32) (n := 32) (Fin.addCases (m := 16) (n := 16) (by decide +kernel) (by decide +kernel)) (Fin.addCases (m := 16) (n := 16) (by decide +kernel) (by decide +kernel))))

theorem normalMask_mem (i : Fin 28) (x : Source) :
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
  · exact (normalMask_checked13 x.index).trans
      (N13.normalCertificate.mem_closure_iff x).symm
  · exact (normalMask_checked14 x.index).trans
      (N14.normalCertificate.mem_closure_iff x).symm
  · exact (normalMask_checked15 x.index).trans
      (N15.normalCertificate.mem_closure_iff x).symm
  · exact (normalMask_checked16 x.index).trans
      (N16.normalCertificate.mem_closure_iff x).symm
  · exact (normalMask_checked17 x.index).trans
      (N17.normalCertificate.mem_closure_iff x).symm
  · exact (normalMask_checked18 x.index).trans
      (N18.normalCertificate.mem_closure_iff x).symm
  · exact (normalMask_checked19 x.index).trans
      (N19.normalCertificate.mem_closure_iff x).symm
  · exact (normalMask_checked20 x.index).trans
      (N20.normalCertificate.mem_closure_iff x).symm
  · exact (normalMask_checked21 x.index).trans
      (N21.normalCertificate.mem_closure_iff x).symm
  · exact (normalMask_checked22 x.index).trans
      (N22.normalCertificate.mem_closure_iff x).symm
  · exact (normalMask_checked23 x.index).trans
      (N23.normalCertificate.mem_closure_iff x).symm
  · exact (normalMask_checked24 x.index).trans
      (N24.normalCertificate.mem_closure_iff x).symm
  · exact (normalMask_checked25 x.index).trans
      (N25.normalCertificate.mem_closure_iff x).symm
  · exact (normalMask_checked26 x.index).trans
      (N26.normalCertificate.mem_closure_iff x).symm
  · exact (normalMask_checked27 x.index).trans
      (N27.normalCertificate.mem_closure_iff x).symm

private def derivedWord0 : DerivedGeneratorWord (Fin 3) := .one
private def derivedWord1 : DerivedGeneratorWord (Fin 3) := .comm 0 2
private def derivedWord2 : DerivedGeneratorWord (Fin 3) := .comm 1 2
private def derivedWord3 : DerivedGeneratorWord (Fin 3) := .mul derivedWord1 derivedWord2
private def derivedWord4 : DerivedGeneratorWord (Fin 3) := .conj 1 derivedWord1
private def derivedWord5 : DerivedGeneratorWord (Fin 3) := .conj 2 derivedWord1
private def derivedWord6 : DerivedGeneratorWord (Fin 3) := .mul derivedWord2 derivedWord1
private def derivedWord7 : DerivedGeneratorWord (Fin 3) := .conj 0 derivedWord2
private def derivedWord8 : DerivedGeneratorWord (Fin 3) := .mul derivedWord3 derivedWord1
private def derivedWord9 : DerivedGeneratorWord (Fin 3) := .conj 0 derivedWord3
private def derivedWord10 : DerivedGeneratorWord (Fin 3) := .conj 1 derivedWord3
private def derivedWord11 : DerivedGeneratorWord (Fin 3) := .mul derivedWord4 derivedWord1
private def derivedWord12 : DerivedGeneratorWord (Fin 3) := .conjInv 2 derivedWord4
private def derivedWord13 : DerivedGeneratorWord (Fin 3) := .mul derivedWord5 derivedWord1
private def derivedWord14 : DerivedGeneratorWord (Fin 3) := .conj 2 derivedWord7
private def derivedWord15 : DerivedGeneratorWord (Fin 3) := .mul derivedWord8 derivedWord2

private def derivedWords (j : Fin 3) : DerivedGeneratorWord (Fin 3) :=
  (if j.val < 1 then derivedWord9 else (if j.val < 2 then derivedWord13 else derivedWord2))

private theorem derivedWords_checked : ∀ j : Fin 3,
    (derivedWords j).eval generators = N12.normalGenerators j := by
  intro j
  fin_cases j <;> decide +kernel

private def generatorCommutatorRow (i j : Fin 3) : Fin 16 :=
  ((if i.val < 1 then #[15,15,7] else (if i.val < 2 then #[15,15,2] else #[7,2,15])) : Array (Fin 16))[j.val]!

private theorem generatorCommutators_checked : ∀ i j : Fin 3,
    ⁅generators i, generators j⁆ =
      (⟨N12.normalCertificate.rows (generatorCommutatorRow i j)⟩ : Source) := by
  decide +kernel

/-- N12 is identified with the actual derived subgroup in both directions. -/
theorem source_derived_eq : commutator Source = N12.kernel := by
  apply le_antisymm
  · apply commutator_le_of_generator_commutators N12.kernel generators generators_full
    intro i j
    rw [generatorCommutators_checked]
    exact binaryNormalRow_mem N12.normalCertificate _
  · change Subgroup.closure (Set.range N12.normalGenerators) ≤ commutator Source
    apply (Subgroup.closure_le _).mpr
    rintro _ ⟨j, rfl⟩
    rw [← derivedWords_checked j]
    exact (derivedWords j).eval_mem_commutator generators

theorem source_derived_state_eq : commutator Source = (states derivedIndex).kernel :=
  source_derived_eq

theorem source_derived_card : Nat.card (commutator Source) = 16 := by
  rw [source_derived_eq]
  exact N12.kernel_card

end SymmetricSubgroupAsymptotics.BinaryCarrierNormal8T35
