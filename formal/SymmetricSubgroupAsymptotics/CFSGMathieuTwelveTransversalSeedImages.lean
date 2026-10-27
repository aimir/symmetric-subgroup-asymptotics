import SymmetricSubgroupAsymptotics.CFSGMathieuTwelveFiveTransversalCover
import SymmetricSubgroupAsymptotics.CFSGMathieuTwelveRecoveredPairRelations

/-! Selected 50-row M12 seed certificate, DATA receipt SHA409f72d0f8595c3a15aebd6460357a93088709e010206943c01465bfc3e64739.
The actual original Word.toM12 transversals remain the semantic inputs.
Every supplied table is independently bound by a whole-point kernel proof.
No incidence/capacity or other-prefix assertion; no resource cap is raised.
Original certificate data: Kenta, Apache-2.0, revision7f09e33. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
namespace SymmetricSubgroupAsymptotics.CFSGMathieuTwelveTransversalSeedImages
open CFSG.Certificates.Mathieu12 CFSGMathieuTwelveFiveTransversalCover
open CFSGMathieuTwelveRecoveredPairRelations
open CFSGMathieuTwelvePresentationWords

private def firstForward (i p : Fin 12) : Fin 12 :=
  match i.val with
  | 0 => (match p.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 3 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | 8 => 8 | 9 => 9 | 10 => 10 | _ => 11)
  | 1 => (match p.val with | 0 => 1 | 1 => 2 | 2 => 3 | 3 => 4 | 4 => 5 | 5 => 6 | 6 => 7 | 7 => 8 | 8 => 9 | 9 => 10 | 10 => 0 | _ => 11)
  | 2 => (match p.val with | 0 => 2 | 1 => 3 | 2 => 4 | 3 => 5 | 4 => 6 | 5 => 7 | 6 => 8 | 7 => 9 | 8 => 10 | 9 => 0 | 10 => 1 | _ => 11)
  | 3 => (match p.val with | 0 => 3 | 1 => 4 | 2 => 5 | 3 => 6 | 4 => 7 | 5 => 8 | 6 => 9 | 7 => 10 | 8 => 0 | 9 => 1 | 10 => 2 | _ => 11)
  | 4 => (match p.val with | 0 => 4 | 1 => 7 | 2 => 0 | 3 => 1 | 4 => 6 | 5 => 9 | 6 => 5 | 7 => 3 | 8 => 10 | 9 => 2 | 10 => 8 | _ => 11)
  | 5 => (match p.val with | 0 => 5 | 1 => 7 | 2 => 8 | 3 => 2 | 4 => 9 | 5 => 3 | 6 => 4 | 7 => 6 | 8 => 1 | 9 => 11 | 10 => 10 | _ => 0)
  | 6 => (match p.val with | 0 => 6 | 1 => 0 | 2 => 1 | 3 => 7 | 4 => 5 | 5 => 9 | 6 => 4 | 7 => 2 | 8 => 10 | 9 => 8 | 10 => 3 | _ => 11)
  | 7 => (match p.val with | 0 => 7 | 1 => 0 | 2 => 1 | 3 => 6 | 4 => 9 | 5 => 5 | 6 => 3 | 7 => 10 | 8 => 2 | 9 => 8 | 10 => 4 | _ => 11)
  | 8 => (match p.val with | 0 => 8 | 1 => 9 | 2 => 10 | 3 => 0 | 4 => 1 | 5 => 2 | 6 => 3 | 7 => 4 | 8 => 5 | 9 => 6 | 10 => 7 | _ => 11)
  | 9 => (match p.val with | 0 => 9 | 1 => 10 | 2 => 0 | 3 => 1 | 4 => 2 | 5 => 3 | 6 => 4 | 7 => 5 | 8 => 6 | 9 => 7 | 10 => 8 | _ => 11)
  | 10 => (match p.val with | 0 => 10 | 1 => 0 | 2 => 1 | 3 => 2 | 4 => 3 | 5 => 4 | 6 => 5 | 7 => 6 | 8 => 7 | 9 => 8 | 10 => 9 | _ => 11)
  | 11 => (match p.val with | 0 => 11 | 1 => 10 | 2 => 5 | 3 => 7 | 4 => 8 | 5 => 2 | 6 => 9 | 7 => 3 | 8 => 4 | 9 => 6 | 10 => 1 | _ => 0)
  | _ => p

private def firstInverse (i p : Fin 12) : Fin 12 :=
  match i.val with
  | 0 => (match p.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 3 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | 8 => 8 | 9 => 9 | 10 => 10 | _ => 11)
  | 1 => (match p.val with | 0 => 10 | 1 => 0 | 2 => 1 | 3 => 2 | 4 => 3 | 5 => 4 | 6 => 5 | 7 => 6 | 8 => 7 | 9 => 8 | 10 => 9 | _ => 11)
  | 2 => (match p.val with | 0 => 9 | 1 => 10 | 2 => 0 | 3 => 1 | 4 => 2 | 5 => 3 | 6 => 4 | 7 => 5 | 8 => 6 | 9 => 7 | 10 => 8 | _ => 11)
  | 3 => (match p.val with | 0 => 8 | 1 => 9 | 2 => 10 | 3 => 0 | 4 => 1 | 5 => 2 | 6 => 3 | 7 => 4 | 8 => 5 | 9 => 6 | 10 => 7 | _ => 11)
  | 4 => (match p.val with | 0 => 2 | 1 => 3 | 2 => 9 | 3 => 7 | 4 => 0 | 5 => 6 | 6 => 4 | 7 => 1 | 8 => 10 | 9 => 5 | 10 => 8 | _ => 11)
  | 5 => (match p.val with | 0 => 11 | 1 => 8 | 2 => 3 | 3 => 5 | 4 => 6 | 5 => 0 | 6 => 7 | 7 => 1 | 8 => 2 | 9 => 4 | 10 => 10 | _ => 9)
  | 6 => (match p.val with | 0 => 1 | 1 => 2 | 2 => 7 | 3 => 10 | 4 => 6 | 5 => 4 | 6 => 0 | 7 => 3 | 8 => 9 | 9 => 5 | 10 => 8 | _ => 11)
  | 7 => (match p.val with | 0 => 1 | 1 => 2 | 2 => 8 | 3 => 6 | 4 => 10 | 5 => 5 | 6 => 3 | 7 => 0 | 8 => 9 | 9 => 4 | 10 => 7 | _ => 11)
  | 8 => (match p.val with | 0 => 3 | 1 => 4 | 2 => 5 | 3 => 6 | 4 => 7 | 5 => 8 | 6 => 9 | 7 => 10 | 8 => 0 | 9 => 1 | 10 => 2 | _ => 11)
  | 9 => (match p.val with | 0 => 2 | 1 => 3 | 2 => 4 | 3 => 5 | 4 => 6 | 5 => 7 | 6 => 8 | 7 => 9 | 8 => 10 | 9 => 0 | 10 => 1 | _ => 11)
  | 10 => (match p.val with | 0 => 1 | 1 => 2 | 2 => 3 | 3 => 4 | 4 => 5 | 5 => 6 | 6 => 7 | 7 => 8 | 8 => 9 | 9 => 10 | 10 => 0 | _ => 11)
  | 11 => (match p.val with | 0 => 11 | 1 => 10 | 2 => 5 | 3 => 7 | 4 => 8 | 5 => 2 | 6 => 9 | 7 => 3 | 8 => 4 | 9 => 6 | 10 => 1 | _ => 0)
  | _ => p

def firstSeed (i : Fin 12) : Equiv.Perm (Fin 12) where
  toFun := firstForward i
  invFun := firstInverse i
  left_inv := by fin_cases i <;> decide +kernel
  right_inv := by fin_cases i <;> decide +kernel

private def secondForward (i p : Fin 12) : Fin 12 :=
  match i.val with
  | 1 => (match p.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 3 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | 8 => 8 | 9 => 9 | 10 => 10 | _ => 11)
  | 2 => (match p.val with | 0 => 0 | 1 => 2 | 2 => 9 | 3 => 8 | 4 => 5 | 5 => 1 | 6 => 3 | 7 => 10 | 8 => 7 | 9 => 4 | 10 => 6 | _ => 11)
  | 3 => (match p.val with | 0 => 0 | 1 => 3 | 2 => 7 | 3 => 5 | 4 => 4 | 5 => 9 | 6 => 8 | 7 => 6 | 8 => 2 | 9 => 1 | 10 => 10 | _ => 11)
  | 4 => (match p.val with | 0 => 0 | 1 => 4 | 2 => 8 | 3 => 9 | 4 => 7 | 5 => 3 | 6 => 1 | 7 => 10 | 8 => 5 | 9 => 2 | 10 => 6 | _ => 11)
  | 5 => (match p.val with | 0 => 0 | 1 => 5 | 2 => 8 | 3 => 4 | 4 => 2 | 5 => 9 | 6 => 1 | 7 => 7 | 8 => 3 | 9 => 6 | 10 => 10 | _ => 11)
  | 6 => (match p.val with | 0 => 0 | 1 => 6 | 2 => 4 | 3 => 8 | 4 => 3 | 5 => 1 | 6 => 9 | 7 => 7 | 8 => 2 | 9 => 5 | 10 => 10 | _ => 11)
  | 7 => (match p.val with | 0 => 0 | 1 => 7 | 2 => 6 | 3 => 5 | 4 => 1 | 5 => 10 | 6 => 4 | 7 => 3 | 8 => 2 | 9 => 8 | 10 => 11 | _ => 9)
  | 8 => (match p.val with | 0 => 0 | 1 => 8 | 2 => 2 | 3 => 1 | 4 => 5 | 5 => 10 | 6 => 4 | 7 => 9 | 8 => 6 | 9 => 7 | 10 => 11 | _ => 3)
  | 9 => (match p.val with | 0 => 0 | 1 => 9 | 2 => 8 | 3 => 1 | 4 => 4 | 5 => 3 | 6 => 7 | 7 => 2 | 8 => 6 | 9 => 5 | 10 => 10 | _ => 11)
  | 10 => (match p.val with | 0 => 0 | 1 => 10 | 2 => 7 | 3 => 3 | 4 => 8 | 5 => 2 | 6 => 6 | 7 => 5 | 8 => 9 | 9 => 4 | 10 => 11 | _ => 1)
  | 11 => (match p.val with | 0 => 0 | 1 => 11 | 2 => 9 | 3 => 4 | 4 => 6 | 5 => 7 | 6 => 1 | 7 => 8 | 8 => 2 | 9 => 3 | 10 => 5 | _ => 10)
  | _ => p

private def secondInverse (i p : Fin 12) : Fin 12 :=
  match i.val with
  | 1 => (match p.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 3 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | 8 => 8 | 9 => 9 | 10 => 10 | _ => 11)
  | 2 => (match p.val with | 0 => 0 | 1 => 5 | 2 => 1 | 3 => 6 | 4 => 9 | 5 => 4 | 6 => 10 | 7 => 8 | 8 => 3 | 9 => 2 | 10 => 7 | _ => 11)
  | 3 => (match p.val with | 0 => 0 | 1 => 9 | 2 => 8 | 3 => 1 | 4 => 4 | 5 => 3 | 6 => 7 | 7 => 2 | 8 => 6 | 9 => 5 | 10 => 10 | _ => 11)
  | 4 => (match p.val with | 0 => 0 | 1 => 6 | 2 => 9 | 3 => 5 | 4 => 1 | 5 => 8 | 6 => 10 | 7 => 4 | 8 => 2 | 9 => 3 | 10 => 7 | _ => 11)
  | 5 => (match p.val with | 0 => 0 | 1 => 6 | 2 => 4 | 3 => 8 | 4 => 3 | 5 => 1 | 6 => 9 | 7 => 7 | 8 => 2 | 9 => 5 | 10 => 10 | _ => 11)
  | 6 => (match p.val with | 0 => 0 | 1 => 5 | 2 => 8 | 3 => 4 | 4 => 2 | 5 => 9 | 6 => 1 | 7 => 7 | 8 => 3 | 9 => 6 | 10 => 10 | _ => 11)
  | 7 => (match p.val with | 0 => 0 | 1 => 4 | 2 => 8 | 3 => 7 | 4 => 6 | 5 => 3 | 6 => 2 | 7 => 1 | 8 => 9 | 9 => 11 | 10 => 5 | _ => 10)
  | 8 => (match p.val with | 0 => 0 | 1 => 3 | 2 => 2 | 3 => 11 | 4 => 6 | 5 => 4 | 6 => 8 | 7 => 9 | 8 => 1 | 9 => 7 | 10 => 5 | _ => 10)
  | 9 => (match p.val with | 0 => 0 | 1 => 3 | 2 => 7 | 3 => 5 | 4 => 4 | 5 => 9 | 6 => 8 | 7 => 6 | 8 => 2 | 9 => 1 | 10 => 10 | _ => 11)
  | 10 => (match p.val with | 0 => 0 | 1 => 11 | 2 => 5 | 3 => 3 | 4 => 9 | 5 => 7 | 6 => 6 | 7 => 2 | 8 => 4 | 9 => 8 | 10 => 1 | _ => 10)
  | 11 => (match p.val with | 0 => 0 | 1 => 6 | 2 => 8 | 3 => 9 | 4 => 3 | 5 => 10 | 6 => 4 | 7 => 5 | 8 => 7 | 9 => 2 | 10 => 11 | _ => 1)
  | _ => p

def secondSeed (i : Fin 12) : Equiv.Perm (Fin 12) where
  toFun := secondForward i
  invFun := secondInverse i
  left_inv := by fin_cases i <;> decide +kernel
  right_inv := by fin_cases i <;> decide +kernel

private def thirdForward (i p : Fin 12) : Fin 12 :=
  match i.val with
  | 2 => (match p.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 3 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | 8 => 8 | 9 => 9 | 10 => 10 | _ => 11)
  | 3 => (match p.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 6 | 4 => 4 | 5 => 10 | 6 => 2 | 7 => 9 | 8 => 7 | 9 => 8 | 10 => 11 | _ => 5)
  | 4 => (match p.val with | 0 => 0 | 1 => 1 | 2 => 4 | 3 => 8 | 4 => 6 | 5 => 5 | 6 => 10 | 7 => 9 | 8 => 7 | 9 => 3 | 10 => 2 | _ => 11)
  | 5 => (match p.val with | 0 => 0 | 1 => 1 | 2 => 5 | 3 => 8 | 4 => 10 | 5 => 3 | 6 => 7 | 7 => 4 | 8 => 2 | 9 => 9 | 10 => 6 | _ => 11)
  | 6 => (match p.val with | 0 => 0 | 1 => 1 | 2 => 6 | 3 => 9 | 4 => 5 | 5 => 3 | 6 => 10 | 7 => 2 | 8 => 8 | 9 => 4 | 10 => 7 | _ => 11)
  | 7 => (match p.val with | 0 => 0 | 1 => 1 | 2 => 7 | 3 => 5 | 4 => 9 | 5 => 4 | 6 => 2 | 7 => 10 | 8 => 8 | 9 => 3 | 10 => 6 | _ => 11)
  | 8 => (match p.val with | 0 => 0 | 1 => 1 | 2 => 8 | 3 => 11 | 4 => 7 | 5 => 4 | 6 => 6 | 7 => 5 | 8 => 9 | 9 => 2 | 10 => 3 | _ => 10)
  | 9 => (match p.val with | 0 => 0 | 1 => 1 | 2 => 9 | 3 => 10 | 4 => 5 | 5 => 7 | 6 => 6 | 7 => 4 | 8 => 2 | 9 => 8 | 10 => 11 | _ => 3)
  | 10 => (match p.val with | 0 => 0 | 1 => 1 | 2 => 10 | 3 => 4 | 4 => 3 | 5 => 9 | 6 => 7 | 7 => 6 | 8 => 8 | 9 => 5 | 10 => 2 | _ => 11)
  | 11 => (match p.val with | 0 => 0 | 1 => 1 | 2 => 11 | 3 => 5 | 4 => 10 | 5 => 8 | 6 => 4 | 7 => 6 | 8 => 2 | 9 => 7 | 10 => 9 | _ => 3)
  | _ => p

private def thirdInverse (i p : Fin 12) : Fin 12 :=
  match i.val with
  | 2 => (match p.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 3 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | 8 => 8 | 9 => 9 | 10 => 10 | _ => 11)
  | 3 => (match p.val with | 0 => 0 | 1 => 1 | 2 => 6 | 3 => 2 | 4 => 4 | 5 => 11 | 6 => 3 | 7 => 8 | 8 => 9 | 9 => 7 | 10 => 5 | _ => 10)
  | 4 => (match p.val with | 0 => 0 | 1 => 1 | 2 => 10 | 3 => 9 | 4 => 2 | 5 => 5 | 6 => 4 | 7 => 8 | 8 => 3 | 9 => 7 | 10 => 6 | _ => 11)
  | 5 => (match p.val with | 0 => 0 | 1 => 1 | 2 => 8 | 3 => 5 | 4 => 7 | 5 => 2 | 6 => 10 | 7 => 6 | 8 => 3 | 9 => 9 | 10 => 4 | _ => 11)
  | 6 => (match p.val with | 0 => 0 | 1 => 1 | 2 => 7 | 3 => 5 | 4 => 9 | 5 => 4 | 6 => 2 | 7 => 10 | 8 => 8 | 9 => 3 | 10 => 6 | _ => 11)
  | 7 => (match p.val with | 0 => 0 | 1 => 1 | 2 => 6 | 3 => 9 | 4 => 5 | 5 => 3 | 6 => 10 | 7 => 2 | 8 => 8 | 9 => 4 | 10 => 7 | _ => 11)
  | 8 => (match p.val with | 0 => 0 | 1 => 1 | 2 => 9 | 3 => 10 | 4 => 5 | 5 => 7 | 6 => 6 | 7 => 4 | 8 => 2 | 9 => 8 | 10 => 11 | _ => 3)
  | 9 => (match p.val with | 0 => 0 | 1 => 1 | 2 => 8 | 3 => 11 | 4 => 7 | 5 => 4 | 6 => 6 | 7 => 5 | 8 => 9 | 9 => 2 | 10 => 3 | _ => 10)
  | 10 => (match p.val with | 0 => 0 | 1 => 1 | 2 => 10 | 3 => 4 | 4 => 3 | 5 => 9 | 6 => 7 | 7 => 6 | 8 => 8 | 9 => 5 | 10 => 2 | _ => 11)
  | 11 => (match p.val with | 0 => 0 | 1 => 1 | 2 => 8 | 3 => 11 | 4 => 6 | 5 => 3 | 6 => 7 | 7 => 9 | 8 => 5 | 9 => 10 | 10 => 4 | _ => 2)
  | _ => p

def thirdSeed (i : Fin 12) : Equiv.Perm (Fin 12) where
  toFun := thirdForward i
  invFun := thirdInverse i
  left_inv := by fin_cases i <;> decide +kernel
  right_inv := by fin_cases i <;> decide +kernel

private def fourthForward (i p : Fin 12) : Fin 12 :=
  match i.val with
  | 3 => (match p.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 3 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | 8 => 8 | 9 => 9 | 10 => 10 | _ => 11)
  | 4 => (match p.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 9 | 5 => 8 | 6 => 10 | 7 => 3 | 8 => 6 | 9 => 7 | 10 => 5 | _ => 11)
  | 5 => (match p.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 5 | 4 => 10 | 5 => 9 | 6 => 3 | 7 => 8 | 8 => 4 | 9 => 6 | 10 => 7 | _ => 11)
  | 6 => (match p.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 6 | 4 => 8 | 5 => 3 | 6 => 9 | 7 => 10 | 8 => 7 | 9 => 5 | 10 => 4 | _ => 11)
  | 7 => (match p.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 7 | 4 => 9 | 5 => 11 | 6 => 5 | 7 => 8 | 8 => 3 | 9 => 10 | 10 => 4 | _ => 6)
  | 8 => (match p.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 8 | 4 => 10 | 5 => 6 | 6 => 11 | 7 => 3 | 8 => 7 | 9 => 4 | 10 => 9 | _ => 5)
  | 9 => (match p.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 9 | 4 => 3 | 5 => 4 | 6 => 11 | 7 => 8 | 8 => 6 | 9 => 5 | 10 => 10 | _ => 7)
  | 10 => (match p.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 10 | 4 => 6 | 5 => 4 | 6 => 7 | 7 => 5 | 8 => 3 | 9 => 8 | 10 => 9 | _ => 11)
  | 11 => (match p.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 11 | 4 => 6 | 5 => 9 | 6 => 5 | 7 => 10 | 8 => 8 | 9 => 4 | 10 => 3 | _ => 7)
  | _ => p

private def fourthInverse (i p : Fin 12) : Fin 12 :=
  match i.val with
  | 3 => (match p.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 3 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | 8 => 8 | 9 => 9 | 10 => 10 | _ => 11)
  | 4 => (match p.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 7 | 4 => 3 | 5 => 10 | 6 => 8 | 7 => 9 | 8 => 5 | 9 => 4 | 10 => 6 | _ => 11)
  | 5 => (match p.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 6 | 4 => 8 | 5 => 3 | 6 => 9 | 7 => 10 | 8 => 7 | 9 => 5 | 10 => 4 | _ => 11)
  | 6 => (match p.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 5 | 4 => 10 | 5 => 9 | 6 => 3 | 7 => 8 | 8 => 4 | 9 => 6 | 10 => 7 | _ => 11)
  | 7 => (match p.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 8 | 4 => 10 | 5 => 6 | 6 => 11 | 7 => 3 | 8 => 7 | 9 => 4 | 10 => 9 | _ => 5)
  | 8 => (match p.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 7 | 4 => 9 | 5 => 11 | 6 => 5 | 7 => 8 | 8 => 3 | 9 => 10 | 10 => 4 | _ => 6)
  | 9 => (match p.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 5 | 5 => 9 | 6 => 8 | 7 => 11 | 8 => 7 | 9 => 3 | 10 => 10 | _ => 6)
  | 10 => (match p.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 8 | 4 => 5 | 5 => 7 | 6 => 4 | 7 => 6 | 8 => 9 | 9 => 10 | 10 => 3 | _ => 11)
  | 11 => (match p.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 10 | 4 => 9 | 5 => 6 | 6 => 4 | 7 => 11 | 8 => 8 | 9 => 5 | 10 => 7 | _ => 3)
  | _ => p

def fourthSeed (i : Fin 12) : Equiv.Perm (Fin 12) where
  toFun := fourthForward i
  invFun := fourthInverse i
  left_inv := by fin_cases i <;> decide +kernel
  right_inv := by fin_cases i <;> decide +kernel

private def fifthForward (i p : Fin 12) : Fin 12 :=
  match i.val with
  | 4 => (match p.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 3 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | 8 => 8 | 9 => 9 | 10 => 10 | _ => 11)
  | 5 => (match p.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 3 | 4 => 5 | 5 => 6 | 6 => 10 | 7 => 9 | 8 => 11 | 9 => 8 | 10 => 4 | _ => 7)
  | 6 => (match p.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 3 | 4 => 6 | 5 => 10 | 6 => 4 | 7 => 8 | 8 => 7 | 9 => 11 | 10 => 5 | _ => 9)
  | 7 => (match p.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 3 | 4 => 7 | 5 => 11 | 6 => 8 | 7 => 6 | 8 => 4 | 9 => 5 | 10 => 9 | _ => 10)
  | 8 => (match p.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 3 | 4 => 8 | 5 => 9 | 6 => 7 | 7 => 4 | 8 => 6 | 9 => 10 | 10 => 11 | _ => 5)
  | 9 => (match p.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 3 | 4 => 9 | 5 => 7 | 6 => 11 | 7 => 10 | 8 => 5 | 9 => 6 | 10 => 8 | _ => 4)
  | 10 => (match p.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 3 | 4 => 10 | 5 => 4 | 6 => 5 | 7 => 11 | 8 => 9 | 9 => 7 | 10 => 6 | _ => 8)
  | 11 => (match p.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 3 | 4 => 11 | 5 => 8 | 6 => 9 | 7 => 5 | 8 => 10 | 9 => 4 | 10 => 7 | _ => 6)
  | _ => p

private def fifthInverse (i p : Fin 12) : Fin 12 :=
  match i.val with
  | 4 => (match p.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 3 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | 8 => 8 | 9 => 9 | 10 => 10 | _ => 11)
  | 5 => (match p.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 3 | 4 => 10 | 5 => 4 | 6 => 5 | 7 => 11 | 8 => 9 | 9 => 7 | 10 => 6 | _ => 8)
  | 6 => (match p.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 3 | 4 => 6 | 5 => 10 | 6 => 4 | 7 => 8 | 8 => 7 | 9 => 11 | 10 => 5 | _ => 9)
  | 7 => (match p.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 3 | 4 => 8 | 5 => 9 | 6 => 7 | 7 => 4 | 8 => 6 | 9 => 10 | 10 => 11 | _ => 5)
  | 8 => (match p.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 3 | 4 => 7 | 5 => 11 | 6 => 8 | 7 => 6 | 8 => 4 | 9 => 5 | 10 => 9 | _ => 10)
  | 9 => (match p.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 3 | 4 => 11 | 5 => 8 | 6 => 9 | 7 => 5 | 8 => 10 | 9 => 4 | 10 => 7 | _ => 6)
  | 10 => (match p.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 3 | 4 => 5 | 5 => 6 | 6 => 10 | 7 => 9 | 8 => 11 | 9 => 8 | 10 => 4 | _ => 7)
  | 11 => (match p.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 3 | 4 => 9 | 5 => 7 | 6 => 11 | 7 => 10 | 8 => 5 | 9 => 6 | 10 => 8 | _ => 4)
  | _ => p

def fifthSeed (i : Fin 12) : Equiv.Perm (Fin 12) where
  toFun := fifthForward i
  invFun := fifthInverse i
  left_inv := by fin_cases i <;> decide +kernel
  right_inv := by fin_cases i <;> decide +kernel

theorem first_coe_eq (i : Fin 12) : (first i).val = firstSeed i := by
  fin_cases i <;> ext p <;> fin_cases p <;> decide +kernel

theorem second_coe_eq : ∀ i : Second, (second i).val = secondSeed i.val := by
  decide +kernel

theorem third_coe_eq : ∀ i : Third, (third i).val = thirdSeed i.val := by
  decide +kernel

theorem fourth_coe_eq : ∀ i : Fourth, (fourth i).val = fourthSeed i.val := by
  decide +kernel

theorem fifth_coe_eq : ∀ i : Fifth, (fifth i).val = fifthSeed i.val := by
  decide +kernel

def decodedPermutation (c : Code) : Equiv.Perm (Fin 12) :=
  firstSeed c.1.1 * secondSeed c.1.2.val * thirdSeed c.2.1.val *
    fourthSeed c.2.2.1.val * fifthSeed c.2.2.2.val

theorem decode_coe_eq (c : Code) : (decode c).val = decodedPermutation c := by
  simp only [decode,decodedPermutation,Subgroup.coe_mul,
    first_coe_eq,second_coe_eq,third_coe_eq,fourth_coe_eq,fifth_coe_eq]

private def fixedForward (p : Fin 12) : Fin 12 := (match p.val with | 0 => 6 | 1 => 11 | 2 => 3 | 3 => 10 | 4 => 4 | 5 => 1 | 6 => 8 | 7 => 2 | 8 => 5 | 9 => 7 | 10 => 0 | _ => 9)

private def fixedInverse (p : Fin 12) : Fin 12 := (match p.val with | 0 => 10 | 1 => 5 | 2 => 7 | 3 => 2 | 4 => 4 | 5 => 8 | 6 => 0 | 7 => 9 | 8 => 6 | 9 => 11 | 10 => 3 | _ => 1)

def fixedSeed : Equiv.Perm (Fin 12) where
  toFun := fixedForward
  invFun := fixedInverse
  left_inv := by decide +kernel
  right_inv := by decide +kernel

theorem firstElement_coe_eq : firstElement.val = fixedSeed := by
  change x.val * y.val = fixedSeed
  rw [x_coe_eq,y_coe_eq]
  ext p
  fin_cases p <;> decide +kernel

end SymmetricSubgroupAsymptotics.CFSGMathieuTwelveTransversalSeedImages
