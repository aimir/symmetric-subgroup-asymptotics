import SymmetricSubgroupAsymptotics.CFSGMathieuElevenFourTransversalCover
import SymmetricSubgroupAsymptotics.CFSGMathieuElevenPresentationWords
import Mathlib.Tactic.FinCases

/-! Selected table-backed images of the38 existing stabilizer transversals.
The original Word.toM11 values are bound by whole eleven-point kernel
equalities. Data are from primary receipt 9bc0898f963e0d450331c2de3219ef8d910aa70671d8a41d2df9bfe8423474c0; generated data are
not proof until this source passes the primary check. No resource cap is
raised. Original input data are Kenta's Apache-2.0 M11 certificates. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
namespace SymmetricSubgroupAsymptotics.CFSGMathieuElevenFourTransversalSeedImages
open CFSG.Certificates.Mathieu11 CFSGMathieuElevenFourTransversalCover
open CFSGMathieuElevenPresentationWords


private def firstForward (i p : Fin 11) : Fin 11 :=
  match i.val with
  | 0 => (match p.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 3 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | 8 => 8 | 9 => 9 | _ => 10)
  | 1 => (match p.val with | 0 => 1 | 1 => 2 | 2 => 3 | 3 => 4 | 4 => 5 | 5 => 6 | 6 => 7 | 7 => 8 | 8 => 9 | 9 => 10 | _ => 0)
  | 2 => (match p.val with | 0 => 2 | 1 => 3 | 2 => 4 | 3 => 5 | 4 => 6 | 5 => 7 | 6 => 8 | 7 => 9 | 8 => 10 | 9 => 0 | _ => 1)
  | 3 => (match p.val with | 0 => 3 | 1 => 4 | 2 => 5 | 3 => 6 | 4 => 7 | 5 => 8 | 6 => 9 | 7 => 10 | 8 => 0 | 9 => 1 | _ => 2)
  | 4 => (match p.val with | 0 => 4 | 1 => 5 | 2 => 6 | 3 => 7 | 4 => 8 | 5 => 9 | 6 => 10 | 7 => 0 | 8 => 1 | 9 => 2 | _ => 3)
  | 5 => (match p.val with | 0 => 5 | 1 => 6 | 2 => 7 | 3 => 8 | 4 => 9 | 5 => 10 | 6 => 0 | 7 => 1 | 8 => 2 | 9 => 3 | _ => 4)
  | 6 => (match p.val with | 0 => 6 | 1 => 7 | 2 => 8 | 3 => 9 | 4 => 10 | 5 => 0 | 6 => 1 | 7 => 2 | 8 => 3 | 9 => 4 | _ => 5)
  | 7 => (match p.val with | 0 => 7 | 1 => 8 | 2 => 9 | 3 => 10 | 4 => 0 | 5 => 1 | 6 => 2 | 7 => 3 | 8 => 4 | 9 => 5 | _ => 6)
  | 8 => (match p.val with | 0 => 8 | 1 => 9 | 2 => 10 | 3 => 0 | 4 => 1 | 5 => 2 | 6 => 3 | 7 => 4 | 8 => 5 | 9 => 6 | _ => 7)
  | 9 => (match p.val with | 0 => 9 | 1 => 10 | 2 => 0 | 3 => 1 | 4 => 2 | 5 => 3 | 6 => 4 | 7 => 5 | 8 => 6 | 9 => 7 | _ => 8)
  | 10 => (match p.val with | 0 => 10 | 1 => 0 | 2 => 1 | 3 => 2 | 4 => 3 | 5 => 4 | 6 => 5 | 7 => 6 | 8 => 7 | 9 => 8 | _ => 9)
  | _ => p

private def firstInverse (i p : Fin 11) : Fin 11 :=
  match i.val with
  | 0 => (match p.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 3 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | 8 => 8 | 9 => 9 | _ => 10)
  | 1 => (match p.val with | 0 => 10 | 1 => 0 | 2 => 1 | 3 => 2 | 4 => 3 | 5 => 4 | 6 => 5 | 7 => 6 | 8 => 7 | 9 => 8 | _ => 9)
  | 2 => (match p.val with | 0 => 9 | 1 => 10 | 2 => 0 | 3 => 1 | 4 => 2 | 5 => 3 | 6 => 4 | 7 => 5 | 8 => 6 | 9 => 7 | _ => 8)
  | 3 => (match p.val with | 0 => 8 | 1 => 9 | 2 => 10 | 3 => 0 | 4 => 1 | 5 => 2 | 6 => 3 | 7 => 4 | 8 => 5 | 9 => 6 | _ => 7)
  | 4 => (match p.val with | 0 => 7 | 1 => 8 | 2 => 9 | 3 => 10 | 4 => 0 | 5 => 1 | 6 => 2 | 7 => 3 | 8 => 4 | 9 => 5 | _ => 6)
  | 5 => (match p.val with | 0 => 6 | 1 => 7 | 2 => 8 | 3 => 9 | 4 => 10 | 5 => 0 | 6 => 1 | 7 => 2 | 8 => 3 | 9 => 4 | _ => 5)
  | 6 => (match p.val with | 0 => 5 | 1 => 6 | 2 => 7 | 3 => 8 | 4 => 9 | 5 => 10 | 6 => 0 | 7 => 1 | 8 => 2 | 9 => 3 | _ => 4)
  | 7 => (match p.val with | 0 => 4 | 1 => 5 | 2 => 6 | 3 => 7 | 4 => 8 | 5 => 9 | 6 => 10 | 7 => 0 | 8 => 1 | 9 => 2 | _ => 3)
  | 8 => (match p.val with | 0 => 3 | 1 => 4 | 2 => 5 | 3 => 6 | 4 => 7 | 5 => 8 | 6 => 9 | 7 => 10 | 8 => 0 | 9 => 1 | _ => 2)
  | 9 => (match p.val with | 0 => 2 | 1 => 3 | 2 => 4 | 3 => 5 | 4 => 6 | 5 => 7 | 6 => 8 | 7 => 9 | 8 => 10 | 9 => 0 | _ => 1)
  | 10 => (match p.val with | 0 => 1 | 1 => 2 | 2 => 3 | 3 => 4 | 4 => 5 | 5 => 6 | 6 => 7 | 7 => 8 | 8 => 9 | 9 => 10 | _ => 0)
  | _ => p


def firstSeed (i : Fin 11) : Equiv.Perm (Fin 11) where
  toFun := firstForward i
  invFun := firstInverse i
  left_inv := by fin_cases i <;> decide +kernel
  right_inv := by fin_cases i <;> decide +kernel


private def secondForward (i p : Fin 11) : Fin 11 :=
  match i.val with
  | 1 => (match p.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 3 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | 8 => 8 | 9 => 9 | _ => 10)
  | 2 => (match p.val with | 0 => 0 | 1 => 2 | 2 => 9 | 3 => 8 | 4 => 5 | 5 => 1 | 6 => 3 | 7 => 10 | 8 => 7 | 9 => 4 | _ => 6)
  | 3 => (match p.val with | 0 => 0 | 1 => 3 | 2 => 8 | 3 => 5 | 4 => 6 | 5 => 4 | 6 => 1 | 7 => 2 | 8 => 9 | 9 => 10 | _ => 7)
  | 4 => (match p.val with | 0 => 0 | 1 => 4 | 2 => 8 | 3 => 9 | 4 => 7 | 5 => 3 | 6 => 1 | 7 => 10 | 8 => 5 | 9 => 2 | _ => 6)
  | 5 => (match p.val with | 0 => 0 | 1 => 5 | 2 => 8 | 3 => 4 | 4 => 2 | 5 => 9 | 6 => 1 | 7 => 7 | 8 => 3 | 9 => 6 | _ => 10)
  | 6 => (match p.val with | 0 => 0 | 1 => 6 | 2 => 4 | 3 => 8 | 4 => 3 | 5 => 1 | 6 => 9 | 7 => 7 | 8 => 2 | 9 => 5 | _ => 10)
  | 7 => (match p.val with | 0 => 0 | 1 => 7 | 2 => 3 | 3 => 8 | 4 => 4 | 5 => 1 | 6 => 5 | 7 => 6 | 8 => 10 | 9 => 9 | _ => 2)
  | 8 => (match p.val with | 0 => 0 | 1 => 8 | 2 => 1 | 3 => 4 | 4 => 9 | 5 => 6 | 6 => 7 | 7 => 5 | 8 => 2 | 9 => 3 | _ => 10)
  | 9 => (match p.val with | 0 => 0 | 1 => 9 | 2 => 3 | 3 => 2 | 4 => 8 | 5 => 6 | 6 => 5 | 7 => 7 | 8 => 4 | 9 => 1 | _ => 10)
  | 10 => (match p.val with | 0 => 0 | 1 => 10 | 2 => 5 | 3 => 8 | 4 => 9 | 5 => 1 | 6 => 4 | 7 => 2 | 8 => 6 | 9 => 3 | _ => 7)
  | _ => p

private def secondInverse (i p : Fin 11) : Fin 11 :=
  match i.val with
  | 1 => (match p.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 3 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | 8 => 8 | 9 => 9 | _ => 10)
  | 2 => (match p.val with | 0 => 0 | 1 => 5 | 2 => 1 | 3 => 6 | 4 => 9 | 5 => 4 | 6 => 10 | 7 => 8 | 8 => 3 | 9 => 2 | _ => 7)
  | 3 => (match p.val with | 0 => 0 | 1 => 6 | 2 => 7 | 3 => 1 | 4 => 5 | 5 => 3 | 6 => 4 | 7 => 10 | 8 => 2 | 9 => 8 | _ => 9)
  | 4 => (match p.val with | 0 => 0 | 1 => 6 | 2 => 9 | 3 => 5 | 4 => 1 | 5 => 8 | 6 => 10 | 7 => 4 | 8 => 2 | 9 => 3 | _ => 7)
  | 5 => (match p.val with | 0 => 0 | 1 => 6 | 2 => 4 | 3 => 8 | 4 => 3 | 5 => 1 | 6 => 9 | 7 => 7 | 8 => 2 | 9 => 5 | _ => 10)
  | 6 => (match p.val with | 0 => 0 | 1 => 5 | 2 => 8 | 3 => 4 | 4 => 2 | 5 => 9 | 6 => 1 | 7 => 7 | 8 => 3 | 9 => 6 | _ => 10)
  | 7 => (match p.val with | 0 => 0 | 1 => 5 | 2 => 10 | 3 => 2 | 4 => 4 | 5 => 6 | 6 => 7 | 7 => 1 | 8 => 3 | 9 => 9 | _ => 8)
  | 8 => (match p.val with | 0 => 0 | 1 => 2 | 2 => 8 | 3 => 9 | 4 => 3 | 5 => 7 | 6 => 5 | 7 => 6 | 8 => 1 | 9 => 4 | _ => 10)
  | 9 => (match p.val with | 0 => 0 | 1 => 9 | 2 => 3 | 3 => 2 | 4 => 8 | 5 => 6 | 6 => 5 | 7 => 7 | 8 => 4 | 9 => 1 | _ => 10)
  | 10 => (match p.val with | 0 => 0 | 1 => 5 | 2 => 7 | 3 => 9 | 4 => 6 | 5 => 2 | 6 => 8 | 7 => 10 | 8 => 3 | 9 => 4 | _ => 1)
  | _ => p


def secondSeed (i : Fin 11) : Equiv.Perm (Fin 11) where
  toFun := secondForward i
  invFun := secondInverse i
  left_inv := by fin_cases i <;> decide +kernel
  right_inv := by fin_cases i <;> decide +kernel


private def thirdForward (i p : Fin 11) : Fin 11 :=
  match i.val with
  | 2 => (match p.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 3 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | 8 => 8 | 9 => 9 | _ => 10)
  | 3 => (match p.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 9 | 4 => 10 | 5 => 4 | 6 => 8 | 7 => 6 | 8 => 7 | 9 => 2 | _ => 5)
  | 4 => (match p.val with | 0 => 0 | 1 => 1 | 2 => 4 | 3 => 5 | 4 => 2 | 5 => 3 | 6 => 8 | 7 => 7 | 8 => 6 | 9 => 10 | _ => 9)
  | 5 => (match p.val with | 0 => 0 | 1 => 1 | 2 => 5 | 3 => 2 | 4 => 3 | 5 => 4 | 6 => 10 | 7 => 7 | 8 => 9 | 9 => 6 | _ => 8)
  | 6 => (match p.val with | 0 => 0 | 1 => 1 | 2 => 6 | 3 => 9 | 4 => 5 | 5 => 3 | 6 => 10 | 7 => 2 | 8 => 8 | 9 => 4 | _ => 7)
  | 7 => (match p.val with | 0 => 0 | 1 => 1 | 2 => 7 | 3 => 5 | 4 => 9 | 5 => 4 | 6 => 2 | 7 => 10 | 8 => 8 | 9 => 3 | _ => 6)
  | 8 => (match p.val with | 0 => 0 | 1 => 1 | 2 => 8 | 3 => 10 | 4 => 3 | 5 => 5 | 6 => 9 | 7 => 4 | 8 => 6 | 9 => 2 | _ => 7)
  | 9 => (match p.val with | 0 => 0 | 1 => 1 | 2 => 9 | 3 => 2 | 4 => 5 | 5 => 10 | 6 => 7 | 7 => 8 | 8 => 6 | 9 => 3 | _ => 4)
  | 10 => (match p.val with | 0 => 0 | 1 => 1 | 2 => 10 | 3 => 4 | 4 => 3 | 5 => 9 | 6 => 7 | 7 => 6 | 8 => 8 | 9 => 5 | _ => 2)
  | _ => p

private def thirdInverse (i p : Fin 11) : Fin 11 :=
  match i.val with
  | 2 => (match p.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 3 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | 8 => 8 | 9 => 9 | _ => 10)
  | 3 => (match p.val with | 0 => 0 | 1 => 1 | 2 => 9 | 3 => 2 | 4 => 5 | 5 => 10 | 6 => 7 | 7 => 8 | 8 => 6 | 9 => 3 | _ => 4)
  | 4 => (match p.val with | 0 => 0 | 1 => 1 | 2 => 4 | 3 => 5 | 4 => 2 | 5 => 3 | 6 => 8 | 7 => 7 | 8 => 6 | 9 => 10 | _ => 9)
  | 5 => (match p.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 4 | 4 => 5 | 5 => 2 | 6 => 9 | 7 => 7 | 8 => 10 | 9 => 8 | _ => 6)
  | 6 => (match p.val with | 0 => 0 | 1 => 1 | 2 => 7 | 3 => 5 | 4 => 9 | 5 => 4 | 6 => 2 | 7 => 10 | 8 => 8 | 9 => 3 | _ => 6)
  | 7 => (match p.val with | 0 => 0 | 1 => 1 | 2 => 6 | 3 => 9 | 4 => 5 | 5 => 3 | 6 => 10 | 7 => 2 | 8 => 8 | 9 => 4 | _ => 7)
  | 8 => (match p.val with | 0 => 0 | 1 => 1 | 2 => 9 | 3 => 4 | 4 => 7 | 5 => 5 | 6 => 8 | 7 => 10 | 8 => 2 | 9 => 6 | _ => 3)
  | 9 => (match p.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 9 | 4 => 10 | 5 => 4 | 6 => 8 | 7 => 6 | 8 => 7 | 9 => 2 | _ => 5)
  | 10 => (match p.val with | 0 => 0 | 1 => 1 | 2 => 10 | 3 => 4 | 4 => 3 | 5 => 9 | 6 => 7 | 7 => 6 | 8 => 8 | 9 => 5 | _ => 2)
  | _ => p


def thirdSeed (i : Fin 11) : Equiv.Perm (Fin 11) where
  toFun := thirdForward i
  invFun := thirdInverse i
  left_inv := by fin_cases i <;> decide +kernel
  right_inv := by fin_cases i <;> decide +kernel


private def fourthForward (i p : Fin 11) : Fin 11 :=
  match i.val with
  | 3 => (match p.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 3 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | 8 => 8 | 9 => 9 | _ => 10)
  | 4 => (match p.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 9 | 5 => 8 | 6 => 10 | 7 => 3 | 8 => 6 | 9 => 7 | _ => 5)
  | 5 => (match p.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 5 | 4 => 10 | 5 => 9 | 6 => 3 | 7 => 8 | 8 => 4 | 9 => 6 | _ => 7)
  | 6 => (match p.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 6 | 4 => 8 | 5 => 3 | 6 => 9 | 7 => 10 | 8 => 7 | 9 => 5 | _ => 4)
  | 7 => (match p.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 7 | 4 => 3 | 5 => 10 | 6 => 8 | 7 => 9 | 8 => 5 | 9 => 4 | _ => 6)
  | 8 => (match p.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 8 | 4 => 5 | 5 => 7 | 6 => 4 | 7 => 6 | 8 => 9 | 9 => 10 | _ => 3)
  | 9 => (match p.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 9 | 4 => 7 | 5 => 6 | 6 => 5 | 7 => 4 | 8 => 10 | 9 => 3 | _ => 8)
  | 10 => (match p.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 10 | 4 => 6 | 5 => 4 | 6 => 7 | 7 => 5 | 8 => 3 | 9 => 8 | _ => 9)
  | _ => p

private def fourthInverse (i p : Fin 11) : Fin 11 :=
  match i.val with
  | 3 => (match p.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 3 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | 8 => 8 | 9 => 9 | _ => 10)
  | 4 => (match p.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 7 | 4 => 3 | 5 => 10 | 6 => 8 | 7 => 9 | 8 => 5 | 9 => 4 | _ => 6)
  | 5 => (match p.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 6 | 4 => 8 | 5 => 3 | 6 => 9 | 7 => 10 | 8 => 7 | 9 => 5 | _ => 4)
  | 6 => (match p.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 5 | 4 => 10 | 5 => 9 | 6 => 3 | 7 => 8 | 8 => 4 | 9 => 6 | _ => 7)
  | 7 => (match p.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 9 | 5 => 8 | 6 => 10 | 7 => 3 | 8 => 6 | 9 => 7 | _ => 5)
  | 8 => (match p.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 10 | 4 => 6 | 5 => 4 | 6 => 7 | 7 => 5 | 8 => 3 | 9 => 8 | _ => 9)
  | 9 => (match p.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 9 | 4 => 7 | 5 => 6 | 6 => 5 | 7 => 4 | 8 => 10 | 9 => 3 | _ => 8)
  | 10 => (match p.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 8 | 4 => 5 | 5 => 7 | 6 => 4 | 7 => 6 | 8 => 9 | 9 => 10 | _ => 3)
  | _ => p


def fourthSeed (i : Fin 11) : Equiv.Perm (Fin 11) where
  toFun := fourthForward i
  invFun := fourthInverse i
  left_inv := by fin_cases i <;> decide +kernel
  right_inv := by fin_cases i <;> decide +kernel



theorem first_coe_eq (i : Fin 11) : (first i).val=firstSeed i := by
  fin_cases i <;> ext p <;> fin_cases p <;> decide +kernel

theorem second_coe_eq : ∀ j : Second, (second j).val=secondSeed j.val := by
  decide +kernel

theorem third_coe_eq : ∀ k : Third, (third k).val=thirdSeed k.val := by
  decide +kernel

theorem fourth_coe_eq : ∀ l : Fourth, (fourth l).val=fourthSeed l.val := by
  decide +kernel

def decodedPermutation (c : Code) : Equiv.Perm (Fin 11) :=
  firstSeed c.1.1*secondSeed c.1.2.val*thirdSeed c.2.1.val*fourthSeed c.2.2.val

theorem decode_coe_eq (c : Code) : (decode c).val=decodedPermutation c := by
  simp only [decode,decodedPermutation,Subgroup.coe_mul,
    first_coe_eq,second_coe_eq,third_coe_eq,fourth_coe_eq]



private def yForward (p : Fin 11) : Fin 11 := (match p.val with | 0 => 0 | 1 => 1 | 2 => 6 | 3 => 9 | 4 => 5 | 5 => 3 | 6 => 10 | 7 => 2 | 8 => 8 | 9 => 4 | _ => 7)
private def yInverse (p : Fin 11) : Fin 11 := (match p.val with | 0 => 0 | 1 => 1 | 2 => 7 | 3 => 5 | 4 => 9 | 5 => 4 | 6 => 2 | 7 => 10 | 8 => 8 | 9 => 3 | _ => 6)

def ySeed : Equiv.Perm (Fin 11) where
  toFun := yForward
  invFun := yInverse
  left_inv := by decide +kernel
  right_inv := by decide +kernel

theorem y_coe_eq : y.val=ySeed := by
  ext p
  fin_cases p <;> decide +kernel

def relationValue {G : Type*} [Group G] (r : Fin 5) (u v : G) : G :=
  match r.val with
  | 0 => (u ^ 2)
  | 1 => (v ^ 4)
  | 2 => ((u * v) ^ 11)
  | 3 => ((u * (v ^ 2)) ^ 6)
  | _ => (((((((((((((((((u * v) * u) * v) * u) * ((v⁻¹) ^ 1)) * u) * v) * u) * (v ^ 2)) * u) * ((v⁻¹) ^ 1)) * u) * v) * u) * ((v⁻¹) ^ 1)) * u) * ((v⁻¹) ^ 1))

theorem relationValue_map {G H : Type*} [Group G] [Group H]
    (f : G →* H) (r : Fin 5) (u v : G) :
    f (relationValue r u v)=relationValue r (f u) (f v) := by
  fin_cases r <;> simp only [relationValue,map_pow,map_mul,map_inv]

theorem relationValue_coe (r : Fin 5) (u v : M11) :
    (relationValue r u v).val=relationValue r u.val v.val :=
  relationValue_map M11Subgroup.subtype r u v

def Accepts (u : M11) : Prop := ∀ r : Fin 5, relationValue r u y=1

theorem accepts_x : Accepts x := by
  intro r
  fin_cases r
  · exact relator_zero
  · exact relator_one
  · exact relator_two
  · exact relator_three
  · exact relator_four

theorem accepts_map_of_fixed_y (f : MulAut M11) (hf : f y=y) : Accepts (f x) := by
  intro r
  have h := congrArg f (accepts_x r)
  have hm := relationValue_map f.toMonoidHom r x y
  have he : relationValue r (f x) (f y)=1 := hm.symm.trans (by simpa only [map_one] using h)
  simpa only [hf] using he

theorem accepts_pointwise (c : Code) (h : Accepts (decode c)) (r : Fin 5) (p : Fin 11) :
    relationValue r (decodedPermutation c) ySeed p=p := by
  have hh := congrArg (fun g : M11 => g.val) (h r)
  change (relationValue r (decode c) y).val=(1 : Equiv.Perm (Fin 11)) at hh
  rw [relationValue_coe,decode_coe_eq,y_coe_eq] at hh
  exact congrArg (fun σ : Equiv.Perm (Fin 11) => σ p) hh

end SymmetricSubgroupAsymptotics.CFSGMathieuElevenFourTransversalSeedImages
