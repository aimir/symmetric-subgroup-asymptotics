/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
import Mathlib.Algebra.Group.Commutator
import Mathlib.GroupTheory.PresentedGroup

/-!
Minimal source port from TauCeti commit
`6e0c6acab5f4c6f42e5f5bab9bd5e4e84f74c380`, for a Lean 4.30 presentation
comparison. The retained carrier definitions and Co2 row have their upstream
names. Module/public/expose syntax and unrelated cyclic-reduction, length,
metadata-checking and row-field lemmas are omitted. The compiler correctness
proof is retained. The Co2 metadata strings are provenance, not theorems.

Sources: TauCeti/GroupTheory/Presentation/{Relator,GroupPresentation}.lean and
TauCeti/GroupTheory/SpecificGroups/CFSG/Sporadic/Conway/Two.lean.
No upstream order, simplicity, classification or permutation-model proof is
part of this port.
-/

namespace TauCeti

open scoped commutatorElement

abbrev PresentationWord (α : Type*) := List (α × Bool)

inductive Relator (α : Type*) where
  | gen (x : α)
  | inv (r : Relator α)
  | mul (r s : Relator α)
  | pow (r : Relator α) (n : ℕ)
  | comm (r s : Relator α)
  deriving DecidableEq

namespace Relator

def toWord {α : Type*} : Relator α → PresentationWord α
  | .gen x => [(x, true)]
  | .inv r => FreeGroup.invRev r.toWord
  | .mul r s => r.toWord ++ s.toWord
  | .pow r n => (List.replicate n r.toWord).flatten
  | .comm r s => ((r.toWord ++ s.toWord) ++ FreeGroup.invRev r.toWord) ++
      FreeGroup.invRev s.toWord

@[simp] theorem toWord_gen {α : Type*} (x : α) :
    (Relator.gen x).toWord = [(x, true)] := by rw [toWord]

@[simp] theorem toWord_inv {α : Type*} (r : Relator α) :
    (Relator.inv r).toWord = FreeGroup.invRev r.toWord := by rw [toWord]

@[simp] theorem toWord_mul {α : Type*} (r s : Relator α) :
    (Relator.mul r s).toWord = r.toWord ++ s.toWord := by rw [toWord]

@[simp] theorem toWord_pow {α : Type*} (r : Relator α) (n : ℕ) :
    (Relator.pow r n).toWord = (List.replicate n r.toWord).flatten := by rw [toWord]

@[simp] theorem toWord_comm {α : Type*} (r s : Relator α) :
    (Relator.comm r s).toWord =
      ((r.toWord ++ s.toWord) ++ FreeGroup.invRev r.toWord) ++ FreeGroup.invRev s.toWord := by
  rw [toWord]

def toFreeGroup {α : Type*} : Relator α → FreeGroup α
  | .gen x => FreeGroup.of x
  | .inv r => r.toFreeGroup⁻¹
  | .mul r s => r.toFreeGroup * s.toFreeGroup
  | .pow r n => r.toFreeGroup ^ n
  | .comm r s => ⁅r.toFreeGroup, s.toFreeGroup⁆

@[simp] theorem toFreeGroup_gen {α : Type*} (x : α) :
    (Relator.gen x).toFreeGroup = FreeGroup.of x := by rw [toFreeGroup]

@[simp] theorem toFreeGroup_inv {α : Type*} (r : Relator α) :
    (Relator.inv r).toFreeGroup = r.toFreeGroup⁻¹ := by rw [toFreeGroup]

@[simp] theorem toFreeGroup_mul {α : Type*} (r s : Relator α) :
    (Relator.mul r s).toFreeGroup = r.toFreeGroup * s.toFreeGroup := by rw [toFreeGroup]

@[simp] theorem toFreeGroup_pow {α : Type*} (r : Relator α) (n : ℕ) :
    (Relator.pow r n).toFreeGroup = r.toFreeGroup ^ n := by rw [toFreeGroup]

@[simp] theorem toFreeGroup_comm {α : Type*} (r s : Relator α) :
    (Relator.comm r s).toFreeGroup = ⁅r.toFreeGroup, s.toFreeGroup⁆ := by rw [toFreeGroup]

def commInvInv {α : Type*} (r s : Relator α) : Relator α := .comm (.inv r) (.inv s)

@[simp] theorem toFreeGroup_commInvInv {α : Type*} (r s : Relator α) :
    (r.commInvInv s).toFreeGroup =
      r.toFreeGroup⁻¹ * s.toFreeGroup⁻¹ * r.toFreeGroup * s.toFreeGroup := by
  rw [commInvInv, toFreeGroup_comm, toFreeGroup_inv, toFreeGroup_inv,
    commutatorElement_def, inv_inv, inv_inv]

@[simp] theorem toWord_toFreeGroup {α : Type*} (r : Relator α) :
    FreeGroup.mk r.toWord = r.toFreeGroup := by
  induction r with
  | gen => rfl
  | inv r ih => rw [toWord_inv, toFreeGroup_inv, ← FreeGroup.inv_mk, ih]
  | mul r s ihr ihs => rw [toWord_mul, toFreeGroup_mul, ← FreeGroup.mul_mk, ihr, ihs]
  | pow r n ih => rw [toWord_pow, toFreeGroup_pow, ← FreeGroup.pow_mk, ih]
  | comm r s ihr ihs =>
      rw [toWord_comm, toFreeGroup_comm, commutatorElement_def, ← FreeGroup.mul_mk,
        ← FreeGroup.mul_mk, ← FreeGroup.mul_mk, ← FreeGroup.inv_mk, ← FreeGroup.inv_mk,
        ihr, ihs]

end Relator

structure GroupPresentation where
  generatorNames : List String
  source : String
  sourceLocator : String
  generatorConvention : String
  transcriptionNotes : String
  expectedGeneratorCount : ℕ
  expectedRelatorCount : ℕ
  transcribed : List (Relator (Fin generatorNames.length))

namespace GroupPresentation

abbrev generatorCount (P : GroupPresentation) : ℕ := P.generatorNames.length

def relators (P : GroupPresentation) : List (PresentationWord (Fin P.generatorCount)) :=
  P.transcribed.map Relator.toWord

theorem relators_def (P : GroupPresentation) : P.relators = P.transcribed.map Relator.toWord := by
  rw [relators]

def relatorSet (P : GroupPresentation) : Set (FreeGroup (Fin P.generatorCount)) :=
  {r | r ∈ P.relators.map FreeGroup.mk}

abbrev Group (P : GroupPresentation) : Type := PresentedGroup P.relatorSet

end GroupPresentation

namespace Sporadic

private abbrev a : Relator (Fin 2) := .gen 0
private abbrev b : Relator (Fin 2) := .gen 1
local infixl:70 " ⬝ " => Relator.mul
private abbrev ab1 : Relator (Fin 2) := a ⬝ b
private abbrev ab2 : Relator (Fin 2) := a ⬝ .pow b 2
private abbrev abNeg1 : Relator (Fin 2) := a ⬝ .inv b
private abbrev abNeg2 : Relator (Fin 2) := a ⬝ .pow (.inv b) 2

def co2Presentation : GroupPresentation where
  generatorNames := ["a", "b"]
  source := "R. A. Wilson, R. A. Parker, J. N. Bray et al., ATLAS of Finite Group \
    Representations, version 3; presentation contributed by John Bray"
  sourceLocator := "Co2G1-P1, https://brauer.maths.qmul.ac.uk/Atlas/v3/pres/Co2G1-P1, with the \
    relator list and the demonstration of correctness in the Magma source file \
    https://brauer.maths.qmul.ac.uk/Atlas/spor/Co2/mag/Co2G1-P1.M"
  generatorConvention := "The ATLAS standard generators a and b of Co2, that is, a in class 2A \
    and b in class 5A with ab of order 28, in that order, so index 0 is a and index 1 is b. \
    Products are read left to right, negative exponents denote inverses, and [r,s] denotes \
    r^-1 s^-1 r s."
  transcriptionNotes := "The ten words of the source's relator list are stored as ten relators \
    equal to the identity. The source's eleventh displayed word (x,y^2*x*y^2)^3 is struck out of \
    the relator list, shown struck through on the presentation page and commented out as \
    'Redundant, but useful.' in the Magma file, so it lies outside the relator list and is not \
    transcribed. The source demonstrates correctness with and without that word, enumerating in \
    each case the 56925 cosets of a subgroup that centralizes a, \
    which is the index of the involution centralizer [2^9].S6(2) in Co2. GAP 4.15.1 checks that \
    the ten compiled words vanish on five independent standard generating pairs of the 2300-point \
    primitive representation of Co2, taking a with centralizer of order 743178240, b of order 5 \
    with centralizer of order 3000, and ab of order 28."
  expectedGeneratorCount := 2
  expectedRelatorCount := 10
  transcribed :=
    [ .pow a 2,
      .pow b 5,
      .pow ab2 9,
      .pow (.commInvInv a b) 4,
      .pow (.commInvInv a (.pow b 2)) 4,
      .pow (.commInvInv a (b ⬝ a ⬝ b)) 3,
      .pow (.commInvInv a (b ⬝ ab2 ⬝ ab1)) 2,
      .pow (.commInvInv a (b ⬝ abNeg2)) 3,
      .pow (.commInvInv a (.pow (.inv b) 2 ⬝ ab1 ⬝ abNeg2)) 2,
      .pow (ab1 ⬝ ab2 ⬝ abNeg1 ⬝ abNeg2) 7 ]

end Sporadic
end TauCeti
