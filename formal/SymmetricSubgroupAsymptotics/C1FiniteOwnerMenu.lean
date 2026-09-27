import SymmetricSubgroupAsymptotics.C1FiniteOwnerTransport
import SymmetricSubgroupAsymptotics.FaithfulFiniteActionImage
import SymmetricSubgroupAsymptotics.TernaryOwnerWitness6T1
import SymmetricSubgroupAsymptotics.TernaryOwnerWitness6T4
import SymmetricSubgroupAsymptotics.TernaryOwnerWitness6T5
import SymmetricSubgroupAsymptotics.TernaryOwnerWitness6T6
import SymmetricSubgroupAsymptotics.TernaryOwnerWitness12T20
import SymmetricSubgroupAsymptotics.TernaryOwnerWitness12T85
import SymmetricSubgroupAsymptotics.TernaryOwnerWitness12T164
import SymmetricSubgroupAsymptotics.TernaryPrimeBase12T194
import SymmetricSubgroupAsymptotics.TernaryV4Semidirect12T228
import SymmetricSubgroupAsymptotics.TernaryV4Semidirect12T229
import SymmetricSubgroupAsymptotics.TernaryV4Semidirect12T265

/-!
# The exact bounded c=1 owner menu

This file gives the surviving degree-six and degree-twelve owner actions one
typed, invariant recognition target.  A recognition contains an actual
labelling of the original point set and equality of its literal permutation
image with a checked owner action.  Thus future high-pair coverage cannot
replace action membership by equality of orders or by an unverified catalogue
name.

The first seven actions are also connected here to their intrinsic owner
witnesses on the literal permutation groups.  The remaining four actions keep
their checked prime-base or V4-block geometry in the corresponding certificate
modules imported above.
-/

set_option autoImplicit false
noncomputable section
open scoped Classical

namespace SymmetricSubgroupAsymptotics

inductive C1BoundedOwnerLabel
  | sixT1 | sixT4 | sixT5 | sixT6
  | twelveT20 | twelveT85 | twelveT164 | twelveT194
  | twelveT228 | twelveT229 | twelveT265
  deriving DecidableEq, Fintype

namespace C1BoundedOwnerLabel

def width : C1BoundedOwnerLabel → ℕ
  | .sixT1 | .sixT4 | .sixT5 | .sixT6 => 6
  | .twelveT20 | .twelveT85 | .twelveT164 | .twelveT194
  | .twelveT228 | .twelveT229 | .twelveT265 => 12

@[simp] theorem width_eq_six_or_twelve (i : C1BoundedOwnerLabel) :
    i.width = 6 ∨ i.width = 12 := by
  cases i <;> simp [width]

/-- The checked literal subgroup on its original point set. -/
def action : (i : C1BoundedOwnerLabel) → Subgroup (Equiv.Perm (Fin i.width))
  | .sixT1 => Subgroup.closure (Set.range TernaryOwnerCayley6T1.generators)
  | .sixT4 => Subgroup.closure (Set.range TernaryOwnerCayley6T4.generators)
  | .sixT5 => Subgroup.closure (Set.range TernaryOwnerCayley6T5.generators)
  | .sixT6 => Subgroup.closure (Set.range TernaryOwnerCayley6T6.generators)
  | .twelveT20 => Subgroup.closure (Set.range TernaryOwnerCayley12T20.generators)
  | .twelveT85 => Subgroup.closure (Set.range TernaryOwnerCayley12T85.generators)
  | .twelveT164 => Subgroup.closure (Set.range TernaryOwnerCayley12T164.generators)
  | .twelveT194 => TernaryPrimeBase12T194.certificate.action
  | .twelveT228 => TernaryV4Semidirect12T228.certificate.action
  | .twelveT229 => TernaryV4Semidirect12T229.certificate.action
  | .twelveT265 => TernaryV4Semidirect12T265.certificate.action

/-- The two degree-six index-two owners, now on their literal original
permutation groups rather than on executable row indices. -/
def sixT1Owner : C1OddIndexTwoOwnerWitness C1BoundedOwnerLabel.sixT1.action := by
  letI : Group (FiniteGroupRow 6) := TernaryOwnerCayley6T1.group
  exact TernaryOwnerWitness6T1.earlierOwner.map TernaryOwnerCayley6T1.originalEquiv

def sixT5Owner : C1OddIndexTwoOwnerWitness C1BoundedOwnerLabel.sixT5.action := by
  letI : Group (FiniteGroupRow 18) := TernaryOwnerCayley6T5.group
  exact TernaryOwnerWitness6T5.earlierOwner.map TernaryOwnerCayley6T5.originalEquiv

/-- The five cyclic binary-module owners, transported to the literal original
permutation groups with their distinguished vectors and conjugate words. -/
def sixT4Owner : C1CyclicBinaryModuleOwnerWitness C1BoundedOwnerLabel.sixT4.action := by
  letI : Group (FiniteGroupRow 12) := TernaryOwnerCayley6T4.group
  exact TernaryOwnerWitness6T4.earlierOwner.map TernaryOwnerCayley6T4.originalEquiv

def sixT6Owner : C1CyclicBinaryModuleOwnerWitness C1BoundedOwnerLabel.sixT6.action := by
  letI : Group (FiniteGroupRow 24) := TernaryOwnerCayley6T6.group
  exact TernaryOwnerWitness6T6.earlierOwner.map TernaryOwnerCayley6T6.originalEquiv

def twelveT20Owner :
    C1CyclicBinaryModuleOwnerWitness C1BoundedOwnerLabel.twelveT20.action := by
  letI : Group (FiniteGroupRow 36) := TernaryOwnerCayley12T20.group
  exact TernaryOwnerWitness12T20.earlierOwner.map TernaryOwnerCayley12T20.originalEquiv

def twelveT85Owner :
    C1CyclicBinaryModuleOwnerWitness C1BoundedOwnerLabel.twelveT85.action := by
  letI : Group (FiniteGroupRow 144) := TernaryOwnerCayley12T85.group
  exact TernaryOwnerWitness12T85.earlierOwner.map TernaryOwnerCayley12T85.originalEquiv

def twelveT164Owner :
    C1CyclicBinaryModuleOwnerWitness C1BoundedOwnerLabel.twelveT164.action := by
  letI : Group (FiniteGroupRow 576) := TernaryOwnerCayley12T164.group
  exact TernaryOwnerWitness12T164.earlierOwner.map
    TernaryOwnerCayley12T164.originalEquiv

end C1BoundedOwnerLabel

/-- Exact action-level recognition of an arbitrary original action by one of
the eleven checked bounded owners. -/
structure C1BoundedOwnerRecognition (A Ω : Type) [Group A] [MulAction A Ω] where
  label : C1BoundedOwnerLabel
  points : Ω ≃ Fin label.width
  image_eq : labelledActionImage (A := A) points = label.action

namespace C1BoundedOwnerRecognition

variable {A Ω : Type} [Group A] [MulAction A Ω]

theorem card (R : C1BoundedOwnerRecognition A Ω) : Nat.card Ω = R.label.width :=
  labelledAction_card R.points

/-- Faithfulness upgrades exact recognized image equality to an ambient group
equivalence.  Intrinsic owner witnesses can then be transported back to the
original group by `C1FiniteOwnerTransport`. -/
def groupEquiv [FaithfulSMul A Ω] (R : C1BoundedOwnerRecognition A Ω) :
    A ≃* R.label.action :=
  (faithfulLabelledActionEquiv R.points).trans (MulEquiv.subgroupCongr R.image_eq)

@[simp] theorem groupEquiv_coe [FaithfulSMul A Ω]
    (R : C1BoundedOwnerRecognition A Ω) (a : A) :
    (R.groupEquiv a : Equiv.Perm (Fin R.label.width)) =
      labelledActionHom R.points a := rfl

end C1BoundedOwnerRecognition

end SymmetricSubgroupAsymptotics

end
