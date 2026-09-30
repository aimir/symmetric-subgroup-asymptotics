import SymmetricSubgroupAsymptotics.BinaryCarrierKernelNaturalizedReflection
import SymmetricSubgroupAsymptotics.BinaryCarrierFusionNaturalPointChart

/-!
# Naturality under equality of bundled carrier slots

A retained proper route is a literal bundled slot.  Once the finite record
identifies the two slots, all of its source, carrier, quotient, cell, and
displayed-point data transport by equality.  This module names those casts
and packages their commuting quotient square.
-/

set_option autoImplicit false
noncomputable section
open scoped Classical

namespace SymmetricSubgroupAsymptotics.BinaryCarrierSlotCastNaturality

open SymmetricSubgroupAsymptotics
open BinaryCarrierKernelNaturalizedReflection
open BinaryCarrierWordClosure

/-- Source-group transport induced by equality of bundled slots. -/
def sourceEquivOfEq {S T : Slot} (h : S = T) : S.Source ≃* T.Source := by
  subst T
  exact MulEquiv.refl _

/-- Carrier-group transport induced by equality of bundled slots. -/
def carrierEquivOfEq {S T : Slot} (h : S = T) : S.carrier ≃* T.carrier := by
  subst T
  exact MulEquiv.refl _

/-- Quotient-group transport induced by equality of bundled slots. -/
def quotientEquivOfEq {S T : Slot} (h : S = T) : S.Quotient ≃* T.Quotient := by
  subst T
  exact MulEquiv.refl _

/-- The source and replacement quotient maps commute with literal slot
transport. -/
def quotientSquareOfEq {S T : Slot} (h : S = T) :
    QuotientSquare S.alpha T.alpha S.beta T.beta
      (sourceEquivOfEq h) (carrierEquivOfEq h) := by
  subst T
  exact QuotientSquare.refl S.alpha S.beta

/-- Equality of bundled slots transports their complete displayed-point
sigma. -/
def displayedPointEquivOfEq {S T : Slot} (h : S = T) :
    (Σ c : S.Cells, BinaryCarrierProfileTransport.mixturePoints (S.color c)) ≃
      (Σ c : T.Cells, BinaryCarrierProfileTransport.mixturePoints (T.color c)) :=
  Equiv.cast (congrArg
    (fun R : Slot =>
      Σ c : R.Cells, BinaryCarrierProfileTransport.mixturePoints (R.color c)) h)

@[simp] theorem sourceEquivOfEq_rfl (S : Slot) :
    sourceEquivOfEq (rfl : S = S) = MulEquiv.refl S.Source := rfl

@[simp] theorem carrierEquivOfEq_rfl (S : Slot) :
    carrierEquivOfEq (rfl : S = S) = MulEquiv.refl S.carrier := rfl

@[simp] theorem displayedPointEquivOfEq_rfl (S : Slot) :
    displayedPointEquivOfEq (rfl : S = S) = Equiv.refl _ := rfl

/-- Proof irrelevance removes a self-cast even when its equality proof was
assembled through dependent route matching rather than written as `rfl`. -/
@[simp] theorem sourceEquivOfEq_self {S : Slot} (h : S = S) :
    sourceEquivOfEq h = MulEquiv.refl S.Source := by
  rw [Subsingleton.elim h rfl]
  rfl

@[simp] theorem carrierEquivOfEq_self {S : Slot} (h : S = S) :
    carrierEquivOfEq h = MulEquiv.refl S.carrier := by
  rw [Subsingleton.elim h rfl]
  rfl

@[simp] theorem displayedPointEquivOfEq_self {S : Slot} (h : S = S) :
    displayedPointEquivOfEq h = Equiv.refl _ := by
  rw [Subsingleton.elim h rfl]
  rfl

end SymmetricSubgroupAsymptotics.BinaryCarrierSlotCastNaturality

end
