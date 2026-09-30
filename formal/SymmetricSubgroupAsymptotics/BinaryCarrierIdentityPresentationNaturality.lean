import SymmetricSubgroupAsymptotics.BinaryCarrierIdentityKernelNaturalizer
import SymmetricSubgroupAsymptotics.BinaryS16RouteSlotSkeleton

/-!
# Naturality from exposed quotient-identity presentations

The S16 route skeleton exposes every nonproper slot as a literal
`quotientIdentitySlot`, but the bundled slot equality is dependent.  These
definitions eliminate that equality once and return the carrier equivalence
and kernel-first quotient square at the original bundled-slot types.
-/

set_option autoImplicit false
noncomputable section
open scoped Classical

namespace SymmetricSubgroupAsymptotics.BinaryCarrierIdentityPresentationNaturality

open SymmetricSubgroupAsymptotics
open BinaryCarrierIdentityKernelNaturalizer
open BinaryCarrierIdentitySlotNaturality
open BinaryCarrierKernelNaturalizedReflection
open BinaryCarrierMenuSlots
open BinaryCarrierWordClosure
open BinaryS16RouteSlotSkeleton

/-- Evaluation of the unique displayed carrier coordinate of an exposed
quotient-identity slot. -/
def carrierEval {S : Slot} (P : IdentityPresentation S) :
    S.carrier →* S.Source := by
  rcases P with ⟨g,N,hN,hS⟩
  subst S
  exact BinaryCarrierMenuSlots.identityCarrierEval g

/-- Constant insertion is the inverse of evaluation on a one-cell full
carrier. -/
def carrierSection {S : Slot} (P : IdentityPresentation S) :
    S.Source →* S.carrier := by
  rcases P with ⟨g,N,hN,hS⟩
  subst S
  exact identityCarrierSection g

@[simp] theorem carrierEval_section {S : Slot}
    (P : IdentityPresentation S) (u : S.Source) :
    carrierEval P (carrierSection P u) = u := by
  rcases P with ⟨g,N,hN,hS⟩
  subst S
  rfl

theorem carrierSection_eval {S : Slot}
    (P : IdentityPresentation S) (p : S.carrier) :
    carrierSection P (carrierEval P p) = p := by
  rcases P with ⟨g,N,hN,hS⟩
  subst S
  change identityCarrier g at p
  change identityCarrierSection g
      (BinaryCarrierMenuSlots.identityCarrierEval g p) = p
  apply Subtype.ext
  funext i
  change Fin 1 at i
  change p.1 (0 : Fin 1) = p.1 i
  exact congrArg p.1 (Subsingleton.elim (0 : Fin 1) i)

/-- Coordinatewise carrier equivalence associated to two exposed identity
slots and an equivalence of their source actions. -/
def carrierEquiv {S T : Slot}
    (PS : IdentityPresentation S) (PT : IdentityPresentation T)
    (e : S.Source ≃* T.Source) : S.carrier ≃* T.carrier := by
  rcases PS with ⟨g,N,hN,hS⟩
  rcases PT with ⟨h,M,hM,hT⟩
  subst S
  subst T
  exact identityCarrierEquiv g e

@[simp] theorem carrierEval_carrierEquiv {S T : Slot}
    (PS : IdentityPresentation S) (PT : IdentityPresentation T)
    (e : S.Source ≃* T.Source) (p : S.carrier) :
    carrierEval PT (carrierEquiv PS PT e p) = e (carrierEval PS p) := by
  rcases PS with ⟨g,N,hN,hS⟩
  rcases PT with ⟨h,M,hM,hT⟩
  subst S
  subst T
  rfl

@[simp] theorem carrierEquiv_section {S T : Slot}
    (PS : IdentityPresentation S) (PT : IdentityPresentation T)
    (e : S.Source ≃* T.Source) (u : S.Source) :
    carrierEquiv PS PT e (carrierSection PS u) =
      carrierSection PT (e u) := by
  rcases PS with ⟨g,N,hN,hS⟩
  rcases PT with ⟨h,M,hM,hT⟩
  subst S
  subst T
  rfl

/-- Once equality of replacement kernels is recovered from the target, the
two exposed identity cells produce their canonical quotient square. -/
def quotientSquare {S T : Slot}
    (PS : IdentityPresentation S) (PT : IdentityPresentation T)
    (e : S.Source ≃* T.Source)
    (hkernel : S.beta.ker.map (carrierEquiv PS PT e).toMonoidHom =
      T.beta.ker) :
    QuotientSquare S.alpha T.alpha S.beta T.beta e
      (carrierEquiv PS PT e) := by
  rcases PS with ⟨g,N,hN,hS⟩
  rcases PT with ⟨h,M,hM,hT⟩
  subst S
  subst T
  exact BinaryCarrierIdentityKernelNaturalizer.quotientSquare
    g h N M e hkernel

end SymmetricSubgroupAsymptotics.BinaryCarrierIdentityPresentationNaturality

end
