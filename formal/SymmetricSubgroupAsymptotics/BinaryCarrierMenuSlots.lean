import SymmetricSubgroupAsymptotics.BinaryExceptional8ProfileCarriers
import SymmetricSubgroupAsymptotics.BinaryExceptional16ProfileCarrier

/-!
# Bundled slots for the remaining binary carrier menu

This file packages the three exceptional degree-eight charts and the proper
`16T1086` chart as heterogeneous `BinaryCarrierWordClosure.Slot`s.  It also
supplies the generic one-cell identity slot used to leave an original action
in place while retaining its actual quotient map and normal axis.
-/

set_option autoImplicit false
noncomputable section
open scoped Classical

namespace SymmetricSubgroupAsymptotics.BinaryCarrierMenuSlots

open SymmetricSubgroupAsymptotics
open BinaryCarrierProfileTransport
open BinaryCarrierWordClosure

section Identity

variable (g : MixtureKind) {Q : Type*} [Group Q]
  (α : mixtureAction g →* Q) (hα : Function.Surjective α)

def identityCarrier : Subgroup (∀ _ : Fin 1, mixtureAction g) := ⊤

theorem identityCarrier_full : CarrierProductFull (identityCarrier g) := by
  intro j u
  exact ⟨⟨fun _ => u,Subgroup.mem_top _⟩,rfl⟩

def identityBeta : identityCarrier g →* Q :=
  α.comp ((MulEquiv.piUnique (fun _ : Fin 1 => mixtureAction g)).toMonoidHom.comp
    (identityCarrier g).subtype)

include hα in
theorem identityBeta_surjective : Function.Surjective (identityBeta g α) := by
  intro q
  obtain ⟨u,hu⟩ := hα q
  refine ⟨⟨fun _ => u,Subgroup.mem_top _⟩,?_⟩
  simpa [identityBeta] using hu

/-- Leave one literal original action in place.  Its arbitrary actual
quotient map is retained on both sides, so the source axis need not be
trivial. -/
def identitySlot : Slot where
  Cells := Fin 1
  Source := mixtureAction g
  Quotient := Q
  cellsFintype := inferInstance
  sourceGroup := inferInstance
  quotientGroup := inferInstance
  sourceFinite := inferInstance
  color := fun _ => g
  carrier := identityCarrier g
  carrierFull := identityCarrier_full g
  alpha := α
  beta := identityBeta g α
  alphaSurjective := hα
  betaSurjective := identityBeta_surjective (hα := hα) g α

/-- The canonical identity slot for an actual normal axis. -/
def quotientIdentitySlot (N : Subgroup (mixtureAction g)) [N.Normal] : Slot :=
  identitySlot g (QuotientGroup.mk' N) (QuotientGroup.mk'_surjective N)

theorem quotientIdentitySlot_alpha_ker
    (N : Subgroup (mixtureAction g)) [N.Normal] :
    (quotientIdentitySlot g N).alpha.ker = N := by
  change (QuotientGroup.mk' N).ker = N
  exact QuotientGroup.ker_mk' N

end Identity

/-- The four fixed exceptional replacement charts left by the finite menu. -/
inductive Exceptional
  | t16
  | t20
  | t21
  | t1086
  deriving DecidableEq, Fintype

open BinaryExceptional8ProfileCarriers

def t16Slot : Slot where
  Cells := Fin 1
  Source := T16.Source
  Quotient := T16.Quotient
  cellsFintype := inferInstance
  sourceGroup := inferInstance
  quotientGroup := inferInstance
  sourceFinite := inferInstance
  color := fun _ => Target
  carrier := T16.flatCarrier
  carrierFull := T16.flatCarrier_full
  alpha := T16.alpha
  beta := T16.beta
  alphaSurjective := T16.alpha_surjective
  betaSurjective := T16.beta_surjective

def t20Slot : Slot where
  Cells := Fin 1
  Source := T20.Source
  Quotient := T20.Quotient
  cellsFintype := inferInstance
  sourceGroup := inferInstance
  quotientGroup := inferInstance
  sourceFinite := inferInstance
  color := fun _ => Target
  carrier := T20.flatCarrier
  carrierFull := T20.flatCarrier_full
  alpha := T20.alpha
  beta := T20.beta
  alphaSurjective := T20.alpha_surjective
  betaSurjective := T20.beta_surjective

def t21Slot : Slot where
  Cells := Fin 1
  Source := T21.Source
  Quotient := T21.Quotient
  cellsFintype := inferInstance
  sourceGroup := inferInstance
  quotientGroup := inferInstance
  sourceFinite := inferInstance
  color := fun _ => Target
  carrier := T21.flatCarrier
  carrierFull := T21.flatCarrier_full
  alpha := T21.alpha
  beta := T21.beta
  alphaSurjective := T21.alpha_surjective
  betaSurjective := T21.beta_surjective

namespace E1086

open BinaryExceptional16ProfileCarrier

def slot : Slot where
  Cells := Occurrence
  Source := Source
  Quotient := Quotient
  cellsFintype := inferInstance
  sourceGroup := inferInstance
  quotientGroup := inferInstance
  sourceFinite := inferInstance
  color := Sigma.fst
  carrier := flatCarrier
  carrierFull := flatCarrier_full
  alpha := alpha
  beta := beta
  alphaSurjective := alpha_surjective
  betaSurjective := beta_surjective

end E1086

def exceptionalSlot : Exceptional → Slot
  | .t16 => t16Slot
  | .t20 => t20Slot
  | .t21 => t21Slot
  | .t1086 => E1086.slot

/-- Every exceptional slot has a literal noncritical displayed cell. -/
theorem exceptional_has_noncritical (e : Exceptional) :
    ∃ j : (exceptionalSlot e).Cells, ∃ t,
      (exceptionalSlot e).color j = .inr t := by
  cases e with
  | t16 =>
      change ∃ j : Fin 1, ∃ t, Target = .inr t
      exact ⟨0,some (.degree8 .t27),rfl⟩
  | t20 =>
      change ∃ j : Fin 1, ∃ t, Target = .inr t
      exact ⟨0,some (.degree8 .t27),rfl⟩
  | t21 =>
      change ∃ j : Fin 1, ∃ t, Target = .inr t
      exact ⟨0,some (.degree8 .t27),rfl⟩
  | t1086 =>
      change ∃ j : BinaryExceptional16ProfileCarrier.Occurrence,
        ∃ t, j.1 = .inr t
      exact ⟨⟨.inr none,0⟩,none,rfl⟩

/-- Any nonempty simultaneous word made from the four exceptional charts is
absorbed by the exact completed mixture.  In particular this includes mixed
words and arbitrarily many occurrences of the nonabelian proper `16T1086`
carrier. -/
theorem exceptional_word_card_le_mixture
    {ι : Type*} [Fintype ι] [DecidableEq ι] [Nonempty ι]
    (route : ι → Exceptional) :
    Nat.card (CarrierTransportSource
      (alphas (fun i => exceptionalSlot (route i)))) ≤
      Nat.card (BinaryCarrierMixtureCompletion.Family
        (parameter
          (cells (fun i => exceptionalSlot (route i)))
          (colors (fun i => exceptionalSlot (route i))))) := by
  apply slot_source_card_le_mixture
  let i : ι := Classical.choice inferInstance
  obtain ⟨j,t,hj⟩ := exceptional_has_noncritical (route i)
  exact ⟨⟨i,j⟩,t,hj⟩

/-! ## Mixed unchanged and exceptional words -/

section Mixed

variable {ι δ : Type*} [Fintype ι] [DecidableEq ι]
  [Fintype δ] [DecidableEq δ]
  (color : ι → MixtureKind)
  (N : ∀ i, Subgroup (mixtureAction (color i)))
  [∀ i, (N i).Normal]
  (route : δ → Exceptional)

/-- Interleave literal unchanged original-action factors, carrying their
actual normal-axis quotient maps, with any of the four exceptional carrier
charts. -/
def mixedSlot : ι ⊕ δ → Slot
  | .inl i => quotientIdentitySlot (color i) (N i)
  | .inr d => exceptionalSlot (route d)

/-- The full mixed case enters one completed mixture whenever either an
unchanged factor is noncritical or at least one exceptional carrier occurs.
This includes arbitrary repetitions of the proper nonabelian `16T1086`
carrier among unchanged literal factors. -/
theorem mixed_word_card_le_mixture
    (hsupport : (∃ i, ∃ t, color i = .inr t) ∨ Nonempty δ) :
    Nat.card (CarrierTransportSource (alphas (mixedSlot color N route))) ≤
      Nat.card (BinaryCarrierMixtureCompletion.Family
        (parameter (cells (mixedSlot color N route))
          (colors (mixedSlot color N route)))) := by
  apply slot_source_card_le_mixture
  rcases hsupport with ⟨i,t,hi⟩ | hδ
  · let j : (mixedSlot color N route (.inl i)).Cells := by
      change Fin 1
      exact 0
    refine ⟨⟨.inl i,j⟩,t,?_⟩
    exact hi
  · let d : δ := Classical.choice hδ
    obtain ⟨j,t,hj⟩ := exceptional_has_noncritical (route d)
    exact ⟨⟨.inr d,j⟩,t,hj⟩

end Mixed

end SymmetricSubgroupAsymptotics.BinaryCarrierMenuSlots
