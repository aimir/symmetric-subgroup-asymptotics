import SymmetricSubgroupAsymptotics.BinaryCarrierProfileTransport

/-!
# Physical carrier targets on a supplied labelled point chart

The generic carrier producer normally relabels its completed orbit profile
onto a canonical `Fin` point set.  Fibrewise reconstruction of an actual
permutation subgroup instead needs the resulting carrier subgroup on the
original labelled ambient set.  This file exposes the same construction for
an arbitrary supplied complete point chart.

No chart is counted here.  An application constructs the chart canonically
from its literal orbit data and uses the resulting physical subgroup as the
target.  Injectivity is only asserted after that chart has been fixed.
-/

set_option autoImplicit false
noncomputable section
open scoped Classical

namespace SymmetricSubgroupAsymptotics.BinaryCarrierOriginalLabelPhysicalTarget

open SymmetricSubgroupAsymptotics
open BinaryCarrierParameterProfiles
open BinaryCarrierProfileTransport

variable {ι : Type*}
  {U Q : ι → Type*} [∀ i, Group (U i)] [∀ i, Group (Q i)]
  {κ : ι → Type*} {V : ∀ i, κ i → Type*} [∀ i j, Group (V i j)]

variable
  (C : ∀ i, Subgroup (∀ j, V i j))
  (hC : ∀ i, CarrierProductFull (C i))
  (α : ∀ i, U i →* Q i) (β : ∀ i, C i →* Q i)
  (hα : ∀ i, Function.Surjective (α i))
  (hβ : ∀ i, Function.Surjective (β i))

variable {R a T : ℕ} (s : ProfileIndex R a T)
  (Dmix : ProfileDisplay (V := V) mixtureAction
    (profileMultiplicity R a T s))

/-- Realize a literal full displayed carrier subgroup on any supplied
labelled point chart.  This is the original-label analogue of
`ProfileDisplay.physicalTarget`. -/
def ProfileDisplay.physicalTargetOn {X : Type*}
    (e : OrbitProfilePoints mixturePoints
      (profileMultiplicity R a T s) ≃ X) :
    CarrierTransportTarget (V := V) → PhysicalFamily R a T X := fun H => by
  let M := ProfileDisplay.modelTarget (Ω := mixturePoints)
    mixtureAction (profileMultiplicity R a T s) Dmix H
  exact ⟨relabelSubgroup e M.1,s,e,M.1,M.2,rfl⟩

/-- A fixed supplied point chart loses no displayed carrier subgroup. -/
theorem ProfileDisplay.physicalTargetOn_injective {X : Type*}
    (e : OrbitProfilePoints mixturePoints
      (profileMultiplicity R a T s) ≃ X) :
    Function.Injective (ProfileDisplay.physicalTargetOn s Dmix e) := by
  intro H K h
  apply ProfileDisplay.modelTarget_injective (Ω := mixturePoints)
    mixtureAction (profileMultiplicity R a T s) Dmix
  apply Subtype.ext
  apply (relabelSubgroup e).injective
  exact congrArg Subtype.val h

/-- Simultaneous carrier transport followed by realization on a supplied
labelled point chart. -/
def physicalTransportOn {X : Type*}
    (e : OrbitProfilePoints mixturePoints
      (profileMultiplicity R a T s) ≃ X)
    [DecidableEq ι] :
    CarrierTransportSource α → PhysicalFamily R a T X := fun H =>
  ProfileDisplay.physicalTargetOn s Dmix e
    (carrierTransportRecords C hC α β hα hβ H)

/-- The supplied-chart transport factors through the literal simultaneous
carrier subgroup. -/
theorem physicalTransportOn_eq_physicalTargetOn {X : Type*}
    (e : OrbitProfilePoints mixturePoints
      (profileMultiplicity R a T s) ≃ X)
    [DecidableEq ι] (H : CarrierTransportSource α) :
    physicalTransportOn C hC α β hα hβ s Dmix e H =
      ProfileDisplay.physicalTargetOn s Dmix e
        (carrierTransportRecords C hC α β hα hβ H) :=
  rfl

/-- Reversibility of simultaneous carrier transport and faithfulness of the
supplied chart give injectivity on the complete source relation. -/
theorem physicalTransportOn_injective {X : Type*}
    (e : OrbitProfilePoints mixturePoints
      (profileMultiplicity R a T s) ≃ X)
    [Finite ι] [DecidableEq ι] :
    Function.Injective (physicalTransportOn C hC α β hα hβ s Dmix e) :=
  (ProfileDisplay.physicalTargetOn_injective s Dmix e).comp
    (carrierTransportRecords_injective C hC α β hα hβ)

end SymmetricSubgroupAsymptotics.BinaryCarrierOriginalLabelPhysicalTarget

end
