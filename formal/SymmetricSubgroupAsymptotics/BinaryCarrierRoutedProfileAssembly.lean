import SymmetricSubgroupAsymptotics.BinaryCarrierRoutedWordClosure

/-!
# Assembly by the canonical normal-axis profile

A full subgroup of a finite product determines one literal normal axis in
each coordinate.  After removing every subgroup with a direct local owner,
this canonical axis profile partitions the residual without any chosen orbit,
axis, quotient, or route marking.  Each fixed profile is then exactly the
source family consumed by the routed carrier-word theorem.

The final statement deliberately retains the finite sum over residual axis
profiles.  Routed transport is injective inside each fixed profile; no
cross-profile identification is assumed here.
-/

set_option autoImplicit false
set_option maxHeartbeats 0
noncomputable section
open scoped Classical BigOperators

namespace SymmetricSubgroupAsymptotics.BinaryCarrierRoutedProfileAssembly

open SymmetricSubgroupAsymptotics
open FullSubdirectGoursat
open BinaryCarrierProfileTransport
open BinaryCarrierWordClosure
open BinaryCarrierSourceExtraction
open BinaryDegreeEightPhysicalAnalyticClosure
open BinaryCarrierRoutedWordClosure

variable {ι : Type*} [Fintype ι] [DecidableEq ι]
  (A : ι → Type) [∀ i, Group (A i)] [∀ i, Finite (A i)]

/-- The literal normal axis in every source coordinate. -/
abbrev AxisProfile := ∀ i, NormalAxis (A i)

/-- Original full subgroups; no axis or owner witness is counted. -/
abbrev FullFamily :=
  {H : Subgroup (∀ i, A i) // CarrierProductFull H}

/-- The canonical axis profile extracted from the subgroup itself. -/
def axisProfile (H : FullFamily A) : AxisProfile A :=
  fun i => ⟨carrierAxis H.1 i,carrierAxis_normal H.1 H.2 i⟩

variable (D : ∀ i, NormalAxis (A i) → Prop)

/-- At least one coordinate has already entered a direct continuation. -/
def DirectAt (H : FullFamily A) : Prop :=
  ∃ i, D i (axisProfile A H i)

/-- The unmarked complement of all direct local owners. -/
abbrev CarrierResidual :=
  {H : FullFamily A // ¬ DirectAt A D H}

/-- Exactly the axis profiles on which no direct local owner fires. -/
abbrev ResidualAxisProfile :=
  {ν : AxisProfile A // ∀ i, ¬ D i (ν i)}

/-- The dependent sum of fixed-axis residual fibres. -/
abbrev ResidualCode :=
  Σ ν : ResidualAxisProfile A D,
    BinaryCarrierRoutedWordClosure.ExactAxisFamily A (fun i => (ν.1 i).1)

/-- Record the unique literal axis profile of a residual subgroup. -/
def residualCode (H : CarrierResidual A D) : ResidualCode A D := by
  let ν : ResidualAxisProfile A D :=
    ⟨axisProfile A H.1,fun i hi => H.2 ⟨i,hi⟩⟩
  exact ⟨ν,⟨H.1.1,H.1.2,fun _ => rfl⟩⟩

/-- The profile code retains the original subgroup and is therefore
injective.  In particular, partitioning by axes creates no multiplicity. -/
theorem residualCode_injective :
    Function.Injective (residualCode A D) := by
  intro H K h
  apply Subtype.ext
  apply Subtype.ext
  exact congrArg (fun z : ResidualCode A D => z.2.1) h

variable
  (hroute : ∀ i (ν : NormalAxis (A i)),
    D i ν ∨ Nonempty (AxisSlot (A i) ν.1))

/-- On a residual profile, finite choice selects one exact route in each
coordinate.  The choice affects only the target map, not the counted source. -/
def residualSlot (ν : ResidualAxisProfile A D) (i : ι) :
    AxisSlot (A i) (ν.1 i).1 :=
  Classical.choice ((hroute i (ν.1 i)).resolve_left (ν.2 i))

/-- The exact finite residual-profile sum.  Every fibre enters its completed
mixture family, and the source partition remains canonical. -/
theorem carrierResidual_card_le_profile_mixture_sum
    (hsupport : ∀ ν : ResidualAxisProfile A D,
      ∃ c : Σ i, (residualSlot A D hroute ν i).slot.Cells,
        ∃ t, (residualSlot A D hroute ν c.1).slot.color c.2 = Sum.inr t) :
    Nat.card (CarrierResidual A D) ≤
      ∑ ν : ResidualAxisProfile A D,
        Nat.card (BinaryCarrierMixtureCompletion.Family
          (parameter
            (cells (fun i => (residualSlot A D hroute ν i).slot))
            (colors (fun i => (residualSlot A D hroute ν i).slot)))) := by
  calc
    Nat.card (CarrierResidual A D) ≤ Nat.card (ResidualCode A D) :=
      Nat.card_le_card_of_injective _ (residualCode_injective A D)
    _ = ∑ ν : ResidualAxisProfile A D,
        Nat.card (BinaryCarrierRoutedWordClosure.ExactAxisFamily A
          (fun i => (ν.1 i).1)) := Nat.card_sigma
    _ ≤ ∑ ν : ResidualAxisProfile A D,
        Nat.card (BinaryCarrierMixtureCompletion.Family
          (parameter
            (cells (fun i => (residualSlot A D hroute ν i).slot))
            (colors (fun i => (residualSlot A D hroute ν i).slot)))) := by
      apply Finset.sum_le_sum
      intro ν _
      exact exact_axis_word_card_le_mixture A (fun i => (ν.1 i).1)
        (residualSlot A D hroute ν) (hsupport ν)

end SymmetricSubgroupAsymptotics.BinaryCarrierRoutedProfileAssembly
