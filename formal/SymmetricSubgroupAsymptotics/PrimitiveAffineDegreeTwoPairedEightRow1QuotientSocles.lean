import SymmetricSubgroupAsymptotics.PrimitiveAffineDegreeTwoPairedEightSharedTops
import SymmetricSubgroupAsymptotics.PrimitiveAffineDegreeTwoPairedEightRow1NaturalModule
import SymmetricSubgroupAsymptotics.PrimitiveAffineDegreeTwoPairTopStructuralAnchor

/-!
# Quotient socles and Schur data for paired-eight row 1

The shared row-0 normal-word registry has six states.  This file checks the
relative minimal-normal lattice and a uniformly padded two-position normal
generator for the socle above each state.  It transports those data to the
literal degree-eight top and combines them with the independently checked
natural-module generator theorem.
-/

set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 0
noncomputable section
open scoped Classical

namespace SymmetricSubgroupAsymptotics
namespace Non2UnipotentPrefixFiniteMenu
namespace PrimitiveAffineImprimitiveBlockTransfer
namespace DegreeTwoPairedEightRow1QuotientSocles

namespace TopCert := PrimitiveAffineEightFrameRow0TopCertificate
namespace NormalCert := PrimitiveAffineEightFrameRow0NormalCertificate
namespace Natural := PrimitiveAffineDegreeTwoPairedEightRow1NaturalModule
namespace Shared := DegreeTwoPairedEightSharedTops

abbrev Source := TopCert.Source
local instance sourceGroup : Group Source := TopCert.group

private def rowState (i : Fin 6) : Subgroup Source :=
  Subgroup.closure (Set.range (NormalCert.stateGenerators i))

private theorem rowState_injective : Function.Injective rowState := by
  native_decide

noncomputable def rowRegistry : FiniteNormalStateRegistry Source :=
  FiniteNormalStateRegistry.ofWordRegistry
    NormalCert.topConjugacy.toCardinalCover NormalCert.topAmbient
    NormalCert.stateGenerators NormalCert.data rowState_injective

noncomputable def topRegistry : FiniteNormalStateRegistry Natural.Top :=
  rowRegistry.mapEquiv Natural.actionEquiv

private abbrev RR := rowRegistry

private theorem rowRegistry_state (i : Fin 6) :
    RR.state i = rowState i := rfl

private def RowIsMinimalStateAbove (base j : Fin 6) : Prop :=
  rowState base < rowState j ∧
    ∀ k : Fin 6, rowState base < rowState k →
      rowState k ≤ rowState j → rowState k = rowState j

private theorem rowRegistry_minimal_iff (base j : Fin 6) :
    RR.IsMinimalStateAbove base j ↔ RowIsMinimalStateAbove base j := by
  rfl

private def carrierState (i : Fin 6) : Fin 6 :=
  ![3, 3, 5, 5, 5, 5] i

private def state0Generators : Fin 2 → Source := ![⟨4⟩, ⟨3⟩]
private def state1Generators : Fin 2 → Source := ![⟨2⟩, ⟨0⟩]
private def state2Generators : Fin 2 → Source := ![⟨12⟩, ⟨7⟩]
private def state3Generators : Fin 2 → Source := ![⟨7⟩, ⟨0⟩]
private def state4Generators : Fin 2 → Source := ![⟨4⟩, ⟨0⟩]
private def state5Generators : Fin 2 → Source := ![⟨0⟩, ⟨0⟩]

private def rowGenerator (i : Fin 6) : Fin 2 → Source :=
  ![state0Generators, state1Generators, state2Generators,
    state3Generators, state4Generators, state5Generators] i

private theorem row_carrier_eq_checked : ∀ i : Fin 6,
    rowState (carrierState i) = rowState i ⊔
      ⨆ j : {j : Fin 6 // RowIsMinimalStateAbove i j}, rowState j.1 := by
  native_decide

private theorem row_generated_checked : ∀ i : Fin 6,
    Subgroup.normalClosure (Set.range (rowGenerator i)) ⊔ rowState i =
      rowState (carrierState i) := by
  native_decide

noncomputable def rowStateData (i : Fin 6) :
    FiniteRelativeSocleGeneratorData Source (RR.state i) 2 :=
  RR.relativeSocleGeneratorDataOfStates i (carrierState i) 2
    {j : Fin 6 // RowIsMinimalStateAbove i j}
    Subtype.val
    (fun j ↦ (rowRegistry_minimal_iff i j).2 j.property)
    (fun j hj ↦ ⟨⟨j, (rowRegistry_minimal_iff i j).1 hj⟩, rfl⟩)
    (by simpa only [rowRegistry_state] using row_carrier_eq_checked i)
    (rowGenerator i)
    (by simpa only [rowRegistry_state] using row_generated_checked i)

noncomputable def topStateData (i : Fin 6) :
    FiniteRelativeSocleGeneratorData Natural.Top (topRegistry.state i) 2 :=
  (rowStateData i).mapEquiv Natural.actionEquiv

/-- The shared literal-top normal registry, indexed however it chooses,
inherits the checked two-position quotient-socle family from the six-state
source registry by semantic completeness. -/
noncomputable def family :
    (Shared.top1.normalRegistry).QuotientSocleGeneratorFamily 2 where
  data := by
    intro i
    let N := Shared.top1.normalRegistry.state i
    letI : N.Normal := Shared.top1.normalRegistry.state_normal i
    obtain ⟨j, hj⟩ := topRegistry.complete N
    exact cast
      (congrArg
        (fun M : Subgroup Natural.Top ↦
          FiniteRelativeSocleGeneratorData Natural.Top M 2) hj)
      (topStateData j)

/-- Concrete row-1 Schur data.  The realization is arbitrary because both
finite inputs depend only on the literal top selected by the catalogue. -/
noncomputable def schurData
    {p : PreE7PairActionClass 8}
    {R : DegreeTwoPairTopRealization Shared.top1 p} :
    DegreeTwoPairTopSchurData Shared.top1 p R :=
  DegreeTwoPairTopSchurData.ofUniform 2 2 family (by
    change UniformSubrepresentationGeneratorBound Natural.representation 2
    exact Natural.uniform)

end DegreeTwoPairedEightRow1QuotientSocles
end PrimitiveAffineImprimitiveBlockTransfer
end Non2UnipotentPrefixFiniteMenu
end SymmetricSubgroupAsymptotics

end
