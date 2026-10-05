import SymmetricSubgroupAsymptotics.PrimitiveAffineDegreeTwoSixPairAction001Normals
import SymmetricSubgroupAsymptotics.PrimitiveAffineDegreeTwoSixPairSelectedWitness
import SymmetricSubgroupAsymptotics.FiniteConjugacyCentralizerCoordinateTransport
import SymmetricSubgroupAsymptotics.FiniteNormalJoinWordRegistryTransport

/-!
# Selected six-pair action 1: literal physical witness

This file is the small checked adapter from the executable row certificates
to the literal twelve-point permutation subgroup.  It retains the adjacent
pair system of the selected action, and transports both the reversible
centralizer coordinates and the normal-join registry across the checked
Cayley equivalence.
-/

set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 0
noncomputable section

namespace SymmetricSubgroupAsymptotics.PrimitiveAffineDegreeTwoSixPairAction001Witness

local instance selectedSourceGroup : Group PrimitiveAffineDegreeTwoSixPairAction001ClassPilot.Source := PrimitiveAffineDegreeTwoSixPairAction001ClassPilot.group

abbrev Original : Subgroup (Equiv.Perm (Fin 12)) :=
  Subgroup.closure (Set.range PrimitiveAffineDegreeTwoSixPairAction001ClassPilot.generators)

/-- The original selected action preserves the six adjacent pairs. -/
def frame : Fin 6 × ZMod 2 ≃ Fin 12 :=
  (Equiv.prodCongr (Equiv.refl (Fin 6))
    (ZMod.finEquiv 2).symm.toEquiv).trans finProdFinEquiv

private theorem frame_checked : ∀ i : Fin 12, ∀ p : Fin 6 × ZMod 2,
    (frame.symm
      (finFunctionFinEquiv.symm (PrimitiveAffineDegreeTwoSixPairAction001ClassPilot.certificate.rows i) (frame p))).1 =
        PrimitiveAffineDegreeTwoSixPairAction001ClassPilot.pairTop (⟨i⟩ : PrimitiveAffineDegreeTwoSixPairAction001ClassPilot.Source) p.1 := by
  native_decide

/-- Literal binary pair frame on the selected twelve-point subgroup. -/
def pairFrame : BinaryPairFrame Original (Fin 6) :=
  BinaryPairFrame.ofEquiv PrimitiveAffineDegreeTwoSixPairAction001ClassPilot.originalEquiv PrimitiveAffineDegreeTwoSixPairAction001ClassPilot.pairTop frame (by
    intro u p
    change (frame.symm
      (PrimitiveAffineDegreeTwoSixPairAction001ClassPilot.certificate.toCayley.elements u.index (frame p))).1 =
        PrimitiveAffineDegreeTwoSixPairAction001ClassPilot.pairTop u p.1
    rw [binaryPair_source_row_apply]
    exact frame_checked u.index p)

def ambient (j : Fin 3) : Original :=
  PrimitiveAffineDegreeTwoSixPairAction001ClassPilot.originalEquiv (PrimitiveAffineDegreeTwoSixPairAction001ClassPilot.ambient j)

def representative (i : Fin 6) : Original :=
  PrimitiveAffineDegreeTwoSixPairAction001ClassPilot.originalEquiv (PrimitiveAffineDegreeTwoSixPairAction001ClassPilot.representative i)

def stateGenerators (i : Fin 7) (j : Fin 3) : Original :=
  PrimitiveAffineDegreeTwoSixPairAction001ClassPilot.originalEquiv (PrimitiveAffineDegreeTwoSixPairAction001Normals.stateGenerators i j)

/-- Reversible centralizer coordinates transported to the literal
permutation subgroup. -/
noncomputable def conjugacy :
    FiniteConjugacyCentralizerCoordinateChunk representative 6 :=
  PrimitiveAffineDegreeTwoSixPairAction001ClassPilot.conjugacyChunk.mapEquiv PrimitiveAffineDegreeTwoSixPairAction001ClassPilot.originalEquiv

/-- The complete normal-join registry transported to the same literal
permutation subgroup and the same literal class cover. -/
noncomputable def normalRegistry : FiniteNormalJoinWordRegistryData
    conjugacy.toCardinalCover ambient stateGenerators :=
  PrimitiveAffineDegreeTwoSixPairAction001Normals.normalRegistry.mapEquiv PrimitiveAffineDegreeTwoSixPairAction001ClassPilot.originalEquiv
    conjugacy.toCardinalCover

private theorem row_centralizer_top (i : Fin 6) :
    (PrimitiveAffineDegreeTwoSixPairAction001ClassPilot.conjugacyChunk.centralizer i).top =
      PrimitiveAffineDegreeTwoSixPairAction001ClassPilot.pairTop.comp
        (Subgroup.centralizer
          ({PrimitiveAffineDegreeTwoSixPairAction001ClassPilot.representative i} :
            Set PrimitiveAffineDegreeTwoSixPairAction001ClassPilot.Source)).subtype := by
  fin_cases i <;> rfl

private theorem centralizer_top (i : Fin 6) :
    (conjugacy.centralizer i).top =
      pairFrame.top.comp
        (Subgroup.centralizer
          ({representative i} : Set Original)).subtype := by
  apply MonoidHom.ext
  intro x
  simp only [conjugacy,
    FiniteConjugacyCentralizerCoordinateChunk.mapEquiv,
    FinitePairCentralizerCoordinateCertificate.mapCentralizerEquiv,
    pairFrame, BinaryPairFrame.ofEquiv, representative,
    centralizerSingletonMulEquiv]
  rw [row_centralizer_top]
  rfl

/-- Full selected witness for action 1, now living on the actual original
twelve-point subgroup. -/
noncomputable def selectedWitness :
    PrimitiveAffineDegreeTwoSixPairSelectedWitness
      Original ambient representative stateGenerators where
  pairFrame := pairFrame
  conjugacy := conjugacy
  centralizer_top := centralizer_top
  normalRegistry := normalRegistry

/-- Every literal normal subgroup of the original selected action is one of
the seven transported generated states. -/
theorem normal_complete (N : Subgroup Original) [N.Normal] :
    ∃ i, Subgroup.closure (Set.range (stateGenerators i)) = N :=
  selectedWitness.normal_complete N

end SymmetricSubgroupAsymptotics.PrimitiveAffineDegreeTwoSixPairAction001Witness

end
