import SymmetricSubgroupAsymptotics.BinaryNormalTransport16
import SymmetricSubgroupAsymptotics.BinaryExceptional16Proper

/-!
# The reversible 16T1086 carrier enters the cyclic-four owner

The exceptional carrier has four physical blocks.  Its first restriction is
the literal transitive cyclic group of order four.  Fullness of the original
fusion source passes first to the complete proper carrier and then onto this
block.  Thus the reversible alternative has positive noncritical physical
support; it is not a zero-motion quotient comparison.
-/

set_option autoImplicit false
noncomputable section

namespace SymmetricSubgroupAsymptotics.BinaryExceptional16CyclicOwner

open BinaryNormalTransport16T1086
open BinaryPairBinding16T1086

abbrev CyclicBlock : Subgroup (Equiv.Perm (Fin 4)) :=
  Subgroup.closure (Set.range BinaryChart16T1086.block0BaseGenerators)

theorem cyclicBlock_card : Nat.card CyclicBlock=4 :=
  BinaryChart16T1086.block0_base_card

instance cyclicBlock_isCyclic : IsCyclic CyclicBlock :=
  subgroup_closure_single_generator_isCyclic BinaryChart16T1086.block0BaseGenerators

/-- Restrict the transported subgroup to the literal first carrier block.
The codomain is the exact generated C4, rather than an abstract isomorphic
copy. -/
def transportCyclicBlock {E : Type*} [Group E]
    (H : Subgroup (chart.source×E)) : chart.transport H →* CyclicBlock :=
  let raw : chart.transport H →* Equiv.Perm (Fin 4) :=
    BinaryChart16T1086.block0.hom.comp
      ((MonoidHom.fst chart.carrier E).comp (chart.transport H).subtype)
  raw.codRestrict CyclicBlock (fun z => by
    change BinaryChart16T1086.block0.hom z.1.1∈
      Subgroup.closure (Set.range BinaryChart16T1086.block0BaseGenerators)
    rw [← BinaryChart16T1086.block0_range]
    exact ⟨z.1.1,rfl⟩)

/-- Reversible transport of a full original source is full on the entire
literal C4 block, even though the carrier is a proper nonabelian subdirect
subgroup of the displayed four-block product. -/
theorem transportCyclicBlock_surjective {E : Type*} [Group E]
    (H : Subgroup (chart.source×E))
    (hfull : ∀ x : chart.source, ∃ e : E, (x,e)∈H) :
    Function.Surjective (transportCyclicBlock H) := by
  intro u
  have hu : (u : Equiv.Perm (Fin 4))∈BinaryChart16T1086.block0.hom.range := by
    rw [BinaryChart16T1086.block0_range]
    exact u.property
  obtain ⟨y,hy⟩ := hu
  obtain ⟨e,he⟩ := chart.transport_full_carrier H hfull y
  refine ⟨⟨(y,e),he⟩,?_⟩
  apply Subtype.ext
  exact hy

/-- The cyclic block occupies one quarter of the physical carrier width. -/
theorem cyclicBlock_quarter : 16=4*Fintype.card (Fin 4) := by
  decide

/-- Self-contained analytic owner data for the exceptional original axis.
The two equalities enable reversible reconstruction; `cyclic_full` is the
positive physical motion that sends every transported exterior correlation
to the already counted cyclic-four sector. -/
structure AxisOwner (N : Subgroup Original) : Prop where
  source_eq : chart.source=Original
  axis_eq : chart.axis=N.map Original.subtype
  cyclic_full : ∀ {E : Type} [Group E]
    (H : Subgroup (chart.source×E)),
    (∀ x : chart.source, ∃ e : E, (x,e)∈H) →
      Function.Surjective (transportCyclicBlock H)

def AxisOwner.ofEqualities {N : Subgroup Original}
    (hs : chart.source=Original) (ha : chart.axis=N.map Original.subtype) :
    AxisOwner N where
  source_eq := hs
  axis_eq := ha
  cyclic_full := fun H hfull => transportCyclicBlock_surjective H hfull

end SymmetricSubgroupAsymptotics.BinaryExceptional16CyclicOwner
