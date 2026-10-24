import SymmetricSubgroupAsymptotics.MinimalNormalIsotypicRelativeOrdinaryGenerators
import SymmetricSubgroupAsymptotics.SemisimpleSubdirectChart

/-! A normal subgroup of an ACTUAL homogeneous semisimple overgroup
inherits coordinates with their original simple-factor origins. This
makes the relative ordinary-generation theorem use the same original
simple group, not a merely equicardinal replacement. -/
set_option autoImplicit false
noncomputable section
open scoped Classical
namespace SymmetricSubgroupAsymptotics.NormalIsotypicCoordinateOrigins

variable {G T I : Type} [Group G] [Finite G] [Group T] [Finite T]
    [IsSimpleGroup T] [Fintype I]
    (N E : Subgroup G) [E.Normal] (hEN : E ≤ N)
    (eN : N ≃* (I → T)) (hT : IsCenterless T)

def ambientChart : SemisimpleNormalChart N where
  ι := I
  factor := fun _ => T
  simple := fun _ => inferInstance
  centerless := fun _ => hT
  equiv := eN

/-- Every coordinate is a literal original overgroup coordinate. Normality
makes its range either zero or the actual simple factor. -/
def origins : SemisimpleGroupChartOrigins E (Unit × I) (fun _ => T) := by
  let C := ambientChart N eN hT
  let f : Unit → E →* N := fun _ => Subgroup.inclusion hEN
  apply C.chartOfNormalCoordinateMapsOrigins f ?_ ?_
  · intro _ j
    let p : N →* T := (Pi.evalMonoidHom (fun _ : I => T) j).comp eN.toMonoidHom
    have hp : Function.Surjective p := by
      intro t
      refine ⟨eN.symm (Pi.mulSingle j t),?_⟩
      change eN (eN.symm (Pi.mulSingle j t)) j = t
      rw [eN.apply_symm_apply,Pi.mulSingle_eq_same]
    have hn : ((E.subgroupOf N).map p).Normal :=
      Subgroup.Normal.map (inferInstance : (E.subgroupOf N).Normal) p hp
    change ((p.comp (Subgroup.inclusion hEN)).range).Normal
    rw [MonoidHom.range_comp,Subgroup.inclusion_range]
    exact hn
  · intro x y hxy
    have hN : Subgroup.inclusion hEN x = Subgroup.inclusion hEN y := congrFun hxy ()
    have hG : x.val = y.val := congrArg (fun z : N => z.val) hN
    exact Subtype.ext hG

/-- A homogeneous chart of E using the retained equivalence to each
original T-coordinate; the origin object remains separately available. -/
def coordinates : E ≃* ((origins N E hEN eN hT).ι → T) :=
  (origins N E hEN eN hT).equiv.trans
    (MulEquiv.piCongrRight (origins N E hEN eN hT).factor_equiv)

theorem coordinates_apply (x : E) (j : (origins N E hEN eN hT).ι) :
    coordinates N E hEN eN hT x j =
      (origins N E hEN eN hT).factor_equiv j
        ((origins N E hEN eN hT).equiv x j) := rfl

theorem coordinates_nonempty (hE : E ≠ ⊥) :
    Nonempty (origins N E hEN eN hT).ι := by
  letI : Nontrivial E := E.nontrivial_iff_ne_bot.mpr hE
  obtain ⟨x,hx⟩ := exists_ne (1 : E)
  by_contra hn
  apply hx
  apply (coordinates N E hEN eN hT).injective
  funext j
  exact False.elim (hn ⟨j⟩)

include hEN eN hT in
theorem genRank_le_relative (hE : IsMinimalNormalSubgroup E) :
    MarkedC4.genRank G ≤ MarkedC4.genRank T+MarkedC4.genRank (G ⧸ E) := by
  let i := Classical.choice (coordinates_nonempty N E hEN eN hT hE.2.1)
  exact MinimalNormalIsotypicRelativeOrdinaryGenerators.genRank_le E
    (coordinates N E hEN eN hT) i hE

/-- The marked union is supported on one genuine retained factor and on
lifts from the SAME original quotientG/E. -/
theorem exists_marked_generators (hE : IsMinimalNormalSubgroup E) :
    ∃ i : (origins N E hEN eN hT).ι, ∃ s : Finset T, ∃ q : Finset (G ⧸ E),
      Subgroup.closure (s : Set T) = ⊤ ∧ s.card = MarkedC4.genRank T ∧
      Subgroup.closure (q : Set (G ⧸ E)) = ⊤ ∧ q.card = MarkedC4.genRank (G ⧸ E) ∧
      Subgroup.closure ((s.image
        (MinimalNormalIsotypicRelativeOrdinaryGenerators.axisHom E
          (coordinates N E hEN eN hT) i) ∪ q.image Quotient.out : Finset G) : Set G) = ⊤ := by
  let i := Classical.choice (coordinates_nonempty N E hEN eN hT hE.2.1)
  exact ⟨i,MinimalNormalIsotypicRelativeOrdinaryGenerators.exists_marked_generators E
    (coordinates N E hEN eN hT) i hE⟩

end SymmetricSubgroupAsymptotics.NormalIsotypicCoordinateOrigins
