import SymmetricSubgroupAsymptotics.DistinctDiagonalFullCoordinateModule
import SymmetricSubgroupAsymptotics.PrimitiveAffineDegreeThreeFourBlockSignedIsotypeSplit
import SymmetricSubgroupAsymptotics.PrimitiveAffineDegreeThreeFourBlockTranslationCoordinates
import SymmetricSubgroupAsymptotics.PrimitiveAffineDegreeThreeLocalScalar

/-!
# Literal signed action on the four-block translation submodule

This file states the one exact compatibility identity still needed between
the two already constructed literal objects:

* the four-pair frame of the signed quotient `U / E`; and
* the correlated translation submodule `E ≤ V⁴`.

The scalar at a coordinate is defined from that pair frame's actual flip
bit.  The compatibility record says only that quotient conjugation on the
actual translation submodule is the corresponding diagonal scalar action.
It does not assert a marker embedding and it does not enlarge the correlated
submodule to the full product.

Once this identity is available, the four distinct-sign branch is formal:
coordinatewise surjectivity comes from the literal block action, distinct
characters isolate the four coordinates, and the correlated submodule is
therefore the whole local product.
-/

set_option autoImplicit false
noncomputable section
open scoped Classical

namespace SymmetricSubgroupAsymptotics

/-- Reindex a function module along an equivalence of its literal
coordinates. -/
def coordinateLinearEquiv
    {k I J V : Type*} [Semiring k] [AddCommMonoid V] [Module k V]
    (e : I ≃ J) : (I → V) ≃ₗ[k] (J → V) where
  toFun v j := v (e.symm j)
  invFun v i := v (e i)
  map_add' _ _ := rfl
  map_smul' _ _ := rfl
  left_inv v := by
    funext i
    simp
  right_inv v := by
    funext j
    simp

namespace Non2UnipotentPrefixFiniteMenu
namespace PrimitiveAffineImprimitiveBlockTransfer

open OddMarkerTernaryChart

variable {w : ℕ} {U : PreE7NonPairActionClass w}
  {basePoint : Fin w}
  (block : OriginalMinimalBlock
    (A := preE7NonPairAction w U) basePoint)
  (P : PrimitiveAffineProfile block.Component block.Fibre)
  [Nontrivial block.Fibre]

local instance : Fact P.p.Prime := (chart block P).primeFact

/-- The block relabelling already used by the fixed four-pair chart. -/
noncomputable def degreeThreeFourBlockIndexEquiv
    (hs : Nat.card block.Points = 4) : block.Points ≃ Fin 4 :=
  Finite.equivFinOfCardEq hs

/-- The original correlated translation submodule with only its four block
labels changed. -/
noncomputable def degreeThreeFourBlockReindexedTranslationSubmodule
    (hs : Nat.card block.Points = 4) :
    Submodule (ZMod P.p) (Fin 4 → (chart block P).V) :=
  (TranslationSubmodule block P).map
    (coordinateLinearEquiv (k := ZMod P.p)
      (degreeThreeFourBlockIndexEquiv block hs)).toLinearMap

/-- The literal diagonal scalar attached to one actual pair-frame bit. -/
noncomputable def degreeThreeFourBlockTranslationScalar
    (hr : Nat.card block.Fibre = 3)
    (hs : Nat.card block.Points = 4)
    (hcomponent : Nat.card block.Component = 6)
    (i : Fin 4)
    (k : (degreeThreeFourBlockPairChart
      block P hr hs hcomponent).frame.top.ker) : ZMod P.p :=
  (degreeThreeScalarFieldEquiv block P hr).symm
    (signScalar (Multiplicative.ofAdd
      ((degreeThreeFourBlockPairChart
        block P hr hs hcomponent).frame.bits k i)))

/-- Equality of actual pair characters is exactly equality of the transported
ternary scalar characters. -/
theorem degreeThreeFourBlockTranslationScalar_injective
    (hr : Nat.card block.Fibre = 3)
    (hs : Nat.card block.Points = 4)
    (hcomponent : Nat.card block.Component = 6)
    (hsign : Function.Injective
      (BinaryPairFrame.fourCoordinateSign
        (degreeThreeFourBlockPairChart
          block P hr hs hcomponent).frame)) :
    Function.Injective
      (degreeThreeFourBlockTranslationScalar
        block P hr hs hcomponent) := by
  let C := degreeThreeFourBlockPairChart block P hr hs hcomponent
  intro i j hij
  apply hsign
  apply Subtype.ext
  funext k
  have hk := congrFun hij k
  have hsignScalar :
      signScalar (Multiplicative.ofAdd (C.frame.bits k i)) =
        signScalar (Multiplicative.ofAdd (C.frame.bits k j)) := by
    have := congrArg (degreeThreeScalarFieldEquiv block P hr) hk
    simpa only [degreeThreeFourBlockTranslationScalar,
      RingEquiv.apply_symm_apply, C] using this
  exact congrArg Multiplicative.toAdd
    (signScalar_injective hsignScalar)

/-- The exact remaining action-theoretic identity.  It compares quotient
conjugation on the actual bundled translation submodule with the diagonal
action read from the same literal four-pair frame. -/
structure DegreeThreeFourBlockSignedTranslationCompatibility
    (hr : Nat.card block.Fibre = 3)
    (hs : Nat.card block.Points = 4)
    (hcomponent : Nat.card block.Component = 6) : Prop where
  diagonal_action :
    let C := degreeThreeFourBlockPairChart block P hr hs hcomponent
    let e := degreeThreeFourBlockIndexEquiv block hs
    ∀ (k : C.frame.top.ker) (v : TranslationSubmodule block P),
      coordinateLinearEquiv (k := ZMod P.p) e
          (((elementaryChart block P).quotientRepresentation.ρ
            (C.sourceEquiv.symm k.1) v).1) =
        DiagonalInvariantSubmodules.diagonalModuleOperator
          (degreeThreeFourBlockTranslationScalar
            block P hr hs hcomponent) k
          (coordinateLinearEquiv (k := ZMod P.p) e v.1)

namespace DegreeThreeFourBlockSignedTranslationCompatibility

variable
  {hr : Nat.card block.Fibre = 3}
  {hs : Nat.card block.Points = 4}
  {hcomponent : Nat.card block.Component = 6}
  (A : DegreeThreeFourBlockSignedTranslationCompatibility
    block P hr hs hcomponent)

/-- The reindexed correlated translation submodule is stable under all four
literal diagonal characters. -/
noncomputable def stable :
    DiagonalInvariantSubmodules.ModuleStable (V := (chart block P).V)
      (degreeThreeFourBlockTranslationScalar
        block P hr hs hcomponent) := by
  let C := degreeThreeFourBlockPairChart block P hr hs hcomponent
  let e := degreeThreeFourBlockIndexEquiv block hs
  let K := degreeThreeFourBlockReindexedTranslationSubmodule block P hs
  refine ⟨K, ?_⟩
  intro k x hx
  rcases hx with ⟨v, hv, rfl⟩
  let t : TranslationSubmodule block P := ⟨v, hv⟩
  let t' : TranslationSubmodule block P :=
    (elementaryChart block P).quotientRepresentation.ρ
      (C.sourceEquiv.symm k.1) t
  refine ⟨t'.1, t'.2, ?_⟩
  simpa only [C, e, t, t'] using A.diagonal_action k t

/-- The reindexed translation submodule projects onto every local
translation coordinate. -/
theorem fullCoordinates
    (hbinary : IsPGroup 2
      (degreeThreeFourBlockPairChart
        block P hr hs hcomponent).action) :
    DiagonalInvariantSubmodules.ModuleFullCoordinates
      (degreeThreeFourBlockReindexedTranslationSubmodule block P hs) := by
  let e := degreeThreeFourBlockIndexEquiv block hs
  have hsurjective :=
    degreeThreeFourBlock_translationSubmodule_fullCoordinates
      block P hr hs hcomponent hbinary
  intro j z
  obtain ⟨g, hg⟩ := hsurjective (e.symm j) (Multiplicative.ofAdd z)
  let t : TranslationSubmodule block P :=
    translationAddEquiv block P (Additive.ofMul g)
  let y : Fin 4 → (chart block P).V :=
    coordinateLinearEquiv (k := ZMod P.p) e t.1
  have hy : y ∈ degreeThreeFourBlockReindexedTranslationSubmodule
      block P hs := by
    exact ⟨t.1, t.2, rfl⟩
  refine ⟨⟨y, hy⟩, ?_⟩
  change (coordinate block P (e.symm j) g).toAdd = z
  exact congrArg Multiplicative.toAdd hg

include A
/-- In the four-character branch, the literal correlated translation
submodule is the whole four-coordinate product. -/
theorem reindexedTranslationSubmodule_eq_top_of_fourSigns
    (hbinary : IsPGroup 2
      (degreeThreeFourBlockPairChart
        block P hr hs hcomponent).action)
    (hfour :
      (degreeThreeFourBlockSignedIsotypeProfile
        block P hr hs hcomponent).isotypeCount = 4) :
    degreeThreeFourBlockReindexedTranslationSubmodule block P hs = ⊤ := by
  let C := degreeThreeFourBlockPairChart block P hr hs hcomponent
  have hsign :=
    degreeThreeFourBlockSignedIsotype_injective_of_count_eq_four
      block P hr hs hcomponent hfour
  exact DiagonalInvariantSubmodules.eq_top_of_moduleFullCoordinates_of_injective
    (degreeThreeFourBlockTranslationScalar block P hr hs hcomponent)
    (degreeThreeFourBlockTranslationScalar_injective
      block P hr hs hcomponent hsign)
    (stable (block := block) (P := P) A)
    (fullCoordinates (block := block) (P := P) hbinary)

end DegreeThreeFourBlockSignedTranslationCompatibility

end PrimitiveAffineImprimitiveBlockTransfer
end Non2UnipotentPrefixFiniteMenu
end SymmetricSubgroupAsymptotics

end
