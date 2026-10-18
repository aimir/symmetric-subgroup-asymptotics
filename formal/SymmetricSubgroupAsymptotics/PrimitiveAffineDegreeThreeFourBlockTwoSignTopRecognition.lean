import SymmetricSubgroupAsymptotics.BinaryPairPreservingD8
import SymmetricSubgroupAsymptotics.PrimitiveAffineDegreeThreeFourBlockTwoSignTopFrame
import SymmetricSubgroupAsymptotics.PrimitiveAffineDegreeThreeFourBlockTwoSignProjectiveSeries

/-!
# Recognition of the order-eight two-sign top

The actual four-point top embeds into the full group preserving its literal
two-pair frame.  That full group has order at most eight and is canonically
identified with the displayed `D₈`.  Consequently an actual top of order
eight fills the full pair-preserving group, giving the required literal
isomorphism without a transitive-group catalogue.
-/

set_option autoImplicit false
noncomputable section
open scoped Classical

namespace SymmetricSubgroupAsymptotics
namespace BinaryPairFrame

variable {X : Type*} [Finite X] {H : Subgroup (Equiv.Perm X)}

/-- Forget the retained top coordinate while keeping the literal
pair-preserving certificate. -/
def pairPreservingEmbedding
    (D : BinaryPairFrame H (Fin 2)) :
    H →* pairPreserving D.frame where
  toFun h := ⟨h, ⟨D.top h, D.intertwine h⟩⟩
  map_one' := Subtype.ext rfl
  map_mul' _ _ := Subtype.ext rfl

theorem pairPreservingEmbedding_injective
    (D : BinaryPairFrame H (Fin 2)) :
    Function.Injective (pairPreservingEmbedding D) := by
  intro x y hxy
  apply Subtype.ext
  exact congrArg
    (fun z : pairPreserving D.frame => (z : Equiv.Perm X)) hxy

/-- An order-eight pair action is the full pair-preserving group. -/
noncomputable def pairPreservingEquivOfCardEight
    (D : BinaryPairFrame H (Fin 2))
    (hH : Nat.card H = 8) :
    H ≃* pairPreserving D.frame := by
  let f := pairPreservingEmbedding D
  have hf : Function.Injective f := pairPreservingEmbedding_injective D
  have hcard : Nat.card (pairPreserving D.frame) ≤ Nat.card H := by
    rw [hH]
    exact pairPreserving_card_le_eight D.frame
  exact MulEquiv.ofBijective f (hf.bijective_of_nat_card_le hcard)

/-- An order-eight pair action is the literal dihedral target used by the
fixed comparator. -/
noncomputable def topEquivD8OfCardEight
    (D : BinaryPairFrame H (Fin 2))
    (hH : Nat.card H = 8) :
    H ≃* DegreeSixS3Wreath.D8 :=
  (pairPreservingEquivOfCardEight D hH).trans
    (pairPreservingEquivD8 D.frame)

end BinaryPairFrame

namespace Non2UnipotentPrefixFiniteMenu
namespace PrimitiveAffineImprimitiveBlockTransfer

variable {w : ℕ} {U : PreE7NonPairActionClass w}
  {basePoint : Fin w}
  (block : OriginalMinimalBlock
    (A := preE7NonPairAction w U) basePoint)
  (P : PrimitiveAffineProfile block.Component block.Fibre)
  [Nontrivial block.Fibre]

/-- The literal order-eight projective top in the two-sign branch is the
dihedral two-pair group. -/
noncomputable def degreeThreeFourBlockTwoSign_topEquivD8_of_card_eight
    (hr : Nat.card block.Fibre = 3)
    (hs : Nat.card block.Points = 4)
    (hcomponent : Nat.card block.Component = 6)
    (htwo : (degreeThreeFourBlockSignedIsotypeProfile
      block P hr hs hcomponent).isotypeCount = 2)
    (htop : Nat.card (DegreeThreeFourBlockTwoSignProjectiveImage
      block P hr hs hcomponent) = 8) :
    DegreeThreeFourBlockTwoSignProjectiveImage
      block P hr hs hcomponent ≃* DegreeSixS3Wreath.D8 :=
  BinaryPairFrame.topEquivD8OfCardEight
    (degreeThreeFourBlockTwoSign_topPairFrame
      block P hr hs hcomponent htwo) htop

end PrimitiveAffineImprimitiveBlockTransfer
end Non2UnipotentPrefixFiniteMenu
end SymmetricSubgroupAsymptotics

end
