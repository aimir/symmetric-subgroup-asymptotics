import SymmetricSubgroupAsymptotics.SixteenPointMinimalBlockGeometry
import SymmetricSubgroupAsymptotics.BinaryPairFrameTransport

/-! Exhaustive original sixteen-point geometry with pair systems handled
first. Choosing an arbitrary minimal block alone would not exclude a second,
independent pair system. Here every size-four or size-eight branch retains
an actual proof that the original action admits no pair frame. -/

set_option autoImplicit false
noncomputable section
open scoped Classical

namespace SymmetricSubgroupAsymptotics

inductive SixteenPointPairFirstGeometry {X : Type} [Finite X]
    (T : Subgroup (Equiv.Perm X)) [MulAction.IsPretransitive T X] : Type 1 where
  | pair (frame : BinaryPairFrame T (Fin 8))
  | primitive (noPair : ¬Nonempty (BinaryPairFrame T (Fin 8)))
      (h : MulAction.IsPreprimitive T X)
  | four (noPair : ¬Nonempty (BinaryPairFrame T (Fin 8)))
      (x : X) (D : OriginalMinimalBlock (A := T) x)
      (fibre : Nat.card D.Fibre = 4) (points : Nat.card D.Points = 4)
  | eight (noPair : ¬Nonempty (BinaryPairFrame T (Fin 8)))
      (x : X) (D : OriginalMinimalBlock (A := T) x)
      (fibre : Nat.card D.Fibre = 8) (points : Nat.card D.Points = 2)

/-- Exhaustiveness is proved from the original action; no finite list or
named classification input stands in for this geometric dispatcher. -/
def sixteenPointPairFirstGeometry {X : Type} [Finite X]
    (T : Subgroup (Equiv.Perm X)) [MulAction.IsPretransitive T X]
    (hX : Nat.card X = 16) : SixteenPointPairFirstGeometry T := by
  by_cases hp : Nonempty (BinaryPairFrame T (Fin 8))
  · exact .pair (Classical.choice hp)
  cases sixteenPointMinimalBlockGeometry T hX with
  | primitive h => exact .primitive hp h
  | pair x D hr hs =>
      exact False.elim (hp ⟨(D.binaryPairFrame hr).reindex
        (Finite.equivFinOfCardEq hs)⟩)
  | four x D hr hs => exact .four hp x D hr hs
  | eight x D hr hs => exact .eight hp x D hr hs

end SymmetricSubgroupAsymptotics

end
