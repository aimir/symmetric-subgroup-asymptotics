import SymmetricSubgroupAsymptotics.SixPairFiveCycleAllNormalB6
import SymmetricSubgroupAsymptotics.BinaryPairFrameGenerators
import SymmetricSubgroupAsymptotics.DerivedGeneratorWords

/-! Thin actual-action witness for the primitive six-pair structural source.
Only original generators, their physical pair chart, two retained words,
and a six-coordinate polynomial equality are checked. -/
set_option autoImplicit false
noncomputable section
namespace SymmetricSubgroupAsymptotics
open BinarySixPointFiveCyclePolynomial

structure SixPairFiveCycleWordB6Witness {n : ℕ}
    (generators : Fin n → Equiv.Perm (Fin 12)) where
  points : Fin 6 × ZMod 2 ≃ Fin 12
  tops : Fin n → Equiv.Perm (Fin 6)
  preserves : ∀ i, BinaryPairFrame.Preserves points (generators i) (tops i)
  fiveCycleWord : List (Fin n)
  moverWord : List (Fin n)
  mover : Equiv.Perm (Fin 6)
  fiveCycle_eval : (fiveCycleWord.map tops).prod=SixPointFiveCyclePrimitive.cycle
  mover_eval : (moverWord.map tops).prod=mover
  moves : mover 5≠5
  matrix : ∀ i x : Fin 6,
    actualOperator representation SixPointFiveCyclePrimitive.cycle mover (Pi.single i 1) x=
      operator 0 (Pi.single i 1) x

namespace SixPairFiveCycleWordB6Witness
variable {n : ℕ} {generators : Fin n → Equiv.Perm (Fin 12)}
  (W : SixPairFiveCycleWordB6Witness generators)

def frame : BinaryPairFrame (Subgroup.closure (Set.range generators)) (Fin 6) :=
  BinaryPairFrame.ofGenerators W.points generators W.tops W.preserves

def evalWord (_W : SixPairFiveCycleWordB6Witness generators) (w : List (Fin n)) : Subgroup.closure (Set.range generators) :=
  (w.map (closureGenerators generators)).prod

private theorem word_top (w : List (Fin n)) :
    W.frame.top (W.evalWord w)=(w.map W.tops).prod := by
  have hg (i : Fin n) : W.frame.top (closureGenerators generators i)=W.tops i :=
    BinaryPairFrame.ofGenerators_top_generator _ _ _ W.preserves i
  induction w with
  | nil => exact map_one W.frame.top
  | cons i w ih =>
    change W.frame.top (closureGenerators generators i * W.evalWord w)=_
    rw [map_mul,hg,ih]
    rfl

/-- Every original normal quotient is handled by the structural theorem. -/
def actionCertificate (h6 : PublishedPrimitiveDegreeSixClassification)
    (hZmud : ZmudFaithfulCharacterTupleInput) :
    Non2UnipotentPrefixFiniteMenu.PreE7B6ActionCertificate
      (Subgroup.closure (Set.range generators)) :=
  SixPairFiveCycleAllNormalB6.actionCertificate W.frame h6 hZmud
    (W.evalWord W.fiveCycleWord) (W.evalWord W.moverWord) W.mover
    ((W.word_top _).trans W.fiveCycle_eval) ((W.word_top _).trans W.mover_eval)
    W.moves W.matrix

end SixPairFiveCycleWordB6Witness
end SymmetricSubgroupAsymptotics
