import SymmetricSubgroupAsymptotics.SixPairB6ElementaryCubic
import SymmetricSubgroupAsymptotics.PrimitiveAffineDegreeTwoSixPairGeneralSourceAssembly

/-! The complete elementary-binary-by-C3 structural class enters the exact
representative-facing source assembly. The actual cubic map and original
kernel exponent construct all quotient coordinates; no normal registry,
module chart, scalar nonvanishing, or source inequality is supplied. -/
set_option autoImplicit false
noncomputable section
open scoped Classical
namespace SymmetricSubgroupAsymptotics.SixPairElementaryCubicRepresentativeSource
open Non2UnipotentPrefixFiniteMenu

/-- Every normal axis of the SAME original action is certified. -/
def source (p : PreE7PairActionClass 6)
    [MulAction.IsPretransitive (preE7PairAction 6 p) (Fin 12)]
    (F : BinaryPairFrame (preE7PairAction 6 p) (Fin 6))
    (top : preE7PairAction 6 p →* CyclicThree) (htop : Function.Surjective top)
    (hkernel : ∀ k : top.ker,k^2=1) (hKP : KovacsPraegerAbelianizationBound) :
    PreE7RankTailSourceOrYonedaTopData 12 (preE7SixPairNonPairAction p) :=
  .inl (.b6 (SixPairB6ElementaryCubic.actionCertificate F top htop hkernel hKP))

/-- A structural existence proof suffices; no selected generator list or
finite catalogue index is required to build this actual source. -/
def source_of_exists (p : PreE7PairActionClass 6)
    [MulAction.IsPretransitive (preE7PairAction 6 p) (Fin 12)]
    (F : BinaryPairFrame (preE7PairAction 6 p) (Fin 6))
    (h : ∃ top : preE7PairAction 6 p →* CyclicThree,
      Function.Surjective top ∧ ∀ k : top.ker,k^2=1)
    (hKP : KovacsPraegerAbelianizationBound) :
    PreE7RankTailSourceOrYonedaTopData 12 (preE7SixPairNonPairAction p) :=
  source p F (Classical.choose h) (Classical.choose_spec h).1 (Classical.choose_spec h).2 hKP

end SymmetricSubgroupAsymptotics.SixPairElementaryCubicRepresentativeSource
