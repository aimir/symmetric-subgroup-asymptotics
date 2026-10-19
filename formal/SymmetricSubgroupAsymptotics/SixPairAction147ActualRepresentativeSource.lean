import SymmetricSubgroupAsymptotics.SixPairAction147PrimitiveB6Pilot
import SymmetricSubgroupAsymptotics.SixPairFiveCycleActualRepresentativeSource
import SymmetricSubgroupAsymptotics.FinitePointWordCertificate

/-! A twelve-point orbit-word certificate binds the primitive-six B6
construction to an actual pre-E7 representative, keeping the literal point
conjugacy. No normal registry or class locator is assumed. -/
set_option autoImplicit false
noncomputable section
namespace SymmetricSubgroupAsymptotics.SixPairAction147ActualRepresentativeSource
open Non2UnipotentPrefixFiniteMenu SixPairAction147PrimitiveB6Pilot

private def paths : Fin 12 → List (Fin 2) :=
  ![[], [1,0], [1,0,1,1], [1,1], [0,0], [0,0,0,1],
    [1,0,1], [1], [0], [1,0,0], [0,0,0], [1,1,1]]

private def pointWord (x : Fin 12) : FiniteGeneratorWord (Fin 2) :=
  (paths x).foldl (fun w i => .mul (.generator i) w) .one

def orbitCertificate : FinitePointWordCertificate generators where
  basePoint := 0
  words := pointWord
  reaches := by decide +kernel

theorem transitive : MulAction.IsPretransitive Original (Fin 12) :=
  orbitCertificate.pretransitive

theorem exists_source
    (h6 : PublishedPrimitiveDegreeSixClassification)
    (hZmud : ZmudFaithfulCharacterTupleInput) :
    ∃ p : PreE7PairActionClass 6, ∃ c : Equiv.Perm (Fin 12),
      relabelSubgroup c Original = preE7PairAction 6 p ∧
      Nonempty (PreE7B6SourceData 12 (preE7SixPairNonPairAction p)) :=
  SixPairFiveCycleActualRepresentativeSource.exists_actualRepresentativeSource
    witness h6 hZmud transitive

end SymmetricSubgroupAsymptotics.SixPairAction147ActualRepresentativeSource
end
