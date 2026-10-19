import SymmetricSubgroupAsymptotics.NoTernaryQuotientFourthPowerWords
import SymmetricSubgroupAsymptotics.PrimitiveAffineDegreeTwoTwelvePairFiniteCatalogueRows151To200
set_option autoImplicit false
noncomputable section
namespace SymmetricSubgroupAsymptotics.QuarterTurnTwoOriginalNoTernary
open Non2UnipotentPrefixFiniteMenu.PrimitiveAffineImprimitiveBlockTransfer
open DegreeTwoTwelvePairFiniteCatalogue
private def words162 : Fin 5 → DerivedGeneratorWord (Fin 5) :=
  ![.one,.one,.mul (.comm 2 3) (.comm 2 3),.one,.one]
private def words199 : Fin 4 → DerivedGeneratorWord (Fin 4) :=
  ![.one,.mul (.comm 1 2) (.comm 1 2),.one,.one]

theorem row162 : NoTernaryQuotient row162Interface.top :=
  NoTernaryQuotientFourthPowerWords.of_generators (closureGenerators row162Generators)
    (closureGenerators_full _) words162 (by intro i; apply Subtype.ext; revert i; decide +kernel)
theorem row199 : NoTernaryQuotient row199Interface.top :=
  NoTernaryQuotientFourthPowerWords.of_generators (closureGenerators row199Generators)
    (closureGenerators_full _) words199 (by intro i; apply Subtype.ext; revert i; decide +kernel)
end SymmetricSubgroupAsymptotics.QuarterTurnTwoOriginalNoTernary
