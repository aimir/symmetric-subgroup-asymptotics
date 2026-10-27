import SymmetricSubgroupAsymptotics.PermutationalWreathProduct
import Mathlib.SetTheory.Cardinal.Finite

set_option autoImplicit false
namespace SymmetricSubgroupAsymptotics
instance finitePermutationalWreath {R Q I : Type} [Group R] [Group Q] [MulAction Q I]
    [Finite R] [Finite Q] [Finite I] : Finite (PermutationalWreathProduct R Q I) :=
  Finite.of_injective (fun w : PermutationalWreathProduct R Q I => (w.left,w.right))
    (by
      intro a b h
      apply PermutationalWreathProduct.ext
      · exact congrArg Prod.fst h
      · exact congrArg Prod.snd h)
end SymmetricSubgroupAsymptotics
