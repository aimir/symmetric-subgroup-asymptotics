import SymmetricSubgroupAsymptotics.CFSGSignedCartanReflections
import SymmetricSubgroupAsymptotics.CFSGSerreConcreteDiagrams

/-! The prefix roots of the two literal folded descent words lie in the
nonnegative cones on their indicated simple nodes. These are bounded
integer matrix certificates: three and six prefixes in dimension six.
No root-system or Weyl-group elements are enumerated. -/
set_option autoImplicit false
set_option Elab.async false
namespace SymmetricSubgroupAsymptotics.CFSGReeFFourPairedDescentPrefixes
open scoped Matrix
open CFSGSignedCartanReflections

def pairedWord (middle : Bool) : List (Fin 6) :=
  if middle then [2,4,3,2,4,3] else [0,5,1]

def pairedSupport (middle : Bool) : List (Fin 6) :=
  if middle then [2,3,4] else [0,1,5]

def prefixVector (middle : Bool) (n : Fin (pairedWord middle).length) : Fin 6→ℤ :=
  latticeWord CartanMatrix.E₆ ((pairedWord middle).take n.val)*ᵥ
    Pi.single ((pairedWord middle).get n) 1

theorem paired_prefix_nonnegative :
    ∀middle n j,0≤prefixVector middle n j := by
  decide

theorem paired_prefix_supported :
    ∀middle n j,j∉pairedSupport middle→prefixVector middle n j=0 := by
  decide

end SymmetricSubgroupAsymptotics.CFSGReeFFourPairedDescentPrefixes
