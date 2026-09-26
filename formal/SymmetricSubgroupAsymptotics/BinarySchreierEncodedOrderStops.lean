import SymmetricSubgroupAsymptotics.BinarySchreierPrunedAdapter
import SymmetricSubgroupAsymptotics.FiniteEncodedOrderBound
import SymmetricSubgroupAsymptotics.FinitePermutationEncoding

/-! Original-action order stops from finite encoded closure bounds.
The row certificate is tied to the exact original generator tuple. An
upper bound needs no row injectivity, parent words or declared group order.
-/
set_option autoImplicit false
noncomputable section

namespace SymmetricSubgroupAsymptotics.BinarySchreierPrunedBinding

variable {w cap n k : ℕ} {I : Type*}
    {actions : I → Subgroup (Equiv.Perm (Fin w))} {i : I}

/-- A finite transition-closed set of faithful codes supplies the actual
order bound needed by the boundary constructor. -/
def ofEncodedOrderBound (generators : Fin k → Equiv.Perm (Fin w))
    (C : EncodedOrderBoundCertificate (permutationGeneratorEncoding generators) n)
    (hsource : actions i = Subgroup.closure (Set.range generators))
    (hsize : n ≤ 2*cap) : BinarySchreierPrunedBinding actions cap i :=
  .boundary (by
    rw [hsource]
    exact C.card_closure_le.trans hsize)

/-- Existing stronger certificates feed the same consumer; their parent
and reachability fields are unnecessary for this one-sided bound. -/
def ofEncodedCayley (generators : Fin k → Equiv.Perm (Fin w))
    (C : EncodedCayleyCertificate (permutationGeneratorEncoding generators) n)
    (hsource : actions i = Subgroup.closure (Set.range generators))
    (hsize : n ≤ 2*cap) : BinarySchreierPrunedBinding actions cap i :=
  ofEncodedOrderBound generators C.toOrderBound hsource hsize

end SymmetricSubgroupAsymptotics.BinarySchreierPrunedBinding
