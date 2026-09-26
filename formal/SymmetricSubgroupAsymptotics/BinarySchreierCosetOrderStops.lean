import SymmetricSubgroupAsymptotics.BinarySchreierPrunedAdapter
import SymmetricSubgroupAsymptotics.GeneratorCosetOrderBound

/-! Original-action order stops from a finite coset cover. The checked
right-generator defects may use any actual ambient subgroup. Neither a
normal quotient chart nor an enumeration of the whole source is required.
-/
set_option autoImplicit false
noncomputable section

namespace SymmetricSubgroupAsymptotics.BinarySchreierPrunedBinding

variable {w cap q k : ℕ} {I : Type*}
    {actions : I → Subgroup (Equiv.Perm (Fin w))} {i : I}

/-- A compressed cover of the exact original generated source installs
the same order boundary as a full row certificate. -/
def ofCosetOrderBound (generators : Fin k → Equiv.Perm (Fin w))
    (K : Subgroup (Equiv.Perm (Fin w)))
    (C : GeneratorCosetOrderBoundCertificate generators K q)
    (hsource : actions i = Subgroup.closure (Set.range generators))
    (hsize : q * Nat.card K ≤ 2*cap) : BinarySchreierPrunedBinding actions cap i :=
  .boundary (by
    rw [hsource]
    exact C.card_closure_le.trans hsize)

end SymmetricSubgroupAsymptotics.BinarySchreierPrunedBinding
