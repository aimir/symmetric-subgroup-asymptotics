import SymmetricSubgroupAsymptotics.PrimitiveAffineDegreeTwoQuotientEnvelopeTransport

/-!
# A raw pair envelope with its retained comparator action

The source-summed envelope keeps the complete quotient moment of a hidden
finite comparator `R`.  An affine layer can be prepended only if the faithful
permutation action of that same `R` is retained as well.  This small wrapper
keeps those two pieces together before any physical-width numerical margin
is chosen.
-/

set_option autoImplicit false
noncomputable section

namespace SymmetricSubgroupAsymptotics
namespace Non2UnipotentPrefixFiniteMenu

/-- A literal complete-quotient envelope together with a faithful action of
its retained comparator.  There is deliberately no physical-width margin in
this record. -/
structure PreE7DegreeTwoPairQuotientSummedPackage
    (Q : Type) [Group Q] [Finite Q] : Type 1 where
  envelope : PreE7DegreeTwoPairQuotientSummedEnvelope Q
  v : ℕ
  action : envelope.R →* Equiv.Perm (Fin v)
  action_injective : Function.Injective action

namespace PreE7DegreeTwoPairQuotientSummedPackage

/-- Pull a packaged row back along a literal target equivalence.  The target
envelope is transported, while its comparator and faithful action are kept
unchanged. -/
noncomputable def comapEquiv
    {Q Q' : Type} [Group Q] [Finite Q] [Group Q'] [Finite Q']
    (e : Q ≃* Q')
    (S : PreE7DegreeTwoPairQuotientSummedPackage Q') :
    PreE7DegreeTwoPairQuotientSummedPackage Q where
  envelope := S.envelope.comapEquiv e
  v := S.v
  action := S.action
  action_injective := S.action_injective

end PreE7DegreeTwoPairQuotientSummedPackage
end Non2UnipotentPrefixFiniteMenu
end SymmetricSubgroupAsymptotics

end
