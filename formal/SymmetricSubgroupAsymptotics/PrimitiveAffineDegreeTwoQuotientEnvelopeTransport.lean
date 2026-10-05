import SymmetricSubgroupAsymptotics.PrimitiveAffineDegreeTwoPairSummedSource
import SymmetricSubgroupAsymptotics.FusionEpimorphismTransport

/-!
# Transport of raw complete-quotient envelopes

The ternary affine prepend reaches a literal signed quotient, rather than a
member of the retained non-pair action index.  A published small-action row
therefore has to be transported to that literal quotient before any physical
pointing.  This file proves the required action-free transport through an
actual group equivalence.  It changes neither the comparator nor any
coefficient.
-/

set_option autoImplicit false
noncomputable section
open scoped BigOperators Classical

namespace SymmetricSubgroupAsymptotics
namespace Non2UnipotentPrefixFiniteMenu

attribute [-instance] originalNormalFintype

/-- Normal subgroups, including their normality witnesses, transport
bijectively through a group equivalence. -/
private def normalAxisMapEquiv
    {Q Q' : Type} [Group Q] [Group Q'] (e : Q ≃* Q') :
    {N : Subgroup Q // N.Normal} ≃
      {N : Subgroup Q' // N.Normal} where
  toFun N := ⟨N.1.map e.toMonoidHom,
    N.2.map e.toMonoidHom e.surjective⟩
  invFun N := ⟨N.1.comap e.toMonoidHom,
    Subgroup.Normal.comap N.2 e.toMonoidHom⟩
  left_inv N := Subtype.ext
    (Subgroup.comap_map_eq_self_of_injective e.injective N.1)
  right_inv N := Subtype.ext
    (Subgroup.map_comap_eq_self_of_surjective e.surjective N.1)

/-- The complete normal-quotient weight is invariant under an actual target
group equivalence.  In particular no action-index reclassification is
needed when the target is a signed quotient produced by an affine layer. -/
theorem completeQuotientWeight_congr
    {Q Q' : Type} [Group Q] [Finite Q] [Group Q'] [Finite Q']
    (e : Q ≃* Q') {b : ℕ}
    (J : Subgroup (Equiv.Perm (Fin b))) :
    completeQuotientWeight (R := Q) J =
      completeQuotientWeight (R := Q') J := by
  have hnat : completeQuotientCount (R := Q) J =
      completeQuotientCount (R := Q') J := by
    unfold completeQuotientCount
    apply Fintype.sum_equiv (normalAxisMapEquiv e)
    intro N
    let N' : Subgroup Q' := N.1.map e.toMonoidHom
    letI : N'.Normal := N.2.map e.toMonoidHom e.surjective
    exact fusionGroupEpimorphism_card_congr (MulEquiv.refl J)
      (QuotientGroup.congr N.1 N' e rfl)
  unfold completeQuotientWeight
  exact_mod_cast hnat

namespace PreE7DegreeTwoPairQuotientSummedEnvelope

/-- Pull a raw source-summed envelope back to a literal isomorphic target.
All raw rows, including a correlated exceptional term, remain unchanged. -/
noncomputable def comapEquiv
    {Q Q' : Type} [Group Q] [Finite Q] [Group Q'] [Finite Q']
    (e : Q ≃* Q')
    (S : PreE7DegreeTwoPairQuotientSummedEnvelope Q') :
    PreE7DegreeTwoPairQuotientSummedEnvelope Q where
  R := S.R
  mainCoefficient := S.mainCoefficient
  coldCoefficient := S.coldCoefficient
  eta := S.eta
  theta := S.theta
  mainCoefficient_nonneg := S.mainCoefficient_nonneg
  coldCoefficient_nonneg := S.coldCoefficient_nonneg
  exceptionalRaw := S.exceptionalRaw
  exceptionalRaw_nonneg := S.exceptionalRaw_nonneg
  summed := fun b => by
    have heq :
        (∑ J : Subgroup (Equiv.Perm (Fin b)),
          completeQuotientWeight (R := Q) J) =
        ∑ J : Subgroup (Equiv.Perm (Fin b)),
          completeQuotientWeight (R := Q') J := by
      apply Finset.sum_congr rfl
      intro J _
      exact completeQuotientWeight_congr e J
    rw [heq]
    exact S.summed b

end PreE7DegreeTwoPairQuotientSummedEnvelope
end Non2UnipotentPrefixFiniteMenu
end SymmetricSubgroupAsymptotics

end
