import SymmetricSubgroupAsymptotics.CFSGTwistedA2TraceFibers
import SymmetricSubgroupAsymptotics.CFSGTwistedA2UnipotentArrays

/-! Exact q^3 parameter chart of the literal upper-unipotent arrays.
The second parameter lies in a genuine trace fibre; a kernel translate,
not an assumed unitary-group order, gives its cardinality. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section

namespace SymmetricSubgroupAsymptotics.CFSGTwistedA2UnipotentParameters
open CFSGSerreOrdinaryTwists CFSGTwistedANaturalMatrices
open CFSGTwistedA2TraceFibers CFSGTwistedA2UnipotentArrays

abbrev Parameters (q : CFSG.PrimePower) :=
  {ab : q.Extension 2 × q.Extension 2 //
    NormCondition (definingFieldAutomorphism q 2) ab.1 ab.2}

def particular (q : CFSG.PrimePower) (hq : 3 ≤ q.order) (a : q.Extension 2) : q.Extension 2 :=
  Classical.choose (exists_trace_eq_norm q hq a)

theorem particular_spec (q : CFSG.PrimePower) (hq : 3 ≤ q.order) (a : q.Extension 2) :
    NormCondition (definingFieldAutomorphism q 2) a (particular q hq a) :=
  Classical.choose_spec (exists_trace_eq_norm q hq a)

def parameterEquiv (q : CFSG.PrimePower) (hq : 3 ≤ q.order) :
    (q.Extension 2 × (traceHom q).ker) ≃ Parameters q where
  toFun az := ⟨(az.1, particular q hq az.1 + az.2.val), by
    have hp := particular_spec q hq az.1
    have hz : az.2.val + definingFieldAutomorphism q 2 az.2.val = 0 := az.2.property
    change particular q hq az.1 + definingFieldAutomorphism q 2 (particular q hq az.1) =
      az.1 * definingFieldAutomorphism q 2 az.1 at hp
    change particular q hq az.1 + az.2.val +
      definingFieldAutomorphism q 2 (particular q hq az.1 + az.2.val) = _
    rw [map_add]
    linear_combination hp + hz⟩
  invFun ab := (ab.val.1, ⟨ab.val.2 - particular q hq ab.val.1, by
    have hp := particular_spec q hq ab.val.1
    have hab := ab.property
    change particular q hq ab.val.1 + definingFieldAutomorphism q 2 (particular q hq ab.val.1) =
      ab.val.1 * definingFieldAutomorphism q 2 ab.val.1 at hp
    change ab.val.2 + definingFieldAutomorphism q 2 ab.val.2 =
      ab.val.1 * definingFieldAutomorphism q 2 ab.val.1 at hab
    change ab.val.2 - particular q hq ab.val.1 +
      definingFieldAutomorphism q 2 (ab.val.2 - particular q hq ab.val.1) = 0
    rw [map_sub]
    linear_combination hab - hp⟩)
  left_inv az := by
    dsimp only
    apply Prod.ext
    · rfl
    apply Subtype.ext
    change particular q hq az.1 + az.2.val - particular q hq az.1 = az.2.val
    ring
  right_inv ab := by
    apply Subtype.ext
    dsimp only
    apply Prod.ext
    · rfl
    change particular q hq ab.val.1 + (ab.val.2 - particular q hq ab.val.1) = ab.val.2
    ring

theorem parameters_card (q : CFSG.PrimePower) (hq : 3 ≤ q.order) :
    Nat.card (Parameters q) = q.order ^ 3 := by
  rw [Nat.card_congr (parameterEquiv q hq).symm, Nat.card_prod,
    extension_two_card, trace_kernel_card q hq]
  exact (pow_succ q.order 2).symm

end SymmetricSubgroupAsymptotics.CFSGTwistedA2UnipotentParameters
