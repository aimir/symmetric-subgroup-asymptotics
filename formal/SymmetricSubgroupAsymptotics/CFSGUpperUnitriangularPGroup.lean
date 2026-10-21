import SymmetricSubgroupAsymptotics.CFSGUpperUnitriangular
import SymmetricSubgroupAsymptotics.CFSGStrictUpperNilpotence
import Mathlib.GroupTheory.PGroup

/-! Every literal upper-unitriangular subgroup is a p-group in the
original defining characteristic, uniformly in the dimension. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
open scoped Classical
namespace SymmetricSubgroupAsymptotics.CFSGUpperUnitriangular

theorem upperUnitriangular_isPGroup {F : Type*} [Field F] {p : ℕ}
    [Fact p.Prime] [CharP F p] (n : ℕ) : IsPGroup p (upperUnitriangular F n) := by
  cases n with
  | zero =>
    intro g
    refine ⟨0,?_⟩
    simp only [pow_zero,pow_one]
    apply Subtype.ext
    apply Subtype.ext
    ext i j
    exact isEmptyElim i
  | succ n =>
    intro g
    refine ⟨n+1,?_⟩
    apply Subtype.ext
    apply Subtype.ext
    change g.val.val^(p^(n+1))=1
    exact CFSGStrictUpperNilpotence.unitriangular_pow_prime_pow g.val.val
      g.property.1 g.property.2

end SymmetricSubgroupAsymptotics.CFSGUpperUnitriangular
