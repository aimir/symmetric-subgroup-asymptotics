import SymmetricSubgroupAsymptotics.OriginalEquivariantQuotientEmbedding
import SymmetricSubgroupAsymptotics.ScalarFourHeadDefinitions

/-! Simultaneous coordinates on actual C3 module quotients. Maschke is
applied once to the retained quotient map, so invariant and scalar parts
are not replaced by unrelated dimension bounds. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
open scoped Classical
namespace SymmetricSubgroupAsymptotics

structure CubicBinaryCoordinates {V : Type} [AddCommGroup V] [Module (ZMod 2) V]
    (rho : Representation (ZMod 2) CyclicThree V) where
  invariant : Fin 2 → (V →ₗ[ZMod 2] ZMod 2)
  scalar : Fin 2 → (V →ₗ[ZMod 2] (ZMod 2 × ZMod 2))
  invariant_fixed : ∀ c v j, invariant j (rho c v) = invariant j v
  scalar_twisted : ∀ c v j,
    scalar j (rho c v) = scalarFourTwistAdd (Multiplicative.toAdd c) (scalar j v)
  joint : Function.Injective (fun v =>
    ((invariant 0 v, invariant 1 v), (scalar 0 v, scalar 1 v)))

namespace CubicBinaryCoordinates
variable {V W : Type} [AddCommGroup V] [Module (ZMod 2) V]
  [AddCommGroup W] [Module (ZMod 2) W]
  {rho : Representation (ZMod 2) CyclicThree V}
  {sigma : Representation (ZMod 2) CyclicThree W}

/-- Pull every coordinate back through the same actual injected module. -/
def ofInjective (D : CubicBinaryCoordinates rho)
    (i : sigma.IntertwiningMap rho) (hi : Function.Injective i) :
    CubicBinaryCoordinates sigma where
  invariant := fun j => (D.invariant j).comp i.toLinearMap
  scalar := fun j => (D.scalar j).comp i.toLinearMap
  invariant_fixed := by
    intro c v j
    change D.invariant j (i (sigma c v)) = D.invariant j (i v)
    have he := LinearMap.congr_fun (i.isIntertwining' c) v
    change i (sigma c v) = rho c (i v) at he
    rw [he,D.invariant_fixed]
  scalar_twisted := by
    intro c v j
    change D.scalar j (i (sigma c v)) = _
    have he := LinearMap.congr_fun (i.isIntertwining' c) v
    change i (sigma c v) = rho c (i v) at he
    rw [he,D.scalar_twisted]
    rfl
  joint := by
    intro v w he
    exact hi (D.joint he)

private instance cyclicThreeOdd : NeZero (Nat.card CyclicThree : ZMod 2) := by
  constructor
  have hc : Nat.card CyclicThree = 3 := by
    norm_num [CyclicThree, Nat.card_eq_fintype_card]
  rw [hc]
  decide +kernel

/-- Actual quotient coordinates are obtained from the original source
coordinates and original equivariant surjection, with no new scalar bound. -/
def ofSurjective (D : CubicBinaryCoordinates rho)
    (f : rho.IntertwiningMap sigma) (hf : Function.Surjective f) :
    CubicBinaryCoordinates sigma := by
  let h := original_equivariant_quotient_embedding rho sigma f hf
  exact D.ofInjective (Classical.choose h) (Classical.choose_spec h)

end CubicBinaryCoordinates
end SymmetricSubgroupAsymptotics
end
