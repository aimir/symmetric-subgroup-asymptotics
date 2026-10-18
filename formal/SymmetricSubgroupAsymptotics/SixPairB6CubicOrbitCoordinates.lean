import SymmetricSubgroupAsymptotics.CubicRegularBinaryCoordinates

/-! Two local binary observations whose original cubic translates
separate vectors give one simultaneous invariant/twisted coordinate
chart. Both coordinates use the SAME actual regular-module embedding. -/
set_option autoImplicit false
noncomputable section
namespace SymmetricSubgroupAsymptotics
namespace SixPairB6CubicOrbitCoordinates

variable {V : Type} [AddCommGroup V] [Module (ZMod 2) V]
    (rho : Representation (ZMod 2) CyclicThree V)
    (q : V →ₗ[ZMod 2] (Fin 2 → ZMod 2))

include q in
/-- Matrix coefficients of the original observation, indexed by the
actual C3 element and the original two local coordinates. -/
def embedding : rho.IntertwiningMap CubicBinaryCoordinateUniform.regular where
  toLinearMap := {
    toFun := fun v x => q (rho x.2⁻¹ v) x.1
    map_add' := by
      intro v w
      funext x
      simp only [map_add,Pi.add_apply]
    map_smul' := by
      intro a v
      funext x
      simp only [map_smul,Pi.smul_apply,RingHom.id_apply] }
  isIntertwining' := by
    intro c
    apply LinearMap.ext
    intro v
    funext x
    change q (rho x.2⁻¹ (rho c v)) x.1 =
      q (rho (c⁻¹*x.2)⁻¹ v) x.1
    rw [mul_inv_rev,inv_inv,map_mul,Module.End.mul_apply]

theorem embedding_injective
    (hseparate : ∀ v : V, (∀ c : CyclicThree, q (rho c v) = 0) → v = 0) :
    Function.Injective (embedding rho q) := by
  rw [injective_iff_map_eq_zero]
  intro v hv
  apply hseparate v
  intro c
  funext j
  have he := congrArg (fun f : CubicRegularBinaryCoordinates.Vector => f (j,c⁻¹)) hv
  change q (rho (c⁻¹)⁻¹ v) j = 0 at he
  simpa only [inv_inv] using he

/-- Canonical trace/twisted coordinates, with no separate-maxima estimate. -/
def coordinates
    (hseparate : ∀ v : V, (∀ c : CyclicThree, q (rho c v) = 0) → v = 0) :
    CubicBinaryCoordinates rho :=
  CubicRegularBinaryCoordinates.coordinates.ofInjective (embedding rho q)
    (embedding_injective rho q hseparate)

end SixPairB6CubicOrbitCoordinates
end SymmetricSubgroupAsymptotics
end
