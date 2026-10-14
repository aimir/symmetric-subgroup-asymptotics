import Mathlib.Algebra.Module.ZMod
import Mathlib.Algebra.Field.ZMod
import Mathlib.LinearAlgebra.FiniteDimensional.Basic
import Mathlib.LinearAlgebra.Basis.VectorSpace

/-!
# Surjective images of a binary plane embed in that plane

A quotient inherits commutativity and exponent two. It is therefore an
F₂-vector space, and a linear section of the quotient map supplies the
group embedding. No subgroup enumeration or finite-group classification
is needed.
-/

set_option autoImplicit false
noncomputable section

namespace SymmetricSubgroupAsymptotics
namespace BinaryPlaneSurjectiveImage

abbrev Plane := Fin 2 → Multiplicative (ZMod 2)

private theorem plane_square (x : Plane) : x ^ 2 = 1 := by
  funext i
  change x i ^ 2 = 1
  have h : ∀ z : Multiplicative (ZMod 2), z ^ 2 = 1 := by decide +kernel
  exact h _

/-- Every surjective image of the elementary binary plane has a faithful
homomorphism back into the same plane. The target need not be supplied
with commutativity, finiteness, or a vector-space structure. -/
theorem exists_injective {Q : Type} [Group Q]
    (q : Plane →* Q) (hq : Function.Surjective q) :
    ∃ f : Q →* Plane, Function.Injective f := by
  letI : CommGroup Q := q.commGroupOfSurjective hq
  have hsquare : ∀ x : Q, x ^ 2 = 1 := by
    intro x
    obtain ⟨u, rfl⟩ := hq x
    rw [← map_pow, plane_square, map_one]
  letI : Module (ZMod 2) (Additive Plane) := AddCommGroup.zmodModule (by
    intro x
    change x.toMul ^ 2 = 1
    exact plane_square x.toMul)
  letI : Module (ZMod 2) (Additive Q) := AddCommGroup.zmodModule (by
    intro x
    change x.toMul ^ 2 = 1
    exact hsquare x.toMul)
  letI : Module.Free (ZMod 2) (Additive Q) :=
    Module.Free.of_divisionRing (ZMod 2) (Additive Q)
  letI : Module.Projective (ZMod 2) (Additive Q) := Module.Projective.of_free
  let L : Additive Plane →ₗ[ZMod 2] Additive Q :=
    q.toAdditive.toZModLinearMap 2
  have hL : Function.Surjective L := by
    intro x
    obtain ⟨u, hu⟩ := hq x.toMul
    exact ⟨Additive.ofMul u, congrArg Additive.ofMul hu⟩
  obtain ⟨s, hs⟩ := L.exists_rightInverse_of_surjective
    (LinearMap.range_eq_top.mpr hL)
  have hsection : Function.RightInverse s L := LinearMap.ext_iff.mp hs
  refine ⟨MonoidHom.toAdditive.symm s.toAddMonoidHom, ?_⟩
  intro x y hxy
  apply Additive.ofMul.injective
  apply hsection.injective
  exact congrArg Additive.ofMul hxy

end BinaryPlaneSurjectiveImage
end SymmetricSubgroupAsymptotics

end
