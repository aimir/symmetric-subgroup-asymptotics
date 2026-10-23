import SymmetricSubgroupAsymptotics.CFSGHermitianMaximalExchange
import Mathlib.Algebra.Module.Submodule.Equiv

/-! Transport an actual pairing-preserving map to the literal range of
an injective source embedding. This keeps the partial isometry concrete
when the source is presented as a product of opposed spaces. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section

namespace SymmetricSubgroupAsymptotics.CFSGHermitianRangeIsometry
open CFSGTwistedAUnitaryParameters CFSGHermitianOrthogonalSpan
variable {K I U : Type*} [Field K] [Fintype I] [AddCommGroup U] [Module K U]

def onRange (a : U →ₗ[K] (I → K)) (ha : Function.Injective a)
    (b : U →ₗ[K] (I → K)) : a.range →ₗ[K] (I → K) :=
  b.comp (LinearEquiv.ofInjective a ha).symm.toLinearMap

theorem onRange_apply (a : U →ₗ[K] (I → K)) (ha : Function.Injective a)
    (b : U →ₗ[K] (I → K)) (x : U) :
    onRange a ha b (LinearEquiv.ofInjective a ha x) = b x := by
  change b ((LinearEquiv.ofInjective a ha).symm (LinearEquiv.ofInjective a ha x)) = b x
  rw [LinearEquiv.symm_apply_apply]

theorem onRange_pair (sigma : K ≃+* K) (H : Matrix I I K)
    (a : U →ₗ[K] (I → K)) (ha : Function.Injective a) (b : U →ₗ[K] (I → K))
    (hpair : ∀ x y, hermitianPair sigma H (b x) (b y) = hermitianPair sigma H (a x) (a y))
    (x y : a.range) :
    hermitianPair sigma H (onRange a ha b x) (onRange a ha b y) =
      hermitianPair sigma H x.val y.val := by
  obtain ⟨u,rfl⟩ := (LinearEquiv.ofInjective a ha).surjective x
  obtain ⟨v,rfl⟩ := (LinearEquiv.ofInjective a ha).surjective y
  simpa only [onRange_apply,LinearEquiv.ofInjective_apply] using hpair u v

theorem range_nondegenerate (sigma : K ≃+* K) (H : Matrix I I K)
    (a : U →ₗ[K] (I → K))
    (hND : ∀ x : U, (∀ y : U, hermitianPair sigma H (a x) (a y) = 0) → x = 0) :
    ∀ x ∈ a.range, (∀ y ∈ a.range, hermitianPair sigma H x y = 0) → x = 0 := by
  rintro x ⟨u,rfl⟩ hu
  have he : u = 0 := hND u (fun v => hu _ ⟨v,rfl⟩)
  rw [he,map_zero]

end SymmetricSubgroupAsymptotics.CFSGHermitianRangeIsometry
