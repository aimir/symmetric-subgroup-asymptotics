import Mathlib.LinearAlgebra.TensorProduct.Tower

/-! An actual linear left inverse survives arbitrary tensor base change.
No flatness, characteristic-zero hypothesis or rational-dimension
argument is needed. This applies in particular to integral coordinate
left inverses before reduction modulo a prime.
-/
set_option autoImplicit false
namespace SymmetricSubgroupAsymptotics.SplitLinearTensorInjectivity

variable {R M N:Type*} [CommRing R] [AddCommGroup M] [Module R M]
    [AddCommGroup N] [Module R N]

theorem lTensor_leftInverse (f:M→ₗ[R]N) (g:N→ₗ[R]M)
    (h:Function.LeftInverse g f) (S:Type*) [AddCommGroup S] [Module R S] :
    Function.LeftInverse (g.lTensor S) (f.lTensor S) := by
  have hgf:g.comp f=LinearMap.id := LinearMap.ext h
  have ht:=congrArg (fun a:M→ₗ[R]M=>a.lTensor S) hgf
  change (g.comp f).lTensor S=(LinearMap.id:M→ₗ[R]M).lTensor S at ht
  rw [LinearMap.lTensor_comp,LinearMap.lTensor_id] at ht
  intro x
  exact LinearMap.congr_fun ht x

theorem lTensor_injective (f:M→ₗ[R]N) (g:N→ₗ[R]M)
    (h:Function.LeftInverse g f) (S:Type*) [AddCommGroup S] [Module R S] :
    Function.Injective (f.lTensor S) :=
  (lTensor_leftInverse f g h S).injective

theorem baseChange_leftInverse (f:M→ₗ[R]N) (g:N→ₗ[R]M)
    (h:Function.LeftInverse g f) (S:Type*) [CommRing S] [Algebra R S] :
    Function.LeftInverse (g.baseChange S) (f.baseChange S) :=
  lTensor_leftInverse f g h S

theorem baseChange_injective (f:M→ₗ[R]N) (g:N→ₗ[R]M)
    (h:Function.LeftInverse g f) (S:Type*) [CommRing S] [Algebra R S] :
    Function.Injective (f.baseChange S) :=
  (baseChange_leftInverse f g h S).injective

end SymmetricSubgroupAsymptotics.SplitLinearTensorInjectivity
