import SymmetricSubgroupAsymptotics.BinaryPGroupLinearFixedVector
import Mathlib.LinearAlgebra.Basis.Defs
import Mathlib.FieldTheory.Finite.Basic

/-! Fixed vectors in an actual regular translation basis have constant
coordinates. Over a field of order two the nonzero fixed vector is
unique. No irreducibility or group recognition is an input. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
namespace SymmetricSubgroupAsymptotics.BinaryRegularTranslationFixedVectors
open Module
variable {K V A : Type*} [Field K] [AddCommGroup V] [Module K V]
    [AddGroup A] (b : Basis A K V) (ρ : Multiplicative A →* (V ≃ₗ[K] V))
    (htranslate : ∀ a t : A, ρ (Multiplicative.ofAdd a) (b t)=b (a+t))

include htranslate in
theorem coefficients_of_fixed (v : V)
    (hv : ∀ a : A, ρ (Multiplicative.ofAdd a) v=v) (t : A) :
    b.repr v t=b.repr v 0 := by
  classical
  have he : (b.coord t).comp (ρ (Multiplicative.ofAdd t)).toLinearMap=b.coord 0 := by
    apply b.ext
    intro i
    change b.repr (ρ (Multiplicative.ofAdd t) (b i)) t=b.repr (b i) 0
    rw [htranslate]
    simp only [Basis.repr_self,Finsupp.single_apply]
    simp
  have ht := congrArg (fun f : V →ₗ[K] K => f v) he
  change b.repr (ρ (Multiplicative.ofAdd t) v) t=b.repr v 0 at ht
  rw [hv] at ht
  exact ht

private theorem nonzero_eq_one [Finite K] (hK : Nat.card K=2) (a : K) (ha : a≠0) : a=1 := by
  letI : Fintype K := Fintype.ofFinite K
  have hs : a^2=a := by
    simpa only [←Nat.card_eq_fintype_card,hK] using FiniteField.pow_card a
  have hz : a*(a-1)=0 := by rw [mul_sub,mul_one,←pow_two,hs,sub_self]
  exact sub_eq_zero.mp ((mul_eq_zero.mp hz).resolve_left ha)

include b htranslate in
theorem fixed_nonzero_unique [Finite K] (hK : Nat.card K=2) (v w : V)
    (hv : v≠0) (hw : w≠0)
    (hvfix : ∀ a : A, ρ (Multiplicative.ofAdd a) v=v)
    (hwfix : ∀ a : A, ρ (Multiplicative.ofAdd a) w=w) : v=w := by
  have hcoeff (x : V) (hx : x≠0) (hfix : ∀ a : A, ρ (Multiplicative.ofAdd a) x=x) :
      b.repr x 0=1 := by
    apply nonzero_eq_one hK
    intro hz
    apply hx
    apply b.repr.injective
    ext i
    rw [coefficients_of_fixed b ρ htranslate x hfix i,hz]
    simp only [map_zero,Finsupp.zero_apply]
  apply b.repr.injective
  ext i
  rw [coefficients_of_fixed b ρ htranslate v hvfix i,
    coefficients_of_fixed b ρ htranslate w hwfix i,
    hcoeff v hv hvfix,hcoeff w hw hwfix]

end SymmetricSubgroupAsymptotics.BinaryRegularTranslationFixedVectors
