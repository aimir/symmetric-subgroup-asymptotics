import Mathlib.LinearAlgebra.BilinearForm.Basic
import Mathlib.LinearAlgebra.Basis.VectorSpace

/-! A function preserving an actual nondegenerate bilinear pairing on
a finite carrier is automatically a linear equivalence. Linearity is
derived from the pairing and surjectivity, rather than assumed as a
recognition callback. No characteristic restriction is used. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
namespace SymmetricSubgroupAsymptotics.CFSGFinitePairingPreserver
variable {K V : Type*} [Field K] [AddCommGroup V] [Module K V]

theorem injective_of_pairing (B : LinearMap.BilinForm K V)
    (hn : ∀ x, (∀ y, B x y = 0) → x = 0) (f : V → V)
    (hf : ∀ x y, B (f x) (f y) = B x y) : Function.Injective f := by
  intro x y he
  apply sub_eq_zero.mp
  apply hn
  intro z
  rw [map_sub, LinearMap.sub_apply, ← hf x z, ← hf y z, he, sub_self]

def linearMap [Finite V] (B : LinearMap.BilinForm K V)
    (hn : ∀ x, (∀ y, B x y = 0) → x = 0) (f : V → V)
    (hf : ∀ x y, B (f x) (f y) = B x y) : V →ₗ[K] V where
  toFun := f
  map_add' x y := by
    have hsurj := Finite.surjective_of_injective (injective_of_pairing B hn f hf)
    apply sub_eq_zero.mp
    apply hn
    intro z
    obtain ⟨w, rfl⟩ := hsurj z
    simp only [map_sub, map_add, LinearMap.sub_apply, LinearMap.add_apply, hf, sub_self]
  map_smul' a x := by
    change f (a • x) = a • f x
    have hsurj := Finite.surjective_of_injective (injective_of_pairing B hn f hf)
    apply sub_eq_zero.mp
    apply hn
    intro z
    obtain ⟨w, rfl⟩ := hsurj z
    simp only [map_sub, map_smul, LinearMap.sub_apply, LinearMap.smul_apply,
      hf, smul_eq_mul, sub_self]

theorem linearMap_apply [Finite V] (B : LinearMap.BilinForm K V)
    (hn : ∀ x, (∀ y, B x y = 0) → x = 0) (f : V → V)
    (hf : ∀ x y, B (f x) (f y) = B x y) (x : V) : linearMap B hn f hf x = f x := rfl

def linearEquiv [Finite V] (B : LinearMap.BilinForm K V)
    (hn : ∀ x, (∀ y, B x y = 0) → x = 0) (f : V → V)
    (hf : ∀ x y, B (f x) (f y) = B x y) : V ≃ₗ[K] V :=
  LinearEquiv.ofBijective (linearMap B hn f hf)
    ⟨injective_of_pairing B hn f hf,
      Finite.surjective_of_injective (injective_of_pairing B hn f hf)⟩

theorem linearEquiv_apply [Finite V] (B : LinearMap.BilinForm K V)
    (hn : ∀ x, (∀ y, B x y = 0) → x = 0) (f : V → V)
    (hf : ∀ x y, B (f x) (f y) = B x y) (x : V) : linearEquiv B hn f hf x = f x := rfl

end SymmetricSubgroupAsymptotics.CFSGFinitePairingPreserver
