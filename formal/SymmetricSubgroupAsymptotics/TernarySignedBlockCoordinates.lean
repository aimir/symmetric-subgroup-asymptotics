import SymmetricSubgroupAsymptotics.PermutationalWreathProduct
import Mathlib.GroupTheory.SemidirectProduct
import Mathlib.LinearAlgebra.Pi
import Mathlib.Data.ZMod.Basic
import Mathlib.Tactic.Ring
import Mathlib.Tactic.FinCases

/-!
# Faithful affine coordinates on four ternary blocks

Signed block permutations act on the four translation coordinates. Their
semidirect product has a faithful action on twelve points. A phase chart
retains the original point labels, and an injective closure transport binds
any displayed coordinate generators to their actual permutation subgroup.
No group elements or subgroups are enumerated here.
-/

set_option autoImplicit false
noncomputable section
open scoped Classical

namespace SymmetricSubgroupAsymptotics
namespace TernarySignedBlockCoordinates

abbrev Scalar := ZMod 3
abbrev Vector := Fin 4 → Scalar
abbrev Points := Scalar × Fin 4
abbrev Signed := PermutationalWreathProduct Scalarˣ (Equiv.Perm (Fin 4)) (Fin 4)

instance : Finite Signed :=
  Finite.of_injective (fun g : Signed ↦ (g.left, g.right)) (by
    intro g h he
    exact PermutationalWreathProduct.ext
      (congrArg (fun p : (Fin 4 → Scalarˣ) × Equiv.Perm (Fin 4) ↦ p.1) he)
      (congrArg (fun p : (Fin 4 → Scalarˣ) × Equiv.Perm (Fin 4) ↦ p.2) he))

/-- The monomial action uses signs at the destination block. -/
def linear (g : Signed) : Vector ≃ₗ[Scalar] Vector where
  toFun v i := (g.left i : Scalar) * v (g.right⁻¹ i)
  invFun v i := ((g.left (g.right i))⁻¹ : Scalarˣ) * v (g.right i)
  left_inv := by intro v; funext i; simp
  right_inv := by intro v; funext i; simp
  map_add' := by intro v w; funext i; simp [mul_add]
  map_smul' := by
    intro c v
    funext i
    change (g.left i : Scalar) * (c * v (g.right⁻¹ i)) =
      c * ((g.left i : Scalar) * v (g.right⁻¹ i))
    ring

def signedLinear : Signed →* (Vector ≃ₗ[Scalar] Vector) where
  toFun := linear
  map_one' := by ext v i; simp [linear]
  map_mul' g h := by
    ext v i
    simp [linear, PermutationalWreathProduct.mul_left,
      PermutationalWreathProduct.mul_right, Equiv.Perm.mul_apply, mul_assoc]

def linAut : Signed →* MulAut (Multiplicative Vector) where
  toFun g := ((signedLinear g).toAddEquiv).toMultiplicative
  map_one' := by ext v; simp [signedLinear, linear]
  map_mul' g h := by
    apply MulEquiv.ext
    intro v
    change Multiplicative.ofAdd (signedLinear (g * h) v.toAdd) =
      Multiplicative.ofAdd (signedLinear g (signedLinear h v.toAdd))
    rw [map_mul]
    rfl

abbrev Affine := Multiplicative Vector ⋊[linAut] Signed

instance : Finite Affine := Finite.of_equiv _ SemidirectProduct.equivProd.symm

/-- Translation first, then destination-indexed signs and the block motion. -/
def action : Affine →* Equiv.Perm Points where
  toFun g :=
    { toFun p :=
        (g.left.toAdd (g.right.right p.2) +
          (g.right.left (g.right.right p.2) : Scalar) * p.1,
          g.right.right p.2)
      invFun p :=
        (((g.right.left p.2)⁻¹ : Scalarˣ) * (p.1 - g.left.toAdd p.2),
          g.right.right⁻¹ p.2)
      left_inv := by intro p; ext <;> simp
      right_inv := by intro p; ext <;> simp }
  map_one' := by ext p <;> simp
  map_mul' g h := by
    ext p <;>
      simp [SemidirectProduct.mul_left, SemidirectProduct.mul_right,
        linAut, signedLinear, linear, PermutationalWreathProduct.mul_left,
        PermutationalWreathProduct.mul_right, Equiv.Perm.mul_apply,
        mul_add, mul_assoc, add_assoc]

theorem action_apply (g : Affine) (p : Points) :
    action g p =
      (g.left.toAdd (g.right.right p.2) +
        (g.right.left (g.right.right p.2) : Scalar) * p.1,
        g.right.right p.2) := rfl

theorem action_injective : Function.Injective action := by
  rw [injective_iff_map_eq_one]
  intro g hg
  have hpoint (p : Points) : action g p = p := by rw [hg]; rfl
  have hblock : g.right.right = 1 := by
    apply Equiv.ext
    intro i
    exact congrArg (fun p : Points ↦ p.2) (hpoint (0, i))
  have htranslation : g.left = 1 := by
    apply Multiplicative.toAdd.injective
    funext i
    have h := congrArg (fun p : Points ↦ p.1) (hpoint (0, i))
    simpa [action_apply, hblock] using h
  have hsign : g.right.left = 1 := by
    funext i
    apply Units.ext
    have h := congrArg (fun p : Points ↦ p.1) (hpoint (1, i))
    simpa [action_apply, hblock, htranslation] using h
  exact SemidirectProduct.ext htranslation
    (PermutationalWreathProduct.ext hsign hblock)

/-- The unshifted original point labels are `4 * z + i`. -/
def baseChart : Fin 12 ≃ Points where
  toFun x := (#[
    (0, 0), (0, 1), (0, 2), (0, 3),
    (1, 0), (1, 1), (1, 2), (1, 3),
    (2, 0), (2, 1), (2, 2), (2, 3)] : Array Points)[x.val]!
  invFun p :=
    ((#[#[0, 1, 2, 3], #[4, 5, 6, 7], #[8, 9, 10, 11]] :
      Array (Array (Fin 12)))[p.1.val]!)[p.2.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def phaseChart (d : Vector) : Points ≃ Points where
  toFun p := (p.1 + d p.2, p.2)
  invFun p := (p.1 - d p.2, p.2)
  left_inv := by intro p; ext <;> simp
  right_inv := by intro p; ext <;> simp

def pointChart (d : Vector) : Fin 12 ≃ Points := baseChart.trans (phaseChart d)

def literalAction (d : Vector) : Affine →* Equiv.Perm (Fin 12) :=
  (pointChart d).symm.permCongrHom.toMonoidHom.comp action

theorem literalAction_injective (d : Vector) : Function.Injective (literalAction d) :=
  (pointChart d).symm.permCongrHom.injective.comp action_injective

def translate (v : Vector) : Affine := SemidirectProduct.inl (Multiplicative.ofAdd v)

def signed (g : Signed) : Affine := SemidirectProduct.inr g

theorem translate_mul (v w : Vector) : translate v * translate w = translate (v + w) := by
  exact (map_mul SemidirectProduct.inl (Multiplicative.ofAdd v) (Multiplicative.ofAdd w)).symm

theorem signed_conj_translate (g : Signed) (v : Vector) :
    signed g * translate v * (signed g)⁻¹ = translate (linear g v) := by
  simpa only [signed, translate, map_inv] using
    (SemidirectProduct.inl_aut (φ := linAut) g (Multiplicative.ofAdd v)).symm

/-- Exact closure transport, independent of any order or completeness count. -/
theorem map_closure_eq {ι : Type} (d : Vector)
    (generators : ι → Affine) (literalGenerators : ι → Equiv.Perm (Fin 12))
    (binding : ∀ i, literalAction d (generators i) = literalGenerators i) :
    (Subgroup.closure (Set.range generators)).map (literalAction d) =
      Subgroup.closure (Set.range literalGenerators) := by
  rw [MonoidHom.map_closure]
  congr 1
  ext x
  constructor
  · rintro ⟨g, ⟨i, rfl⟩, rfl⟩
    exact ⟨i, (binding i).symm⟩
  · rintro ⟨i, rfl⟩
    exact ⟨generators i, Set.mem_range_self i, binding i⟩

noncomputable def closureEquiv {ι : Type} (d : Vector)
    (generators : ι → Affine) (literalGenerators : ι → Equiv.Perm (Fin 12))
    (binding : ∀ i, literalAction d (generators i) = literalGenerators i) :
    Subgroup.closure (Set.range generators) ≃*
      Subgroup.closure (Set.range literalGenerators) :=
  ((Subgroup.closure (Set.range generators)).equivMapOfInjective
    (literalAction d) (literalAction_injective d)).trans
      (MulEquiv.subgroupCongr (map_closure_eq d generators literalGenerators binding))

end TernarySignedBlockCoordinates
end SymmetricSubgroupAsymptotics

end
