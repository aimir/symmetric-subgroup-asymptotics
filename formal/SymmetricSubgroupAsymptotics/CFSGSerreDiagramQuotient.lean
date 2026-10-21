import SymmetricSubgroupAsymptotics.CFSGSerreDiagramFree
import Mathlib.LinearAlgebra.Quotient.Basic

/-! A Cartan-preserving diagram permutation acts on the actual rational
Serre quotient, with its actual inverse and divided-power intertwining. -/
set_option autoImplicit false
noncomputable section
open scoped Classical
namespace SymmetricSubgroupAsymptotics.CFSGSerreDiagram
open CFSG.Models.Chevalley CFSGSerreLocalNilpotence
variable {n : ℕ} (A : Matrix (Fin n) (Fin n) ℤ) (p : Equiv.Perm (Fin n))
    (hA : ∀ i j, A (p i) (p j) = A i j)
include hA

private theorem ideal_le_rename_ker :
    (CartanMatrix.Relations.toIdeal ℚ A).toSubmodule ≤
      LinearMap.ker (((quotientMap A).comp (freeRename p)).toLinearMap) := by
  intro x hx
  change quotientMap A (freeRename p x) = 0
  apply LieSubmodule.Quotient.mk_eq_zero'.mpr
  exact freeRename_ideal A p hA x hx

def rationalMap : RationalLie A →ₗ⁅ℚ⁆ RationalLie A where
  __ := (CartanMatrix.Relations.toIdeal ℚ A).toSubmodule.liftQ
    (((quotientMap A).comp (freeRename p)).toLinearMap) (ideal_le_rename_ker A p hA)
  map_lie' := by
    intro x y
    obtain ⟨u, rfl⟩ := quotientMap_surjective A x
    obtain ⟨v, rfl⟩ := quotientMap_surjective A y
    change ((quotientMap A).comp (freeRename p)) ⁅u, v⁆ =
      ⁅((quotientMap A).comp (freeRename p)) u, ((quotientMap A).comp (freeRename p)) v⁆
    exact LieHom.map_lie _ _ _

@[simp] theorem rationalMap_apply_mk (x : Free (n := n)) :
    rationalMap A p hA (quotientMap A x) = quotientMap A (freeRename p x) := rfl

@[simp] theorem rationalMap_generator (g : CartanMatrix.Generators (Fin n)) :
    rationalMap A p hA (generator A g) = generator A (nodeRename p g) := by
  change rationalMap A p hA (quotientMap A (FreeLieAlgebra.of ℚ g)) = _
  rw [rationalMap_apply_mk, freeRename_of, quotientMap_of]

theorem rationalMap_inverse_apply (x : RationalLie A) :
    rationalMap A p.symm (preserves_symm A p hA) (rationalMap A p hA x) = x := by
  obtain ⟨y, rfl⟩ := quotientMap_surjective A x
  rw [rationalMap_apply_mk, rationalMap_apply_mk, freeRename_symm_apply]

def rationalEquiv : RationalLie A ≃ₗ⁅ℚ⁆ RationalLie A where
  __ := rationalMap A p hA
  invFun := rationalMap A p.symm (preserves_symm A p hA)
  left_inv := rationalMap_inverse_apply A p hA
  right_inv := by
    intro x
    simpa only [Equiv.symm_symm] using
      rationalMap_inverse_apply A p.symm (preserves_symm A p hA) x

@[simp] theorem rationalEquiv_generator (g : CartanMatrix.Generators (Fin n)) :
    rationalEquiv A p hA (generator A g) = generator A (nodeRename p g) :=
  rationalMap_generator A p hA g

@[simp] theorem rationalEquiv_rootVector (negative : Bool) (i : Fin n) :
    rationalEquiv A p hA (rootVector A negative i) = rootVector A negative (p i) := by
  cases negative with
  | false => exact rationalEquiv_generator A p hA (CartanMatrix.Generators.E i)
  | true => exact rationalEquiv_generator A p hA (CartanMatrix.Generators.F i)

/-- Intertwining holds for ALL actual divided powers, before reduction. -/
theorem rationalEquiv_dividedPower (negative : Bool) (i : Fin n) (k : ℕ) (x : RationalLie A) :
    rationalEquiv A p hA (dividedPower A negative i k x) =
      dividedPower A negative (p i) k (rationalEquiv A p hA x) := by
  change rationalEquiv A p hA (((k.factorial : ℚ)⁻¹) •
      (LieAlgebra.ad ℚ (RationalLie A) (rootVector A negative i) ^ k) x) =
    ((k.factorial : ℚ)⁻¹) • (LieAlgebra.ad ℚ (RationalLie A) (rootVector A negative (p i)) ^ k)
      (rationalEquiv A p hA x)
  rw [map_smul]
  apply congrArg (fun y : RationalLie A => ((k.factorial : ℚ)⁻¹) • y)
  have h := lieHom_ad_pow_apply (rationalEquiv A p hA).toLieHom (rootVector A negative i) x k
  change rationalEquiv A p hA ((LieAlgebra.ad ℚ (RationalLie A) (rootVector A negative i) ^ k) x) =
    (LieAlgebra.ad ℚ (RationalLie A) (rationalEquiv A p hA (rootVector A negative i)) ^ k)
      (rationalEquiv A p hA x) at h
  rw [rationalEquiv_rootVector] at h
  exact h

end SymmetricSubgroupAsymptotics.CFSGSerreDiagram
