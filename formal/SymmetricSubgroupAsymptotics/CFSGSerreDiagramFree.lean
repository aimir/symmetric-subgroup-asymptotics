import SymmetricSubgroupAsymptotics.CFSGSerreGeneratorRelations
import Mathlib.Algebra.Lie.Ideal

/-! Actual relator transport under a Cartan-preserving node permutation
of the literal free Lie algebra. No root-basis identification is used. -/
set_option autoImplicit false
noncomputable section
open scoped Classical
namespace SymmetricSubgroupAsymptotics.CFSGSerreDiagram
open CFSG.Models.Chevalley CFSGSerreLocalNilpotence
variable {n : ℕ}

def nodeRename (p : Equiv.Perm (Fin n)) :
    CartanMatrix.Generators (Fin n) → CartanMatrix.Generators (Fin n)
  | .H i => .H (p i)
  | .E i => .E (p i)
  | .F i => .F (p i)

def freeRename (p : Equiv.Perm (Fin n)) : Free (n := n) →ₗ⁅ℚ⁆ Free (n := n) :=
  FreeLieAlgebra.lift ℚ (fun g => FreeLieAlgebra.of ℚ (nodeRename p g))

@[simp] theorem freeRename_of (p : Equiv.Perm (Fin n))
    (g : CartanMatrix.Generators (Fin n)) :
    freeRename p (FreeLieAlgebra.of ℚ g) = FreeLieAlgebra.of ℚ (nodeRename p g) :=
  FreeLieAlgebra.lift_of_apply _ _

@[simp] theorem nodeRename_symm (p : Equiv.Perm (Fin n)) (g : CartanMatrix.Generators (Fin n)) :
    nodeRename p.symm (nodeRename p g) = g := by
  cases g <;> simp [nodeRename]

theorem freeRename_symm_apply (p : Equiv.Perm (Fin n)) (x : Free (n := n)) :
    freeRename p.symm (freeRename p x) = x := by
  have h : (freeRename p.symm).comp (freeRename p) = (LieHom.id : Free (n := n) →ₗ⁅ℚ⁆ Free (n := n)) := by
    apply FreeLieAlgebra.hom_ext
    intro g
    simp only [LieHom.comp_apply, freeRename_of, nodeRename_symm, LieHom.coe_id, id_eq]
  exact congrArg (fun f : Free (n := n) →ₗ⁅ℚ⁆ Free (n := n) => f x) h

def freeEquiv (p : Equiv.Perm (Fin n)) : Free (n := n) ≃ₗ⁅ℚ⁆ Free (n := n) where
  __ := freeRename p
  invFun := freeRename p.symm
  left_inv := freeRename_symm_apply p
  right_inv := by simpa only [Equiv.symm_symm] using freeRename_symm_apply p.symm

theorem preserves_symm (A : Matrix (Fin n) (Fin n) ℤ) (p : Equiv.Perm (Fin n))
    (hA : ∀ i j, A (p i) (p j) = A i j) :
    ∀ i j, A (p.symm i) (p.symm j) = A i j := by
  intro i j
  simpa only [Equiv.apply_symm_apply] using (hA (p.symm i) (p.symm j)).symm

theorem freeRename_HH (p : Equiv.Perm (Fin n)) (i j : Fin n) :
    freeRename p (CartanMatrix.Relations.HH ℚ (i, j)) =
      CartanMatrix.Relations.HH ℚ (p i, p j) := by
  simp only [CartanMatrix.Relations.HH, Function.uncurry, Function.comp_apply,
    LieHom.map_lie, freeRename_of, nodeRename]

theorem freeRename_EF (p : Equiv.Perm (Fin n)) (i j : Fin n) :
    freeRename p (CartanMatrix.Relations.EF ℚ (i, j)) =
      CartanMatrix.Relations.EF ℚ (p i, p j) := by
  by_cases hij : i = j
  · subst j
    simp only [CartanMatrix.Relations.EF, Function.uncurry, Function.comp_apply,
      if_pos rfl, if_true, map_sub, LieHom.map_lie, freeRename_of, nodeRename]
  · have hpij : p i ≠ p j := fun h => hij (p.injective h)
    simp only [CartanMatrix.Relations.EF, Function.uncurry, Function.comp_apply,
      if_neg hij, if_neg hpij, LieHom.map_lie, freeRename_of, nodeRename]

variable (A : Matrix (Fin n) (Fin n) ℤ) (p : Equiv.Perm (Fin n))
    (hA : ∀ i j, A (p i) (p j) = A i j)

include hA

theorem freeRename_HE (i j : Fin n) :
    freeRename p (CartanMatrix.Relations.HE ℚ A (i, j)) =
      CartanMatrix.Relations.HE ℚ A (p i, p j) := by
  simp only [CartanMatrix.Relations.HE, Function.uncurry, Function.comp_apply,
    map_sub, LieHom.map_lie, map_zsmul, freeRename_of, nodeRename, hA]

theorem freeRename_HF (i j : Fin n) :
    freeRename p (CartanMatrix.Relations.HF ℚ A (i, j)) =
      CartanMatrix.Relations.HF ℚ A (p i, p j) := by
  simp only [CartanMatrix.Relations.HF, Function.uncurry, Function.comp_apply,
    map_add, LieHom.map_lie, map_zsmul, freeRename_of, nodeRename, hA]

theorem freeRename_adE (i j : Fin n) :
    freeRename p (CartanMatrix.Relations.adE ℚ A (i, j)) =
      CartanMatrix.Relations.adE ℚ A (p i, p j) := by
  simp only [CartanMatrix.Relations.adE, Function.uncurry, Function.comp_apply,
    lieHom_ad_pow_apply, LieHom.map_lie, freeRename_of, nodeRename, hA]

theorem freeRename_adF (i j : Fin n) :
    freeRename p (CartanMatrix.Relations.adF ℚ A (i, j)) =
      CartanMatrix.Relations.adF ℚ A (p i, p j) := by
  simp only [CartanMatrix.Relations.adF, Function.uncurry, Function.comp_apply,
    lieHom_ad_pow_apply, LieHom.map_lie, freeRename_of, nodeRename, hA]

/-- Every original relator maps to the corresponding original relator. -/
theorem freeRename_relations (r : Free (n := n))
    (hr : r ∈ CartanMatrix.Relations.toSet ℚ A) :
    freeRename p r ∈ CartanMatrix.Relations.toSet ℚ A := by
  rcases hr with (((((hHH | hEF) | hHE) | hHF) | hE) | hF)
  · obtain ⟨⟨i, j⟩, rfl⟩ := hHH
    rw [freeRename_HH]
    exact Or.inl (Or.inl (Or.inl (Or.inl (Or.inl ⟨(p i, p j), rfl⟩))))
  · obtain ⟨⟨i, j⟩, rfl⟩ := hEF
    rw [freeRename_EF]
    exact Or.inl (Or.inl (Or.inl (Or.inl (Or.inr ⟨(p i, p j), rfl⟩))))
  · obtain ⟨⟨i, j⟩, rfl⟩ := hHE
    rw [freeRename_HE A p hA]
    exact Or.inl (Or.inl (Or.inl (Or.inr ⟨(p i, p j), rfl⟩)))
  · obtain ⟨⟨i, j⟩, rfl⟩ := hHF
    rw [freeRename_HF A p hA]
    exact Or.inl (Or.inl (Or.inr ⟨(p i, p j), rfl⟩))
  · obtain ⟨⟨i, j⟩, rfl⟩ := hE
    rw [freeRename_adE A p hA]
    exact Or.inl (Or.inr ⟨(p i, p j), rfl⟩)
  · obtain ⟨⟨i, j⟩, rfl⟩ := hF
    rw [freeRename_adF A p hA]
    exact Or.inr ⟨(p i, p j), rfl⟩

/-- The literal Serre ideal is preserved, proved by ideal closure from
literal relators rather than an assumed quotient action. -/
theorem freeRename_ideal (x : Free (n := n))
    (hx : x ∈ CartanMatrix.Relations.toIdeal ℚ A) :
    freeRename p x ∈ CartanMatrix.Relations.toIdeal ℚ A := by
  have hle : CartanMatrix.Relations.toIdeal ℚ A ≤
      LieIdeal.comap (freeRename p) (CartanMatrix.Relations.toIdeal ℚ A) := by
    apply LieSubmodule.lieSpan_le.mpr
    intro r hr
    exact LieSubmodule.subset_lieSpan (freeRename_relations A p hA r hr)
  exact hle hx

end SymmetricSubgroupAsymptotics.CFSGSerreDiagram
