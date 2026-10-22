import SymmetricSubgroupAsymptotics.CFSGOrthogonalDIndexShears
import SymmetricSubgroupAsymptotics.CFSGMatrixFlagSubgroups
import Mathlib.Logic.Equiv.Fin.Basic

/-! The actual defining-characteristic flag-unipotent subgroup of the
SAME elementary D group. It is proved a p-group; Sylow maximality and
its intrinsic centre are separate subsequent obligations, not premises
or properties inferred from the name. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
namespace SymmetricSubgroupAsymptotics.CFSGOrthogonalDIndexUnipotent
open CFSGOrthogonalDSerreMatrices CFSGOrthogonalDIndexParameters
open CFSGOrthogonalDIndexShears CFSGMatrixShearUnits

def flagEquiv (r : ℕ) : Index r ≃ Fin (r + r) :=
  (Equiv.sumCongr (Equiv.refl (Fin r)) Fin.revPerm).trans finSumFinEquiv

@[simp] theorem flagEquiv_pos (r : ℕ) (i : Fin r) :
    flagEquiv r (Sum.inl i) = Fin.castAdd r i := rfl

@[simp] theorem flagEquiv_neg (r : ℕ) (i : Fin r) :
    flagEquiv r (Sum.inr i) = Fin.natAdd r (Fin.revPerm i) := rfl

def borel (K : Type) [Field K] (r : ℕ) : Subgroup (elementaryRootGroup K r) :=
  (CFSGMatrixFlagSubgroups.borelUnits (K := K) (flagEquiv r)).comap (elementaryRootGroup K r).subtype

def unipotent (K : Type) [Field K] (r : ℕ) : Subgroup (elementaryRootGroup K r) :=
  (CFSGMatrixFlagSubgroups.unipotentUnits (K := K) (flagEquiv r)).comap (elementaryRootGroup K r).subtype

@[simp] theorem mem_unipotent (K : Type) [Field K] (r : ℕ) (g : elementaryRootGroup K r) :
    g ∈ unipotent K r ↔ (g.val : Mat K r).BlockTriangular (flagEquiv r) ∧
      ∀ i, (g.val : Mat K r) i i = 1 := Iff.rfl

theorem unipotent_isPGroup (K : Type) [Field K] (r p : ℕ) [Fact p.Prime] [CharP K p] :
    IsPGroup p (unipotent K r) :=
  (CFSGMatrixFlagSubgroups.unipotentUnits_isPGroup (K := K) (flagEquiv r) p).comap_of_injective
    (elementaryRootGroup K r).subtype Subtype.val_injective

theorem flag_pos_lt_neg (r : ℕ) (i j : Fin r) :
    flagEquiv r (Sum.inl i) < flagEquiv r (Sum.inr j) := by
  change i.val < r + (Fin.rev j).val
  have hi := i.isLt
  omega

theorem upperShear_triangular (K : Type) [Field K] (r : ℕ)
    (S : Matrix (Fin r) (Fin r) K) :
    (upper S : Mat K r).BlockTriangular (flagEquiv r) := by
  intro x y hxy
  cases x with
  | inl i =>
    cases y with
    | inl j =>
      have hij : i ≠ j := by intro h; subst j; exact (lt_irrefl _ hxy)
      change (1 : Matrix (Fin r) (Fin r) K) i j = 0
      exact Matrix.one_apply_ne hij
    | inr j => exact False.elim ((not_lt_of_gt (flag_pos_lt_neg r i j)) hxy)
  | inr i =>
    cases y with
    | inl j => rfl
    | inr j =>
      have hij : i ≠ j := by intro h; subst j; exact (lt_irrefl _ hxy)
      change (1 : Matrix (Fin r) (Fin r) K) i j = 0
      exact Matrix.one_apply_ne hij

def upperShearInU (K : Type) [Field K] (s : ℕ) (p : Parameters K (s + 4)) :
    unipotent K (s + 4) :=
  ⟨⟨upper (alternating p), upper_alternating_mem K s p⟩,
    upperShear_triangular K (s + 4) (alternating p), by
      intro i
      cases i <;> exact Matrix.one_apply_eq _⟩

theorem unipotent_lower_left_zero (K : Type) [Field K] (r : ℕ) (g : unipotent K r)
    (i j : Fin r) : (g.val.val : Mat K r) (Sum.inr i) (Sum.inl j) = 0 :=
  g.property.1 (flag_pos_lt_neg r j i)

end SymmetricSubgroupAsymptotics.CFSGOrthogonalDIndexUnipotent
