import Mathlib.Data.Matrix.Cartan
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.GroupTheory.Solvable
import Mathlib.Tactic.FinCases

/-! Actual diagram automorphisms of the three literal exceptional Cartan
matrices. Short walk invariants distinguish all E7/E8 vertices, and distinguish
all E6 vertices once its endpoint zero is marked. No permutation census or
Weyl-chamber recognition is assumed. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
open scoped BigOperators
namespace SymmetricSubgroupAsymptotics.CFSGExceptionalDiagramAutomorphisms
variable {I : Type*} [Fintype I] [DecidableEq I]

def walk (A : Matrix I I ℤ) : ℕ→I→ℤ
  | 0=>fun _=>1
  | k+1=>fun i=>∑j : I,A i j*walk A k j

theorem walk_invariant (A : Matrix I I ℤ) (σ : Equiv.Perm I)
    (hσ : ∀i j,A (σ i) (σ j)=A i j) (k : ℕ) (i : I) :
    walk A k (σ i)=walk A k i := by
  induction k generalizing i with
  | zero=>rfl
  | succ k ih=>
    change (∑j : I,A (σ i) j*walk A k j)=∑j : I,A i j*walk A k j
    rw [←Equiv.sum_comp σ (fun j=>A (σ i) j*walk A k j)]
    simp only [hσ,ih]

def fingerprint (A : Matrix I I ℤ) (i : I) : ℤ×ℤ×ℤ :=
  (walk A 1 i,walk A 2 i,walk A 3 i)

theorem fingerprint_invariant (A : Matrix I I ℤ) (σ : Equiv.Perm I)
    (hσ : ∀i j,A (σ i) (σ j)=A i j) (i : I) :
    fingerprint A (σ i)=fingerprint A i := by
  simp only [fingerprint,walk_invariant A σ hσ]

private theorem E7_fingerprint_injective :
    Function.Injective (fingerprint CartanMatrix.E₇) := by decide

private theorem E8_fingerprint_injective :
    Function.Injective (fingerprint CartanMatrix.E₈) := by decide

private theorem E6_marked_injective : Function.Injective
    (fun i : Fin 6=>(fingerprint CartanMatrix.E₆ i,CartanMatrix.E₆ i 0)) := by decide

private theorem E6_endpoint_fingerprint (i : Fin 6)
    (hi : fingerprint CartanMatrix.E₆ i=fingerprint CartanMatrix.E₆ 0) :
    i=0 ∨ i=5 := by
  exact (by decide : ∀j : Fin 6,
    fingerprint CartanMatrix.E₆ j=fingerprint CartanMatrix.E₆ 0→j=0 ∨ j=5) i hi

theorem E7_rigid (σ : Equiv.Perm (Fin 7))
    (hσ : ∀i j,CartanMatrix.E₇ (σ i) (σ j)=CartanMatrix.E₇ i j) : σ=1 := by
  apply Equiv.ext
  intro i
  exact E7_fingerprint_injective (fingerprint_invariant _ σ hσ i)

theorem E8_rigid (σ : Equiv.Perm (Fin 8))
    (hσ : ∀i j,CartanMatrix.E₈ (σ i) (σ j)=CartanMatrix.E₈ i j) : σ=1 := by
  apply Equiv.ext
  intro i
  exact E8_fingerprint_injective (fingerprint_invariant _ σ hσ i)

theorem E6_fix_zero (σ : Equiv.Perm (Fin 6))
    (hσ : ∀i j,CartanMatrix.E₆ (σ i) (σ j)=CartanMatrix.E₆ i j)
    (h0 : σ 0=0) : σ=1 := by
  apply Equiv.ext
  intro i
  apply E6_marked_injective
  apply Prod.ext
  · exact fingerprint_invariant _ σ hσ i
  · simpa only [h0] using hσ i 0

theorem E6_endpoint (σ : Equiv.Perm (Fin 6))
    (hσ : ∀i j,CartanMatrix.E₆ (σ i) (σ j)=CartanMatrix.E₆ i j) :
    σ 0=0 ∨ σ 0=5 :=
  E6_endpoint_fingerprint _ (fingerprint_invariant _ σ hσ 0)

theorem E6_square (σ : Equiv.Perm (Fin 6))
    (hσ : ∀i j,CartanMatrix.E₆ (σ i) (σ j)=CartanMatrix.E₆ i j) : σ*σ=1 := by
  apply E6_fix_zero (σ*σ)
  · intro i j
    exact (hσ (σ i) (σ j)).trans (hσ i j)
  · change σ (σ 0)=0
    rcases E6_endpoint σ hσ with h0|h0
    · rw [h0,h0]
    · have h5 : σ 5=0 ∨ σ 5=5 := E6_endpoint_fingerprint _ (by
        have hh := fingerprint_invariant _ σ hσ 5
        exact hh.trans (by decide))
      rcases h5 with h5|h5
      · rw [h0,h5]
      · have hbad : (0:Fin 6)=5 := σ.injective (h0.trans h5.symm)
        exact False.elim ((by decide : (0:Fin 6)≠5) hbad)

def diagramGroup (A : Matrix I I ℤ) : Subgroup (Equiv.Perm I) where
  carrier := {σ | ∀i j,A (σ i) (σ j)=A i j}
  one_mem' := by intro i j; rfl
  mul_mem' := by
    intro σ τ hσ hτ i j
    exact (hσ (τ i) (τ j)).trans (hτ i j)
  inv_mem' := by
    intro σ hσ i j
    have hh := hσ (σ.symm i) (σ.symm j)
    simpa only [Equiv.apply_symm_apply] using hh.symm

theorem E6_diagram_soluble : IsSolvable (diagramGroup CartanMatrix.E₆) := by
  have hsq : ∀a : diagramGroup CartanMatrix.E₆,a*a=1 := by
    intro a
    apply Subtype.ext
    exact E6_square a.val a.property
  have hinv : ∀a : diagramGroup CartanMatrix.E₆,a⁻¹=a := by
    intro a
    exact inv_eq_of_mul_eq_one_right (hsq a)
  apply isSolvable_of_comm
  intro a b
  calc
    a*b=(a*b)⁻¹ := (hinv (a*b)).symm
    _=b⁻¹*a⁻¹ := mul_inv_rev a b
    _=b*a := by rw [hinv b,hinv a]

theorem E7_diagram_soluble : IsSolvable (diagramGroup CartanMatrix.E₇) := by
  apply isSolvable_of_comm
  intro a b
  have ha : a=1 := Subtype.ext (E7_rigid a.val a.property)
  have hb : b=1 := Subtype.ext (E7_rigid b.val b.property)
  rw [ha,hb]

theorem E8_diagram_soluble : IsSolvable (diagramGroup CartanMatrix.E₈) := by
  apply isSolvable_of_comm
  intro a b
  have ha : a=1 := Subtype.ext (E8_rigid a.val a.property)
  have hb : b=1 := Subtype.ext (E8_rigid b.val b.property)
  rw [ha,hb]

end SymmetricSubgroupAsymptotics.CFSGExceptionalDiagramAutomorphisms
