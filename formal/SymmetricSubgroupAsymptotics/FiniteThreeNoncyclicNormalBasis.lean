import SymmetricSubgroupAsymptotics.FiniteThreeQuadraticMinpoly
import SymmetricSubgroupAsymptotics.FiniteThreeDistinctEigenbasis
import SymmetricSubgroupAsymptotics.FiniteThreeSquareZeroBasis
import Mathlib.GroupTheory.Perm.Fin

/-! An actual three-dimensional operator with minimal polynomial of
degree at most two has an actual diagonal basis with a repeated scalar,
or an actual length-two Jordan chain plus a scalar vector. No canonical
form theorem is assumed; both bases are constructed from the preceding
all-field linear lemmas. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
namespace SymmetricSubgroupAsymptotics.FiniteThreeNoncyclicNormalBasis

open Module
variable {K V : Type*} [Field K] [AddCommGroup V] [Module K V]

theorem repeated_eigenbasis (A : Module.End K V) (c : Basis (Fin 3) K V)
    (d : Fin 3 → K) (hd : ∀ i, A (c i) = d i • c i)
    (a b : K) (hab : ∀ i, d i = a ∨ d i = b) :
    ∃ (e : Basis (Fin 3) K V) (x y : K),
      A (e 0) = x • e 0 ∧ A (e 1) = x • e 1 ∧ A (e 2) = y • e 2 := by
  have hp : d 0 = d 1 ∨ d 0 = d 2 ∨ d 1 = d 2 := by
    rcases hab 0 with h0 | h0 <;> rcases hab 1 with h1 | h1 <;>
      rcases hab 2 with h2 | h2 <;> simp_all
  rcases hp with hp | hp | hp
  · exact ⟨c, d 0, d 2, hd 0, by simpa only [hp] using hd 1, hd 2⟩
  · refine ⟨c.reindex (Equiv.swap 1 2), d 0, d 1, ?_, ?_, ?_⟩
    · simpa [Module.Basis.reindex_apply, Equiv.swap_apply_def] using hd 0
    · simpa [Module.Basis.reindex_apply, Equiv.swap_apply_def, hp] using hd 2
    · simpa [Module.Basis.reindex_apply, Equiv.swap_apply_def] using hd 1
  · refine ⟨c.reindex (Equiv.swap 0 2), d 1, d 0, ?_, ?_, ?_⟩
    · simpa [Module.Basis.reindex_apply, Equiv.swap_apply_def, hp] using hd 2
    · simpa [Module.Basis.reindex_apply, Equiv.swap_apply_def] using hd 1
    · simpa [Module.Basis.reindex_apply, Equiv.swap_apply_def] using hd 0

theorem exists_basis [Module.Finite K V] (A : Module.End K V)
    (hd : Module.finrank K V = 3) (hmin : (minpoly K A).natDegree ≤ 2) :
    (∃ (c : Basis (Fin 3) K V) (a b : K),
      A (c 0) = a • c 0 ∧ A (c 1) = a • c 1 ∧ A (c 2) = b • c 2) ∨
    (∃ (c : Basis (Fin 3) K V) (a : K),
      A (c 0) = a • c 0 + c 1 ∧ A (c 1) = a • c 1 ∧ A (c 2) = a • c 2) := by
  classical
  have hscalar (a : K) (ha : A = a • 1) :
      ∃ (c : Basis (Fin 3) K V) (x y : K),
        A (c 0) = x • c 0 ∧ A (c 1) = x • c 1 ∧ A (c 2) = y • c 2 := by
    let c := Module.finBasisOfFinrankEq K V hd
    refine ⟨c, a, a, ?_, ?_, ?_⟩ <;>
      simp only [ha, LinearMap.smul_apply, Module.End.one_apply]
  rcases FiniteThreeQuadraticMinpoly.scalar_or_annihilating_pair A hd hmin with
    ⟨a, ha⟩ | ⟨a, b, hab⟩
  · exact Or.inl (hscalar a ha)
  · by_cases he : a = b
    · subst b
      by_cases ha : A = a • 1
      · exact Or.inl (hscalar a ha)
      · obtain ⟨c, hc⟩ := FiniteThreeSquareZeroBasis.exists_shifted_basis A a hd hab ha
        exact Or.inr ⟨c, a, hc⟩
    · obtain ⟨c, hc⟩ := FiniteThreeDistinctEigenbasis.exists_eigenbasis A hd a b he hab
      let d : Fin 3 → K := fun i => if A (c i) = a • c i then a else b
      have hdi : ∀ i, A (c i) = d i • c i := by
        intro i
        dsimp only [d]
        split_ifs with hi
        · exact hi
        · exact (hc i).resolve_left hi
      have hdm : ∀ i, d i = a ∨ d i = b := by
        intro i
        dsimp only [d]
        split_ifs <;> simp
      exact Or.inl (repeated_eigenbasis A c d hdi a b hdm)

end SymmetricSubgroupAsymptotics.FiniteThreeNoncyclicNormalBasis
