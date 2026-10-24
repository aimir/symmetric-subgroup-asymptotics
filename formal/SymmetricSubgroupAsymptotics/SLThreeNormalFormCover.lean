import SymmetricSubgroupAsymptotics.FiniteThreeNoncyclicConjugacy
import Mathlib.Tactic.Ring
import Lean.Elab.Tactic.Omega

/-! Every actual determinant-one three-by-three matrix has a literal GL3
conjugator to a raw matrix keyed by two field elements, or by one field
element in either noncyclic family. Unused keys need not be invertible;
all keys actually selected by the theorem are literal conjugates of the
original SL3 matrix. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
namespace SymmetricSubgroupAsymptotics.SLThreeNormalFormCover

open scoped Matrix
variable (K : Type*) [Field K]

abbrev Key := (K × K) ⊕ (K ⊕ K)

def normalMatrix : Key K → Matrix (Fin 3) (Fin 3) K
  | Sum.inl st => FiniteThreeCyclicCompanion.companion ![1, st.1, st.2]
  | Sum.inr (Sum.inl a) => FiniteThreeNoncyclicConjugacy.diagonal a ((a⁻¹)^2)
  | Sum.inr (Sum.inr a) => FiniteThreeNoncyclicConjugacy.jordan a

variable {K}

theorem det_conjugate (P : Matrix.GeneralLinearGroup (Fin 3) K)
    (A : Matrix (Fin 3) (Fin 3) K) :
    ((↑(P⁻¹) : Matrix (Fin 3) (Fin 3) K) * A *
      (P : Matrix (Fin 3) (Fin 3) K)).det = A.det := by
  have hP : (↑(P⁻¹) : Matrix (Fin 3) (Fin 3) K).det *
      (P : Matrix (Fin 3) (Fin 3) K).det = 1 := by
    rw [← Matrix.det_mul, Units.inv_mul, Matrix.det_one]
  rw [Matrix.det_mul, Matrix.det_mul]
  calc
    (↑(P⁻¹) : Matrix (Fin 3) (Fin 3) K).det * A.det *
        (P : Matrix (Fin 3) (Fin 3) K).det =
      A.det * ((↑(P⁻¹) : Matrix (Fin 3) (Fin 3) K).det *
        (P : Matrix (Fin 3) (Fin 3) K).det) := by ring
    _ = A.det := by rw [hP, mul_one]

theorem companion_det (c : Fin 3 → K) :
    (FiniteThreeCyclicCompanion.companion c).det = c 0 := by
  simp [FiniteThreeCyclicCompanion.companion, Matrix.det_fin_three]

theorem diagonal_det (a b : K) :
    (FiniteThreeNoncyclicConjugacy.diagonal a b).det = a * a * b := by
  simp [FiniteThreeNoncyclicConjugacy.diagonal, Fin.prod_univ_three]

theorem exists_key_conjugator (A : Matrix.SpecialLinearGroup (Fin 3) K) :
    ∃ (k : Key K) (P : Matrix.GeneralLinearGroup (Fin 3) K),
      (↑(P⁻¹) : Matrix (Fin 3) (Fin 3) K) * A.val *
        (P : Matrix (Fin 3) (Fin 3) K) = normalMatrix K k := by
  have hmin : (minpoly K A.val).natDegree ≤ 3 := by
    have hh := Polynomial.natDegree_le_of_dvd (Matrix.minpoly_dvd_charpoly A.val)
      (Matrix.charpoly_monic A.val).ne_zero
    simpa only [Matrix.charpoly_natDegree_eq_dim, Fintype.card_fin] using hh
  by_cases hc : (minpoly K A.val).natDegree = 3
  · obtain ⟨P, c, hP⟩ := FiniteThreeCyclicCompanion.exists_companion_conjugator A.val hc
    have hc0 : c 0 = 1 := by
      have hh := congrArg Matrix.det hP
      rw [det_conjugate, A.property, companion_det] at hh
      exact hh.symm
    have he : c = ![1, c 1, c 2] := by
      ext i
      fin_cases i <;> simp [hc0]
    refine ⟨Sum.inl (c 1, c 2), P, ?_⟩
    change _ = FiniteThreeCyclicCompanion.companion ![1, c 1, c 2]
    exact hP.trans (congrArg FiniteThreeCyclicCompanion.companion he)
  · have hc2 : (minpoly K A.val).natDegree ≤ 2 := by omega
    rcases FiniteThreeNoncyclicConjugacy.exists_conjugator A.val hc2 with
      ⟨P, a, b, hP⟩ | ⟨P, a, hP⟩
    · have hab : a * a * b = 1 := by
        have hh := congrArg Matrix.det hP
        rw [det_conjugate, A.property, diagonal_det] at hh
        exact hh.symm
      have ha : a ≠ 0 := by
        intro hz
        simp only [hz, zero_mul, zero_ne_one] at hab
      have hb : b = (a⁻¹)^2 := by
        calc
          b = (a * a)⁻¹ * ((a * a) * b) := by
            rw [← mul_assoc, inv_mul_cancel₀ (mul_ne_zero ha ha), one_mul]
          _ = (a * a)⁻¹ := by rw [hab, mul_one]
          _ = (a⁻¹)^2 := by rw [mul_inv_rev, pow_two]
      refine ⟨Sum.inr (Sum.inl a), P, ?_⟩
      change _ = FiniteThreeNoncyclicConjugacy.diagonal a ((a⁻¹)^2)
      exact hP.trans (congrArg (FiniteThreeNoncyclicConjugacy.diagonal a) hb)
    · exact ⟨Sum.inr (Sum.inr a), P, hP⟩

end SymmetricSubgroupAsymptotics.SLThreeNormalFormCover
