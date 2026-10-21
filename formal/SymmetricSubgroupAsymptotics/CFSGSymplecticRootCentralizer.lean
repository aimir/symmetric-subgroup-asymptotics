import SymmetricSubgroupAsymptotics.CFSGMatrixCyclicCentralizer
import SymmetricSubgroupAsymptotics.CFSGSymplecticRootBasisAction

/-! The common centralizer of the literal simple symplectic root matrices
is scalar. This remains valid in characteristic two and does not use a
classification, dimension formula, or Serre-quotient faithfulness. -/
set_option autoImplicit false
open scoped Matrix
namespace SymmetricSubgroupAsymptotics.CFSGSymplecticSerreMatrices
open CFSGMatrixCyclicCentralizer
variable {R : Type*} [CommRing R]

theorem simple_root_centralizer (r : ℕ) (A : Mat R (r + 1))
    (hE : ∀ i, A * positive R (r + 1) i = positive R (r + 1) i * A)
    (hF : ∀ i, A * negative R (r + 1) i = negative R (r + 1) i * A) :
    ∃ c : R, A = c • (1 : Mat R (r + 1)) := by
  let j := Fin.last r
  let c := A (Sum.inl j) (Sum.inl j)
  have hprod : A * (positive R (r + 1) j * negative R (r + 1) j) =
      (positive R (r + 1) j * negative R (r + 1) j) * A := by
    rw [← mul_assoc, hE, mul_assoc, hF, ← mul_assoc]
  rw [terminal_root_product] at hprod
  have hpos : A *ᵥ Pi.single (Sum.inl j) 1 = c • Pi.single (Sum.inl j) 1 :=
    eigenvector_of_commutes_projection A (Sum.inl j) hprod
  have hneg : A *ᵥ Pi.single (Sum.inr j) 1 = c • Pi.single (Sum.inr j) 1 := by
    have h := eigenvector_of_commutes A (negative R (r + 1) j) (hF j)
      (Pi.single (Sum.inl j) 1) c hpos
    simpa only [j, negative_last_basis] using h
  have hall : ∀ i : Fin (r + 1),
      (A *ᵥ Pi.single (Sum.inl i) 1 = c • Pi.single (Sum.inl i) 1) ∧
      (A *ᵥ Pi.single (Sum.inr i) 1 = c • Pi.single (Sum.inr i) 1) := by
    intro i
    induction i using Fin.reverseInduction with
    | last => exact ⟨hpos, hneg⟩
    | cast i ih =>
      have hp := eigenvector_of_commutes A (positive R (r + 1) i.castSucc)
        (hE i.castSucc) (Pi.single (Sum.inl i.succ) 1) c ih.1
      rw [positive_castSucc_basis] at hp
      have hn := eigenvector_of_commutes A (negative R (r + 1) i.castSucc)
        (hF i.castSucc) (Pi.single (Sum.inr i.succ) 1) c ih.2
      rw [negative_castSucc_basis] at hn
      have hn' : -(A *ᵥ Pi.single (Sum.inr i.castSucc) 1) =
          -(c • Pi.single (Sum.inr i.castSucc) 1) := by
        simpa only [Matrix.mulVec_neg, smul_neg] using hn
      exact ⟨hp, neg_injective hn'⟩
  refine ⟨c, Matrix.ext_of_mulVec_single ?_⟩
  intro y
  have hy : A *ᵥ Pi.single y 1 = c • Pi.single y 1 := by
    cases y with
    | inl i => exact (hall i).1
    | inr i => exact (hall i).2
  simpa only [Matrix.smul_mulVec, Matrix.one_mulVec] using hy

end SymmetricSubgroupAsymptotics.CFSGSymplecticSerreMatrices
