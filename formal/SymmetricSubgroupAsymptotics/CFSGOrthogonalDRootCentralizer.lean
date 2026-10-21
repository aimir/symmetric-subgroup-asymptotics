import SymmetricSubgroupAsymptotics.CFSGMatrixCyclicCentralizer
import SymmetricSubgroupAsymptotics.CFSGOrthogonalDRootBasisAction

/-! The commutant of the literal type-D simple root matrices is scalar.
The two fork projections isolate one coordinate. Chain propagation then
reaches both halves of the standard basis, in every characteristic. -/
set_option autoImplicit false
open scoped Matrix
namespace SymmetricSubgroupAsymptotics.CFSGOrthogonalDSerreMatrices
open CFSGMatrixCyclicCentralizer
variable {R : Type*} [CommRing R]

theorem simple_root_centralizer (r : ℕ) (A : Mat R (r + 2))
    (hE : ∀ i, A * positive R (r + 2) i = positive R (r + 2) i * A)
    (hF : ∀ i, A * negative R (r + 2) i = negative R (r + 2) i * A) :
    ∃ c : R, A = c • (1 : Mat R (r + 2)) := by
  let j : Fin (r + 2) := (Fin.last r).castSucc
  let k : Fin (r + 2) := Fin.last (r + 1)
  let c := A (Sum.inl j) (Sum.inl j)
  have hprod (i : Fin (r + 2)) :
      A * (positive R (r + 2) i * negative R (r + 2) i) =
        (positive R (r + 2) i * negative R (r + 2) i) * A := by
    rw [← mul_assoc, hE, mul_assoc, hF, ← mul_assoc]
  have hproj : A * Matrix.single (Sum.inl j) (Sum.inl j) 1 =
      Matrix.single (Sum.inl j) (Sum.inl j) 1 * A := by
    have h : A * ((positive R (r + 2) k * negative R (r + 2) k) *
          (positive R (r + 2) j * negative R (r + 2) j)) =
        ((positive R (r + 2) k * negative R (r + 2) k) *
          (positive R (r + 2) j * negative R (r + 2) j)) * A := by
      rw [← mul_assoc, hprod k, mul_assoc, hprod j, ← mul_assoc]
    simpa only [j, k, fork_chain_projection] using h
  have hpj : A *ᵥ Pi.single (Sum.inl j) 1 = c • Pi.single (Sum.inl j) 1 :=
    eigenvector_of_commutes_projection A (Sum.inl j) hproj
  have hpos : A *ᵥ Pi.single (Sum.inl k) 1 = c • Pi.single (Sum.inl k) 1 := by
    have h := eigenvector_of_commutes A (negative R (r + 2) j) (hF j)
      (Pi.single (Sum.inl j) 1) c hpj
    simpa only [j, k, negative_castSucc_positive_basis] using h
  have hneg : A *ᵥ Pi.single (Sum.inr k) 1 = c • Pi.single (Sum.inr k) 1 := by
    have h := eigenvector_of_commutes A (negative R (r + 2) k) (hF k)
      (Pi.single (Sum.inl j) 1) c hpj
    simpa only [j, k, negative_fork_basis] using h
  have hall : ∀ i : Fin (r + 2),
      (A *ᵥ Pi.single (Sum.inl i) 1 = c • Pi.single (Sum.inl i) 1) ∧
      (A *ᵥ Pi.single (Sum.inr i) 1 = c • Pi.single (Sum.inr i) 1) := by
    intro i
    induction i using Fin.reverseInduction with
    | last => exact ⟨hpos, hneg⟩
    | cast i ih =>
      have hp := eigenvector_of_commutes A (positive R (r + 2) i.castSucc)
        (hE i.castSucc) (Pi.single (Sum.inl i.succ) 1) c ih.1
      rw [positive_castSucc_basis] at hp
      have hn := eigenvector_of_commutes A (negative R (r + 2) i.castSucc)
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

end SymmetricSubgroupAsymptotics.CFSGOrthogonalDSerreMatrices
