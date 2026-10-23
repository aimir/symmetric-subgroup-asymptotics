import SymmetricSubgroupAsymptotics.CFSGQuadraticMaximalSingularGallery
import SymmetricSubgroupAsymptotics.CFSGTwistedDSingularDimensionBound
import SymmetricSubgroupAsymptotics.CFSGTwistedDFixedVectorParametrization

/-! One literal untouched positive fixed-field space has dimension
r-1 and is maximal by the proved nonsplit Witt ceiling. Generic maximal
Q-gallery dimension constancy then gives the same dimension for EVERY
inclusion-maximum, and completion of every actual singular subspace. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
namespace SymmetricSubgroupAsymptotics.CFSGTwistedDMaximalSingularDimension
open CFSGOrthogonalDSerreMatrices CFSGOrthogonalDIndexBundledQuadratic
open CFSGOrthogonalDIndexQuadraticForm CFSGTwistedDFixedQuadraticSpace
open CFSGTwistedDFixedVectorParametrization CFSGTwistedDSingularDimensionBound
open CFSGTwistedA2FixedField CFSGQuadraticMaximalSingularGallery

local instance (n : ℕ) (q : CFSG.PrimePower) :
    Module.Finite (fixedField q) (fixedSpace n q) := Module.Finite.of_finite

private theorem order_ne_zero (q : CFSG.PrimePower) : q.order ≠ 0 := by
  change q.prime ^ q.exponent ≠ 0
  exact pow_ne_zero _ q.prime_isPrime.ne_zero

def positiveEmbedding (n : ℕ) (q : CFSG.PrimePower) :
    (Fin (n + 1) → fixedField q) →ₗ[fixedField q] fixedSpace n q where
  toFun x := ⟨fromParameters n q (x, (0, 0)), fromParameters_fixed n q _⟩
  map_add' x y := by
    apply Subtype.ext
    funext i
    cases i with
    | inl i =>
      rcases Fin.eq_castSucc_or_eq_last i with ⟨j, rfl⟩ | rfl <;>
        simp [fromParameters, order_ne_zero q]
    | inr i =>
      rcases Fin.eq_castSucc_or_eq_last i with ⟨j, rfl⟩ | rfl <;>
        simp [fromParameters, order_ne_zero q]
  map_smul' a x := by
    apply Subtype.ext
    funext i
    cases i with
    | inl i =>
      rcases Fin.eq_castSucc_or_eq_last i with ⟨j, rfl⟩ | rfl
      · simp only [fromParameters, Fin.lastCases_castSucc, Submodule.coe_smul,
          Pi.smul_apply, RingHom.id_apply]
        change ((a * x j : fixedField q) : q.Extension 2) = a • (x j : q.Extension 2)
        rfl
      · simp only [fromParameters, Fin.lastCases_last, Submodule.coe_smul,
          Pi.smul_apply, RingHom.id_apply]
        change (0 : q.Extension 2) = a • (0 : q.Extension 2)
        simp only [smul_zero]
    | inr i =>
      rcases Fin.eq_castSucc_or_eq_last i with ⟨j, rfl⟩ | rfl <;>
        simp [fromParameters, order_ne_zero q]

theorem positiveEmbedding_injective (n : ℕ) (q : CFSG.PrimePower) :
    Function.Injective (positiveEmbedding n q) := by
  intro x y he
  funext j
  apply Subtype.ext
  have hv := congrArg (fun v : fixedSpace n q => v.val (Sum.inl j.castSucc)) he
  change fromParameters n q (x, (0, 0)) (Sum.inl j.castSucc) =
    fromParameters n q (y, (0, 0)) (Sum.inl j.castSucc) at hv
  simpa only [fromParameters, Fin.lastCases_castSucc] using hv

def positiveSpace (n : ℕ) (q : CFSG.PrimePower) :
    Submodule (fixedField q) (fixedSpace n q) := LinearMap.range (positiveEmbedding n q)

theorem positiveSpace_finrank (n : ℕ) (q : CFSG.PrimePower) :
    Module.finrank (fixedField q) (positiveSpace n q) = n + 1 :=
  (LinearMap.finrank_range_of_inj (positiveEmbedding_injective n q)).trans
    (by simp only [Module.finrank_fintype_fun_eq_card, Fintype.card_fin])

theorem positiveSpace_singular (n : ℕ) (q : CFSG.PrimePower) :
    ∀ v ∈ positiveSpace n q, fixedQuadraticForm n q v = 0 := by
  rintro v ⟨x, rfl⟩
  apply Subtype.ext
  rw [fixedQuadraticForm_apply, splitQuadraticForm_apply]
  have hr : rightPart (q.Extension 2) (positiveEmbedding n q x).val = 0 := by
    funext i
    rcases Fin.eq_castSucc_or_eq_last i with ⟨j, rfl⟩ | rfl <;>
      simp [rightPart, positiveEmbedding, fromParameters, order_ne_zero q]
  change dotProduct (leftPart (q.Extension 2) (positiveEmbedding n q x).val)
    (rightPart (q.Extension 2) (positiveEmbedding n q x).val) = 0
  rw [hr, dotProduct_zero]

theorem positiveSpace_maximal (n : ℕ) (q : CFSG.PrimePower) :
    MaximalSingular (fixedQuadraticForm n q) (positiveSpace n q) := by
  refine ⟨positiveSpace_singular n q, ?_⟩
  intro T hT hle
  have hd := singular_finrank_le q n T hT
  exact (Submodule.eq_of_le_of_finrank_le hle (by rw [positiveSpace_finrank]; exact hd)).symm

theorem maximalSingular_finrank (n : ℕ) (q : CFSG.PrimePower)
    (M : Submodule (fixedField q) (fixedSpace n q))
    (hM : MaximalSingular (fixedQuadraticForm n q) M) :
    Module.finrank (fixedField q) M = n + 1 :=
  (maximal_finrank_eq (fixedQuadraticForm n q) ⟨M, hM⟩
    ⟨positiveSpace n q, positiveSpace_maximal n q⟩).trans (positiveSpace_finrank n q)

theorem exists_full_singular_extension (n : ℕ) (q : CFSG.PrimePower)
    (P : Submodule (fixedField q) (fixedSpace n q))
    (hP : ∀ x ∈ P, fixedQuadraticForm n q x = 0) :
    ∃ M : Submodule (fixedField q) (fixedSpace n q), P ≤ M ∧
      Module.finrank (fixedField q) M = n + 1 ∧ ∀ x ∈ M, fixedQuadraticForm n q x = 0 := by
  obtain ⟨M, hPM, hM⟩ := exists_maximal_ge (fixedQuadraticForm n q) P hP
  exact ⟨M, hPM, maximalSingular_finrank n q M hM, hM.1⟩

end SymmetricSubgroupAsymptotics.CFSGTwistedDMaximalSingularDimension
