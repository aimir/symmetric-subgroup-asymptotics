import SymmetricSubgroupAsymptotics.CFSGTwistedDLinearParameters
import SymmetricSubgroupAsymptotics.CFSGTwistedDMaximalSingularDimension

/-! The literal negative maximal singular space in the actual fixed
carrier has dimension r-1 and is recognized by vanishing of all positive
coordinates. Its anisotropic coordinate is zero; no complementary split
dimension identity is assumed. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
namespace SymmetricSubgroupAsymptotics.CFSGTwistedDNegativeSpaceCoordinates
open CFSGOrthogonalDSerreMatrices CFSGTwistedDFixedQuadraticSpace
open CFSGTwistedDLinearParameters CFSGTwistedA2FixedField
open CFSGTwistedDMaximalSingularDimension CFSGQuadraticMaximalSingularGallery
open CFSGTwistedDFixedVectorParametrization CFSGOrthogonalDIndexBundledQuadratic
open CFSGOrthogonalDIndexQuadraticForm

local instance (n : ℕ) (q : CFSG.PrimePower) :
    Module.Finite (fixedField q) (fixedSpace n q) := Module.Finite.of_finite

def negativeEmbedding (n : ℕ) (q : CFSG.PrimePower) :
    (Fin (n + 1) → fixedField q) →ₗ[fixedField q] fixedSpace n q where
  toFun y := (linearParameters n q).symm (0, (y, 0))
  map_add' y z := by
    rw [← map_add]
    congr 1
    simp only [Prod.mk_add_mk, add_zero]
  map_smul' a y := by
    rw [← map_smul]
    congr 1
    simp only [Prod.smul_mk, smul_zero, RingHom.id_apply]

theorem negativeEmbedding_injective (n : ℕ) (q : CFSG.PrimePower) :
    Function.Injective (negativeEmbedding n q) := by
  intro y z he
  have h := congrArg (linearParameters n q) he
  change linearParameters n q ((linearParameters n q).symm (0, (y, 0))) =
    linearParameters n q ((linearParameters n q).symm (0, (z, 0))) at h
  simp only [LinearEquiv.apply_symm_apply] at h
  exact congrArg (fun x => x.2.1) h

def negativeSpace (n : ℕ) (q : CFSG.PrimePower) :
    Submodule (fixedField q) (fixedSpace n q) := LinearMap.range (negativeEmbedding n q)

theorem negativeSpace_finrank (n : ℕ) (q : CFSG.PrimePower) :
    Module.finrank (fixedField q) (negativeSpace n q) = n + 1 :=
  (LinearMap.finrank_range_of_inj (negativeEmbedding_injective n q)).trans
    (by simp only [Module.finrank_fintype_fun_eq_card, Fintype.card_fin])

def positiveZeroSpace (n : ℕ) (q : CFSG.PrimePower) :
    Submodule (fixedField q) (fixedSpace n q) where
  carrier := {v | ∀ i, v.val (Sum.inl i) = 0}
  zero_mem' := by intro i; rfl
  add_mem' {v w} hx hy := by
    intro i
    change v.val (Sum.inl i) + w.val (Sum.inl i) = 0
    rw [hx i, hy i, add_zero]
  smul_mem' a v hv := by
    intro i
    change (a : q.Extension 2) * v.val (Sum.inl i) = 0
    rw [hv i, mul_zero]

theorem positiveZeroSpace_singular (n : ℕ) (q : CFSG.PrimePower) :
    ∀ v ∈ positiveZeroSpace n q, fixedQuadraticForm n q v = 0 := by
  intro v hv
  apply Subtype.ext
  rw [fixedQuadraticForm_apply, splitQuadraticForm_apply]
  have hl : leftPart (q.Extension 2) v.val = 0 := by
    funext i
    exact hv i
  change dotProduct (leftPart (q.Extension 2) v.val) (rightPart (q.Extension 2) v.val) = 0
  rw [hl, zero_dotProduct]

theorem negativeSpace_le_positiveZeroSpace (n : ℕ) (q : CFSG.PrimePower) :
    negativeSpace n q ≤ positiveZeroSpace n q := by
  rintro v ⟨y, rfl⟩ i
  change fromParameters n q (0, (y, 0)) (Sum.inl i) = 0
  rcases Fin.eq_castSucc_or_eq_last i with ⟨j, rfl⟩ | rfl <;>
    simp only [fromParameters, Fin.lastCases_castSucc, Fin.lastCases_last, Pi.zero_apply,
      ZeroMemClass.coe_zero]

theorem negativeSpace_eq_positiveZeroSpace (n : ℕ) (q : CFSG.PrimePower) :
    negativeSpace n q = positiveZeroSpace n q := by
  apply Submodule.eq_of_le_of_finrank_le (negativeSpace_le_positiveZeroSpace n q)
  rw [negativeSpace_finrank]
  exact CFSGTwistedDSingularDimensionBound.singular_finrank_le q n
    (positiveZeroSpace n q) (positiveZeroSpace_singular n q)

theorem mem_negativeSpace_iff (n : ℕ) (q : CFSG.PrimePower) (v : fixedSpace n q) :
    v ∈ negativeSpace n q ↔ ∀ i, v.val (Sum.inl i) = 0 := by
  rw [negativeSpace_eq_positiveZeroSpace]
  rfl

theorem negativeSpace_singular (n : ℕ) (q : CFSG.PrimePower) :
    ∀ v ∈ negativeSpace n q, fixedQuadraticForm n q v = 0 := by
  rw [negativeSpace_eq_positiveZeroSpace]
  exact positiveZeroSpace_singular n q

theorem negativeSpace_maximal (n : ℕ) (q : CFSG.PrimePower) :
    MaximalSingular (fixedQuadraticForm n q) (negativeSpace n q) := by
  refine ⟨negativeSpace_singular n q, ?_⟩
  intro T hT hle
  apply (Submodule.eq_of_le_of_finrank_le hle ?_).symm
  rw [negativeSpace_finrank]
  exact CFSGTwistedDSingularDimensionBound.singular_finrank_le q n T hT

end SymmetricSubgroupAsymptotics.CFSGTwistedDNegativeSpaceCoordinates
