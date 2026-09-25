import SymmetricSubgroupAsymptotics.Statements

/-! Exact finite-field linear-map counts for the shared-top audit. -/

set_option autoImplicit false
noncomputable section
open scoped BigOperators Classical

namespace SymmetricSubgroupAsymptotics

variable {K V : Type*} [Field K] [AddCommGroup V] [Module K V]

/-- A linear map to K^m is its literal tuple of coordinate functionals. -/
def linearRowsEquiv (m : ℕ) : (V →ₗ[K] (Fin m → K)) ≃ (Fin m → Module.Dual K V) where
  toFun L i := (LinearMap.proj i).comp L
  invFun f := LinearMap.pi f
  left_inv L := by ext v i; rfl
  right_inv f := by funext i; rfl

/-- Onto linear maps correspond exactly to independent coordinate rows. -/
theorem linearRows_independent_iff (m : ℕ) (L : V →ₗ[K] (Fin m → K)) :
    LinearIndependent K (linearRowsEquiv m L) ↔ Function.Surjective L := by
  let b := (Pi.basisFun K (Fin m)).dualBasis
  have he : (b.constr K) (linearRowsEquiv m L) = L.dualMap := by
    apply b.constr_eq
    intro i
    ext v
    simp [b,linearRowsEquiv]
  constructor
  · intro h
    apply LinearMap.dualMap_injective_iff.mp
    rw [← he]
    exact b.injective_constr_of_linearIndependent h
  · intro h
    have hi := b.linearIndependent.map' L.dualMap
      (LinearMap.ker_eq_bot.mpr (LinearMap.dualMap_injective_iff.mpr h))
    have hv : (fun i ↦ L.dualMap (b i)) = linearRowsEquiv m L := by
      funext i
      ext v
      simp [b,linearRowsEquiv]
    simpa only [Function.comp_def,hv] using hi

def surjectiveLinearRowsEquiv (m : ℕ) :
    {L : V →ₗ[K] (Fin m → K) // Function.Surjective L} ≃
      {f : Fin m → Module.Dual K V // LinearIndependent K f} :=
  (linearRowsEquiv m).subtypeEquiv (fun L ↦ (linearRows_independent_iff m L).symm)

/-- Exact count of actual surjective linear maps, including the zero count
when the codomain dimension exceeds the source dimension. -/
theorem finiteField_surjective_linearMap_card (K : Type*) [Field K] [Fintype K]
    (r m : ℕ) :
    Nat.card {L : (Fin r → K) →ₗ[K] (Fin m → K) // Function.Surjective L} =
      ∏ i : Fin m, ((Fintype.card K)^r-(Fintype.card K)^(i : ℕ)) := by
  rw [Nat.card_congr (surjectiveLinearRowsEquiv (K := K) (V := Fin r → K) m)]
  letI : Finite (Module.Dual K (Fin r → K)) :=
    Finite.of_injective (fun f : Module.Dual K (Fin r → K) ↦ (f : (Fin r → K) → K))
      DFunLike.coe_injective
  have hr : Module.finrank K (Module.Dual K (Fin r → K)) = r := by simp
  by_cases hm : m ≤ r
  · simpa only [hr] using card_linearIndependent (K := K)
      (V := Module.Dual K (Fin r → K)) (k := m) (by omega)
  · have hempty : IsEmpty {f : Fin m → Module.Dual K (Fin r → K) // LinearIndependent K f} := by
      refine ⟨fun f ↦ ?_⟩
      have h := f.2.fintype_card_le_finrank
      simp only [Fintype.card_fin,hr] at h
      omega
    rw [Nat.card_of_isEmpty]
    symm
    apply Finset.prod_eq_zero (i := ⟨r,by omega⟩) (Finset.mem_univ _)
    simp

/-- Exact count of all linear maps, obtained by values on a basis. -/
theorem finiteField_linearMap_card (K : Type*) [Field K] [Fintype K] (r m : ℕ) :
    Nat.card ((Fin r → K) →ₗ[K] (Fin m → K)) = (Fintype.card K)^(m*r) := by
  rw [← Nat.card_congr ((Pi.basisFun K (Fin r)).constr K).toEquiv]
  simp [pow_mul]

end SymmetricSubgroupAsymptotics
