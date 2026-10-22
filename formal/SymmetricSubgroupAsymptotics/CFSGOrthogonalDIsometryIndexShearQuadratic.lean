import SymmetricSubgroupAsymptotics.CFSGOrthogonalDIndexShears
import SymmetricSubgroupAsymptotics.CFSGAlternatingMatrixParameters
import SymmetricSubgroupAsymptotics.CFSGOrthogonalDIndexQuadraticForm
import SymmetricSubgroupAsymptotics.CFSGOrthogonalDElementaryGroup

/-! A literal upper shear preserves the actual split QUADRATIC form
only if its parameter is alternating, with diagonal zero proved
separately even in characteristic two. Every such actual parameter
then gives an original elementary D word. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
open scoped Matrix
namespace SymmetricSubgroupAsymptotics.CFSGOrthogonalDIsometryIndexShearQuadratic
open Matrix CFSGOrthogonalDSerreMatrices CFSGOrthogonalDIndexQuadraticForm
open CFSGOrthogonalDIndexShears CFSGMatrixShearUnits
variable (K : Type) [Field K]

theorem upper_alternating_of_quadratic (r : ℕ) (C : Matrix (Fin r) (Fin r) K)
    (hQ : upper C ∈ quadraticPreserving K r) :
    C.transpose = -C ∧ ∀ i, C i i = 0 := by
  have hq (y : Fin r → K) : (C *ᵥ y) ⬝ᵥ y = 0 := by
    have h := hQ (Sum.elim 0 y)
    change splitQ K (Matrix.fromBlocks 1 C 0 1 *ᵥ Sum.elim 0 y) =
      splitQ K (Sum.elim 0 y) at h
    simpa only [Matrix.fromBlocks_mulVec, Function.comp_def, Sum.elim_inl,
      Sum.elim_inr, Matrix.one_mulVec, Matrix.zero_mulVec, Matrix.mulVec_zero,
      add_zero, zero_add, splitQ, leftPart, rightPart, zero_dotProduct] using h
  have he (i j : Fin r) :
      (C *ᵥ Pi.single i (1 : K)) ⬝ᵥ Pi.single j (1 : K) = C j i := by
    rw [dotProduct_single, mul_one, Matrix.mulVec_single_one]
    rfl
  have hd (i : Fin r) : C i i = 0 := (he i i).symm.trans (hq (Pi.single i 1))
  refine ⟨?_, hd⟩
  ext i j
  change C j i = -(C i j)
  have hh := hq (Pi.single i 1 + Pi.single j 1)
  rw [Matrix.mulVec_add, add_dotProduct, dotProduct_add, dotProduct_add,
    he i i, he i j, he j i, he j j, hd i, hd j, zero_add, add_zero] at hh
  exact eq_neg_of_add_eq_zero_left hh

theorem upper_mem_of_alternating (s : ℕ) (C : Matrix (Fin (s + 4)) (Fin (s + 4)) K)
    (ht : C.transpose = -C) (hd : ∀ i, C i i = 0) :
    upper C ∈ elementaryRootGroup K (s + 4) := by
  have he := CFSGAlternatingMatrixParameters.alternating_parametersOf (s + 4) C ht hd
  exact he ▸ upper_alternating_mem K s (CFSGAlternatingMatrixParameters.parametersOf (s + 4) C)

theorem upper_mem_of_quadratic (s : ℕ) (C : Matrix (Fin (s + 4)) (Fin (s + 4)) K)
    (hQ : upper C ∈ quadraticPreserving K (s + 4)) :
    upper C ∈ elementaryRootGroup K (s + 4) :=
  upper_mem_of_alternating K s C (upper_alternating_of_quadratic K (s + 4) C hQ).1
    (upper_alternating_of_quadratic K (s + 4) C hQ).2

end SymmetricSubgroupAsymptotics.CFSGOrthogonalDIsometryIndexShearQuadratic
