import SymmetricSubgroupAsymptotics.CFSGOrthogonalDIndexPositiveSpace
import SymmetricSubgroupAsymptotics.CFSGMatrixShearUnits

/-! The intersection of the original positive space and its image by
a literal lower shear is the image of the actual shear kernel. This
retains original coordinates and makes the component codimension an
exact linear-algebra rank, with no orthogonal recognition premise. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
open scoped Matrix
namespace SymmetricSubgroupAsymptotics.CFSGOrthogonalDIndexPositiveGraph
open CFSGOrthogonalDSerreMatrices CFSGOrthogonalDIndexPositiveSpace
open CFSGOrthogonalDIndexQuadraticForm CFSGMatrixShearUnits
variable (K : Type) [Field K]

def ambientLinearEquiv (r : ℕ) : (Mat K r)ˣ ≃* ((Index r → K) ≃ₗ[K] (Index r → K)) :=
  Matrix.GeneralLinearGroup.toLin.trans
    (LinearMap.GeneralLinearGroup.generalLinearEquiv K (Index r → K))

def positiveEmbedding (r : ℕ) : (Fin r → K) →ₗ[K] (Index r → K) :=
  (positiveSpace K r).subtype.comp (positiveEquiv K r).toLinearMap

theorem positiveEmbedding_apply (r : ℕ) (x : Fin r → K) :
    positiveEmbedding K r x = Sum.elim x 0 := rfl

theorem positiveEmbedding_injective (r : ℕ) : Function.Injective (positiveEmbedding K r) := by
  intro x y h
  funext i
  exact congrFun h (Sum.inl i)

theorem positiveEmbedding_leftPart (r : ℕ) (x : Index r → K)
    (hx : x ∈ positiveSpace K r) : positiveEmbedding K r (leftPart K x) = x := by
  funext i
  cases i with
  | inl j => rfl
  | inr j => exact (hx j).symm

theorem lower_positive_apply (r : ℕ) (S : Matrix (Fin r) (Fin r) K) (x : Fin r → K) :
    ambientLinearEquiv K r (lower S) (positiveEmbedding K r x) = Sum.elim x (S *ᵥ x) := by
  change Matrix.fromBlocks (1 : Matrix (Fin r) (Fin r) K) 0 S
    (1 : Matrix (Fin r) (Fin r) K) *ᵥ Sum.elim x 0 = _
  rw [Matrix.fromBlocks_mulVec]
  simp only [Sum.elim_comp_inl, Sum.elim_comp_inr, Matrix.one_mulVec, Matrix.zero_mulVec,
    Matrix.mulVec_zero, add_zero]

theorem lower_intersection_range (r : ℕ) (S : Matrix (Fin r) (Fin r) K) :
    positiveSpace K r ⊓ (positiveSpace K r).map
        (ambientLinearEquiv K r (lower S)).toLinearMap =
      (Matrix.mulVecLin S).ker.map (positiveEmbedding K r) := by
  ext x
  constructor
  · rintro ⟨hx, y, hy, he⟩
    let v := leftPart K y
    have hyrep : positiveEmbedding K r v = y := positiveEmbedding_leftPart K r y hy
    have hact : ambientLinearEquiv K r (lower S) y = Sum.elim v (S *ᵥ v) := by
      rw [← hyrep, lower_positive_apply]
    have hrep : Sum.elim v (S *ᵥ v) = x := hact.symm.trans he
    have hker : v ∈ (Matrix.mulVecLin S).ker := by
      change S *ᵥ v = 0
      funext i
      exact (congrFun hrep (Sum.inr i)).trans (hx i)
    refine ⟨v, hker, ?_⟩
    funext i
    cases i with
    | inl j => exact congrFun hrep (Sum.inl j)
    | inr j => exact (hx j).symm
  · rintro ⟨v, hv, rfl⟩
    have hp : positiveEmbedding K r v ∈ positiveSpace K r := fun _ => rfl
    refine ⟨hp, positiveEmbedding K r v, hp, ?_⟩
    change ambientLinearEquiv K r (lower S) (positiveEmbedding K r v) =
      positiveEmbedding K r v
    rw [lower_positive_apply]
    change S *ᵥ v = 0 at hv
    rw [hv]
    rfl

theorem lower_intersection_finrank (r : ℕ) (S : Matrix (Fin r) (Fin r) K) :
    Module.finrank K ↥(positiveSpace K r ⊓ (positiveSpace K r).map
      (ambientLinearEquiv K r (lower S)).toLinearMap) =
        Module.finrank K (Matrix.mulVecLin S).ker := by
  rw [lower_intersection_range]
  let f : (Matrix.mulVecLin S).ker →ₗ[K] (Index r → K) :=
    (positiveEmbedding K r).domRestrict (Matrix.mulVecLin S).ker
  have hinj : Function.Injective f := by
    intro x y h
    exact Subtype.ext (positiveEmbedding_injective K r h)
  have h := LinearMap.finrank_range_of_inj (f := f) hinj
  change Module.finrank K ((positiveEmbedding K r).domRestrict
      (Matrix.mulVecLin S).ker).range = Module.finrank K (Matrix.mulVecLin S).ker at h
  rw [LinearMap.range_domRestrict] at h
  exact h

end SymmetricSubgroupAsymptotics.CFSGOrthogonalDIndexPositiveGraph
