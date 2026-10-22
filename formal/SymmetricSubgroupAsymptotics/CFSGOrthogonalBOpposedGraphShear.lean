import SymmetricSubgroupAsymptotics.CFSGOrthogonalBOpposedProjection
import SymmetricSubgroupAsymptotics.CFSGOrthogonalBArbitraryShearMembership
import Mathlib.Tactic.LinearCombination

/-! A literal middle-zero singular graph with identity negative
projection is carried to the negative space by an actual original
alternating shear, fixing the whole positive space pointwise. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
open scoped BigOperators Matrix
namespace SymmetricSubgroupAsymptotics.CFSGOrthogonalBOpposedGraphShear
open CFSGOrthogonalBSerreMatrices CFSGOrthogonalBPositiveSubspace
open CFSGOrthogonalBVectorCoordinates CFSGOrthogonalBIndexShears CFSGMatrixShearUnits
open CFSGOrthogonalBPositiveMiddleWords
variable (K : Type) [Field K]

def negativeEmbedding (n : ℕ) : (Fin n → K) →ₗ[K] (Index n → K) where
  toFun y := Sum.elim (Sum.elim (fun _ => 0) y) (fun _ => 0)
  map_add' _ _ := by funext i; rcases i with (i | i) | ⟨⟩ <;> simp
  map_smul' _ _ := by funext i; rcases i with (i | i) | ⟨⟩ <;> simp

def negativeSubspace (n : ℕ) : Submodule K (Index n → K) := (negativeEmbedding K n).range

theorem gram_pairing_coordinates (n : ℕ) (v w : Index n → K) :
    (gram K n).toBilin' v w =
      (∑ i : Fin n, (positivePart K n v i * 2 * negativePart K n w i +
        negativePart K n v i * 2 * positivePart K n w i)) + v (middle n) * w (middle n) := by
  simp [Matrix.toBilin'_apply, gram, Fintype.sum_sum_type, positivePart, negativePart,
    pos, neg, middle, Finset.sum_add_distrib, mul_ite, ite_mul]
  exact add_comm _ _

def graphMatrix (n : ℕ) (L : (Fin n → K) →ₗ[K] (Index n → K)) :
    Matrix (Fin n) (Fin n) K := fun i j => L (Pi.single j 1) (pos n i)

theorem graphMatrix_mulVec (n : ℕ) (L : (Fin n → K) →ₗ[K] (Index n → K))
    (y : Fin n → K) : graphMatrix K n L *ᵥ y = positivePart K n (L y) := by
  funext i
  let f : (Fin n → K) →ₗ[K] K := (LinearMap.proj (pos n i)).comp L
  have hf := functional_coordinates K f y
  change (∑ j : Fin n, graphMatrix K n L i j * y j) = f y
  rw [hf]
  apply Finset.sum_congr rfl
  intro j _
  change graphMatrix K n L i j * y j = y j * graphMatrix K n L i j
  exact mul_comm _ _

theorem graphMatrix_alternating (h2 : (2 : K) ≠ 0) (n : ℕ)
    (L : (Fin n → K) →ₗ[K] (Index n → K))
    (hn : ∀ y, negativePart K n (L y) = y)
    (hm : ∀ y, L y (middle n) = 0)
    (hs : ∀ x y, (gram K n).toBilin' (L x) (L y) = 0) :
    (graphMatrix K n L).transpose = -(graphMatrix K n L) ∧
      ∀ i, graphMatrix K n L i i = 0 := by
  have hsum (i j : Fin n) : graphMatrix K n L j i + graphMatrix K n L i j = 0 := by
    have hh := hs (Pi.single i 1) (Pi.single j 1)
    rw [gram_pairing_coordinates, hn, hn, hm, hm] at hh
    simp only [mul_zero, add_zero, Finset.sum_add_distrib] at hh
    simp [Pi.single_apply, mul_ite, ite_mul, positivePart] at hh
    apply mul_left_cancel₀ h2
    change 2 * (graphMatrix K n L j i + graphMatrix K n L i j) = 2 * 0
    dsimp only [graphMatrix]
    linear_combination hh
  constructor
  · ext i j
    exact eq_neg_of_add_eq_zero_left (hsum i j)
  · intro i
    have hh : (2 : K) * graphMatrix K n L i i = 0 := by linear_combination (hsum i i)
    exact (mul_eq_zero.mp hh).resolve_left h2

theorem exists_shear_align (h2 : (2 : K) ≠ 0) (s : ℕ)
    (L : (Fin (s + 1) → K) →ₗ[K] (Index (s + 1) → K))
    (hn : ∀ y, negativePart K (s + 1) (L y) = y)
    (hm : ∀ y, L y (middle (s + 1)) = 0)
    (hs : ∀ x y, (gram K (s + 1)).toBilin' (L x) (L y) = 0) :
    ∃ g : elementaryRootGroup K (s + 1),
      (∀ v ∈ positiveSubspace K (s + 1), (g.val : Mat K (s + 1)) *ᵥ v = v) ∧
      L.range.map (Matrix.mulVecLin (g.val : Mat K (s + 1))) = negativeSubspace K (s + 1) := by
  let A := graphMatrix K (s + 1) L
  obtain ⟨hAt, hAd⟩ := graphMatrix_alternating K h2 (s + 1) L hn hm hs
  have ht : (-A).transpose = -(-A) := by simpa only [Matrix.transpose_neg] using congrArg Neg.neg hAt
  have hd : ∀ i, (-A) i i = 0 := fun i => by simp [A, hAd i]
  let g : elementaryRootGroup K (s + 1) :=
    ⟨extensionHom K (s + 1) (upper (-A)),
      CFSGOrthogonalBArbitraryShearMembership.upper_mem K h2 s (-A) ht hd⟩
  have hv (v : Index (s + 1) → K) : (g.val : Mat K (s + 1)) *ᵥ v =
      Sum.elim (Sum.elim (positivePart K (s + 1) v - A *ᵥ negativePart K (s + 1) v)
        (negativePart K (s + 1) v)) (fun _ => v (middle (s + 1))) := by
    change Matrix.fromBlocks (Matrix.fromBlocks 1 (-A) 0 1) 0 0 1 *ᵥ v = _
    funext i
    rcases i with (i | i) | ⟨⟩ <;>
      simp [Matrix.fromBlocks_mulVec, positivePart, negativePart, pos, neg, middle,
        Function.comp_def, Matrix.neg_mulVec, sub_eq_add_neg]
    all_goals rfl
  have hLy (y : Fin (s + 1) → K) :
      (g.val : Mat K (s + 1)) *ᵥ L y = negativeEmbedding K (s + 1) y := by
    rw [hv, hn, hm, ← graphMatrix_mulVec K (s + 1) L y]
    simp [A, negativeEmbedding]
    rfl
  refine ⟨g, ?_, ?_⟩
  · intro v hvp
    obtain ⟨hvn, _⟩ := (mem_positiveSubspace K (s + 1) v).mp hvp
    have hz : negativePart K (s + 1) v = 0 := funext hvn
    rw [hv, hz, Matrix.mulVec_zero, sub_zero]
    funext i
    rcases i with (i | i) | ⟨⟩
    · rfl
    · exact (hvn i).symm
    · rfl
  · ext v
    constructor
    · rintro ⟨x, ⟨y, rfl⟩, rfl⟩
      exact ⟨y, (hLy y).symm⟩
    · rintro ⟨y, rfl⟩
      exact ⟨L y, ⟨y, rfl⟩, hLy y⟩

end SymmetricSubgroupAsymptotics.CFSGOrthogonalBOpposedGraphShear
