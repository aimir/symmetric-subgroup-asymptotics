import SymmetricSubgroupAsymptotics.CFSGGradedMatrixTransportStrict
import SymmetricSubgroupAsymptotics.CFSGNormTwoGeckWordLatticeSupport
import SymmetricSubgroupAsymptotics.CFSGNormTwoCoordinateLeadingHom
import SymmetricSubgroupAsymptotics.CFSGNormTwoCoordinatePositiveWordNormalizer

/-! A conjugate of the literal positive group by a Weyl word can contain
an element with all simple leading coordinates nonzero only when the
word normalizes that positive group. This is a literal integer-grading
argument and permits every coefficient-field characteristic. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
namespace SymmetricSubgroupAsymptotics.CFSGNormTwoCoordinateRegularLeadingWord
open CFSGIntegerMatrixPairing CFSGNormTwoRootPairing CFSGSerreQuadraticMatrix
open CFSGNormTwoGeckIntegralRealization CFSGNormTwoGeckPositivePGroup
open CFSGNormTwoGeckWeylWordDegree CFSGNormTwoGeckWeylWordAlgebra
open CFSGNormTwoGeckWeylLatticeLinear CFSGNormTwoGeckWordLatticeSupport
open CFSGNormTwoGeckLatticeDegree CFSGNormTwoGeckHeightSupport
open CFSGNormTwoGeckColumns
open CFSGNormTwoCoordinateHeight CFSGNormTwoCoordinateLeadingFactor
open CFSGNormTwoGeckPositiveFirstLayer CFSGNormTwoCoordinatePositiveWordNormalizer
open CFSGGradedMatrixSupport CFSGGradedMatrixSubgroups CFSGGradedMatrixTransportStrict
variable {r : ℕ} (A : Matrix (Fin r) (Fin r) ℤ) (hd : ∀ i, A i i = 2)
    (hs : A.transpose = A) (hp : (rationalMatrix A).PosDef)
    (ho : ∀ i j, i ≠ j → A i j ≤ 0)
    [Fintype (Roots A)] [DecidableEq (Roots A)] [(rootPairing A hs hp).IsIrreducible]
local notation "b₀" => coordinateBase A hd hs hp ho
local notation "s₀" => coordinateIndexEquiv A hd hs hp ho
private abbrev Mat (K : Type) := Matrix ((b₀).support ⊕ Roots A) ((b₀).support ⊕ Roots A) K

theorem positive_mem_transported_strict (K : Type) [Field K] (w : List (Fin r))
    (u : (Mat A hd hs hp ho K)ˣ) (hu : u ∈ rootGroup A hs hp b₀ s₀ K false) :
    wordUnit A hs hp b₀ s₀ K w * u * (wordUnit A hs hp b₀ s₀ K w)⁻¹ ∈
      strictUnits (fun k => coordinateHeight
        ((wordLinear A hs hp b₀ s₀ w).symm (latticeWeight A hs hp b₀ k))) := by
  have hwt : (fun k => coordinateHeight (latticeWeight A hs hp b₀ k)) =
      weight A hs hp b₀ coordinateHeight := by
    funext k
    cases k <;> simp only [latticeWeight, weight, map_zero]
  have hstrict := (positive_firstLayer_mem_span A hs hp b₀ s₀ coordinateHeight
    (simple_height A hd hs hp ho) K u hu).1
  rw [← hwt] at hstrict
  have hwi := word_lattice_support A hs hp b₀ s₀ K (inverseWord w)
  rw [wordUnit_inverseWord, wordLinear_inverseWord] at hwi
  exact conjugate_mem_strict (latticeWeight A hs hp b₀) coordinateHeight
    (wordLinear A hs hp b₀ s₀ w).toEquiv (wordUnit A hs hp b₀ s₀ K w)
    (word_lattice_support A hs hp b₀ s₀ K w) hwi u hstrict

theorem inverse_simple_height_pos_of_leading_ne_zero (K : Type) [Field K]
    (w : List (Fin r)) (u : (Mat A hd hs hp ho K)ˣ)
    (hu : u ∈ rootGroup A hs hp b₀ s₀ K false) (i : Fin r)
    (hreg : leadingCoordinates A hd hs hp ho K
      (wordUnit A hs hp b₀ s₀ K w * u * (wordUnit A hs hp b₀ s₀ K w)⁻¹) i ≠ 0) :
    0 < coordinateHeight ((wordLinear A hs hp b₀ s₀ w).symm (s₀ i : Roots A).val) := by
  by_contra h
  have hn : coordinateHeight ((wordLinear A hs hp b₀ s₀ w).symm
      (s₀ i : Roots A).val) ≤ 0 := le_of_not_gt h
  have ht := positive_mem_transported_strict A hd hs hp ho K w u hu
  have hentry := ht (Sum.inl (s₀ i))
    (Sum.inr (negativeIndex A hs hp (s₀ i))) (by
      simp only [latticeWeight, negative_val, map_zero, map_neg]
      omega)
  apply hreg
  change (↑(wordUnit A hs hp b₀ s₀ K w * u * (wordUnit A hs hp b₀ s₀ K w)⁻¹) :
      Mat A hd hs hp ho K) (Sum.inl (s₀ i))
        (Sum.inr (negativeIndex A hs hp (s₀ i))) = 0
  simpa only [Matrix.one_apply, Sum.inl_ne_inr, if_false] using hentry

theorem regular_leading_word_mem_normalizer (K : Type) [Field K] [Finite K]
    (w : List (Fin r)) (u : (Mat A hd hs hp ho K)ˣ)
    (hu : u ∈ rootGroup A hs hp b₀ s₀ K false)
    (hreg : ∀ i, leadingCoordinates A hd hs hp ho K
      (wordUnit A hs hp b₀ s₀ K w * u * (wordUnit A hs hp b₀ s₀ K w)⁻¹) i ≠ 0) :
    wordUnit A hs hp b₀ s₀ K w ∈
      Subgroup.normalizer (rootGroup A hs hp b₀ s₀ K false : Set _) := by
  have hpos : ∀ i j, 0 ≤ (wordRoot A hs hp b₀ s₀ (inverseWord w) (s₀ i)).val j := by
    intro i
    let k := wordRoot A hs hp b₀ s₀ (inverseWord w) (s₀ i)
    have hh := inverse_simple_height_pos_of_leading_ne_zero A hd hs hp ho K w u hu i (hreg i)
    have he : k.val = (wordLinear A hs hp b₀ s₀ w).symm (s₀ i : Roots A).val := by
      dsimp only [k]
      rw [← wordLinear_root, wordLinear_inverseWord]
      rfl
    have hk : 0 < coordinateHeight k.val := by rw [he]; exact hh
    rcases CFSGIntegralNormTwoSigns.norm_two_coordinates_one_sign A hs hp
      (fun j => by rw [hd j]; exact even_two) ho k.val k.property with hp' | hn'
    · exact hp'
    · have hsum : coordinateHeight k.val ≤ 0 := by
        change ∑ j : Fin r, k.val j ≤ 0
        exact Finset.sum_nonpos (fun j _ => hn' j)
      omega
  let N := Subgroup.normalizer (rootGroup A hs hp b₀ s₀ K false :
    Set (Mat A hd hs hp ho K)ˣ)
  have hi : (wordUnit A hs hp b₀ s₀ K w)⁻¹ ∈ N := by
    rw [← wordUnit_inverseWord]
    exact positive_word_mem_normalizer A hd hs hp ho K (inverseWord w) hpos
  simpa only [inv_inv] using N.inv_mem hi

end SymmetricSubgroupAsymptotics.CFSGNormTwoCoordinateRegularLeadingWord
