import SymmetricSubgroupAsymptotics.CFSGReeFFourRelativeWeylPositiveWords
import SymmetricSubgroupAsymptotics.CFSGNonpositiveCoordinateCone

/-! The literal middle relative Weyl word sends the selected middle
positive root factors into the ambient negative subgroup. Only its three
middle simple columns are evaluated; the higher roots follow by the
integer nonpositive-coordinate cone, before field reduction. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
open scoped Classical Matrix
namespace SymmetricSubgroupAsymptotics.CFSGReeFFourMiddleNegativeRootWords
open CFSGExceptionalNormTwoBases CFSGExceptionalCartanPositiveDefinite
open CFSGNormTwoRootPairing CFSGNormTwoCoordinateLatticeWord CFSGSignedCartanReflections
open CFSGNormTwoGeckWeylLatticeLinear CFSGNormTwoGeckWeylWordAlgebra
open CFSGNormTwoGeckWeylWordDegree CFSGNormTwoCoordinateWeylRootMembership
open CFSGNormTwoCoordinateOutsideWordConjugation CFSGNonpositiveCoordinateCone
open CFSGE6GeckMiddleRootDegrees CFSGTwistedE6GeckPositiveTwist
local notation "A" => CartanMatrix.E₆
local notation "hd" => CartanMatrix.E₆_diag
local notation "hs" => CartanMatrix.E₆_transpose
local notation "hp" => E6_positive_definite
local notation "ho" => CartanMatrix.E₆_off_diag_nonpos
local notation "b₀" => coordinateBase A hd hs hp ho
local notation "s₀" => coordinateIndexEquiv A hd hs hp ho
local notation "W" => ([2,4,3,2,4,3] : List (Fin 6))

private theorem middle_simple_lattice (i : Fin 6) (hi : i=2∨i=3∨i=4) :
    ∀j,(latticeWord A W*ᵥ(Pi.single i (1:ℤ) : Fin 6→ℤ)) j≤0 := by
  rcases hi with rfl|rfl|rfl <;> decide

theorem middle_conjugate_rootWord_mem_negative (K : Type) [Field K]
    (w : List (Fin 6)) (i : Fin 6) (t : K)
    (hpos : ∀j,0≤(wordRoot A hs hp b₀ s₀ w (s₀ i)).val j)
    (hsupport : ∀j,(wordRoot A hs hp b₀ s₀ w (s₀ i)).val j≠0→j=2∨j=3∨j=4) :
    wordUnit A hs hp b₀ s₀ K W*rootWord A hd hs hp ho K w i t*
      (wordUnit A hs hp b₀ s₀ K W)⁻¹∈Negative K := by
  rw [conjugate_rootWord_eq]
  apply negative_word_mem A hd hs hp ho K (W++w) i t
  rw [wordRoot_append]
  have hcolumns (j : Fin 6)
      (hj : (wordRoot A hs hp b₀ s₀ w (s₀ i)).val j≠0) :
      ∀k,wordLinear A hs hp b₀ s₀ W (Pi.single j (1:ℤ)) k≤0 := by
    have he := LinearMap.congr_fun (latticeWord_linear A hd hs hp ho W)
      (Pi.single j (1:ℤ))
    change latticeWord A W*ᵥ(Pi.single j (1:ℤ))=
      wordLinear A hs hp b₀ s₀ W (Pi.single j (1:ℤ)) at he
    rw [←he]
    exact middle_simple_lattice j (hsupport j hj)
  have hn := linearMap_nonpositive_of_support_columns
    (wordLinear A hs hp b₀ s₀ W).toLinearMap
    (wordRoot A hs hp b₀ s₀ w (s₀ i)).val hpos hcolumns
  intro j
  have he := wordLinear_root A hs hp b₀ s₀ W (wordRoot A hs hp b₀ s₀ w (s₀ i))
  calc
    (wordRoot A hs hp b₀ s₀ W (wordRoot A hs hp b₀ s₀ w (s₀ i))).val j=
        wordLinear A hs hp b₀ s₀ W (wordRoot A hs hp b₀ s₀ w (s₀ i)).val j :=
      congrArg (fun x : Fin 6→ℤ=>x j) he.symm
    _≤0 := hn j

theorem middle_conjugate_simple_mem_negative (K : Type) [Field K]
    (i : Fin 6) (hi : i=2∨i=3∨i=4) (t : K) :
    wordUnit A hs hp b₀ s₀ K W*rootWord A hd hs hp ho K [] i t*
      (wordUnit A hs hp b₀ s₀ K W)⁻¹∈Negative K := by
  apply middle_conjugate_rootWord_mem_negative K [] i t
  · change ∀j,0≤(Pi.single i (1:ℤ) : Fin 6→ℤ) j
    intro j
    simp only [Pi.single_apply]
    split_ifs <;> norm_num
  · change ∀j,(Pi.single i (1:ℤ) : Fin 6→ℤ) j≠0→j=2∨j=3∨j=4
    intro j hj
    have hij : i=j := by
      by_contra h
      exact hj (by simp [h])
    exact hij ▸ hi

theorem middle_conjugate_long_mem_negative (K : Type) [Field K] (t : K) :
    wordUnit A hs hp b₀ s₀ K W*rootWord A hd hs hp ho K [2,4] 3 t*
      (wordUnit A hs hp b₀ s₀ K W)⁻¹∈Negative K := by
  apply middle_conjugate_rootWord_mem_negative K [2,4] 3 t
  · change ∀j,0≤(wordRoot A hs hp E6Base E6Index [2,4] (E6Index 3)).val j
    rw [highest_root_degree]
    decide
  · change ∀j,(wordRoot A hs hp E6Base E6Index [2,4] (E6Index 3)).val j≠0→_
    rw [highest_root_degree]
    decide

theorem middle_conjugate_pair_factor_mem_negative (K : Type) [Field K]
    (i : Fin 6) (hi : i=2∨i=4) (t : K) :
    wordUnit A hs hp b₀ s₀ K W*rootWord A hd hs hp ho K [3] i t*
      (wordUnit A hs hp b₀ s₀ K W)⁻¹∈Negative K := by
  apply middle_conjugate_rootWord_mem_negative K [3] i t
  · rcases hi with rfl|rfl
    · change ∀j,0≤(wordRoot A hs hp E6Base E6Index [3] (E6Index 2)).val j
      rw [paired_first_degree]
      decide
    · change ∀j,0≤(wordRoot A hs hp E6Base E6Index [3] (E6Index 4)).val j
      rw [paired_second_degree]
      decide
  · rcases hi with rfl|rfl
    · change ∀j,(wordRoot A hs hp E6Base E6Index [3] (E6Index 2)).val j≠0→_
      rw [paired_first_degree]
      decide
    · change ∀j,(wordRoot A hs hp E6Base E6Index [3] (E6Index 4)).val j≠0→_
      rw [paired_second_degree]
      decide

end SymmetricSubgroupAsymptotics.CFSGReeFFourMiddleNegativeRootWords
