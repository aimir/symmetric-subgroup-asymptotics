import SymmetricSubgroupAsymptotics.CFSGReeFFourMiddleNegativeCoordinateFamily

/-! A word whose three middle simple columns are nonpositive carries the
literal negative middle family back to the positive group. The finite
certificate concerns only six integral root degrees; all parameters and
all subsequent conjugations remain arbitrary. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
open scoped Classical Matrix
namespace SymmetricSubgroupAsymptotics.CFSGReeFFourNegativeMiddleSeedTransport
open CFSGExceptionalNormTwoBases CFSGExceptionalCartanPositiveDefinite
open CFSGNormTwoRootPairing CFSGNormTwoCoordinateLatticeWord CFSGSignedCartanReflections
open CFSGNormTwoGeckWeylLatticeLinear CFSGNormTwoGeckWeylWordAlgebra
open CFSGNormTwoGeckWeylWordDegree CFSGNormTwoCoordinateWeylRootMembership
open CFSGNormTwoCoordinateOutsideWordConjugation CFSGNonpositiveCoordinateCone
open CFSGReeFFourFieldParameters CFSGReeFFourPositiveMatrixWordValues
open CFSGTwistedE6GeckPositiveTwist
local notation "A" => CartanMatrix.E₆
local notation "hd" => CartanMatrix.E₆_diag
local notation "hs" => CartanMatrix.E₆_transpose
local notation "hp" => E6_positive_definite
local notation "ho" => CartanMatrix.E₆_off_diag_nonpos
local notation "b₀" => coordinateBase A hd hs hp ho
local notation "s₀" => coordinateIndexEquiv A hd hs hp ho
local notation "W" => ([2,4,3,2,4,3] : List (Fin 6))

private def factors : List (List (Fin 6)×Fin 6) :=
  [([],2),([],4),([],3),([2,4],3),([3],2),([3],4)]

private theorem factor_degrees : ∀p∈factors,
    (∀j,(latticeWord A (W++p.1)*ᵥ(Pi.single p.2 (1:ℤ) : Fin 6→ℤ)) j≤0) ∧
    (∀j,(latticeWord A (W++p.1)*ᵥ(Pi.single p.2 (1:ℤ) : Fin 6→ℤ)) j≠0→
      j=2∨j=3∨j=4) := by
  unfold factors
  decide

private theorem factor_degree_value (v : List (Fin 6)) (i : Fin 6) :
    (wordRoot A hs hp b₀ s₀ (W++v) (s₀ i)).val=
      latticeWord A (W++v)*ᵥ(Pi.single i (1:ℤ) : Fin 6→ℤ) := by
  have hL := LinearMap.congr_fun (latticeWord_linear A hd hs hp ho (W++v))
    (Pi.single i (1:ℤ))
  change latticeWord A (W++v)*ᵥ(Pi.single i (1:ℤ))=
    wordLinear A hs hp b₀ s₀ (W++v) (Pi.single i (1:ℤ)) at hL
  exact (wordLinear_root A hs hp b₀ s₀ (W++v) (s₀ i)).symm.trans hL.symm

private theorem conjugate_factor_positive (K : Type) [Field K]
    (w : List (Fin 6))
    (hall : ∀i,i=2∨i=3∨i=4→∀j,(wordRoot A hs hp b₀ s₀ w (s₀ i)).val j≤0)
    (p : List (Fin 6)×Fin 6) (hpick : p∈factors) (t : K) :
    wordUnit A hs hp b₀ s₀ K w*
      (wordUnit A hs hp b₀ s₀ K W*rootWord A hd hs hp ho K p.1 p.2 t*
        (wordUnit A hs hp b₀ s₀ K W)⁻¹)*
      (wordUnit A hs hp b₀ s₀ K w)⁻¹∈Positive K := by
  rw [conjugate_rootWord_eq,conjugate_rootWord_eq]
  apply positive_word_mem A hd hs hp ho K (w++(W++p.1)) p.2 t
  let k := wordRoot A hs hp b₀ s₀ (W++p.1) (s₀ p.2)
  have hk : ∀j,k.val j≤0 := by
    dsimp only [k]
    rw [factor_degree_value]
    exact (factor_degrees p hpick).1
  have hsupport : ∀j,k.val j≠0→j=2∨j=3∨j=4 := by
    dsimp only [k]
    rw [factor_degree_value]
    exact (factor_degrees p hpick).2
  have hcolumns (i : Fin 6) (hi : (-k.val) i≠0) :
      ∀j,wordLinear A hs hp b₀ s₀ w (Pi.single i (1:ℤ)) j≤0 := by
    have hki : k.val i≠0 := by simpa only [Pi.neg_apply,neg_ne_zero] using hi
    have he := wordLinear_root A hs hp b₀ s₀ w (s₀ i)
    change wordLinear A hs hp b₀ s₀ w (Pi.single i (1:ℤ))=
      (wordRoot A hs hp b₀ s₀ w (s₀ i)).val at he
    rw [he]
    exact hall i (hsupport i hki)
  have hn := linearMap_nonpositive_of_support_columns
    (wordLinear A hs hp b₀ s₀ w).toLinearMap (-k.val)
    (fun i=>neg_nonneg.mpr (hk i)) hcolumns
  rw [wordRoot_append]
  intro j
  have he := wordLinear_root A hs hp b₀ s₀ w k
  rw [←he]
  have hh := hn j
  simp only [map_neg,Pi.neg_apply] at hh
  exact neg_nonpos.mp hh

theorem conjugate_negative_middle_positive (m : ℕ) (w : List (Fin 6))
    (hall : ∀i,i=2∨i=3∨i=4→∀j,(wordRoot A hs hp b₀ s₀ w (s₀ i)).val j≤0)
    (a b c d : Field m) :
    wordUnit A hs hp b₀ s₀ (Field m) w*
      (wordUnit A hs hp b₀ s₀ (Field m) W*coordinateMiddleWord m a b c d*
        (wordUnit A hs hp b₀ s₀ (Field m) W)⁻¹)*
      (wordUnit A hs hp b₀ s₀ (Field m) w)⁻¹∈Positive (Field m) := by
  let C := ((MulAut.conj (wordUnit A hs hp b₀ s₀ (Field m) w)).toMonoidHom).comp
    (MulAut.conj (wordUnit A hs hp b₀ s₀ (Field m) W)).toMonoidHom
  have hfactor (p : List (Fin 6)×Fin 6) (hpick : p∈factors) (t : Field m) :
      C (rootWord A hd hs hp ho (Field m) p.1 p.2 t)∈Positive (Field m) :=
    conjugate_factor_positive (Field m) w hall p hpick t
  change C (coordinateMiddleWord m a b c d)∈Positive (Field m)
  simp only [coordinateMiddleWord,map_mul]
  exact (Positive (Field m)).mul_mem
    ((Positive (Field m)).mul_mem
      ((Positive (Field m)).mul_mem
        ((Positive (Field m)).mul_mem (hfactor ([],2) (by decide) a)
          (hfactor ([],4) (by decide) a)) (hfactor ([],3) (by decide) b))
      (hfactor ([2,4],3) (by decide) d))
    ((Positive (Field m)).mul_mem (hfactor ([3],2) (by decide) c)
      (hfactor ([3],4) (by decide) c))

end SymmetricSubgroupAsymptotics.CFSGReeFFourNegativeMiddleSeedTransport
