import SymmetricSubgroupAsymptotics.CFSGFFourE6DiagramFixed
import SymmetricSubgroupAsymptotics.CFSGTwistedE6GeckRelativeWordTwist

/-! Actual relative E6 Weyl words belong to the folded F4 matrix group.
The two paired orbit reflections are the literal canonical F4 Weyl words,
proved by collecting only commuting orthogonal signed root factors. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
open scoped Classical
namespace SymmetricSubgroupAsymptotics.CFSGFFourE6RelativeWords
open CFSGFFourSerreMatrices CFSGFFourE6PositiveRootUnits CFSGFFourE6NegativeRootUnits
open CFSGSerreQuadraticMatrix CFSGSerreQuadraticWeylWord
open CFSGExceptionalNormTwoBases CFSGExceptionalCartanPositiveDefinite
open CFSGNormTwoGeckOrthogonalWeyl
open CFSGTwistedE6RelativeWeylOrbits CFSGTwistedE6FixedWordClassification

private theorem collect_pair {G : Type*} [Group G] (a b c d : G)
    (hbc : Commute b c) (hba : Commute b a) (hda : Commute d a) :
    (a*b)*(c*d)*(a*b) = (a*c*a)*(b*d*b) := by
  rw [hbc.mul_mul_mul_comm a d]
  calc
    (a*c*(b*d))*(a*b) = (a*c)*((b*d)*a)*b := by simp only [mul_assoc]
    _ = (a*c)*(a*(b*d))*b := by rw [(hba.mul_left hda).eq]
    _ = (a*c*a)*(b*d*b) := by simp only [mul_assoc]

private theorem orthogonal_weyl_pair (K : Type) [Field K] (i j : Fin 6)
    (hij : CFSGGeckSerreRepresentation.cartan E6Base E6Index i j=0) :
    (canonicalRoot e6Data K false i 1 * canonicalRoot e6Data K false j 1) *
      (canonicalRoot e6Data K true i (-1) * canonicalRoot e6Data K true j (-1)) *
      (canonicalRoot e6Data K false i 1 * canonicalRoot e6Data K false j 1) =
      canonicalWeyl e6Data K i * canonicalWeyl e6Data K j := by
  exact collect_pair _ _ _ _
    (orthogonal_signed_roots CartanMatrix.E₆ CartanMatrix.E₆_transpose E6_positive_definite
      E6Base E6Index K i j hij true false (-1) 1).symm
    (orthogonal_signed_roots CartanMatrix.E₆ CartanMatrix.E₆_transpose E6_positive_definite
      E6Base E6Index K i j hij false false 1 1).symm
    (orthogonal_signed_roots CartanMatrix.E₆ CartanMatrix.E₆_transpose E6_positive_definite
      E6Base E6Index K i j hij false true 1 (-1)).symm

theorem foldedWeyl_eq_orbitWord (K : Type) [Field K] (a : Fin 4) :
    canonicalWeyl realizationData K a = canonicalWord e6Data K (orbitWord a) := by
  simp only [canonicalWeyl,folded_positive_root,folded_negative_root]
  fin_cases a
  · change (canonicalRoot e6Data K false 0 1 * canonicalRoot e6Data K false 5 1) *
      (canonicalRoot e6Data K true 0 (-1) * canonicalRoot e6Data K true 5 (-1)) *
      (canonicalRoot e6Data K false 0 1 * canonicalRoot e6Data K false 5 1) =
      canonicalWeyl e6Data K 0 * (canonicalWeyl e6Data K 5 * 1)
    simpa only [mul_one] using
      orthogonal_weyl_pair K 0 5 (by rw [E6_cartan]; decide)
  · change (canonicalRoot e6Data K false 2 1 * canonicalRoot e6Data K false 4 1) *
      (canonicalRoot e6Data K true 2 (-1) * canonicalRoot e6Data K true 4 (-1)) *
      (canonicalRoot e6Data K false 2 1 * canonicalRoot e6Data K false 4 1) =
      canonicalWeyl e6Data K 2 * (canonicalWeyl e6Data K 4 * 1)
    simpa only [mul_one] using
      orthogonal_weyl_pair K 2 4 (by rw [E6_cartan]; decide)
  · change canonicalWeyl e6Data K 3 = canonicalWeyl e6Data K 3 * 1
    exact (mul_one _).symm
  · change canonicalWeyl e6Data K 1 = canonicalWeyl e6Data K 1 * 1
    exact (mul_one _).symm

private theorem word_append (K : Type) [Field K] (v w : List (Fin 6)) :
    canonicalWord e6Data K (v++w)=canonicalWord e6Data K v*canonicalWord e6Data K w := by
  induction v with
  | nil => simp only [List.nil_append,canonicalWord,one_mul]
  | cons i v ih => rw [List.cons_append,canonicalWord,ih,canonicalWord,mul_assoc]

theorem foldedWord_eq_relativeWord (K : Type) [Field K] (w : List (Fin 4)) :
    canonicalWord realizationData K w = canonicalWord e6Data K (expandRelative w) := by
  induction w with
  | nil => rfl
  | cons a w ih => rw [canonicalWord,foldedWeyl_eq_orbitWord,ih,expandRelative,word_append]

theorem relativeWord_mem_folded (K : Type) [Field K] (w : List (Fin 4)) :
    canonicalWord e6Data K (expandRelative w) ∈ canonicalElementaryGroup realizationData K := by
  rw [←foldedWord_eq_relativeWord]
  have hroot (neg : Bool) (i : Fin 4) (t : K) :
      canonicalRoot realizationData K neg i t ∈ canonicalElementaryGroup realizationData K :=
    Subgroup.subset_closure ⟨neg,i,t,rfl⟩
  have hweyl (i : Fin 4) : canonicalWeyl realizationData K i ∈
      canonicalElementaryGroup realizationData K :=
    (canonicalElementaryGroup realizationData K).mul_mem
      ((canonicalElementaryGroup realizationData K).mul_mem (hroot false i 1) (hroot true i (-1)))
      (hroot false i 1)
  induction w with
  | nil => exact (canonicalElementaryGroup realizationData K).one_mem
  | cons i w ih => exact (canonicalElementaryGroup realizationData K).mul_mem (hweyl i) ih

end SymmetricSubgroupAsymptotics.CFSGFFourE6RelativeWords
