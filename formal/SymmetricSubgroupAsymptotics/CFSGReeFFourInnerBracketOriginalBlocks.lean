import SymmetricSubgroupAsymptotics.CFSGReeFFourInnerBracketFixedBlocks
import SymmetricSubgroupAsymptotics.CFSGReeFFourBinaryMiddleSquareSaving

/-! Literal original fixed-group versions of the five designated blocks.
Fixedness is intrinsic to these conjugates. The square corrections are
proved derived using the checked actual middle-square commutator, rather
than any membership assertion about individual selected E6 parameters. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
open scoped Classical
namespace SymmetricSubgroupAsymptotics.CFSGReeFFourInnerBracketOriginalBlocks
open CFSGReeFFourMiddleSquareOriginalWords CFSGReeFFourMiddleSquareRootWordValues
open CFSGReeFFourMiddleSquareCommutator CFSGReeFFourBinaryMiddleSquareSaving
open CFSGReeFFourMiddleDerivedFiveWord CFSGReeFFourOuterThreeWord
open CFSGReeFFourRelativePositiveSubgroups CFSGReeFFourRelativeWeylRawWords
open CFSGReeFFourFieldParameters CFSGReeFFourFixedModelEquivalence
open CFSGReeFFourFixedPositiveFamilies CFSGFFourOriginalMiddleWords
open CFSGReeFFourOuterFixedRoot CFSGReeFFourMiddleFixedWords
open CFSGFFourE6PositiveRootUnits CFSGSerreQuadraticMatrix CFSGSerreQuadraticWeylWord

private abbrev W (m : ℕ) (s : List (Fin 6)) := canonicalWord e6Data (Field m) s
private abbrev R (m : ℕ) (i : Fin 6) := canonicalRoot e6Data (Field m) false i 1

private theorem word_append (m : ℕ) (s t : List (Fin 6)) :
    W m (s++t)=W m s*W m t := by
  induction s with
  | nil => simp only [W,List.nil_append,canonicalWord,one_mul]
  | cons i s ih =>
    change canonicalWeyl e6Data (Field m) i*W m (s++t) =
      (canonicalWeyl e6Data (Field m) i*W m s)*W m t
    rw [ih,mul_assoc]

private theorem raw_outer (m : ℕ) : fixedRawHom m (outerFixedWeyl m)=W m [0,5,1] := by
  rw [fixedRawHom_apply]
  exact rawHom_outerRelativeWeyl m

private theorem raw_middle (m : ℕ) : fixedRawHom m (middleFixedWeyl m)=W m [2,4,3,2,4,3] := by
  rw [fixedRawHom_apply]
  exact rawHom_middleRelativeWeyl m

private theorem raw_x (m : ℕ) :
    fixedRawHom m (outerInvolution m)=R m 0*R m 5*R m 1 := by
  rw [fixedRawHom_apply]
  change rawHom (Field m) (CFSGReeFFourOuterFixedRoot.outerWord m 1)=_
  simp only [CFSGReeFFourOuterFixedRoot.outerWord,map_mul,rawHom_root,map_one,
    folded_positive_root]
  rfl

def outerConjugator (m : ℕ) : Fin 3 → originalModelFixed m :=
  ![middleFixedWeyl m, outerFixedWeyl m*middleFixedWeyl m,
    middleFixedWeyl m*outerFixedWeyl m*middleFixedWeyl m]

def middleConjugator (m : ℕ) : Fin 2 → originalModelFixed m :=
  ![middleFixedWeyl m*outerFixedWeyl m,
    outerFixedWeyl m*middleFixedWeyl m*outerFixedWeyl m]

def actualOuterBlock (m : ℕ) (b : Fin 3) : originalModelFixed m :=
  (MulAut.conj (outerConjugator m b)) (outerInvolution m)

def actualMiddleBlock (m : ℕ) (b : Fin 2) : originalModelFixed m :=
  (MulAut.conj (middleConjugator m b)) (fourCycle m)

theorem raw_outerConjugator (m : ℕ) (b : Fin 3) :
    fixedRawHom m (outerConjugator m b)=
      W m (CFSGReeFFourInnerBracketFixedBlocks.outerWord b) := by
  fin_cases b
  · exact raw_middle m
  · change fixedRawHom m (outerFixedWeyl m*middleFixedWeyl m)=
      W m ([0,5,1]++[2,4,3,2,4,3])
    rw [map_mul,raw_outer,raw_middle]
    exact (word_append m _ _).symm
  · change fixedRawHom m ((middleFixedWeyl m*outerFixedWeyl m)*middleFixedWeyl m)=
      W m (([2,4,3,2,4,3]++[0,5,1])++[2,4,3,2,4,3])
    rw [map_mul,map_mul,raw_middle,raw_outer,←word_append,←word_append]

theorem raw_middleConjugator (m : ℕ) (b : Fin 2) :
    fixedRawHom m (middleConjugator m b)=
      W m (CFSGReeFFourInnerBracketFixedBlocks.middleWord b) := by
  fin_cases b
  · change fixedRawHom m (middleFixedWeyl m*outerFixedWeyl m)=
      W m ([2,4,3,2,4,3]++[0,5,1])
    rw [map_mul,raw_middle,raw_outer]
    exact (word_append m _ _).symm
  · change fixedRawHom m ((outerFixedWeyl m*middleFixedWeyl m)*outerFixedWeyl m)=
      W m (([0,5,1]++[2,4,3,2,4,3])++[0,5,1])
    rw [map_mul,map_mul,raw_outer,raw_middle,←word_append,←word_append]

private theorem map_conjugate {G H : Type*} [Group G] [Group H]
    (f : G →* H) (a b : G) : f ((MulAut.conj a) b)=(MulAut.conj (f a)) (f b) := by
  change f (a*b*a⁻¹)=f a*f b*(f a)⁻¹
  rw [map_mul,map_mul,map_inv]

theorem raw_actualOuterBlock (m : ℕ) (b : Fin 3) :
    fixedRawHom m (actualOuterBlock m b)=
      CFSGReeFFourInnerBracketFixedBlocks.outerBlock (Field m) b := by
  rw [actualOuterBlock,map_conjugate,raw_outerConjugator,raw_x]
  rfl

theorem raw_actualMiddleBlock (m : ℕ) (b : Fin 2) :
    fixedRawHom m (actualMiddleBlock m b)=
      CFSGReeFFourInnerBracketFixedBlocks.middleBlock (Field m) b := by
  rw [actualMiddleBlock,map_conjugate,raw_middleConjugator,raw_fourCycle]
  rfl

private theorem conjugate_pow_two {G : Type*} [Group G] (a b : G) :
    ((MulAut.conj a) b)^2=a*b^2*a⁻¹ := by
  change (a*b*a⁻¹)^2=a*b^2*a⁻¹
  rw [pow_two,pow_two]
  group

theorem raw_T_square (m : ℕ) :
    fixedRawHom m ((actualMiddleBlock m 0)^2)=squareWord (Field m) := by
  rw [actualMiddleBlock,conjugate_pow_two]
  exact raw_conjugateSquare m

theorem raw_S_square (m : ℕ) :
    fixedRawHom m ((actualMiddleBlock m 1)^2)=
      (MulAut.conj (W m [0,5,1])) (squareWord (Field m)) := by
  have he : (actualMiddleBlock m 1)^2=
      outerFixedWeyl m*(actualMiddleBlock m 0)^2*(outerFixedWeyl m)⁻¹ := by
    change ((outerFixedWeyl m*middleFixedWeyl m*outerFixedWeyl m)*fourCycle m*
        (outerFixedWeyl m*middleFixedWeyl m*outerFixedWeyl m)⁻¹)^2 =
      outerFixedWeyl m*((middleFixedWeyl m*outerFixedWeyl m)*fourCycle m*
        (middleFixedWeyl m*outerFixedWeyl m)⁻¹)^2*(outerFixedWeyl m)⁻¹
    rw [pow_two,pow_two]
    group
  rw [he,map_mul,map_mul,map_inv,raw_outer,raw_T_square]
  rfl

theorem middle_square_mem_derived (m : ℕ) (b : Fin 2) :
    (actualMiddleBlock m b)^2 ∈ commutator (originalModelFixed m) := by
  rw [actualMiddleBlock,conjugate_pow_two]
  have h := (inferInstance : (commutator (originalModelFixed m)).Normal).conj_mem'
    _ (square_mem_derived m) ((middleConjugator m b)⁻¹)
  simpa only [inv_inv] using h

private theorem abelian_conjugate {G B : Type*} [Group G] [CommGroup B]
    (f : G →* B) (a b : G) : f ((MulAut.conj a) b)=f b := by
  rw [map_conjugate]
  change f a*f b*(f a)⁻¹=f b
  rw [mul_comm (f a) (f b),mul_assoc,mul_inv_cancel,mul_one]

theorem outer_image {B : Type*} [CommGroup B] (m : ℕ)
    (f : originalModelFixed m →* B) (b : Fin 3) :
    f (actualOuterBlock m b)=f (outerInvolution m) :=
  abelian_conjugate f _ _

theorem middle_image {B : Type*} [CommGroup B] (m : ℕ)
    (f : originalModelFixed m →* B) (b : Fin 2) :
    f (actualMiddleBlock m b)=f (fourCycle m) :=
  abelian_conjugate f _ _

def candidate (m : ℕ) : originalModelFixed m :=
  (actualMiddleBlock m 1)⁻¹*(actualMiddleBlock m 0)⁻¹*
    actualOuterBlock m 2*actualOuterBlock m 1*actualOuterBlock m 0

theorem candidate_image {B : Type*} [CommGroup B] (m : ℕ)
    (f : originalModelFixed m →* B) : f (candidate m)=f (outerInvolution m) := by
  have hx : (f (outerInvolution m))^2=1 := by
    rw [←map_pow,outerInvolution_square,map_one]
  have hy := square_image_one m f
  simp only [candidate,map_mul,map_inv,outer_image,middle_image]
  calc
    _ = ((f (fourCycle m))^2)⁻¹*(f (outerInvolution m))^2*f (outerInvolution m) := by
      rw [pow_two,pow_two,mul_inv_rev]
      simp only [mul_assoc]
    _ = _ := by rw [hx,hy]; simp only [inv_one,one_mul]

end SymmetricSubgroupAsymptotics.CFSGReeFFourInnerBracketOriginalBlocks
