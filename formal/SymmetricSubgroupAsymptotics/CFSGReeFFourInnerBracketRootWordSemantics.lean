import SymmetricSubgroupAsymptotics.CFSGReeFFourInnerBracketSquareSupports
import SymmetricSubgroupAsymptotics.CFSGNormTwoCharTwoRootWordRewrite

/-! Whole-block semantics of literal selected-root words. Reverse words
represent inverses because the SAME parameter1 root elements are involutions
in characteristic two. Only complete y, reflected-y, C/D/E and T/S blocks
are bound; no individual selected root is assumed exceptional-fixed. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
open scoped Classical
namespace SymmetricSubgroupAsymptotics.CFSGReeFFourInnerBracketRootWordSemantics
open CFSGNormTwoRootPairing CFSGExceptionalCartanPositiveDefinite CFSGExceptionalNormTwoBases
open CFSGNormTwoCoordinateSelectedRootElement CFSGNormTwoCoordinateSelectedRootAdditive
open CFSGReeFFourMiddleSquareBracketRootRelations CFSGReeFFourMiddleSquareRootWordValues
open CFSGReeFFourMiddleSquareSelectedWordTransport CFSGReeFFourInnerBracketSquareSupports
open CFSGFFourE6PositiveRootUnits CFSGSerreQuadraticWeylWord
open TwoLetterWordRewrite
local notation "A" => CartanMatrix.E₆
local notation "hd" => CartanMatrix.E₆_diag
local notation "hs" => CartanMatrix.E₆_transpose
local notation "hp" => E6_positive_definite
local notation "ho" => CartanMatrix.E₆_off_diag_nonpos

variable (K : Type) [CommRing K] [CharP K 2]

def rootValue (w : List (Roots A)) :=
  value (fun k : Roots A => selectedRootElement A hd hs hp ho K k 1) w

theorem rootValue_nil : rootValue K []=1 := rfl

theorem rootValue_cons (k : Roots A) (w : List (Roots A)) :
    rootValue K (k::w)=selectedRootElement A hd hs hp ho K k 1*rootValue K w := rfl

theorem rootValue_append (v w : List (Roots A)) :
    rootValue K (v++w)=rootValue K v*rootValue K w := by
  simp only [rootValue,value,List.map_append,List.prod_append]

private theorem parameter_inverse (k : Roots A) :
    (selectedRootElement A hd hs hp ho K k 1)⁻¹=selectedRootElement A hd hs hp ho K k 1 := by
  rw [selectedRootElement_inverse,CharTwo.neg_eq]

theorem rootValue_reverse (w : List (Roots A)) :
    rootValue K w.reverse=(rootValue K w)⁻¹ := by
  induction w with
  | nil => simp only [List.reverse_nil,rootValue_nil,inv_one]
  | cons k w ih =>
    rw [List.reverse_cons,rootValue_append,ih,rootValue_cons,rootValue_nil,mul_one,
      rootValue_cons,mul_inv_rev,parameter_inverse]

theorem rootValue_map {I : Type*} (R : I → Roots A) (w : List I) :
    rootValue K (w.map R)=value (CFSGNormTwoCharTwoRootWordRewrite.parameter A hd hs hp ho R K) w := by
  simp only [rootValue,value,List.map_map,Function.comp_def,
    CFSGNormTwoCharTwoRootWordRewrite.parameter]

def outerRoots (b : Fin 3) : List (Roots A) :=
  [CFSGReeFFourInnerBracketFixedBlocks.outerRoot b 0,
    CFSGReeFFourInnerBracketFixedBlocks.outerRoot b 1,
    CFSGReeFFourInnerBracketFixedBlocks.outerRoot b 2]

def middleRoots (b : Fin 2) : List (Roots A) :=
  [CFSGReeFFourInnerBracketFixedBlocks.middleRoot b 0,
    CFSGReeFFourInnerBracketFixedBlocks.middleRoot b 1,
    CFSGReeFFourInnerBracketFixedBlocks.middleRoot b 2,
    CFSGReeFFourInnerBracketFixedBlocks.middleRoot b 3]

def yRoots : List (Roots A) := [yRoot 0,yRoot 1,yRoot 2,yRoot 3]

def reflectedRoot (i : Fin 4) : Roots A :=
  ⟨CFSGReeFFourOuterKernelBracketRootData.reflectedY i,
    (CFSGReeFFourOuterKernelBracketRootData.root_properties.1 i).1⟩

def reflectedRoots : List (Roots A) :=
  [reflectedRoot 0,reflectedRoot 1,reflectedRoot 2,reflectedRoot 3]

def squareRoots : List (Roots A) := [bracketRoot 0,bracketRoot 1,bracketRoot 2]

def outerSquareRoots : List (Roots A) :=
  [outerSquareRoot 0,outerSquareRoot 1,outerSquareRoot 2]

theorem value_outerRoots (b : Fin 3) :
    rootValue K (outerRoots b)=CFSGReeFFourInnerBracketFixedBlocks.outerBlock K b := by
  simpa only [outerRoots,rootValue_cons,rootValue_nil,mul_one,mul_assoc,
    CFSGReeFFourInnerBracketFixedBlocks.outerParameter] using
    (CFSGReeFFourInnerBracketFixedBlocks.outerBlock_eq K b).symm

theorem value_middleRoots (b : Fin 2) :
    rootValue K (middleRoots b)=CFSGReeFFourInnerBracketFixedBlocks.middleBlock K b := by
  simpa only [middleRoots,rootValue_cons,rootValue_nil,mul_one,mul_assoc,
    CFSGReeFFourInnerBracketFixedBlocks.middleParameter] using
    (CFSGReeFFourInnerBracketFixedBlocks.middleBlock_eq K b).symm

theorem value_yRoots : rootValue K yRoots=yWord K := by
  simpa only [yRoots,rootValue_cons,rootValue_nil,mul_one,mul_assoc,yParameter] using
    (yWord_eq K).symm

theorem value_squareRoots : rootValue K squareRoots=squareWord K := by
  simpa only [squareRoots,rootValue_cons,rootValue_nil,mul_one,mul_assoc,bracketParameter] using
    (squareWord_eq K).symm

theorem value_outerSquareRoots : rootValue K outerSquareRoots=
    (MulAut.conj (canonicalWord e6Data K [0,5,1])) (squareWord K) := by
  simpa only [outerSquareRoots,rootValue_cons,rootValue_nil,mul_one,mul_assoc,
    outerSquareParameter] using (squareWord_outer_conjugate K).symm

private theorem reflected_parameter (i : Fin 4) :
    (MulAut.conj (canonicalWord e6Data K [0,5,1])) (yParameter K i 1)=
      selectedRootElement A hd hs hp ho K (reflectedRoot i) 1 :=
  selected_word_one K [0,5,1] (yRoot i) (reflectedRoot i)
    (CFSGReeFFourOuterKernelBracketRootData.outer_transport i)

private theorem map_four {G H : Type*} [Monoid G] [Monoid H]
    (f : G →* H) (a b c d : G) : f (a*b*c*d)=f a*f b*f c*f d := by
  rw [map_mul,map_mul,map_mul]

theorem value_reflectedRoots : rootValue K reflectedRoots=
    (MulAut.conj (canonicalWord e6Data K [0,5,1])) (yWord K) := by
  let F := (MulAut.conj (canonicalWord e6Data K [0,5,1])).toMonoidHom
  have hm := map_four F (yParameter K 0 1) (yParameter K 1 1)
    (yParameter K 2 1) (yParameter K 3 1)
  have h0 := reflected_parameter K 0
  have h1 := reflected_parameter K 1
  have h2 := reflected_parameter K 2
  have h3 := reflected_parameter K 3
  have he := (congrArg F (yWord_eq K)).trans (hm.trans
    (congrArg₂ (fun a c => a*c)
      (congrArg₂ (fun a c => a*c) (congrArg₂ (fun a c => a*c) h0 h1) h2) h3))
  simpa only [reflectedRoots,rootValue_cons,rootValue_nil,mul_one,mul_assoc] using he.symm

end SymmetricSubgroupAsymptotics.CFSGReeFFourInnerBracketRootWordSemantics
