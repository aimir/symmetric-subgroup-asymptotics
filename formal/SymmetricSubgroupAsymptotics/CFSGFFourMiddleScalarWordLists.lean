import SymmetricSubgroupAsymptotics.CFSGFFourE6MiddleScalarColumnCertificate
import SymmetricSubgroupAsymptotics.CFSGFFourMiddleWeylWordLists

/-! Literal signed-token bookkeeping for the one selected variable
middle residual. Equality of these lists is not a Weyl-action argument. -/
set_option autoImplicit false
set_option Elab.async false
namespace SymmetricSubgroupAsymptotics.CFSGFFourMiddleScalarWordLists
open CFSGFFourE6MiddleScalarPolynomialData CFSGFFourE6MiddleScalarColumnCertificate
open CFSGFFourMiddleWeylWordLists CFSGFFourE6MiddleWeylColumnAction

private def weylLetters (i : Fin 4) : List Action :=
  [((false,i),(0,0)),((true,i),(0,0)),((false,i),(0,0))]
private def middleLetters : List Action :=
  weylLetters 1++weylLetters 2++weylLetters 1++weylLetters 2
private def longLetters (p : Exponent) : List Action :=
  weylLetters 1++[((false,2),p)]++(weylLetters 1).reverse
private def shortLetters : List Action :=
  weylLetters 2++[((false,1),(0,0))]++(weylLetters 2).reverse
private def firstLetters : List Action := longLetters (0,0)++shortLetters
private def variableLetters : List Action :=
  [((false,1),(1,0)),((false,2),(0,1))]++longLetters (2,1)
private def thirdLetters : List Action :=
  [((false,1),(0,0)),((false,2),(0,0))]++shortLetters

private theorem letters : (List.ofFn actions).reverse=
    firstLetters++middleLetters++variableLetters++middleLetters.reverse++thirdLetters++middleLetters.reverse := by
  decide +kernel

private def wordValue {G : Type*} [Monoid G] (root : Action→G) (l : List Action) : G :=
  (l.map root).prod
private theorem wordValue_append {G : Type*} [Monoid G] (root : Action→G) (l k : List Action) :
    wordValue root (l++k)=wordValue root l*wordValue root k := by
  simp only [wordValue,List.map_append,List.prod_append]
private theorem wordValue_cons {G : Type*} [Monoid G] (root : Action→G) (a : Action) (l : List Action) :
    wordValue root (a::l)=root a*wordValue root l := by
  simp only [wordValue,List.map_cons,List.prod_cons]
private theorem wordValue_singleton {G : Type*} [Monoid G] (root : Action→G) (a : Action) :
    wordValue root [a]=root a := by
  simp only [wordValue,List.map_cons,List.map_nil,List.prod_cons,List.prod_nil,mul_one]
private theorem wordValue_reverse {G : Type*} [Group G] (root : Action→G)
    (hinv : ∀a,(root a)⁻¹=root a) (l : List Action) :
    wordValue root l.reverse=(wordValue root l)⁻¹ := by
  induction l with
  | nil => simp only [List.reverse_nil,wordValue,List.map_nil,List.prod_nil,inv_one]
  | cons a l ih =>
    rw [List.reverse_cons,wordValue_append,ih,wordValue_singleton,wordValue_cons,mul_inv_rev,hinv]

def rootOne {G : Type*} (root : Action→G) (a : Bool×Fin 4) : G := root (a,(0,0))

private theorem wordValue_weyl {G : Type*} [Group G] (root : Action→G) (i : Fin 4) :
    wordValue root (weylLetters i)=rootOne root (false,i)*rootOne root (true,i)*rootOne root (false,i) := by
  simp only [wordValue,weylLetters,rootOne,List.map_cons,List.map_nil,List.prod_cons,List.prod_nil,mul_one,mul_assoc]

def residualValue {G : Type*} [Group G] (root : Action→G) : G :=
  (longValue (rootOne root)*shortValue (rootOne root))*middleValue (rootOne root)*
    (root ((false,1),(1,0))*root ((false,2),(0,1))*
      ((rootOne root (false,1)*rootOne root (true,1)*rootOne root (false,1))*
        root ((false,2),(2,1))*(rootOne root (false,1)*rootOne root (true,1)*rootOne root (false,1))⁻¹))*
    (middleValue (rootOne root))⁻¹*
    (rootOne root (false,1)*rootOne root (false,2)*shortValue (rootOne root))*
    (middleValue (rootOne root))⁻¹

theorem residual_word_value {G : Type*} [Group G] (root : Action→G)
    (hinv : ∀a,(root a)⁻¹=root a) :
    actionWord (fun i : Fin 68=>root (actions i))=residualValue root := by
  change (List.ofFn (root∘actions)).reverse.prod=_
  rw [←List.map_ofFn,←List.map_reverse]
  change wordValue root ((List.ofFn actions).reverse)=_
  rw [letters]
  have hm : wordValue root middleLetters=middleValue (rootOne root) := by
    simp only [middleLetters,wordValue_append,wordValue_weyl,middleValue]
  have hl (p : Exponent) : wordValue root (longLetters p)=
      (rootOne root (false,1)*rootOne root (true,1)*rootOne root (false,1))*root ((false,2),p)*
        (rootOne root (false,1)*rootOne root (true,1)*rootOne root (false,1))⁻¹ := by
    rw [longLetters,wordValue_append,wordValue_append,wordValue_reverse root hinv,
      wordValue_singleton,wordValue_weyl]
  have hp : wordValue root shortLetters=shortValue (rootOne root) := by
    rw [shortLetters,wordValue_append,wordValue_append,wordValue_reverse root hinv,
      wordValue_singleton,wordValue_weyl]
    rfl
  simp only [firstLetters,variableLetters,thirdLetters,wordValue_append,wordValue_reverse root hinv,
    hm,hl,hp,wordValue_cons]
  simp only [wordValue,List.map_nil,List.prod_nil,mul_one,rootOne]
  dsimp only [residualValue,longValue,rootOne]

end SymmetricSubgroupAsymptotics.CFSGFFourMiddleScalarWordLists
