import SymmetricSubgroupAsymptotics.CFSGFFourE6MiddleWeylColumnAction

/-! Literal finite-letter bookkeeping for the constant middle word.
The 56-letter identity here only identifies the tested right-hand word
with its three factors; equality to the 12-letter word still requires
all 26 actual-action certificates. -/
set_option autoImplicit false
set_option Elab.async false
namespace SymmetricSubgroupAsymptotics.CFSGFFourMiddleWeylWordLists
open CFSGFFourE6MiddleWeylColumnPilot CFSGFFourE6MiddleWeylColumnAction
private def weylLetters (i : Fin 4) : List (Bool×Fin 4) :=
  [(false,i),(true,i),(false,i)]
private def middleLetters : List (Bool×Fin 4) :=
  weylLetters 1++weylLetters 2++weylLetters 1++weylLetters 2
private def longLetters : List (Bool×Fin 4) :=
  weylLetters 1++[(false,2)]++(weylLetters 1).reverse
private def shortLetters : List (Bool×Fin 4) :=
  weylLetters 2++[(false,1)]++(weylLetters 2).reverse
private def firstLetters : List (Bool×Fin 4) := longLetters++shortLetters
private def secondLetters : List (Bool×Fin 4) := [(false,1),(false,2)]++longLetters
private def thirdLetters : List (Bool×Fin 4) := [(false,1),(false,2)]++shortLetters

private theorem left_letters : (List.ofFn leftActions).reverse=middleLetters := by decide
private theorem right_letters : (List.ofFn rightActions).reverse=
    firstLetters++middleLetters++secondLetters++middleLetters.reverse++thirdLetters := by decide

private def wordValue {G : Type*} [Monoid G] (root : Bool×Fin 4→G)
    (l : List (Bool×Fin 4)) : G := (l.map root).prod
private theorem wordValue_append {G : Type*} [Monoid G] (root : Bool×Fin 4→G)
    (l k : List (Bool×Fin 4)) : wordValue root (l++k)=wordValue root l*wordValue root k := by
  simp only [wordValue,List.map_append,List.prod_append]
private theorem wordValue_cons {G : Type*} [Monoid G] (root : Bool×Fin 4→G)
    (a : Bool×Fin 4) (l : List (Bool×Fin 4)) :
    wordValue root (a::l)=root a*wordValue root l := by
  simp only [wordValue,List.map_cons,List.prod_cons]
private theorem wordValue_singleton {G : Type*} [Monoid G] (root : Bool×Fin 4→G)
    (a : Bool×Fin 4) : wordValue root [a]=root a := by
  simp only [wordValue,List.map_cons,List.map_nil,List.prod_cons,List.prod_nil,mul_one]
private theorem wordValue_reverse {G : Type*} [Group G] (root : Bool×Fin 4→G)
    (hinv : ∀a,(root a)⁻¹=root a) (l : List (Bool×Fin 4)) :
    wordValue root l.reverse=(wordValue root l)⁻¹ := by
  induction l with
  | nil=>simp only [List.reverse_nil,wordValue,List.map_nil,List.prod_nil,inv_one]
  | cons a l ih=>
    rw [List.reverse_cons,wordValue_append,ih]
    rw [wordValue_singleton,wordValue_cons,mul_inv_rev,hinv]
private theorem wordValue_weyl {G : Type*} [Monoid G] (root : Bool×Fin 4→G) (i : Fin 4) :
    wordValue root (weylLetters i)=root (false,i)*root (true,i)*root (false,i) := by
  simp only [wordValue,weylLetters,List.map_cons,List.map_nil,List.prod_cons,List.prod_nil,mul_one,mul_assoc]

def middleValue {G : Type*} [Group G] (root : Bool×Fin 4→G) : G :=
  (root (false,1)*root (true,1)*root (false,1))*
    (root (false,2)*root (true,2)*root (false,2))*
    (root (false,1)*root (true,1)*root (false,1))*
    (root (false,2)*root (true,2)*root (false,2))
def longValue {G : Type*} [Group G] (root : Bool×Fin 4→G) : G :=
  (root (false,1)*root (true,1)*root (false,1))*root (false,2)*
    (root (false,1)*root (true,1)*root (false,1))⁻¹
def shortValue {G : Type*} [Group G] (root : Bool×Fin 4→G) : G :=
  (root (false,2)*root (true,2)*root (false,2))*root (false,1)*
    (root (false,2)*root (true,2)*root (false,2))⁻¹

theorem left_word_value {G : Type*} [Group G] (root : Bool×Fin 4→G) :
    actionWord (fun i : Fin 12=>root (leftActions i))=middleValue root := by
  change (List.ofFn (root ∘ leftActions)).reverse.prod=_
  rw [←List.map_ofFn,←List.map_reverse]
  change wordValue root ((List.ofFn leftActions).reverse)=_
  rw [left_letters]
  simp only [middleLetters,wordValue_append,wordValue_weyl,middleValue]

theorem right_word_value {G : Type*} [Group G] (root : Bool×Fin 4→G)
    (hinv : ∀a,(root a)⁻¹=root a) :
    actionWord (fun i : Fin 56=>root (rightActions i))=
      (longValue root*shortValue root)*
        (middleValue root*(root (false,1)*root (false,2)*longValue root)*(middleValue root)⁻¹)*
        (root (false,1)*root (false,2)*shortValue root) := by
  change (List.ofFn (root ∘ rightActions)).reverse.prod=_
  rw [←List.map_ofFn,←List.map_reverse]
  change wordValue root ((List.ofFn rightActions).reverse)=_
  rw [right_letters]
  have hm : wordValue root middleLetters=middleValue root := by
    simp only [middleLetters,wordValue_append,wordValue_weyl,middleValue]
  have hl : wordValue root longLetters=longValue root := by
    rw [longLetters,wordValue_append,wordValue_append,wordValue_reverse root hinv,
      wordValue_singleton,wordValue_weyl]
    rfl
  have hp : wordValue root shortLetters=shortValue root := by
    rw [shortLetters,wordValue_append,wordValue_append,wordValue_reverse root hinv,
      wordValue_singleton,wordValue_weyl]
    rfl
  simp only [firstLetters,secondLetters,thirdLetters,wordValue_append,
    wordValue_reverse root hinv,hm,hl,hp]
  change (longValue root*shortValue root)*middleValue root*
    ((root (false,1)*(root (false,2)*1))*longValue root)*(middleValue root)⁻¹*
      ((root (false,1)*(root (false,2)*1))*shortValue root)=_
  group

end SymmetricSubgroupAsymptotics.CFSGFFourMiddleWeylWordLists
