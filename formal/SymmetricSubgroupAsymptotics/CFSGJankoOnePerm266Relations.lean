import SymmetricSubgroupAsymptotics.CFSGJankoOnePerm266Pilot
import SymmetricSubgroupAsymptotics.CFSGJankoOneLiteralRepresentation

/-! The remaining four exact OLD J1 presentation relations on two explicit
Perm266 tables. Their source-derived selection is provenance only. Each
relation is independently checked as a raw Boolean identity on all266points.
No XYZ word binding, target order, source identification or surjectivity is
asserted or needed. The first relation and movedpoint reuse the passed pilot. -/
set_option autoImplicit false
set_option Elab.async false
namespace SymmetricSubgroupAsymptotics.CFSGJankoOnePerm266Relations
open SignedPermutationWordPointEvaluation FiniteRawPermutationReflection
open CFSGJankoOnePerm266Pilot CFSGJankoOneLiteralRepresentation

/-- Same four-letter repeated subword as the literal old fourth/fifth rows. -/
def repeatedWord : List Letter :=
  [Letter.first, Letter.second, Letter.first, Letter.secondInv]

def secondRelator : List Letter := powerWord [Letter.second] 3

def thirdRelator : List Letter := powerWord [Letter.first, Letter.second] 7

def fourthRelator : List Letter :=
  powerWord ([Letter.first, Letter.second] ++ powerWord repeatedWord 3) 5

def fifthRelator : List Letter :=
  powerWord (([Letter.first, Letter.second] ++ powerWord repeatedWord 6) ++
    [Letter.first, Letter.second, Letter.first, Letter.second] ++
    powerWord [Letter.first, Letter.secondInv] 2) 2

theorem second_semantics {G : Type} [Group G] (x y : G) :
    eval x y secondRelator = y ^ 3 := by
  simp only [secondRelator, eval_power, eval, value, mul_one]

theorem third_semantics {G : Type} [Group G] (x y : G) :
    eval x y thirdRelator = (x * y) ^ 7 := by
  simp only [thirdRelator, eval_power, eval, value, mul_one]

theorem fourth_semantics {G : Type} [Group G] (x y : G) :
    eval x y fourthRelator = (fourthWord x y) ^ 5 := by
  simp only [fourthRelator, eval_power, eval_append, repeatedWord, eval,
    value, mul_one, fourthWord, pow_one, mul_assoc]

theorem fifth_semantics {G : Type} [Group G] (x y : G) :
    eval x y fifthRelator =
      (CFSGJankoOnePresentationGenerators.lastInvolutionWord x y) ^ 2 := by
  simp only [fifthRelator, eval_power, eval_append, repeatedWord, eval,
    value, mul_one, CFSGJankoOnePresentationGenerators.lastInvolutionWord,
    pow_one, mul_assoc]

theorem second_check : wordCheck 266 af ai bf bi secondRelator = true := by
  decide +kernel

theorem third_check : wordCheck 266 af ai bf bi thirdRelator = true := by
  decide +kernel

theorem fourth_check : wordCheck 266 af ai bf bi fourthRelator = true := by
  decide +kernel

theorem fifth_check : wordCheck 266 af ai bf bi fifthRelator = true := by
  decide +kernel

theorem b_cube : b ^ 3 = 1 := by
  have he := eval_eq_one_of_wordCheck a_valid b_valid secondRelator second_check
  change eval a b secondRelator = 1 at he
  exact (second_semantics a b).symm.trans he

theorem product_seventh : (a * b) ^ 7 = 1 := by
  have he := eval_eq_one_of_wordCheck a_valid b_valid thirdRelator third_check
  change eval a b thirdRelator = 1 at he
  exact (third_semantics a b).symm.trans he

theorem fourth_fifth : (fourthWord a b) ^ 5 = 1 := by
  have he := eval_eq_one_of_wordCheck a_valid b_valid fourthRelator fourth_check
  change eval a b fourthRelator = 1 at he
  exact (fourth_semantics a b).symm.trans he

theorem fifth_square :
    (CFSGJankoOnePresentationGenerators.lastInvolutionWord a b) ^ 2 = 1 := by
  have he := eval_eq_one_of_wordCheck a_valid b_valid fifthRelator fifth_check
  change eval a b fifthRelator = 1 at he
  exact (fifth_semantics a b).symm.trans he

/-- A closed packet for the literal original OLD five-row presentation. -/
def packet : RelatorPacket a b :=
  ⟨a_square, b_cube, product_seventh, fourth_fifth, fifth_square⟩

end SymmetricSubgroupAsymptotics.CFSGJankoOnePerm266Relations
