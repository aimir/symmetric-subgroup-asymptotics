import SymmetricSubgroupAsymptotics.CFSGReeFFourMiddleDerivedFiveSurvival
import SymmetricSubgroupAsymptotics.CFSGReeFFourBinaryDerivedGeneration
import SymmetricSubgroupAsymptotics.CFSGInvolutionOrder

/-! Two genuine derived-fixed involutions give parity in the ORIGINAL
ReeF4 model for EVERY m, including its full-centre Tits quotient at0.
The original five-word is already proved nontrivial after that exact
central quotient; here it is factored into actual square-one elements.
No group order, simple/finite premise, ambient identification or new
full-positive membership assumption is used. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
namespace SymmetricSubgroupAsymptotics.CFSGReeFFourAndTitsEvenOrder
open CFSGReeFFourFixedModelEquivalence CFSGReeFFourRelativePositiveSubgroups
open CFSGReeFFourMiddleDerivedFiveWord CFSGReeFFourMiddleDerivedFiveSurvival
open CFSGReeFFourMiddleSquareCommutator CFSGReeFFourBinaryDerivedGeneration
open CFSGReeFFourOriginalPositiveSylow

theorem even_card_of_square_factors {G : Type*} [Group G] (x y : G)
    (hx : x^2=1) (hy : y^2=1) (hne : x*y≠1) : Even (Nat.card G) := by
  by_contra he
  have hodd : Odd (Nat.card G) := Nat.not_even_iff_odd.mp he
  have hx1 := CFSGReduction.eq_one_of_square_eq_one_of_odd_card hodd x hx
  have hy1 := CFSGReduction.eq_one_of_square_eq_one_of_odd_card hodd y hy
  exact hne (by rw [hx1,hy1,mul_one])

def firstSource (m : ℕ) : commutator (originalModelFixed m) :=
  ⟨middleFixedWeyl m,middle_weyl_mem_derived m⟩

def secondSource (m : ℕ) : commutator (originalModelFixed m) :=
  ⟨(fourCycle m)^2,square_mem_derived m⟩

def firstInvolution (m : ℕ) : CFSG.Models.ReeF4 m := derivedReeHom m (firstSource m)
def secondInvolution (m : ℕ) : CFSG.Models.ReeF4 m := derivedReeHom m (secondSource m)

private theorem map_square {G H : Type*} [Group G] [Group H] (f : G →* H)
    (x : G) (hx : x^2=1) : (f x)^2=1 :=
  (map_pow f x 2).symm.trans ((congrArg f hx).trans (map_one f))

theorem first_square (m : ℕ) : firstInvolution m ^ 2 = 1 :=
  map_square (derivedReeHom m) (firstSource m) (Subtype.ext (middleWeyl_square m))

theorem second_square (m : ℕ) : secondInvolution m ^ 2 = 1 := by
  have hs : ((fourCycle m)^2)^2=1 := by
    rw [←pow_mul]
    exact fourCycle_four m
  exact map_square (derivedReeHom m) (secondSource m) (Subtype.ext hs)

theorem product_value (m : ℕ) :
    firstInvolution m * secondInvolution m = originalFiveWord m := by
  have hs : firstSource m * secondSource m = derivedFiveWord m := Subtype.ext rfl
  calc
    _ = derivedReeHom m (firstSource m * secondSource m) :=
      (map_mul (derivedReeHom m) _ _).symm
    _ = derivedReeHom m (derivedFiveWord m) := congrArg (derivedReeHom m) hs
    _ = originalFiveWord m := rfl

theorem reeF4_even_card (m : ℕ) : Even (Nat.card (CFSG.Models.ReeF4 m)) := by
  apply even_card_of_square_factors (firstInvolution m) (secondInvolution m)
    (first_square m) (second_square m)
  intro he
  exact originalFiveWord_ne_one m ((product_value m).symm.trans he)

theorem tits_even_card : Even (Nat.card CFSG.Models.Tits) := reeF4_even_card 0

end SymmetricSubgroupAsymptotics.CFSGReeFFourAndTitsEvenOrder
