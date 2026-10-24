import SymmetricSubgroupAsymptotics.CFSGReeFFourMiddleFixedSubgroup

/-! The exact two-coordinate multiplication law of the actual original
middle fixed subgroup. This is derived from the proved four-coordinate
source-word law and the actual field twist, before any chart equivalence
or automorphism reconstruction. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
open scoped CharTwo
namespace SymmetricSubgroupAsymptotics.CFSGReeFFourMiddleFixedLaw
open CFSGReeFFourFieldParameters CFSGReeFFourMiddleFixedWords
open CFSGReeFFourMiddleWordMultiplication

theorem fixedMiddleWord_mul (m : ℕ) (a c e s : Field m) :
    fixedMiddleWord m a c*fixedMiddleWord m e s=
      fixedMiddleWord m (a+e) (c+s+e*alpha m a) := by
  have hd : (alpha m c+a^2*alpha m a)+(alpha m s+e^2*alpha m e)+e^2*alpha m a=
      alpha m (c+s+e*alpha m a)+(a+e)^2*alpha m (a+e) := by
    simp only [map_add,map_mul,alpha_twice]
    ring_nf <;> simp only [CharTwo.two_eq_zero,mul_zero,zero_mul,add_zero,zero_add]
  dsimp only [fixedMiddleWord]
  rw [middleWord_mul]
  exact congrArg₂ (fun b d : Field m=>middleWord m (a+e) b (c+s+e*alpha m a) d)
    (map_add (alpha m) a e).symm hd

theorem fixedMiddleParameter_mul (m : ℕ) (a c e s : Field m) :
    fixedMiddleParameter m (a,c)*fixedMiddleParameter m (e,s)=
      fixedMiddleParameter m (a+e,c+s+e*alpha m a) := by
  apply Subtype.ext
  exact fixedMiddleWord_mul m a c e s

end SymmetricSubgroupAsymptotics.CFSGReeFFourMiddleFixedLaw
