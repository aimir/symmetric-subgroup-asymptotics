import SymmetricSubgroupAsymptotics.CFSGReeFFourMiddleCollecting
import SymmetricSubgroupAsymptotics.CFSGReeFFourMiddleRootCovariance
import SymmetricSubgroupAsymptotics.CFSGReeFFourFixedModelEquivalence

/-! A genuine two-parameter middle fixed word in the literal original
ReeF4 fixed group. This is a parameter map, not an additive homomorphism;
no whole-positive or derived-central-quotient assertion is made here. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
namespace SymmetricSubgroupAsymptotics.CFSGReeFFourMiddleFixedWords
open CFSG.Models.Chevalley CFSGSerreModelRootGeneration
open CFSGFFourOriginalMiddleWords CFSGReeFFourMiddleRootCovariance
open CFSGReeFFourMiddleCollecting CFSGReeFFourFieldParameters
open CFSGReeFFourOriginalAutomorphism CFSGReeFFourFixedModelEquivalence
local notation "A" => CartanMatrix.F₄

def middleWord (m : ℕ) (a b c d : Field m) : Model A (Field m) :=
  modelRoot A (Field m) false 1 a*modelRoot A (Field m) false 2 b*
    middleLong (Field m) d*middleShort (Field m) c

theorem middleWord_twist (m : ℕ) (a b c d : Field m) :
    reeAutomorphism m (middleWord m a b c d)=
      middleWord m (beta m b) (alpha m a)
        (beta m d+beta m b*alpha m a) (alpha m c+(beta m b)^2*alpha m a) := by
  simp only [middleWord,map_mul,reeAutomorphism_root,middleLong_twist,middleShort_twist]
  change modelRoot A (Field m) false 2 (alpha m a)*
      modelRoot A (Field m) false 1 (beta m b)*middleShort (Field m) (beta m d)*
      middleLong (Field m) (alpha m c)=_
  calc
    _=(middleLong (Field m) ((beta m b)^2*alpha m a)*
        middleShort (Field m) (beta m b*alpha m a))*
      (modelRoot A (Field m) false 1 (beta m b)*
        modelRoot A (Field m) false 2 (alpha m a))*
      (middleShort (Field m) (beta m d)*middleLong (Field m) (alpha m c)) := by
        rw [middle_reverse_axes]
        group
    _=modelRoot A (Field m) false 1 (beta m b)*
      modelRoot A (Field m) false 2 (alpha m a)*
      middleLong (Field m) ((beta m b)^2*alpha m a+alpha m c)*
      middleShort (Field m) (beta m b*alpha m a+beta m d) :=
        middle_collect_central m (beta m b) (alpha m a)
          ((beta m b)^2*alpha m a) (beta m b*alpha m a) (beta m d) (alpha m c)
    _=_ := by rw [add_comm ((beta m b)^2*alpha m a),add_comm (beta m b*alpha m a)]

def fixedMiddleWord (m : ℕ) (a c : Field m) : Model A (Field m) :=
  middleWord m a (alpha m a) c (alpha m c+a^2*alpha m a)

theorem fixedMiddleWord_fixed (m : ℕ) (a c : Field m) :
    reeAutomorphism m (fixedMiddleWord m a c)=fixedMiddleWord m a c := by
  have he : beta m (alpha m c+a^2*alpha m a)+a*alpha m a=c := by
    rw [map_add,beta_alpha,map_mul,map_pow,beta_alpha,←alpha_eq_beta_square]
    rw [mul_comm (alpha m a) a,add_assoc,CharTwo.add_self_eq_zero,add_zero]
  unfold fixedMiddleWord
  rw [middleWord_twist,beta_alpha,he]

def fixedMiddleParameter (m : ℕ) (p : Field m×Field m) : originalModelFixed m :=
  ⟨fixedMiddleWord m p.1 p.2,fixedMiddleWord_fixed m p.1 p.2⟩

def originalFixedMiddleParameter (m : ℕ) (p : Field m×Field m) :
    fixedSubgroup A (Field m) CFSG.Models.reverseNode (originalExponent m) :=
  (originalFixedEquiv m).symm (fixedMiddleParameter m p)

theorem originalFixedMiddleParameter_val (m : ℕ) (p : Field m×Field m) :
    (originalFixedMiddleParameter m p).val=(fixedMiddleWord m p.1 p.2).val := rfl

end SymmetricSubgroupAsymptotics.CFSGReeFFourMiddleFixedWords
