import SymmetricSubgroupAsymptotics.CFSGGTwoOriginalSignedWeylTransport
import SymmetricSubgroupAsymptotics.CFSGWeylWordBruhatCover

/-! Uniform opposite-root transport for arbitrary literal Weyl words.
The same sign flip and scalar apply to BOTH members of each opposite
pair. This supplies the actual root alternative in local Bruhat
multiplication, without a pre-existing BN-pair. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
namespace SymmetricSubgroupAsymptotics.CFSGGTwoOriginalWeylRootDichotomy
open CFSG.Models.Chevalley CFSGSerreModelRootGeneration
open CFSGGTwoOriginalPositiveRootWords CFSGGTwoOriginalSignDuality
open CFSGGTwoOriginalSignedWeylTransport CFSGGTwoSimpleBruhatComplement
open CFSGGTwoPositiveCoordinateKernels CFSGGTwoPositiveWordSubgroup
open CFSGWeylWordBruhatCover
variable (K : Type) [Field K] [CharP K 3]
local notation "A" => CartanMatrix.G₂

private theorem targetSign_twice (i : Fin 2) (neg : Bool) (j : Fin 6) :
    targetSign i (targetSign i neg j) (targetIndex i j)=neg := by
  fin_cases i <;> fin_cases j <;> cases neg <;> rfl

private theorem undo {G : Type*} [Group G] (s x : G) :
    s⁻¹*(s*x*s⁻¹)*s=x := by group

theorem inverse_signed_transport (i : Fin 2) (neg : Bool) (j : Fin 6) (t : K) :
    (simpleWeyl K i)⁻¹*signedModel K neg j t*simpleWeyl K i=
      signedModel K (targetSign i neg j) (targetIndex i j)
        (coefficient K i (targetIndex i j)*t) := by
  have he := signed_transport K i (targetSign i neg j) (targetIndex i j)
    (coefficient K i (targetIndex i j)*t)
  rw [targetSign_twice,targetIndex_involutive,←mul_assoc,coefficient_sq,one_mul] at he
  have hh := congrArg (fun x : Model A K=>(simpleWeyl K i)⁻¹*x*simpleWeyl K i) he
  dsimp only at hh
  rw [undo] at hh
  exact hh.symm

theorem inverse_word_signed_pair (w : List (Fin 2)) (j : Fin 6) :
    ∃(b : Bool)(k : Fin 6)(c : K),∀(neg : Bool)(t : K),
      (wordValue (simpleWeyl K) w)⁻¹*signedModel K neg j t*
        wordValue (simpleWeyl K) w=
      signedModel K (if b then !neg else neg) k (c*t) := by
  induction w generalizing j with
  | nil=>
    refine ⟨false,j,1,?_⟩
    intro neg t
    simp only [wordValue,inv_one,one_mul,mul_one,Bool.false_eq_true,if_false]
  | cons i w ih=>
    obtain ⟨b,k,c,hc⟩ := ih (targetIndex i j)
    refine ⟨Bool.xor b (flipsSign i j),k,c*coefficient K i (targetIndex i j),?_⟩
    intro neg t
    calc
      (wordValue (simpleWeyl K) (i::w))⁻¹*signedModel K neg j t*
          wordValue (simpleWeyl K) (i::w)=
        (wordValue (simpleWeyl K) w)⁻¹*
          ((simpleWeyl K i)⁻¹*signedModel K neg j t*simpleWeyl K i)*
            wordValue (simpleWeyl K) w := by rw [wordValue];group
      _=(wordValue (simpleWeyl K) w)⁻¹*
          signedModel K (targetSign i neg j) (targetIndex i j)
            (coefficient K i (targetIndex i j)*t)*
            wordValue (simpleWeyl K) w := by rw [inverse_signed_transport]
      _=signedModel K (if b then !(targetSign i neg j) else targetSign i neg j) k
          (c*(coefficient K i (targetIndex i j)*t)) := hc _ _
      _=signedModel K (if Bool.xor b (flipsSign i j) then !neg else neg) k
          ((c*coefficient K i (targetIndex i j))*t) := by
        rw [mul_assoc]
        unfold targetSign
        cases b <;> cases h : flipsSign i j <;> cases neg <;> rfl

omit [CharP K 3] in
private theorem signed_simple (neg : Bool) (i : Fin 2) (t : K) :
    signedModel K neg (simpleIndex i) t=modelRoot A K neg i t := by
  fin_cases i <;>
    simp [signedModel,simpleIndex,directionModel,CFSGGTwoPositiveDirections.rootNode]

theorem word_simple_root_dichotomy (w : List (Fin 2)) (i : Fin 2) :
    (∀t : K,(wordValue (simpleWeyl K) w)⁻¹*
        positiveModel K (simpleIndex i) t*wordValue (simpleWeyl K) w∈positiveWordGroup K) ∨
    (∀t : K,(wordValue (simpleWeyl K) w)⁻¹*
        modelRoot A K true i t*wordValue (simpleWeyl K) w∈positiveWordGroup K) := by
  obtain ⟨b,j,c,hc⟩ := inverse_word_signed_pair K w (simpleIndex i)
  cases b
  · left
    intro t
    have he := hc false t
    simp only [Bool.false_eq_true,if_false,signedModel_positive] at he
    rw [he]
    exact (positiveElement K j (c*t)).property
  · right
    intro t
    have he := hc true t
    simp only [if_true,Bool.not_true,signedModel_positive,signed_simple] at he
    rw [he]
    exact (positiveElement K j (c*t)).property

end SymmetricSubgroupAsymptotics.CFSGGTwoOriginalWeylRootDichotomy
