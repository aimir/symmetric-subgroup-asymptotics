import SymmetricSubgroupAsymptotics.CFSGFiniteSignedInversionCount
import SymmetricSubgroupAsymptotics.CFSGNormTwoCoordinateReflectionSigns
import SymmetricSubgroupAsymptotics.CFSGNormTwoGeckWeylLatticeLinear

/-! The actual finite norm-two root permutation of a literal Weyl word
has a strictly decreasing inversion count at every negative simple
image. Positivity means nonnegative ORIGINAL integer coordinates. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
open scoped Classical
namespace SymmetricSubgroupAsymptotics.CFSGNormTwoCoordinateInversionCount
open CFSGIntegerMatrixPairing CFSGNormTwoRootPairing CFSGNormTwoGeckColumns
open CFSGNormTwoGeckWeylWordDegree CFSGNormTwoGeckWeylLatticeLinear
open CFSGNormTwoCoordinateReflectionSigns CFSGNormTwoGeckWeylWordAlgebra
variable {r : ℕ} (A : Matrix (Fin r) (Fin r) ℤ) (hd : ∀i,A i i=2)
    (hs : A.transpose=A) (hp : (rationalMatrix A).PosDef)
    (ho : ∀i j,i≠j→A i j≤0)
    [Fintype (Roots A)] [DecidableEq (Roots A)] [(rootPairing A hs hp).IsIrreducible]
local notation "b₀" => coordinateBase A hd hs hp ho
local notation "s₀" => coordinateIndexEquiv A hd hs hp ho

def Positive (k : Roots A) : Prop := ∀j,0≤k.val j

def rootAction : List (Fin r)→Equiv.Perm (Roots A)
  | []=>1
  | i::w=>(rootPairing A hs hp).reflectionPerm (s₀ i)*rootAction w

omit [Fintype (Roots A)] [DecidableEq (Roots A)] [(rootPairing A hs hp).IsIrreducible] in
theorem rootAction_apply (w : List (Fin r)) (k : Roots A) :
    rootAction A hd hs hp ho w k=wordRoot A hs hp b₀ s₀ w k := by
  induction w with
  | nil=>rfl
  | cons i w ih=>
    change (rootPairing A hs hp).reflectionPerm (s₀ i)
      (rootAction A hd hs hp ho w k)=_
    rw [ih]
    rfl

omit [Fintype (Roots A)] [DecidableEq (Roots A)] [(rootPairing A hs hp).IsIrreducible] in
theorem rootAction_append (v w : List (Fin r)) :
    rootAction A hd hs hp ho (v++w)=rootAction A hd hs hp ho v*rootAction A hd hs hp ho w := by
  induction v with
  | nil=>simp only [List.nil_append,rootAction,one_mul]
  | cons i v ih=>rw [List.cons_append,rootAction,ih,rootAction,mul_assoc]

def inversionCount (w : List (Fin r)) : ℕ :=
  CFSGFiniteSignedInversionCount.inversionCount (Positive A) (rootAction A hd hs hp ho w)

include ho in
theorem inversionCount_append_simple (w : List (Fin r)) (i : Fin r)
    (hneg : ∀j,(wordRoot A hs hp b₀ s₀ w (s₀ i)).val j≤0) :
    inversionCount A hd hs hp ho (w++[i])+1=inversionCount A hd hs hp ho w := by
  let a : Roots A := s₀ i
  let s := (rootPairing A hs hp).reflectionPerm a
  have ha : Positive A a := by
    intro j
    change 0≤(Pi.single i (1:ℤ) : Fin r→ℤ) j
    simp only [Pi.single_apply]
    split_ifs <;> norm_num
  have hsa : ¬Positive A (s a) := by
    intro h
    have hi := h i
    change 0≤(negativeIndex A hs hp a).val i at hi
    rw [negative_val] at hi
    change 0≤ -(Pi.single i (1:ℤ) : Fin r→ℤ) i at hi
    norm_num [Pi.single_apply] at hi
  have hpres : ∀k,Positive A k→k≠a→Positive A (s k) := by
    intro k hk hka
    exact reflection_nonnegative A hd hs hp ho i k hk hka
  have hwa : ¬Positive A (rootAction A hd hs hp ho w a) := by
    intro h
    rw [rootAction_apply] at h
    exact root_signs_incompatible A (wordRoot A hs hp b₀ s₀ w a) h hneg
  have hwsa : Positive A (rootAction A hd hs hp ho w (s a)) := by
    rw [rootAction_apply]
    change ∀j,0≤(wordRoot A hs hp b₀ s₀ w (negativeIndex A hs hp a)).val j
    rw [wordRoot_negative_val]
    intro j
    exact neg_nonneg.mpr (hneg j)
  have hdrop := CFSGFiniteSignedInversionCount.reflection_drop (Positive A) s
    (rootAction A hd hs hp ho w) a ha
    ((rootPairing A hs hp).reflectionPerm_involutive a) hsa hpres hwa hwsa
  simpa only [inversionCount,rootAction_append,rootAction,mul_one] using hdrop

end SymmetricSubgroupAsymptotics.CFSGNormTwoCoordinateInversionCount
