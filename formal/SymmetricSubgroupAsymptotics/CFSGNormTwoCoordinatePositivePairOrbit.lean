import SymmetricSubgroupAsymptotics.CFSGNormTwoCoordinatePositivePairDescent
import SymmetricSubgroupAsymptotics.CFSGNormTwoGeckWeylWordAlgebra

/-! An actual finite reflection word sends any adjacent positive-root
pair to a simple/positive pair. Strong height induction constructs the
word and preserves the second root's positivity at every step. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
namespace SymmetricSubgroupAsymptotics.CFSGNormTwoCoordinatePositivePairOrbit
open CFSGIntegerMatrixPairing CFSGNormTwoRootPairing CFSGIntegerHeightSign
open CFSGNormTwoGeckWeylWordDegree CFSGNormTwoGeckWeylWordAlgebra
open CFSGNormTwoGeckWeylLatticeLinear CFSGNormTwoCoordinatePositivePairDescent
variable {r : ℕ} (A : Matrix (Fin r) (Fin r) ℤ) (hd : ∀i,A i i=2)
    (hs : A.transpose=A) (hp : (rationalMatrix A).PosDef)
    (ho : ∀i j,i≠j→A i j≤0)
    [Fintype (Roots A)] [DecidableEq (Roots A)]
    [(rootPairing A hs hp).IsIrreducible]

local notation "b₀" => coordinateBase A hd hs hp ho
local notation "s₀" => coordinateIndexEquiv A hd hs hp ho

theorem exists_word_simple_positive_pair (k l : Roots A)
    (hk : ∀j,0≤k.val j) (hl : ∀j,0≤l.val j)
    (hpair : integerPairing A k.val l.val= -1) :
    ∃(w : List (Fin r)) (j : Fin r),
      wordRoot A hs hp b₀ s₀ w k=(s₀ j:Roots A) ∧
      (∀t,0≤(wordRoot A hs hp b₀ s₀ w l).val t) ∧
      integerPairing A (wordRoot A hs hp b₀ s₀ w l).val (s₀ j:Roots A).val= -1 := by
  classical
  have H : ∀m : ℕ,∀k l : Roots A,(height k.val).toNat=m→
      (∀j,0≤k.val j)→(∀j,0≤l.val j)→integerPairing A k.val l.val= -1→
      ∃(w : List (Fin r)) (j : Fin r),
        wordRoot A hs hp b₀ s₀ w k=(s₀ j:Roots A) ∧
        (∀t,0≤(wordRoot A hs hp b₀ s₀ w l).val t) ∧
        integerPairing A (wordRoot A hs hp b₀ s₀ w l).val (s₀ j:Roots A).val= -1 := by
    intro m
    induction m using Nat.strong_induction_on with
    | h m ih=>
      intro k l hm hk hl hpair
      by_cases hsimple : ∃j,k=(s₀ j:Roots A)
      · obtain ⟨j,hj⟩ := hsimple
        refine ⟨[],j,hj,hl,?_⟩
        change integerPairing A l.val (s₀ j:Roots A).val= -1
        rw [←hj,integer_symmetric A hs l.val k.val]
        exact hpair
      have hnonsimple : ∀i,k≠(s₀ i:Roots A) := fun i he=>hsimple ⟨i,he⟩
      obtain ⟨i,hk',hl',hheight,hpair'⟩ := positive_pair_step A hd hs hp ho k l hk hl hpair hnonsimple
      let k' := (rootPairing A hs hp).reflectionPerm (s₀ i) k
      let l' := (rootPairing A hs hp).reflectionPerm (s₀ i) l
      have hknonneg : 0≤height k.val := Finset.sum_nonneg (fun j _=>hk j)
      have hk'nonneg : 0≤height k'.val := Finset.sum_nonneg (fun j _=>hk' j)
      have hlt : (height k'.val).toNat<m := by change height k'.val<height k.val at hheight;omega
      obtain ⟨w,j,hfirst,hsecond,hlast⟩ := ih (height k'.val).toNat hlt k' l' rfl hk' hl' hpair'
      refine ⟨w++[i],j,?_,?_,?_⟩
      · rw [wordRoot_append]
        exact hfirst
      · rw [wordRoot_append]
        exact hsecond
      · rw [wordRoot_append]
        exact hlast
  exact H (height k.val).toNat k l rfl hk hl hpair

end SymmetricSubgroupAsymptotics.CFSGNormTwoCoordinatePositivePairOrbit
