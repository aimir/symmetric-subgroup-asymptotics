import SymmetricSubgroupAsymptotics.CFSGNormTwoCoordinateChainStarStrings
import SymmetricSubgroupAsymptotics.CFSGNormTwoCoordinateSignedRootCollecting
import SymmetricSubgroupAsymptotics.CFSGNormTwoCoordinateSimpleRootParametrization
import SymmetricSubgroupAsymptotics.CFSGNormTwoCoordinatePositivePairCommute
import SymmetricSubgroupAsymptotics.CFSGNormTwoCoordinateWordRootElementSign

/-! Actual root-element conjugation on the chain-star generators.
A simple positive root adds the next star coordinate with a proved
integral unit coefficient and fixes all other root elements. Its actual
Weyl word swaps the adjacent labels with proved integral unit signs.
Every identity holds before passing to the original projective group. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
namespace SymmetricSubgroupAsymptotics.CFSGNormTwoCoordinateChainStarRootActions
open CFSGIntegerMatrixPairing CFSGNormTwoRootPairing CFSGSerreQuadraticMatrix
open CFSGExceptionalChainStarData CFSGNormTwoCoordinateChainStarStrings
open CFSGNormTwoCoordinateSignedRootCollecting CFSGNormTwoCoordinateSimpleRootParametrization
open CFSGNormTwoCoordinateSelectedRootElement CFSGNormTwoCoordinatePositivePairCommute
open CFSGNormTwoCoordinateRootCollectingTransport CFSGNormTwoCoordinateWordRootElementSign
open CFSGNormTwoGeckIntegralRealization CFSGSerreQuadraticWeylWord
variable {r n : ℕ} (A : Matrix (Fin r) (Fin r) ℤ) (hd : ∀i,A i i=2)
    (hs : A.transpose=A) (hp : (rationalMatrix A).PosDef)
    (ho : ∀i j,i≠j→A i j≤0)
    [Fintype (Roots A)] [DecidableEq (Roots A)]
    [(rootPairing A hs hp).IsReduced] [(rootPairing A hs hp).IsIrreducible]
    (C : ChainStar A n)
local notation "b₀" => coordinateBase A hd hs hp ho
local notation "s₀" => coordinateIndexEquiv A hd hs hp ho
local notation "D" => realizationData A hs hp b₀ s₀

theorem forward_commutator_sign (j : Fin n) :
    ∃ε:ℤ,(ε=1 ∨ ε= -1) ∧ ∀(K:Type)[CommRing K](t a:K),
      positiveRootCommutator A hd hs hp ho K (C.root j.castSucc).val (C.step j) t a=
        selectedRootElement A hd hs hp ho K (C.root j.succ).val ((ε:K)*(a*t)) := by
  have hpj : integerPairing A (C.root j.castSucc).val.val
      (s₀ (C.step j) : Roots A).val= -1 := by
    rw [simple_pair A hd hs hp ho C j j.castSucc,if_pos rfl]
  obtain ⟨ε,hε,he⟩ := simple_positive_commutator_sign A hd hs hp ho
    (C.root j.castSucc).val (C.root j.castSucc).property (C.step j) hpj
  refine ⟨ε,hε,?_⟩
  intro K _ t a
  rw [he K t a,raised_root A hd hs hp ho C j hpj]

theorem other_root_commutes (K:Type)[CommRing K] (j : Fin n) (k : Fin (n+1))
    (hk:k≠j.castSucc) (t a:K) :
    Commute (canonicalRoot D K false (C.step j) t)
      (selectedRootElement A hd hs hp ho K (C.root k).val a) := by
  have hsimple : ∀i,0≤(s₀ (C.step j):Roots A).val i := by
    change ∀i,0≤(Pi.single (C.step j) (1:ℤ) : Fin r→ℤ) i
    intro i
    simp only [Pi.single_apply]
    split_ifs <;> norm_num
  have hpj : integerPairing A (C.root k).val.val (s₀ (C.step j):Roots A).val=0 ∨
      integerPairing A (C.root k).val.val (s₀ (C.step j):Roots A).val=1 := by
    rw [simple_pair A hd hs hp ho C j k,if_neg hk]
    by_cases he:k=j.succ
    · rw [if_pos he]
      exact Or.inr rfl
    · rw [if_neg he]
      exact Or.inl rfl
  obtain ⟨ε,hε,he⟩ := selected_simple_root_sign A hd hs hp ho (C.step j)
  have hsquare : (ε:K)*(ε:K)=1 := by rcases hε with rfl|rfl <;> norm_num
  have hc := positive_pair_commute A hd hs hp ho K (C.root k).val (s₀ (C.step j))
    (C.root k).property hsimple hpj a ((ε:K)*t)
  rw [he K ((ε:K)*t),←mul_assoc,hsquare,one_mul] at hc
  exact hc.symm

theorem simple_weyl_sign (j : Fin n) (k : Fin (n+1)) :
    ∃ε:ℤ,(ε=1 ∨ ε= -1) ∧ ∀(K:Type)[CommRing K](a:K),
      canonicalWeyl D K (C.step j)*selectedRootElement A hd hs hp ho K (C.root k).val a*
        (canonicalWeyl D K (C.step j))⁻¹=
      selectedRootElement A hd hs hp ho K
        (C.root (Equiv.swap j.castSucc j.succ k)).val ((ε:K)*a) := by
  obtain ⟨ε,hε,he⟩ := word_selected_root_sign A hd hs hp ho [C.step j] (C.root k).val
  refine ⟨ε,hε,?_⟩
  intro K _ a
  have hh := he K a
  rw [reflected_root A hd hs hp ho C j k] at hh
  simpa only [canonicalWord,mul_one] using hh

end SymmetricSubgroupAsymptotics.CFSGNormTwoCoordinateChainStarRootActions
