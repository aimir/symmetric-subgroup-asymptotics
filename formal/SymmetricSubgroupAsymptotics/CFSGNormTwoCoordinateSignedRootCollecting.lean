import SymmetricSubgroupAsymptotics.CFSGNormTwoCoordinateRootCollectingTransport
import SymmetricSubgroupAsymptotics.CFSGNormTwoCoordinateRaisedRoot
import SymmetricSubgroupAsymptotics.CFSGNormTwoCoordinateRootWordIdentity

/-! Actual simple-versus-positive-root commutators are root elements
of the sum root, with one integral unit sign valid in all characteristics.
The selected words are identified by the original integer reflection
degrees and checked primitive integral word recognition. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
namespace SymmetricSubgroupAsymptotics.CFSGNormTwoCoordinateSignedRootCollecting
open CFSGIntegerMatrixPairing CFSGNormTwoRootPairing CFSGSerreQuadraticMatrix
open CFSGNormTwoGeckIntegralRealization CFSGNormTwoGeckLatticeDegree
open CFSGNormTwoGeckWeylLatticeLinear CFSGNormTwoCoordinateRootSubgroup
open CFSGSerreQuadraticWeylWord CFSGSerreQuadraticWordRootTransport
open CFSGNormTwoCoordinateSelectedRootElement CFSGNormTwoCoordinateRaisedRoot
open CFSGNormTwoCoordinateRootCollectingTransport
variable {r : ℕ} (A : Matrix (Fin r) (Fin r) ℤ) (hd : ∀i,A i i=2)
    (hs : A.transpose=A) (hp : (rationalMatrix A).PosDef)
    (ho : ∀i j,i≠j→A i j≤0)
    [Fintype (Roots A)] [DecidableEq (Roots A)]
    [(rootPairing A hs hp).IsReduced] [(rootPairing A hs hp).IsIrreducible]

local notation "b₀" => coordinateBase A hd hs hp ho
local notation "s₀" => coordinateIndexEquiv A hd hs hp ho
local notation "D" => realizationData A hs hp b₀ s₀

theorem weyl_selected_root_sign (k : Roots A) (i : Fin r)
    (hpair : integerPairing A k.val (s₀ i:Roots A).val= -1) :
    ∃ε : ℤ,(ε=1 ∨ ε= -1) ∧ ∀(K : Type) [CommRing K] (a : K),
      weylSelectedRootElement A hd hs hp ho K k i a=
        selectedRootElement A hd hs hp ho K (raisedRoot A hd hs hp ho k i hpair) ((ε:K)*a) := by
  let p := rootWitness A hd hs hp ho k
  let g := raisedRoot A hd hs hp ho k i hpair
  let q := rootWitness A hd hs hp ho g
  have hdegree : wordLinear A hs hp b₀ s₀ (i::p.val.1) (-(s₀ p.val.2:Roots A).val)=
      wordLinear A hs hp b₀ s₀ q.val.1 (-(s₀ q.val.2:Roots A).val) := by
    calc
      _=reflectionEquiv A (s₀ i)
          (wordLinear A hs hp b₀ s₀ p.val.1 (-(s₀ p.val.2:Roots A).val)) := rfl
      _=reflectionEquiv A (s₀ i) k.val := congrArg (reflectionEquiv A (s₀ i)) p.property.symm
      _=g.val := by
        change k.val-integerPairing A k.val (s₀ i:Roots A).val • (s₀ i:Roots A).val=
          k.val+(s₀ i:Roots A).val
        rw [hpair,neg_one_smul,sub_neg_eq_add]
      _=_ := q.property
  obtain ⟨ε,hε,he⟩ := CFSGNormTwoCoordinateRootWordIdentity.same_degree_root_identity
    A hd hs hp ho (i::p.val.1) q.val.1 p.val.2 q.val.2 hdegree
  refine ⟨ε,hε,?_⟩
  intro K _ a
  have hw : weylSelectedRootElement A hd hs hp ho K k i a=
      rootWord D K (i::p.val.1) true p.val.2 a := by
    dsimp only [p,weylSelectedRootElement,selectedRootElement,rootWord,canonicalWord]
    group
  exact hw.trans (he K a)

theorem simple_positive_commutator_sign (k : Roots A) (hk : ∀t,0≤k.val t) (i : Fin r)
    (hpair : integerPairing A k.val (s₀ i:Roots A).val= -1) :
    ∃ε : ℤ,(ε=1 ∨ ε= -1) ∧ ∀(K : Type) [CommRing K] (t a : K),
      positiveRootCommutator A hd hs hp ho K k i t a=
        selectedRootElement A hd hs hp ho K (raisedRoot A hd hs hp ho k i hpair)
          ((ε:K)*(a*t)) := by
  obtain ⟨ε,hε,he⟩ := weyl_selected_root_sign A hd hs hp ho k i hpair
  refine ⟨ε,hε,?_⟩
  intro K _ t a
  rw [simple_positive_collecting A hd hs hp ho K k hk i hpair t a,he K (a*t)]

theorem simple_positive_commutator_mem (K : Type) [Field K] (k : Roots A)
    (hk : ∀t,0≤k.val t) (i : Fin r)
    (hpair : integerPairing A k.val (s₀ i:Roots A).val= -1) (t a : K) :
    positiveRootCommutator A hd hs hp ho K k i t a∈
      rootSubgroup A hd hs hp ho K (raisedRoot A hd hs hp ho k i hpair) := by
  obtain ⟨ε,_,he⟩ := simple_positive_commutator_sign A hd hs hp ho k hk i hpair
  rw [he K t a]
  exact selectedRootElement_mem A hd hs hp ho K _ _

end SymmetricSubgroupAsymptotics.CFSGNormTwoCoordinateSignedRootCollecting
