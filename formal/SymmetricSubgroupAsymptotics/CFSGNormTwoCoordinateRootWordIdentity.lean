import SymmetricSubgroupAsymptotics.CFSGNormTwoCoordinateRootWordComparison
import SymmetricSubgroupAsymptotics.CFSGNormTwoGeckRootWordMembership
import SymmetricSubgroupAsymptotics.CFSGSerreQuadraticWordRootComparison

/-! Same-root Weyl-word parametrizations agree up to an integral sign in
EVERY coefficient characteristic. The degree comparison is on the actual
integer lattice; generated-Lie recognition and primitive integer inverse
conjugation establish the sign before polynomial base change. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
namespace SymmetricSubgroupAsymptotics.CFSGNormTwoCoordinateRootWordIdentity
open CFSGIntegerMatrixPairing CFSGNormTwoRootPairing
open CFSGNormTwoGeckIntegralRealization CFSGNormTwoGeckWeylLatticeLinear
open CFSGNormTwoGeckIntegralWord CFSGNormTwoGeckWeylWordDegree
open CFSGSerreQuadraticMatrix CFSGSerreQuadraticWeylWord
open CFSGSerreQuadraticWordRootTransport CFSGNormTwoCoordinateRootWordComparison
variable {r : ℕ} (A : Matrix (Fin r) (Fin r) ℤ) (hd : ∀i,A i i=2)
    (hs : A.transpose=A) (hp : (rationalMatrix A).PosDef)
    (ho : ∀i j,i≠j→A i j≤0)
    [Fintype (Roots A)] [DecidableEq (Roots A)]
    [(rootPairing A hs hp).IsReduced] [(rootPairing A hs hp).IsIrreducible]

local notation "b₀" => coordinateBase A hd hs hp ho
local notation "s₀" => coordinateIndexEquiv A hd hs hp ho
local notation "D" => realizationData A hs hp b₀ s₀

theorem same_degree_root_identity (w v : List (Fin r)) (i j : Fin r)
    (hdegree : wordLinear A hs hp b₀ s₀ w (-(s₀ i:Roots A).val)=
      wordLinear A hs hp b₀ s₀ v (-(s₀ j:Roots A).val)) :
    ∃ε : ℤ,(ε=1 ∨ ε= -1) ∧
      ∀ (K : Type) [CommRing K] (a : K),
        rootWord D K w true i a=rootWord D K v true j ((ε:K)*a) := by
  obtain ⟨ε,hε,hc⟩ := same_degree_sign A hd hs hp ho w v i j hdegree
  refine ⟨ε,hε,?_⟩
  have hr : ∀a : ℚ,rootWord D ℚ w true i a=rootWord D ℚ v true j ((ε:ℚ)*a) := by
    intro a
    apply CFSGSerreQuadraticWordRootComparison.rational_scaled_pair D
      (canonicalWord D ℚ w) (canonicalWord D ℚ v) true true i j (ε:ℚ) _ a
    simpa only [coefficient,CFSGAlgebraConjugationAction.action_apply,
      word_eq_canonicalWord,CFSGNormTwoGeckRationalWeylCollecting.rational_F_eq] using hc
  intro K _ a
  exact CFSGSerreQuadraticWordRootComparison.word_pair_of_rational D K
    w v true true i j ε hr a

theorem same_degree_root_ranges (K : Type) [Field K] (w v : List (Fin r)) (i j : Fin r)
    (hdegree : wordLinear A hs hp b₀ s₀ w (-(s₀ i:Roots A).val)=
      wordLinear A hs hp b₀ s₀ v (-(s₀ j:Roots A).val)) :
    Set.range (rootWord D K w true i)=Set.range (rootWord D K v true j) := by
  obtain ⟨ε,hε,he⟩ := same_degree_root_identity A hd hs hp ho w v i j hdegree
  have hsurj : Function.Surjective (fun a : K=>(ε:K)*a) := by
    rcases hε with rfl | rfl
    · intro a
      exact ⟨a,by simp⟩
    · intro a
      exact ⟨-a,by simp⟩
  ext u
  constructor
  · rintro ⟨a,rfl⟩
    exact ⟨(ε:K)*a,(he K a).symm⟩
  · rintro ⟨a,rfl⟩
    obtain ⟨b,hb⟩ := hsurj a
    dsimp only at hb
    exact ⟨b,by rw [he K b,hb]⟩

end SymmetricSubgroupAsymptotics.CFSGNormTwoCoordinateRootWordIdentity
