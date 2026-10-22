import SymmetricSubgroupAsymptotics.CFSGNormTwoCoordinateOriginalSimpleParameters
import SymmetricSubgroupAsymptotics.CFSGConnectedRootParameterField
import SymmetricSubgroupAsymptotics.CFSGNormTwoGeckOffDiagonalCollecting

/-! One field automorphism acts on ALL literal original simple-root
parameters when their actual subgroups are fixed. Adjacent incidence is
proved in the original group; propagation uses connected Cartan paths.
No preservation of higher root groups is assumed. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
namespace SymmetricSubgroupAsymptotics.CFSGNormTwoCoordinateOriginalCommonField
open CFSG.Models.Chevalley CFSGIntegerMatrixPairing CFSGNormTwoRootPairing
open CFSGGeckSerreRepresentation CFSGNormTwoCoordinateOriginalProjection
open CFSGNormTwoCoordinateOriginalRootDegree CFSGNormTwoCoordinatePositivePairCollecting
open CFSGNormTwoCoordinateElementaryRootParameters CFSGRootParameterAutomorphism
open CFSGFieldScaledRootHom CFSGCommutatorParameterRange
open CFSGNormTwoCoordinateOriginalA2FieldRecognition
open CFSGNormTwoCoordinateOriginalA2PairStabilizer
open CFSGNormTwoCoordinateOriginalAllRootLines CFSGNormTwoCoordinateRootElementRange
open CFSGNormTwoCoordinateRootSubgroup
variable {r : ℕ} (A : Matrix (Fin r) (Fin r) ℤ) (hd : ∀ i, A i i = 2)
    (hs : A.transpose = A) (hp : (rationalMatrix A).PosDef)
    (ho : ∀ i j, i ≠ j → A i j ≤ 0)
    [Fintype (Roots A)] [DecidableEq (Roots A)]
    [(rootPairing A hs hp).IsReduced] [(rootPairing A hs hp).IsIrreducible]
    (K : Type) [Field K]
local notation "b₀" => coordinateBase A hd hs hp ho
local notation "s₀" => coordinateIndexEquiv A hd hs hp ho

open CFSGNormTwoCoordinateOriginalSimpleParameters CFSGConnectedRootParameterField
open CFSGNormTwoGeckOffDiagonalCollecting

theorem simple_parameters_common_field [Finite K] [Nontrivial (Fin r)]
    (p : ℕ) [Fact p.Prime] [CharP K p]
    [IsSimpleGroup (Projective (cartan b₀ s₀) K)] (i : Fin r)
    (f : MulAut (Projective (cartan b₀ s₀) K))
    (hf : ∀ j, (originalFullRootLine A hd hs hp ho K i (s₀ j)).map f.toMonoidHom =
      originalFullRootLine A hd hs hp ho K i (s₀ j))
    (j₀ k₀ : Fin r) (hjk : A j₀ k₀ = -1)
    (hconn : ∀ j, Relation.ReflTransGen (fun a b => A a b ≠ 0) j₀ j) :
    ∃ (σ : K ≃+* K) (c : Fin r → K), ∀ j,
      c j ≠ 0 ∧ ∀ a,
        f (simpleParameterHom A hd hs hp ho K i j (Multiplicative.ofAdd a)) =
          simpleParameterHom A hd hs hp ho K i j (Multiplicative.ofAdd (c j * σ a)) := by
  let u (j : Fin r) (a : K) :=
    simpleParameterHom A hd hs hp ho K i j (Multiplicative.ofAdd a)
  have hu (j : Fin r) : Function.Injective (u j) :=
    (simpleParameterHom_injective A hd hs hp ho K p i j).comp Multiplicative.ofAdd.injective
  have hpair (j k : Fin r) (hn : A j k ≠ 0) (hne : j ≠ k) :
      ∃ (σ : K ≃+* K) (c d : K), c ≠ 0 ∧ d ≠ 0 ∧ ∀ a,
        f (u j a) = u j (c * σ a) ∧ f (u k a) = u k (d * σ a) := by
    have hentry : A j k = -1 := by
      have hh := cartan_zero_or_neg_one A hs hp b₀ s₀ j k hne
      change (b₀).cartanMatrix (s₀ k) (s₀ j) = 0 ∨
        (b₀).cartanMatrix (s₀ k) (s₀ j) = -1 at hh
      rw [coordinate_cartan_transpose A hd hs hp ho] at hh
      exact hh.resolve_left hn
    exact adjacent_simple_parameters_semilinear A hd hs hp ho K p i j k hentry f (hf j) (hf k)
  have hstart : A j₀ k₀ ≠ 0 := by rw [hjk]; norm_num
  have hne : j₀ ≠ k₀ := by
    intro h
    subst k₀
    rw [hd] at hjk
    norm_num at hjk
  exact common_field_of_connected (fun j k => A j k ≠ 0) u hu (fun j a => f (u j a))
    hpair j₀ k₀ hstart hne hconn

end SymmetricSubgroupAsymptotics.CFSGNormTwoCoordinateOriginalCommonField
