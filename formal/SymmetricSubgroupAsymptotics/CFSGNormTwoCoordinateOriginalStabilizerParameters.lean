import SymmetricSubgroupAsymptotics.CFSGNormTwoCoordinateOriginalSimpleStabilizer
import SymmetricSubgroupAsymptotics.CFSGNormTwoCoordinateOriginalNegativeSimpleAction
import SymmetricSubgroupAsymptotics.CFSGNormTwoCoordinateOriginalParameterRigidity
import SymmetricSubgroupAsymptotics.CFSGNormTwoCoordinateOriginalCommonField

/-! The ACTUAL original simple-line stabilizer has common-field scalar
data, and its positive simple-root parameter action is faithful. Negative
range preservation is deduced from actual opposite-root geometry, not a
new input. The original elementary generation discharges final rigidity. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
namespace SymmetricSubgroupAsymptotics.CFSGNormTwoCoordinateOriginalStabilizerParameters
open CFSG.Models.Chevalley CFSGIntegerMatrixPairing CFSGNormTwoRootPairing
open CFSGGeckSerreRepresentation CFSGNormTwoCoordinateOriginalPositiveCenter
open CFSGNormTwoCoordinateOriginalOppositeAlignment CFSGNormTwoCoordinateOriginalSimpleRootAction
open CFSGNormTwoCoordinateOriginalNormalizerIntersection
open CFSGNormTwoGeckPositivePGroup CFSGNormTwoGeckWeylWordDegree CFSGNormTwoGeckWeylLatticeLinear
variable {r : ℕ} (A : Matrix (Fin r) (Fin r) ℤ) (hd : ∀i,A i i=2)
    (hs : A.transpose=A) (hp : (rationalMatrix A).PosDef)
    (ho : ∀i j,i≠j→A i j≤0)
    [Fintype (Roots A)] [DecidableEq (Roots A)]
    [(rootPairing A hs hp).IsReduced] [(rootPairing A hs hp).IsIrreducible]
    (K : Type) [Field K] [Finite K] [Nontrivial (Fin r)]
local notation "b₀" => coordinateBase A hd hs hp ho
local notation "s₀" => coordinateIndexEquiv A hd hs hp ho

open CFSGSubgroupFamilyStabilizer CFSGSubgroupFamilyIndex CFSGExceptionalDiagramAutomorphisms

open CFSGNormTwoCoordinateOriginalSimpleStabilizer CFSGNormTwoCoordinateOriginalSimpleParameters
open CFSGNormTwoCoordinateOriginalCommonField CFSGNormTwoCoordinateOriginalNegativeSimpleAction
open CFSGNormTwoCoordinateOriginalParameterRigidity CFSGNormTwoCoordinateOriginalAllRootLines

private theorem parameter_action_faithful {J P B H : Type*} [Group B] [Group H]
    (u : J → P → H) (ρ : B →* MulAut H)
    (hker : ∀ f : B, (∀ j x, ρ f (u j x) = u j x) → f = 1)
    (a b : B) (h : ∀ j x, ρ a (u j x) = ρ b (u j x)) : a = b := by
  have hfix (j : J) (x : P) : ρ (b⁻¹ * a) (u j x) = u j x := by
    rw [map_mul, map_inv]
    change (ρ b).symm (ρ a (u j x)) = u j x
    rw [h j x]
    exact (ρ b).symm_apply_apply _
  exact (inv_mul_eq_one.mp (hker (b⁻¹ * a) hfix)).symm

set_option maxHeartbeats 800000 in
theorem simple_stabilizer_semilinear
    (p : ℕ) [Fact p.Prime] [CharP K p]
    [IsSimpleGroup (Projective (cartan b₀ s₀) K)] (i j₀ k₀ : Fin r)
    (hjk : A j₀ k₀ = -1)
    (hconn : ∀ j, Relation.ReflTransGen (fun a b => A a b ≠ 0) j₀ j)
    (f : originalSimpleStabilizer A hd hs hp ho K i) :
    ∃ (σ : K ≃+* K) (c : Fin r → Kˣ), ∀ j a,
      simpleStabilizerAction A hd hs hp ho K i f
        (simpleParameterHom A hd hs hp ho K i j (Multiplicative.ofAdd a)) =
      simpleParameterHom A hd hs hp ho K i j (Multiplicative.ofAdd ((c j : K) * σ a)) := by
  have hR (j : Fin r) : (originalFullRootLine A hd hs hp ho K i (s₀ j)).map
      (simpleStabilizerAction A hd hs hp ho K i f).toMonoidHom =
        originalFullRootLine A hd hs hp ho K i (s₀ j) := by
    have hh := simple_stabilizer_preserves_simple A hd hs hp ho K i f j
    simpa only [originalSimpleRootGroup_eq_fullRootLine] using hh
  let F : MulAut (Projective (cartan b₀ s₀) K) := simpleStabilizerAction A hd hs hp ho K i f
  have hdata : ∃ (σ : K ≃+* K) (c : Fin r → K), ∀ j,
      c j ≠ 0 ∧ ∀ a,
        F (simpleParameterHom A hd hs hp ho K i j (Multiplicative.ofAdd a)) =
          simpleParameterHom A hd hs hp ho K i j (Multiplicative.ofAdd (c j * σ a)) :=
    simple_parameters_common_field A hd hs hp ho K p i F hR j₀ k₀ hjk hconn
  obtain ⟨σ, c, hc⟩ := hdata
  refine ⟨σ, fun j => Units.mk0 (c j) (hc j).1, ?_⟩
  intro j a
  exact (hc j).2 a

theorem simple_stabilizer_eq_one_of_fixed
    (ε : Fin r→ℤ) (hε : ∀j,ε j*ε j=1) (hA : ∀i j,ε i*|A i j|=A j i*ε j)
    (hidentity : ∀w : List (Fin r),wordUnit A hs hp b₀ s₀ K w∈
      Subgroup.normalizer (rootGroup A hs hp b₀ s₀ K false : Set _)→wordLinear A hs hp b₀ s₀ w=1)
    (p : ℕ) [Fact p.Prime] [CharP K p]
    [IsSimpleGroup (Projective (cartan b₀ s₀) K)] (i : Fin r) (θ : Roots A)
    (hθ : ∀j,0≤θ.val j)
    (hdom : ∀j,0 ≤ integerPairing A θ.val (Pi.single j (1:ℤ) : Fin r→ℤ))

    (hneighbors : ∀ j, ∃ k, A j k = -1)
    (f : originalSimpleStabilizer A hd hs hp ho K i)
    (hfix : ∀ j a, simpleStabilizerAction A hd hs hp ho K i f
      (simpleParameterHom A hd hs hp ho K i j (Multiplicative.ofAdd a)) =
        simpleParameterHom A hd hs hp ho K i j (Multiplicative.ofAdd a)) : f = 1 := by
  have hneg := negative_simple_fixed_of_positive_simple_fixed A hd hs hp ho K
    ε hε hA hidentity p i θ hθ hdom (simpleStabilizerAction A hd hs hp ho K i f)
    (pair_preserves_negative A hd hs hp ho K i f.val)
    (pair_preserves_positive A hd hs hp ho K i f.val)
    (simple_stabilizer_preserves_simple A hd hs hp ho K i f)
  have he := eq_one_of_positive_parameters_fixed A hd hs hp ho K p i hneighbors
    (simpleStabilizerAction A hd hs hp ho K i f) hfix hneg
  apply Subtype.ext
  apply Subtype.ext
  exact he

theorem simple_stabilizer_parameter_faithful
    (ε : Fin r→ℤ) (hε : ∀j,ε j*ε j=1) (hA : ∀i j,ε i*|A i j|=A j i*ε j)
    (hidentity : ∀w : List (Fin r),wordUnit A hs hp b₀ s₀ K w∈
      Subgroup.normalizer (rootGroup A hs hp b₀ s₀ K false : Set _)→wordLinear A hs hp b₀ s₀ w=1)
    (p : ℕ) [Fact p.Prime] [CharP K p]
    [IsSimpleGroup (Projective (cartan b₀ s₀) K)] (i : Fin r) (θ : Roots A)
    (hθ : ∀j,0≤θ.val j)
    (hdom : ∀j,0 ≤ integerPairing A θ.val (Pi.single j (1:ℤ) : Fin r→ℤ))

    (hneighbors : ∀ j, ∃ k, A j k = -1)
    (a b : originalSimpleStabilizer A hd hs hp ho K i)
    (h : ∀ j x, simpleStabilizerAction A hd hs hp ho K i a
      (simpleParameterHom A hd hs hp ho K i j (Multiplicative.ofAdd x)) =
        simpleStabilizerAction A hd hs hp ho K i b
          (simpleParameterHom A hd hs hp ho K i j (Multiplicative.ofAdd x))) : a = b := by
  exact parameter_action_faithful
    (fun j x => simpleParameterHom A hd hs hp ho K i j (Multiplicative.ofAdd x))
    (simpleStabilizerAction A hd hs hp ho K i)
    (simple_stabilizer_eq_one_of_fixed A hd hs hp ho K
      ε hε hA hidentity p i θ hθ hdom hneighbors) a b h

end SymmetricSubgroupAsymptotics.CFSGNormTwoCoordinateOriginalStabilizerParameters
