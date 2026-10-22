import SymmetricSubgroupAsymptotics.CFSGNormTwoCoordinateOriginalA2PairStabilizer
import SymmetricSubgroupAsymptotics.CFSGNormTwoCoordinateCanonicalSimpleRootLine

/-! Injective parameters for the literal original simple-root lines,
and actual common-field recognition on every adjacent pair. All image
and commutator premises are discharged from the same original projection. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
namespace SymmetricSubgroupAsymptotics.CFSGNormTwoCoordinateOriginalSimpleParameters
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

theorem originalSelectedHom_range
    [IsSimpleGroup (Projective (cartan b₀ s₀) K)] (i : Fin r)
    (k : Roots A) (hk : ∀ j, 0 ≤ k.val j) :
    (originalSelectedHom A hd hs hp ho K i k hk).range =
      originalFullRootLine A hd hs hp ho K i k := by
  ext y
  constructor
  · rintro ⟨a, rfl⟩
    refine ⟨elementarySelectedRootHom A hd hs hp ho K k a, ?_, rfl⟩
    change (elementarySelectedRootHom A hd hs hp ho K k a).val ∈
      rootSubgroup A hd hs hp ho K k
    exact (mem_rootSubgroup_iff_selected A hd hs hp ho K k _).mpr ⟨a.toAdd, rfl⟩
  · rintro ⟨x, hx, rfl⟩
    change x.val ∈ rootSubgroup A hd hs hp ho K k at hx
    obtain ⟨a, ha⟩ := (mem_rootSubgroup_iff_selected A hd hs hp ho K k x.val).mp hx
    refine ⟨Multiplicative.ofAdd a, ?_⟩
    rw [originalSelectedHom_apply]
    apply congrArg (originalProjection A hd hs hp ho K i)
    exact Subtype.ext ha

 theorem simple_root_nonnegative (j a : Fin r) : 0 ≤ (s₀ j : Roots A).val a := by
  change 0 ≤ (Pi.single j (1 : ℤ) : Fin r → ℤ) a
  simp only [Pi.single_apply]
  split_ifs <;> norm_num

 def simpleParameterHom [IsSimpleGroup (Projective (cartan b₀ s₀) K)] (i j : Fin r) :
    Multiplicative K →* Projective (cartan b₀ s₀) K :=
  originalSelectedHom A hd hs hp ho K i (s₀ j)
    (simple_root_nonnegative A hd hs hp ho j)

 theorem simpleParameterHom_injective [Finite K] [Nontrivial (Fin r)]
    (p : ℕ) [Fact p.Prime] [CharP K p]
    [IsSimpleGroup (Projective (cartan b₀ s₀) K)] (i j : Fin r) :
    Function.Injective (simpleParameterHom A hd hs hp ho K i j) :=
  originalSelectedHom_injective A hd hs hp ho K p i _ _

 theorem simpleParameterHom_range
    [IsSimpleGroup (Projective (cartan b₀ s₀) K)] (i j : Fin r) :
    (simpleParameterHom A hd hs hp ho K i j).range =
      originalFullRootLine A hd hs hp ho K i (s₀ j) :=
  originalSelectedHom_range A hd hs hp ho K i _ _

 theorem adjacent_simple_parameters_semilinear [Finite K] [Nontrivial (Fin r)]
    (p : ℕ) [Fact p.Prime] [CharP K p]
    [IsSimpleGroup (Projective (cartan b₀ s₀) K)] (i j k : Fin r) (hjk : A j k = -1)
    (f : MulAut (Projective (cartan b₀ s₀) K))
    (hfj : (originalFullRootLine A hd hs hp ho K i (s₀ j)).map f.toMonoidHom =
      originalFullRootLine A hd hs hp ho K i (s₀ j))
    (hfk : (originalFullRootLine A hd hs hp ho K i (s₀ k)).map f.toMonoidHom =
      originalFullRootLine A hd hs hp ho K i (s₀ k)) :
    ∃ (σ : K ≃+* K) (c d : K), c ≠ 0 ∧ d ≠ 0 ∧ ∀ a,
      f (simpleParameterHom A hd hs hp ho K i j (Multiplicative.ofAdd a)) =
        simpleParameterHom A hd hs hp ho K i j (Multiplicative.ofAdd (c * σ a)) ∧
      f (simpleParameterHom A hd hs hp ho K i k (Multiplicative.ofAdd a)) =
        simpleParameterHom A hd hs hp ho K i k (Multiplicative.ofAdd (d * σ a)) := by
  have hpair : integerPairing A (s₀ j : Roots A).val (s₀ k : Roots A).val = -1 := by
    change integerPairing A (Pi.single j 1) (Pi.single k 1) = -1
    simpa only [integerPairing, Matrix.toBilin'_single] using hjk
  have hfj' : (simpleParameterHom A hd hs hp ho K i j).range.map f.toMonoidHom =
      (simpleParameterHom A hd hs hp ho K i j).range := by
    simpa only [simpleParameterHom_range] using hfj
  have hfk' : (simpleParameterHom A hd hs hp ho K i k).range.map f.toMonoidHom =
      (simpleParameterHom A hd hs hp ho K i k).range := by
    simpa only [simpleParameterHom_range] using hfk
  exact positive_A2_pair_stabilizer_semilinear A hd hs hp ho K p i (s₀ j) (s₀ k)
    (simple_root_nonnegative A hd hs hp ho j) (simple_root_nonnegative A hd hs hp ho k)
    hpair f hfj' hfk'

end SymmetricSubgroupAsymptotics.CFSGNormTwoCoordinateOriginalSimpleParameters
