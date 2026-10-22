import SymmetricSubgroupAsymptotics.CFSGNormTwoCoordinateExcludedHeight
import SymmetricSubgroupAsymptotics.CFSGNormTwoCoordinateNormalizerDiagonalFactor

/-! The FULL actual positive normalizer normalizes every excluded-simple
complement. Arbitrary diagonal factors are retained; no claim that an
identity-degree Weyl word belongs to the generated torus is needed. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
namespace SymmetricSubgroupAsymptotics.CFSGNormTwoCoordinateComplementNormalizerBase
open CFSGIntegerMatrixPairing CFSGNormTwoRootPairing CFSGSerreQuadraticMatrix
open CFSGNormTwoGeckIntegralRealization CFSGNormTwoGeckHeightSupport
open CFSGNormTwoGeckPositivePGroup CFSGNormTwoGeckPositiveComplement
open CFSGNormTwoGeckComplementNormalizer CFSGNormTwoGeckComplementGrading
open CFSGNormTwoCoordinateExcludedHeight CFSGNormTwoCoordinateNormalizerDiagonalFactor
open CFSGNormTwoGeckWeylWordDegree CFSGNormTwoGeckWeylLatticeLinear
open CFSGGradedMatrixSubgroups
variable {r : ℕ} (A : Matrix (Fin r) (Fin r) ℤ) (hd : ∀i,A i i=2)
    (hs : A.transpose=A) (hp : (rationalMatrix A).PosDef)
    (ho : ∀i j,i≠j→A i j≤0)
    [Fintype (Roots A)] [DecidableEq (Roots A)] [(rootPairing A hs hp).IsIrreducible]
    (K : Type) [Field K]
local notation "b₀" => coordinateBase A hd hs hp ho
local notation "s₀" => coordinateIndexEquiv A hd hs hp ho
local notation "D" => realizationData A hs hp b₀ s₀
local notation "U" => rootGroup A hs hp b₀ s₀ K false
local notation "M" => positiveComplement A hs hp b₀ s₀ K

theorem complement_eq_positive_inf_strict (i : Fin r) :
    M i=U⊓strictUnits (weight A hs hp b₀ (excludedHeight i)) := by
  apply le_antisymm
  · exact le_inf (complement_le_positive A hs hp b₀ s₀ K i)
      (complement_le_strict A hs hp b₀ s₀ (excludedHeight i) i
        (excluded_simple_zero A hd hs hp ho i)
        (fun j hij=>excluded_other_positive A hd hs hp ho i j hij) K)
  · intro g hg
    exact coordinate_positive_mem_complement_of_strict A hd hs hp ho i K g hg.1 hg.2

theorem positive_le_normalizer_complement (i : Fin r) :
    U≤Subgroup.normalizer (M i : Set _) := by
  rw [positive_eq_complement_sup_root A hs hp b₀ s₀ K i]
  exact sup_le (M i).le_normalizer (single_root_le_complement_normalizer A hs hp b₀ s₀ K i)

theorem diagonal_positive_normalizer_mem_complement_normalizer (i : Fin r)
    (d : (Matrix ((b₀).support⊕Roots A) ((b₀).support⊕Roots A) K)ˣ)
    (hdN : d∈Subgroup.normalizer (U : Set _))
    (hdD : (d : Matrix ((b₀).support⊕Roots A) ((b₀).support⊕Roots A) K).IsDiag) :
    d∈Subgroup.normalizer (M i : Set _) := by
  rw [complement_eq_positive_inf_strict A hd hs hp ho K i]
  apply Subgroup.inf_normalizer_le_normalizer_inf
  refine ⟨hdN,?_⟩
  have hdP : d∈preservingUnits (weight A hs hp b₀ (excludedHeight i)) := by
    intro j k hjk
    exact hdD (fun h=>hjk (by subst k;rfl))
  have hle : preservingUnits (K:=K) (weight A hs hp b₀ (excludedHeight i))≤
      Subgroup.normalizer (strictUnits (K:=K) (weight A hs hp b₀ (excludedHeight i)) :
        Set (Matrix ((b₀).support⊕Roots A) ((b₀).support⊕Roots A) K)ˣ) := by
    apply Subgroup.le_normalizer_iff.mpr
    intro g hg u hu
    exact preserving_conjugate_strict _ g u hg hu
  exact hle hdP

theorem positive_normalizer_mem_complement_normalizer
    (ε : Fin r→ℤ) (hε : ∀i,ε i*ε i=1)
    (hA : ∀i j,ε i*|A i j|=A j i*ε j)
    (hidentity : ∀w : List (Fin r),wordUnit A hs hp b₀ s₀ K w∈
      Subgroup.normalizer (U : Set _)→wordLinear A hs hp b₀ s₀ w=1)
    (i : Fin r) (g : (Matrix ((b₀).support⊕Roots A) ((b₀).support⊕Roots A) K)ˣ)
    (hg : g∈canonicalElementaryGroup D K) (hgN : g∈Subgroup.normalizer (U : Set _)) :
    g∈Subgroup.normalizer (M i : Set _) := by
  obtain ⟨u,hu,d,hdD,he⟩ := normalizer_diagonal_factor A hd hs hp ho K ε hε hA hidentity g hg hgN
  let N : Subgroup (Matrix ((b₀).support⊕Roots A) ((b₀).support⊕Roots A) K)ˣ :=
    Subgroup.normalizer (U : Set _)
  have huN : u∈N := (U).le_normalizer hu
  have hdN : d∈N := by
    have hh := N.mul_mem (N.inv_mem huN) hgN
    rw [he,inv_mul_cancel_left] at hh
    exact hh
  rw [he]
  let NM : Subgroup (Matrix ((b₀).support⊕Roots A) ((b₀).support⊕Roots A) K)ˣ :=
    Subgroup.normalizer (M i : Set _)
  exact NM.mul_mem
    (positive_le_normalizer_complement A hd hs hp ho K i hu)
    (diagonal_positive_normalizer_mem_complement_normalizer A hd hs hp ho K i d hdN hdD)

end SymmetricSubgroupAsymptotics.CFSGNormTwoCoordinateComplementNormalizerBase
