import SymmetricSubgroupAsymptotics.CFSGNormTwoCoordinateComplementNormalizerBase
import SymmetricSubgroupAsymptotics.CFSGNormTwoCoordinateComplementWord
import SymmetricSubgroupAsymptotics.CFSGNormTwoCoordinateBruhatCover
import SymmetricSubgroupAsymptotics.CFSGNormTwoGeckRootWordMembership

/-! The actual normalizer of an excluded-simple positive complement is
the rank-one extension of the FULL positive normalizer. All diagonal
factors remain present; no identification of them with torus words. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
namespace SymmetricSubgroupAsymptotics.CFSGNormTwoCoordinateComplementNormalizer
open CFSGIntegerMatrixPairing CFSGNormTwoRootPairing CFSGSerreQuadraticMatrix
open CFSGNormTwoGeckIntegralRealization CFSGNormTwoGeckPositivePGroup
open CFSGNormTwoGeckPositiveComplement CFSGNormTwoGeckComplementNormalizer
open CFSGNormTwoGeckWeylWordDegree CFSGNormTwoGeckWeylWordAlgebra
open CFSGNormTwoCoordinateComplementNormalizerBase CFSGNormTwoCoordinateComplementWord
open CFSGNormTwoCoordinateBruhatCover CFSGNormTwoGeckBorelEnvelope
open CFSGNormTwoGeckBorelNormalization CFSGNormTwoGeckRootWordMembership
open CFSGNormTwoGeckWeylLatticeLinear
variable {r : ℕ} (A : Matrix (Fin r) (Fin r) ℤ) (hd : ∀j,A j j=2)
    (hs : A.transpose=A) (hp : (rationalMatrix A).PosDef)
    (ho : ∀i j,i≠j→A i j≤0)
    [Fintype (Roots A)] [DecidableEq (Roots A)]
    [(rootPairing A hs hp).IsReduced] [(rootPairing A hs hp).IsIrreducible]
    (K : Type) [Field K] [Finite K]
local notation "b₀" => coordinateBase A hd hs hp ho
local notation "s₀" => coordinateIndexEquiv A hd hs hp ho
local notation "D" => realizationData A hs hp b₀ s₀
local notation "U" => rootGroup A hs hp b₀ s₀ K false
local notation "M" => positiveComplement A hs hp b₀ s₀ K
local notation "H" => canonicalElementaryGroup D K
local notation "N" => (Subgroup.normalizer (U : Set _) ⊓ H)

theorem complement_normalizer_eq_rank_one
    (ε : Fin r→ℤ) (hε : ∀j,ε j*ε j=1)
    (hA : ∀i j,ε i*|A i j|=A j i*ε j)
    (hidentity : ∀w : List (Fin r),wordUnit A hs hp b₀ s₀ K w∈
      Subgroup.normalizer (U : Set _)→wordLinear A hs hp b₀ s₀ w=1) (i : Fin r) :
    Subgroup.normalizer (M i : Set _) ⊓ H=
      N ⊔ Subgroup.closure {canonicalWeyl D K i} := by
  let P : Subgroup (Matrix ((b₀).support⊕Roots A) ((b₀).support⊕Roots A) K)ˣ :=
    N ⊔ Subgroup.closure {canonicalWeyl D K i}
  have hwiH : canonicalWeyl D K i∈H := by
    simpa only [wordUnit,mul_one] using word_mem A hs hp b₀ s₀ K [i]
  have hwiP : canonicalWeyl D K i∈P :=
    (show Subgroup.closure {canonicalWeyl D K i}≤P from le_sup_right)
      (Subgroup.subset_closure (Set.mem_singleton _))
  apply le_antisymm
  · intro g hg
    obtain ⟨w,b,hb,c,hc,he⟩ := canonical_bruhat_cover A hd hs hp ho K g hg.2
    have hbN : b∈N := ⟨borelEnvelope_le_normalizer_positive A hs hp b₀ s₀ K hb,
      borelEnvelope_le_canonical A hs hp b₀ s₀ K hb⟩
    have hcN : c∈N := ⟨borelEnvelope_le_normalizer_positive A hs hp b₀ s₀ K hc,
      borelEnvelope_le_canonical A hs hp b₀ s₀ K hc⟩
    let NM : Subgroup (Matrix ((b₀).support⊕Roots A) ((b₀).support⊕Roots A) K)ˣ :=
      Subgroup.normalizer (M i : Set _)
    have hbM : b∈NM := positive_normalizer_mem_complement_normalizer
      A hd hs hp ho K ε hε hA hidentity i b hbN.2 hbN.1
    have hcM : c∈NM := positive_normalizer_mem_complement_normalizer
      A hd hs hp ho K ε hε hA hidentity i c hcN.2 hcN.1
    have hwM : wordUnit A hs hp b₀ s₀ K w∈NM := by
      have hh := NM.mul_mem (NM.mul_mem (NM.inv_mem hbM) hg.1) (NM.inv_mem hcM)
      have he' : b⁻¹*g*c⁻¹=wordUnit A hs hp b₀ s₀ K w := by rw [he];group
      rwa [he'] at hh
    have hwP : wordUnit A hs hp b₀ s₀ K w∈P := by
      rcases complement_word_normalizer_dichotomy A hd hs hp ho K i w hwM with hw|hw
      · exact (show N≤P from le_sup_left) ⟨hw,word_mem A hs hp b₀ s₀ K w⟩
      · have hw' : wordUnit A hs hp b₀ s₀ K (w++[i])∈P :=
          (show N≤P from le_sup_left) ⟨hw,word_mem A hs hp b₀ s₀ K (w++[i])⟩
        have he' : wordUnit A hs hp b₀ s₀ K w=
            wordUnit A hs hp b₀ s₀ K (w++[i])*(canonicalWeyl D K i)⁻¹ := by
          rw [wordUnit_append]
          simp only [wordUnit,mul_one]
          group
        rw [he']
        exact P.mul_mem hw' (P.inv_mem hwiP)
    change g∈P
    rw [he]
    exact P.mul_mem (P.mul_mem ((show N≤P from le_sup_left) hbN) hwP)
      ((show N≤P from le_sup_left) hcN)
  · apply sup_le
    · intro g hg
      exact ⟨positive_normalizer_mem_complement_normalizer A hd hs hp ho K
        ε hε hA hidentity i g hg.2 hg.1,hg.2⟩
    · apply (Subgroup.closure_le _).mpr
      intro g hg
      have he : g=canonicalWeyl D K i := Set.mem_singleton_iff.mp hg
      subst g
      exact ⟨weyl_mem_normalizer A hs hp b₀ s₀ K i,hwiH⟩

end SymmetricSubgroupAsymptotics.CFSGNormTwoCoordinateComplementNormalizer
