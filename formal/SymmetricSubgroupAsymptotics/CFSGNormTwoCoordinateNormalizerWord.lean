import SymmetricSubgroupAsymptotics.CFSGNormTwoCoordinateBruhatCover
import SymmetricSubgroupAsymptotics.CFSGNormTwoGeckOppositeIntersection
import SymmetricSubgroupAsymptotics.CFSGNormTwoCoordinateHeight
import SymmetricSubgroupAsymptotics.CFSGNormTwoGeckBorelNormalization

/-! A normalizer element of the actual canonical group has a Weyl-word
representative normalizing U. Every simple root image of that word and
its inverse is coordinate-positive. Chamber and diagonal-kernel rigidity
are deliberately not inferred by this reduction. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
namespace SymmetricSubgroupAsymptotics.CFSGNormTwoCoordinateNormalizerWord
open CFSGIntegerMatrixPairing CFSGNormTwoRootPairing
open CFSGNormTwoGeckIntegralRealization CFSGNormTwoGeckPositivePGroup
open CFSGNormTwoGeckWeylWordDegree CFSGNormTwoGeckWeylWordAlgebra
open CFSGNormTwoCoordinateWeylRootMembership CFSGNormTwoCoordinateBruhatCover
open CFSGNormTwoGeckOppositeIntersection CFSGNormTwoCoordinateHeight
open CFSGNormTwoGeckBorelEnvelope CFSGNormTwoGeckBorelNormalization
open CFSGSerreQuadraticMatrix
variable {r : ℕ} (A : Matrix (Fin r) (Fin r) ℤ) (hd : ∀j,A j j=2)
    (hs : A.transpose=A) (hp : (rationalMatrix A).PosDef)
    (ho : ∀i j,i≠j→A i j≤0)
    [Fintype (Roots A)] [DecidableEq (Roots A)] [(rootPairing A hs hp).IsIrreducible]

local notation "b₀" => coordinateBase A hd hs hp ho
local notation "s₀" => coordinateIndexEquiv A hd hs hp ho

theorem word_simple_nonnegative (K : Type) [Field K] (w : List (Fin r))
    (hn : wordUnit A hs hp b₀ s₀ K w∈
      Subgroup.normalizer (rootGroup A hs hp b₀ s₀ K false : Set _)) (i : Fin r) :
    ∀l,0≤(wordRoot A hs hp b₀ s₀ w (s₀ i)).val l := by
  have hu : canonicalRoot (realizationData A hs hp b₀ s₀) K false i 1∈
      rootGroup A hs hp b₀ s₀ K false := Subgroup.subset_closure ⟨(i,1),rfl⟩
  have hword : rootWord A hd hs hp ho K w i 1∈rootGroup A hs hp b₀ s₀ K false :=
    (Subgroup.mem_normalizer_iff.mp hn _).mp hu
  rcases word_sign_membership A hd hs hp ho K w i 1 with hpos|hneg
  · exact hpos.1
  · have hb : rootWord A hd hs hp ho K w i 1∈
        rootGroup A hs hp b₀ s₀ K false⊓rootGroup A hs hp b₀ s₀ K true := ⟨hword,hneg.2⟩
    rw [positive_inf_negative A hs hp b₀ s₀ coordinateHeight
      (simple_height A hd hs hp ho) K,Subgroup.mem_bot] at hb
    have he : canonicalRoot (realizationData A hs hp b₀ s₀) K false i 1=
        (wordUnit A hs hp b₀ s₀ K w)⁻¹*rootWord A hd hs hp ho K w i 1*
          wordUnit A hs hp b₀ s₀ K w := by
      dsimp only [rootWord]
      group
    rw [hb,mul_one,inv_mul_cancel] at he
    exact False.elim (canonicalRoot_one_ne_one A hs hp b₀ s₀ coordinateHeight
      (simple_height A hd hs hp ho) K i he)

theorem inverse_word_simple_nonnegative (K : Type) [Field K] (w : List (Fin r))
    (hn : wordUnit A hs hp b₀ s₀ K w∈
      Subgroup.normalizer (rootGroup A hs hp b₀ s₀ K false : Set _)) (i : Fin r) :
    ∀l,0≤(wordRoot A hs hp b₀ s₀ (inverseWord w) (s₀ i)).val l := by
  let N : Subgroup (Matrix ((b₀).support⊕Roots A) ((b₀).support⊕Roots A) K)ˣ :=
    Subgroup.normalizer (rootGroup A hs hp b₀ s₀ K false : Set _)
  have hni : (wordUnit A hs hp b₀ s₀ K w)⁻¹∈N := N.inv_mem hn
  apply word_simple_nonnegative A hd hs hp ho K (inverseWord w) _ i
  rw [wordUnit_inverseWord]
  exact hni

theorem normalizer_word_reduction (K : Type) [Field K]
    (g : (Matrix ((b₀).support⊕Roots A) ((b₀).support⊕Roots A) K)ˣ)
    (hg : g∈canonicalElementaryGroup (realizationData A hs hp b₀ s₀) K)
    (hN : g∈Subgroup.normalizer (rootGroup A hs hp b₀ s₀ K false : Set _)) :
    ∃w : List (Fin r),∃b∈borelEnvelope A hs hp b₀ s₀ K,
      ∃c∈borelEnvelope A hs hp b₀ s₀ K,
      g=b*wordUnit A hs hp b₀ s₀ K w*c ∧
      wordUnit A hs hp b₀ s₀ K w∈Subgroup.normalizer (rootGroup A hs hp b₀ s₀ K false : Set _) ∧
      (∀i l,0≤(wordRoot A hs hp b₀ s₀ w (s₀ i)).val l) ∧
      (∀i l,0≤(wordRoot A hs hp b₀ s₀ (inverseWord w) (s₀ i)).val l) := by
  obtain ⟨w,b,hb,c,hc,he⟩ := canonical_bruhat_cover A hd hs hp ho K g hg
  let N : Subgroup (Matrix ((b₀).support⊕Roots A) ((b₀).support⊕Roots A) K)ˣ :=
    Subgroup.normalizer (rootGroup A hs hp b₀ s₀ K false : Set _)
  have hbN : b∈N := borelEnvelope_le_normalizer_positive A hs hp b₀ s₀ K hb
  have hcN : c∈N := borelEnvelope_le_normalizer_positive A hs hp b₀ s₀ K hc
  have hn : b⁻¹*g*c⁻¹∈N := N.mul_mem (N.mul_mem (N.inv_mem hbN) hN) (N.inv_mem hcN)
  have he' : b⁻¹*g*c⁻¹=wordUnit A hs hp b₀ s₀ K w := by rw [he];group
  rw [he'] at hn
  exact ⟨w,b,hb,c,hc,he,hn,word_simple_nonnegative A hd hs hp ho K w hn,
    inverse_word_simple_nonnegative A hd hs hp ho K w hn⟩

end SymmetricSubgroupAsymptotics.CFSGNormTwoCoordinateNormalizerWord
