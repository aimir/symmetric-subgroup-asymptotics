import SymmetricSubgroupAsymptotics.CFSGNormTwoCoordinateOppositeWord
import SymmetricSubgroupAsymptotics.CFSGSubgroupConjugateDisjoint

/-! The actual positive Borel is transitive on conjugates of the positive
subgroup having trivial intersection with it. This uses the literal
Bruhat cover and actual root-word signs, rather than an assumed BN-pair. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
namespace SymmetricSubgroupAsymptotics.CFSGNormTwoCoordinateOppositeAlignment
open CFSGIntegerMatrixPairing CFSGNormTwoRootPairing
open CFSGNormTwoGeckIntegralRealization CFSGNormTwoGeckPositivePGroup
open CFSGSerreQuadraticMatrix
open CFSGNormTwoGeckWeylWordDegree CFSGNormTwoGeckWeylWordAlgebra
open CFSGNormTwoCoordinateBruhatCover CFSGNormTwoGeckBorelEnvelope
open CFSGNormTwoGeckBorelNormalization CFSGNormTwoCoordinateOppositeWord
open CFSGSubgroupConjugateOrbitCardinality CFSGSubgroupConjugateDisjoint
variable {r : ℕ} (A : Matrix (Fin r) (Fin r) ℤ) (hd : ∀j,A j j=2)
    (hs : A.transpose=A) (hp : (rationalMatrix A).PosDef)
    (ho : ∀i j,i≠j→A i j≤0)
    [Fintype (Roots A)] [DecidableEq (Roots A)] [(rootPairing A hs hp).IsIrreducible]

local notation "b₀" => coordinateBase A hd hs hp ho
local notation "s₀" => coordinateIndexEquiv A hd hs hp ho

theorem opposite_conjugate_by_borel (K : Type) [Field K] [Finite K]
    (g : (Matrix ((b₀).support⊕Roots A) ((b₀).support⊕Roots A) K)ˣ)
    (hg : g∈canonicalElementaryGroup (realizationData A hs hp b₀ s₀) K)
    (hdisj : rootGroup A hs hp b₀ s₀ K false ⊓
      (rootGroup A hs hp b₀ s₀ K false).map (MulAut.conj g).toMonoidHom=⊥) :
    ∃b∈borelEnvelope A hs hp b₀ s₀ K,
      (rootGroup A hs hp b₀ s₀ K false).map (MulAut.conj g).toMonoidHom=
        (rootGroup A hs hp b₀ s₀ K true).map (MulAut.conj b).toMonoidHom := by
  obtain ⟨w,b,hb,c,hc,he⟩ := canonical_bruhat_cover A hd hs hp ho K g hg
  have hbN := borelEnvelope_le_normalizer_positive A hs hp b₀ s₀ K hb
  have hcN := borelEnvelope_le_normalizer_positive A hs hp b₀ s₀ K hc
  have hmap : (rootGroup A hs hp b₀ s₀ K false).map (MulAut.conj g).toMonoidHom=
      ((rootGroup A hs hp b₀ s₀ K false).map
        (MulAut.conj (wordUnit A hs hp b₀ s₀ K w)).toMonoidHom).map
          (MulAut.conj b).toMonoidHom := by
    rw [he,conjugate_mul,conjugate_eq_of_mem_normalizer _ c hcN,conjugate_mul]
  have hw : rootGroup A hs hp b₀ s₀ K false ⊓
      (rootGroup A hs hp b₀ s₀ K false).map
        (MulAut.conj (wordUnit A hs hp b₀ s₀ K w)).toMonoidHom=⊥ := by
    apply (inf_conjugate_eq_bot_iff _ _ b hbN).mp
    rw [←hmap]
    exact hdisj
  refine ⟨b,hb,?_⟩
  rw [hmap,word_positive_map_eq_negative_of_disjoint A hd hs hp ho K w hw]

end SymmetricSubgroupAsymptotics.CFSGNormTwoCoordinateOppositeAlignment
