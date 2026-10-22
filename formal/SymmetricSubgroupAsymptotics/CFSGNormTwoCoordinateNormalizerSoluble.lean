import SymmetricSubgroupAsymptotics.CFSGNormTwoCoordinateLiftedNormalizer
import SymmetricSubgroupAsymptotics.CFSGSolubleNormalizerProduct
import SymmetricSubgroupAsymptotics.CFSGNormTwoGeckWeylWordTorus

/-! Solubility of the actual positive-group normalizer inside the original
coordinate elementary group. This theorem does not assert that the positive
group is Sylow, nor identify its normalizer with the Borel envelope. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
namespace SymmetricSubgroupAsymptotics.CFSGNormTwoCoordinateNormalizerSoluble
open CFSGIntegerMatrixPairing CFSGNormTwoRootPairing CFSGSerreQuadraticMatrix
open CFSGNormTwoGeckIntegralRealization CFSGNormTwoGeckPositivePGroup
open CFSGNormTwoGeckLiftedWeylWords CFSGNormTwoCoordinateLiftedNormalizer
open CFSGNormTwoGeckWeylWordDegree CFSGNormTwoCoordinateNormalizerWord
open CFSGNormTwoGeckBorelEnvelope CFSGNormTwoGeckBorelNormalization
open CFSGNormTwoGeckWeylWordTorus CFSGNormTwoGeckWeylSquareTorus
open CFSGNormTwoCoordinateHeight
open CFSGExceptionalDiagramAutomorphisms
variable {r : ℕ} (A : Matrix (Fin r) (Fin r) ℤ) (hd : ∀j,A j j=2)
    (hs : A.transpose=A) (hp : (rationalMatrix A).PosDef)
    (ho : ∀i j,i≠j→A i j≤0)
    [Fintype (Roots A)] [DecidableEq (Roots A)] [(rootPairing A hs hp).IsIrreducible]

local notation "b₀" => coordinateBase A hd hs hp ho
local notation "s₀" => coordinateIndexEquiv A hd hs hp ho

def positiveWordGroup (K : Type) [Field K] : Subgroup
    ((Matrix ((b₀).support⊕Roots A) ((b₀).support⊕Roots A) K)ˣ) :=
  ((MonoidHom.fst _ _).comp (liftedPositive A hd hs hp ho K).subtype).range

theorem positiveWordGroup_soluble (K : Type) [Field K]
    (ε : Fin r→ℤ) (hε : ∀i,ε i*ε i=1)
    (hA : ∀i j,ε i*|A i j|=A j i*ε j)
    [IsSolvable (diagramGroup A)] : IsSolvable (positiveWordGroup A hd hs hp ho K) := by
  letI := liftedPositive_soluble A hd hs hp ho K ε hε hA
  exact solvable_of_surjective
    (f:=((MonoidHom.fst _ _).comp (liftedPositive A hd hs hp ho K).subtype).rangeRestrict)
    (MonoidHom.rangeRestrict_surjective _)

theorem wordUnit_mem_canonical (K : Type) [Field K] (w : List (Fin r)) :
    wordUnit A hs hp b₀ s₀ K w∈canonicalElementaryGroup (realizationData A hs hp b₀ s₀) K := by
  induction w with
  | nil=>exact Subgroup.one_mem _
  | cons i w ih=>
    apply (canonicalElementaryGroup (realizationData A hs hp b₀ s₀) K).mul_mem _ ih
    simpa only [parameterWeyl_one] using parameterWeyl_mem A hs hp b₀ s₀ K i 1

theorem positiveWordGroup_le_normalizer_borel (K : Type) [Field K] :
    positiveWordGroup A hd hs hp ho K≤Subgroup.normalizer
      (borelEnvelope A hs hp b₀ s₀ K : Set _) := by
  rintro g ⟨x,rfl⟩
  obtain ⟨w,hw⟩ := x.property.1
  apply (rootGroup A hs hp b₀ s₀ K false).normalizer_inf_normalizer_le_normalizer_sup
    (torusGroup A hs hp b₀ s₀ K)
  constructor
  · exact x.property.2
  · change x.val.1∈Subgroup.normalizer (torusGroup A hs hp b₀ s₀ K : Set _)
    have hfst : wordUnit A hs hp b₀ s₀ K w=x.val.1 := congrArg Prod.fst hw
    rw [←hfst]
    exact wordUnit_mem_torus_normalizer A hs hp b₀ s₀ K w

theorem normalizer_inter_model_soluble (K : Type) [Field K]
    (ε : Fin r→ℤ) (hε : ∀i,ε i*ε i=1)
    (hA : ∀i j,ε i*|A i j|=A j i*ε j)
    [IsSolvable (diagramGroup A)] : IsSolvable
    ↥(Subgroup.normalizer (rootGroup A hs hp b₀ s₀ K false : Set _) ⊓
      canonicalElementaryGroup (realizationData A hs hp b₀ s₀) K) := by
  let B := borelEnvelope A hs hp b₀ s₀ K
  let W := positiveWordGroup A hd hs hp ho K
  let N : Subgroup ((Matrix ((b₀).support⊕Roots A) ((b₀).support⊕Roots A) K)ˣ) :=
    Subgroup.normalizer (rootGroup A hs hp b₀ s₀ K false : Set _) ⊓
    canonicalElementaryGroup (realizationData A hs hp b₀ s₀) K
  have hB : B≤N := le_inf (borelEnvelope_le_normalizer_positive A hs hp b₀ s₀ K)
    (borelEnvelope_le_canonical A hs hp b₀ s₀ K)
  have hW : W≤N := by
    rintro g ⟨x,rfl⟩
    obtain ⟨w,hw⟩ := x.property.1
    refine ⟨x.property.2,?_⟩
    change x.val.1∈canonicalElementaryGroup (realizationData A hs hp b₀ s₀) K
    have hfst : wordUnit A hs hp b₀ s₀ K w=x.val.1 := congrArg Prod.fst hw
    rw [←hfst]
    exact wordUnit_mem_canonical A hd hs hp ho K w
  letI : IsSolvable B := borelEnvelope_soluble A hs hp b₀ s₀ coordinateHeight
    (simple_height A hd hs hp ho) K
  letI : IsSolvable W := positiveWordGroup_soluble A hd hs hp ho K ε hε hA
  apply CFSGSolubleNormalizerProduct.soluble_of_product_cover N B W hB hW
    (positiveWordGroup_le_normalizer_borel A hd hs hp ho K)
  intro g hg
  obtain ⟨w,b,hb,c,hc,he,hn,_⟩ := normalizer_word_reduction A hd hs hp ho K g hg.2 hg.1
  have hwW : wordUnit A hs hp b₀ s₀ K w∈W := by
    refine ⟨⟨wordPair A hs hp b₀ s₀ K w,?_⟩,rfl⟩
    exact ⟨wordPair_mem_liftedWeyl A hs hp b₀ s₀ K w,hn⟩
  have hnB := positiveWordGroup_le_normalizer_borel A hd hs hp ho K hwW
  have hconj : wordUnit A hs hp b₀ s₀ K w*c*(wordUnit A hs hp b₀ s₀ K w)⁻¹∈B :=
    (Subgroup.mem_normalizer_iff.mp hnB c).mp hc
  refine ⟨b*(wordUnit A hs hp b₀ s₀ K w*c*(wordUnit A hs hp b₀ s₀ K w)⁻¹),
    B.mul_mem hb hconj,wordUnit A hs hp b₀ s₀ K w,hwW,?_⟩
  rw [he]
  group

end SymmetricSubgroupAsymptotics.CFSGNormTwoCoordinateNormalizerSoluble
