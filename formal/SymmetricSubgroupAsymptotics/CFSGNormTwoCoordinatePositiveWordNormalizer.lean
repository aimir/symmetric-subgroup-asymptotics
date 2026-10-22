import SymmetricSubgroupAsymptotics.CFSGNormTwoCoordinateWeylRootMembership
import SymmetricSubgroupAsymptotics.CFSGNormTwoGeckWeylWordAlgebra

/-! A literal Weyl word with positive images of all simple roots
normalizes the SAME finite positive group. Only actual containment and
conjugation cardinality are used, with no longest-word recognition. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
namespace SymmetricSubgroupAsymptotics.CFSGNormTwoCoordinatePositiveWordNormalizer
open CFSGIntegerMatrixPairing CFSGNormTwoRootPairing CFSGSerreQuadraticMatrix
open CFSGNormTwoGeckIntegralRealization CFSGNormTwoGeckPositivePGroup
open CFSGNormTwoGeckWeylWordDegree CFSGNormTwoGeckWeylWordAlgebra
open CFSGNormTwoCoordinateWeylRootMembership
variable {r : ℕ} (A : Matrix (Fin r) (Fin r) ℤ) (hd : ∀j,A j j=2)
    (hs : A.transpose=A) (hp : (rationalMatrix A).PosDef)
    (ho : ∀i j,i≠j→A i j≤0)
    [Fintype (Roots A)] [DecidableEq (Roots A)] [(rootPairing A hs hp).IsIrreducible]
    (K : Type) [Field K] [Finite K]
local notation "b₀" => coordinateBase A hd hs hp ho
local notation "s₀" => coordinateIndexEquiv A hd hs hp ho
local notation "U" => rootGroup A hs hp b₀ s₀ K false
private abbrev Mat := Matrix ((b₀).support⊕Roots A) ((b₀).support⊕Roots A) K

theorem positive_word_mem_normalizer (w : List (Fin r))
    (hw : ∀i j,0≤(wordRoot A hs hp b₀ s₀ w (s₀ i)).val j) :
    wordUnit A hs hp b₀ s₀ K w∈Subgroup.normalizer (U : Set _) := by
  have hle : (U).map (MulAut.conj (wordUnit A hs hp b₀ s₀ K w)).toMonoidHom≤U := by
    apply Subgroup.map_le_iff_le_comap.mpr
    apply (Subgroup.closure_le _).mpr
    rintro _ ⟨z,rfl⟩
    exact positive_word_mem A hd hs hp ho K w z.1 z.2 (hw z.1)
  have he : (U).map (MulAut.conj (wordUnit A hs hp b₀ s₀ K w)).toMonoidHom=U := by
    apply Subgroup.eq_of_le_of_card_ge hle
    exact (Nat.card_congr ((MulAut.conj (wordUnit A hs hp b₀ s₀ K w)).subgroupMap U).toEquiv).le
  apply Subgroup.mem_normalizer_iff_conj_image_eq.mpr
  change (((U).map (MulAut.conj (wordUnit A hs hp b₀ s₀ K w)).toMonoidHom) :
    Set (Mat A hd hs hp ho K)ˣ)=(U : Set (Mat A hd hs hp ho K)ˣ)
  exact congrArg (fun H : Subgroup (Mat A hd hs hp ho K)ˣ=>(H : Set (Mat A hd hs hp ho K)ˣ)) he

end SymmetricSubgroupAsymptotics.CFSGNormTwoCoordinatePositiveWordNormalizer
