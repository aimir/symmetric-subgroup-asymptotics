import SymmetricSubgroupAsymptotics.CFSGNormTwoCoordinateOppositeWord

/-! A Weyl word sending every original simple root to the negative
cone sends the whole actual positive subgroup to the negative subgroup.
This retains the sign conclusion separately from an ambient-disjointness
hypothesis, allowing fixed-point intersection tests. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
namespace SymmetricSubgroupAsymptotics.CFSGNormTwoCoordinateNegativeSimpleWord
open CFSGIntegerMatrixPairing CFSGNormTwoRootPairing CFSGNormTwoGeckIntegralRealization
open CFSGNormTwoGeckPositivePGroup CFSGNormTwoGeckWeylWordDegree
open CFSGNormTwoCoordinateWeylRootMembership CFSGNormTwoGeckFieldOpposition
variable {r : ℕ} (A : Matrix (Fin r) (Fin r) ℤ) (hd : ∀j,A j j=2)
    (hs : A.transpose=A) (hp : (rationalMatrix A).PosDef)
    (ho : ∀i j,i≠j→A i j≤0)
    [Fintype (Roots A)] [DecidableEq (Roots A)] [(rootPairing A hs hp).IsIrreducible]
local notation "b₀" => coordinateBase A hd hs hp ho
local notation "s₀" => coordinateIndexEquiv A hd hs hp ho

theorem positive_map_le_negative_of_simple_nonpositive (K : Type) [Field K]
    (w : List (Fin r)) (hw : ∀i l,(wordRoot A hs hp b₀ s₀ w (s₀ i)).val l≤0) :
    (rootGroup A hs hp b₀ s₀ K false).map
      (MulAut.conj (wordUnit A hs hp b₀ s₀ K w)).toMonoidHom≤
        rootGroup A hs hp b₀ s₀ K true := by
  apply Subgroup.map_le_iff_le_comap.mpr
  apply (Subgroup.closure_le _).mpr
  rintro _ ⟨z,rfl⟩
  exact negative_word_mem A hd hs hp ho K w z.1 z.2 (hw z.1)

theorem positive_map_eq_negative_of_simple_nonpositive (K : Type) [Field K] [Finite K]
    (w : List (Fin r)) (hw : ∀i l,(wordRoot A hs hp b₀ s₀ w (s₀ i)).val l≤0) :
    (rootGroup A hs hp b₀ s₀ K false).map
      (MulAut.conj (wordUnit A hs hp b₀ s₀ K w)).toMonoidHom=
        rootGroup A hs hp b₀ s₀ K true := by
  apply Subgroup.eq_of_le_of_card_ge
    (positive_map_le_negative_of_simple_nonpositive A hd hs hp ho K w hw)
  have hc := Nat.card_congr ((MulAut.conj (wordUnit A hs hp b₀ s₀ K w)).subgroupMap
    (rootGroup A hs hp b₀ s₀ K false)).toEquiv
  have hv := Nat.card_congr ((MulAut.conj (oppositionUnit A hs hp b₀ K)).subgroupMap
    (rootGroup A hs hp b₀ s₀ K false)).toEquiv
  change Nat.card (rootGroup A hs hp b₀ s₀ K false)=
    Nat.card ((rootGroup A hs hp b₀ s₀ K false).map
      (MulAut.conj (oppositionUnit A hs hp b₀ K)).toMonoidHom) at hv
  rw [opposition_positive_eq_negative A hs hp b₀ s₀ K] at hv
  exact (hv.symm.trans hc).le

end SymmetricSubgroupAsymptotics.CFSGNormTwoCoordinateNegativeSimpleWord
