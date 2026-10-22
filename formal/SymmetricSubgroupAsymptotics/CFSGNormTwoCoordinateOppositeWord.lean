import SymmetricSubgroupAsymptotics.CFSGNormTwoCoordinateNormalizerWord
import Mathlib.Algebra.Group.Subgroup.Finite

/-! Disjoint positive Sylow candidates force every simple image of the
actual Weyl word to be negative. In finite fields this identifies its
whole conjugate with the literal opposite subgroup, without selecting
a longest word or using an order formula. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
namespace SymmetricSubgroupAsymptotics.CFSGNormTwoCoordinateOppositeWord
open CFSGIntegerMatrixPairing CFSGNormTwoRootPairing
open CFSGNormTwoGeckIntegralRealization CFSGNormTwoGeckPositivePGroup
open CFSGNormTwoGeckWeylWordDegree CFSGNormTwoGeckWeylWordAlgebra
open CFSGNormTwoCoordinateWeylRootMembership
open CFSGNormTwoGeckOppositeIntersection CFSGNormTwoCoordinateHeight
open CFSGSerreQuadraticMatrix CFSGNormTwoGeckFieldOpposition
variable {r : ℕ} (A : Matrix (Fin r) (Fin r) ℤ) (hd : ∀j,A j j=2)
    (hs : A.transpose=A) (hp : (rationalMatrix A).PosDef)
    (ho : ∀i j,i≠j→A i j≤0)
    [Fintype (Roots A)] [DecidableEq (Roots A)] [(rootPairing A hs hp).IsIrreducible]

local notation "b₀" => coordinateBase A hd hs hp ho
local notation "s₀" => coordinateIndexEquiv A hd hs hp ho

theorem word_simple_nonpositive_of_disjoint (K : Type) [Field K] (w : List (Fin r))
    (hdisj : rootGroup A hs hp b₀ s₀ K false ⊓
      (rootGroup A hs hp b₀ s₀ K false).map
        (MulAut.conj (wordUnit A hs hp b₀ s₀ K w)).toMonoidHom = ⊥)
    (i : Fin r) : ∀l,(wordRoot A hs hp b₀ s₀ w (s₀ i)).val l≤0 := by
  rcases word_sign_membership A hd hs hp ho K w i 1 with hpos|hneg
  · have hu : canonicalRoot (realizationData A hs hp b₀ s₀) K false i 1∈
        rootGroup A hs hp b₀ s₀ K false := Subgroup.subset_closure ⟨(i,1),rfl⟩
    have him : rootWord A hd hs hp ho K w i 1∈
        (rootGroup A hs hp b₀ s₀ K false).map
          (MulAut.conj (wordUnit A hs hp b₀ s₀ K w)).toMonoidHom := ⟨_,hu,rfl⟩
    have hb : rootWord A hd hs hp ho K w i 1∈
        rootGroup A hs hp b₀ s₀ K false ⊓
          (rootGroup A hs hp b₀ s₀ K false).map
            (MulAut.conj (wordUnit A hs hp b₀ s₀ K w)).toMonoidHom := ⟨hpos.2,him⟩
    rw [hdisj,Subgroup.mem_bot] at hb
    have he : canonicalRoot (realizationData A hs hp b₀ s₀) K false i 1=
        (wordUnit A hs hp b₀ s₀ K w)⁻¹*rootWord A hd hs hp ho K w i 1*
          wordUnit A hs hp b₀ s₀ K w := by
      dsimp only [rootWord]
      group
    rw [hb,mul_one,inv_mul_cancel] at he
    exact False.elim (canonicalRoot_one_ne_one A hs hp b₀ s₀ coordinateHeight
      (simple_height A hd hs hp ho) K i he)
  · exact hneg.1

theorem word_positive_map_le_negative_of_disjoint (K : Type) [Field K]
    (w : List (Fin r))
    (hdisj : rootGroup A hs hp b₀ s₀ K false ⊓
      (rootGroup A hs hp b₀ s₀ K false).map
        (MulAut.conj (wordUnit A hs hp b₀ s₀ K w)).toMonoidHom = ⊥) :
    (rootGroup A hs hp b₀ s₀ K false).map
      (MulAut.conj (wordUnit A hs hp b₀ s₀ K w)).toMonoidHom ≤
        rootGroup A hs hp b₀ s₀ K true := by
  apply Subgroup.map_le_iff_le_comap.mpr
  apply (Subgroup.closure_le _).mpr
  rintro _ ⟨z,rfl⟩
  exact negative_word_mem A hd hs hp ho K w z.1 z.2
    (word_simple_nonpositive_of_disjoint A hd hs hp ho K w hdisj z.1)

theorem word_positive_map_eq_negative_of_disjoint (K : Type) [Field K] [Finite K]
    (w : List (Fin r))
    (hdisj : rootGroup A hs hp b₀ s₀ K false ⊓
      (rootGroup A hs hp b₀ s₀ K false).map
        (MulAut.conj (wordUnit A hs hp b₀ s₀ K w)).toMonoidHom = ⊥) :
    (rootGroup A hs hp b₀ s₀ K false).map
      (MulAut.conj (wordUnit A hs hp b₀ s₀ K w)).toMonoidHom =
        rootGroup A hs hp b₀ s₀ K true := by
  apply Subgroup.eq_of_le_of_card_ge
    (word_positive_map_le_negative_of_disjoint A hd hs hp ho K w hdisj)
  have hc := Nat.card_congr ((MulAut.conj (wordUnit A hs hp b₀ s₀ K w)).subgroupMap
    (rootGroup A hs hp b₀ s₀ K false)).toEquiv
  have hv := Nat.card_congr ((MulAut.conj (oppositionUnit A hs hp b₀ K)).subgroupMap
    (rootGroup A hs hp b₀ s₀ K false)).toEquiv
  change Nat.card (rootGroup A hs hp b₀ s₀ K false)=
    Nat.card ((rootGroup A hs hp b₀ s₀ K false).map
      (MulAut.conj (oppositionUnit A hs hp b₀ K)).toMonoidHom) at hv
  rw [opposition_positive_eq_negative A hs hp b₀ s₀ K] at hv
  exact (hv.symm.trans hc).le

end SymmetricSubgroupAsymptotics.CFSGNormTwoCoordinateOppositeWord
