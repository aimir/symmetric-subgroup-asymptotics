import SymmetricSubgroupAsymptotics.CFSGNormTwoCoordinateWeylRootMembership
import SymmetricSubgroupAsymptotics.CFSGNormTwoGeckSelfRootConjugation
import SymmetricSubgroupAsymptotics.CFSGNormTwoGeckWeylWordAlgebra
import Mathlib.Tactic.Group

/-! An actual Weyl word carrying a simple root into the negative cone
carries its NEGATIVE simple parameter into the positive subgroup. This
retains the exact all-field unit identity, providing a chamber-descent
extraction step for overgroups of positive root subgroups. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
namespace SymmetricSubgroupAsymptotics.CFSGNormTwoCoordinateNegativeRootWordMembership
open CFSGIntegerMatrixPairing CFSGNormTwoRootPairing CFSGNormTwoGeckColumns
open CFSGNormTwoGeckIntegralRealization CFSGNormTwoGeckPositivePGroup
open CFSGNormTwoGeckWeylWordDegree CFSGNormTwoGeckWeylWordAlgebra
open CFSGNormTwoCoordinateWeylRootMembership CFSGNormTwoGeckSelfRootConjugation
open CFSGSerreQuadraticMatrix
variable {r : ℕ} (A : Matrix (Fin r) (Fin r) ℤ) (hd : ∀j,A j j=2)
    (hs : A.transpose=A) (hp : (rationalMatrix A).PosDef)
    (ho : ∀i j,i≠j→A i j≤0)
    [Fintype (Roots A)] [DecidableEq (Roots A)] [(rootPairing A hs hp).IsIrreducible]
local notation "b₀" => coordinateBase A hd hs hp ho
local notation "s₀" => coordinateIndexEquiv A hd hs hp ho
local notation "D" => realizationData A hs hp b₀ s₀

theorem appended_self_root_word (K : Type) [Field K] (w : List (Fin r)) (i : Fin r) (t : K) :
    rootWord A hd hs hp ho K (w++[i]) i (-t)=
      wordUnit A hs hp b₀ s₀ K w*canonicalRoot D K true i t*
        (wordUnit A hs hp b₀ s₀ K w)⁻¹ := by
  unfold rootWord
  rw [wordUnit_append]
  change (wordUnit A hs hp b₀ s₀ K w*(canonicalWeyl D K i*1))*
    canonicalRoot D K false i (-t)*
      (wordUnit A hs hp b₀ s₀ K w*(canonicalWeyl D K i*1))⁻¹=_
  rw [mul_one]
  calc
    _=wordUnit A hs hp b₀ s₀ K w*
        (canonicalWeyl D K i*canonicalRoot D K false i (-t)*(canonicalWeyl D K i)⁻¹)*
          (wordUnit A hs hp b₀ s₀ K w)⁻¹ := by group
    _=_ := by rw [self_root_word,neg_neg]

theorem positive_negative_root_word (K : Type) [Field K] (w : List (Fin r))
    (i : Fin r) (t : K) (hneg : ∀j,(wordRoot A hs hp b₀ s₀ w (s₀ i)).val j≤0) :
    wordUnit A hs hp b₀ s₀ K w*canonicalRoot D K true i t*
      (wordUnit A hs hp b₀ s₀ K w)⁻¹∈rootGroup A hs hp b₀ s₀ K false := by
  rw [←appended_self_root_word A hd hs hp ho K w i t]
  apply positive_word_mem A hd hs hp ho K (w++[i]) i (-t)
  have he : (wordRoot A hs hp b₀ s₀ (w++[i]) (s₀ i)).val=
      -(wordRoot A hs hp b₀ s₀ w (s₀ i)).val := by
    rw [wordRoot_append]
    change (wordRoot A hs hp b₀ s₀ w (negativeIndex A hs hp (s₀ i))).val=_
    exact wordRoot_negative_val A hs hp b₀ s₀ w (s₀ i)
  intro j
  rw [he]
  exact neg_nonneg.mpr (hneg j)

end SymmetricSubgroupAsymptotics.CFSGNormTwoCoordinateNegativeRootWordMembership
