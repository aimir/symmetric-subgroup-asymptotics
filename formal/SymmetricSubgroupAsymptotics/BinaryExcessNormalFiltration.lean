import SymmetricSubgroupAsymptotics.BinaryExcessMaximalTailAxes
import SymmetricSubgroupAsymptotics.MarkedC4ActualNormalSubdirectFiltration
import SymmetricSubgroupAsymptotics.NormalGeneratorActualIntersectionImage

/-! A maximal-tail normal filtration separates the original dependent
kernel from its actual full-tail image. Only proper normal subgroups of
dependent factors are charged. Local bounds remain theorem hypotheses
for reuse; this module declares no published input. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
open scoped Classical BigOperators

namespace SymmetricSubgroupAsymptotics.BinaryExcessNormalFiltration

open MarkedC4 MarkedC4.RDTOriginalWordStructure
open BinaryExcessMaximalTailAxes

variable {t : ℕ} (K : Fin t → Type) [∀ i, Group (K i)] [∀ i, Finite (K i)]
    (L : Subgroup (∀ i, K i))
    (hfull : ∀ i, Function.Surjective (coordinate K L i))
    (tail : Finset (Fin t)) (hmax : MaximalTail K L tail)

include hfull hmax

/-- The literal tail kernel pays only local proper-normal costs outside
the maximal full tail, and zero for coordinates in the tail. -/
theorem kernel_normalGen_le
    (N : Subgroup L) [N.Normal] (weight : Fin t → ℝ)
    (hlocal : ∀ i, i ∉ tail → ∀ V : Subgroup (K i), V.Normal → V ≠ ⊤ →
      (normalGen V : ℝ) ≤ weight i) :
    (normalGen (N ⊓ (tailProjection K L tail).ker) : ℝ) ≤
      ∑ i : Fin t, if i ∈ tail then 0 else weight i := by
  let U := N ⊓ (tailProjection K L tail).ker
  have hb : (normalGen U : ℝ) ≤ ∑ i : Fin t,
      (normalGen (ActualNormalSubdirectFiltration.diagonal K L U i) : ℝ) := by
    exact_mod_cast ActualNormalSubdirectFiltration.normalGen_le_sum_diagonal K L U hfull
  apply hb.trans
  apply Finset.sum_le_sum
  intro i _
  by_cases hi : i ∈ tail
  · rw [if_pos hi]
    have hz : ∀ x ∈ U, ActualSubdirectFiltration.coordinate K L i x = 1 := by
      intro x hx
      have he := MonoidHom.mem_ker.mp hx.2
      exact congrFun he (⟨i, hi⟩ : {j // j ∈ tail})
    rw [ActualNormalSubdirectFiltration.diagonal_eq_bot_of_zero K L U i hz,
      normalGen_bot, Nat.cast_zero]
  · rw [if_neg hi]
    apply hlocal i hi _
      (ActualNormalSubdirectFiltration.diagonalNormal K L U hfull i)
    apply map_ne_top_of_le_kernel K L tail hmax i hi
    exact inf_le_left.trans inf_le_right

/-- Normal generation of the whole original normal subgroup is the sum
of its dependent-kernel budget and its actual full-tail image budget. -/
theorem normalGen_le_kernel_weights_add_tail
    (N : Subgroup L) [N.Normal] (weight : Fin t → ℝ)
    (hlocal : ∀ i, i ∉ tail → ∀ V : Subgroup (K i), V.Normal → V ≠ ⊤ →
      (normalGen V : ℝ) ≤ weight i) :
    (normalGen N : ℝ) ≤
      (∑ i : Fin t, if i ∈ tail then 0 else weight i) +
        normalGen (N.map (tailProjection K L tail)) := by
  have h := normalGen_le_actual_intersection_add_image
    (tailProjection K L tail) hmax.1 N
    (normalGen (N ⊓ (tailProjection K L tail).ker))
    (normalGen (N.map (tailProjection K L tail))) le_rfl le_rfl
  have hr : (normalGen N : ℝ) ≤
      (normalGen (N ⊓ (tailProjection K L tail).ker) : ℝ) +
        normalGen (N.map (tailProjection K L tail)) := by exact_mod_cast h
  exact hr.trans (add_le_add (kernel_normalGen_le K L hfull tail hmax N weight hlocal) le_rfl)

end SymmetricSubgroupAsymptotics.BinaryExcessNormalFiltration
