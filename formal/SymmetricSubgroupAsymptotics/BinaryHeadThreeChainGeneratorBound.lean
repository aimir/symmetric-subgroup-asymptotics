import SymmetricSubgroupAsymptotics.BinaryRegular46HeadThreeMonomialComplete
import SymmetricSubgroupAsymptotics.FiniteChainOperatorGeneratorBound
import SymmetricSubgroupAsymptotics.BinaryCommonEightExtraShearLeading

/-! The checked thirty-six leading-label certificates generate the
original module by seven elements. The caller supplies genuine operators
for each displayed step; no module or normal-subgroup census occurs. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
namespace SymmetricSubgroupAsymptotics
namespace BinaryRegular46HeadThreeMonomial
open BinaryElementaryPairMonomialWidth BinaryBooleanFourPolynomialCoordinates

/-- The same finite steps, with the two original polynomial layers named. -/
def pairStep (c : Fin 36) (op : Op) (a : Monomial) : Option Monomial :=
  match op with
  | .derivative i => if i ∈ support a.2 then some (a.1, removeIndex i a.2) else none
  | .extra => if a.2.val % 2 = 1 ∧ a.2.val < 8 then
      some (a.1, BinaryCommonEightExtraShearLeading.target a.2) else none
  | .shear k => if a.1 = true ∧ Disjoint (support (labels c k)) (support a.2) then
      some (false, unionIndex (labels c k) a.2) else none

set_option maxHeartbeats 2000000 in
theorem pairStep_index : ∀ c op a,
    (pairStep c op a).map BinaryMonomialRaisingWords.index =
      step c op (BinaryMonomialRaisingWords.index a) := by
  intro c op a
  cases op with
  | derivative i => revert c i a; decide
  | extra => revert c a; decide
  | shear k => revert c k a; decide

end BinaryRegular46HeadThreeMonomial

open BinaryRegular46HeadThreeMonomial
local instance : Fact (Nat.Prime 2) := ⟨by decide⟩
variable {A M : Type} [Ring A] [Algebra (ZMod 2) A]
    [AddCommGroup M] [Module A M] [Module (ZMod 2) M]
    [IsScalarTower (ZMod 2) A M] {d : ℕ}

theorem binary_generating_finset_le_seven_of_head_three_steps
    (c : Fin 36) (hd : ModuleGeneratedBy A M d)
    (C : M →ₗ[ZMod 2] (Fin 32 → ZMod 2)) (hC : Function.Injective C)
    (hstep : ∀ op a b, pairStep c op a = some b →
      ∀ v : M, FiniteRowLeadingWeight.HasLeading (C v) (BinaryMonomialRaisingWords.index a) →
        ∃ r : A, FiniteRowLeadingWeight.HasLeading (C (r • v))
          (BinaryMonomialRaisingWords.index b)) :
    ∃ S : Finset M, Submodule.span A (S : Set M) = ⊤ ∧ S.card ≤ 7 := by
  have hs : ∀ op a b, step c op a = some b → ∀ v : M,
      FiniteRowLeadingWeight.HasLeading (C v) a →
      ∃ r : A, FiniteRowLeadingWeight.HasLeading (C (r • v)) b := by
    intro op a b hab v hv
    have hh := pairStep_index c op (BinaryMonomialRaisingWords.index.symm a)
    rw [Equiv.apply_symm_apply, hab] at hh
    cases hp : pairStep c op (BinaryMonomialRaisingWords.index.symm a) with
    | none =>
      have hnone : (none : Option (Fin 32)) = some b := by
        simpa only [hp, Option.map_none] using hh
      cases hnone
    | some z =>
      have hsome : (some (BinaryMonomialRaisingWords.index z) : Option (Fin 32)) = some b := by
        simpa only [hp, Option.map_some] using hh
      have hz : BinaryMonomialRaisingWords.index z = b := Option.some.inj hsome
      obtain ⟨r, hr⟩ := hstep op _ z hp v
        (by simpa only [Equiv.apply_symm_apply] using hv)
      exact ⟨r, hz ▸ hr⟩
  apply algebra_generating_finset_le_of_chain_successors hd C hC 0
    (colour c) (rank c) (next c) (labels_all c) (advance_all c)
  intro v a hv
  exact ModuleLeadingOperatorWords.exists_operator_of_run (step c)
    (fun v a => FiniteRowLeadingWeight.HasLeading (C v) a) hs
    (successorPath c a) a (next c a) (paths_all c a) v hv

end SymmetricSubgroupAsymptotics
