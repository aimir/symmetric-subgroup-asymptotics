import SymmetricSubgroupAsymptotics.BinaryInvariantRegistry
import SymmetricSubgroupAsymptotics.PermutationSubrepresentationHead
import Mathlib.GroupTheory.GroupAction.MultipleTransitivity
import Mathlib.LinearAlgebra.Pi

/-!
# Pair vectors in a nonconstant natural binary orbit span

A three-cycle extracts a pair vector from a nonconstant binary function.
The two-transitivity of the alternating group then supplies every pair
vector. All point types and acting groups remain symbolic.
-/

set_option autoImplicit false
noncomputable section
open scoped BigOperators

namespace SymmetricSubgroupAsymptotics
namespace NaturalBinaryAlternating

variable {X : Type} [Fintype X] [DecidableEq X]

/-- The binary vector supported at two displayed points. -/
def pairVector (a b : X) : X → ZMod 2 :=
  Pi.single a 1 + Pi.single b 1

private theorem binary_zero_or_one (x : ZMod 2) : x = 0 ∨ x = 1 := by
  have hx : x.val < 2 := ZMod.val_lt x
  have hx01 : x.val = 0 ∨ x.val = 1 := by omega
  rcases hx01 with hx0 | hx1
  · left
    apply ZMod.val_injective 2
    simpa only [ZMod.val_zero] using hx0
  · right
    apply ZMod.val_injective 2
    rw [ZMod.val_one_eq_one_mod]
    exact hx1

private theorem binary_add_of_ne (x y : ZMod 2) (h : x ≠ y) : x + y = 1 := by
  rcases binary_zero_or_one x with rfl | rfl <;>
    rcases binary_zero_or_one y with rfl | rfl <;> norm_num at *

private theorem binary_eq_of_ne (x y z : ZMod 2) (h : x ≠ y) : z = x ∨ z = y := by
  rcases binary_zero_or_one x with rfl | rfl <;>
    rcases binary_zero_or_one y with rfl | rfl <;>
    rcases binary_zero_or_one z with rfl | rfl <;> norm_num at *

private theorem orbitSpan_apply_mem {G V : Type} [Group G]
    [AddCommGroup V] [Module (ZMod 2) V]
    (rho : Representation (ZMod 2) G V) (v : V) (g : G)
    {x : V} (hx : x ∈ binaryOrbitSpan rho v) :
    rho g x ∈ binaryOrbitSpan rho v := by
  induction hx using Submodule.span_induction with
  | mem x hx =>
      obtain ⟨h, rfl⟩ := hx
      rw [← Module.End.mul_apply, ← map_mul]
      exact Submodule.subset_span ⟨g * h, rfl⟩
  | zero => simp
  | add x y _ _ hx hy =>
      simpa only [map_add] using (binaryOrbitSpan rho v).add_mem hx hy
  | smul a x _ hx =>
      simpa only [map_smul] using (binaryOrbitSpan rho v).smul_mem a hx

variable (T : Subgroup (Equiv.Perm X))

omit [Fintype X] in
/-- Permutation action transports a pair vector to its image pair. -/
theorem action_pairVector (g : T) (a b : X) :
    permutationFunctionRepresentation (ZMod 2) T X g (pairVector a b) =
      pairVector (g.1 a) (g.1 b) := by
  ext x
  change (Pi.single a (1 : ZMod 2) : X → ZMod 2) (g.1.symm x) +
      (Pi.single b (1 : ZMod 2) : X → ZMod 2) (g.1.symm x) = _
  simp [pairVector, Pi.single_apply, Equiv.symm_apply_eq]

/-- One three-cycle already produces a pair vector in a nonconstant
function's orbit span. -/
theorem exists_pairVector_mem_orbitSpan
    (hT : alternatingGroup X ≤ T) (hcard : 4 ≤ Nat.card X)
    (v : X → ZMod 2) (hnonconstant : ∃ a b, v a ≠ v b) :
    ∃ a b, a ≠ b ∧ pairVector a b ∈
      binaryOrbitSpan (permutationFunctionRepresentation (ZMod 2) T X) v := by
  obtain ⟨a, b, hv⟩ := hnonconstant
  have hab : a ≠ b := fun h ↦ hv (congrArg v h)
  have hlt : ({a, b} : Finset X).card < (Finset.univ : Finset X).card := by
    rw [Finset.card_pair hab, Finset.card_univ, ← Nat.card_eq_fintype_card]
    omega
  obtain ⟨c, _, hc⟩ := Finset.exists_mem_notMem_of_card_lt_card hlt
  simp only [Finset.mem_insert, Finset.mem_singleton, not_or] at hc
  have hac : a ≠ c := Ne.symm hc.1
  have hbc : b ≠ c := Ne.symm hc.2
  let p : Equiv.Perm X := Equiv.swap a b * Equiv.swap b c
  have hp : p ∈ alternatingGroup X := by
    simp [p, Equiv.Perm.mem_alternatingGroup, hab, hbc]
  let g : T := ⟨p, hT hp⟩
  let S := binaryOrbitSpan (permutationFunctionRepresentation (ZMod 2) T X) v
  have hvS : v ∈ S := binaryOrbitSpan_point _ _
  have hsum : v + permutationFunctionRepresentation (ZMod 2) T X g v ∈ S :=
    S.add_mem hvS (Submodule.subset_span ⟨g, rfl⟩)
  have hinv (x : X) :
      permutationFunctionRepresentation (ZMod 2) T X g v x =
        v (Equiv.swap b c (Equiv.swap a b x)) := rfl
  rcases binary_eq_of_ne (v a) (v b) (v c) hv with hca | hcb
  · refine ⟨b, c, hbc, ?_⟩
    have heq : v + permutationFunctionRepresentation (ZMod 2) T X g v =
        pairVector b c := by
      ext x
      change v x + permutationFunctionRepresentation (ZMod 2) T X g v x = _
      rw [hinv]
      by_cases hxa : x = a
      · subst x
        simp [pairVector, hab, hac, hca, ZModModule.add_self]
      by_cases hxb : x = b
      · subst x
        simp [pairVector, Equiv.swap_apply_def, hab, hac, hbc,
          binary_add_of_ne _ _ hv.symm]
      by_cases hxc : x = c
      · subst x
        simp [pairVector, Equiv.swap_apply_def, Ne.symm hac, Ne.symm hbc,
          hca, binary_add_of_ne _ _ hv]
      · simp [pairVector, Equiv.swap_apply_of_ne_of_ne,
          hxa, hxb, hxc, ZModModule.add_self]
    exact heq ▸ hsum
  · refine ⟨a, b, hab, ?_⟩
    have heq : v + permutationFunctionRepresentation (ZMod 2) T X g v =
        pairVector a b := by
      ext x
      change v x + permutationFunctionRepresentation (ZMod 2) T X g v x = _
      rw [hinv]
      by_cases hxa : x = a
      · subst x
        simp [pairVector, hab, hcb, binary_add_of_ne _ _ hv]
      by_cases hxb : x = b
      · subst x
        simp [pairVector, Equiv.swap_apply_def, hab, hac, Ne.symm hab,
          binary_add_of_ne _ _ hv.symm]
      by_cases hxc : x = c
      · subst x
        simp [pairVector, Equiv.swap_apply_def, Ne.symm hac, Ne.symm hbc,
          hcb, ZModModule.add_self]
      · simp [pairVector, Equiv.swap_apply_of_ne_of_ne,
          hxa, hxb, hxc, ZModModule.add_self]
    exact heq ▸ hsum

/-- Every pair vector lies in the orbit span of a nonconstant function
whenever the acting top contains the alternating group. -/
theorem pairVector_mem_orbitSpan
    (hT : alternatingGroup X ≤ T) (hcard : 4 ≤ Nat.card X)
    (v : X → ZMod 2) (hnonconstant : ∃ a b, v a ≠ v b)
    (a b : X) : pairVector a b ∈
      binaryOrbitSpan (permutationFunctionRepresentation (ZMod 2) T X) v := by
  by_cases hab : a = b
  · subst b
    simp [pairVector, ZModModule.add_self]
  obtain ⟨c, d, hcd, hpair⟩ :=
    exists_pairVector_mem_orbitSpan T hT hcard v hnonconstant
  letI : MulAction.IsMultiplyPretransitive (alternatingGroup X) X
      (Nat.card X - 2) := alternatingGroup.isMultiplyPretransitive X
  have htwo : MulAction.IsMultiplyPretransitive (alternatingGroup X) X 2 :=
    MulAction.isMultiplyPretransitive_of_le (n := Nat.card X - 2)
      (by omega) (Nat.sub_le _ _)
  obtain ⟨g, hga, hgb⟩ := MulAction.is_two_pretransitive_iff.mp htwo hcd hab
  let t : T := ⟨g.1, hT g.2⟩
  have h := orbitSpan_apply_mem
    (permutationFunctionRepresentation (ZMod 2) T X) v t hpair
  rw [action_pairVector] at h
  change g.1 c = a at hga
  change g.1 d = b at hgb
  simpa only [t, hga, hgb] using h

/-- Pair vectors span the kernel of the coordinate-sum functional. -/
theorem mem_of_sum_eq_zero (S : Submodule (ZMod 2) (X → ZMod 2))
    (hpairs : ∀ a b, pairVector a b ∈ S) (b : X)
    (v : X → ZMod 2) (hsum : ∑ i, v i = 0) : v ∈ S := by
  have hdecomp : (∑ i, v i • pairVector i b) =
      v + (∑ i, v i) • Pi.single b (1 : ZMod 2) := by
    simp only [pairVector, smul_add, Finset.sum_add_distrib, ← Finset.sum_smul]
    congr 1
    calc
      (∑ i, v i • Pi.single i (1 : ZMod 2)) = ∑ i, Pi.single i (v i) := by
        apply Finset.sum_congr rfl
        intro i _
        rw [← Pi.single_smul]
        simp
      _ = v := LinearMap.sum_single_apply (fun _ : X ↦ ZMod 2) v
  have hm : (∑ i, v i • pairVector i b) ∈ S :=
    S.sum_mem fun i _ ↦ S.smul_mem (v i) (hpairs i b)
  simpa only [hdecomp, hsum, zero_smul, add_zero] using hm

end NaturalBinaryAlternating
end SymmetricSubgroupAsymptotics

end
