import SymmetricSubgroupAsymptotics.NaturalBinaryAlternatingPairSpan
import SymmetricSubgroupAsymptotics.BinaryInvariantCyclicGeneratorBound

/-!
# Cyclic submodules of the natural binary alternating permutation module

For an even number of points at least four, every submodule is cyclic as
soon as its acting top contains the alternating group. A nonconstant vector
produces all even-sum vectors. An odd-sum vector is nonconstant and therefore
generates the whole space. A subspace consisting of constant vectors has
dimension at most one.
-/

set_option autoImplicit false
noncomputable section
open scoped BigOperators

namespace SymmetricSubgroupAsymptotics
namespace NaturalBinaryAlternating

variable {X : Type} [Fintype X] [DecidableEq X]

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

omit [DecidableEq X] in
private theorem constant_sum_eq_zero (heven : Even (Nat.card X))
    (b : X) (v : X → ZMod 2) (hconstant : ∀ a, v a = v b) :
    ∑ i, v i = 0 := by
  have hcast : (Fintype.card X : ZMod 2) = 0 := by
    rw [← Nat.card_eq_fintype_card]
    obtain ⟨m, hm⟩ := heven
    rw [hm, Nat.cast_add, ZModModule.add_self]
  calc
    ∑ i, v i = ∑ _ : X, v b := Finset.sum_congr rfl (fun i _ ↦ hconstant i)
    _ = 0 := by simp [hcast, nsmul_eq_mul]

/-- Every invariant subspace of the even-degree natural binary action is
one vector's orbit span. This is independent of any finite-state registry. -/
theorem exists_orbitSpan_eq
    (T : Subgroup (Equiv.Perm X)) (hT : alternatingGroup X ≤ T)
    (hcard : 4 ≤ Nat.card X) (heven : Even (Nat.card X))
    (W : Subrepresentation (permutationFunctionRepresentation (ZMod 2) T X)) :
    ∃ v : X → ZMod 2, v ∈ W ∧
      W.toSubmodule = binaryOrbitSpan
        (permutationFunctionRepresentation (ZMod 2) T X) v := by
  letI : Nonempty X := Finite.card_pos_iff.mp (by omega)
  let b : X := Classical.choice inferInstance
  let rho := permutationFunctionRepresentation (ZMod 2) T X
  by_cases hodd : ∃ v : X → ZMod 2, v ∈ W ∧ (∑ i, v i) ≠ 0
  · obtain ⟨v, hvW, hvodd⟩ := hodd
    have hvsum : ∑ i, v i = 1 := by
      rcases binary_zero_or_one (∑ i, v i) with h | h
      · exact (hvodd h).elim
      · exact h
    have hnonconstant : ∃ a c, v a ≠ v c := by
      by_contra h
      push Not at h
      exact hvodd (constant_sum_eq_zero heven b v (fun a ↦ h a b))
    let S := binaryOrbitSpan rho v
    have hvS : v ∈ S := binaryOrbitSpan_point rho v
    have hpairs : ∀ a c, pairVector a c ∈ S :=
      pairVector_mem_orbitSpan T hT hcard v hnonconstant
    refine ⟨v, hvW, le_antisymm ?_ (binaryOrbitSpan_le rho W hvW)⟩
    intro w _
    have hsum : ∑ i, (w + (∑ j, w j) • v) i = 0 := by
      change (∑ i, (w i + (∑ j, w j) * v i)) = 0
      rw [Finset.sum_add_distrib, ← Finset.mul_sum, hvsum, mul_one,
        ZModModule.add_self]
    have hm := mem_of_sum_eq_zero S hpairs b
      (w + (∑ j, w j) • v) hsum
    have hadd := S.add_mem hm (S.smul_mem (∑ j, w j) hvS)
    simpa only [add_assoc, ZModModule.add_self, add_zero] using hadd
  · have hsumW : ∀ v : X → ZMod 2, v ∈ W → ∑ i, v i = 0 := by
      intro v hv
      by_contra h
      exact hodd ⟨v, hv, h⟩
    by_cases hnonconstant : ∃ v : X → ZMod 2, v ∈ W ∧ ∃ a c, v a ≠ v c
    · obtain ⟨v, hvW, hv⟩ := hnonconstant
      refine ⟨v, hvW, le_antisymm ?_ (binaryOrbitSpan_le rho W hvW)⟩
      intro w hw
      exact mem_of_sum_eq_zero _
        (pairVector_mem_orbitSpan T hT hcard v hv) b w (hsumW w hw)
    · have hconstant : ∀ v : X → ZMod 2, v ∈ W → ∀ a, v a = v b := by
        intro v hv a
        by_contra h
        exact hnonconstant ⟨v, hv, a, b, h⟩
      by_cases hone : ∃ v : X → ZMod 2, v ∈ W ∧ v b = 1
      · obtain ⟨v, hvW, hvb⟩ := hone
        refine ⟨v, hvW, le_antisymm ?_ (binaryOrbitSpan_le rho W hvW)⟩
        intro w hw
        have heq : w = (w b) • v := by
          funext a
          change w a = w b * v a
          rw [hconstant w hw a, hconstant v hvW a, hvb, mul_one]
        rw [heq]
        exact (binaryOrbitSpan rho v).smul_mem _ (binaryOrbitSpan_point rho v)
      · refine ⟨0, W.toSubmodule.zero_mem, le_antisymm ?_ (binaryOrbitSpan_le rho W W.toSubmodule.zero_mem)⟩
        intro w hw
        have hwb : w b = 0 := by
          rcases binary_zero_or_one (w b) with h | h
          · exact h
          · exact (hone ⟨w, hw, h⟩).elim
        have hwzero : w = 0 := by
          funext a
          exact (hconstant w hw a).trans hwb
        rw [hwzero]
        exact (binaryOrbitSpan rho 0).zero_mem

/-- A symbolic one-generator bound for every natural binary invariant
subspace under an alternating-containing top of even degree at least four. -/
theorem uniform_one
    (T : Subgroup (Equiv.Perm X)) (hT : alternatingGroup X ≤ T)
    (hcard : 4 ≤ Nat.card X) (heven : Even (Nat.card X)) :
    UniformSubrepresentationGeneratorBound
      (permutationFunctionRepresentation (ZMod 2) T X) 1 := by
  intro W
  obtain ⟨v, _, hv⟩ := exists_orbitSpan_eq T hT hcard heven W
  apply representationGeneratedBy_of_iSup_binaryOrbitSpan
    (permutationFunctionRepresentation (ZMod 2) T X) W 1 (fun _ ↦ v)
  simpa only [iSup_const] using hv

end NaturalBinaryAlternating
end SymmetricSubgroupAsymptotics

end
