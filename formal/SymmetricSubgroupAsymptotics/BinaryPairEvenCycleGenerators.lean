import SymmetricSubgroupAsymptotics.BinaryPairEvenKernelGenerators
import SymmetricSubgroupAsymptotics.LiteralCyclicOrbitWitness

/-! One adjacent pair flip and one literal six-cycle supply all even
pair flips by telescoping along the cycle. The six-point orbit certificate
is shared, so an odd-offset original element gives uniform bound one. -/

set_option autoImplicit false
noncomputable section
open scoped Classical BigOperators

namespace SymmetricSubgroupAsymptotics.BinaryPairEvenCycleGenerators

def pairCycle : Equiv.Perm (Fin 6) where
  toFun := ![1, 2, 3, 4, 5, 0]
  invFun := ![5, 0, 1, 2, 3, 4]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

theorem pairCycle_zero (i : Fin 6) : (pairCycle ^ i.val) 0 = i := by
  revert i
  decide +kernel

variable {X : Type} {U : Subgroup (Equiv.Perm X)}
  (F : BinaryPairFrame U (Fin 6)) (c : U) (k : F.top.ker)

def anchorFlip (i : Fin 6) : F.top.ker :=
  ((List.range i.val).map (fun j ↦ MulAut.conjNormal (c ^ j) k)).prod

private theorem bits_mul (a b : F.top.ker) : F.bits (a * b) = F.bits a + F.bits b :=
  congrArg Multiplicative.toAdd (F.bitsHom.map_mul a b)

private theorem bits_one : F.bits (1 : F.top.ker) = 0 :=
  congrArg Multiplicative.toAdd F.bitsHom.map_one

theorem anchorFlip_bits
    (hc : F.top c = pairCycle)
    (hk : F.bits k = Pi.single 0 (1 : ZMod 2) + Pi.single 1 (1 : ZMod 2))
    (i : Fin 6) :
    F.bits (anchorFlip F c k i) = Pi.single 0 (1 : ZMod 2) + Pi.single i (1 : ZMod 2) := by
  have hconj (n : ℕ) (j : Fin 6) :
      F.bits (((MulAut.conjNormal c : MulAut F.top.ker) ^ n) k) j =
        (Pi.single 0 (1 : ZMod 2) + Pi.single 1 1 : Fin 6 → ZMod 2)
          ((pairCycle ^ n)⁻¹ j) := by
    have hn : (MulAut.conjNormal c : MulAut F.top.ker) ^ n =
        MulAut.conjNormal (c ^ n) :=
      (map_pow (MulAut.conjNormal (H := F.top.ker)) c n).symm
    rw [hn, F.bits_conjNormal, map_pow, hc, hk]
  fin_cases i <;> funext j
  all_goals
    simp only [anchorFlip, List.range_succ, List.range_zero, List.map_append,
      List.map_cons, List.map_nil, List.prod_append, List.prod_cons, List.prod_nil,
      bits_mul, bits_one, Pi.add_apply, Pi.zero_apply,
      map_pow, hconj]
    revert j
    decide +kernel

theorem even_flips
    (hc : F.top c = pairCycle)
    (hk : F.bits k = Pi.single 0 (1 : ZMod 2) + Pi.single 1 (1 : ZMod 2))
    (i j : Fin 6) : ∃ a : F.top.ker,
      F.bits a = Pi.single i (1 : ZMod 2) + Pi.single j (1 : ZMod 2) := by
  refine ⟨anchorFlip F c k i * anchorFlip F c k j, ?_⟩
  rw [bits_mul, anchorFlip_bits F c k hc hk, anchorFlip_bits F c k hc hk]
  have hz : (Pi.single 0 (1 : ZMod 2) + Pi.single 0 1 : Fin 6 → ZMod 2) = 0 := by
    funext x
    exact CharTwo.add_self_eq_zero ((Pi.single 0 1 : Fin 6 → ZMod 2) x)
  calc
    _ = ((Pi.single 0 (1 : ZMod 2) : Fin 6 → ZMod 2) + Pi.single 0 1) +
        (Pi.single i 1 + Pi.single j 1) := by abel
    _ = _ := by rw [hz, zero_add]

theorem pair_transitive (hc : F.top c = pairCycle) (i j : Fin 6) :
    ∃ u : U, F.top u i = j := by
  refine ⟨c ^ j.val * (c ^ i.val)⁻¹, ?_⟩
  rw [map_mul, map_inv, map_pow, map_pow, hc]
  change (pairCycle ^ j.val) ((pairCycle ^ i.val)⁻¹ i) = j
  have hi : (pairCycle ^ i.val)⁻¹ i = 0 := by
    calc
      _ = (pairCycle ^ i.val)⁻¹ ((pairCycle ^ i.val) 0) :=
        congrArg (fun x ↦ (pairCycle ^ i.val)⁻¹ x) (pairCycle_zero i).symm
      _ = 0 := (pairCycle ^ i.val).symm_apply_apply 0
  rw [hi, pairCycle_zero]

def pairOrbitWitness (hc : F.top c = pairCycle) :
    LiteralCyclicOrbitWitness F.top.range 1 where
  element := F.top.rangeRestrict c
  representative := fun _ ↦ 0
  orbitIndex := fun _ ↦ 0
  exponent := id
  point_eq x := by
    change (F.top c ^ x.val) 0 = x
    rw [hc]
    exact pairCycle_zero x

/-- A literal adjacent kernel flip, six-cycle on pairs, and odd-offset
element certify the original point module, without enumerating the top. -/
theorem uniform
    (hc : F.top c = pairCycle)
    (hk : F.bits k = Pi.single 0 (1 : ZMod 2) + Pi.single 1 (1 : ZMod 2))
    (hodd : ∃ u : U, ∑ i, F.offset u i = 1) :
    UniformSubrepresentationGeneratorBound
      (permutationFunctionRepresentation (ZMod 2) U X) 1 :=
  F.uniform_of_even_pair_kernel_and_odd_offset_coordinateTop
    (even_flips F c k hc hk) (pair_transitive F c hc) hodd 1
    ((pairOrbitWitness F c hc).uniform (ZMod 2))

end SymmetricSubgroupAsymptotics.BinaryPairEvenCycleGenerators

end
