import SymmetricSubgroupAsymptotics.CFSGTwistedAUnitaryNaturalRadical
import SymmetricSubgroupAsymptotics.CFSGTwistedAUnitaryRadicalCommutator

/-! Every highest central radical parameter is an actual commutator in
THE ORIGINAL fixed source, all prime powers including2. This is only the
central one-coordinate layer; derived inclusion of the whole upper group
requires further genuine root arguments. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
open scoped BigOperators Matrix commutatorElement

namespace SymmetricSubgroupAsymptotics.CFSGTwistedAUnitaryNaturalRadical
open CFSGTwistedANaturalMatrices CFSGTwistedAUnitaryUpperArrays
open CFSGTwistedAUnitaryCoordinates CFSGTwistedAUnitaryParameters
open CFSGSerreOrdinaryTwists CFSGTwistedAUpperUnipotent

theorem centralCondition_iff (q : CFSG.PrimePower) (s : ℕ) (c : q.Extension 2) :
    Condition q s 0 c ↔ definingFieldAutomorphism q 2 c + parity q s * c = 0 := by
  simp [Condition, hermitianNorm]

theorem firstRow_zero_eq (q : CFSG.PrimePower) (s : ℕ) : firstRow q s 0 = 0 := by
  have hz : definingFieldAutomorphism q 2 ∘ (0 : Fin (s + 1) → q.Extension 2) = 0 := by
    funext j
    exact map_zero (definingFieldAutomorphism q 2)
  funext i
  change -parity q s * ((definingFieldAutomorphism q 2 ∘
    (0 : Fin (s + 1) → q.Extension 2)) ᵥ* middleForm q s) i = 0
  rw [hz, Matrix.zero_vecMul]
  simp

theorem firstRow_single_entry (q : CFSG.PrimePower) (s : ℕ)
    (i j : Fin (s + 1)) (a : q.Extension 2) :
    firstRow q s (Pi.single i a) j =
      -parity q s * (definingFieldAutomorphism q 2 a) * middleForm q s i j := by
  have hv : definingFieldAutomorphism q 2 ∘ Pi.single i a =
      Pi.single i (definingFieldAutomorphism q 2 a) := by
    funext k
    simp only [Function.comp_apply, Pi.single_apply, apply_ite, map_zero]
    split_ifs <;> rfl
  change -parity q s * ((definingFieldAutomorphism q 2 ∘ Pi.single i a) ᵥ*
    middleForm q s) j = _
  rw [hv]
  simp only [Matrix.vecMul, single_dotProduct]
  ring

theorem endpoint_pairing (q : CFSG.PrimePower) (s : ℕ) (t : q.Extension 2) :
    dotProduct (firstRow q s (Pi.single 0 1)) (Pi.single (Fin.last s) t) -
      dotProduct (firstRow q s (Pi.single (Fin.last s) t)) (Pi.single 0 1) =
        parity q s * t - definingFieldAutomorphism q 2 t := by
  have h0 : (0 : Fin (s + 1)).rev = Fin.last s := by
    apply Fin.ext
    simp [Fin.rev]
  have hl : (Fin.last s).rev = (0 : Fin (s + 1)) := by
    apply Fin.ext
    simp [Fin.rev]
  have hp : parity q s * parity q s = 1 := by
    change ((-1 : q.Extension 2) ^ s) * ((-1 : q.Extension 2) ^ s) = 1
    rw [← mul_pow]
    simp
  rw [dotProduct_single, dotProduct_single, firstRow_single_entry, firstRow_single_entry]
  simp only [middleForm, Matrix.neg_apply, signedReversalUnit_apply, h0, hl,
    if_true, signWeight, Fin.val_zero, Fin.val_last, pow_zero, map_one, mul_one]
  change -parity q s * -1 * t -
    (-parity q s * definingFieldAutomorphism q 2 t * -parity q s) = _
  calc
    _ = parity q s * t - (parity q s * parity q s) * definingFieldAutomorphism q 2 t := by ring
    _ = _ := by rw [hp, one_mul]

theorem radicalCentral_mem_commutator (q : CFSG.PrimePower) (s : ℕ)
    (c : q.Extension 2) (hc : Condition q s 0 c) :
    unipotentToOriginalFixed (s + 2) q (radicalElement q s 0 c hc) ∈
      commutator (Fixed (s + 2) q) := by
  obtain ⟨t, ht⟩ := exists_signedCentral_commutator_parameter q (parity q s) c
    (neg_one_pow_eq_or (q.Extension 2) s) ((centralCondition_iff q s c).mp hc)
  obtain ⟨b, hb⟩ := condition_exists q s (Pi.single 0 1)
  obtain ⟨d, hd⟩ := condition_exists q s (Pi.single (Fin.last s) t)
  let x := radicalElement q s (Pi.single 0 1) b hb
  let y := radicalElement q s (Pi.single (Fin.last s) t) d hd
  have hxy : ⁅x, y⁆ = radicalElement q s 0 c hc := by
    apply Subtype.ext
    apply Subtype.ext
    let f := Units.map (Matrix.reindexAlgEquiv (q.Extension 2) (q.Extension 2)
      (splitEquiv s)).toRingHom.toMonoidHom
    change ⁅f (upperUnit (firstRow q s (Pi.single 0 1)) (Pi.single 0 1) b),
      f (upperUnit (firstRow q s (Pi.single (Fin.last s) t)) (Pi.single (Fin.last s) t) d)⁆ =
        f (upperUnit (firstRow q s 0) 0 c)
    rw [← map_commutatorElement, upperUnit_commutator, endpoint_pairing, ht, firstRow_zero_eq]
  have himage := congrArg (unipotentToOriginalFixed (s + 2) q) hxy
  rw [map_commutatorElement] at himage
  rw [← himage, commutator_eq_closure]
  exact Subgroup.subset_closure (commutator_mem_commutatorSet _ _)

end SymmetricSubgroupAsymptotics.CFSGTwistedAUnitaryNaturalRadical
