import SymmetricSubgroupAsymptotics.BinaryPairRegularKernelSplit
import SymmetricSubgroupAsymptotics.BinaryElementarySixteenOffsetGauge
import SymmetricSubgroupAsymptotics.BinaryElementaryPairKernelConstants

/-! An original elementary degree-sixteen source has exact zero square
and commutator carries. The sparse regular-eight cocycle certificate then
gives literal point-conjugacy to its zero-offset model. -/
set_option autoImplicit false
noncomputable section
namespace SymmetricSubgroupAsymptotics.BinaryPairFrame

open BinaryRegularEightSquareCarry RegularEightCarries

variable {X : Type} {U : Subgroup (Equiv.Perm X)} (F : BinaryPairFrame U (Fin 8))

/-- The exponent condition is on the original source; no complement,
module classification, or extra kernel hypothesis occurs. -/
theorem original_elementary_exists_physical_conjugate_zero_offset_model
    (hpow : ∀ g : U, g ^ 2 = 1)
    (u : Fin 3 → U)
    (hp : ∀ i j, F.top (u i) j = generatorImages i j)
    (hgen : Subgroup.closure (Set.range fun i => F.top (u i)) = F.top.range) :
    ∃ a : V, U.map (MulAut.conj (F.physicalFlip a)).toMonoidHom =
      F.affineGeneratedModel F.kernelSpace (fun i => F.top (u i)) (fun _ => 0) := by
  have hcomm (g h : U) : g * h = h * g :=
    (Commute.of_orderOf_dvd_two
      (fun g => orderOf_dvd_iff_pow_eq_one.mpr (hpow g)) g h).eq
  have hbits : F.bits (1 : F.top.ker) = 0 :=
    congrArg Multiplicative.toAdd F.bitsHom.map_one
  have hsquare (i : Fin 3) : squareDisplacement i (actualOffsets F u) = 0 := by
    rw [squareDisplacement_actualOffsets F u hp]
    have he : F.carrySquare (u i) (lift_top_square F u hp i) = 1 :=
      Subtype.ext (hpow (u i))
    rw [he, hbits]
  have hcarry (p : Fin 3) :
      commutatorDisplacement (pairs p).1 (pairs p).2 (actualOffsets F u) = 0 := by
    rw [commutatorDisplacement_actualOffsets F u hp]
    have he : F.carryDifference (u (pairs p).1) (u (pairs p).2)
        (lift_tops_commute F u hp (pairs p).1 (pairs p).2) = 1 := by
      apply Subtype.ext
      simp only [carryDifference,hcomm,mul_inv_cancel,Subgroup.coe_one]
    rw [he, hbits]
  obtain ⟨a, ha⟩ := BinaryElementarySixteenOffsetGauge.exists_source_orientation
    (actualOffsets F u) hsquare hcarry
  refine ⟨a, F.physical_conjugate_eq_zero_offset_model_of_source_orientation u hgen a ?_⟩
  intro i
  have hi := ha i
  rw [offsetProjection_actualOffsets] at hi
  have hz : F.offset (u i) + (fun j => a (F.top (u i) j)) - a = 0 := by
    simpa only [hp] using hi
  rw [hz]
  exact F.kernelSpace.zero_mem

end SymmetricSubgroupAsymptotics.BinaryPairFrame
