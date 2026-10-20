import SymmetricSubgroupAsymptotics.BinaryPairAffineChart
import SymmetricSubgroupAsymptotics.BinaryRegularEightSquareCarry
import Mathlib.GroupTheory.Commutator.Basic
import Mathlib.Tactic.Abel

/-! Carry coordinates of literal original lifts in an arbitrary physical
pair frame. The lifts are never assumed to be involutions or to form a
complement. Their actual squares and their actual derived discrepancies
are retained in the original kernel. -/
set_option autoImplicit false
noncomputable section
open scoped Classical commutatorElement

namespace SymmetricSubgroupAsymptotics.BinaryPairFrame

variable {X I : Type} {U : Subgroup (Equiv.Perm X)} (F : BinaryPairFrame U I)

def carrySquare (u : U) (hu : (F.top u) ^ 2 = 1) : F.top.ker :=
  ⟨u ^ 2, by change F.top (u ^ 2) = 1; rw [map_pow, hu]⟩

theorem carrySquare_bits (u : U) (hu : (F.top u) ^ 2 = 1) :
    F.bits (F.carrySquare u hu) =
      fun i => F.offset u (F.top u i) - F.offset u i := by
  ext i
  change F.offset (u ^ 2) i = _
  rw [pow_two, F.offset_mul, sub_eq_add_neg, ZMod.neg_eq_self_mod_two, add_comm]

def carryDifference (u v : U) (h : F.top u * F.top v = F.top v * F.top u) :
    F.top.ker :=
  ⟨(v * u)⁻¹ * (u * v), by
    change F.top ((v * u)⁻¹ * (u * v)) = 1
    rw [map_mul, map_inv, map_mul, map_mul, h, inv_mul_cancel]⟩

theorem carryDifference_mem_commutator
    (u v : U) (h : F.top u * F.top v = F.top v * F.top u) :
    (F.carryDifference u v h : U) ∈ commutator U := by
  have hc : ⁅u⁻¹, v⁻¹⁆ ∈ commutator U :=
    Subgroup.commutator_mem_commutator (Subgroup.mem_top _) (Subgroup.mem_top _)
  simpa only [carryDifference, commutatorElement_def, inv_inv, mul_inv_rev, mul_assoc]
    using hc

theorem carryDifference_bits
    (u v : U) (h : F.top u * F.top v = F.top v * F.top u) :
    F.bits (F.carryDifference u v h) = fun i =>
      (F.offset u (F.top v i) - F.offset u i) +
        (F.offset v (F.top u i) - F.offset v i) := by
  let k := F.carryDifference u v h
  have hprod : (v * u) * (k : U) = u * v := by
    dsimp [k, carryDifference]
    group
  ext i
  have he := F.offset_mul (v * u) (k : U) i
  rw [hprod, k.property] at he
  change F.offset (u * v) i = F.bits k i + F.offset (v * u) i at he
  have hd : F.bits k i = F.offset (u * v) i - F.offset (v * u) i :=
    eq_sub_iff_add_eq.mpr he.symm
  change F.bits k i = _
  rw [hd, F.offset_mul, F.offset_mul]
  simp only [sub_eq_add_neg, ZMod.neg_eq_self_mod_two]
  abel

end SymmetricSubgroupAsymptotics.BinaryPairFrame

namespace SymmetricSubgroupAsymptotics.BinaryPairFrame.RegularEightCarries

open BinaryRegularEightSquareCarry

variable {X : Type} {U : Subgroup (Equiv.Perm X)}
  (F : BinaryPairFrame U (Fin 8)) (u : Fin 3 → U)
  (himages : ∀ i j, F.top (u i) j = generatorImages i j)

def actualOffsets : Offsets := fun j =>
  F.offset (u ((finProdFinEquiv (m := 3) (n := 8)).symm j).1)
    ((finProdFinEquiv (m := 3) (n := 8)).symm j).2

theorem offsetProjection_actualOffsets (i : Fin 3) :
    offsetProjection i (actualOffsets F u) = F.offset (u i) := by
  ext j
  change F.offset (u (finProdFinEquiv.symm (finProdFinEquiv (i, j))).1)
    (finProdFinEquiv.symm (finProdFinEquiv (i, j))).2 = F.offset (u i) j
  rw [Equiv.symm_apply_apply]

include himages

theorem lift_top_square (i : Fin 3) : (F.top (u i)) ^ 2 = 1 := by
  apply Equiv.ext
  intro j
  change F.top (u i) (F.top (u i) j) = j
  rw [himages, himages]
  exact generator_involution i j

theorem lift_tops_commute (i j : Fin 3) :
    F.top (u i) * F.top (u j) = F.top (u j) * F.top (u i) := by
  apply Equiv.ext
  intro k
  change F.top (u i) (F.top (u j) k) = F.top (u j) (F.top (u i) k)
  rw [himages, himages, himages, himages]
  exact generators_commute i j k

theorem squareDisplacement_actualOffsets (i : Fin 3) :
    squareDisplacement i (actualOffsets F u) =
      F.bits (F.carrySquare (u i) (lift_top_square F u himages i)) := by
  change difference i (offsetProjection i (actualOffsets F u)) = _
  rw [offsetProjection_actualOffsets, F.carrySquare_bits]
  ext j
  change F.offset (u i) (generatorImages i j) - F.offset (u i) j = _
  rw [himages]

theorem commutatorDisplacement_actualOffsets (i j : Fin 3) :
    commutatorDisplacement i j (actualOffsets F u) =
      F.bits (F.carryDifference (u i) (u j) (lift_tops_commute F u himages i j)) := by
  change difference j (offsetProjection i (actualOffsets F u)) +
    difference i (offsetProjection j (actualOffsets F u)) = _
  rw [offsetProjection_actualOffsets, offsetProjection_actualOffsets, F.carryDifference_bits]
  ext k
  change (F.offset (u i) (generatorImages j k) - F.offset (u i) k) +
    (F.offset (u j) (generatorImages i k) - F.offset (u j) k) = _
  rw [himages, himages]

/-- The regular-eight augmentation case on the SAME original physical
kernel. The derived-kernel condition will be supplied by abelianization
saturation and the intrinsic radical identification. -/
theorem square_carries45
    (hK : F.kernelSpace = K45)
    (hderived : ∀ k : F.top.ker, (k : U) ∈ commutator U → F.bits k ∈ R45) :
    ∀ i, F.bits (F.carrySquare (u i) (lift_top_square F u himages i)) ∈ R45 := by
  have hsquare (i : Fin 3) : squareDisplacement i (actualOffsets F u) ∈ K45 := by
    rw [squareDisplacement_actualOffsets F u himages]
    rw [← hK]
    exact ⟨Additive.ofMul _, rfl⟩
  have hcomm (p : Fin 3) :
      commutatorDisplacement (pairs p).1 (pairs p).2 (actualOffsets F u) ∈ R45 := by
    rw [commutatorDisplacement_actualOffsets F u himages]
    exact hderived _ (F.carryDifference_mem_commutator _ _ _)
  intro i
  rw [← squareDisplacement_actualOffsets F u himages]
  exact BinaryRegularEightSquareCarry.square_carry45 _ hsquare hcomm i

/-- The corresponding actual-kernel carry statement for J². -/
theorem square_carries46
    (hK : F.kernelSpace = K46)
    (hderived : ∀ k : F.top.ker, (k : U) ∈ commutator U → F.bits k ∈ R46) :
    ∀ i, F.bits (F.carrySquare (u i) (lift_top_square F u himages i)) ∈ R46 := by
  have hsquare (i : Fin 3) : squareDisplacement i (actualOffsets F u) ∈ K46 := by
    rw [squareDisplacement_actualOffsets F u himages]
    rw [← hK]
    exact ⟨Additive.ofMul _, rfl⟩
  have hcomm (p : Fin 3) :
      commutatorDisplacement (pairs p).1 (pairs p).2 (actualOffsets F u) ∈ R46 := by
    rw [commutatorDisplacement_actualOffsets F u himages]
    exact hderived _ (F.carryDifference_mem_commutator _ _ _)
  intro i
  rw [← squareDisplacement_actualOffsets F u himages]
  exact BinaryRegularEightSquareCarry.square_carry46 _ hsquare hcomm i

end SymmetricSubgroupAsymptotics.BinaryPairFrame.RegularEightCarries
