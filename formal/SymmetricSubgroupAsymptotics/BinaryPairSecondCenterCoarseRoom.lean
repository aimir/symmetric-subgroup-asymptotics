import SymmetricSubgroupAsymptotics.BinaryPairSecondCenterRoom
import SymmetricSubgroupAsymptotics.BinaryPairActualKernelImageBounds
import SymmetricSubgroupAsymptotics.TransitiveNonabelianCenterBound
import SymmetricSubgroupAsymptotics.BinaryPairOriginalKernelCoordinateCard
import SymmetricSubgroupAsymptotics.BinaryPairJointNormalFBounds

/-! The original second centre can be charged jointly to its actual
constant-displacement axis and its image in the literal top centre.
Dimension nine of the original kernel suffices for a256 capacity; no
faithfulness claim on the half-dimensional quotient is made. -/
set_option autoImplicit false
noncomputable section
open scoped commutatorElement
namespace SymmetricSubgroupAsymptotics.BinaryPairFrame
local instance secondCenterCoarseRoomPrimeTwo : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
variable {X : Type} [Finite X] {U : Subgroup (Equiv.Perm X)}
    (F : BinaryPairFrame U (Fin 16)) [MulAction.IsPretransitive U X]
include F

theorem original_second_center_card_le_256_of_nine_dim_nonelementary_kernel
    (hU : IsPGroup 2 U) (hlarge : 9≤Module.finrank (ZMod 2) F.kernelSpace)
    (hnon : ¬BinarySquareActionStructure.SquaresActTrivially (G := F.top.range) (X := Fin 16)) :
    Nat.card (Subgroup.upperCentralSeries U 2)≤256 := by
  letI : MulAction.IsPretransitive F.top.range (Fin 16) := F.top_pretransitive
  let L := Subgroup.upperCentralSeries U 2
  let beta := F.top.rangeRestrict
  have hZker : Subgroup.center U≤F.top.ker :=
    F.original_center_le_kernel_of_half_lt hU (0 : Fin 16) (by omega)
  have hmap : L.map beta≤Subgroup.center F.top.range := by
    rintro t ⟨u,hu,rfl⟩
    apply Subgroup.mem_center_iff.mpr
    intro b
    obtain ⟨g,rfl⟩ := F.top.rangeRestrict_surjective b
    have hc : ⁅u,g⁆∈Subgroup.center U := by
      have hh := Subgroup.mem_upperCentralSeries_succ_iff.mp hu g
      simpa only [Subgroup.upperCentralSeries_one] using hh
    have hh : beta ⁅u,g⁆=1 := by
      apply MonoidHom.mem_ker.mp
      simpa only [beta,MonoidHom.ker_rangeRestrict] using hZker hc
    rw [map_commutatorElement] at hh
    exact (commutatorElement_eq_one_iff_mul_comm.mp hh).symm
  have htop : Nat.card (Subgroup.center F.top.range)≤16 := by
    have hh := Nat.card_le_card_of_injective
      (fun z : Subgroup.center F.top.range => (z : F.top.range) • (0 : Fin 16))
      (transitive_center_evaluation_injective (0 : Fin 16))
    simpa only [Nat.card_fin] using hh
  let W := F.ambientAxis L
  have hd : Module.finrank (ZMod 2) W≤4 :=
    BinaryConstantDisplacementDimension.finrank_le_four_of_not_squares_trivial
      W (0 : Fin 16) (by simp only [Nat.card_fin])
      (fun g v x y => F.second_center_axis_constant_displacements g v x y) hnon
  have haxis : Nat.card W≤16 := by
    rw [Module.natCard_eq_pow_finrank (K := ZMod 2)]
    simpa only [Nat.card_zmod] using
      (Nat.pow_le_pow_right (by decide : 0<(2:ℕ)) hd)
  have hinter : Nat.card (L⊓F.top.ker : Subgroup U)≤16 := by
    rw [inf_comm,←F.axis_card_eq_kernel_intersection L]
    exact haxis
  have hc := subgroup_card_eq_map_mul_kernel_intersection beta L
  rw [show beta.ker=F.top.ker by simp only [beta,MonoidHom.ker_rangeRestrict]] at hc
  rw [hc]
  exact (Nat.mul_le_mul ((Subgroup.card_le_of_le hmap).trans htop) hinter).trans (by norm_num)

end SymmetricSubgroupAsymptotics.BinaryPairFrame
