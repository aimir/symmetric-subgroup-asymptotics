import SymmetricSubgroupAsymptotics.NormalHeadEqualityMixedRadical
import SymmetricSubgroupAsymptotics.BinaryPairCoordinateSubgroups
import SymmetricSubgroupAsymptotics.InvariantKernelSmallStabilizer

/-! Equality in the original normal-head filtration forces the actual top
image to stabilize every kernel vector modulo the intersection radical.
Small stabilizer certificates therefore recover the literal full kernel
inside the original normal subgroup, without enlarging that subgroup. -/
set_option autoImplicit false
noncomputable section
open scoped Classical commutatorElement

namespace SymmetricSubgroupAsymptotics.BinaryPairFrame

variable {X : Type} {w : ℕ} {U : Subgroup (Equiv.Perm X)}
  (F : BinaryPairFrame U (Fin w)) (N : Subgroup U) [N.Normal]

/-- The displacement denominator is the whole-ambient radical of the
actual intersection. The acting elements come from the original N. -/
theorem original_image_displacement_mem_radical_axis
    (hcomm : ⁅F.top.ker, N⁆ ≤ primeRelativeRadical 2 (N ⊓ F.top.ker))
    (t : F.top.range) (ht : t ∈ N.map F.top.rangeRestrict)
    (v : Fin w → ZMod 2) (hv : v ∈ F.kernelSpace) :
    F.coordinateTopAction t v - v ∈
      F.ambientAxis (primeRelativeRadical 2 (N ⊓ F.top.ker)) := by
  obtain ⟨u, hu, rfl⟩ := ht
  obtain ⟨a, rfl⟩ := hv
  let k : F.top.ker := a.toMul
  let c : F.top.ker := k⁻¹ * MulAut.conjNormal u k
  have hc : (c : U) ∈ primeRelativeRadical 2 (N ⊓ F.top.ker) := by
    apply hcomm
    change ⁅(k : U)⁻¹, u⁆ ∈ ⁅F.top.ker, N⁆
    exact Subgroup.commutator_mem_commutator (F.top.ker.inv_mem k.property) hu
  have he := F.bits_commutator u k
  change F.bits c = F.coordinateTopAction (F.top.rangeRestrict u) (F.bits k) -
    F.bits k at he
  change F.coordinateTopAction (F.top.rangeRestrict u) (F.bits k) - F.bits k ∈ _
  rw [← he]
  exact (F.bits_mem_ambientAxis _ c).mpr hc

/-- Exact head additivity supplies the radical displacement condition. -/
theorem original_image_displacement_of_head_additivity [Finite X]
    (heq : Module.finrank (ZMod 2) (primeRelativeCharacters 2 N) =
      Module.finrank (ZMod 2) (primeRelativeCharacters 2 (N ⊓ F.top.ker)) +
        Module.finrank (ZMod 2)
          (primeRelativeCharacters 2 (normalChainQuotient (N ⊓ F.top.ker) N)))
    (t : F.top.range) (ht : t ∈ N.map F.top.rangeRestrict)
    (v : Fin w → ZMod 2) (hv : v ∈ F.kernelSpace) :
    F.coordinateTopAction t v - v ∈
      F.ambientAxis (primeRelativeRadical 2 (N ⊓ F.top.ker)) := by
  apply F.original_image_displacement_mem_radical_axis N ?_ t ht v hv
  exact mixed_commutator_le_intersection_radical_of_head_additivity
    2 (N ⊓ F.top.ker) N inf_le_left F.top.ker rfl heq

/-- A finite small-stabilizer certificate forces the original normal N
to contain the full actual pair kernel. The cardinality is the cardinality
of N's own retained top image. -/
theorem kernel_le_normal_of_small_radical_stabilizers [Finite X]
    {r : ℕ} (row : Fin r → F.top.range) (hrow : Function.Bijective row)
    (cap : ℕ)
    (hcount : ∀ v : Fin w → ZMod 2, v ∉ F.ambientAxis N →
      Nat.card {i : Fin r // F.coordinateTopAction (row i) v - v ∈
        F.ambientAxis (primeRelativeRadical 2 (N ⊓ F.top.ker))} ≤ cap)
    (hlarge : cap < Nat.card (N.map F.top.rangeRestrict))
    (heq : Module.finrank (ZMod 2) (primeRelativeCharacters 2 N) =
      Module.finrank (ZMod 2) (primeRelativeCharacters 2 (N ⊓ F.top.ker)) +
        Module.finrank (ZMod 2)
          (primeRelativeCharacters 2 (normalChainQuotient (N ⊓ F.top.ker) N))) :
    F.top.ker ≤ N := by
  have hle : F.kernelSpace ≤ F.ambientAxis N :=
    submodule_le_of_small_stabilizer_rows row hrow F.coordinateTopAction
      (F.ambientAxis N) (F.ambientAxis (primeRelativeRadical 2 (N ⊓ F.top.ker)))
      F.kernelSpace cap hcount (N.map F.top.rangeRestrict) hlarge
      (fun d v hv => F.original_image_displacement_of_head_additivity
        N heq d.val d.property v hv)
  intro k hk
  let a : F.top.ker := ⟨k, hk⟩
  apply (F.bits_mem_ambientAxis N a).mp
  exact hle ⟨Additive.ofMul a, rfl⟩

end SymmetricSubgroupAsymptotics.BinaryPairFrame
