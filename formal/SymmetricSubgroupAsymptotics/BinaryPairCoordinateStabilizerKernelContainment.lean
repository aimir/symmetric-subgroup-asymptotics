import SymmetricSubgroupAsymptotics.BinaryPairIntersectionRadicalStabilizer
import SymmetricSubgroupAsymptotics.BinaryPairOriginalCoordinateRepresentation
import SymmetricSubgroupAsymptotics.BinaryPairAxisNaturalModule

/-! A finite original-coordinate stabilizer bound is consumed without
changing the normal subgroup. Its denominator is the actual intersection
radical and its tested space is the full original correlated kernel. -/
set_option autoImplicit false
noncomputable section
open scoped commutatorElement
namespace SymmetricSubgroupAsymptotics.BinaryPairFrame
variable {X : Type} {U : Subgroup (Equiv.Perm X)}
    (F : BinaryPairFrame U (Fin 16)) (E : BinaryPairFrame F.top.range (Fin 8))
    (N : Subgroup U) [N.Normal]

theorem kernel_le_normal_of_coordinate_stabilizer
    (S R : Submodule (ZMod 2) (Fin 16 → ZMod 2))
    (hS : (E.originalCoordinateSubrepresentation
      (F.axisNaturalSubrepresentation (N ⊓ F.top.ker))).toSubmodule = S)
    (hR : (F.ambientAxis (primeRelativeRadical 2 (N ⊓ F.top.ker))).map
      E.originalCoordinateEquiv.toLinearMap = R)
    (hcomm : ⁅F.top.ker, N⁆ ≤ primeRelativeRadical 2 (N ⊓ F.top.ker))
    (hfixedKernel : ∀ K : Submodule (ZMod 2) (Fin 16 → ZMod 2),
      (∀ d : N.map F.top.rangeRestrict, ∀ v ∈ K,
        E.originalCoordinateRepresentation d.val v - v ∈ R) → K ≤ S) :
    F.top.ker ≤ N := by
  let K := F.kernelSpace.map E.originalCoordinateEquiv.toLinearMap
  have hK : K ≤ S := by
    apply hfixedKernel K
    intro d v hv
    obtain ⟨a, ha, rfl⟩ := hv
    have hr := F.original_image_displacement_mem_radical_axis N hcomm d.val d.property a ha
    have himage : E.originalCoordinateEquiv (F.coordinateTopAction d.val a - a) ∈ R := by
      rw [← hR]
      exact ⟨_, hr, rfl⟩
    have he : E.originalCoordinateRepresentation d.val (E.originalCoordinateEquiv a) -
        E.originalCoordinateEquiv a =
        E.originalCoordinateEquiv (F.coordinateTopAction d.val a - a) := by
      change E.originalCoordinateEquiv
        (permutationFunctionRepresentation (ZMod 2) F.top.range (Fin 16) d.val
          (E.originalCoordinateEquiv.symm (E.originalCoordinateEquiv a))) -
        E.originalCoordinateEquiv a = _
      rw [E.originalCoordinateEquiv.symm_apply_apply, ← map_sub]
      rfl
    change E.originalCoordinateRepresentation d.val (E.originalCoordinateEquiv a) -
      E.originalCoordinateEquiv a ∈ R
    rw [he]
    exact himage
  intro k hk
  let a : F.top.ker := ⟨k, hk⟩
  have ha : E.originalCoordinateEquiv (F.bits a) ∈ K :=
    ⟨F.bits a, ⟨Additive.ofMul a, rfl⟩, rfl⟩
  have hs := hK ha
  rw [← hS] at hs
  change E.originalCoordinateEquiv (F.bits a) ∈
    (F.ambientAxis (N ⊓ F.top.ker)).map E.originalCoordinateEquiv.toLinearMap at hs
  obtain ⟨v, hv, he⟩ := hs
  have he' : v = F.bits a := E.originalCoordinateEquiv.injective he
  rw [he'] at hv
  exact ((F.bits_mem_ambientAxis (N ⊓ F.top.ker) a).mp hv).1

end SymmetricSubgroupAsymptotics.BinaryPairFrame
