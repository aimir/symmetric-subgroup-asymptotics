import SymmetricSubgroupAsymptotics.BinaryPairSection
import SymmetricSubgroupAsymptotics.BinaryPairCoordinateSubgroups

/-! The inner section denominator and its original ambient coordinate
axis are the same space under the literal inclusion into the flip module. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
namespace SymmetricSubgroupAsymptotics.BinaryPairFrame

variable {X : Type} {w : ℕ} {U : Subgroup (Equiv.Perm X)}
    (F : BinaryPairFrame U (Fin w)) (N : Subgroup U)

theorem normalSpace_eq_comap_ambientAxis :
    F.normalSpace N = (F.ambientAxis N).comap F.kernelSpace.subtype := by
  ext v
  constructor
  · rintro ⟨n, hn⟩
    have he : F.bits (n.toMul : F.top.ker) = (v : Fin w → ZMod 2) :=
      congrArg Subtype.val hn
    change (v : Fin w → ZMod 2) ∈ F.ambientAxis N
    rw [← he]
    exact (F.bits_mem_ambientAxis N (n.toMul : F.top.ker)).mpr n.toMul.property
  · intro hv
    obtain ⟨k, hk, he⟩ := (F.mem_ambientAxis N (v : Fin w → ZMod 2)).mp hv
    refine ⟨Additive.ofMul (⟨k, hk⟩ : N.subgroupOf F.top.ker), ?_⟩
    exact Subtype.ext he

def normalSpaceAxisEquiv : F.normalSpace N ≃ₗ[ZMod 2] F.ambientAxis N :=
  (LinearEquiv.ofEq _ _ (F.normalSpace_eq_comap_ambientAxis N)).trans
    (Submodule.comapSubtypeEquivOfLe (F.ambientAxis_le_kernelSpace N))

theorem normalSpaceAxisEquiv_finrank :
    Module.finrank (ZMod 2) (F.normalSpace N) =
      Module.finrank (ZMod 2) (F.ambientAxis N) :=
  (F.normalSpaceAxisEquiv N).finrank_eq

end SymmetricSubgroupAsymptotics.BinaryPairFrame
