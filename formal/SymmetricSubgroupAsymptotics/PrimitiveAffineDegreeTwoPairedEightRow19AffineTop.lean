import SymmetricSubgroupAsymptotics.PrimitiveAffineDegreeTwoPairedEightAffineTops
import SymmetricSubgroupAsymptotics.PrimitiveAffineDegreeTwoPairedEightRow19NormalChain

/-! Binary affine coordinates for the already checked local Row27 top.
The retained Frobenius map is displayed on three coordinates; the existing
Singer orbit and literal local generators give the exact affine closure. -/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
open scoped Classical

namespace SymmetricSubgroupAsymptotics
namespace PrimitiveAffineDegreeTwoPairedEightRow19AffineTop

open SemidirectProduct
open Non2UnipotentPrefixFiniteMenu.PrimitiveAffineImprimitiveBlockTransfer
open PrimitiveAffineDegreeTwoPairedEightAffineTops

abbrev Top := PrimitiveAffineDegreeTwoPairedEightRow19NormalChain.Top

def frobenius : LinearGroup where
  toFun v := ![v 0 + v 1, v 0, v 2]
  invFun v := ![v 1, v 0 + v 1, v 2]
  left_inv := by decide +kernel
  right_inv := by decide +kernel
  map_add' := by decide +kernel
  map_smul' := by decide +kernel

def linearGenerators : Fin 2 → LinearGroup := ![singer, frobenius]
abbrev linearGroup : Subgroup LinearGroup := Subgroup.closure (Set.range linearGenerators)

theorem singer_mem : singer ∈ linearGroup :=
  Subgroup.subset_closure (Set.mem_range_self (0 : Fin 2))

theorem frobenius_mem : frobenius ∈ linearGroup :=
  Subgroup.subset_closure (Set.mem_range_self (1 : Fin 2))

theorem irreducible : AffineModel.Irreducible linearGroup :=
  irreducible_of_singer_mem linearGroup singer_mem

theorem local_generator_binding (i : Fin 3) :
    ![linearPerm singer, linearPerm frobenius,
      translationPerm (Multiplicative.ofAdd firstVector)] i =
        PrimitiveAffineEightFrameRow27TopCertificate.generators i := by
  apply Equiv.ext
  intro x
  revert i x
  decide +kernel

theorem top18_le : DegreeTwoPairedEightSharedTops.Top18 ≤ Top := by
  apply (Subgroup.closure_le _).mpr
  rintro _ ⟨i, rfl⟩
  fin_cases i
  · change DegreeTwoPairedEightSharedTops.top18Generators 0 ∈ Top
    rw [← linearPerm_singer, show linearPerm singer =
      PrimitiveAffineEightFrameRow27TopCertificate.generators 0 from local_generator_binding 0]
    exact Subgroup.subset_closure (Set.mem_range_self (0 : Fin 3))
  · change DegreeTwoPairedEightSharedTops.top18Generators 1 ∈ Top
    rw [← translationPerm_firstVector, show translationPerm (Multiplicative.ofAdd firstVector) =
      PrimitiveAffineEightFrameRow27TopCertificate.generators 2 from local_generator_binding 2]
    exact Subgroup.subset_closure (Set.mem_range_self (2 : Fin 3))

theorem affineAction_range : (affineAction linearGroup).range = Top := by
  apply le_antisymm
  · apply affineAction_range_le linearGroup Top
      (fun v ↦ top18_le (translation_mem_top18 v))
    intro r hr
    apply linearPerm_mem_of_generators linearGenerators Top _ hr
    intro i
    fin_cases i
    · change linearPerm singer ∈ Top
      rw [show linearPerm singer = PrimitiveAffineEightFrameRow27TopCertificate.generators 0
        from local_generator_binding 0]
      exact Subgroup.subset_closure (Set.mem_range_self (0 : Fin 3))
    · change linearPerm frobenius ∈ Top
      rw [show linearPerm frobenius = PrimitiveAffineEightFrameRow27TopCertificate.generators 1
        from local_generator_binding 1]
      exact Subgroup.subset_closure (Set.mem_range_self (1 : Fin 3))
  · apply (Subgroup.closure_le _).mpr
    rintro _ ⟨i, rfl⟩
    fin_cases i
    · refine ⟨inr (⟨singer, singer_mem⟩ : linearGroup), ?_⟩
      exact (affineAction_inr _ _).trans (local_generator_binding 0)
    · refine ⟨inr (⟨frobenius, frobenius_mem⟩ : linearGroup), ?_⟩
      exact (affineAction_inr _ _).trans (local_generator_binding 1)
    · refine ⟨inl (Multiplicative.ofAdd firstVector), ?_⟩
      exact (affineAction_inl _ _).trans (local_generator_binding 2)

def modelEquiv : Top ≃* AffineModel.Aff linearGroup :=
  (MulEquiv.subgroupCongr affineAction_range.symm).trans
    (MonoidHom.ofInjective (affineAction_injective linearGroup)).symm

end PrimitiveAffineDegreeTwoPairedEightRow19AffineTop
end SymmetricSubgroupAsymptotics

end
