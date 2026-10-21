import SymmetricSubgroupAsymptotics.BinaryPairPermutationGeneratorExtension
import SymmetricSubgroupAsymptotics.BinaryAffineDoubleCommutatorZeroLift

/-! Difference kernels in an actual pair-sum quotient descend to the SAME
outer affine quotient. The original pair kernel and all lift offsets remain
unchanged. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
namespace SymmetricSubgroupAsymptotics.BinaryPairFrame
variable {X : Type} {w : ℕ} {U : Subgroup (Equiv.Perm X)}
    (F : BinaryPairFrame U (Fin (w+w))) (E : BinaryPairFrame F.top.range (Fin w))
include F E

theorem pairSum_outer_difference (t : F.top.range) (v : Fin (w+w) → ZMod 2) :
    E.pairSum (F.coordinateTopAction t v-v)=
      E.coordinateTopAction (E.top.rangeRestrict t) (E.pairSum v)-E.pairSum v := by
  rw [map_sub]
  have he := Representation.IntertwiningMap.isIntertwining _ _ E.pairSumIntertwiner t v
  change E.pairSum (F.coordinateTopAction t v)=
    E.coordinateTopAction (E.top.rangeRestrict t) (E.pairSum v) at he
  rw [he]

theorem affineQuotient_kernel_inclusion_of_pairSum_preimage
    (S : Submodule (ZMod 2) (Fin w → ZMod 2))
    (hK : F.kernelSpace=S.comap E.pairSum) (g h : F.top.range)
    (hker : ∀ v : Fin w → ZMod 2,
      E.coordinateTopAction (E.top.rangeRestrict h) v-v∈S →
      E.coordinateTopAction (E.top.rangeRestrict g) v-v∈S) :
    ∀ a : (Fin (w+w) → ZMod 2) ⧸ F.kernelSpace,
      F.affineQuotientRepresentation h a-a=0 →
      F.affineQuotientRepresentation g a-a=0 := by
  intro a ha
  obtain ⟨v,rfl⟩ := F.kernelSpace.mkQ_surjective a
  have hsub (t : F.top.range) :
      F.affineQuotientRepresentation t (F.kernelSpace.mkQ v)-F.kernelSpace.mkQ v=
        F.kernelSpace.mkQ (F.coordinateTopAction t v-v) := by
    change F.kernelSpace.mkQ (F.coordinateTopAction t v)-F.kernelSpace.mkQ v=_
    rw [map_sub]
  rw [hsub] at ha ⊢
  apply (Submodule.Quotient.mk_eq_zero F.kernelSpace).mpr
  have hv := (Submodule.Quotient.mk_eq_zero F.kernelSpace).mp ha
  rw [hK] at hv ⊢
  change E.pairSum (F.coordinateTopAction h v-v)∈S at hv
  change E.pairSum (F.coordinateTopAction g v-v)∈S
  rw [F.pairSum_outer_difference E] at hv ⊢
  exact hker (E.pairSum v) hv

theorem affineQuotient_eq_one_of_pairSum_preimage_kernel
    (S : Submodule (ZMod 2) (Fin w → ZMod 2))
    (hK : F.kernelSpace=S.comap E.pairSum) (j : F.top.range) (hj : E.top j=1) :
    F.affineQuotientRepresentation j=1 := by
  apply LinearMap.ext
  intro a
  obtain ⟨v,rfl⟩ := F.kernelSpace.mkQ_surjective a
  change F.kernelSpace.mkQ (F.coordinateTopAction j v)=F.kernelSpace.mkQ v
  apply (Submodule.Quotient.eq F.kernelSpace).mpr
  rw [hK]
  change E.pairSum (F.coordinateTopAction j v-v)∈S
  rw [F.pairSum_outer_difference E]
  change (binaryPermutationRepresentation w) (E.top j) (E.pairSum v)-E.pairSum v∈S
  rw [hj,map_one]
  simpa only [Module.End.one_apply,sub_self] using S.zero_mem
end SymmetricSubgroupAsymptotics.BinaryPairFrame
