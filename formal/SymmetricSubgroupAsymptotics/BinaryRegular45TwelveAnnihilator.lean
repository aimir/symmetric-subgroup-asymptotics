import SymmetricSubgroupAsymptotics.BinarySplitRegular46FullConstantStabilizerData
import SymmetricSubgroupAsymptotics.InvariantKernelQuotientRepresentatives
import SymmetricSubgroupAsymptotics.BinaryPairOriginalAffineAction
import SymmetricSubgroupAsymptotics.BinaryMenuCayley8T3

/-! The regular45 twelve-space quotient ignores the whole lower layer.
One selected pair of eight-point translations annihilates it after two
differences, independently of every actual inner affine lift offset. -/
set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 2000000
noncomputable section
namespace SymmetricSubgroupAsymptotics.BinaryRegular45TwelveAnnihilator
local instance regular45TwelveAnnihilatorPrimeTwo : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
abbrev V := Fin 16 → ZMod 2
abbrev V8 := Fin 8 → ZMod 2
abbrev K := BinarySplitRegular46FullConstantStabilizer.state
abbrev projection := BinarySplitRegular46FullConstantStabilizer.projection
private abbrev flat := BinaryPairFrame.pairLayerFlatten (w := 8)
def upper : V →ₗ[ZMod 2] V8 := (LinearMap.snd (ZMod 2) V8 V8).comp flat.symm.toLinearMap
def upperQ : V8 →ₗ[ZMod 2] (Fin 4 → ZMod 2) :=
  projection.comp (flat.toLinearMap.comp (LinearMap.inr (ZMod 2) V8 V8))
private theorem projection_basis : ∀ i : Fin 16,
    projection (Pi.single i 1)=upperQ (upper (Pi.single i 1)) := by decide +kernel
private theorem projection_eq_upper : projection=upperQ.comp upper := by
  apply LinearMap.pi_ext
  intro i c
  have hs : Pi.single i c=c • Pi.single i (1 : ZMod 2) := by ext j;simp [Pi.single_apply,mul_ite]
  simp only [hs,map_smul,LinearMap.comp_apply,projection_basis]

theorem mem_K_of_projection_zero (v : V) (hv : projection v=0) : v∈K.space := by
  have h := linear_quotient_defect_mem_of_basis K.space projection
    BinarySplitRegular46FullConstantStabilizer.sectionMap
    BinarySplitRegular46FullConstantStabilizer.quotient_basis v
  rw [hv,map_zero,sub_zero] at h
  exact h

private abbrev r (i : Fin 3) := (binaryPermutationRepresentation 8) (BinaryMenuCayley8T3.generators i)
private def doubleQ : V8 →ₗ[ZMod 2] (Fin 4 → ZMod 2) :=
  upperQ.comp ((r 2-LinearMap.id).comp (r 1-LinearMap.id))
private theorem double_basis : ∀ i : Fin 8,doubleQ (Pi.single i 1)=0 := by decide +kernel
private theorem double_eq_zero : doubleQ=0 := by
  apply LinearMap.pi_ext
  intro i c
  have hs : Pi.single i c=c • Pi.single i (1 : ZMod 2) := by ext j;simp [Pi.single_apply,mul_ite]
  simp only [hs,map_smul,double_basis,smul_zero,LinearMap.zero_apply]

theorem upper_action_actual {H : Subgroup (Equiv.Perm (Fin 16))}
    (E : BinaryPairFrame H (Fin 8)) (u : H) (v : V) :
    upper (E.originalCoordinateRepresentation u v)=
      (binaryPermutationRepresentation 8) (E.top u) (upper v) := by
  rw [E.originalCoordinateRepresentation_actual_row]
  change (flat.symm (flat (BinaryPairFrame.affinePairLayerMap
    (E.top u) (E.affineTranslation u) (flat.symm v)))).2=_
  rw [flat.symm_apply_apply]
  rfl

/-- Two ORIGINAL actual lifts with these top images suffice; their inner
offsets are not normalized or enumerated. -/
theorem double_displacement_mem_K {H : Subgroup (Equiv.Perm (Fin 16))}
    (E : BinaryPairFrame H (Fin 8)) (g h : H)
    (hg : E.top g=BinaryMenuCayley8T3.generators 2)
    (hh : E.top h=BinaryMenuCayley8T3.generators 1) (v : V) :
    E.originalCoordinateRepresentation g (E.originalCoordinateRepresentation h v-v)-
      (E.originalCoordinateRepresentation h v-v)∈K.space := by
  apply mem_K_of_projection_zero
  rw [projection_eq_upper]
  change upperQ (upper (E.originalCoordinateRepresentation g
    (E.originalCoordinateRepresentation h v-v)-(E.originalCoordinateRepresentation h v-v)))=0
  have hinner : upper (E.originalCoordinateRepresentation h v-v)=r 1 (upper v)-upper v := by
    rw [map_sub,upper_action_actual,hh]
  have houter : upper (E.originalCoordinateRepresentation g
      (E.originalCoordinateRepresentation h v-v)-(E.originalCoordinateRepresentation h v-v))=
      r 2 (upper (E.originalCoordinateRepresentation h v-v))-
        upper (E.originalCoordinateRepresentation h v-v) := by
    rw [map_sub,upper_action_actual,hg]
  rw [houter,hinner]
  exact DFunLike.congr_fun double_eq_zero (upper v)

/-- Any actual inner pair-kernel row acts trivially on the quotient. -/
theorem kernel_displacement_mem_K {H : Subgroup (Equiv.Perm (Fin 16))}
    (E : BinaryPairFrame H (Fin 8)) (j : H) (hj : E.top j=1) (v : V) :
    E.originalCoordinateRepresentation j v-v∈K.space := by
  apply mem_K_of_projection_zero
  rw [projection_eq_upper]
  change upperQ (upper (E.originalCoordinateRepresentation j v-v))=0
  rw [map_sub,upper_action_actual,hj,map_one]
  simp only [Module.End.one_apply,sub_self,map_zero]
end SymmetricSubgroupAsymptotics.BinaryRegular45TwelveAnnihilator
