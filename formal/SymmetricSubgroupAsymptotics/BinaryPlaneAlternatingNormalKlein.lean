import SymmetricSubgroupAsymptotics.BinaryPlaneAlternatingCharacteristicKlein
import Mathlib.Data.Fintype.Perm

/-! The actual regular Klein lift is normalized by the whole linear image.
The finite calculation is only normality of the literal regular V4 in S4. -/
set_option autoImplicit false
noncomputable section
open scoped Classical
namespace SymmetricSubgroupAsymptotics.BinaryPlaneAlternatingNormalKlein
open BinaryPlaneAlternatingKernelPartition (Frame Cubic)
open BinaryPlaneAlternatingCentralizerCommutators (R regular top)
open BinaryPlaneAlternatingCentralizerKleinLift (centralRegular beta alpha)
open BinaryPlaneWreathActualOddKernel
local instance : Fintype R := BinaryRegularKleinWreath.rFintype
local instance : DecidableEq R := BinaryRegularKleinWreath.rDecidableEq

private theorem conjugate_regular : ∀ (p : Equiv.Perm (Fin 4)) (r : R),
    ∃ s : R, p*regular r*p⁻¹=regular s := by decide +kernel

private theorem regular_normal : regular.range.Normal := by
  constructor
  intro x hx p
  obtain ⟨r,rfl⟩ := hx
  obtain ⟨s,hs⟩ := conjugate_regular p r
  exact ⟨s,hs.symm⟩

theorem centralRegular_normal (C : Subgroup Frame) : (centralRegular C).Normal := by
  letI : regular.range.Normal := regular_normal
  change ((alpha C).ker ⊓ regular.range.comap (top C)).Normal
  infer_instance

/-- Characteristic subgroups of this actual normal preimage remain
normal after their literal inclusion into the actual linear image. -/
theorem characteristic_image_normal {G : Type} [Group G]
    (D : Subgroup G) [D.Normal] (P : Subgroup D) (hP : P.Characteristic) :
    (P.map D.subtype).Normal := by
  constructor
  intro x hx g
  obtain ⟨d,hd,rfl⟩ := hx
  have hh := (Subgroup.characteristic_iff_le_comap.mp hP) (MulAut.conjNormal g)
  exact ⟨(MulAut.conjNormal g) d,hh hd,rfl⟩

/-- A normal actual V4 complement, not a pure-top complement assumed in
advance. Any actual lift of a block three-cycle normalizes its image. -/
theorem exists_normal_section (C : Subgroup Frame)
    (e : oddKernel C ≃* Cubic)
    (heven : ∀ p : alternatingGroup (Fin 4), ∃ h : C, (h : Frame).right=p.val) :
    ∃ s : regular.range →* centralRegular C,
      (∀ r, beta C (s r)=r) ∧
      (s.range.map (centralRegular C).subtype).Normal := by
  obtain ⟨s,hs,hchar⟩ :=
    BinaryPlaneAlternatingCharacteristicKlein.exists_characteristic_section C e heven
  letI : (centralRegular C).Normal := centralRegular_normal C
  exact ⟨s,hs,characteristic_image_normal (centralRegular C) s.range hchar⟩

end SymmetricSubgroupAsymptotics.BinaryPlaneAlternatingNormalKlein
