import SymmetricSubgroupAsymptotics.BinaryPlaneAlternatingCentralizerKleinLift
import SymmetricSubgroupAsymptotics.BinaryPlaneTopTrivialCubicKernel
import SymmetricSubgroupAsymptotics.CentralCubicRegularBinaryComplement

/-! The genuine regular Klein complement is characteristic in the
ACTUAL centralizing preimage. Its central cubic kernel is derived from
the original odd kernel, not postulated as an abstract extension datum. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
open scoped Classical
namespace SymmetricSubgroupAsymptotics.BinaryPlaneAlternatingCharacteristicKlein
open BinaryPlaneAlternatingKernelPartition (Frame Cubic)
open BinaryPlaneAlternatingCentralizerCommutators (R regular top)
open BinaryPlaneAlternatingCentralizerKleinLift (centralRegular beta alpha)
open BinaryPlaneWreathActualOddKernel
local instance : Fintype R := BinaryRegularKleinWreath.rFintype
local instance : DecidableEq R := BinaryRegularKleinWreath.rDecidableEq

variable (C : Subgroup Frame) (e : oddKernel C ≃* Cubic)
  (heven : ∀ p : alternatingGroup (Fin 4), ∃ h : C, (h : Frame).right=p.val)

include e heven in
theorem kernel_central (x : (beta C).ker) (d : centralRegular C) :
    Commute (x : centralRegular C) d := by
  let g : C := ((x : centralRegular C) : C)
  have ht : (g : Frame).right=1 :=
    congrArg Subtype.val (MonoidHom.mem_ker.mp x.property)
  have hc : g^3=1 := congrArg (fun z : (beta C).ker => ((z : centralRegular C) : C))
    (BinaryPlaneAlternatingCentralizerKleinLift.beta_kernel_cubic C e heven x)
  let o : oddKernel C := ⟨g,BinaryPlaneTopTrivialCubicKernel.mem_oddKernel C g ht hc⟩
  have ha : alpha C (d : C)=1 := d.property.1
  have hh := congrArg (fun f : MulAut (oddKernel C) => (f o : C)) ha
  change (d : C)*g*(d : C)⁻¹=g at hh
  have hm : Commute (d : C) g := mul_inv_eq_iff_eq_mul.mp hh
  apply Subtype.ext
  exact hm.symm.eq

include e heven in
/-- A characteristic complement in the actual centralizing preimage,
obtained from the actual homomorphic lift already constructed there. -/
theorem exists_characteristic_section :
    ∃ s : regular.range →* centralRegular C,
      (∀ r, beta C (s r)=r) ∧ s.range.Characteristic := by
  obtain ⟨l,hl,ht,hcomm⟩ :=
    BinaryPlaneAlternatingCentralizerKleinLift.exists_regular_hom C e heven
  let dl : R →* centralRegular C := l.codRestrict (centralRegular C) (by
    intro r
    constructor
    · apply MulEquiv.ext
      intro o
      apply Subtype.ext
      change l r*(o : C)*(l r)⁻¹=(o : C)
      rw [(hcomm r o).eq,mul_assoc,mul_inv_cancel,mul_one]
    · exact ⟨r,(ht r).symm⟩)
  let er : R ≃* regular.range := MulEquiv.ofBijective regular.rangeRestrict
    ⟨fun x y h => BinaryPlaneAlternatingCentralizerCommutators.regular_injective
      (congrArg Subtype.val h),
      regular.rangeRestrict_surjective⟩
  let s : regular.range →* centralRegular C := dl.comp er.symm.toMonoidHom
  have hs : ∀ r, beta C (s r)=r := by
    intro r
    apply Subtype.ext
    change top C (l (er.symm r))=(r : Equiv.Perm (Fin 4))
    rw [ht]
    exact congrArg Subtype.val (er.apply_symm_apply r)
  have hb : ∀ r : regular.range, r^2=1 := by
    intro r
    obtain ⟨u,rfl⟩ := er.surjective r
    rw [← map_pow]
    have hu : u^2=1 := (by decide +kernel : ∀ u : R, u^2=1) u
    rw [hu,map_one]
  refine ⟨s,hs,?_⟩
  exact CentralCubicRegularBinaryComplement.characteristic_range (beta C) s hs hb
    (BinaryPlaneAlternatingCentralizerKleinLift.beta_kernel_cubic C e heven)
    (kernel_central C e heven)

end SymmetricSubgroupAsymptotics.BinaryPlaneAlternatingCharacteristicKlein
