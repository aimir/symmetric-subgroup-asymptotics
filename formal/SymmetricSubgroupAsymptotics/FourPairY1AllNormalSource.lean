import SymmetricSubgroupAsymptotics.FourPairY1RepeatedHeadKernel
import SymmetricSubgroupAsymptotics.PureCubicKernelY1Certificate
import SymmetricSubgroupAsymptotics.Y1QuotientCertificateEquiv
import SymmetricSubgroupAsymptotics.ScalarFourRepeatedHeadKernelChart
import SymmetricSubgroupAsymptotics.PrimitiveAffineDegreeTwoPairedEightRow12QuotientSocles
import SymmetricSubgroupAsymptotics.Non2PreE7SmallModelToolkit

/-! Actual Y1 all-original-normal certificate. The already complete nine
normal states are reused. Bottom has actual central-headed weight3;
nonbottom proper states descend through the same original central kernel
to pure scalar module quotients, of headed weight2 or cyclic3; top is
trivial. No new normal census or weakened cold exponent is introduced. -/
set_option autoImplicit false
set_option maxRecDepth 8192
noncomputable section
open scoped Classical
namespace SymmetricSubgroupAsymptotics.FourPairY1AllNormalSource
open Non2UnipotentPrefixFiniteMenu
open PrimitiveAffineEightFrameRow21TopCertificate FourPairY1RepeatedHeadMap
open FourPairY1RepeatedHeadKernel
local instance sourceGroup : Group Source := group
private abbrev R := ScalarFourRepeatedHeadModel.G
private abbrev state := PrimitiveAffineDegreeTwoPairedEightRow12NormalStates.state
private abbrev mask := PrimitiveAffineDegreeTwoPairedEightRow12NormalStates.normalMask
private instance state_normal (i : Fin 9) : (state i).Normal :=
  PrimitiveAffineDegreeTwoPairedEightRow12QuotientSocles.normalRegistry.state_normal i

private theorem bottom_checked : ∀ x : Fin 96,
    mask 0 x=true ↔ x=certificate.identity := by decide +kernel
private theorem state_bot : state 0=⊥ := by
  ext x
  rw [← PrimitiveAffineDegreeTwoPairedEightRow12NormalStates.normalMask_mem,bottom_checked,
    Subgroup.mem_bot]
  exact ⟨FiniteGroupRow.ext,fun h => congrArg FiniteGroupRow.index h⟩
private theorem top_checked : ∀ x : Fin 96, mask 8 x = true := by
  decide +kernel
private theorem state_top : state 8 = ⊤ := by
  apply top_unique
  intro x _
  exact (PrimitiveAffineDegreeTwoPairedEightRow12NormalStates.normalMask_mem 8 x).mp
    (top_checked x.index)

private theorem central_in_checked : ∀ i : Fin 9, i≠0 → mask i centralIndex=true := by
  decide +kernel
private theorem proper_top_checked : ∀ (i : Fin 9) (x : Fin 96), i≠8 → mask i x=true →
    ScalarFourRepeatedHeadModel.top (sourceMap ⟨x⟩)=1 := by
  decide +kernel

private theorem kernel_le_state (i : Fin 9) (hi : i≠0) : sourceMap.ker ≤ state i := by
  intro x hx
  rcases (kernel_mem_iff x).mp hx with rfl|rfl
  · exact (state i).one_mem
  · exact (PrimitiveAffineDegreeTwoPairedEightRow12NormalStates.normalMask_mem i centralElement).mp
      (central_in_checked i hi)
private theorem state_le_top_kernel (i : Fin 9) (hi : i≠8) :
    state i≤(ScalarFourRepeatedHeadModel.top.comp sourceMap).ker := by
  intro x hx
  exact proper_top_checked i x.index hi
    ((PrimitiveAffineDegreeTwoPairedEightRow12NormalStates.normalMask_mem i x).mpr hx)

private def repeatedQuotient (hZmud : ZmudFaithfulCharacterTupleInput)
    (M : Subgroup R) [M.Normal] (hM : M≤ScalarFourRepeatedHeadModel.top.ker) :
    PreE7Y1QuotientCertificate (R ⧸ M) := by
  let t := ScalarFourRepeatedHeadModel.top
  let A := ScalarFourRepeatedHeadModel.kernelModule
  let E := ScalarFourRepeatedHeadModel.originalKernelChart
  let B := CubicOriginalNormalQuotientChart.quotientModule t
    ScalarFourRepeatedHeadModel.headed.top_surjective A E M
  let F := CubicOriginalNormalQuotientChart.quotientChart t
    ScalarFourRepeatedHeadModel.headed.top_surjective A E M hM
  let D := CubicOriginalNormalQuotientChart.quotientCoordinates t
    ScalarFourRepeatedHeadModel.headed.top_surjective A E M
    ScalarFourRepeatedHeadModel.kernelCoordinates
  have ht : Function.Surjective (QuotientGroup.lift M t hM) := by
    intro c
    obtain ⟨g,hg⟩ := ScalarFourRepeatedHeadModel.headed.top_surjective c
    exact ⟨QuotientGroup.mk' M g,hg⟩
  have hz : ∀ (j : Fin 2) (v : B), D.invariant j v=0 := by
    intro j v
    rfl
  exact PureCubicKernelY1Certificate.certificate (QuotientGroup.lift M t hM) ht B F D hz hZmud

private def trivialCertificate (hZmud : ZmudFaithfulCharacterTupleInput)
    {Q : Type} [Group Q] [Finite Q] [Subsingleton Q] : PreE7Y1QuotientCertificate Q := by
  have hg : SocleNormalGeneratorBound Q 0 := by
    refine ⟨Fin.elim0,?_⟩
    ext x
    have hx : x=1 := Subsingleton.elim _ _
    subst x
    simp
  exact .character (hZmud.generalCertificate hg) (by
    simp only [ZmudFaithfulCharacterTupleInput.generalCertificate,
      CharacterQuotientCertificate.slope,
      ZmudFaithfulCharacterTupleInput.generalTuple_binaryCount,
      ZmudFaithfulCharacterTupleInput.generalTuple_linearCount,
      ZmudFaithfulCharacterTupleInput.generalTuple_generalCount,
      CharacterQuotientMode.generalSlope,Nat.cast_zero,zero_mul,zero_add]
    norm_num)

private def stateCertificate (hZmud : ZmudFaithfulCharacterTupleInput) (i : Fin 9) :
    PreE7Y1QuotientCertificate (Source ⧸ state i) := by
  by_cases h0 : i=0
  · subst i
    let e : (Source ⧸ state 0) ≃* Source :=
      (QuotientGroup.quotientMulEquivOfEq state_bot).trans QuotientGroup.quotientBot
    exact (PreE7Y1QuotientCertificate.headed FourPairY1RepeatedHeadKernel.headed
      (by rw [headed_weight])).comapEquiv e
  · by_cases h8 : i=8
    · subst i
      letI : Subsingleton (Source ⧸ state 8) := ⟨by
        intro x y
        have hz : ∀ z : Source ⧸ state 8, z=1 := by
          intro z
          obtain ⟨g,rfl⟩ := QuotientGroup.mk'_surjective (state 8) z
          apply (QuotientGroup.eq_one_iff g).mpr
          rw [state_top]
          exact Subgroup.mem_top g
        exact (hz x).trans (hz y).symm⟩
      exact trivialCertificate hZmud
    · let M := (state i).map sourceMap
      letI : M.Normal := (state_normal i).map sourceMap sourceMap_surjective
      have hM : M≤ScalarFourRepeatedHeadModel.top.ker := by
        rintro _ ⟨x,hx,rfl⟩
        exact state_le_top_kernel i h8 hx
      let e : (Source ⧸ state i) ≃* (R ⧸ M) :=
        quotientEquivOfKerLe sourceMap sourceMap_surjective (state i) (kernel_le_state i h0)
      exact (repeatedQuotient hZmud M hM).comapEquiv e

/-- Every actual original normal denominator, selected by the existing
complete word registry rather than a newly enumerated list. -/
def sourceCertificate (hZmud : ZmudFaithfulCharacterTupleInput)
    (N : Subgroup Source) [N.Normal] : PreE7Y1QuotientCertificate (Source ⧸ N) := by
  let selected := PrimitiveAffineEightFrameRow21NormalCertificate.complete N
  let i := Classical.choose selected
  have hi : state i=N := Classical.choose_spec selected
  exact (stateCertificate hZmud i).comapEquiv
    (QuotientGroup.quotientMulEquivOfEq hi.symm)

/-- The certificate lives on the literal original eight-point action. -/
def actionCertificate (hZmud : ZmudFaithfulCharacterTupleInput) :
    PreE7Y1ActionCertificate FourPairY1ActualFrame.Original where
  width_eq := rfl
  quotient N := by
    letI : N.1.Normal := N.2
    let e := originalEquiv.symm
    let M := N.1.map e.toMonoidHom
    letI : M.Normal := N.2.map e.toMonoidHom e.surjective
    exact (sourceCertificate hZmud M).comapEquiv (QuotientGroup.congr N.1 M e rfl)

end SymmetricSubgroupAsymptotics.FourPairY1AllNormalSource
end
