import SymmetricSubgroupAsymptotics.CFSGSerreQuadraticCanonicalRoots
import SymmetricSubgroupAsymptotics.CFSGSerreQuadraticSourceTransport
import SymmetricSubgroupAsymptotics.CFSGPerfectCentralKernel
import SymmetricSubgroupAsymptotics.CFSGCenterQuotientEquiv

/-! A faithful ORIGINAL source-image action and a perfect natural group
with central image kernel have equivalent FULL-centre quotients. Neither
source simplicity nor a separately named finite-model recognition is used.
The actual E6 installer supplies every condition from proved source facts. -/
set_option autoImplicit false
noncomputable section
namespace SymmetricSubgroupAsymptotics.CFSGSerreQuadraticSourceCenterEquivalence
open CFSG.Models.Chevalley CFSGSerreQuadraticMatrix
variable {n : ℕ} {A B : Matrix (Fin n) (Fin n) ℤ}
    {I : Type*} [Fintype I] [DecidableEq I]

/-- Literal source transport does not alter perfectness of the SAME
canonical matrix group. The proof eliminates the Cartan equality once. -/
theorem perfect_transportSource (h : A = B) (D : Data A I) (K : Type) [Field K]
    (hperfect : commutator (canonicalElementaryGroup D K) = ⊤) :
    commutator (canonicalElementaryGroup (transportSource h D) K) = ⊤ := by
  cases h
  exact hperfect

/-- The action and its kernel transport along that SAME source equality;
all target matrices remain literal, not a chosen recognition map. -/
theorem kernel_central_transportSource (h : A = B) (D : Data A I) (K : Type) [Field K]
    (hfour : ∀ neg i (x : Space A K),
      fieldSecond D K neg i * baseChange D K x * fieldSecond D K neg i = 0)
    (hfour' : ∀ neg i (x : Space B K),
      fieldSecond (transportSource h D) K neg i * baseChange (transportSource h D) K x *
        fieldSecond (transportSource h D) K neg i = 0)
    (hker : (canonicalImageAction D K hfour).ker ≤
      Subgroup.center (canonicalElementaryGroup D K)) :
    (canonicalImageAction (transportSource h D) K hfour').ker ≤
      Subgroup.center (canonicalElementaryGroup (transportSource h D) K) := by
  cases h
  exact hker

variable (D : Data A I) (K : Type) [Field K]
    (hfour : ∀ neg i (x : Space A K),
      fieldSecond D K neg i * baseChange D K x * fieldSecond D K neg i = 0)

private def naturalToAction := (canonicalImageAction D K hfour).rangeRestrict

private theorem naturalToAction_surjective :
    Function.Surjective (naturalToAction D K hfour) :=
  (canonicalImageAction D K hfour).rangeRestrict_surjective

include hfour in
private theorem naturalToAction_kernel_central
    (hker : (canonicalImageAction D K hfour).ker ≤
      Subgroup.center (canonicalElementaryGroup D K)) :
    (naturalToAction D K hfour).ker ≤ Subgroup.center (canonicalElementaryGroup D K) := by
  intro g hg
  apply hker
  change canonicalImageAction D K hfour g = 1
  exact congrArg Subtype.val hg

/-- The natural canonical group and its actual action range have the
same full-centre quotient, using perfectness and the proved central kernel. -/
def naturalProjectiveEquivAction
    (hperfect : commutator (canonicalElementaryGroup D K) = ⊤)
    (hker : (canonicalImageAction D K hfour).ker ≤
      Subgroup.center (canonicalElementaryGroup D K)) :
    (canonicalElementaryGroup D K ⧸ Subgroup.center (canonicalElementaryGroup D K)) ≃*
      ((canonicalImageAction D K hfour).range ⧸
        Subgroup.center (canonicalImageAction D K hfour).range) := by
  let f := naturalToAction D K hfour
  let q := QuotientGroup.mk' (Subgroup.center (canonicalImageAction D K hfour).range)
  have hf : Function.Surjective f := naturalToAction_surjective D K hfour
  have hq : Function.Surjective q := QuotientGroup.mk'_surjective _
  have hk : (q.comp f).ker = Subgroup.center (canonicalElementaryGroup D K) :=
    CFSGPerfectCentralKernel.projective_kernel_eq_center f hf hperfect
      (naturalToAction_kernel_central D K hfour hker)
  exact (QuotientGroup.quotientMulEquivOfEq hk.symm).trans
    (QuotientGroup.quotientKerEquivOfSurjective (q.comp f) (hq.comp hf))

/-- No simplicity premise: genuine source-action faithfulness, actual
range equality, and perfect natural central-kernel descent suffice. -/
def originalProjectiveEquivCanonical
    (hinj : Function.Injective (imageRepresentation D K))
    (hperfect : commutator (canonicalElementaryGroup D K) = ⊤)
    (hker : (canonicalImageAction D K hfour).ker ≤
      Subgroup.center (canonicalElementaryGroup D K)) :
    Projective A K ≃*
      (canonicalElementaryGroup D K ⧸ Subgroup.center (canonicalElementaryGroup D K)) := by
  let e : Model A K ≃* (imageRepresentation D K).range :=
    MulEquiv.ofBijective (imageRepresentation D K).rangeRestrict
      ⟨fun x y h => hinj (congrArg Subtype.val h),
        (imageRepresentation D K).rangeRestrict_surjective⟩
  let e' : Model A K ≃* (canonicalImageAction D K hfour).range :=
    e.trans (MulEquiv.subgroupCongr (canonical_action_ranges_eq D K hfour))
  exact (CFSGCenterQuotientEquiv.equiv e').trans
    (naturalProjectiveEquivAction D K hfour hperfect hker).symm

end SymmetricSubgroupAsymptotics.CFSGSerreQuadraticSourceCenterEquivalence
