import SymmetricSubgroupAsymptotics.Non2PreE7SemisimpleTemplate
import SymmetricSubgroupAsymptotics.Non2PreE7Sns2RankTailInstance
import SymmetricSubgroupAsymptotics.Non2PreE7Sns2ExceptionalCatalogue
import SymmetricSubgroupAsymptotics.Non2PreE7SmallOrderSemisimple
import SymmetricSubgroupAsymptotics.Non2PreE7ActualSemisimple
import SymmetricSubgroupAsymptotics.Non2PreE7SemisimpleSmallQuotient
import SymmetricSubgroupAsymptotics.Non2PreE7NonsolublePrimitiveAffine

/-!
# The five semisimple-family certificate shapes

`SS` and `SNS` use the proved semisimple outer-fibre template.  `SNS2` uses
the correlated binary-rank-tail certificate and therefore remains outside
the pointwise comparator type.  `SO` and `NSAPRIM` retain their direct
pointwise certificates together with the structural scope conditions from
their audited sources.

This distinction is mathematical: forcing `SNS2` into a pointwise envelope
would discard the weighted binary-rank moment that makes its all-width sum
contractive.
-/

set_option autoImplicit false
noncomputable section
open scoped Classical

namespace SymmetricSubgroupAsymptotics
namespace Non2UnipotentPrefixFiniteMenu

def IsPreE7SemisimpleFamily
    (family : PreE7NoPairNoC3EarlierOwnerFamily) : Prop :=
  family.template = .semisimple

instance : DecidablePred IsPreE7SemisimpleFamily := fun family =>
  inferInstanceAs (Decidable (family.template = .semisimple))

theorem isPreE7SemisimpleFamily_iff
    (family : PreE7NoPairNoC3EarlierOwnerFamily) :
    IsPreE7SemisimpleFamily family ↔
      family = .ss ∨ family = .so ∨ family = .sns ∨
        family = .sns2 ∨ family = .nsaprim := by
  cases family <;> decide

/-- Exact source type of all five semisimple families. -/
def SemisimpleCertificateSourceData
    (family : PreE7NoPairNoC3EarlierOwnerFamily)
    (w : ℕ) (i : PreE7NonPairActionClass w) : Type 1 :=
  match family with
  | .ss => PreE7SsActionCertificate w i
  | .so => ULift.{1, 0} (PreE7SoOrderSourceData w i)
  | .sns => PreE7SnsActionCertificate w i
  | .sns2 => PreE7Sns2SourceData w i
  | .nsaprim => ULift.{1, 0} (PreE7NsaprimActionCertificate w i)
  | _ => PEmpty

variable {w : ℕ} {i : PreE7NonPairActionClass w}

def preE7_ssCertificate
    (S : SemisimpleCertificateSourceData .ss w i) :
    PreE7EarlierActionComparatorCertificate .ss w i :=
  S.direct.certificate

def preE7_soCertificate
    (hgen : PermutationSubgroupGeneratorBound)
    (S : SemisimpleCertificateSourceData .so w i) :
    PreE7EarlierActionComparatorCertificate .so w i :=
  S.down.certificate hgen

def preE7_snsCertificate
    (hgen : PermutationSubgroupGeneratorBound)
    (S : SemisimpleCertificateSourceData .sns w i) :
    PreE7EarlierActionComparatorCertificate .sns w i :=
  (S.direct hgen).certificate

def preE7_nsaprimCertificate
    (S : SemisimpleCertificateSourceData .nsaprim w i) :
    PreE7EarlierActionComparatorCertificate .nsaprim w i :=
  S.down.certificate

def preE7_sns2Certificate
    (S : SemisimpleCertificateSourceData .sns2 w i) :
    PreE7Sns2RankTailCertificate w i :=
  preE7_sns2RankTailCertificate S

theorem preE7_ssFamilyAction
    (S : SemisimpleCertificateSourceData .ss w i) :
    preE7NoPairNoC3EarlierFamilyAction .ss w i :=
  ⟨preE7_ssCertificate S⟩

theorem preE7_soFamilyAction
    (hgen : PermutationSubgroupGeneratorBound)
    (S : SemisimpleCertificateSourceData .so w i) :
    preE7NoPairNoC3EarlierFamilyAction .so w i :=
  ⟨preE7_soCertificate hgen S⟩

theorem preE7_snsFamilyAction
    (hgen : PermutationSubgroupGeneratorBound)
    (S : SemisimpleCertificateSourceData .sns w i) :
    preE7NoPairNoC3EarlierFamilyAction .sns w i :=
  ⟨preE7_snsCertificate hgen S⟩

theorem preE7_nsaprimFamilyAction
    (S : SemisimpleCertificateSourceData .nsaprim w i) :
    preE7NoPairNoC3EarlierFamilyAction .nsaprim w i :=
  ⟨preE7_nsaprimCertificate S⟩

/-- SNS2 lands in the mixed local certificate, retaining the weighted
rank-tail split rather than pretending to be pointwise. -/
def preE7_sns2LocalCertificate
    (S : SemisimpleCertificateSourceData .sns2 w i) :
    PreE7EarlierLocalCertificate .sns2 w i :=
  .ofSns2 (preE7_sns2Certificate S)

/-- The source dispatcher accepts no label outside the five audited
semisimple families. -/
theorem semisimpleCertificateSourceData_nonempty_iff
    (family : PreE7NoPairNoC3EarlierOwnerFamily)
    (w : ℕ) (i : PreE7NonPairActionClass w) :
    Nonempty (SemisimpleCertificateSourceData family w i) →
      IsPreE7SemisimpleFamily family := by
  cases family <;> simp_all [SemisimpleCertificateSourceData,
    IsPreE7SemisimpleFamily,
    PreE7NoPairNoC3EarlierOwnerFamily.template]

end Non2UnipotentPrefixFiniteMenu
end SymmetricSubgroupAsymptotics

end
