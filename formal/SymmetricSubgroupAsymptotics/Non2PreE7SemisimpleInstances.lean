import SymmetricSubgroupAsymptotics.Non2PreE7SemisimpleTemplate
import SymmetricSubgroupAsymptotics.Non2PreE7Sns2RankTailInstance
import SymmetricSubgroupAsymptotics.Non2PreE7Sns2ExceptionalCatalogue

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

/-- `SS`: the displayed semisimple layer is the entire nontrivial action. -/
structure PreE7SsSourceData (w : ℕ) (i : PreE7NonPairActionClass w) where
  outer : PreE7SemisimpleOuterSourceData .ss w i
  layer_eq_top : outer.E = ⊤
  layer_ne_bot : outer.E ≠ ⊥

/-- `SNS`: a nontrivial semisimple normal layer with a genuinely smaller
outer quotient.  The numerical quotient-size margin is retained in the
outer certificate's comparator parameters. -/
structure PreE7SnsSourceData (w : ℕ) (i : PreE7NonPairActionClass w) where
  outer : PreE7SemisimpleOuterSourceData .sns w i
  width_lower : 64 ≤ w
  layer_ne_bot : outer.E ≠ ⊥

/-- `SO`: the direct small-order all-source theorem.  Its proof is not a
semisimple-layer reduction, so the complete direct comparator certificate is
retained together with the exact audited order scope. -/
structure PreE7SoSourceData (w : ℕ) (i : PreE7NonPairActionClass w) where
  width_lower : 64 ≤ w
  order_not_two_power : ¬ IsPGroup 2 (preE7NonPairAction w i)
  order_log_small : 8 * Nat.log 2 (Nat.card (preE7NonPairAction w i)) ≤ w
  certificate : PreE7EarlierActionComparatorCertificate .so w i

/-- `NSAPRIM`: one action in the fixed nonsoluble primitive-affine range.
The bounded catalogue-completeness premise is a separate coverage input;
this datum retains only the literal action's checked pointwise certificate. -/
structure PreE7NsaprimSourceData
    (w : ℕ) (i : PreE7NonPairActionClass w) where
  width_lower : 5 ≤ w
  width_upper : w ≤ 1024
  primitive : MulAction.IsPreprimitive
    (preE7NonPairAction w i) (Fin w)
  certificate : PreE7EarlierActionComparatorCertificate .nsaprim w i

/-- Exact source type of all five semisimple families. -/
def SemisimpleCertificateSourceData
    (family : PreE7NoPairNoC3EarlierOwnerFamily)
    (w : ℕ) (i : PreE7NonPairActionClass w) : Type 1 :=
  match family with
  | .ss => PreE7SsSourceData w i
  | .so => PreE7SoSourceData w i
  | .sns => PreE7SnsSourceData w i
  | .sns2 => PreE7Sns2SourceData w i
  | .nsaprim => PreE7NsaprimSourceData w i
  | _ => PEmpty

variable {w : ℕ} {i : PreE7NonPairActionClass w}

def preE7_ssCertificate
    (S : SemisimpleCertificateSourceData .ss w i) :
    PreE7EarlierActionComparatorCertificate .ss w i :=
  S.outer.certificate

def preE7_soCertificate
    (S : SemisimpleCertificateSourceData .so w i) :
    PreE7EarlierActionComparatorCertificate .so w i :=
  S.certificate

def preE7_snsCertificate
    (S : SemisimpleCertificateSourceData .sns w i) :
    PreE7EarlierActionComparatorCertificate .sns w i :=
  S.outer.certificate

def preE7_nsaprimCertificate
    (S : SemisimpleCertificateSourceData .nsaprim w i) :
    PreE7EarlierActionComparatorCertificate .nsaprim w i :=
  S.certificate

def preE7_sns2Certificate
    (S : SemisimpleCertificateSourceData .sns2 w i) :
    PreE7Sns2RankTailCertificate w i :=
  preE7_sns2RankTailCertificate S

theorem preE7_ssFamilyAction
    (S : SemisimpleCertificateSourceData .ss w i) :
    preE7NoPairNoC3EarlierFamilyAction .ss w i :=
  ⟨preE7_ssCertificate S⟩

theorem preE7_soFamilyAction
    (S : SemisimpleCertificateSourceData .so w i) :
    preE7NoPairNoC3EarlierFamilyAction .so w i :=
  ⟨preE7_soCertificate S⟩

theorem preE7_snsFamilyAction
    (S : SemisimpleCertificateSourceData .sns w i) :
    preE7NoPairNoC3EarlierFamilyAction .sns w i :=
  ⟨preE7_snsCertificate S⟩

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
