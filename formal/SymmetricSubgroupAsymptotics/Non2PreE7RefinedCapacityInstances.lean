import SymmetricSubgroupAsymptotics.Non2PreE7RefinedCapacityTemplate

/-!
# The nine refined-capacity families as certificate instances

This file fixes the exact source shape of every family assigned to the
refined-capacity template.  Eight families use the correlated multiplicative
carrier/Yoneda capacity.  `FWRALL` alone uses the additive source, retaining
its source-independent branch B as a pure cold row.

The family match is deliberately exhaustive.  A label outside these nine has
empty source data, while a refined-capacity label cannot be routed through the
wrong constructor.  The mathematical action predicate is still the common
predicate `preE7NoPairNoC3EarlierFamilyAction`: the declarations below only
exhibit its certificate when the corresponding literal source data exist.
-/

set_option autoImplicit false
noncomputable section
open scoped Classical

namespace SymmetricSubgroupAsymptotics
namespace Non2UnipotentPrefixFiniteMenu

/-- The nine families assigned to the refined-capacity template. -/
def IsPreE7RefinedCapacityFamily
    (family : PreE7NoPairNoC3EarlierOwnerFamily) : Prop :=
  family.template = .refinedCapacity

instance : DecidablePred IsPreE7RefinedCapacityFamily := fun family =>
  inferInstanceAs (Decidable (family.template = .refinedCapacity))

theorem isPreE7RefinedCapacityFamily_iff
    (family : PreE7NoPairNoC3EarlierOwnerFamily) :
    IsPreE7RefinedCapacityFamily family ↔
      family = .acert ∨ family = .fwrall ∨ family = .aff128 ∨
        family = .regcap ∨ family = .ps3cap ∨ family = .p4cap ∨
        family = .acomp ∨ family = .smallaff ∨ family = .dzero := by
  cases family <;> decide

/-- Exact source type of a refined-capacity family.  `FWRALL` has a genuine
additive branch; all other refined-capacity families have one correlated
multiplicative capacity. -/
def RefinedCapacityCertificateSourceData
    (family : PreE7NoPairNoC3EarlierOwnerFamily)
    (w : ℕ) (i : PreE7NonPairActionClass w) : Type 1 :=
  match family with
  | .acert => PreE7RefinedCapacitySourceData .acert w i
  | .fwrall => PreE7RefinedCapacityAdditiveSourceData .fwrall w i
  | .aff128 => PreE7RefinedCapacitySourceData .aff128 w i
  | .regcap => PreE7RefinedCapacitySourceData .regcap w i
  | .ps3cap => PreE7RefinedCapacitySourceData .ps3cap w i
  | .p4cap => PreE7RefinedCapacitySourceData .p4cap w i
  | .acomp => PreE7RefinedCapacitySourceData .acomp w i
  | .smallaff => PreE7RefinedCapacitySourceData .smallaff w i
  | .dzero => PreE7RefinedCapacitySourceData .dzero w i
  | _ => PEmpty

variable {w : ℕ} {i : PreE7NonPairActionClass w}

/-! ## Family-specific certificates -/

def preE7_acertCertificate
    (S : RefinedCapacityCertificateSourceData .acert w i) :
    PreE7EarlierActionComparatorCertificate .acert w i :=
  .ofRefinedCapacity S

def preE7_fwrallCertificate
    (S : RefinedCapacityCertificateSourceData .fwrall w i) :
    PreE7EarlierActionComparatorCertificate .fwrall w i :=
  .ofRefinedCapacityAdditive S

def preE7_aff128Certificate
    (S : RefinedCapacityCertificateSourceData .aff128 w i) :
    PreE7EarlierActionComparatorCertificate .aff128 w i :=
  .ofRefinedCapacity S

def preE7_regcapCertificate
    (S : RefinedCapacityCertificateSourceData .regcap w i) :
    PreE7EarlierActionComparatorCertificate .regcap w i :=
  .ofRefinedCapacity S

def preE7_ps3capCertificate
    (S : RefinedCapacityCertificateSourceData .ps3cap w i) :
    PreE7EarlierActionComparatorCertificate .ps3cap w i :=
  .ofRefinedCapacity S

def preE7_p4capCertificate
    (S : RefinedCapacityCertificateSourceData .p4cap w i) :
    PreE7EarlierActionComparatorCertificate .p4cap w i :=
  .ofRefinedCapacity S

def preE7_acompCertificate
    (S : RefinedCapacityCertificateSourceData .acomp w i) :
    PreE7EarlierActionComparatorCertificate .acomp w i :=
  .ofRefinedCapacity S

def preE7_smallaffCertificate
    (S : RefinedCapacityCertificateSourceData .smallaff w i) :
    PreE7EarlierActionComparatorCertificate .smallaff w i :=
  .ofRefinedCapacity S

def preE7_dzeroCertificate
    (S : RefinedCapacityCertificateSourceData .dzero w i) :
    PreE7EarlierActionComparatorCertificate .dzero w i :=
  .ofRefinedCapacity S

/-- Dispatcher over exactly the nine refined-capacity families. -/
def preE7_refinedCapacityCertificate
    (family : PreE7NoPairNoC3EarlierOwnerFamily)
    (hfamily : IsPreE7RefinedCapacityFamily family)
    (w : ℕ) (i : PreE7NonPairActionClass w)
    (source : RefinedCapacityCertificateSourceData family w i) :
    PreE7EarlierActionComparatorCertificate family w i := by
  cases family
  all_goals first
    | exact absurd hfamily (by decide)
    | skip
  case acert => exact preE7_acertCertificate source
  case fwrall => exact preE7_fwrallCertificate source
  case aff128 => exact preE7_aff128Certificate source
  case regcap => exact preE7_regcapCertificate source
  case ps3cap => exact preE7_ps3capCertificate source
  case p4cap => exact preE7_p4capCertificate source
  case acomp => exact preE7_acompCertificate source
  case smallaff => exact preE7_smallaffCertificate source
  case dzero => exact preE7_dzeroCertificate source

/-- Every dispatched source supplies the catalogue's actual action
predicate. -/
theorem preE7_refinedCapacityFamilyAction
    (family : PreE7NoPairNoC3EarlierOwnerFamily)
    (hfamily : IsPreE7RefinedCapacityFamily family)
    (w : ℕ) (i : PreE7NonPairActionClass w)
    (source : RefinedCapacityCertificateSourceData family w i) :
    preE7NoPairNoC3EarlierFamilyAction family w i :=
  ⟨preE7_refinedCapacityCertificate family hfamily w i source⟩

/-- The exact nine-way source dispatcher is exhaustive. -/
theorem refinedCapacityCertificateSourceData_nonempty_iff
    (family : PreE7NoPairNoC3EarlierOwnerFamily)
    (w : ℕ) (i : PreE7NonPairActionClass w) :
    Nonempty (RefinedCapacityCertificateSourceData family w i) →
      IsPreE7RefinedCapacityFamily family := by
  cases family <;> simp_all [RefinedCapacityCertificateSourceData,
    IsPreE7RefinedCapacityFamily, PreE7NoPairNoC3EarlierOwnerFamily.template]

end Non2UnipotentPrefixFiniteMenu
end SymmetricSubgroupAsymptotics

end
