import SymmetricSubgroupAsymptotics.Non2PreE7ComparatorAbelianTowerTemplate

/-!
# The sixteen comparator/abelian-tower families

This file fixes the source shape of every historical family assigned to the
comparator-plus-abelian-layers template.  Fourteen families use one retained
abelian Yoneda tower on every literal normal axis.  `CB` and `S3WR` retain
their genuine additive branches, so they use the tower-plus-cold-tail form.

The family labels are used only to select a certificate shape.  An action is
accepted precisely when the corresponding source datum exists on that
literal action; no ledger label is promoted to a subgroup predicate.
-/

set_option autoImplicit false
noncomputable section
open scoped Classical

namespace SymmetricSubgroupAsymptotics
namespace Non2UnipotentPrefixFiniteMenu

/-- The sixteen families assigned to the comparator/abelian-tower template. -/
def IsPreE7ComparatorAbelianTowerFamily
    (family : PreE7NoPairNoC3EarlierOwnerFamily) : Prop :=
  family.template = .comparatorAbelianTower

instance : DecidablePred IsPreE7ComparatorAbelianTowerFamily := fun family =>
  inferInstanceAs (Decidable (family.template = .comparatorAbelianTower))

theorem isPreE7ComparatorAbelianTowerFamily_iff
    (family : PreE7NoPairNoC3EarlierOwnerFamily) :
    IsPreE7ComparatorAbelianTowerFamily family ↔
      family = .it ∨ family = .inv ∨ family = .pcs ∨
      family = .asFamily ∨ family = .cm ∨ family = .mult ∨
      family = .pcsStar ∨ family = .cp3 ∨ family = .tower ∨
      family = .comp ∨ family = .binirr ∨ family = .s3wr ∨
      family = .c3six ∨ family = .s3iso ∨ family = .s3cent ∨
      family = .cb := by
  cases family <;> decide

/-- Exact source type of a comparator/abelian-tower family.  `CB` and
`S3WR` use the additive source because their audited small modes contain a
source-independent cold tail. -/
def ComparatorAbelianTowerCertificateSourceData
    (family : PreE7NoPairNoC3EarlierOwnerFamily)
    (w : ℕ) (i : PreE7NonPairActionClass w) : Type 1 :=
  match family with
  | .it => PreE7ComparatorAbelianTowerSourceData .it w i
  | .inv => PreE7ComparatorAbelianTowerSourceData .inv w i
  | .pcs => PreE7ComparatorAbelianTowerSourceData .pcs w i
  | .asFamily => PreE7ComparatorAbelianTowerSourceData .asFamily w i
  | .cm => PreE7ComparatorAbelianTowerSourceData .cm w i
  | .mult => PreE7ComparatorAbelianTowerSourceData .mult w i
  | .pcsStar => PreE7ComparatorAbelianTowerSourceData .pcsStar w i
  | .cp3 => PreE7ComparatorAbelianTowerSourceData .cp3 w i
  | .tower => PreE7ComparatorAbelianTowerSourceData .tower w i
  | .comp => PreE7ComparatorAbelianTowerSourceData .comp w i
  | .binirr => PreE7ComparatorAbelianTowerSourceData .binirr w i
  | .s3wr => PreE7ComparatorAbelianTowerAdditiveSourceData .s3wr w i
  | .c3six => PreE7ComparatorAbelianTowerSourceData .c3six w i
  | .s3iso => PreE7ComparatorAbelianTowerSourceData .s3iso w i
  | .s3cent => PreE7ComparatorAbelianTowerSourceData .s3cent w i
  | .cb => PreE7ComparatorAbelianTowerAdditiveSourceData .cb w i
  | _ => PEmpty

variable {w : ℕ} {i : PreE7NonPairActionClass w}

/-! ## Family-specific constructors -/

def preE7_itCertificate
    (S : ComparatorAbelianTowerCertificateSourceData .it w i) :
    PreE7EarlierActionComparatorCertificate .it w i :=
  .ofAbelianYonedaTowers S

def preE7_invCertificate
    (S : ComparatorAbelianTowerCertificateSourceData .inv w i) :
    PreE7EarlierActionComparatorCertificate .inv w i :=
  .ofAbelianYonedaTowers S

def preE7_pcsCertificate
    (S : ComparatorAbelianTowerCertificateSourceData .pcs w i) :
    PreE7EarlierActionComparatorCertificate .pcs w i :=
  .ofAbelianYonedaTowers S

def preE7_asCertificate
    (S : ComparatorAbelianTowerCertificateSourceData .asFamily w i) :
    PreE7EarlierActionComparatorCertificate .asFamily w i :=
  .ofAbelianYonedaTowers S

def preE7_cmCertificate
    (S : ComparatorAbelianTowerCertificateSourceData .cm w i) :
    PreE7EarlierActionComparatorCertificate .cm w i :=
  .ofAbelianYonedaTowers S

def preE7_multCertificate
    (S : ComparatorAbelianTowerCertificateSourceData .mult w i) :
    PreE7EarlierActionComparatorCertificate .mult w i :=
  .ofAbelianYonedaTowers S

def preE7_pcsStarCertificate
    (S : ComparatorAbelianTowerCertificateSourceData .pcsStar w i) :
    PreE7EarlierActionComparatorCertificate .pcsStar w i :=
  .ofAbelianYonedaTowers S

def preE7_cp3Certificate
    (S : ComparatorAbelianTowerCertificateSourceData .cp3 w i) :
    PreE7EarlierActionComparatorCertificate .cp3 w i :=
  .ofAbelianYonedaTowers S

def preE7_towerCertificate
    (S : ComparatorAbelianTowerCertificateSourceData .tower w i) :
    PreE7EarlierActionComparatorCertificate .tower w i :=
  .ofAbelianYonedaTowers S

def preE7_compCertificate
    (S : ComparatorAbelianTowerCertificateSourceData .comp w i) :
    PreE7EarlierActionComparatorCertificate .comp w i :=
  .ofAbelianYonedaTowers S

def preE7_binirrCertificate
    (S : ComparatorAbelianTowerCertificateSourceData .binirr w i) :
    PreE7EarlierActionComparatorCertificate .binirr w i :=
  .ofAbelianYonedaTowers S

def preE7_s3wrCertificate
    (S : ComparatorAbelianTowerCertificateSourceData .s3wr w i) :
    PreE7EarlierActionComparatorCertificate .s3wr w i :=
  .ofAbelianYonedaTowersAdditive S

def preE7_c3sixCertificate
    (S : ComparatorAbelianTowerCertificateSourceData .c3six w i) :
    PreE7EarlierActionComparatorCertificate .c3six w i :=
  .ofAbelianYonedaTowers S

def preE7_s3isoCertificate
    (S : ComparatorAbelianTowerCertificateSourceData .s3iso w i) :
    PreE7EarlierActionComparatorCertificate .s3iso w i :=
  .ofAbelianYonedaTowers S

def preE7_s3centCertificate
    (S : ComparatorAbelianTowerCertificateSourceData .s3cent w i) :
    PreE7EarlierActionComparatorCertificate .s3cent w i :=
  .ofAbelianYonedaTowers S

def preE7_cbCertificate
    (S : ComparatorAbelianTowerCertificateSourceData .cb w i) :
    PreE7EarlierActionComparatorCertificate .cb w i :=
  .ofAbelianYonedaTowersAdditive S

/-- Dispatcher over exactly the sixteen comparator/abelian-tower families. -/
def preE7_comparatorAbelianTowerCertificate
    (family : PreE7NoPairNoC3EarlierOwnerFamily)
    (hfamily : IsPreE7ComparatorAbelianTowerFamily family)
    (w : ℕ) (i : PreE7NonPairActionClass w)
    (source : ComparatorAbelianTowerCertificateSourceData family w i) :
    PreE7EarlierActionComparatorCertificate family w i := by
  cases family
  all_goals first
    | exact absurd hfamily (by decide)
    | skip
  case it => exact preE7_itCertificate source
  case inv => exact preE7_invCertificate source
  case pcs => exact preE7_pcsCertificate source
  case asFamily => exact preE7_asCertificate source
  case cm => exact preE7_cmCertificate source
  case mult => exact preE7_multCertificate source
  case pcsStar => exact preE7_pcsStarCertificate source
  case cp3 => exact preE7_cp3Certificate source
  case tower => exact preE7_towerCertificate source
  case comp => exact preE7_compCertificate source
  case binirr => exact preE7_binirrCertificate source
  case s3wr => exact preE7_s3wrCertificate source
  case c3six => exact preE7_c3sixCertificate source
  case s3iso => exact preE7_s3isoCertificate source
  case s3cent => exact preE7_s3centCertificate source
  case cb => exact preE7_cbCertificate source

/-- Every dispatched source supplies the catalogue's actual action
predicate. -/
theorem preE7_comparatorAbelianTowerFamilyAction
    (family : PreE7NoPairNoC3EarlierOwnerFamily)
    (hfamily : IsPreE7ComparatorAbelianTowerFamily family)
    (w : ℕ) (i : PreE7NonPairActionClass w)
    (source : ComparatorAbelianTowerCertificateSourceData family w i) :
    preE7NoPairNoC3EarlierFamilyAction family w i :=
  ⟨preE7_comparatorAbelianTowerCertificate family hfamily w i source⟩

/-- The source dispatcher cannot accept a label outside the audited
sixteen-family list. -/
theorem comparatorAbelianTowerCertificateSourceData_nonempty_iff
    (family : PreE7NoPairNoC3EarlierOwnerFamily)
    (w : ℕ) (i : PreE7NonPairActionClass w) :
    Nonempty (ComparatorAbelianTowerCertificateSourceData family w i) →
      IsPreE7ComparatorAbelianTowerFamily family := by
  cases family <;> simp_all [ComparatorAbelianTowerCertificateSourceData,
    IsPreE7ComparatorAbelianTowerFamily,
    PreE7NoPairNoC3EarlierOwnerFamily.template]

end Non2UnipotentPrefixFiniteMenu
end SymmetricSubgroupAsymptotics

end
