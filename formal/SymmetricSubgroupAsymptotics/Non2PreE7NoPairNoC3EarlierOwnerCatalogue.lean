import SymmetricSubgroupAsymptotics.Non2PreE7NoPairNoC3ConcreteInterface

/-!
# Ordered earlier-owner catalogue for the final pre-E7 residual

This is the exact 53-family precedence inherited by the final no-pair,
no-regular-`C3` residual.  The type records the mathematical family names and
their order; it does not turn a historical label into a subgroup predicate.
The subgroup predicates and their direct owned-axis envelopes are separate
data and must be supplied by the corresponding formal counting theorems.

The historical `DEG9all` row is deliberately absent: it is a separate
degree-nine partition in the retained construction, not one of these earlier
owner families.
-/

set_option autoImplicit false
noncomputable section

namespace SymmetricSubgroupAsymptotics
namespace Non2UnipotentPrefixFiniteMenu

/-- The 53 earlier-owner families, in exact overlay precedence. -/
inductive PreE7NoPairNoC3EarlierOwnerFamily where
  -- D0379
  | it | inv | pcs | asFamily | dih | cm
  -- D0381 (`DEG9all` remains a separate partition)
  | mult | pcsStar | inv12All | ss | cp3
  -- D0382--D0385
  | so | sns | tower | comp | sns2 | binirr | s4 | acert
  -- D0386--D0388
  | a4w2 | f20 | lin | saprim | s3wr
  | fwrall | aff128 | regcap | ps3cap | p4cap
  -- D0389--D0392
  | acomp | nsaprim | c3six | s3exc | s3iso | s3cent
  | smallaff | s3two | s3cycl | s3syl | cb | tf
  | fiveExc | b4char | y1
  -- D0393--D0407
  | fchar | mchar | b6 | qchar | dzero | bchar | hchar | dchar | jchar
  deriving DecidableEq, Fintype

/-- Number of earlier-owner families in the frozen overlay precedence. -/
abbrev preE7NoPairNoC3EarlierOwnerCount : ℕ :=
  Fintype.card PreE7NoPairNoC3EarlierOwnerFamily

theorem preE7NoPairNoC3EarlierOwnerCount_eq :
    preE7NoPairNoC3EarlierOwnerCount = 53 := by
  decide

/-- Canonical finite index used by the first-owner machinery. -/
def preE7NoPairNoC3EarlierOwnerEquiv :
    Fin preE7NoPairNoC3EarlierOwnerCount ≃
      PreE7NoPairNoC3EarlierOwnerFamily :=
  (Fintype.equivFin PreE7NoPairNoC3EarlierOwnerFamily).symm

/-- The five proof templates to which the 53 action families reduce.  These
are mathematical certificate shapes, not replacements for the family
predicates: a family applies precisely when its corresponding certificate is
inhabited on the literal original action. -/
inductive PreE7EarlierCertificateTemplate where
  | refinedCapacity
  | comparatorAbelianTower
  | character
  | semisimple
  | smallFixedAdditive
  deriving DecidableEq, Fintype

/-- The audited template assignment.  In particular, the three semisimple
families `so`, `sns`, and `sns2` remain separate: neither `comp` nor `acert`
covers their full source predicates.  The `fwrall` certificate includes its
additive branch B inside one refined-capacity family certificate. -/
def PreE7NoPairNoC3EarlierOwnerFamily.template :
    PreE7NoPairNoC3EarlierOwnerFamily → PreE7EarlierCertificateTemplate
  | .acert | .fwrall | .aff128 | .regcap | .ps3cap | .p4cap
  | .acomp | .smallaff | .dzero => .refinedCapacity
  | .comp | .binirr | .c3six | .s3iso | .s3cent | .cb | .s3wr
  | .it | .inv | .pcs | .pcsStar | .cp3 | .cm | .mult | .asFamily
  | .tower => .comparatorAbelianTower
  | .fchar | .mchar | .bchar | .dchar | .jchar | .hchar | .qchar
  | .b4char => .character
  | .ss | .so | .sns | .sns2 | .nsaprim => .semisimple
  | .dih | .inv12All | .s4 | .a4w2 | .f20 | .lin | .saprim
  | .s3exc | .s3two | .s3cycl | .s3syl | .tf | .fiveExc | .y1
  | .b6 => .smallFixedAdditive

/-- The exceptional moment which a certificate must retain in addition to
its template's generic complete-quotient moment. -/
inductive PreE7EarlierSpecialMoment where
  | none
  | markedC4
  | binaryRankTail
  deriving DecidableEq, Fintype

def PreE7NoPairNoC3EarlierOwnerFamily.specialMoment :
    PreE7NoPairNoC3EarlierOwnerFamily → PreE7EarlierSpecialMoment
  | .f20 => .markedC4
  | .y1 | .b6 | .sns2 => .binaryRankTail
  | _ => .none

theorem preE7Earlier_template_partition_cardinality :
    (Finset.univ.filter (fun f : PreE7NoPairNoC3EarlierOwnerFamily =>
      f.template = .refinedCapacity)).card = 9 ∧
    (Finset.univ.filter (fun f : PreE7NoPairNoC3EarlierOwnerFamily =>
      f.template = .comparatorAbelianTower)).card = 16 ∧
    (Finset.univ.filter (fun f : PreE7NoPairNoC3EarlierOwnerFamily =>
      f.template = .character)).card = 8 ∧
    (Finset.univ.filter (fun f : PreE7NoPairNoC3EarlierOwnerFamily =>
      f.template = .semisimple)).card = 5 ∧
    (Finset.univ.filter (fun f : PreE7NoPairNoC3EarlierOwnerFamily =>
      f.template = .smallFixedAdditive)).card = 15 := by
  decide

end Non2UnipotentPrefixFiniteMenu
end SymmetricSubgroupAsymptotics

end
