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

end Non2UnipotentPrefixFiniteMenu
end SymmetricSubgroupAsymptotics

end
