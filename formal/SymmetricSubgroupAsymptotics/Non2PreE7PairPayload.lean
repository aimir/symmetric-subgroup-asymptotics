import SymmetricSubgroupAsymptotics.Non2PreE7PhysicalFrontier
import SymmetricSubgroupAsymptotics.Non2OriginalFusionFaithfulCover

/-!
# Universal pair payloads on the pre-E7 frontier

The pre-`E7` action index excludes a pair frame only at the eight widths
already paid by the fixed unipotent-prefix owner.  At every other pair width,
a retained pair frame has a faithful nonbinary top and therefore supplies the
complete arbitrary-normal-axis fusion payload.  This file records that
statement on the literal pre-`E7` representative; no abstract replacement of
the original action or normal axis is made.
-/

set_option autoImplicit false
noncomputable section
open scoped Classical

namespace SymmetricSubgroupAsymptotics
namespace Non2UnipotentPrefixFiniteMenu

/-- Pre-`E7` action classes of degree `2*s` which nevertheless admit a
literal pair system of half-width `s`.  Frame existence is retained as a
proposition, so choosing a frame later adds no counted index. -/
abbrev PreE7PairActionClass (s : ℕ) :=
  {i : PreE7ActionClass (2 * s) //
    Nonempty (BinaryPairFrame (preE7Action (2 * s) i) (Fin s))}

instance preE7PairActionClassFintype (s : ℕ) :
    Fintype (PreE7PairActionClass s) :=
  Fintype.ofFinite _

/-- The unchanged original permutation representative. -/
def preE7PairAction (s : ℕ) (i : PreE7PairActionClass s) :
    Subgroup (Equiv.Perm (Fin (2 * s))) :=
  preE7Action (2 * s) i.1

/-- A pair frame is chosen only after the conjugacy-class action index has
been fixed. -/
def preE7PairFrame (s : ℕ) (i : PreE7PairActionClass s) :
    BinaryPairFrame (preE7PairAction s i) (Fin s) :=
  Classical.choice i.2

instance preE7PairAction_pretransitive (s : ℕ)
    (i : PreE7PairActionClass s) :
    MulAction.IsPretransitive (preE7PairAction s i) (Fin (2 * s)) := by
  change MulAction.IsPretransitive i.1.1.representative (Fin (2 * s))
  infer_instance

instance preE7PairTop_pretransitive (s : ℕ)
    (i : PreE7PairActionClass s) :
    MulAction.IsPretransitive (preE7PairFrame s i).top.range (Fin s) :=
  (preE7PairFrame s i).top_pretransitive

theorem preE7PairAction_not_isPGroup (s : ℕ)
    (i : PreE7PairActionClass s) :
    ¬ IsPGroup 2 (preE7PairAction s i) := by
  change ¬ IsPGroup 2 i.1.1.representative
  exact i.1.1.representative_not_isPGroup

theorem preE7PairTop_not_isPGroup (s : ℕ)
    (i : PreE7PairActionClass s) :
    ¬ IsPGroup 2 (preE7PairFrame s i).top.range :=
  (preE7PairFrame s i).top_not_isPGroup
    (preE7PairAction_not_isPGroup s i)

/-- The selected eight `E7` pair widths are literally absent from the
pre-`E7` pair index.  This proves disjointness at the action-index level. -/
theorem preE7PairActionClass_false_of_selected
    (d : PairCountLabel) (i : PreE7PairActionClass d.pairCount) : False := by
  exact i.1.2 d rfl i.2

instance preE7PairActionClass_isEmpty_of_selected (d : PairCountLabel) :
    IsEmpty (PreE7PairActionClass d.pairCount) :=
  ⟨preE7PairActionClass_false_of_selected d⟩

/-- Every literal normal axis of every residual pre-`E7` pair action carries
the complete original-weight nonbinary fusion payload.  This is the universal
pair-capacity theorem at the exact action interface needed by the remaining
pre-`E7` catalogue. -/
theorem exists_preE7PairAxisPayload
    (hTracey : TraceyBinaryFormulaInput)
    (hExceptional : TraceyBinaryExceptionalThreeInput)
    {s : ℕ} (hs : 24 ≤ s) (heven : Even s)
    (i : PreE7PairActionClass s)
    (N : {N : Subgroup (preE7PairAction s i) // N.Normal}) :
    Nonempty (Non2OriginalFusionAxisPayload s (preE7PairAction s i) N) := by
  exact
    (preE7PairFrame s i).exists_non2OriginalFusionAxisPayload_of_arbitraryPairAxis
      N hTracey hExceptional (preE7PairTop_not_isPGroup s i)
      ⟨0, by omega⟩ hs heven

/-- Canonical choice of the universal payload after the original action and
literal normal axis have been fixed. -/
noncomputable def preE7PairAxisPayload
    (hTracey : TraceyBinaryFormulaInput)
    (hExceptional : TraceyBinaryExceptionalThreeInput)
    {s : ℕ} (hs : 24 ≤ s) (heven : Even s)
    (i : PreE7PairActionClass s)
    (N : {N : Subgroup (preE7PairAction s i) // N.Normal}) :
    Non2OriginalFusionAxisPayload s (preE7PairAction s i) N :=
  Classical.choice
    (exists_preE7PairAxisPayload hTracey hExceptional hs heven i N)

/-- The selected payload has the strict original-degree reduction required
by the direct recurrence. -/
theorem preE7PairAxisPayload_prefixDegree_lt
    (hTracey : TraceyBinaryFormulaInput)
    (hExceptional : TraceyBinaryExceptionalThreeInput)
    {s : ℕ} (hs : 24 ≤ s) (heven : Even s)
    (i : PreE7PairActionClass s)
    (N : {N : Subgroup (preE7PairAction s i) // N.Normal}) :
    (preE7PairAxisPayload hTracey hExceptional hs heven i N).certificate.prefixDegree
        < 2 * s :=
  (preE7PairAxisPayload hTracey hExceptional hs heven i N).certificate.prefixDegree_lt hs

/-- The exact universal reserve retained on every residual pair axis. -/
theorem preE7PairAxisPayload_gap_ge
    (hTracey : TraceyBinaryFormulaInput)
    (hExceptional : TraceyBinaryExceptionalThreeInput)
    {s : ℕ} (hs : 24 ≤ s) (heven : Even s)
    (i : PreE7PairActionClass s)
    (N : {N : Subgroup (preE7PairAction s i) // N.Normal}) :
    (s : ℝ) / 768 ≤
      (preE7PairAxisPayload hTracey hExceptional hs heven i N).certificate.gapParameter :=
  (preE7PairAxisPayload hTracey hExceptional hs heven i N).certificate.gap_ge

end Non2UnipotentPrefixFiniteMenu
end SymmetricSubgroupAsymptotics

end
