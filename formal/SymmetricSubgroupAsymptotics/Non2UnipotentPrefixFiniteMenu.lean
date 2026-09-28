import SymmetricSubgroupAsymptotics.BinaryPairFrameTransport
import SymmetricSubgroupAsymptotics.Non2TransitiveActionClasses

/-!
# The fixed nonbinary unipotent-prefix pair menu

The selected O03/O02 unipotent-prefix branch uses eight faithful pair-top
degrees.  This file records those degrees and the complete conjugacy-class
index of nonbinary transitive original actions that admit a literal pair
frame.  Frame existence is a proposition in the subtype; a frame is chosen
only after the physical action class has been fixed, so auxiliary frame
choices create no counted multiplicity.
-/

set_option autoImplicit false
noncomputable section
open scoped Classical Pointwise

namespace SymmetricSubgroupAsymptotics.Non2UnipotentPrefixFiniteMenu

inductive PairCountLabel
  | c24 | c32 | c48 | c64 | c96 | c128 | c192 | c256
  deriving DecidableEq, Fintype

def PairCountLabel.pairCount : PairCountLabel → ℕ
  | .c24 => 24
  | .c32 => 32
  | .c48 => 48
  | .c64 => 64
  | .c96 => 96
  | .c128 => 128
  | .c192 => 192
  | .c256 => 256

def PairCountLabel.sourceDegree (d : PairCountLabel) : ℕ :=
  2 * d.pairCount

theorem PairCountLabel.pairCount_pos (d : PairCountLabel) :
    0 < d.pairCount := by
  cases d <;> decide

theorem PairCountLabel.pairCount_ge_24 (d : PairCountLabel) :
    24 ≤ d.pairCount := by
  cases d <;> decide

theorem PairCountLabel.pairCount_even (d : PairCountLabel) :
    Even d.pairCount := by
  cases d <;> norm_num [pairCount]

theorem PairCountLabel.pairCount_le_256 (d : PairCountLabel) :
    d.pairCount ≤ 256 := by
  cases d <;> decide

theorem PairCountLabel.sourceDegree_le_512 (d : PairCountLabel) :
    d.sourceDegree ≤ 512 := by
  cases d <;> decide

theorem PairCountLabel.pairCount_injective :
    Function.Injective PairCountLabel.pairCount := by
  intro d e h
  cases d <;> cases e <;> simp_all [pairCount]

theorem PairCountLabel.exists_of_pairCount_menu {s : ℕ}
    (h : s = 24 ∨ s = 32 ∨ s = 48 ∨ s = 64 ∨
      s = 96 ∨ s = 128 ∨ s = 192 ∨ s = 256) :
    ∃ d : PairCountLabel, d.pairCount = s := by
  rcases h with h24 | h32 | h48 | h64 | h96 | h128 | h192 | h256
  · exact ⟨.c24, h24.symm⟩
  · exact ⟨.c32, h32.symm⟩
  · exact ⟨.c48, h48.symm⟩
  · exact ⟨.c64, h64.symm⟩
  · exact ⟨.c96, h96.symm⟩
  · exact ⟨.c128, h128.symm⟩
  · exact ⟨.c192, h192.symm⟩
  · exact ⟨.c256, h256.symm⟩

/-- Complete fixed-menu action index.  The `Nonempty` proof records only that
the representative realizes a pair system; it does not add frames to the
counted index. -/
abbrev ActionIndex :=
  Σ d : PairCountLabel,
    {i : Non2TransitiveActionClass (Fin d.sourceDegree) //
      Nonempty (BinaryPairFrame i.representative (Fin d.pairCount))}

instance actionIndexFintype : Fintype ActionIndex := Fintype.ofFinite _

def pairCount (i : ActionIndex) : ℕ := i.1.pairCount

def sourceAction (i : ActionIndex) :
    Subgroup (Equiv.Perm (Fin (2 * pairCount i))) :=
  i.2.1.representative

def chosenFrame (i : ActionIndex) :
    BinaryPairFrame (sourceAction i) (Fin (pairCount i)) :=
  Classical.choice i.2.2

instance sourceActionPretransitive (i : ActionIndex) :
    MulAction.IsPretransitive (sourceAction i) (Fin (2 * pairCount i)) := by
  change MulAction.IsPretransitive i.2.1.representative
    (Fin i.1.sourceDegree)
  infer_instance

instance chosenTopPretransitive (i : ActionIndex) :
    MulAction.IsPretransitive (chosenFrame i).top.range
      (Fin (pairCount i)) :=
  (chosenFrame i).top_pretransitive

theorem sourceAction_not_isPGroup (i : ActionIndex) :
    ¬ IsPGroup 2 (sourceAction i) := by
  change ¬ IsPGroup 2 i.2.1.representative
  exact i.2.1.representative_not_isPGroup

theorem chosenTop_not_isPGroup (i : ActionIndex) :
    ¬ IsPGroup 2 (chosenFrame i).top.range :=
  (chosenFrame i).top_not_isPGroup (sourceAction_not_isPGroup i)

/-- Every literal nonbinary transitive pair action at one of the eight pair
counts enters one fixed-menu action class.  Relabelling moves the actual
frame to the representative, but only its existence is retained in the
index. -/
theorem exists_actionEntry_of_pairFrame
    (d : PairCountLabel)
    (U : Subgroup (Equiv.Perm (Fin d.sourceDegree)))
    (hU : ¬ IsPGroup 2 U)
    (htrans : MulAction.IsPretransitive U (Fin d.sourceDegree))
    (F : BinaryPairFrame U (Fin d.pairCount)) :
    ∃ j : {i : Non2TransitiveActionClass (Fin d.sourceDegree) //
        Nonempty (BinaryPairFrame i.representative (Fin d.pairCount))},
      ∃ c : Equiv.Perm (Fin d.sourceDegree),
        relabelSubgroup c U = j.1.representative := by
  obtain ⟨j, c, hc⟩ := Non2TransitiveActionClass.representative_cover
    U hU htrans
  have hc' : relabelSubgroup c U = j.representative := by
    calc
      relabelSubgroup c U = MulAut.conj c • U := by
        change U.map c.permCongrHom.toMonoidHom = _
        rw [Subgroup.pointwise_smul_def]
        congr 1
      _ = j.representative := hc
  let F' : BinaryPairFrame j.representative (Fin d.pairCount) :=
    hc' ▸ F.relabelPoints c
  exact ⟨⟨j, ⟨F'⟩⟩, c, hc'⟩

end SymmetricSubgroupAsymptotics.Non2UnipotentPrefixFiniteMenu

end
