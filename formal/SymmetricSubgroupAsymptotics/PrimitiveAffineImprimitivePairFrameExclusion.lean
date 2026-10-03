import SymmetricSubgroupAsymptotics.Non2PreE7NonPairPhysicalFrontier
import SymmetricSubgroupAsymptotics.OriginalMinimalBlock
import SymmetricSubgroupAsymptotics.TransitiveBinaryPairFrame

/-!
# Two-point minimal blocks give literal pair frames

An original minimal block whose base fibre has two points supplies a binary
pair frame on the original ambient action.  The pair labels are the actual
block set, and the top is the literal action on that set.  Relabelling only
the pair labels then contradicts the negative frame field of the pre-`E7`
action index at each of its selected or residual pair widths.

The conclusion is deliberately width-sensitive.  `PreE7ActionClass`
excludes the eight selected pair counts, and `PreE7NonPairActionClass` adds
only the four residual counts.  Neither subtype rules out a two-point block
at any other number of blocks.
-/

set_option autoImplicit false
noncomputable section
open scoped Classical

namespace SymmetricSubgroupAsymptotics

namespace OriginalMinimalBlock

variable {A Ω : Type} [Group A] [Finite Ω]
  [MulAction A Ω] [MulAction.IsPretransitive A Ω]
  {ω₀ : Ω} (D : OriginalMinimalBlock (A := A) ω₀)

/-- Transport from the selected base fibre to every other literal fibre of
the same original block system. -/
def baseFibreEquiv (i : D.Points) :
    D.Fibre ≃ originalBlockFibre D.map i := by
  let a : A := Classical.choose
    (MulAction.exists_smul_eq A D.base i)
  have ha : a • D.base = i := Classical.choose_spec
    (MulAction.exists_smul_eq A D.base i)
  exact
    { toFun := fun x => ⟨a • x.1, by
          rw [D.map_equivariant, x.2, ha]⟩
      invFun := fun x => ⟨a⁻¹ • x.1, by
          rw [D.map_equivariant, x.2, ← ha, inv_smul_smul]⟩
      left_inv := fun x => Subtype.ext (inv_smul_smul a x.1)
      right_inv := fun x => Subtype.ext (smul_inv_smul a x.1) }

/-- Every literal fibre has the cardinality of the selected base fibre. -/
theorem fibre_card_eq_base (i : D.Points) :
    Nat.card (originalBlockFibre D.map i) = Nat.card D.Fibre :=
  (Nat.card_congr (baseFibreEquiv D i)).symm

/-- A two-point original minimal block is already a physical binary pair
frame on the ambient action.  No enlargement to the full flip product is
made. -/
def pairFrameOfFibreCardTwo
    (A : Subgroup (Equiv.Perm Ω))
    [MulAction.IsPretransitive A Ω]
    (D : OriginalMinimalBlock (A := A) ω₀)
    (hFibre : Nat.card D.Fibre = 2) :
    BinaryPairFrame A D.Points :=
  binaryPairFrameOfFibreCardTwo A D.topMap D.map D.map_equivariant
    (fun i => (fibre_card_eq_base D i).trans hFibre)

end OriginalMinimalBlock

namespace Non2UnipotentPrefixFiniteMenu

variable {w : ℕ} (U : PreE7NonPairActionClass w)
  {basePoint : Fin w}
  (block : OriginalMinimalBlock
    (A := preE7NonPairAction w U) basePoint)

local instance : MulAction.IsPretransitive
    (preE7NonPairAction w U) (Fin w) :=
  Non2TransitiveActionClass.representative_pretransitive U.1.1

/-- Relabel the actual block set of a two-point minimal block by its finite
cardinality. -/
def residualPairFrameOfFibreCardTwo
    (d : PreE7ResidualPairCountLabel)
    (hFibre : Nat.card block.Fibre = 2)
    (hPoints : Nat.card block.Points = d.pairCount) :
    BinaryPairFrame (preE7NonPairAction w U) (Fin d.pairCount) :=
  (OriginalMinimalBlock.pairFrameOfFibreCardTwo
      (A := preE7NonPairAction w U) block hFibre).reindex
    (Finite.equivFinOfCardEq hPoints)

/-- At one of the four residual pair widths, the extra non-pair field rules
out a two-point minimal block. -/
theorem fibre_card_ne_two_of_residualPairWidth
    (d : PreE7ResidualPairCountLabel)
    (hwidth : 2 * d.pairCount = w) :
    Nat.card block.Fibre ≠ 2 := by
  intro hFibre
  have hproduct := block.degree_product
  have hPoints : Nat.card block.Points = d.pairCount := by
    rw [hFibre, Nat.card_fin] at hproduct
    omega
  exact U.2 d hwidth
    ⟨residualPairFrameOfFibreCardTwo U block d hFibre hPoints⟩

/-- The underlying pre-`E7` action field gives the analogous exclusion at
the eight selected pair widths. -/
theorem fibre_card_ne_two_of_selectedPairWidth
    (d : PairCountLabel)
    (hwidth : d.sourceDegree = w) :
    Nat.card block.Fibre ≠ 2 := by
  intro hFibre
  have hproduct := block.degree_product
  have hPoints : Nat.card block.Points = d.pairCount := by
    rw [hFibre, Nat.card_fin] at hproduct
    unfold PairCountLabel.sourceDegree at hwidth
    omega
  let F : BinaryPairFrame (preE7NonPairAction w U) (Fin d.pairCount) :=
    (OriginalMinimalBlock.pairFrameOfFibreCardTwo
      (A := preE7NonPairAction w U) block hFibre).reindex
      (Finite.equivFinOfCardEq hPoints)
  exact U.1.2 d hwidth ⟨F⟩

end Non2UnipotentPrefixFiniteMenu
end SymmetricSubgroupAsymptotics

end
