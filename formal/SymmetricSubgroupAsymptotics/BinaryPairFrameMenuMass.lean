import SymmetricSubgroupAsymptotics.BinaryPairFrameTransport
import SymmetricSubgroupAsymptotics.TransitiveBinaryNormalCount
import SymmetricSubgroupAsymptotics.BinaryPairSectionInvariantBound
import SymmetricSubgroupAsymptotics.BinaryPairSectionCocycleBound
import Mathlib.Data.SetLike.Fintype

/-!
# Complete original normal-and-cut mass for one actual pair frame

Every original normal and every literal central cut is included. Each cost
uses the original pair section, its actual acting quotient and the induced
representation on that cut quotient. The numerical bound is assembled from
proved normal counts, invariant-space bounds and original cocycle counts.
No selected-menu count or mass estimate is a hypothesis.
-/

set_option autoImplicit false
noncomputable section
open scoped BigOperators Classical
attribute [local instance] Fintype.ofFinite

namespace SymmetricSubgroupAsymptotics.BinaryPairFrame

variable {X I : Type} {U : Subgroup (Equiv.Perm X)} (F : BinaryPairFrame U I)

/-- All literal cuts in the invariant space of the original section. -/
abbrev CentralCut (N : Subgroup U) [N.Normal] :=
  {C : Submodule (ZMod 2) (F.kernelSpace ⧸ F.normalSpace N) //
    C ≤ (F.sectionRepresentation N).invariants}

instance centralCut_finite [Finite I] (N : Subgroup U) [N.Normal] :
    Finite (F.CentralCut N) := by
  letI : Finite (F.kernelSpace ⧸ F.normalSpace N) :=
    Finite.of_surjective (F.normalSpace N).mkQ (F.normalSpace N).mkQ_surjective
  unfold CentralCut
  infer_instance

/-- The exact original local coefficient, before any scalar bound. -/
def centralCutCost (N : Subgroup U) [N.Normal] (C : F.CentralCut N) : ℕ :=
  Nat.card ((F.kernelSpace ⧸ F.normalSpace N) ⧸ C.1) *
    Nat.card (groupCohomology.H1 (Rep.of (F.cutRepresentation N C.1 C.2)))

/-- Sum over every original central cut for this literal normal. -/
def normalCentralCutMass [Finite I] (N : Subgroup U) [N.Normal] : ℕ :=
  ∑ C : F.CentralCut N, F.centralCutCost N C

local instance originalNormal (N : {N : Subgroup U // N.Normal}) : N.1.Normal := N.2

/-- Sum over every original normal, with its entire literal cut family. -/
def frameMenuMass [Finite X] [Finite I] : ℕ :=
  ∑ N : {N : Subgroup U // N.Normal}, F.normalCentralCutMass N.1

section Bounds

variable [Finite X] [Finite I] [MulAction.IsPretransitive U X]

/-- The actual top is installed internally; the cost is still the original
quotient cardinal times the cohomology of its original cut action. -/
theorem centralCutCost_le (N : Subgroup U) [N.Normal]
    (k : ℕ) (hU : IsPGroup 2 U) (hI : Nat.card I = 2^k)
    (C : F.CentralCut N) :
    F.centralCutCost N C ≤ 2^((2^k)*(1+binaryCumulativeWidth k)) := by
  letI : MulAction.IsPretransitive F.top.range I := F.top_pretransitive
  exact F.cut_card_mul_firstCohomology_le N hU k hI C.1 C.2

/-- Complete cut sum for one original normal. The cut count and each cost
are proved separately on the same actual section and then multiplied. -/
theorem normalCentralCutMass_le (N : Subgroup U) [N.Normal]
    (k : ℕ) (hU : IsPGroup 2 U) (hI : Nat.card I = 2^k) :
    F.normalCentralCutMass N ≤
      2^(k.choose (k/2)*k.choose (k/2) + (2^k)*(1+binaryCumulativeWidth k)) := by
  letI : MulAction.IsPretransitive F.top.range I := F.top_pretransitive
  have hcuts : Nat.card (F.CentralCut N) ≤ 2^(k.choose (k/2)*k.choose (k/2)) :=
    F.section_centralCuts_card_le_of_top N hU k hI
  calc
    F.normalCentralCutMass N ≤
        ∑ _C : F.CentralCut N, 2^((2^k)*(1+binaryCumulativeWidth k)) :=
      Finset.sum_le_sum (fun C _ => F.centralCutCost_le N k hU hI C)
    _ = Nat.card (F.CentralCut N) * 2^((2^k)*(1+binaryCumulativeWidth k)) := by
      simp only [Finset.sum_const, Finset.card_univ, smul_eq_mul,
        ← Nat.card_eq_fintype_card]
    _ ≤ 2^(k.choose (k/2)*k.choose (k/2)) *
        2^((2^k)*(1+binaryCumulativeWidth k)) := Nat.mul_le_mul_right _ hcuts
    _ = 2^(k.choose (k/2)*k.choose (k/2) +
        (2^k)*(1+binaryCumulativeWidth k)) := (pow_add _ _ _).symm

/-- The complete original normal-and-cut coefficient sum for one actual
frame. No action-class count, frame multiplicity or normalizer change is
included in this fixed-frame theorem. -/
theorem frameMenuMass_le (k : ℕ) (hU : IsPGroup 2 U)
    (hX : Nat.card X = 2^(k+1)) (hI : Nat.card I = 2^k) :
    F.frameMenuMass ≤
      2^((2^(k+1)-1)*binaryCumulativeWidth (k+1) +
        k.choose (k/2)*k.choose (k/2) + (2^k)*(1+binaryCumulativeWidth k)) := by
  have hnormals : Nat.card {N : Subgroup U // N.Normal} ≤
      2^((2^(k+1)-1)*binaryCumulativeWidth (k+1)) :=
    transitiveBinary_normal_count_le_degree (k+1) U hU hX
  calc
    F.frameMenuMass ≤ ∑ _N : {N : Subgroup U // N.Normal},
        2^(k.choose (k/2)*k.choose (k/2) + (2^k)*(1+binaryCumulativeWidth k)) :=
      Finset.sum_le_sum (fun N _ => F.normalCentralCutMass_le N.1 k hU hI)
    _ = Nat.card {N : Subgroup U // N.Normal} *
        2^(k.choose (k/2)*k.choose (k/2) + (2^k)*(1+binaryCumulativeWidth k)) := by
      simp only [Finset.sum_const, Finset.card_univ, smul_eq_mul,
        ← Nat.card_eq_fintype_card]
    _ ≤ 2^((2^(k+1)-1)*binaryCumulativeWidth (k+1)) *
        2^(k.choose (k/2)*k.choose (k/2) + (2^k)*(1+binaryCumulativeWidth k)) :=
      Nat.mul_le_mul_right _ hnormals
    _ = 2^((2^(k+1)-1)*binaryCumulativeWidth (k+1) +
        k.choose (k/2)*k.choose (k/2) + (2^k)*(1+binaryCumulativeWidth k)) := by
      simp only [pow_add, mul_assoc]

/-- The frame degree identity discharges the pair-degree input too. -/
theorem frameMenuMass_le_of_degree (k : ℕ) (hU : IsPGroup 2 U)
    (hX : Nat.card X = 2^(k+1)) :
    F.frameMenuMass ≤
      2^((2^(k+1)-1)*binaryCumulativeWidth (k+1) +
        k.choose (k/2)*k.choose (k/2) + (2^k)*(1+binaryCumulativeWidth k)) := by
  apply F.frameMenuMass_le k hU hX
  have hd := F.card_points
  rw [hX, pow_succ] at hd
  omega

end Bounds
end SymmetricSubgroupAsymptotics.BinaryPairFrame

end
