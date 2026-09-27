import SymmetricSubgroupAsymptotics.BinaryOriginalWideRow
import SymmetricSubgroupAsymptotics.BinaryPairZeroCutFusion

/-!
# Literal zero cuts in the complete original wide menu

Every original normal of every representative and realized pairing has an
accepted zero-cut entry at the proved large-width threshold. Its coefficient,
gap, original quotient and same-source moment are the exact zero-cut ones.
No new action, representation, normalizer or cut-count hypothesis is used.
-/

set_option autoImplicit false
noncomputable section
open scoped BigOperators Classical

namespace SymmetricSubgroupAsymptotics.BinaryOriginalZeroCutEntry

variable (h : ℕ) (i : BinaryTransitiveActionClass (Fin (2*h)))
    (p : RealizedPairing i.representative (Fin (2^(Nat.log 2 h))))
    (N : {N : Subgroup i.representative // N.Normal})

local instance originalNormal : N.1.Normal := N.2

/-- The original class/pairing/normal with the literal zero central cut. -/
def entry : BinaryOriginalMenuEntry (Nat.log 2 h) (Fin (2*h)) :=
  ⟨i,p,N,⟨⊥,bot_le⟩⟩

@[simp] theorem cutDimension_eq_zero : (entry h i p N).cutDimension = 0 := by
  dsimp only [entry, BinaryOriginalMenuEntry.cutDimension]
  exact finrank_bot (ZMod 2) _

theorem prefix_eq (hpower : h = 2^(Nat.log 2 h)) (hlarge : 11 ≤ Nat.log 2 h) :
    2*(entry h i p N).markerHalf = h := by
  have hk : 1 ≤ Nat.log 2 h := (show 1 ≤ 11 by decide).trans hlarge
  rw [(entry h i p N).two_mul_markerHalf hk, cutDimension_eq_zero, mul_zero, add_zero]
  exact hpower.symm

/-- The cost is exactly the original zero-cut module and H¹ coefficient. -/
theorem cost_eq : (entry h i p N).cost = p.chosenFrame.zeroCutLiftConstant N.1 := by
  simp only [entry, BinaryOriginalMenuEntry.cost, BinaryPairFrame.centralCutCost,
    BinaryPairFrame.zeroCutLiftConstant, BinaryPairFrame.zeroCutModule, Nat.cast_mul]
  rfl

theorem capacity_eq : (entry h i p N).capacity = p.chosenFrame.zeroCutCapacity N.1 := rfl

/-- The direct-row gap agrees after the actual width and marker identities. -/
theorem gap_eq (hpower : h = 2^(Nat.log 2 h)) (hlarge : 11 ≤ Nat.log 2 h) :
    (entry h i p N).directGap h = p.chosenFrame.zeroCutGapParameter N.1 := by
  have hprefix : 2*((entry h i p N).markerHalf : ℝ) = (h : ℝ) := by
    exact_mod_cast prefix_eq h i p N hpower hlarge
  have hI : Nat.card (Fin (2^(Nat.log 2 h))) = h := by
    rw [Nat.card_fin]
    exact hpower.symm
  unfold BinaryOriginalMenuEntry.directGap BinaryPairFrame.zeroCutGapParameter
  rw [hprefix, capacity_eq, hI, Nat.card_fin]
  push_cast
  ring

/-- Local acceptance is proved for EVERY original normal, not assumed. -/
theorem accepted (hpower : h = 2^(Nat.log 2 h)) (hlarge : 11 ≤ Nat.log 2 h) :
    BinaryOriginalWideAccepted h (entry h i p N) := by
  have hp := prefix_eq h i p N hpower hlarge
  have hz := p.chosenFrame.zeroCut_wide_parameters N.1 i.representative_isPGroup
    (Nat.log 2 h) hlarge (Nat.card_fin _)
  refine ⟨hpower,hlarge,by omega,?_⟩
  rw [gap_eq h i p N hpower hlarge]
  simpa only [Nat.card_fin] using hz.2.2.2

/-- A concrete member of the previously defined accepted wide index. -/
def acceptedEntry (hpower : h = 2^(Nat.log 2 h)) (hlarge : 11 ≤ Nat.log 2 h) :
    BinaryOriginalWideEntry h :=
  ⟨entry h i p N, accepted h i p N hpower hlarge⟩

/-- The original quotient supplies the exact same-source moment. -/
theorem moment_le (b q : ℕ) (hpower : h = 2^(Nat.log 2 h)) :
    (∑ J : Subgroup (Equiv.Perm (Fin b)),
      p.chosenFrame.zeroCutMomentWeight N.1 J^q) ≤
        (subgroupCount (b+q*h) : ℝ) := by
  have hI : Nat.card (Fin (2^(Nat.log 2 h))) = h := by
    rw [Nat.card_fin]
    exact hpower.symm
  simpa only [hI] using p.chosenFrame.zeroCutMomentWeight_moment_le N.1 b q

/-- Arbitrary survival is still evaluated on the original maps to U/N.
The local factor is exactly the one placed in the accepted-entry row. -/
theorem original_survivingEpiCount_le {b : ℕ}
    (hpower : h = 2^(Nat.log 2 h)) (hlarge : 11 ≤ Nat.log 2 h)
    (P : Subgroup (i.representative × Equiv.Perm (Fin b)) → Prop)
    (J : Subgroup (Equiv.Perm (Fin b))) :
    fusionSurvivingEpiCount i.representative P N J ≤
      fusionLocalFactor b h (2*(entry h i p N).markerHalf)
        (entry h i p N).cost ((entry h i p N).directGap h) *
          p.chosenFrame.zeroCutMomentWeight N.1 J := by
  have hI : Nat.card (Fin (2^(Nat.log 2 h))) = h := by
    rw [Nat.card_fin]
    exact hpower.symm
  rw [prefix_eq h i p N hpower hlarge, cost_eq, gap_eq h i p N hpower hlarge]
  simpa only [hI] using p.chosenFrame.zeroCut_original_survivingEpiCount_le N.1 P J

end SymmetricSubgroupAsymptotics.BinaryOriginalZeroCutEntry

end
