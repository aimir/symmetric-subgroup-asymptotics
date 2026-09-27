import SymmetricSubgroupAsymptotics.BinaryOriginalMenuEntries
import SymmetricSubgroupAsymptotics.SchurRepresentation
import SymmetricSubgroupAsymptotics.FusionWideDirectRow

/-!
# A direct row on actual accepted binary menu entries

The index consists of original action classes, distinct original pairings,
literal normals and central cuts. Acceptance tests the actual cut parameters.
The original weighted mass is proved by inclusion in the complete menu.

This constructs and bounds the row. It does not assert that every original
axis has an accepted cut, prove a local epimorphism envelope, or supply a
physical cover of an unmarked subgroup family. Those are separate inputs
to physical installation, not consequences of the mass estimate.
-/

set_option autoImplicit false
noncomputable section
open Filter
open scoped BigOperators Classical

namespace SymmetricSubgroupAsymptotics

local instance wideOriginalNormal {G : Type*} [Group G]
    (N : {N : Subgroup G // N.Normal}) : N.1.Normal := N.2

namespace BinaryOriginalMenuEntry

variable {X : Type} {k : ℕ}

/-- Dimension of the literal central cut, not a supplied cut label. -/
def cutDimension (j : BinaryOriginalMenuEntry k X) : ℕ :=
  Module.finrank (ZMod 2) ↥(j.2.2.2.1)

/-- Half of the same-source marker: half the original pair degree plus
the dimension of the actual central cut. It is used only when k≥11. -/
def markerHalf (j : BinaryOriginalMenuEntry k X) : ℕ :=
  2^(k-1) + j.cutDimension

theorem two_mul_markerHalf (j : BinaryOriginalMenuEntry k X) (hk : 1 ≤ k) :
    2*j.markerHalf = 2^k + 2*j.cutDimension := by
  have hp : 2*2^(k-1) = 2^k := by
    rw [← Nat.mul_comm (2^(k-1)) 2, ← pow_succ, Nat.sub_add_cancel hk]
  dsimp only [markerHalf]
  rw [Nat.mul_add, hp]

/-- Schur capacity of the exact original cut representation. -/
def capacity (j : BinaryOriginalMenuEntry k X) : ℝ :=
  representationSchurCapacity
    (j.2.1.chosenFrame.cutRepresentation j.2.2.1.1 j.2.2.2.1 j.2.2.2.2)

/-- The literal direct-row gap, with its original width and actual cut. -/
def directGap (h : ℕ) (j : BinaryOriginalMenuEntry k X) : ℝ :=
  (2*(h : ℝ) - 2*(j.markerHalf : ℝ) - 4*j.capacity)/16

end BinaryOriginalMenuEntry

/-- Acceptance is a property of the original entry. Non-power widths
have no entries. The threshold leaves the small finite widths separate. -/
def BinaryOriginalWideAccepted (h : ℕ)
    (j : BinaryOriginalMenuEntry (Nat.log 2 h) (Fin (2*h))) : Prop :=
  h = 2^(Nat.log 2 h) ∧ 11 ≤ Nat.log 2 h ∧
    16*j.markerHalf ≤ 13*h ∧ ((2*h : ℕ) : ℝ)/32 ≤ 16*j.directGap h

/-- A subtype of the complete original menu, so labels cannot repeat. -/
abbrev BinaryOriginalWideEntry (h : ℕ) :=
  {j : BinaryOriginalMenuEntry (Nat.log 2 h) (Fin (2*h)) //
    BinaryOriginalWideAccepted h j}

namespace BinaryOriginalWideEntry

def markerHalf (h : ℕ) (j : BinaryOriginalWideEntry h) : ℕ := j.1.markerHalf
def cost (h : ℕ) (j : BinaryOriginalWideEntry h) : ℝ := j.1.cost
def divisor (h : ℕ) (j : BinaryOriginalWideEntry h) : ℝ := j.1.divisor
def gap (h : ℕ) (j : BinaryOriginalWideEntry h) : ℝ := j.1.directGap h

theorem cost_nonneg (h : ℕ) (j : BinaryOriginalWideEntry h) : 0 ≤ cost h j :=
  j.1.cost_nonneg

theorem divisor_pos (h : ℕ) (j : BinaryOriginalWideEntry h) : 0 < divisor h j :=
  j.1.divisor_pos

theorem prefix_le (h : ℕ) (j : BinaryOriginalWideEntry h) :
    16*markerHalf h j ≤ 13*h := j.2.2.2.1

theorem gap_le (h : ℕ) (j : BinaryOriginalWideEntry h) :
    ((2*h : ℕ) : ℝ)/32 ≤ 16*gap h j := j.2.2.2.2

/-- The row target uses the actual pair-degree-plus-cut marker. -/
theorem prefix_eq (h : ℕ) (j : BinaryOriginalWideEntry h) :
    2*markerHalf h j = h + 2*j.1.cutDimension := by
  have hk : 1 ≤ Nat.log 2 h := (show 1 ≤ 11 by decide).trans j.2.2.1
  exact (j.1.two_mul_markerHalf hk).trans
    (congrArg (fun t : ℕ => t + 2*j.1.cutDimension) j.2.1.symm)

/-- The full actual weighted-menu theorem supplies the aggregate mass
internally. No bound on the number of selected labels is substituted. -/
theorem uniform_mass_le :
    ∃ H : ℝ, 0 ≤ H ∧ ∀ h : ℕ,
      (∑ j : BinaryOriginalWideEntry h, cost h j/divisor h j) ≤
        (2 : ℝ)^((h : ℝ)^2/32+H) := by
  obtain ⟨H,hH,hbound⟩ := BinaryOriginalMenuEntry.uniform_subfamily_mass_le
  refine ⟨H,hH,?_⟩
  intro h
  by_cases hp : h = 2^(Nat.log 2 h)
  · have hn : 2^(Nat.log 2 h+1) = 2*h := by
      rw [pow_succ]
      omega
    have hdegree : Nat.card (Fin (2*h)) = 2^(Nat.log 2 h+1) := by
      rw [Nat.card_fin]
      exact hn.symm
    have hb := hbound (Nat.log 2 h) hdegree (BinaryOriginalWideAccepted h)
    have hreal : (2 : ℝ)^(Nat.log 2 h+1) = 2*(h : ℝ) := by exact_mod_cast hn
    have hexp : (2*(h : ℝ))^2/128+H = (h : ℝ)^2/32+H := by ring
    simpa only [cost, divisor, hreal, hexp] using hb
  · letI : IsEmpty (BinaryOriginalWideEntry h) := ⟨fun j => hp j.2.1⟩
    simp only [Finset.univ_eq_empty, Finset.sum_empty]
    positivity

end BinaryOriginalWideEntry

/-- The actual accepted-entry row, with every duplicate target retained
as a separate original action/pair/normal/cut summand. -/
def binaryOriginalWideRow (n m : ℕ) : ℝ :=
  fusionWideDirectRow BinaryOriginalWideEntry.markerHalf BinaryOriginalWideEntry.cost
    BinaryOriginalWideEntry.divisor BinaryOriginalWideEntry.gap n m

theorem binaryOriginalWideRow_nonneg (n m : ℕ) : 0 ≤ binaryOriginalWideRow n m :=
  fusionWideDirectRow_nonneg BinaryOriginalWideEntry.markerHalf BinaryOriginalWideEntry.cost
    BinaryOriginalWideEntry.divisor BinaryOriginalWideEntry.gap BinaryOriginalWideEntry.cost_nonneg
    BinaryOriginalWideEntry.divisor_pos n m

theorem binaryOriginalWideRow_forward {n m : ℕ} (hnm : n ≤ m) :
    binaryOriginalWideRow n m = 0 :=
  fusionWideDirectRow_forward BinaryOriginalWideEntry.markerHalf BinaryOriginalWideEntry.cost
    BinaryOriginalWideEntry.divisor BinaryOriginalWideEntry.gap BinaryOriginalWideEntry.prefix_le hnm

/-- The complete original weighted row decays before any bound on the
unknown subgroup-count sequence. There is no menu-mass hypothesis. -/
theorem binaryOriginalWideRow_decay :
    ∃ C : ℝ, 0 < C ∧ ∀ᶠ n : ℕ in atTop,
      (∑ m ∈ Finset.range n, binaryOriginalWideRow n m) ≤
        C*(2 : ℝ)^(-(n : ℝ)/16) := by
  obtain ⟨H,_hH,hmass⟩ := BinaryOriginalWideEntry.uniform_mass_le
  exact fusionWideDirectRow_decay BinaryOriginalWideEntry.markerHalf BinaryOriginalWideEntry.cost
    BinaryOriginalWideEntry.divisor BinaryOriginalWideEntry.gap H BinaryOriginalWideEntry.cost_nonneg
    BinaryOriginalWideEntry.divisor_pos BinaryOriginalWideEntry.prefix_le
    BinaryOriginalWideEntry.gap_le (fun h _ => hmass h)

/-- Eventual contraction of this same actual row is independent of a
physical-cover theorem or any coarse subgroup-growth input. -/
theorem binaryOriginalWideRow_contractive :
    ∀ᶠ n : ℕ in atTop,
      (∑ m ∈ Finset.range n, binaryOriginalWideRow n m) ≤ 1/2 := by
  obtain ⟨H,_hH,hmass⟩ := BinaryOriginalWideEntry.uniform_mass_le
  exact fusionWideDirectRow_contractive BinaryOriginalWideEntry.markerHalf BinaryOriginalWideEntry.cost
    BinaryOriginalWideEntry.divisor BinaryOriginalWideEntry.gap H BinaryOriginalWideEntry.cost_nonneg
    BinaryOriginalWideEntry.divisor_pos BinaryOriginalWideEntry.prefix_le
    BinaryOriginalWideEntry.gap_le (fun h _ => hmass h)

end SymmetricSubgroupAsymptotics

end
