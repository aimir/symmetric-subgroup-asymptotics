import SymmetricSubgroupAsymptotics.FiniteConjugacyCentralizerCard
import Mathlib.GroupTheory.Index

/-!
# Proof-carrying centralizer chunks

For a selected six-pair action, the emitter restricts the literal block
projection to each selected centralizer.  Exact kernel and image cardinalities
then prove the centralizer order.  Together with pairwise class separation and
one small arithmetic sum, these chunks produce the complete sparse conjugacy
cover used by the normal-state registry.
-/

set_option autoImplicit false
noncomputable section
open scoped BigOperators Classical

namespace SymmetricSubgroupAsymptotics

variable {G : Type*} [Group G] [Finite G] {c w : ℕ}

/-- Exact centralizer cardinality obtained from a literal finite-coordinate
homomorphism.  For the degree-twelve witnesses, `top` is the restriction of
the six-block action; its kernel is checked in sparse binary coordinates. -/
structure FinitePairCentralizerCardCertificate
    (C : Subgroup G) (w : ℕ) where
  top : C →* Equiv.Perm (Fin w)
  kernelCard : ℕ
  topCard : ℕ
  claimedCard : ℕ
  kernel_card : Nat.card top.ker = kernelCard
  top_card : Nat.card top.range = topCard
  product_card : kernelCard * topCard = claimedCard

namespace FinitePairCentralizerCardCertificate

variable {C : Subgroup G}
    (D : FinitePairCentralizerCardCertificate C w)

include D

/-- The coordinate checks determine the literal centralizer order. -/
theorem card_eq : Nat.card C = D.claimedCard := by
  have h := D.top.ker.card_mul_index
  rw [Subgroup.index_ker, D.kernel_card, D.top_card] at h
  exact h.symm.trans D.product_card

end FinitePairCentralizerCardCertificate

/-- One selected-action conjugacy chunk.  The producer supplies no coverage
claim: exact centralizer orders and the checked numerical sum prove coverage
through `FiniteConjugacyCardinalCover.ofCentralizerSum`. -/
structure FiniteConjugacyCentralizerChunk
    (representative : Fin c → G) (w : ℕ) where
  separated : ∀ i j,
    IsConj (representative i) (representative j) → i = j
  centralizer : ∀ i,
    FinitePairCentralizerCardCertificate
      (Subgroup.centralizer ({representative i} : Set G)) w
  claimed_class_sum :
    (∑ i : Fin c, Nat.card G / (centralizer i).claimedCard) = Nat.card G

namespace FiniteConjugacyCentralizerChunk

variable {representative : Fin c → G}
    (D : FiniteConjugacyCentralizerChunk representative w)

include D

/-- Assemble the exact sparse conjugacy cover consumed by the normal-join
registry. -/
noncomputable def toCardinalCover :
    FiniteConjugacyCardinalCover representative := by
  apply FiniteConjugacyCardinalCover.ofCentralizerSum representative D.separated
  calc
    (∑ i : Fin c,
        Nat.card G /
          Nat.card (Subgroup.centralizer
            ({representative i} : Set G))) =
        ∑ i : Fin c, Nat.card G / (D.centralizer i).claimedCard := by
      apply Finset.sum_congr rfl
      intro i _
      rw [(D.centralizer i).card_eq]
    _ = Nat.card G := D.claimed_class_sum

end FiniteConjugacyCentralizerChunk

end SymmetricSubgroupAsymptotics

end
