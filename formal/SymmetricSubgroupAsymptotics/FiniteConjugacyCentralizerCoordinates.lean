import SymmetricSubgroupAsymptotics.FiniteConjugacyCentralizerChunk
import SymmetricSubgroupAsymptotics.FiniteConjugacyGeneratorInvariant

/-!
# Reversible coordinate charts for selected centralizers

The selected emitter should not state the two cardinalities used by a
centralizer chunk.  It supplies reversible charts for the kernel and the
literal block-top image.  Their sizes and hence the centralizer size are then
theorems.
-/

set_option autoImplicit false
noncomputable section

namespace SymmetricSubgroupAsymptotics

open scoped BigOperators Classical

variable {G : Type*} [Group G] [Finite G] {c w : ℕ}

/-- Reversible finite coordinates on the kernel and image of the restricted
pair-top homomorphism.  In degree twelve the chart sizes are at most `64` and
`720`, respectively. -/
structure FinitePairCentralizerCoordinateCertificate
    (C : Subgroup G) (w : ℕ) where
  top : C →* Equiv.Perm (Fin w)
  kernelCard : ℕ
  topCard : ℕ
  claimedCard : ℕ
  kernelChart : top.ker ≃ Fin kernelCard
  topChart : top.range ≃ Fin topCard
  product_card : kernelCard * topCard = claimedCard

namespace FinitePairCentralizerCoordinateCertificate

variable {C : Subgroup G}
    (D : FinitePairCentralizerCoordinateCertificate C w)

include D

/-- Forget the charts only after they have proved the exact cardinalities
needed by the sparse conjugacy cover. -/
noncomputable def toCardCertificate :
    FinitePairCentralizerCardCertificate C w where
  top := D.top
  kernelCard := D.kernelCard
  topCard := D.topCard
  claimedCard := D.claimedCard
  kernel_card := by
    simpa using Nat.card_congr D.kernelChart
  top_card := by
    simpa using Nat.card_congr D.topChart
  product_card := D.product_card

/-- The literal centralizer order obtained from the reversible charts. -/
theorem card_eq : Nat.card C = D.claimedCard :=
  D.toCardCertificate.card_eq

end FinitePairCentralizerCoordinateCertificate

/-- A whole selected class chunk with reversible coordinates at every
representative. -/
structure FiniteConjugacyCentralizerCoordinateChunk
    (representative : Fin c → G) (w : ℕ) where
  separated : ∀ i j,
    IsConj (representative i) (representative j) → i = j
  centralizer : ∀ i,
    FinitePairCentralizerCoordinateCertificate
      (Subgroup.centralizer ({representative i} : Set G)) w
  claimed_class_sum :
    (∑ i : Fin c, Nat.card G / (centralizer i).claimedCard) = Nat.card G

namespace FiniteConjugacyCentralizerCoordinateChunk

variable {representative : Fin c → G}
    (D : FiniteConjugacyCentralizerCoordinateChunk representative w)

include D

/-- Convert reversible coordinate rows to the cardinal chunk consumed by the
generic conjugacy-cover theorem. -/
noncomputable def toCardChunk :
    FiniteConjugacyCentralizerChunk representative w where
  separated := D.separated
  centralizer i := (D.centralizer i).toCardCertificate
  claimed_class_sum := D.claimed_class_sum

/-- The reversible coordinate chunk proves complete conjugacy coverage. -/
noncomputable def toCardinalCover :
    FiniteConjugacyCardinalCover representative :=
  D.toCardChunk.toCardinalCover

end FiniteConjugacyCentralizerCoordinateChunk

/-- Assemble a coordinate chunk with separation derived from a checked class
code on a full literal generator tuple. -/
noncomputable def finiteConjugacyCentralizerCoordinateChunk_ofInvariant
    {ι : Type*} (ambient : ι → G)
    (representative : Fin c → G)
    (ambient_full : Subgroup.closure (Set.range ambient) = ⊤)
    (I : FiniteConjugacyGeneratorInvariant ambient representative)
    (centralizer : ∀ i,
      FinitePairCentralizerCoordinateCertificate
        (Subgroup.centralizer ({representative i} : Set G)) w)
    (claimed_class_sum :
      (∑ i : Fin c, Nat.card G / (centralizer i).claimedCard) = Nat.card G) :
    FiniteConjugacyCentralizerCoordinateChunk representative w where
  separated := I.separated ambient_full
  centralizer := centralizer
  claimed_class_sum := claimed_class_sum

end SymmetricSubgroupAsymptotics

end
