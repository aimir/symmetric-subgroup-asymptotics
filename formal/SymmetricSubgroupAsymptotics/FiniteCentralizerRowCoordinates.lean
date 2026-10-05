import SymmetricSubgroupAsymptotics.FiniteConjugacyCentralizerCoordinates
import SymmetricSubgroupAsymptotics.FiniteCayleyGroup

/-!
# Row-list coordinates for selected centralizers

The selected emitter lists the literal finite-row indices in the kernel of a
restricted block top and one preimage for every top-image row.  The local
membership, injectivity and completeness tests are finite propositions.  This
file turns those checked lists into the reversible charts required by
`FinitePairCentralizerCoordinateCertificate`.
-/

set_option autoImplicit false
noncomputable section

namespace SymmetricSubgroupAsymptotics

variable {n k t w : ℕ} [Group (FiniteGroupRow n)]

/-- The block top restricted to the literal centralizer of one selected row. -/
def finiteRowCentralizerTop
    (top : FiniteGroupRow n →* Equiv.Perm (Fin w))
    (representative : FiniteGroupRow n) :
    Subgroup.centralizer ({representative} : Set (FiniteGroupRow n)) →*
      Equiv.Perm (Fin w) :=
  top.comp (Subgroup.centralizer
    ({representative} : Set (FiniteGroupRow n))).subtype

/-- Proof-carrying kernel rows and top-image preimages for one selected
centralizer. -/
structure FiniteCentralizerRowCoordinates
    (top : FiniteGroupRow n →* Equiv.Perm (Fin w))
    (representative : FiniteGroupRow n) (k t : ℕ) where
  kernelRows : Fin k → Fin n
  kernel_centralizes : ∀ j,
    (⟨kernelRows j⟩ : FiniteGroupRow n) ∈
      Subgroup.centralizer ({representative} : Set (FiniteGroupRow n))
  kernel_mem : ∀ j, top ⟨kernelRows j⟩ = 1
  kernelRows_injective : Function.Injective kernelRows
  kernel_complete : ∀ i,
    (⟨i⟩ : FiniteGroupRow n) ∈
        Subgroup.centralizer ({representative} : Set (FiniteGroupRow n)) →
      top ⟨i⟩ = 1 → ∃ j, kernelRows j = i
  topRows : Fin t → Fin n
  top_centralizes : ∀ j,
    (⟨topRows j⟩ : FiniteGroupRow n) ∈
      Subgroup.centralizer ({representative} : Set (FiniteGroupRow n))
  topImages_injective :
    Function.Injective (fun j => top (⟨topRows j⟩ : FiniteGroupRow n))
  top_complete : ∀ i,
    (⟨i⟩ : FiniteGroupRow n) ∈
        Subgroup.centralizer ({representative} : Set (FiniteGroupRow n)) →
      ∃ j, top ⟨i⟩ = top ⟨topRows j⟩

namespace FiniteCentralizerRowCoordinates

variable {top : FiniteGroupRow n →* Equiv.Perm (Fin w)}
    {representative : FiniteGroupRow n}
    (D : FiniteCentralizerRowCoordinates top representative k t)

include D

private def kernelElement (j : Fin k) :
    (finiteRowCentralizerTop top representative).ker :=
  ⟨⟨⟨D.kernelRows j⟩, D.kernel_centralizes j⟩, D.kernel_mem j⟩

private theorem kernelElement_injective :
    Function.Injective D.kernelElement := by
  intro i j hij
  apply D.kernelRows_injective
  exact congrArg (fun x => x.val.val.index) hij

private theorem kernelElement_surjective :
    Function.Surjective D.kernelElement := by
  rintro ⟨⟨⟨i⟩, hiCentral⟩, hiKernel⟩
  obtain ⟨j, hj⟩ := D.kernel_complete i hiCentral hiKernel
  refine ⟨j, ?_⟩
  apply Subtype.ext
  apply Subtype.ext
  exact FiniteGroupRow.ext hj

/-- Reversible chart of the literal restricted-top kernel by the emitted row
list. -/
noncomputable def kernelChart :
    (finiteRowCentralizerTop top representative).ker ≃ Fin k :=
  (Equiv.ofBijective D.kernelElement
    ⟨D.kernelElement_injective, D.kernelElement_surjective⟩).symm

private def topElement (j : Fin t) :
    (finiteRowCentralizerTop top representative).range :=
  ⟨top ⟨D.topRows j⟩,
    ⟨⟨⟨D.topRows j⟩, D.top_centralizes j⟩, rfl⟩⟩

private theorem topElement_injective : Function.Injective D.topElement := by
  intro i j hij
  apply D.topImages_injective
  exact congrArg Subtype.val hij

private theorem topElement_surjective : Function.Surjective D.topElement := by
  rintro ⟨y, ⟨⟨⟨i⟩, hiCentral⟩, rfl⟩⟩
  obtain ⟨j, hj⟩ := D.top_complete i hiCentral
  refine ⟨j, ?_⟩
  exact Subtype.ext hj.symm

/-- Reversible chart of the literal restricted-top range by the emitted
preimage row list. -/
noncomputable def topChart :
    (finiteRowCentralizerTop top representative).range ≃ Fin t :=
  (Equiv.ofBijective D.topElement
    ⟨D.topElement_injective, D.topElement_surjective⟩).symm

/-- Package the checked row lists as the coordinate certificate consumed by
the class-cardinality cover. -/
noncomputable def toCoordinateCertificate
    (claimedCard : ℕ) (product_card : k * t = claimedCard) :
    FinitePairCentralizerCoordinateCertificate
      (Subgroup.centralizer
        ({representative} : Set (FiniteGroupRow n))) w where
  top := finiteRowCentralizerTop top representative
  kernelCard := k
  topCard := t
  claimedCard := claimedCard
  kernelChart := D.kernelChart
  topChart := D.topChart
  product_card := product_card

end FiniteCentralizerRowCoordinates

end SymmetricSubgroupAsymptotics

end
