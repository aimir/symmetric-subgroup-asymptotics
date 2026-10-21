import SymmetricSubgroupAsymptotics.BinaryCoupledHeadCertificate

/-! Sparse coordinate certificates for the lower denominator in an actual
pair-module head filtration. Displayed radical vectors are already bound
to the same intrinsic coinvariant radical; product vectors use the same
actual kernel and pair-sum state. -/
set_option autoImplicit false
noncomputable section
open scoped BigOperators
namespace SymmetricSubgroupAsymptotics

structure BinaryPairLayerDenominatorCertificate
    {G : Type} [Group G] {w a b r d : ℕ}
    (rho : Representation (ZMod 2) G (Fin w → ZMod 2))
    (L : Subrepresentation rho)
    (K : BinaryCoordinateSpace w a) (S : BinaryCoordinateSpace w b)
    (R : BinaryCoordinateSpace w r) (D : BinaryCoordinateSpace w d) where
  space_le_state : D.space ≤ L.toSubmodule
  radicalCoefficient : Fin d → Fin r → ZMod 2
  productCoefficient : Fin d → Fin a → Fin b → ZMod 2
  basis_eq : ∀ j, D.inclusion (Pi.single j 1) =
    (∑ i, radicalCoefficient j i • R.inclusion (Pi.single i 1)) +
      ∑ i, ∑ k, productCoefficient j i k •
        (K.inclusion (Pi.single i 1) * S.inclusion (Pi.single k 1))

namespace BinaryPairLayerDenominatorCertificate

variable {G : Type} [Group G] {w a b r d : ℕ}
  {rho : Representation (ZMod 2) G (Fin w → ZMod 2)}
  {L : Subrepresentation rho}
  {K : BinaryCoordinateSpace w a} {S : BinaryCoordinateSpace w b}
  {R : BinaryCoordinateSpace w r} {D : BinaryCoordinateSpace w d}
  (C : BinaryPairLayerDenominatorCertificate rho L K S R D)

include C

theorem submoduleOf_le_product_radical
    (hproduct : binaryCoordinateProductSpan K.space S.space ≤ L.toSubmodule)
    (hR : R.space = (Representation.Coinvariants.ker L.toRepresentation).map
      L.toSubmodule.subtype) :
    D.submoduleOf L.toSubmodule C.space_le_state ≤
      (binaryCoordinateProductSpan K.space S.space).comap L.toSubmodule.subtype ⊔
        Representation.Coinvariants.ker L.toRepresentation := by
  apply D.submoduleOf_le_of_basis_mem L.toSubmodule C.space_le_state
  intro j
  have hrad (i : Fin r) : R.inclusion (Pi.single i 1) ∈ L.toSubmodule := by
    have hm : R.inclusion (Pi.single i 1) ∈
        (Representation.Coinvariants.ker L.toRepresentation).map L.toSubmodule.subtype := by
      rw [← hR]
      exact ⟨Pi.single i 1, rfl⟩
    obtain ⟨v, _, he⟩ := hm
    rw [← he]
    exact v.property
  have hprod (i : Fin a) (k : Fin b) :
      K.inclusion (Pi.single i 1) * S.inclusion (Pi.single k 1) ∈ L.toSubmodule :=
    hproduct (binaryCoordinateProductSpan.product_mem K.space S.space
      _ ⟨_, rfl⟩ _ ⟨_, rfl⟩)
  have he : (⟨D.inclusion (Pi.single j 1), C.space_le_state ⟨_, rfl⟩⟩ : L.toSubmodule) =
      (∑ i, C.radicalCoefficient j i •
        (⟨R.inclusion (Pi.single i 1), hrad i⟩ : L.toSubmodule)) +
      ∑ i, ∑ k, C.productCoefficient j i k •
        (⟨K.inclusion (Pi.single i 1) * S.inclusion (Pi.single k 1), hprod i k⟩ :
          L.toSubmodule) := by
    apply Subtype.ext
    simpa only [Submodule.coe_add, Submodule.coe_sum, Submodule.coe_smul] using C.basis_eq j
  rw [he]
  apply Submodule.add_mem
  · apply Submodule.sum_mem
    intro i _
    apply Submodule.smul_mem
    apply Submodule.mem_sup_right
    have hm : R.inclusion (Pi.single i 1) ∈
        (Representation.Coinvariants.ker L.toRepresentation).map L.toSubmodule.subtype := by
      rw [← hR]
      exact ⟨Pi.single i 1, rfl⟩
    obtain ⟨v, hv, he⟩ := hm
    exact (Subtype.ext he : v = ⟨R.inclusion (Pi.single i 1), hrad i⟩) ▸ hv
  · apply Submodule.sum_mem
    intro i _
    apply Submodule.sum_mem
    intro k _
    apply Submodule.smul_mem
    apply Submodule.mem_sup_left
    exact binaryCoordinateProductSpan.product_mem K.space S.space _ ⟨_, rfl⟩ _ ⟨_, rfl⟩

end BinaryPairLayerDenominatorCertificate
end SymmetricSubgroupAsymptotics
