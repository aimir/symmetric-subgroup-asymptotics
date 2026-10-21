import SymmetricSubgroupAsymptotics.BinaryBooleanFourRepresentationLeadingMiddle
import SymmetricSubgroupAsymptotics.BinaryBooleanFourKernelLeadingClosure
import SymmetricSubgroupAsymptotics.FiniteRowLeadingDimension

/-! Head six supplies all six quadratic leading coordinates and their
five smaller supports. Eleven independent ACTUAL vectors follow; lower
terms are retained throughout. No equality with a homogeneous ideal is
assumed or required. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
open scoped Classical
namespace SymmetricSubgroupAsymptotics
open BinaryBooleanFourPolynomialCoordinates BinaryElementaryPairMonomialWidth

variable {G V₀ : Type} [Group G] [AddCommGroup V₀] [Module (ZMod 2) V₀]
    [FiniteDimensional (ZMod 2) V₀]

theorem boolean_four_representation_finrank_ge_eleven_of_head_six
    (rho : Representation (ZMod 2) G V₀) (C : V₀ →ₗ[ZMod 2] V)
    (hC : Function.Injective C)
    (hderivative : ∀ i : Fin 4, ∃ g : G, ∀ v : V₀,
      C (rho g v - v) = derivative i (C v))
    (hhead : 6 ≤ Module.finrank (ZMod 2)
      (rho.IntertwiningMap (Representation.trivial (ZMod 2) G (ZMod 2)))) :
    11 ≤ Module.finrank (ZMod 2) V₀ := by
  obtain ⟨S, label, hspan, hleading, hinj⟩ :=
    boolean_four_representation_generators_quadratic_leading rho C hC hderivative (by omega)
  let Q := S.image label
  have hQ : ∀ a ∈ Q, (support a).card = 2 := by
    intro a ha
    obtain ⟨v, hv, rfl⟩ := Finset.mem_image.mp ha
    exact (hleading v hv).2
  have hQcard : 6 ≤ Q.card := by
    have hS : 6 ≤ S.card := by
      obtain ⟨v, hv⟩ := ModuleGeneratedBy.of_finset_card_le S hspan S.card le_rfl
      exact hhead.trans (representationHead_finrank_le_generators rho v hv)
    rwa [Finset.card_image_of_injOn hinj]
  have hQsub : Q ⊆ quadraticMasks := fun a ha => (mem_quadraticMasks_iff a).mpr (hQ a ha)
  have hquadraticCard : quadraticMasks.card = 6 := by decide
  have hQeq : Q = quadraticMasks := Finset.eq_of_subset_of_card_le hQsub (by
    rw [hquadraticCard]
    exact hQcard)
  let K : Submodule (ZMod 2) V := C.range
  have hstable : ∀ i : Fin 4, ∀ a ∈ K, derivative i a ∈ K := by
    intro i a ha
    obtain ⟨v, rfl⟩ := ha
    obtain ⟨g, hg⟩ := hderivative i
    exact ⟨rho g v - v, hg v⟩
  have hactualQ : ∀ a ∈ Q, ∃ f ∈ K, FiniteRowLeadingWeight.HasLeading f a := by
    intro a ha
    obtain ⟨v, hv, rfl⟩ := Finset.mem_image.mp ha
    exact ⟨C (rho.asModuleEquiv v), ⟨rho.asModuleEquiv v, rfl⟩, (hleading v hv).1⟩
  have hactual : ∀ a : Fin 16, (support a).card ≤ 2 →
      ∃ v : V₀, FiniteRowLeadingWeight.HasLeading (C v) a := by
    intro a ha
    have hex : ∃ f ∈ K, FiniteRowLeadingWeight.HasLeading f a := by
      by_cases hsmall : (support a).card ≤ 1
      · exact five_quadratic_leading_vectors_give_small_supports K hstable Q hQ (by omega)
          hactualQ a hsmall
      · apply hactualQ a
        rw [hQeq]
        exact (mem_quadraticMasks_iff a).mpr (by omega)
    obtain ⟨f, ⟨v, hv⟩, hf⟩ := hex
    exact ⟨v, hv.symm ▸ hf⟩
  let low : Finset (Fin 16) := Finset.univ.filter (fun a => (support a).card ≤ 2)
  have hlow : low.card = 11 := by decide +kernel
  have hb := FiniteRowLeadingWeight.card_le_finrank_of_actual_leading_vectors low C
    (fun a ha => hactual a (Finset.mem_filter.mp ha).2)
  rw [hlow] at hb
  exact hb

end SymmetricSubgroupAsymptotics
