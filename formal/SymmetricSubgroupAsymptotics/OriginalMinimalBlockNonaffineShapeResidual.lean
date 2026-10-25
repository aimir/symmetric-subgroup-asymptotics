import SymmetricSubgroupAsymptotics.OriginalMinimalBlockAffineAllTopClassBound
import SymmetricSubgroupAsymptotics.OriginalMinimalBlockSimpleComponentClassBound
import SymmetricSubgroupAsymptotics.OriginalMinimalBlockBoundedShapeResidual
import SymmetricSubgroupAsymptotics.PrimitiveSocleRawONanScottProof
import SymmetricSubgroupAsymptotics.CFSGClassificationTransport

/-! The bounded minimal-block frontier retains an actual nonaffine base
component, rather than an unexplained bounded-degree class callback.
The checked primitive dichotomy constructs that component or an actual
affine profile; every affine or simple component of degree at least four
is discharged by the proved original-action installers. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
open scoped Classical
namespace SymmetricSubgroupAsymptotics.OriginalMinimalBlockNonaffineShapeResidual
open PrimitiveSocleRawStructure

variable {A Ω : Type} [Group A] [MulAction A Ω] [MulAction.IsPretransitive A Ω]
    [Finite A] [Finite Ω] [FaithfulSMul A Ω]
    {ω₀ : Ω} (D : OriginalMinimalBlock (A := A) ω₀)

def SmallFibreShape : Prop :=
  (Nat.card D.Fibre = 2 ∨ Nat.card D.Fibre = 3) ∧ Nat.card Ω ≤ 36855

def BoundedNonaffineComponent : Prop :=
  (Nat.card D.Points = 2 ∨ Nat.card D.Points = 3) ∧
    5 ≤ Nat.card D.Fibre ∧ Nat.card D.Fibre ≤ 4095 ∧
      ∃ E : NonaffineData D.Component D.Fibre, ∃ i : CFSG.Index,
        Nonempty (E.Simple ≃* i.Model) ∧
        ((∃ K : Subgroup E.Simple, K ≠ ⊤ ∧ Nat.card D.Fibre = K.index ^ E.factorCount) ∨
          (∃ a : ℕ, E.factorCount ≤ 2 * a ∧ Nat.card D.Fibre = (Nat.card E.Simple) ^ a)) ∧
        ¬ IsSimpleGroup D.Component

theorem bounded_degree_of_nonaffine_component (h : BoundedNonaffineComponent D) :
    Nat.card Ω ≤ 12285 := by
  obtain ⟨hblocks, _, hsize, _⟩ := h
  have htop : Nat.card D.Points ≤ 3 := by omega
  have hprod := D.degree_product
  have hb := Nat.mul_le_mul hsize htop
  omega

theorem class_cube_or_small_fibre_or_nonaffine_component_or_actual_finite_model
    (hCFSG : CFSG.CFSGClassification)
    (hSmaller : ∀ m : ℕ, m < Nat.card Ω → 4 ≤ m →
      ∀ L : Subgroup (Equiv.Perm (Fin m)),
        Nat.card (ConjClasses L) ^ 3 ≤ 5 ^ (m - 1)) :
    Nat.card (ConjClasses A) ^ 3 ≤ 5 ^ (Nat.card Ω - 1) ∨
      SmallFibreShape D ∨ BoundedNonaffineComponent D ∨
        OriginalMinimalBlockBoundedShapeResidual.ActualFiniteModelResidual D := by
  rcases OriginalMinimalBlockBoundedShapeResidual.class_cube_or_bounded_shape_or_actual_finite_model
      D hCFSG hSmaller with hclass | hbounded | hfinite
  · exact Or.inl hclass
  · by_cases hfour : Nat.card D.Fibre = 4
    · exact Or.inl (D.class_cube_le_of_four_point_component hfour hSmaller)
    by_cases hsmall : Nat.card D.Fibre = 2 ∨ Nat.card D.Fibre = 3
    · exact Or.inr (Or.inl ⟨hsmall, hbounded⟩)
    have hsize : 5 ≤ Nat.card D.Fibre := by
      have htwo := D.degrees_ge_two.1
      omega
    by_cases htop : 4 ≤ Nat.card D.Points
    · exact Or.inl
        (GaronziMarotiLargeBlockCubeReduction.exact_exponent_large_block_cube_step
          D.map D.map_equivariant (Nat.card D.Fibre) (by omega) htop D.fibre_card_at hSmaller)
    have hblocks : Nat.card D.Points = 2 ∨ Nat.card D.Points = 3 := by
      have htwo := D.degrees_ge_two.2
      omega
    by_cases hlarge : 4096 ≤ Nat.card D.Fibre
    · rcases D.class_cube_or_actual_finite_model_of_large_component hCFSG hlarge hSmaller with h | h
      · exact Or.inl h
      · have hf : OriginalMinimalBlockBoundedShapeResidual.ActualFiniteModelResidual D := Or.inl h
        exact Or.inr (Or.inr (Or.inr hf))
    letI : Nontrivial D.Fibre := Finite.one_lt_card_iff_nontrivial.mp (by omega)
    letI : MulAction.IsPreprimitive D.Component D.Fibre := D.component_preprimitive
    obtain ⟨E⟩ := publishedONanScottStructure D.Component D.Fibre
    cases E with
    | inr P => exact Or.inl (D.class_cube_le_of_affine_component P hsize hSmaller)
    | inl E =>
      by_cases hsimple : IsSimpleGroup D.Component
      · letI := hsimple
        exact Or.inl (D.class_cube_le_of_simple_component (by omega) hSmaller)
      let W := CFSGReduction.simpleModelWitness hCFSG E.Simple
      exact Or.inr (Or.inr (Or.inl
        ⟨hblocks, hsize, by omega, E, W.index, ⟨W.equiv⟩, E.indexForm, hsimple⟩))
  · exact Or.inr (Or.inr (Or.inr hfinite))

end SymmetricSubgroupAsymptotics.OriginalMinimalBlockNonaffineShapeResidual
