import SymmetricSubgroupAsymptotics.FiniteModelPrimitiveClassReserveTail
import SymmetricSubgroupAsymptotics.SmallTopProperSubnormalClassGapBound
import SymmetricSubgroupAsymptotics.OriginalMinimalBlockComponentTransport
import SymmetricSubgroupAsymptotics.LargeSmallFibreSubgroupClassGap

/-! Actual original-action installers for a fixed finite model family.
The component branch uses the SAME base-component D and literal proper
subnormal sources, retaining the ordinary strict-smaller hypothesis.
The small-fibre branch separately uses the SAME actual top order to
bound every original subgroup through its own kernel and top image. -/
set_option autoImplicit false
noncomputable section
open scoped Classical
namespace SymmetricSubgroupAsymptotics.FiniteModelOriginalClassTailInstallers
open PrimitiveSocleRawStructure OriginalBlockClassBound CFSGReduction

theorem finite_family_component_threshold {ι : Type} [Finite ι]
    (M : ι → Type) [∀ i,Group (M i)] :
    ∃ N : ℕ,∀ {A Ω : Type} [Group A] [MulAction A Ω]
      [MulAction.IsPretransitive A Ω] [Finite A] [Finite Ω] [FaithfulSMul A Ω]
      {ω₀ : Ω} (D : OriginalMinimalBlock (A := A) ω₀)
      (E : NonaffineData D.Component D.Fibre) (i : ι) (e : E.Simple ≃* M i),
      N≤Nat.card D.Fibre →
      (∀ m : ℕ, m < Nat.card Ω → 4 ≤ m → ∀ L : Subgroup (Equiv.Perm (Fin m)),
        Nat.card (ConjClasses L)^3≤5^(m-1)) →
      Nat.card (ConjClasses A)^3≤5^(Nat.card Ω-1) := by
  obtain ⟨N,hN⟩ := FiniteModelPrimitiveClassReserveTail.finite_family_threshold M 2
  refine ⟨max 4 N,?_⟩
  intro A Ω _ _ _ _ _ _ ω₀ D E i e hlarge hSmaller
  have hfour : 4≤Nat.card D.Fibre := (le_max_left _ _).trans hlarge
  by_cases htop : 4≤Nat.card D.Points
  · exact GaronziMarotiLargeBlockCubeReduction.exact_exponent_large_block_cube_step
      D.map D.map_equivariant (Nat.card D.Fibre) hfour htop D.fibre_card_at hSmaller
  have hsmall : Nat.card D.Points=2 ∨ Nat.card D.Points=3 := by
    have hh := D.degrees_ge_two.2
    omega
  apply SmallTopProperSubnormalClassGapBound.class_cube_le_of_proper_subnormal_gaps
    D.map D.map_equivariant D.base (Nat.card D.Fibre) hfour rfl hsmall _ hSmaller
  intro L _hL _hne
  exact hN i E e ((le_max_right _ _).trans hlarge) L

theorem finite_family_small_fibre_threshold {ι : Type} [Finite ι]
    (M : ι → Type) [∀ i,Group (M i)] :
    ∃ N : ℕ,∀ {A Ω X : Type} [Group A] [MulAction A Ω] [MulAction A X]
      [Finite A] [Finite Ω] [Finite X] [FaithfulSMul A Ω]
      (π : Ω → X) (hπ : ∀ (g : A) (ω : Ω),π (g • ω)=g • π ω)
      (c : ℕ) (hc : c=2 ∨ c=3)
      (hsize : ∀ x,Nat.card (originalBlockFibre π x)=c)
      (E : NonaffineData (Top (A := A) (X := X)) X)
      (i : ι) (e : E.Simple ≃* M i),N≤Nat.card X → ∀ H : Subgroup A,
      Nat.card (ConjClasses H)^3≤5^(Nat.card Ω-2) := by
  letI := Fintype.ofFinite ι
  let B : ι → ℕ := fun i => Nat.card (M i)*Nat.card (Outer (M i))
  refine ⟨max 4096 (Finset.univ.sup B),?_⟩
  intro A Ω X _ _ _ _ _ _ _ π hπ c hc hsize E i e hlarge H
  letI : Finite (M i) := Finite.of_equiv E.Simple e.toEquiv
  have hn : 4096≤Nat.card X := (le_max_left _ _).trans hlarge
  have hB : Nat.card E.Simple*Nat.card (Outer E.Simple)≤Nat.card X := by
    rw [Nat.card_congr e.toEquiv,outer_card_congr e]
    exact (Finset.le_sup (f := B) (Finset.mem_univ i)).trans
      ((le_max_right _ _).trans hlarge)
  apply LargeSmallFibreSubgroupClassGap.subgroup_class_cube_gap_of_top_order
    π hπ c hc hsize hn _ H
  exact (FiniteModelPrimitiveClassTail.order_le_degree_log_square E hB (by omega)).trans
    (Nat.pow_le_pow_right (by omega) (by omega))

end SymmetricSubgroupAsymptotics.FiniteModelOriginalClassTailInstallers
