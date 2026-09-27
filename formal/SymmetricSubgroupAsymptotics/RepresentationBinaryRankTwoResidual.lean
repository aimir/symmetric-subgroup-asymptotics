import SymmetricSubgroupAsymptotics.RepresentationBinaryCommonCharacter
import SymmetricSubgroupAsymptotics.BinaryDisplacementCentralCut

/-! The actual rank-two residual has either a strict one-dimensional
central cut or a common original character with kernel of index two.
Both branches are derived from the entire original displacement space.
The character branch retains the original displacement endomorphism;
it does not identify any original extension with a split carrier.
-/
set_option autoImplicit false
noncomputable section

namespace SymmetricSubgroupAsymptotics.RepresentationBinaryCommonCharacter

open LinearMapEvaluationSeparator

variable {G A : Type} [Group G] [Finite G]
    [AddCommGroup A] [Module (ZMod 2) A] [FiniteDimensional (ZMod 2) A]
    (ρ : Representation (ZMod 2) G A)

theorem character_kernel_index_two (χ : PrimeCharacters 2 G) (hχ : χ≠0) :
    (AddMonoidHom.toMultiplicativeRight χ).ker.index=2 := by
  obtain ⟨g₀,hg₀⟩ := exists_character_one χ hχ
  have hbits : ∀ c : ZMod 2, c=0 ∨ c=1 := by decide +kernel
  have honto : Function.Surjective (AddMonoidHom.toMultiplicativeRight χ) := by
    intro y
    rcases hbits y.toAdd with hy | hy
    · refine ⟨1,?_⟩
      change χ (Additive.ofMul (1:G))=y.toAdd
      rw [hy]
      exact χ.map_zero
    · refine ⟨g₀,?_⟩
      change χ (Additive.ofMul g₀)=y.toAdd
      exact hg₀.trans hy.symm
  change Nat.card (G ⧸ (AddMonoidHom.toMultiplicativeRight χ).ker)=2
  rw [Nat.card_congr (QuotientGroup.quotientKerEquivOfSurjective
    (AddMonoidHom.toMultiplicativeRight χ) honto).toEquiv]
  simp only [Nat.card_eq_fintype_card,Fintype.card_multiplicative,ZMod.card]

/-- Data entirely on the original group and original vector space. -/
structure TwoBlockCharacter where
  character : PrimeCharacters 2 G
  character_ne_zero : character≠0
  element : G
  value_one : character (Additive.ofMul element)=1
  displacement : ∀ (g : G) (a : A), ρ g a-a=
    character (Additive.ofMul g) • actionDelta ρ element a
  delta_kernel : (actionDelta ρ element).ker=ρ.invariants
  delta_range : (actionDelta ρ element).range=ρ.invariants
  action_kernel : ρ.ker=(AddMonoidHom.toMultiplicativeRight character).ker
  kernel_index : ρ.ker.index=2

theorem twoBlockCharacter_of_evaluation_rank_le_one
    (hA : Module.finrank (ZMod 2) A=4)
    (hS : Module.finrank (ZMod 2) ρ.invariants=2)
    (hD : Module.finrank (ZMod 2) (displacementSlice ρ ρ.invariants)=2)
    (heval : ∀ μ : Module.Dual (ZMod 2) ρ.invariants,
      Module.finrank (ZMod 2) (evaluation (operatorSpace ρ) μ).range≤1) :
    Nonempty (TwoBlockCharacter ρ) := by
  obtain ⟨χ,g₀,hχ,hg₀,hformula,hker,hrange,hkernel⟩ :=
    exists_common_character_two_blocks ρ hA hS hD heval
  exact ⟨{
    character := χ
    character_ne_zero := hχ
    element := g₀
    value_one := hg₀
    displacement := hformula
    delta_kernel := hker
    delta_range := hrange
    action_kernel := hkernel
    kernel_index := by
      rw [hkernel]
      exact character_kernel_index_two χ hχ }⟩

/-- A rank-two evaluation separates the complete two-dimensional slice.
Its literal annihilator in the original fixed space is the required cut. -/
theorem central_cut_of_rank_two_evaluation
    (hS : Module.finrank (ZMod 2) ρ.invariants=2)
    (hD : Module.finrank (ZMod 2) (displacementSlice ρ ρ.invariants)=2)
    (μ : Module.Dual (ZMod 2) ρ.invariants)
    (hμrank : 2≤Module.finrank (ZMod 2) (evaluation (operatorSpace ρ) μ).range) :
    ∃ (C : Submodule (ZMod 2) A) (hC : C≤ρ.invariants),
      displacementSlice ρ C=⊥ ∧ Module.finrank (ZMod 2) C=1 ∧
        Module.finrank (ZMod 2) (centralQuotientRepresentation ρ C hC).invariants=1 := by
  have hdim : Module.finrank (ZMod 2) (operatorSpace ρ)=2 :=
    (LinearEquiv.ofInjective (fixedDisplacementTranspose 2 ρ)
      (fixedDisplacementTranspose_injective 2 ρ)).finrank_eq.symm.trans hD
  have hsum := evaluation_rank_nullity (operatorSpace ρ) μ
  have hzero : Module.finrank (ZMod 2) (vanishingAt (operatorSpace ρ) μ)=0 := by omega
  have hvan : vanishingAt (operatorSpace ρ) μ=⊥ :=
    (Submodule.finrank_eq_zero (R := ZMod 2)
      (M := Module.Dual (ZMod 2) ρ.invariants →ₗ[ZMod 2] PrimeCharacters 2 G)
      (S := vanishingAt (operatorSpace ρ) μ)).mp hzero
  have hμ : μ≠0 := by
    intro hz
    have he : evaluation (operatorSpace ρ) μ=0 := by
      apply LinearMap.ext
      intro f
      change f.1 μ=0
      rw [hz,map_zero]
    rw [he,LinearMap.range_zero,finrank_bot] at hμrank
    omega
  let W := Submodule.span (ZMod 2) {μ}
  have hW : Module.finrank (ZMod 2) W=1 := finrank_span_singleton hμ
  have hsep : Separates (operatorSpace ρ) W := by
    intro f hf hzero
    have hfvan : f∈vanishingAt (operatorSpace ρ) μ :=
      ⟨hf,hzero μ (Submodule.mem_span_singleton_self μ)⟩
    rw [hvan] at hfvan
    exact hfvan
  refine ⟨fixedDualCut ρ W,fixedDualCut_le_invariants ρ W,
    fixedDualCut_displacement_eq_bot ρ W hsep,?_,?_⟩
  · have hcut := fixedDualCut_finrank_add ρ W
    rw [hW,hS] at hcut
    omega
  · exact (fixedDualCut_quotient_invariants_finrank ρ W hsep).trans hW

/-- No evaluation premise remains in this actual residual dichotomy.
The first alternative has joint cost 2*1+4*1=6. -/
theorem central_cut_or_twoBlockCharacter
    (hA : Module.finrank (ZMod 2) A=4)
    (hS : Module.finrank (ZMod 2) ρ.invariants=2)
    (hD : Module.finrank (ZMod 2) (displacementSlice ρ ρ.invariants)=2) :
    (∃ (C : Submodule (ZMod 2) A) (hC : C≤ρ.invariants),
      displacementSlice ρ C=⊥ ∧ Module.finrank (ZMod 2) C=1 ∧
        Module.finrank (ZMod 2) (centralQuotientRepresentation ρ C hC).invariants=1) ∨
      Nonempty (TwoBlockCharacter ρ) := by
  classical
  by_cases htwo : ∃ μ : Module.Dual (ZMod 2) ρ.invariants,
      2≤Module.finrank (ZMod 2) (evaluation (operatorSpace ρ) μ).range
  · obtain ⟨μ,hμ⟩ := htwo
    exact Or.inl (central_cut_of_rank_two_evaluation ρ hS hD μ hμ)
  · apply Or.inr
    apply twoBlockCharacter_of_evaluation_rank_le_one ρ hA hS hD
    intro μ
    by_contra hn
    exact htwo ⟨μ,by omega⟩

end SymmetricSubgroupAsymptotics.RepresentationBinaryCommonCharacter
