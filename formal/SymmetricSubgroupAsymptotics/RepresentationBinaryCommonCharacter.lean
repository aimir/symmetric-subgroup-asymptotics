import SymmetricSubgroupAsymptotics.RepresentationDisplacementCharacters
import SymmetricSubgroupAsymptotics.LinearMapEvaluationSeparator

/-! A common character for the actual four-dimensional binary residual.

The evaluation input is a functional on the original fixed space. Its
domain is the transpose of the complete original displacement slice and
its codomain consists of characters of the original acting group. The
rank-one evaluation condition forces a common character. In dimension
four, with fixed and displacement dimensions both two, the original
action has exactly that character kernel. Its nonidentity displacement
has both kernel and image equal to the original fixed space.

No split extension, module replacement, or carrier identification is
assumed or constructed here.
-/
set_option autoImplicit false
noncomputable section

namespace SymmetricSubgroupAsymptotics.RepresentationBinaryCommonCharacter

open LinearMapEvaluationSeparator

variable {G A : Type} [Group G] [Finite G]
    [AddCommGroup A] [Module (ZMod 2) A] [FiniteDimensional (ZMod 2) A]
    (ρ : Representation (ZMod 2) G A)

/-- The operator space is the full transpose of the original slice. -/
abbrev operatorSpace := (fixedDisplacementTranspose 2 ρ).range

theorem exists_common_character
    (hD : 2≤Module.finrank (ZMod 2) (displacementSlice ρ ρ.invariants))
    (heval : ∀ μ : Module.Dual (ZMod 2) ρ.invariants,
      Module.finrank (ZMod 2) (evaluation (operatorSpace ρ) μ).range≤1) :
    ∃ χ : PrimeCharacters 2 G, χ≠0 ∧
      ∀ f : displacementSlice ρ ρ.invariants,
        (fixedDisplacementTranspose 2 ρ f).range≤Submodule.span (ZMod 2) {χ} := by
  have hdim : Module.finrank (ZMod 2) (operatorSpace ρ)=
      Module.finrank (ZMod 2) (displacementSlice ρ ρ.invariants) :=
    (LinearEquiv.ofInjective (fixedDisplacementTranspose 2 ρ)
      (fixedDisplacementTranspose_injective 2 ρ)).finrank_eq.symm
  obtain ⟨χ,hχ,hline⟩ := common_image_line_of_evaluation_rank_le_one
    (operatorSpace ρ) (hdim.symm ▸ hD) heval
  refine ⟨χ,hχ,?_⟩
  intro f ψ hψ
  obtain ⟨μ,rfl⟩ := hψ
  exact (hline (show fixedDisplacementTranspose 2 ρ f∈operatorSpace ρ
    from ⟨f,rfl⟩)).2 μ

private theorem binary_value (c : ZMod 2) : c=0 ∨ c=1 := by
  revert c
  decide +kernel

theorem exists_character_one (χ : PrimeCharacters 2 G) (hχ : χ≠0) :
    ∃ g : G, χ (Additive.ofMul g)=1 := by
  by_contra hn
  apply hχ
  apply AddMonoidHom.ext
  intro g
  change χ g=0
  rcases binary_value (χ g) with hg | hg
  · exact hg
  · exact (hn ⟨g.toMul,hg⟩).elim

/-- The original vector-valued displacement is reconstructed from one
actual group element. Dual functionals are used only to detect equality. -/
theorem displacement_formula (χ : PrimeCharacters 2 G) (g₀ : G)
    (hg₀ : χ (Additive.ofMul g₀)=1)
    (hline : ∀ f : displacementSlice ρ ρ.invariants,
      (fixedDisplacementTranspose 2 ρ f).range≤Submodule.span (ZMod 2) {χ})
    (f : displacementSlice ρ ρ.invariants) (g : G) :
    fixedDisplacementValue 2 ρ f g=
      χ (Additive.ofMul g) • fixedDisplacementValue 2 ρ f g₀ := by
  apply (Module.evalEquiv (ZMod 2) ρ.invariants).injective
  ext μ
  change μ (fixedDisplacementValue 2 ρ f g)=
    μ (χ (Additive.ofMul g) • fixedDisplacementValue 2 ρ f g₀)
  rw [map_smul]
  obtain ⟨c,hc⟩ := Submodule.mem_span_singleton.mp (hline f ⟨μ,rfl⟩)
  have hc₀ := congrArg (fun ψ : PrimeCharacters 2 G => ψ (Additive.ofMul g₀)) hc
  change c * χ (Additive.ofMul g₀)=μ (fixedDisplacementValue 2 ρ f g₀) at hc₀
  rw [hg₀,mul_one] at hc₀
  have hcg := congrArg (fun ψ : PrimeCharacters 2 G => ψ (Additive.ofMul g)) hc
  change c * χ (Additive.ofMul g)=μ (fixedDisplacementValue 2 ρ f g) at hcg
  change μ (fixedDisplacementValue 2 ρ f g)=
    χ (Additive.ofMul g) * μ (fixedDisplacementValue 2 ρ f g₀)
  rw [← hc₀,mul_comm]
  exact hcg.symm

/-- Equality of the actual dimension sum makes every original
displacement fixed-valued; this is not a supplied trivial quotient. -/
theorem displacementPreimage_eq_top
    (hdim : Module.finrank (ZMod 2) A=
      Module.finrank (ZMod 2) ρ.invariants+
        Module.finrank (ZMod 2) (displacementSlice ρ ρ.invariants)) :
    displacementPreimage ρ ρ.invariants=⊤ := by
  have hd := (displacementToSlice ρ ρ.invariants).finrank_range_add_finrank_ker
  rw [LinearMap.range_eq_top.mpr (displacementToSlice_surjective ρ ρ.invariants),
    finrank_top,displacementToSlice_ker,
    (Submodule.comapSubtypeEquivOfLe
      (invariants_le_displacementPreimage ρ ρ.invariants)).finrank_eq] at hd
  apply Submodule.eq_top_of_finrank_eq
  omega

/-- The displacement endomorphism of the literal original action. -/
def actionDelta (g : G) : A →ₗ[ZMod 2] A := ρ g-LinearMap.id

@[simp] theorem actionDelta_apply (g : G) (a : A) :
    actionDelta ρ g a=ρ g a-a := rfl

/-- A common original character and an actual endomorphism exhibiting
the two length-two blocks. The action kernel is the same original
subgroup as the character kernel. -/
theorem exists_common_character_two_blocks
    (hA : Module.finrank (ZMod 2) A=4)
    (hS : Module.finrank (ZMod 2) ρ.invariants=2)
    (hD : Module.finrank (ZMod 2) (displacementSlice ρ ρ.invariants)=2)
    (heval : ∀ μ : Module.Dual (ZMod 2) ρ.invariants,
      Module.finrank (ZMod 2) (evaluation (operatorSpace ρ) μ).range≤1) :
    ∃ (χ : PrimeCharacters 2 G) (g₀ : G), χ≠0 ∧ χ (Additive.ofMul g₀)=1 ∧
      (∀ (g : G) (a : A), ρ g a-a=
        χ (Additive.ofMul g) • actionDelta ρ g₀ a) ∧
      (actionDelta ρ g₀).ker=ρ.invariants ∧
      (actionDelta ρ g₀).range=ρ.invariants ∧
      ρ.ker=(AddMonoidHom.toMultiplicativeRight χ).ker := by
  obtain ⟨χ,hχ,hline⟩ := exists_common_character ρ hD.ge heval
  obtain ⟨g₀,hg₀⟩ := exists_character_one χ hχ
  have htotal := displacementPreimage_eq_top ρ (by omega)
  have hfixed : ∀ (a : A) (g : G), ρ g a-a∈ρ.invariants := by
    intro a
    have ha : a∈displacementPreimage ρ ρ.invariants := by rw [htotal]; trivial
    exact ha
  have hformula : ∀ (g : G) (a : A), ρ g a-a=
      χ (Additive.ofMul g) • actionDelta ρ g₀ a := by
    intro g a
    let f : displacementSlice ρ ρ.invariants :=
      ⟨representationDisplacement ρ a,⟨⟨a,rfl⟩,hfixed a⟩⟩
    exact congrArg Subtype.val (displacement_formula ρ χ g₀ hg₀ hline f g)
  have hker : (actionDelta ρ g₀).ker=ρ.invariants := by
    ext a
    constructor
    · intro ha g
      have hz : actionDelta ρ g₀ a=0 := ha
      apply sub_eq_zero.mp
      rw [hformula g a,hz,smul_zero]
    · intro ha
      change ρ g₀ a-a=0
      rw [ha g₀,sub_self]
  have hle : (actionDelta ρ g₀).range≤ρ.invariants := by
    rintro _ ⟨a,rfl⟩
    exact hfixed a g₀
  have hrange : (actionDelta ρ g₀).range=ρ.invariants := by
    apply Submodule.eq_of_le_of_finrank_eq hle
    have hd := (actionDelta ρ g₀).finrank_range_add_finrank_ker
    rw [hker,hS,hA] at hd
    omega
  have hδ : actionDelta ρ g₀≠0 := by
    intro hz
    have hd := congrArg (fun S : Submodule (ZMod 2) A => Module.finrank (ZMod 2) S) hrange
    change Module.finrank (ZMod 2) (actionDelta ρ g₀).range=
      Module.finrank (ZMod 2) ρ.invariants at hd
    rw [hz,LinearMap.range_zero,finrank_bot,hS] at hd
    omega
  refine ⟨χ,g₀,hχ,hg₀,hformula,hker,hrange,?_⟩
  ext g
  change ρ g=1 ↔ χ (Additive.ofMul g)=0
  constructor
  · intro hg
    rcases binary_value (χ (Additive.ofMul g)) with hc | hc
    · exact hc
    · exfalso
      apply hδ
      apply LinearMap.ext
      intro a
      have ha := hformula g a
      rw [hg,hc,one_smul] at ha
      change a-a=actionDelta ρ g₀ a at ha
      simpa only [sub_self] using ha.symm
  · intro hc
    apply LinearMap.ext
    intro a
    have ha := hformula g a
    rw [hc,zero_smul] at ha
    exact sub_eq_zero.mp ha

end SymmetricSubgroupAsymptotics.RepresentationBinaryCommonCharacter
