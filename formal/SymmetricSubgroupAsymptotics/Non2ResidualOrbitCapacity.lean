import SymmetricSubgroupAsymptotics.TraceyBinaryFormulaInput
import SymmetricSubgroupAsymptotics.TerminalContraction
import SymmetricSubgroupAsymptotics.NormalSubgroupOrbitIndex
import SymmetricSubgroupAsymptotics.PermutationBinaryFourAugmentation
import SymmetricSubgroupAsymptotics.PermutationBinaryFourNonbinary
import SymmetricSubgroupAsymptotics.Non2UnipotentSection
import Mathlib.GroupTheory.OrderOfElement

/-!
# Capacity on the literal nonbinary residual orbits

The quotient by `O²(G)` is binary.  Consequently, if the residual itself
is binary then the original group is binary.  On a faithful transitive
nonbinary action this excludes residual orbits of sizes one and two.  The
retained Tracey formula then proves the local `3/8` head bound at every
remaining degree except four.
-/

set_option autoImplicit false
noncomputable section
open scoped Classical
attribute [local instance] Fintype.ofFinite

namespace SymmetricSubgroupAsymptotics

variable {G X : Type} [Group G] [Finite G] [MulAction G X] [Finite X]

/-- A binary residual together with the canonical binary quotient makes the
whole finite group binary.  This is the extension step used to rule out tiny
residual orbits. -/
theorem isPGroup_of_terminalTwoResidual_isPGroup
    (hres : IsPGroup 2 (terminalTwoResidual G)) : IsPGroup 2 G := by
  let φ := QuotientGroup.mk' (terminalTwoResidual G)
  have hKernel : IsPGroup 2 φ.ker := by
    rw [QuotientGroup.ker_mk']
    exact hres
  have hPreimage : IsPGroup 2 (φ.range.comap φ) :=
    (terminalTwoResidual_quotient_binary G).to_subgroup φ.range
      |>.comap_of_ker_isPGroup φ hKernel
  have htop : φ.range.comap φ = (⊤ : Subgroup G) := by
    apply top_unique
    intro g _
    exact ⟨g, rfl⟩
  have hTopSubgroup : IsPGroup 2 (⊤ : Subgroup G) := htop ▸ hPreimage
  exact hTopSubgroup.of_equiv Subgroup.topEquiv

variable [MulAction.IsPretransitive G X] [FaithfulSMul G X]

/-- In a faithful transitive nonbinary action every literal `O²(G)`-orbit
has at least three points. -/
theorem terminalTwoResidual_orbit_card_three_le
    (hG : ¬IsPGroup 2 G)
    (o : MulAction.orbitRel.Quotient (terminalTwoResidual G) X) :
    3 ≤ Nat.card o.orbit := by
  by_contra hsmall
  have hle : Nat.card o.orbit ≤ 2 := by omega
  let H := terminalTwoResidual G
  have horbit : ∀ x : X, Nat.card (MulAction.orbit H x) ≤ 2 := by
    intro x
    exact (normal_orbit_card_eq H x o).symm.le.trans hle
  have hsquare : ∀ (h : H) (x : X), ((h : G) ^ 2) • x = x := by
    intro h x
    let O : MulAction.orbitRel.Quotient H X := Quotient.mk'' x
    let y : O.orbit := ⟨x, MulAction.mem_orbit_self x⟩
    let p : Equiv.Perm O.orbit := MulAction.toPerm h
    have hp := pow_card_eq_one' (x := p)
    have hperm : Nat.card (Equiv.Perm O.orbit) ≤ 2 := by
      rw [Nat.card_perm]
      have hc : Nat.card O.orbit ≤ 2 := by
        exact (normal_orbit_card_eq H x O).trans_le (horbit x)
      interval_cases Nat.card O.orbit <;> norm_num
    have hp2 : p ^ 2 = 1 := by
      have hpos : 0 < Nat.card (Equiv.Perm O.orbit) := Nat.card_pos
      have hcases : Nat.card (Equiv.Perm O.orbit) = 1 ∨
          Nat.card (Equiv.Perm O.orbit) = 2 := by omega
      rcases hcases with hcard | hcard
      · rw [hcard, pow_one] at hp
        rw [hp, one_pow]
      · rw [hcard] at hp
        exact hp
    have hy := congrArg (fun e : Equiv.Perm O.orbit => e y) hp2
    have hyv := congrArg Subtype.val hy
    change (h : G) • ((h : G) • x) = x at hyv
    simpa only [pow_two, mul_smul] using hyv
  have hres : IsPGroup 2 H := by
    intro h
    refine ⟨1, ?_⟩
    apply Subtype.ext
    apply (MulAction.toPerm_injective (α := G) (β := X))
    apply Equiv.ext
    intro x
    simpa using hsquare h x
  exact hG (isPGroup_of_terminalTwoResidual_isPGroup hres)

/-- No literal residual orbit can have binary permutation image.  A binary
image on one orbit gives a common binary exponent on that orbit; normality
transports it to every conjugate orbit, and faithfulness makes the residual
itself binary. -/
theorem terminalTwoResidual_orbit_image_not_isPGroup
    (hG : ¬IsPGroup 2 G)
    (o : MulAction.orbitRel.Quotient (terminalTwoResidual G) X) :
    ¬IsPGroup 2
      (MulAction.toPermHom (terminalTwoResidual G) o.orbit).range := by
  intro himage
  let H := terminalTwoResidual G
  obtain ⟨a, ha⟩ := himage.exists_card_eq
  have hres : IsPGroup 2 H := by
    intro h
    refine ⟨a, ?_⟩
    apply Subtype.ext
    apply (MulAction.toPerm_injective (α := G) (β := X))
    apply Equiv.ext
    intro x
    obtain ⟨g, hg⟩ := MulAction.exists_smul_eq G o.out x
    let c : H :=
      ⟨g⁻¹ * (h : G) * g,
        by
          simpa only [inv_inv] using
            (Subgroup.Normal.conj_mem inferInstance (h : G) h.property g⁻¹)⟩
    let q : (MulAction.toPermHom H o.orbit).range :=
      (MulAction.toPermHom H o.orbit).rangeRestrict c
    have hq : q ^ (2 ^ a) = 1 := by
      rw [← ha]
      exact pow_card_eq_one'
    let y : o.orbit := ⟨o.out, by
      rw [o.orbit_eq_orbit_out Quotient.out_eq']
      exact MulAction.mem_orbit_self o.out⟩
    have hcperm :
        (MulAction.toPerm (c ^ (2 ^ a)) : Equiv.Perm o.orbit) = 1 := by
      change MulAction.toPermHom H o.orbit (c ^ (2 ^ a)) = 1
      rw [map_pow]
      simpa [q] using congrArg Subtype.val hq
    have hy := congrArg (fun e : Equiv.Perm o.orbit => e y) hcperm
    have hfix : ((c : H) ^ (2 ^ a)) • o.out = o.out := by
      have hyv := congrArg Subtype.val hy
      simpa [y] using hyv
    have hconj : (g⁻¹ * (h : G) * g) ^ (2 ^ a) • o.out = o.out := by
      exact hfix
    have hm : (h : G) ^ (2 ^ a) • (g • o.out) = g • o.out := by
      have hconjpow :
          (g⁻¹ * (h : G) * g) ^ (2 ^ a) =
            g⁻¹ * (h : G) ^ (2 ^ a) * g := by
        simpa only [inv_inv] using
          (conj_pow :
            (g⁻¹ * (h : G) * (g⁻¹)⁻¹) ^ (2 ^ a) =
              g⁻¹ * (h : G) ^ (2 ^ a) * (g⁻¹)⁻¹)
      have halg :
          g * ((g⁻¹ * (h : G) * g) ^ (2 ^ a)) =
            (h : G) ^ (2 ^ a) * g := by
        rw [hconjpow]
        group
      calc
        (h : G) ^ (2 ^ a) • (g • o.out) =
            ((h : G) ^ (2 ^ a) * g) • o.out := by rw [mul_smul]
        _ = (g * ((g⁻¹ * (h : G) * g) ^ (2 ^ a))) • o.out := by rw [halg]
        _ = g • ((g⁻¹ * (h : G) * g) ^ (2 ^ a) • o.out) := by
          rw [mul_smul]
        _ = g • o.out := congrArg (fun z : X => g • z) hconj
    change ((h : G) ^ (2 ^ a)) • x = (1 : G) • x
    simpa only [one_smul, hg] using hm
  exact hG (isPGroup_of_terminalTwoResidual_isPGroup hres)

/-- The exact Tracey formula proves the local `3/8` head estimate on every
literal residual orbit except the genuine four-point structural endpoint. -/
theorem terminalTwoResidual_orbit_head_three_eighths_of_ne_four
    (hTracey : TraceyBinaryFormulaInput) (hG : ¬IsPGroup 2 G)
    (o : MulAction.orbitRel.Quotient (terminalTwoResidual G) X)
    (hfour : Nat.card o.orbit ≠ 4)
    (S : Subrepresentation
      (permutationFunctionRepresentation (ZMod 2)
        (terminalTwoResidual G) o.orbit)) :
    8 * Module.finrank (ZMod 2) (S.toRepresentation.IntertwiningMap
      (Representation.trivial (ZMod 2) (terminalTwoResidual G) (ZMod 2))) ≤
        3 * Nat.card o.orbit := by
  exact traceyBinaryFormulaBounds_three_eighths_of_three_le_of_ne_four
    (terminalTwoResidual_orbit_card_three_le hG o) hfour
    (hTracey (terminalTwoResidual G) o.orbit S)

/-- The four-point endpoint is smaller than the formula alone records.  If
the head had dimension at least two, the submodule would be the literal
augmentation hyperplane.  But the residual orbit image is nonbinary, hence
contains a three-cycle, whose fixed space on that hyperplane has dimension
at most one. -/
theorem terminalTwoResidual_orbit_head_three_eighths_of_eq_four
    (hG : ¬IsPGroup 2 G)
    (o : MulAction.orbitRel.Quotient (terminalTwoResidual G) X)
    (hfour : Nat.card o.orbit = 4)
    (S : Subrepresentation
      (permutationFunctionRepresentation (ZMod 2)
        (terminalTwoResidual G) o.orbit)) :
    8 * Module.finrank (ZMod 2) (S.toRepresentation.IntertwiningMap
      (Representation.trivial (ZMod 2) (terminalTwoResidual G) (ZMod 2))) ≤
        3 * Nat.card o.orbit := by
  let x : o.orbit :=
    ⟨o.nonempty_orbit.choose, o.nonempty_orbit.choose_spec⟩
  have hd : Module.finrank (ZMod 2) (S.toRepresentation.IntertwiningMap
      (Representation.trivial (ZMod 2)
        (terminalTwoResidual G) (ZMod 2))) ≤ 1 := by
    by_contra hnot
    have htwo : 2 ≤ Module.finrank (ZMod 2)
        (S.toRepresentation.IntertwiningMap
          (Representation.trivial (ZMod 2)
            (terminalTwoResidual G) (ZMod 2))) := by omega
    have haug :=
      (PermutationBinaryFourAugmentation.eq_augmentation_of_head_ge_two_unconditional
        (S := S) x hfour htwo).2
    have hone := four_nonbinary_subrepresentationHead_le_one hfour
      (terminalTwoResidual_orbit_image_not_isPGroup hG o) S haug
    omega
  omega

/-- Every literal orbit of the terminal binary residual has the uniform
`3/8` head capacity in a faithful transitive nonbinary action. -/
theorem terminalTwoResidual_orbit_head_three_eighths
    (hTracey : TraceyBinaryFormulaInput) (hG : ¬IsPGroup 2 G)
    (o : MulAction.orbitRel.Quotient (terminalTwoResidual G) X)
    (S : Subrepresentation
      (permutationFunctionRepresentation (ZMod 2)
        (terminalTwoResidual G) o.orbit)) :
    8 * Module.finrank (ZMod 2) (S.toRepresentation.IntertwiningMap
      (Representation.trivial (ZMod 2) (terminalTwoResidual G) (ZMod 2))) ≤
        3 * Nat.card o.orbit := by
  by_cases hfour : Nat.card o.orbit = 4
  · exact terminalTwoResidual_orbit_head_three_eighths_of_eq_four
      hG o hfour S
  · exact terminalTwoResidual_orbit_head_three_eighths_of_ne_four
      hTracey hG o hfour S

/-- The exact Tracey formula and the nonbinary four-point endpoint discharge
the full two-step unipotent budget for every quotient of the original
permutation section. -/
theorem binary_permutationSection_unipotent_of_Tracey
    {A : Type} [AddCommGroup A] [Module (ZMod 2) A]
    [FiniteDimensional (ZMod 2) A]
    (hTracey : TraceyBinaryFormulaInput) (hG : ¬IsPGroup 2 G)
    (ρ : Representation (ZMod 2) G A)
    (M : Subrepresentation
      (permutationFunctionRepresentation (ZMod 2) G X))
    (q : M.toRepresentation.IntertwiningMap ρ)
    (hq : Function.Surjective q) :
    8 * (Module.finrank (ZMod 2) ρ.invariants +
      Module.finrank (ZMod 2) (displacementSlice ρ ρ.invariants)) ≤
        3 * Nat.card X := by
  let cap : MulAction.orbitRel.Quotient (terminalTwoResidual G) X → ℕ :=
    fun o => 3 * Nat.card o.orbit / 8
  apply binary_permutationSection_unipotent_of_residual_orbit_caps
    ρ M q hq cap
  · intro o S
    apply (Nat.le_div_iff_mul_le (by decide : 0 < 8)).2
    simpa only [Nat.mul_comm] using
      terminalTwoResidual_orbit_head_three_eighths hTracey hG o S
  · intro o
    simpa only [cap, Nat.mul_comm] using
      Nat.div_mul_le_self (3 * Nat.card o.orbit) 8

end SymmetricSubgroupAsymptotics

end
