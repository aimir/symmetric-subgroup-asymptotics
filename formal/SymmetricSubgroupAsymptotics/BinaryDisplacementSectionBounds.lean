import SymmetricSubgroupAsymptotics.BinaryCharacterKernelDisplacement
import SymmetricSubgroupAsymptotics.RepresentationDisplacementCharacters
import SymmetricSubgroupAsymptotics.BinaryZeroCutWideParameters

/-! The actual bounds needed by a linear evaluation separator. The
original fixed space and the complete displacement space each obey the
Boolean-width bound. Every original character-line slice obeys the
coupled two-orbit bound, including the fixed-space term. No separator or
capacity inequality is assumed or concluded here. -/
set_option autoImplicit false
noncomputable section
namespace SymmetricSubgroupAsymptotics

variable {G X A : Type} [Group G] [MulAction G X]
    [Finite G] [Finite X] [MulAction.IsPretransitive G X]
    [AddCommGroup A] [Module (ZMod 2) A] [FiniteDimensional (ZMod 2) A]

/-- Every original section has a bounded fixed space; its preimage in
the original permutation module supplies the trivial quotient. -/
theorem binary_permutationSection_invariants_finrank_le
    (ρ : Representation (ZMod 2) G A) (hG : IsPGroup 2 G)
    (M : Subrepresentation (permutationFunctionRepresentation (ZMod 2) G X))
    (q : M.toRepresentation.IntertwiningMap ρ) (hq : Function.Surjective q)
    (x : X) (a : ℕ) (hdegree : Nat.card X=2^a) :
    Module.finrank (ZMod 2) ρ.invariants ≤ a.choose (a/2) := by
  let W : Submodule (ZMod 2) (PrimeCharacters 2 G) := ⊥
  let χW := primeCharacterSubspaceEmbedding 2 (G := G) W
  have hb := binary_permutationSection_joint_character_kernel_bound (G := G) (V := W)
    ρ hG M q hq χW (primeCharacterSubspaceEmbedding_injective 2 (G := G) W) x a hdegree
  have hj : Module.finrank (ZMod 2)
      (retainedStabilizerVanishing 2 (G := G) (V := W) χW x)=0 := by
    have h := Submodule.finrank_le
      (retainedStabilizerVanishing 2 (G := G) (V := W) χW x)
    exact Nat.eq_zero_of_le_zero (by simpa only [W,finrank_bot] using h)
  simp only [hj,pow_zero,Nat.sub_zero,one_mul] at hb
  exact (Nat.le_add_right _ _).trans hb

/-- Quotienting by all original invariants still gives an actual section
of the same permutation module. This bounds the full displacement image. -/
theorem binary_permutationSection_displacement_finrank_le
    (ρ : Representation (ZMod 2) G A) (hG : IsPGroup 2 G)
    (M : Subrepresentation (permutationFunctionRepresentation (ZMod 2) G X))
    (q : M.toRepresentation.IntertwiningMap ρ) (hq : Function.Surjective q)
    (x : X) (a : ℕ) (hdegree : Nat.card X=2^a) :
    Module.finrank (ZMod 2) (displacementSlice ρ ρ.invariants) ≤ a.choose (a/2) := by
  let σ := centralQuotientRepresentation ρ ρ.invariants le_rfl
  let π : ρ.IntertwiningMap σ := {
    toLinearMap := ρ.invariants.mkQ
    isIntertwining' := fun _ => rfl }
  have hπ : Function.Surjective π := ρ.invariants.mkQ_surjective
  rw [displacementSlice_invariants_finrank]
  exact binary_permutationSection_invariants_finrank_le σ hG M (π.comp q)
    (hπ.comp hq) x a hdegree

/-- Every character-image line slice consumes the same joint budget
with the ENTIRE original fixed space. Transitivity gives one or two
actual common-kernel orbits; neither possibility is assumed away. -/
theorem binary_permutationSection_character_line_slice_bound
    (ρ : Representation (ZMod 2) G A) (hG : IsPGroup 2 G)
    (M : Subrepresentation (permutationFunctionRepresentation (ZMod 2) G X))
    (q : M.toRepresentation.IntertwiningMap ρ) (hq : Function.Surjective q)
    (x : X) (a : ℕ) (ha : 1≤a) (hdegree : Nat.card X=2^a)
    (χ : PrimeCharacters 2 G) (hχ : χ≠0) :
    Module.finrank (ZMod 2) ρ.invariants +
      Module.finrank (ZMod 2) (fixedDisplacementCharacterSlice 2 ρ
        (Submodule.span (ZMod 2) ({χ} : Set (PrimeCharacters 2 G)))) ≤
          2*(a-1).choose ((a-1)/2) := by
  let W := Submodule.span (ZMod 2) ({χ} : Set (PrimeCharacters 2 G))
  let χW := primeCharacterSubspaceEmbedding 2 (G := G) W
  let j := Module.finrank (ZMod 2) (retainedStabilizerVanishing 2 (G := G) (V := W) χW x)
  have hW : Module.finrank (ZMod 2) W=1 := finrank_span_singleton (K := ZMod 2) hχ
  have hj : j≤1 := (Submodule.finrank_le
    (retainedStabilizerVanishing 2 (G := G) (V := W) χW x)).trans_eq hW
  have hb := binary_permutationSection_joint_character_kernel_bound (G := G) (V := W)
    ρ hG M q hq χW (primeCharacterSubspaceEmbedding_injective 2 (G := G) W) x a hdegree
  change Module.finrank (ZMod 2) ρ.invariants + Module.finrank (ZMod 2)
    (displacementJointSlice ρ (retainedCharacterEvaluation 2 (G := G) (V := W) χW).ker) ≤
      2^j*(a-j).choose ((a-j)/2) at hb
  change Module.finrank (ZMod 2) ρ.invariants +
    Module.finrank (ZMod 2) (fixedDisplacementCharacterSlice 2 ρ W) ≤ _
  rw [fixedDisplacementCharacterSlice_finrank]
  rcases (show j=0 ∨ j=1 by omega) with hj0 | hj1
  · simp only [hj0,pow_zero,Nat.sub_zero,one_mul] at hb
    have hwidth := binary_middle_succ_le_twice (a-1)
    rw [Nat.sub_add_cancel ha] at hwidth
    exact hb.trans hwidth
  · simpa only [hj1,pow_one] using hb

end SymmetricSubgroupAsymptotics
