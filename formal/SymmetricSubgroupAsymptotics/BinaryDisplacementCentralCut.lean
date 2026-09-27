import SymmetricSubgroupAsymptotics.BinaryDisplacementSectionBounds
import SymmetricSubgroupAsymptotics.LinearMapEvaluationSeparator
import SymmetricSubgroupAsymptotics.SchurPGroupCapacity

/-! A genuine central cut in the original section, obtained by separating
the entire original displacement image. Its quotient fixed dimension is
computed exactly. The final section theorem proves its line-slice inputs
from the original binary permutation action rather than assuming a cut
capacity or a separator. -/
set_option autoImplicit false
noncomputable section
namespace SymmetricSubgroupAsymptotics
open LinearMapEvaluationSeparator

variable {G A : Type} [Group G] [Finite G]
    [AddCommGroup A] [Module (ZMod 2) A] [FiniteDimensional (ZMod 2) A]
    (ρ : Representation (ZMod 2) G A)

/-- The pure operator line slice is exactly the corresponding domain
slice of the complete original displacement transpose. -/
def fixedDisplacementImageLineEquiv (χ : PrimeCharacters 2 G) :
    fixedDisplacementCharacterSlice 2 ρ (Submodule.span (ZMod 2) {χ}) ≃ₗ[ZMod 2]
      imageLineSlice (fixedDisplacementTranspose 2 ρ).range χ := by
  let f : fixedDisplacementCharacterSlice 2 ρ (Submodule.span (ZMod 2) {χ}) →ₗ[ZMod 2]
      imageLineSlice (fixedDisplacementTranspose 2 ρ).range χ :=
    ((fixedDisplacementTranspose 2 ρ).comp
      (fixedDisplacementCharacterSlice 2 ρ (Submodule.span (ZMod 2) {χ})).subtype).codRestrict
        (imageLineSlice (fixedDisplacementTranspose 2 ρ).range χ)
        (fun v => ⟨⟨v.val,rfl⟩,fun ℓ => v.property ⟨ℓ,rfl⟩⟩)
  apply LinearEquiv.ofBijective f
  constructor
  · intro v v' h
    apply Subtype.ext
    exact fixedDisplacementTranspose_injective 2 ρ (congrArg Subtype.val h)
  · intro T
    obtain ⟨v,hv⟩ := T.property.1
    have hmem : v ∈ fixedDisplacementCharacterSlice 2 ρ (Submodule.span (ZMod 2) {χ}) := by
      rintro ψ ⟨ℓ,rfl⟩
      rw [hv]
      exact T.property.2 ℓ
    exact ⟨⟨v,hmem⟩,Subtype.ext hv⟩

/-- The literal annihilator cut inside the original A, not inside a
chosen coordinate copy of its fixed space. -/
def fixedDualCut (W : Submodule (ZMod 2) (Module.Dual (ZMod 2) ρ.invariants)) :
    Submodule (ZMod 2) A := W.dualCoannihilator.map ρ.invariants.subtype

theorem fixedDualCut_le_invariants
    (W : Submodule (ZMod 2) (Module.Dual (ZMod 2) ρ.invariants)) :
    fixedDualCut ρ W ≤ ρ.invariants := by
  rintro a ⟨s,_,rfl⟩
  exact s.property

theorem fixedDualCut_finrank_add
    (W : Submodule (ZMod 2) (Module.Dual (ZMod 2) ρ.invariants)) :
    Module.finrank (ZMod 2) (fixedDualCut ρ W)+Module.finrank (ZMod 2) W =
      Module.finrank (ZMod 2) ρ.invariants := by
  have he := (ρ.invariants.equivSubtypeMap W.dualCoannihilator).finrank_eq
  have hd := Subspace.finrank_add_finrank_dualCoannihilator_eq W
  change Module.finrank (ZMod 2) W.dualCoannihilator =
    Module.finrank (ZMod 2) (fixedDualCut ρ W) at he
  omega

/-- Separating every full transpose forces the ENTIRE actual surviving
displacement slice of this cut to vanish. -/
theorem fixedDualCut_displacement_eq_bot
    (W : Submodule (ZMod 2) (Module.Dual (ZMod 2) ρ.invariants))
    (hsep : Separates (fixedDisplacementTranspose 2 ρ).range W) :
    displacementSlice ρ (fixedDualCut ρ W)=⊥ := by
  apply bot_unique
  intro f hf
  let f' : displacementSlice ρ ρ.invariants :=
    ⟨f,⟨hf.1,fun g => fixedDualCut_le_invariants ρ W (hf.2 g)⟩⟩
  have ht : fixedDisplacementTranspose 2 ρ f'=0 := by
    apply hsep _ ⟨f',rfl⟩
    intro ℓ hℓ
    apply AddMonoidHom.ext
    intro g
    obtain ⟨s,hs,hsg⟩ := hf.2 g.toMul
    have he : fixedDisplacementValue 2 ρ f' g.toMul=s := Subtype.ext hsg.symm
    change ℓ (fixedDisplacementValue 2 ρ f' g.toMul)=0
    rw [he]
    exact (Submodule.mem_dualCoannihilator s).mp hs ℓ hℓ
  have hf0 : f'=0 := fixedDisplacementTranspose_injective 2 ρ
    (ht.trans (map_zero (fixedDisplacementTranspose 2 ρ)).symm)
  exact congrArg Subtype.val hf0

/-- The quotient fixed dimension is exactly the separator dimension. -/
theorem fixedDualCut_quotient_invariants_finrank
    (W : Submodule (ZMod 2) (Module.Dual (ZMod 2) ρ.invariants))
    (hsep : Separates (fixedDisplacementTranspose 2 ρ).range W) :
    Module.finrank (ZMod 2) (centralQuotientRepresentation ρ
      (fixedDualCut ρ W) (fixedDualCut_le_invariants ρ W)).invariants =
        Module.finrank (ZMod 2) W := by
  rw [centralQuotient_invariants_finrank_of_slice_eq_bot ρ
    (fixedDualCut ρ W) (fixedDualCut_le_invariants ρ W)
    (fixedDualCut_displacement_eq_bot ρ W hsep)]
  have hd := fixedDualCut_finrank_add ρ W
  omega

section ActualPermutationSection

variable {X : Type} [Finite X] [MulAction G X] [MulAction.IsPretransitive G X]

/-- An actual central cut with a proved joint cost. The original section
dimension appears in the result; no small/large branch is assumed here. -/
theorem binary_permutationSection_exists_central_cut
    (hG : IsPGroup 2 G)
    (M : Subrepresentation (permutationFunctionRepresentation (ZMod 2) G X))
    (q : M.toRepresentation.IntertwiningMap ρ) (hq : Function.Surjective q)
    (x : X) (a : ℕ) (ha : 1≤a) (hdegree : Nat.card X=2^a) :
    ∃ (C : Submodule (ZMod 2) A) (hC : C≤ρ.invariants),
      displacementSlice ρ C=⊥ ∧
      2*Module.finrank (ZMod 2) C +
        4*Module.finrank (ZMod 2) (centralQuotientRepresentation ρ C hC).invariants ≤
          Module.finrank (ZMod 2) A + 2*(a-1).choose ((a-1)/2)+1 := by
  let t := Module.finrank (ZMod 2) ρ.invariants
  let ell := Module.finrank (ZMod 2) (displacementSlice ρ ρ.invariants)
  let D := 2*(a-1).choose ((a-1)/2)
  let J := D-t
  let L := (fixedDisplacementTranspose 2 ρ).range
  have hL : Module.finrank (ZMod 2) L=ell :=
    (LinearEquiv.ofInjective (fixedDisplacementTranspose 2 ρ)
      (fixedDisplacementTranspose_injective 2 ρ)).finrank_eq.symm
  have ht : t≤D := by
    have hb := binary_permutationSection_invariants_finrank_le ρ hG M q hq x a hdegree
    have hd := binary_middle_succ_le_twice (a-1)
    rw [Nat.sub_add_cancel ha] at hd
    exact hb.trans hd
  have hJ : ∀ χ : PrimeCharacters 2 G, χ≠0 →
      Module.finrank (ZMod 2) (imageLineSlice L χ)≤J := by
    intro χ hχ
    have hb := binary_permutationSection_character_line_slice_bound ρ hG M q hq
      x a ha hdegree χ hχ
    rw [(fixedDisplacementImageLineEquiv ρ χ).finrank_eq] at hb
    change t+Module.finrank (ZMod 2) (imageLineSlice L χ)≤D at hb
    exact Nat.le_sub_of_add_le (by omega)
  obtain ⟨W,hW,hsep⟩ := exists_separator_subspace_of_image_line_bound L J hJ
  refine ⟨fixedDualCut ρ W,fixedDualCut_le_invariants ρ W,
    fixedDualCut_displacement_eq_bot ρ W hsep,?_⟩
  rw [fixedDualCut_quotient_invariants_finrank ρ W hsep]
  have hcut := fixedDualCut_finrank_add ρ W
  have heA : t+ell≤Module.finrank (ZMod 2) A := by
    have he := Submodule.finrank_le
      (centralQuotientRepresentation ρ ρ.invariants le_rfl).invariants
    rw [← displacementSlice_invariants_finrank] at he
    have hdim := ρ.invariants.finrank_quotient_add_finrank
    change ell≤Module.finrank (ZMod 2) (A ⧸ ρ.invariants) at he
    omega
  rw [hL] at hW
  change Module.finrank (ZMod 2) (fixedDualCut ρ W)+Module.finrank (ZMod 2) W=t at hcut
  change 2*Module.finrank (ZMod 2) (fixedDualCut ρ W)+
    4*Module.finrank (ZMod 2) W ≤ Module.finrank (ZMod 2) A+D+1
  change 2*Module.finrank (ZMod 2) W≤ell+max 1 (D-t) at hW
  omega

/-- The same actual cut has the stated real Schur-capacity cost. -/
theorem binary_permutationSection_exists_central_cut_capacity
    (hG : IsPGroup 2 G)
    (M : Subrepresentation (permutationFunctionRepresentation (ZMod 2) G X))
    (q : M.toRepresentation.IntertwiningMap ρ) (hq : Function.Surjective q)
    (x : X) (a : ℕ) (ha : 1≤a) (hdegree : Nat.card X=2^a) :
    ∃ (C : Submodule (ZMod 2) A) (hC : C≤ρ.invariants),
      (2:ℝ)*Module.finrank (ZMod 2) C +
        4*representationSchurCapacity (centralQuotientRepresentation ρ C hC) ≤
          Module.finrank (ZMod 2) A+2*((a-1).choose ((a-1)/2):ℕ)+1 := by
  obtain ⟨C,hC,_,hc⟩ := binary_permutationSection_exists_central_cut
    ρ hG M q hq x a ha hdegree
  letI : Finite A := Finite.of_surjective q hq
  letI : Finite (A ⧸ C) := Finite.of_surjective C.mkQ C.mkQ_surjective
  refine ⟨C,hC,?_⟩
  rw [pGroup_representationSchurCapacity hG]
  exact_mod_cast hc

end ActualPermutationSection
end SymmetricSubgroupAsymptotics
