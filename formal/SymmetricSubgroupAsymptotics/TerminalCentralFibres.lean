import SymmetricSubgroupAsymptotics.AllLifts
import Mathlib.RepresentationTheory.Homological.GroupCohomology.LowDegree

/-!
# Retained scalar splitting obstruction of an actual central extension

Scalar characters are literal homomorphisms. Their restriction image is an
actual subspace of the original kernel dual. The section-defect criterion
below identifies it with scalar coboundaries of this very extension.
-/

set_option autoImplicit false
noncomputable section
open scoped BigOperators Classical

namespace SymmetricSubgroupAsymptotics

/-- Actual binary characters of a possibly nonabelian group. -/
abbrev terminalCharacters (X : Type*) [Group X] := Additive X →+ ZMod 2

variable {X Y K : Type*} [Group X] [Group Y] [AddCommGroup K] [Module (ZMod 2) K]
    (π : X →* Y) (e : Multiplicative K ≃* π.ker)

/-- The specified original kernel chart, followed by its literal inclusion. -/
def terminalKernelInclusion : Multiplicative K →* X := π.ker.subtype.comp e.toMonoidHom

omit [Module (ZMod 2) K] in
theorem terminalKernelInclusion_injective : Function.Injective (terminalKernelInclusion π e) :=
  Subtype.val_injective.comp e.injective

omit [Module (ZMod 2) K] in
@[simp] theorem terminalKernelInclusion_projection (k : Multiplicative K) :
    π (terminalKernelInclusion π e k) = 1 := (e k).2

/-- Restriction retains a scalar character on the original kernel space. -/
def terminalCharacterRestriction : terminalCharacters X →ₗ[ZMod 2] Module.Dual (ZMod 2) K where
  toFun χ := (χ.comp (MonoidHom.toAdditiveRight (terminalKernelInclusion π e))).toZModLinearMap 2
  map_add' _ _ := by ext k; rfl
  map_smul' _ _ := by ext k; rfl

@[simp] theorem terminalCharacterRestriction_apply (χ : terminalCharacters X) (k : K) :
    terminalCharacterRestriction π e χ k =
      χ (Additive.ofMul (terminalKernelInclusion π e (Multiplicative.ofAdd k))) := rfl

/-- The retained scalar splitting annihilator, as a literal subspace of K*. -/
def terminalSplittingAnnihilator : Submodule (ZMod 2) (Module.Dual (ZMod 2) K) :=
  (terminalCharacterRestriction π e).range

theorem mem_terminalSplittingAnnihilator (ell : Module.Dual (ZMod 2) K) :
    ell ∈ terminalSplittingAnnihilator π e ↔
      ∃ χ : terminalCharacters X, ∀ k : K,
        χ (Additive.ofMul (terminalKernelInclusion π e (Multiplicative.ofAdd k))) = ell k := by
  change (∃ χ, terminalCharacterRestriction π e χ = ell) ↔ _
  constructor
  · rintro ⟨χ,hχ⟩
    exact ⟨χ,fun k => LinearMap.congr_fun hχ k⟩
  · rintro ⟨χ,hχ⟩
    exact ⟨χ,LinearMap.ext hχ⟩

variable (hπ : Function.Surjective π)

/-- A normalized actual set section, chosen from surjectivity. -/
def terminalSection (y : Y) : X := if y = 1 then 1 else (hπ y).choose

@[simp] theorem terminalSection_one : terminalSection π hπ 1 = 1 := by simp [terminalSection]

@[simp] theorem terminalSection_projection (y : Y) : π (terminalSection π hπ y) = y := by
  by_cases hy : y = 1
  · subst y; simp
  · simpa [terminalSection,hy] using (hπ y).choose_spec

/-- The actual defect of the chosen section, valued in the original K. -/
def terminalSectionDefect (y z : Y) : K :=
  (e.symm ⟨terminalSection π hπ y * terminalSection π hπ z *
      (terminalSection π hπ (y*z))⁻¹,by simp⟩).toAdd

/-- Kernel coordinate in the decomposition x=k s(πx). -/
def terminalKernelCoordinate (x : X) : K :=
  (e.symm ⟨x * (terminalSection π hπ (π x))⁻¹,by simp⟩).toAdd

omit [Module (ZMod 2) K] in
@[simp] theorem terminalKernelInclusion_defect (y z : Y) :
    terminalKernelInclusion π e (Multiplicative.ofAdd (terminalSectionDefect π e hπ y z)) =
      terminalSection π hπ y * terminalSection π hπ z * (terminalSection π hπ (y*z))⁻¹ := by
  exact congrArg Subtype.val (e.apply_symm_apply _)

omit [Module (ZMod 2) K] in
@[simp] theorem terminalKernelInclusion_coordinate (x : X) :
    terminalKernelInclusion π e (Multiplicative.ofAdd (terminalKernelCoordinate π e hπ x)) =
      x * (terminalSection π hπ (π x))⁻¹ := by
  exact congrArg Subtype.val (e.apply_symm_apply _)

omit [Module (ZMod 2) K] in
@[simp] theorem terminalKernelCoordinate_one : terminalKernelCoordinate π e hπ 1 = 0 := by
  apply Multiplicative.ofAdd.injective
  apply terminalKernelInclusion_injective π e
  simp

omit [Module (ZMod 2) K] in
@[simp] theorem terminalKernelCoordinate_inclusion (k : K) :
    terminalKernelCoordinate π e hπ (terminalKernelInclusion π e (Multiplicative.ofAdd k)) = k := by
  apply Multiplicative.ofAdd.injective
  apply terminalKernelInclusion_injective π e
  simp

/-- A scalar coboundary witness for the exact section defect. -/
def TerminalScalarCoboundary (ell : Module.Dual (ZMod 2) K) : Prop :=
  ∃ b : Y → ZMod 2, b 1 = 0 ∧ ∀ y z,
    ell (terminalSectionDefect π e hπ y z) = b y + b z - b (y*z)

theorem terminalScalarCoboundary_of_extend (ell : Module.Dual (ZMod 2) K)
    (χ : terminalCharacters X)
    (hχ : ∀ k : K, χ (Additive.ofMul (terminalKernelInclusion π e (Multiplicative.ofAdd k))) = ell k) :
    TerminalScalarCoboundary π e hπ ell := by
  refine ⟨fun y => χ (Additive.ofMul (terminalSection π hπ y)),by simp,?_⟩
  intro y z
  rw [← hχ,terminalKernelInclusion_defect]
  simp only [ofMul_mul,ofMul_inv,map_add,map_neg,sub_eq_add_neg]

variable (hcentral : π.ker ≤ Subgroup.center X)

omit [Module (ZMod 2) K] in
/-- Centrality gives the exact multiplication law for section coordinates. -/
theorem terminalKernelCoordinate_mul (hcentral : π.ker ≤ Subgroup.center X) (x z : X) :
    terminalKernelCoordinate π e hπ (x*z) = terminalKernelCoordinate π e hπ x +
      terminalKernelCoordinate π e hπ z + terminalSectionDefect π e hπ (π x) (π z) := by
  apply Multiplicative.ofAdd.injective
  apply terminalKernelInclusion_injective π e
  simp only [ofAdd_add,map_mul,terminalKernelInclusion_coordinate,
    terminalKernelInclusion_defect]
  have hc : terminalSection π hπ (π x) * (z * (terminalSection π hπ (π z))⁻¹) =
      (z * (terminalSection π hπ (π z))⁻¹) * terminalSection π hπ (π x) := by
    have hk : z * (terminalSection π hπ (π z))⁻¹ ∈ π.ker := by simp
    exact Subgroup.mem_center_iff.mp (hcentral hk) _
  calc
    x*z*(terminalSection π hπ (π x*π z))⁻¹ =
        (x*(terminalSection π hπ (π x))⁻¹) *
          (terminalSection π hπ (π x) * (z*(terminalSection π hπ (π z))⁻¹)) *
          (terminalSection π hπ (π z)) * (terminalSection π hπ (π x*π z))⁻¹ := by group
    _ = _ := by rw [hc]; group

omit [Module (ZMod 2) K] in
@[simp] theorem terminalKernelCoordinate_section (y : Y) :
    terminalKernelCoordinate π e hπ (terminalSection π hπ y) = 0 := by
  apply Multiplicative.ofAdd.injective
  apply terminalKernelInclusion_injective π e
  simp

omit [Module (ZMod 2) K] in
@[simp] theorem terminalSectionDefect_one_left (y : Y) :
    terminalSectionDefect π e hπ 1 y = 0 := by
  apply Multiplicative.ofAdd.injective
  apply terminalKernelInclusion_injective π e
  simp

omit [Module (ZMod 2) K] in
@[simp] theorem terminalSectionDefect_one_right (y : Y) :
    terminalSectionDefect π e hπ y 1 = 0 := by
  apply Multiplicative.ofAdd.injective
  apply terminalKernelInclusion_injective π e
  simp

omit [Module (ZMod 2) K] in
/-- The actual section defect satisfies the normalized central 2-cocycle law. -/
theorem terminalSectionDefect_cocycle (hcentral : π.ker ≤ Subgroup.center X) (x y z : Y) :
    terminalSectionDefect π e hπ x y + terminalSectionDefect π e hπ (x*y) z =
      terminalSectionDefect π e hπ y z + terminalSectionDefect π e hπ x (y*z) := by
  have h := congrArg (terminalKernelCoordinate π e hπ)
    (mul_assoc (terminalSection π hπ x) (terminalSection π hπ y) (terminalSection π hπ z))
  simpa only [terminalKernelCoordinate_mul π e hπ hcentral,
    terminalKernelCoordinate_section,zero_add,add_zero,map_mul,terminalSection_projection] using h

/-- A scalar coboundary supplies an actual extending group character. -/
def terminalCharacterOfCoboundary (ell : Module.Dual (ZMod 2) K)
    (b : Y → ZMod 2) (hb1 : b 1 = 0)
    (hb : ∀ y z, ell (terminalSectionDefect π e hπ y z) = b y + b z - b (y*z)) :
    terminalCharacters X where
  toFun x := ell (terminalKernelCoordinate π e hπ x.toMul) + b (π x.toMul)
  map_zero' := by simp [hb1]
  map_add' x z := by
    change ell (terminalKernelCoordinate π e hπ (x.toMul*z.toMul)) + b (π (x.toMul*z.toMul)) = _
    rw [terminalKernelCoordinate_mul π e hπ hcentral,map_add,map_add,hb,map_mul]
    abel

/-- Membership in the retained subspace is exactly vanishing of the
scalar section-defect class, expressed by an actual coboundary witness. -/
theorem terminalSplittingAnnihilator_iff_coboundary (hcentral : π.ker ≤ Subgroup.center X) (ell : Module.Dual (ZMod 2) K) :
    ell ∈ terminalSplittingAnnihilator π e ↔ TerminalScalarCoboundary π e hπ ell := by
  rw [mem_terminalSplittingAnnihilator]
  constructor
  · rintro ⟨χ,hχ⟩
    exact terminalScalarCoboundary_of_extend π e hπ ell χ hχ
  · rintro ⟨b,hb1,hb⟩
    refine ⟨terminalCharacterOfCoboundary π e hπ hcentral ell b hb1 hb,?_⟩
    intro k
    simp [terminalCharacterOfCoboundary,hb1]

section VectorCoefficients

variable {A : Type*} [AddCommGroup A] [Module (ZMod 2) A]

/-- Restriction of an actual vector-valued group homomorphism. -/
def terminalVectorRestriction : (Additive X →+ A) →ₗ[ZMod 2] (K →ₗ[ZMod 2] A) where
  toFun f := (f.comp (MonoidHom.toAdditiveRight (terminalKernelInclusion π e))).toZModLinearMap 2
  map_add' _ _ := by ext k; rfl
  map_smul' _ _ := by ext k; rfl

@[simp] theorem terminalVectorRestriction_apply (f : Additive X →+ A) (k : K) :
    terminalVectorRestriction π e f k =
      f (Additive.ofMul (terminalKernelInclusion π e (Multiplicative.ofAdd k))) := rfl

/-- Scalar splitting tests determine vector-valued extension, with all
characters retained before any dimension or positive upper bound is taken. -/
theorem terminalVectorExtension_iff_dual [FiniteDimensional (ZMod 2) A]
    (ψ : K →ₗ[ZMod 2] A) :
    ψ ∈ (terminalVectorRestriction π e (A := A)).range ↔
      ∀ ell : Module.Dual (ZMod 2) A, ell.comp ψ ∈ terminalSplittingAnnihilator π e := by
  constructor
  · rintro ⟨f,hf⟩ ell
    rw [mem_terminalSplittingAnnihilator]
    refine ⟨ell.toAddMonoidHom.comp f,?_⟩
    intro k
    have h := LinearMap.congr_fun hf k
    exact congrArg ell h
  · intro h
    let b := Module.finBasis (ZMod 2) A
    have hext (i : Fin (Module.finrank (ZMod 2) A)) :
        ∃ χ : terminalCharacters X, ∀ k : K,
          χ (Additive.ofMul (terminalKernelInclusion π e (Multiplicative.ofAdd k))) =
            b.coord i (ψ k) := by
      exact (mem_terminalSplittingAnnihilator π e (b.coord i |>.comp ψ)).mp (h (b.coord i))
    choose χ hχ using hext
    let f : Additive X →+ A :=
      { toFun := fun x => b.equivFun.symm (fun i => χ i x)
        map_zero' := by simp
        map_add' := fun x y => by
          rw [← map_add]
          apply congrArg b.equivFun.symm
          funext i
          exact (χ i).map_add x y }
    refine ⟨f,LinearMap.ext fun k => ?_⟩
    change f (Additive.ofMul (terminalKernelInclusion π e (Multiplicative.ofAdd k))) = ψ k
    apply b.equivFun.injective
    funext i
    change b.equivFun (b.equivFun.symm (fun j => χ j
      (Additive.ofMul (terminalKernelInclusion π e (Multiplicative.ofAdd k))))) i = b.equivFun (ψ k) i
    rw [b.equivFun.apply_symm_apply]
    exact hχ i k

/-- For a kernel intersection W the retained condition is precisely that
all quotient coefficient characters belong to the splitting annihilator. -/
theorem terminalKernelQuotientExtension_iff (W : Submodule (ZMod 2) K)
    [FiniteDimensional (ZMod 2) K] :
    W.mkQ ∈ (terminalVectorRestriction π e (A := K ⧸ W)).range ↔
      ∀ ell : Module.Dual (ZMod 2) (K ⧸ W),
        ell.comp W.mkQ ∈ terminalSplittingAnnihilator π e :=
  terminalVectorExtension_iff_dual π e W.mkQ

end VectorCoefficients

/-- The exact retained original-dual condition for a proposed kernel
intersection, before replacing any subspace by its dimension. -/
theorem terminalKernelQuotientExtension_iff_annihilator
    [FiniteDimensional (ZMod 2) K] (W : Submodule (ZMod 2) K) :
    W.mkQ ∈ (terminalVectorRestriction π e (A := K ⧸ W)).range ↔
      W.dualAnnihilator ≤ terminalSplittingAnnihilator π e := by
  rw [terminalKernelQuotientExtension_iff,← W.range_dualMap_mkQ_eq]
  constructor
  · intro h ell hell
    obtain ⟨f,rfl⟩ := hell
    exact h f
  · intro h ell
    exact h ⟨ell,rfl⟩

end SymmetricSubgroupAsymptotics
