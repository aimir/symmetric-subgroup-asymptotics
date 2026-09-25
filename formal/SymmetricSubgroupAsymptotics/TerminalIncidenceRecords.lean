import SymmetricSubgroupAsymptotics.TerminalIncidence

/-!
# Ordered terminal records with actual cohomological splitting tests

The counted objects are literal linear maps on U⊕A, surjective on every
quadratic factor, for which each retained scalar bilinear cocycle becomes
an actual coboundary after pullback to U×T. The whole nonabelian exterior
is retained in that test. This module bounds these maps; identifying them
with the original critical-product extension records is a separate step.
-/

set_option autoImplicit false
noncomputable section
open scoped BigOperators Classical

namespace SymmetricSubgroupAsymptotics

variable {U A W ι : Type} [AddCommGroup U] [Module (ZMod 2) U] [Finite U]
    [AddCommGroup A] [Module (ZMod 2) A] [Finite A]
    [AddCommGroup W] [Module (ZMod 2) W] [Finite W] [Fintype ι]
    {V : ι → Type} [∀ i, AddCommGroup (V i)] [∀ i, Module (ZMod 2) (V i)]
    [∀ i, Finite (V i)]
    {T : Type} [Group T]

local instance {D F : Type*} [AddCommGroup D] [Module (ZMod 2) D]
    [AddCommGroup F] [Module (ZMod 2) F] [Finite D] [Finite F] :
    Finite (D →ₗ[ZMod 2] F) :=
  Finite.of_injective DFunLike.coe DFunLike.coe_injective

/-- The retained scalar combination of the original coordinate cocycles. -/
def terminalRecordScalarBilinear
    (c : ∀ i, LinearMap.BilinForm (ZMod 2) (V i))
    (p : (U × A) →ₗ[ZMod 2] (W × ∀ i, V i)) (b : ι → ZMod 2) :
    LinearMap.BilinForm (ZMod 2) (U × A) :=
  ∑ i, b i • (c i).compl₁₂ (quadraticCoordinateMap p i) (quadraticCoordinateMap p i)

/-- Actual surjective coordinate maps satisfying every retained scalar
splitting test in the cohomology of the complete U×T source. -/
abbrev TerminalCohomologicalRecordMaps (β : T →* Multiplicative A)
    (B : Submodule (ZMod 2) (ι → ZMod 2))
    (c : ∀ i, LinearMap.BilinForm (ZMod 2) (V i)) :=
  {p : (U × A) →ₗ[ZMod 2] (W × ∀ i, V i) //
    (∀ i, Function.Surjective (fun x => (p x).2 i)) ∧
    ∀ b : B, groupCohomology.H2π _
      (binaryCocyclePullback (terminalProductQuotient (U := U) β)
        (terminalBilinearCocycle (terminalRecordScalarBilinear c p b.1))) = 0}

private def terminalCohomologicalRecordEncode (β : T →* Multiplicative A)
    (hβ : Function.Surjective β) (B : Submodule (ZMod 2) (ι → ZMod 2))
    (c : ∀ i, LinearMap.BilinForm (ZMod 2) (V i))
    (q : ∀ i, QuadraticForm (ZMod 2) (V i)) (hc : ∀ i v, c i v v=q i v)
    (p : TerminalCohomologicalRecordMaps (U := U) (W := W) β B c) :
    TerminalQuadraticRelationMaps (W := W) (terminalAllowedDiagonals (U := U) β) B q :=
  ⟨p.1,p.2.1,by
    intro b
    have h := terminal_bilinear_diagonal_mem_allowed β hβ
      (terminalRecordScalarBilinear c p.1 b.1) (p.2.2 b)
    convert h using 1
    ext x
    simp [terminalRecordScalarBilinear,quadraticCoordinateMap,hc,smul_eq_mul]⟩

/-- The full ordered-map estimate, with τ literally the dimension of the
original inflation kernel. The realization and pivot counts are proved,
not supplied as assumptions about this record family. -/
theorem terminalCohomologicalRecordMaps_count_le (β : T →* Multiplicative A)
    (hβ : Function.Surjective β) (B : Submodule (ZMod 2) (ι → ZMod 2))
    (c : ∀ i, LinearMap.BilinForm (ZMod 2) (V i))
    (q : ∀ i, QuadraticForm (ZMod 2) (V i)) (hc : ∀ i v, c i v v=q i v)
    (hq : ∀ i, (q i).polarBilin.SeparatingLeft)
    (hv : ∀ i, 2 ≤ Module.finrank (ZMod 2) (V i))
    (M : ℕ) (hM : ∀ i, Nat.card ((q i).IsometryEquiv (q i)) ≤ M) :
    Nat.card (TerminalCohomologicalRecordMaps (U := U) (W := W) β B c) ≤
      (M * 2^Module.finrank (ZMod 2) (binaryH2Pullback β).ker)^Module.finrank (ZMod 2) B *
        2^((Module.finrank (ZMod 2) U + Module.finrank (ZMod 2) A) *
          (Module.finrank (ZMod 2) W + ∑ i, Module.finrank (ZMod 2) (V i) -
            2*Module.finrank (ZMod 2) B)) := by
  have hinj : Function.Injective (terminalCohomologicalRecordEncode
      (U := U) (W := W) β hβ B c q hc) := by
    intro p p' h
    have he : p.1 = p'.1 := congrArg (fun z => z.1) h
    exact Subtype.ext he
  calc
    _ ≤ Nat.card (TerminalQuadraticRelationMaps (W := W) (terminalAllowedDiagonals (U := U) β) B q) :=
      Nat.card_le_card_of_injective _ hinj
    _ ≤ _ := by
      simpa only [Module.finrank_prod] using terminalQuadraticRelationMaps_count_le
        (W := W) (terminalAllowedDiagonals (U := U) β) B q hq hv M
        (Module.finrank (ZMod 2) (binaryH2Pullback β).ker) hM
        (terminalAllowedDiagonals_finrank_le β)

/-- Canonical complete-exterior version: the kernel is exactly the retained
H² inflation kernel previously defined for A₂(T), and the domain dimension
is u+d₂(T). -/
theorem terminalCohomologicalRecordMaps_canonical_count_le [Finite T]
    (B : Submodule (ZMod 2) (ι → ZMod 2))
    (c : ∀ i, LinearMap.BilinForm (ZMod 2) (V i))
    (q : ∀ i, QuadraticForm (ZMod 2) (V i)) (hc : ∀ i v, c i v v=q i v)
    (hq : ∀ i, (q i).polarBilin.SeparatingLeft)
    (hv : ∀ i, 2 ≤ Module.finrank (ZMod 2) (V i))
    (M : ℕ) (hM : ∀ i, Nat.card ((q i).IsometryEquiv (q i)) ≤ M) :
    Nat.card (TerminalCohomologicalRecordMaps (U := U) (W := W)
      (AddMonoidHom.toMultiplicativeRight (binaryAbelianizationMap T)) B c) ≤
      (M * 2^Module.finrank (ZMod 2) (terminalRestrictedInflationKernel T))^
        Module.finrank (ZMod 2) B *
        2^((Module.finrank (ZMod 2) U + binaryCharacterRank T) *
          (Module.finrank (ZMod 2) W + ∑ i, Module.finrank (ZMod 2) (V i) -
            2*Module.finrank (ZMod 2) B)) := by
  have hβ : Function.Surjective
      (AddMonoidHom.toMultiplicativeRight (binaryAbelianizationMap T)) := by
    intro a
    obtain ⟨t,ht⟩ := binaryAbelianizationMap_surjective T a.toAdd
    exact ⟨t.toMul,ht⟩
  simpa only [binaryAbelianization_finrank,terminalRestrictedInflationKernel] using
    terminalCohomologicalRecordMaps_count_le (U := U) (W := W)
      (AddMonoidHom.toMultiplicativeRight (binaryAbelianizationMap T)) hβ B c q hc hq hv M hM

end SymmetricSubgroupAsymptotics
