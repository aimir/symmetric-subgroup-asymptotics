import SymmetricSubgroupAsymptotics.TerminalIncidencePullback
import SymmetricSubgroupAsymptotics.CriticalProducts

/-!
# Original critical-product sections and terminal incidence

The section is the literal zero-central-coordinate section of the concrete
Heisenberg factors. Its defect has the original translation/shear order.
Its diagonal is the already verified hyperbolic square form.
-/

set_option autoImplicit false
noncomputable section
open scoped BigOperators Classical

namespace SymmetricSubgroupAsymptotics

/-- The actual multiplication defect of the zero-central-coordinate section. -/
def terminalHeisenbergBilinear (m : ℕ) :
    LinearMap.BilinForm (ZMod 2) ((Fin m → ZMod 2) × (Fin m → ZMod 2)) where
  toFun x :=
    { toFun := fun y => binaryDot x.2 y.1
      map_add' y z := by simp
      map_smul' s y := by simp [binaryDot,Finset.mul_sum,mul_left_comm] }
  map_add' x y := by
    apply LinearMap.ext
    intro z
    exact binaryDot_add_left x.2 y.2 z.1
  map_smul' s x := by
    apply LinearMap.ext
    intro y
    change binaryDot (s • x.2) y.1 = s * binaryDot x.2 y.1
    simp [binaryDot,Finset.mul_sum,mul_assoc]

/-- The same defect in the original interleaved critical quotient coordinates. -/
def terminalCriticalFactorBilinear (b : Bool) :
    LinearMap.BilinForm (ZMod 2) (CriticalFactorSpace b) :=
  (terminalHeisenbergBilinear (criticalFactorHalfRank b)).compl₁₂
    (criticalFactorChart b).symm.toLinearMap (criticalFactorChart b).symm.toLinearMap

theorem terminalCriticalFactorBilinear_diagonal (b : Bool) (v : CriticalFactorSpace b) :
    terminalCriticalFactorBilinear b v v=criticalFactorQuadratic b v := by
  have h := criticalFactorChart_quadratic b ((criticalFactorChart b).symm v)
  rw [(criticalFactorChart b).apply_symm_apply] at h
  exact h.symm

variable {ι : Type} [Fintype ι]

/-- The zero-central-coordinate section of the actual original product quotient. -/
def terminalCriticalSection (a : ℕ) (d : ι → Bool)
    (v : Multiplicative (Fin (criticalProductRank a d) → ZMod 2)) : CriticalProductGroup a d :=
  (Multiplicative.ofAdd ((criticalProductChart a d v.toAdd).1),
    fun i => ⟨((criticalFactorChart (d i)).symm ((criticalProductChart a d v.toAdd).2 i)).1,
      ((criticalFactorChart (d i)).symm ((criticalProductChart a d v.toAdd).2 i)).2,0⟩)

theorem terminalCriticalSection_projection (a : ℕ) (d : ι → Bool) (v) :
    criticalProductQuotient a d (terminalCriticalSection a d v)=v := by
  apply Multiplicative.toAdd.injective
  apply (criticalProductChart a d).injective
  rw [criticalProductQuotient_chart]
  apply Prod.ext
  · rfl
  · funext i
    exact (criticalFactorChart (d i)).apply_symm_apply _

/-- Original central coordinate tuple of the section multiplication defect. -/
def terminalCriticalCocycle (a : ℕ) (d : ι → Bool)
    (v w : Multiplicative (Fin (criticalProductRank a d) → ZMod 2)) : ι → ZMod 2 :=
  fun i => terminalCriticalFactorBilinear (d i)
    ((criticalProductChart a d v.toAdd).2 i) ((criticalProductChart a d w.toAdd).2 i)

theorem terminalCriticalSection_mul (a : ℕ) (d : ι → Bool) (v w) :
    terminalCriticalSection a d v * terminalCriticalSection a d w =
      terminalKernelInclusion (criticalProductQuotient a d) (criticalProductKernelChart a d)
        (Multiplicative.ofAdd (terminalCriticalCocycle a d v w)) * terminalCriticalSection a d (v*w) := by
  apply Prod.ext
  · change Multiplicative.ofAdd ((criticalProductChart a d v.toAdd).1) *
      Multiplicative.ofAdd ((criticalProductChart a d w.toAdd).1) =
        1 * Multiplicative.ofAdd ((criticalProductChart a d (v*w).toAdd).1)
    simp [← ofAdd_add]
  · funext i
    apply BinaryHeisenberg.ext
    · simp [terminalCriticalSection,terminalKernelInclusion,criticalProductKernelChart,
        BinaryHeisenberg.central]
    · simp [terminalCriticalSection,terminalKernelInclusion,criticalProductKernelChart,
        BinaryHeisenberg.central]
    · simp [terminalCriticalSection,terminalKernelInclusion,criticalProductKernelChart,
        BinaryHeisenberg.central,terminalCriticalCocycle,terminalCriticalFactorBilinear,
        terminalHeisenbergBilinear]

variable {U A T : Type} [AddCommGroup U] [Module (ZMod 2) U]
    [AddCommGroup A] [Module (ZMod 2) A] [Group T]

/-- The actual quotient record map on the complete product U×T. -/
def terminalCriticalRecordHom (a : ℕ) (d : ι → Bool) (β : T →* Multiplicative A)
    (p : (U × A) →ₗ[ZMod 2] CriticalProductSpace a d) :
    Multiplicative U × T →* Multiplicative (Fin (criticalProductRank a d) → ZMod 2) :=
  (AddMonoidHom.toMultiplicative
    (((criticalProductChart a d).symm.toLinearMap.comp p).toAddMonoidHom)).comp
      (terminalProductQuotient β)

@[simp] theorem terminalCriticalRecordHom_chart (a : ℕ) (d : ι → Bool)
    (β : T →* Multiplicative A) (p : (U × A) →ₗ[ZMod 2] CriticalProductSpace a d)
    (x : Multiplicative U × T) :
    criticalProductChart a d ((terminalCriticalRecordHom a d β p x).toAdd) =
      p (x.1.toAdd,(β x.2).toAdd) :=
  (criticalProductChart a d).apply_symm_apply _

/-- The original splitting annihilator of the actual product pullback,
written in the fixed original central-coordinate dual basis. -/
def terminalCriticalRecordAnnihilator (a : ℕ) (d : ι → Bool) (β : T →* Multiplicative A)
    (p : (U × A) →ₗ[ZMod 2] CriticalProductSpace a d) :
    Submodule (ZMod 2) (ι → ZMod 2) :=
  (terminalSplittingAnnihilator
    (terminalPullbackProjection (criticalProductQuotient a d) (terminalCriticalRecordHom a d β p))
    (terminalPullbackKernelChart (criticalProductQuotient a d) (criticalProductKernelChart a d)
      (terminalCriticalRecordHom a d β p))).map binaryDualCoordinates.toLinearMap

/-- Actual splitting characters give exactly the concrete scalar cocycles
needed by the ordered-incidence bound. This is proved from extending
characters on the literal pullback subgroup and its literal section. -/
theorem terminalCriticalRecordAnnihilator_class_zero (a : ℕ) (d : ι → Bool)
    (β : T →* Multiplicative A) (p : (U × A) →ₗ[ZMod 2] CriticalProductSpace a d)
    (b : ι → ZMod 2) (hb : b ∈ terminalCriticalRecordAnnihilator a d β p) :
    groupCohomology.H2π _
      (binaryCocyclePullback (terminalProductQuotient (U := U) β)
        (terminalBilinearCocycle
          (terminalRecordScalarBilinear (fun i => terminalCriticalFactorBilinear (d i)) p b)))=0 := by
  obtain ⟨ell,hell,rfl⟩ := hb
  rw [groupCohomology.H2π_eq_zero_iff]
  have h := terminalPullback_annihilator_coboundary (criticalProductQuotient a d)
    (criticalProductKernelChart a d) (terminalCriticalRecordHom a d β p)
    (terminalCriticalSection a d) (terminalCriticalSection_projection a d)
    (terminalCriticalCocycle a d) (terminalCriticalSection_mul a d) ell hell
  convert h using 1
  funext xy
  change (terminalRecordScalarBilinear (fun i => terminalCriticalFactorBilinear (d i)) p
    (binaryDualCoordinates ell)) (xy.1.1.toAdd,(β xy.1.2).toAdd)
      (xy.2.1.toAdd,(β xy.2.2).toAdd) =
    ell (terminalCriticalCocycle a d (terminalCriticalRecordHom a d β p xy.1)
      (terminalCriticalRecordHom a d β p xy.2))
  rw [binaryDualCoordinates_eval ell]
  simp [terminalRecordScalarBilinear,quadraticCoordinateMap,
    terminalCriticalCocycle,terminalCriticalRecordHom_chart,smul_eq_mul]


/-- Literal full-coordinate quotient records, tested against the original
annihilator of the actual critical-product pullback. Injectivity on U and
any extra regular-factor conditions may subsequently select a subfamily. -/
abbrev TerminalCriticalRecordMaps (a : ℕ) (d : ι → Bool) (β : T →* Multiplicative A)
    (B : Submodule (ZMod 2) (ι → ZMod 2)) :=
  {p : (U × A) →ₗ[ZMod 2] CriticalProductSpace a d //
    (∀ i, Function.Surjective (fun x => (p x).2 i)) ∧
      B ≤ terminalCriticalRecordAnnihilator a d β p}

private def terminalCriticalRecordEncode (a : ℕ) (d : ι → Bool)
    (β : T →* Multiplicative A) (B : Submodule (ZMod 2) (ι → ZMod 2))
    (p : TerminalCriticalRecordMaps (U := U) a d β B) :
    TerminalCohomologicalRecordMaps (U := U) (W := Fin a → ZMod 2) β B
      (fun i => terminalCriticalFactorBilinear (d i)) :=
  ⟨p.1,p.2.1,fun b => terminalCriticalRecordAnnihilator_class_zero a d β p.1 b.1
    (p.2.2 b.2)⟩

local instance {D F : Type*} [AddCommGroup D] [Module (ZMod 2) D]
    [AddCommGroup F] [Module (ZMod 2) F] [Finite D] [Finite F] :
    Finite (D →ₗ[ZMod 2] F) :=
  Finite.of_injective DFunLike.coe DFunLike.coe_injective

/-- Actual original-annihilator incidence, retaining the arbitrary exterior
and paying `72·2^τ` only at the independent pivots. -/
theorem terminalCriticalRecordMaps_count_le [Finite U] [Finite A]
    (a : ℕ) (d : ι → Bool) (β : T →* Multiplicative A) (hβ : Function.Surjective β)
    (B : Submodule (ZMod 2) (ι → ZMod 2)) :
    Nat.card (TerminalCriticalRecordMaps (U := U) a d β B) ≤
      (72 * 2^Module.finrank (ZMod 2) (binaryH2Pullback β).ker)^Module.finrank (ZMod 2) B *
        2^((Module.finrank (ZMod 2) U + Module.finrank (ZMod 2) A) *
          (criticalProductRank a d - 2*Module.finrank (ZMod 2) B)) := by
  have hi : Function.Injective (terminalCriticalRecordEncode (U := U) a d β B) := by
    intro p p' h
    have he : p.1=p'.1 := congrArg (fun z => z.1) h
    exact Subtype.ext he
  refine (Nat.card_le_card_of_injective _ hi).trans ?_
  simpa only [Module.finrank_pi,Fintype.card_fin,criticalProductRank] using
    terminalCohomologicalRecordMaps_count_le (U := U) (W := Fin a → ZMod 2) β hβ B
      (fun i => terminalCriticalFactorBilinear (d i))
      (fun i => criticalFactorQuadratic (d i))
      (fun i => terminalCriticalFactorBilinear_diagonal (d i))
      (fun i => criticalFactorQuadratic_nonsingular (d i))
      (fun i => criticalFactorSpace_finrank_ge_two (d i)) 72
      (fun i => criticalFactorQuadratic_isometry_card_le (d i))

/-- The canonical complete-exterior endpoint. Here τ is literally the
dimension of `ker(H²(A₂(T),F₂)→H²(T,F₂))`; no replacement by a name or
dimension-only condition enters the counted record predicate. -/
theorem terminalCriticalRecordMaps_canonical_count_le [Finite U] [Finite T]
    (a : ℕ) (d : ι → Bool) (B : Submodule (ZMod 2) (ι → ZMod 2)) :
    Nat.card (TerminalCriticalRecordMaps (U := U) a d
      (AddMonoidHom.toMultiplicativeRight (binaryAbelianizationMap T)) B) ≤
      (72 * 2^Module.finrank (ZMod 2) (terminalRestrictedInflationKernel T))^
        Module.finrank (ZMod 2) B *
        2^((Module.finrank (ZMod 2) U + binaryCharacterRank T) *
          (criticalProductRank a d - 2*Module.finrank (ZMod 2) B)) := by
  have hβ : Function.Surjective
      (AddMonoidHom.toMultiplicativeRight (binaryAbelianizationMap T)) := by
    intro x
    obtain ⟨t,ht⟩ := binaryAbelianizationMap_surjective T x.toAdd
    exact ⟨t.toMul,ht⟩
  simpa only [binaryAbelianization_finrank,terminalRestrictedInflationKernel] using
    terminalCriticalRecordMaps_count_le (U := U) a d
      (AddMonoidHom.toMultiplicativeRight (binaryAbelianizationMap T)) hβ B

end SymmetricSubgroupAsymptotics
