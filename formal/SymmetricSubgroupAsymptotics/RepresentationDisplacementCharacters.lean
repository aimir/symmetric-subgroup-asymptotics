import SymmetricSubgroupAsymptotics.RepresentationJointDisplacement
import SymmetricSubgroupAsymptotics.PrimeCharacterKernelDetection

/-! Transpose the complete original fixed-valued displacement space into
linear maps from the dual fixed space to original scalar characters.
The transpose is injective, and all character-image slices are exactly
the actual common-kernel slices. This is the interface for a pure linear
evaluation separator, without assuming a tensor decomposition. -/
set_option autoImplicit false
noncomputable section
namespace SymmetricSubgroupAsymptotics

variable (p : ℕ) [Fact p.Prime]
    {G A : Type} [Group G] [AddCommGroup A] [Module (ZMod p) A]
    (ρ : Representation (ZMod p) G A)

/-- Each value lies in the entire original fixed space. -/
def fixedDisplacementValue (f : displacementSlice ρ ρ.invariants) (g : G) :
    ρ.invariants := ⟨f.val g,f.property.2 g⟩

theorem fixedDisplacementValue_add (f f' : displacementSlice ρ ρ.invariants) (g : G) :
    fixedDisplacementValue p ρ (f+f') g =
      fixedDisplacementValue p ρ f g + fixedDisplacementValue p ρ f' g := by
  apply Subtype.ext
  rfl

theorem fixedDisplacementValue_smul (c : ZMod p)
    (f : displacementSlice ρ ρ.invariants) (g : G) :
    fixedDisplacementValue p ρ (c • f) g = c • fixedDisplacementValue p ρ f g := by
  apply Subtype.ext
  rfl

theorem fixedDisplacementValue_one (f : displacementSlice ρ ρ.invariants) :
    fixedDisplacementValue p ρ f 1=0 := by
  apply Subtype.ext
  obtain ⟨a,ha⟩ := f.property.1
  change f.val 1=0
  rw [← ha]
  change ρ 1 a-a=0
  rw [map_one]
  exact sub_self a

theorem fixedDisplacementValue_mul (f : displacementSlice ρ ρ.invariants) (g h : G) :
    fixedDisplacementValue p ρ f (g*h)=
      fixedDisplacementValue p ρ f g+fixedDisplacementValue p ρ f h := by
  apply Subtype.ext
  exact displacementSlice_invariants_mul ρ f g h

/-- A functional on the fixed space gives an actual original G-character. -/
def fixedDisplacementCharacter (f : displacementSlice ρ ρ.invariants)
    (ℓ : Module.Dual (ZMod p) ρ.invariants) : PrimeCharacters p G where
  toFun g := ℓ (fixedDisplacementValue p ρ f g.toMul)
  map_zero' := by
    change ℓ (fixedDisplacementValue p ρ f 1)=0
    rw [fixedDisplacementValue_one,map_zero]
  map_add' g h := by
    change ℓ (fixedDisplacementValue p ρ f (g.toMul*h.toMul)) = _
    rw [fixedDisplacementValue_mul,map_add]

/-- The full transpose, retaining all fixed functionals and all original
group elements. -/
def fixedDisplacementTranspose : displacementSlice ρ ρ.invariants →ₗ[ZMod p]
    (Module.Dual (ZMod p) ρ.invariants →ₗ[ZMod p] PrimeCharacters p G) where
  toFun f := {
    toFun := fixedDisplacementCharacter p ρ f
    map_add' := by intro ℓ μ; ext g; rfl
    map_smul' := by intro c ℓ; ext g; rfl }
  map_add' f f' := by
    apply LinearMap.ext
    intro ℓ
    apply AddMonoidHom.ext
    intro g
    change ℓ (fixedDisplacementValue p ρ (f+f') g.toMul) =
      ℓ (fixedDisplacementValue p ρ f g.toMul) +
      ℓ (fixedDisplacementValue p ρ f' g.toMul)
    rw [fixedDisplacementValue_add, map_add]
  map_smul' c f := by
    apply LinearMap.ext
    intro ℓ
    apply AddMonoidHom.ext
    intro g
    change ℓ (fixedDisplacementValue p ρ (c • f) g.toMul) =
      c • ℓ (fixedDisplacementValue p ρ f g.toMul)
    rw [fixedDisplacementValue_smul, map_smul]

@[simp] theorem fixedDisplacementTranspose_apply
    (f : displacementSlice ρ ρ.invariants)
    (ℓ : Module.Dual (ZMod p) ρ.invariants) (g : G) :
    fixedDisplacementTranspose p ρ f ℓ (Additive.ofMul g)=
      ℓ (fixedDisplacementValue p ρ f g) := rfl

variable [FiniteDimensional (ZMod p) A]

theorem fixedDisplacementTranspose_injective :
    Function.Injective (fixedDisplacementTranspose p ρ) := by
  intro f f' h
  apply Subtype.ext
  funext g
  have hv : fixedDisplacementValue p ρ f g = fixedDisplacementValue p ρ f' g := by
    apply (Module.evalEquiv (ZMod p) ρ.invariants).injective
    ext ℓ
    exact congrArg (fun T : Module.Dual (ZMod p) ρ.invariants →ₗ[ZMod p]
      PrimeCharacters p G => T ℓ (Additive.ofMul g)) h
  exact congrArg Subtype.val hv

variable [Finite G]

/-- Range containment in an arbitrary retained character space is
equivalent to vanishing on its literal original common group kernel. -/
theorem fixedDisplacementTranspose_range_le_iff
    (f : displacementSlice ρ ρ.invariants)
    (W : Submodule (ZMod p) (PrimeCharacters p G)) :
    (fixedDisplacementTranspose p ρ f).range ≤ W ↔
      ∀ g : G, g ∈ (retainedCharacterEvaluation p (G := G) (V := W)
        (primeCharacterSubspaceEmbedding p (G := G) W)).ker → f.val g=0 := by
  constructor
  · intro h g hg
    have hv : fixedDisplacementValue p ρ f g=0 := by
      apply (Module.evalEquiv (ZMod p) ρ.invariants).injective
      ext ℓ
      have hℓ : fixedDisplacementTranspose p ρ f ℓ ∈ W := h ⟨ℓ,rfl⟩
      change ℓ (fixedDisplacementValue p ρ f g)=ℓ 0
      rw [map_zero]
      exact (primeCharacter_mem_iff_vanishes_retained_kernel p W _).mp hℓ g hg
    exact congrArg Subtype.val hv
  · intro h χ hχ
    obtain ⟨ℓ,rfl⟩ := hχ
    apply (primeCharacter_mem_iff_vanishes_retained_kernel p W _).mpr
    intro g hg
    rw [fixedDisplacementTranspose_apply]
    have hv : fixedDisplacementValue p ρ f g=0 := Subtype.ext (h g hg)
    rw [hv,map_zero]

/-- The actual slice inside the complete displacement domain whose
transpose has its entire image in W. -/
def fixedDisplacementCharacterSlice (W : Submodule (ZMod p) (PrimeCharacters p G)) :
    Submodule (ZMod p) (displacementSlice ρ ρ.invariants) where
  carrier := {f | (fixedDisplacementTranspose p ρ f).range≤W}
  zero_mem' := by
    rintro χ ⟨ℓ,rfl⟩
    simpa only [map_zero,LinearMap.zero_apply] using W.zero_mem
  add_mem' := by
    intro f f' hf hf' χ hχ
    obtain ⟨ℓ,rfl⟩ := hχ
    simpa only [map_add,LinearMap.add_apply] using
      W.add_mem (hf ⟨ℓ,rfl⟩) (hf' ⟨ℓ,rfl⟩)
  smul_mem' := by
    intro c f hf χ hχ
    obtain ⟨ℓ,rfl⟩ := hχ
    simpa only [map_smul,LinearMap.smul_apply] using W.smul_mem c (hf ⟨ℓ,rfl⟩)

/-- The exact image-slice/common-kernel equivalence, including every
displacement in the full slice. -/
def fixedDisplacementCharacterSliceEquiv
    (W : Submodule (ZMod p) (PrimeCharacters p G)) :
    fixedDisplacementCharacterSlice p ρ W ≃ₗ[ZMod p]
      displacementJointSlice ρ (retainedCharacterEvaluation p (G := G) (V := W)
        (primeCharacterSubspaceEmbedding p (G := G) W)).ker where
  toFun f := ⟨f.val.val,⟨f.val.property,fun g =>
    (fixedDisplacementTranspose_range_le_iff p ρ f.val W).mp f.property g.val g.property⟩⟩
  invFun f := ⟨⟨f.val,f.property.1⟩,
    (fixedDisplacementTranspose_range_le_iff p ρ ⟨f.val,f.property.1⟩ W).mpr
      (fun g hg => f.property.2 ⟨g,hg⟩)⟩
  left_inv := fun _ => rfl
  right_inv := fun _ => rfl
  map_add' := fun _ _ => rfl
  map_smul' := fun _ _ => rfl

theorem fixedDisplacementCharacterSlice_finrank
    (W : Submodule (ZMod p) (PrimeCharacters p G)) :
    Module.finrank (ZMod p) (fixedDisplacementCharacterSlice p ρ W)=
      Module.finrank (ZMod p)
        (displacementJointSlice ρ (retainedCharacterEvaluation p (G := G) (V := W)
          (primeCharacterSubspaceEmbedding p (G := G) W)).ker) :=
  (fixedDisplacementCharacterSliceEquiv p ρ W).finrank_eq

end SymmetricSubgroupAsymptotics
