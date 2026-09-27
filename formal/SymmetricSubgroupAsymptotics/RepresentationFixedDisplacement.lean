import Mathlib.RepresentationTheory.Invariants
import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas
import Mathlib.LinearAlgebra.Isomorphisms
import Mathlib.Tactic.Abel

/-! The displacement of the original representation gives the exact
fixed-quotient dimension formula without a cohomology long exact sequence.
All slices are literal intersections in the original function space.
A separator must annihilate the stated slice; none is assumed to exist. -/
set_option autoImplicit false
noncomputable section
open scoped Classical
attribute [local instance] Fintype.ofFinite
namespace SymmetricSubgroupAsymptotics

variable {k G A : Type} [Field k] [Group G] [AddCommGroup A] [Module k A]
    (ρ : Representation k G A)

/-- The original displacement, with every original group element retained. -/
def representationDisplacement : A →ₗ[k] (G → A) where
  toFun a g := ρ g a-a
  map_add' a b := by
    funext g
    change ρ g (a+b)-(a+b)=(ρ g a-a)+(ρ g b-b)
    rw [map_add]
    abel
  map_smul' c a := by
    funext g
    change ρ g (c • a)-c • a=c • (ρ g a-a)
    rw [map_smul,smul_sub]

/-- Functions taking their values in the literal specified subspace. -/
def subspaceValuedFunctions (C : Submodule k A) : Submodule k (G → A) where
  carrier := {f | ∀ g, f g∈C}
  zero_mem' := fun _ => C.zero_mem
  add_mem' := by
    intro f f' hf hf' g
    exact C.add_mem (hf g) (hf' g)
  smul_mem' := by
    intro c f hf g
    exact C.smul_mem c (hf g)

/-- Actual vectors whose entire displacement lies in C. -/
def displacementPreimage (C : Submodule k A) : Submodule k A :=
  (subspaceValuedFunctions (G := G) C).comap (representationDisplacement ρ)

/-- The actual image slice; it is not a supplied tensor or cohomology model. -/
def displacementSlice (C : Submodule k A) : Submodule k (G → A) :=
  (representationDisplacement ρ).range ⊓ subspaceValuedFunctions (G := G) C

theorem representationDisplacement_ker : (representationDisplacement ρ).ker=ρ.invariants := by
  ext a
  change (fun g => ρ g a-a)=(0 : G → A) ↔ ∀ g, ρ g a=a
  simp only [funext_iff,Pi.zero_apply,sub_eq_zero]

theorem invariants_le_displacementPreimage (C : Submodule k A) :
    ρ.invariants≤displacementPreimage ρ C := by
  intro a ha g
  change ρ g a-a∈C
  rw [ha g,sub_self]
  exact C.zero_mem

theorem centralCut_le_displacementPreimage (C : Submodule k A) (hC : C≤ρ.invariants) :
    C≤displacementPreimage ρ C :=
  hC.trans (invariants_le_displacementPreimage ρ C)

/-- The original quotient representation, for a cut inside the entire
original fixed space. The quotient need not split. -/
def centralQuotientRepresentation (C : Submodule k A) (hC : C≤ρ.invariants) :
    Representation k G (A ⧸ C) :=
  ρ.quotient C (fun g a ha => by
    change ρ g a∈C
    rw [hC ha g]
    exact ha)

@[simp] theorem centralQuotientRepresentation_apply_mk
    (C : Submodule k A) (hC : C≤ρ.invariants) (g : G) (a : A) :
    centralQuotientRepresentation ρ C hC g (C.mkQ a)=C.mkQ (ρ g a) := rfl

/-- The complete preimage of quotient invariants is exactly the original
displacement constraint, with no dimension or counting hypothesis. -/
theorem centralQuotient_mem_invariants_iff (C : Submodule k A) (hC : C≤ρ.invariants)
    (a : A) :
    C.mkQ a∈(centralQuotientRepresentation ρ C hC).invariants ↔
      a∈displacementPreimage ρ C := by
  change (∀ g, C.mkQ (ρ g a)=C.mkQ a) ↔ ∀ g, ρ g a-a∈C
  exact forall_congr' (fun _ => Submodule.Quotient.eq C)

def displacementToSlice (C : Submodule k A) :
    displacementPreimage ρ C →ₗ[k] displacementSlice ρ C :=
  ((representationDisplacement ρ).comp (displacementPreimage ρ C).subtype).codRestrict
    (displacementSlice ρ C) (fun a => ⟨⟨a,rfl⟩,a.property⟩)

theorem displacementToSlice_surjective (C : Submodule k A) :
    Function.Surjective (displacementToSlice ρ C) := by
  intro f
  obtain ⟨a,ha⟩ := f.property.1
  have haP : a∈displacementPreimage ρ C := by
    change representationDisplacement ρ a∈subspaceValuedFunctions (G := G) C
    rw [ha]
    exact f.property.2
  exact ⟨⟨a,haP⟩,Subtype.ext ha⟩

theorem displacementToSlice_ker (C : Submodule k A) :
    (displacementToSlice ρ C).ker=
      ρ.invariants.comap (displacementPreimage ρ C).subtype := by
  ext a
  rw [LinearMap.mem_ker,Subtype.ext_iff]
  change representationDisplacement ρ (a:A)=0 ↔ (a:A)∈ρ.invariants
  rw [← LinearMap.mem_ker,representationDisplacement_ker]

/-- Restriction of the actual quotient map onto its entire fixed space. -/
def displacementToQuotientFixed (C : Submodule k A) (hC : C≤ρ.invariants) :
    displacementPreimage ρ C →ₗ[k] (centralQuotientRepresentation ρ C hC).invariants :=
  (C.mkQ.comp (displacementPreimage ρ C).subtype).codRestrict
    (centralQuotientRepresentation ρ C hC).invariants
      (fun a => (centralQuotient_mem_invariants_iff ρ C hC a).mpr a.property)

theorem displacementToQuotientFixed_surjective (C : Submodule k A) (hC : C≤ρ.invariants) :
    Function.Surjective (displacementToQuotientFixed ρ C hC) := by
  intro v
  obtain ⟨a,ha⟩ := C.mkQ_surjective (v : A ⧸ C)
  have haP : a∈displacementPreimage ρ C := by
    apply (centralQuotient_mem_invariants_iff ρ C hC a).mp
    rw [ha]
    exact v.property
  exact ⟨⟨a,haP⟩,Subtype.ext ha⟩

theorem displacementToQuotientFixed_ker (C : Submodule k A) (hC : C≤ρ.invariants) :
    (displacementToQuotientFixed ρ C hC).ker=
      C.comap (displacementPreimage ρ C).subtype := by
  ext a
  rw [LinearMap.mem_ker,Subtype.ext_iff]
  change C.mkQ (a:A)=0 ↔ (a:A)∈C
  rw [Submodule.mkQ_apply,Submodule.Quotient.mk_eq_zero]

/-- Exact fixed-quotient dimension formula in additive form. The last
term is the actual surviving displacement slice, not its scalar-line proxy. -/
theorem centralQuotient_invariants_finrank_add [Finite G] [FiniteDimensional k A]
    (C : Submodule k A) (hC : C≤ρ.invariants) :
    Module.finrank k (centralQuotientRepresentation ρ C hC).invariants+
      Module.finrank k C =
        Module.finrank k ρ.invariants+Module.finrank k (displacementSlice ρ C) := by
  have hd := (displacementToSlice ρ C).finrank_range_add_finrank_ker
  rw [LinearMap.range_eq_top.mpr (displacementToSlice_surjective ρ C),
    finrank_top,displacementToSlice_ker,
    (Submodule.comapSubtypeEquivOfLe (invariants_le_displacementPreimage ρ C)).finrank_eq] at hd
  have hq := (displacementToQuotientFixed ρ C hC).finrank_range_add_finrank_ker
  rw [LinearMap.range_eq_top.mpr (displacementToQuotientFixed_surjective ρ C hC),
    finrank_top,displacementToQuotientFixed_ker,
    (Submodule.comapSubtypeEquivOfLe (centralCut_le_displacementPreimage ρ C hC)).finrank_eq] at hq
  exact hq.trans (hd.symm.trans (Nat.add_comm _ _))

theorem centralQuotient_invariants_finrank_eq [Finite G] [FiniteDimensional k A]
    (C : Submodule k A) (hC : C≤ρ.invariants) :
    Module.finrank k (centralQuotientRepresentation ρ C hC).invariants=
      Module.finrank k ρ.invariants-Module.finrank k C+
        Module.finrank k (displacementSlice ρ C) := by
  have h := centralQuotient_invariants_finrank_add ρ C hC
  have hc := Submodule.finrank_mono hC
  omega

/-- This is the precise residual condition a separator must prove. -/
theorem centralQuotient_invariants_finrank_of_slice_eq_bot
    [Finite G] [FiniteDimensional k A] (C : Submodule k A) (hC : C≤ρ.invariants)
    (hsep : displacementSlice ρ C=⊥) :
    Module.finrank k (centralQuotientRepresentation ρ C hC).invariants=
      Module.finrank k ρ.invariants-Module.finrank k C := by
  rw [centralQuotient_invariants_finrank_eq ρ C hC,hsep]
  simp only [finrank_bot,add_zero]

/-- The full connecting slice has dimension equal to the fixed space
after quotienting by ALL original invariants. -/
theorem displacementSlice_invariants_finrank [Finite G] [FiniteDimensional k A] :
    Module.finrank k (displacementSlice ρ ρ.invariants)=
      Module.finrank k (centralQuotientRepresentation ρ ρ.invariants le_rfl).invariants := by
  simpa only [Nat.sub_self,zero_add] using
    (centralQuotient_invariants_finrank_eq ρ ρ.invariants le_rfl).symm

/-- Every displacement whose values are fixed is a homomorphism from
the ORIGINAL multiplicative group to the additive fixed space. -/
theorem displacement_mul_of_fixed (a : A) (ha : a∈displacementPreimage ρ ρ.invariants)
    (g h : G) :
    representationDisplacement ρ a (g*h)=
      representationDisplacement ρ a g+representationDisplacement ρ a h := by
  have hs : ρ g (ρ h a-a)=ρ h a-a := ha h g
  change ρ (g*h) a-a=(ρ g a-a)+(ρ h a-a)
  calc
    _ = (ρ g (ρ h a)-ρ g a)+(ρ g a-a) := by
      rw [map_mul,Module.End.mul_apply]
      abel
    _ = (ρ h a-a)+(ρ g a-a) := by rw [← map_sub,hs]
    _ = _ := add_comm _ _

theorem displacementSlice_invariants_mul (f : displacementSlice ρ ρ.invariants)
    (g h : G) : f.val (g*h)=f.val g+f.val h := by
  obtain ⟨a,ha⟩ := f.property.1
  have haP : a∈displacementPreimage ρ ρ.invariants := by
    change representationDisplacement ρ a∈subspaceValuedFunctions (G := G) ρ.invariants
    rw [ha]
    exact f.property.2
  rw [← ha]
  exact displacement_mul_of_fixed ρ a haP g h

end SymmetricSubgroupAsymptotics
