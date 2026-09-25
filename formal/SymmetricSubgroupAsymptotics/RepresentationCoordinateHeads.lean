import SymmetricSubgroupAsymptotics.ModuleCoordinateHeads
import SymmetricSubgroupAsymptotics.RepresentationGeneratorHead
import Mathlib.RepresentationTheory.Subrepresentation

/-! Finite coordinate-head bounds for the actual representations and
their actual subrepresentations. Original equivariant coordinate maps
must jointly separate points; no splitting of the source is assumed. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
open scoped MonoidAlgebra BigOperators
namespace SymmetricSubgroupAsymptotics
variable {k G V : Type} [Field k] [Group G] [AddCommGroup V] [Module k V]

def submoduleRepresentationModuleEquiv (ρ : Representation k G V)
    (S : Submodule k[G] ρ.asModule) :
    S≃ₗ[k[G]] (Subrepresentation.ofSubmodule' S).toRepresentation.asModule := by
  refine {
    toFun := fun x=>x
    invFun := fun x=>x
    left_inv := fun _=>rfl
    right_inv := fun _=>rfl
    map_add' := fun _ _=>rfl
    map_smul' := ?_ }
  intro c v
  simp only [RingHom.id_apply]
  induction c using MonoidAlgebra.induction_linear with
  | zero => simp
  | add a b ha hb => simp only [add_smul]; exact congrArg₂ (·+·) ha hb
  | single g a =>
    apply Subtype.ext
    simp only [Representation.single_smul,Submodule.coe_smul_of_tower]
    rfl

theorem representationHom_finrank_le_coordinates
    {A ι : Type} [AddCommGroup A] [Module k A] [FiniteDimensional k A]
    [Fintype ι] (W : ι→Type) [∀i,AddCommGroup (W i)] [∀i,Module k (W i)]
    (ρ : Representation k G V) [FiniteDimensional k V]
    (τ : ∀i,Representation k G (W i)) (σ : Representation k G A)
    (b : ι→ℕ)
    (hb : ∀i (S : Subrepresentation (τ i)),
      Module.finrank k (S.toRepresentation.IntertwiningMap σ)≤b i)
    (f : ∀i,ρ.IntertwiningMap (τ i))
    (hf : Function.Injective (fun v i=>f i v)) :
    Module.finrank k (ρ.IntertwiningMap σ)≤∑i,b i := by
  let fi : ∀i,ρ.asModule→ₗ[k[G]] (τ i).asModule := fun i=>
    Representation.IntertwiningMap.equivLinearMapAsModule ρ (τ i) (f i)
  have hi : Function.Injective (fun v i=>fi i v) := hf
  have hlocal : ∀i (S : Submodule k[G] (τ i).asModule),
      Module.finrank k (S→ₗ[k[G]]σ.asModule)≤b i := by
    intro i S
    have h := hb i (Subrepresentation.ofSubmodule' S)
    rw [(Representation.IntertwiningMap.equivLinearMapAsModule _ σ).finrank_eq] at h
    rw [(moduleHomDomainEquiv (k := k) (A := σ.asModule)
      (submoduleRepresentationModuleEquiv (τ i) S)).finrank_eq]
    exact h
  rw [(Representation.IntertwiningMap.equivLinearMapAsModule ρ σ).finrank_eq]
  exact moduleHom_finrank_le_finite_coordinate_bounds (k := k) (R := k[G])
    (A := σ.asModule) (fun i=>(τ i).asModule) b hlocal ρ.asModule fi hi

theorem representationCharacterHead_le_coordinates
    {p : ℕ} [Fact p.Prime] {G₀ V₀ ι : Type}
    [Group G₀] [AddCommGroup V₀] [Module (ZMod p) V₀]
    [FiniteDimensional (ZMod p) V₀] [Fintype ι]
    (W : ι→Type) [∀i,AddCommGroup (W i)] [∀i,Module (ZMod p) (W i)]
    (ρ : Representation (ZMod p) G₀ V₀)
    (τ : ∀i,Representation (ZMod p) G₀ (W i)) (b : ι→ℕ)
    (hb : ∀i (S : Subrepresentation (τ i)),
      Module.finrank (ZMod p)
        (primeActionCharacters p (representationGroupAction S.toRepresentation))≤b i)
    (f : ∀i,ρ.IntertwiningMap (τ i))
    (hf : Function.Injective (fun v i=>f i v)) :
    Module.finrank (ZMod p) (primeActionCharacters p (representationGroupAction ρ))≤
      ∑i,b i := by
  rw [(representationCharacterHeadEquiv ρ).finrank_eq]
  apply representationHom_finrank_le_coordinates W ρ τ
    (Representation.trivial (ZMod p) G₀ (ZMod p)) b ?_ f hf
  intro i S
  rw [←(representationCharacterHeadEquiv S.toRepresentation).finrank_eq]
  exact hb i S

end SymmetricSubgroupAsymptotics
