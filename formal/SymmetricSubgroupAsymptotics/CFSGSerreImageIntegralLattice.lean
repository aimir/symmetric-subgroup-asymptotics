import SymmetricSubgroupAsymptotics.CFSGSerreGeneratorRelations
import SymmetricSubgroupAsymptotics.CFSGSerreDiagramLattice

/-! Exact image of the ORIGINAL integral Serre lattice under an actual Lie
homomorphism. The target lattice is constructed from the actual target
generators and all their divided powers. There is no source spanning,
faithfulness, target basis, simplicity or recognition premise. -/
set_option autoImplicit false
noncomputable section
namespace SymmetricSubgroupAsymptotics.CFSGSerreImageIntegralLattice
open CFSG.Models.Chevalley CFSGSerreLocalNilpotence
variable {n : ℕ} (A : Matrix (Fin n) (Fin n) ℤ)
    {L : Type*} [LieRing L] [LieAlgebra ℚ L]
    (f : RationalLie A →ₗ⁅ℚ⁆ L)

def targetDividedPower (neg : Bool) (i : Fin n) (k : ℕ) : L →ₗ[ℤ] L :=
  (((k.factorial : ℚ)⁻¹) • ((LieAlgebra.ad ℚ L (f (rootVector A neg i))) ^ k)).restrictScalars ℤ

theorem map_dividedPower (neg : Bool) (i : Fin n) (k : ℕ) (x : RationalLie A) :
    f (dividedPower A neg i k x) = targetDividedPower A f neg i k (f x) := by
  change f (((k.factorial : ℚ)⁻¹) •
    ((LieAlgebra.ad ℚ (RationalLie A) (rootVector A neg i)) ^ k) x) =
    ((k.factorial : ℚ)⁻¹) • ((LieAlgebra.ad ℚ L (f (rootVector A neg i))) ^ k) (f x)
  rw [map_smulₛₗ, RingHom.id_apply, lieHom_ad_pow_apply]

def targetLattice : Submodule ℤ L :=
  sInf {S | (∀ g, f (generator A g) ∈ S) ∧
    ∀ neg i k x, x ∈ S → targetDividedPower A f neg i k x ∈ S}

theorem target_generator_mem (g : CartanMatrix.Generators (Fin n)) :
    f (generator A g) ∈ targetLattice A f := by
  rw [targetLattice, Submodule.mem_sInf]
  intro S hS
  exact hS.1 g

theorem target_dividedPower_mem (neg : Bool) (i : Fin n) (k : ℕ)
    (x : L) (hx : x ∈ targetLattice A f) :
    targetDividedPower A f neg i k x ∈ targetLattice A f := by
  rw [targetLattice, Submodule.mem_sInf] at hx ⊢
  intro S hS
  exact hS.2 neg i k x (hx S hS)

theorem image_eq_targetLattice :
    (integralLattice A).map (f.toLinearMap.restrictScalars ℤ) = targetLattice A f := by
  apply le_antisymm
  · let S := (targetLattice A f).comap (f.toLinearMap.restrictScalars ℤ)
    have hgen : ∀ g, generator A g ∈ S := fun g => target_generator_mem A f g
    have hstable : ∀ neg i k x, x ∈ S → dividedPower A neg i k x ∈ S := by
      intro neg i k x hx
      change f (dividedPower A neg i k x) ∈ targetLattice A f
      rw [map_dividedPower]
      exact target_dividedPower_mem A f neg i k (f x) hx
    have hle : integralLattice A ≤ S := sInf_le ⟨hgen,hstable⟩
    rintro y ⟨x,hx,rfl⟩
    exact hle hx
  · apply sInf_le
    constructor
    · intro g
      refine ⟨generator A g,?_,rfl⟩
      exact CFSGSerreDiagram.generator_mem_integralLattice A g
    · rintro neg i k y ⟨x,hx,rfl⟩
      exact ⟨dividedPower A neg i k x, dividedPower_mem A neg i k x hx,
        map_dividedPower A f neg i k x⟩

def integralMap : integralLattice A →ₗ[ℤ] targetLattice A f :=
  (f.toLinearMap.restrictScalars ℤ).restrict fun x hx => by
    rw [← image_eq_targetLattice]
    exact ⟨x,hx,rfl⟩

theorem integralMap_surjective : Function.Surjective (integralMap A f) := by
  intro y
  have hy : y.val ∈ (integralLattice A).map (f.toLinearMap.restrictScalars ℤ) := by
    rw [image_eq_targetLattice]
    exact y.property
  obtain ⟨x,hx,he⟩ := hy
  exact ⟨⟨x,hx⟩,Subtype.ext he⟩

end SymmetricSubgroupAsymptotics.CFSGSerreImageIntegralLattice
