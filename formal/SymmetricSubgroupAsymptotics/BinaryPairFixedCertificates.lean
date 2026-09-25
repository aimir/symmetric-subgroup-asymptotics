import SymmetricSubgroupAsymptotics.SchurPGroupCapacity

/-!
# Finite fixed-space certificates for original binary sections

Generator checks, a linear inclusion, and reconstruction give an exact
chart of the actual invariant subspace. The p-group theorem converts its
checked dimension into the Schur capacity of the original representation.
The certificate contains no declared capacity or desired fusion bound.
-/

set_option autoImplicit false
noncomputable section
namespace SymmetricSubgroupAsymptotics

variable {G ι V : Type} [Group G] [AddCommGroup V] [Module (ZMod 2) V]

/-- Fixedness is checked on the retained original generators only. -/
theorem binaryPair_invariants_iff_generators
    (ρ : Representation (ZMod 2) G V) (generators : ι → G)
    (hgen : Subgroup.closure (Set.range generators)=⊤) (v : V) :
    v∈ρ.invariants ↔ ∀ j, ρ (generators j) v=v := by
  constructor
  · intro h j
    exact h (generators j)
  · intro h
    let S : Subgroup G := {
      carrier := {g | ρ g v=v}
      one_mem' := by simp
      mul_mem' := by
        intro a b ha hb
        change ρ (a*b) v=v
        rw [map_mul]
        change ρ a (ρ b v)=v
        rw [hb,ha]
      inv_mem' := by
        intro a ha
        change ρ a⁻¹ v=v
        have he : ρ a⁻¹ (ρ a v)=v := by
          change (ρ a⁻¹*ρ a) v=v
          rw [← map_mul,inv_mul_cancel,map_one]
          rfl
        rwa [ha] at he }
    have ht : S=⊤ := by
      apply top_unique
      rw [← hgen]
      apply (Subgroup.closure_le S).mpr
      rintro _ ⟨j,rfl⟩
      exact h j
    intro g
    exact (show g∈S by rw [ht]; trivial)

/-- A reversible finite linear chart of the subspace fixed by the actual
retained generator action. All equations are suitable for finite checking. -/
structure BinaryPairFixedCertificate
    (ρ : Representation (ZMod 2) G V) (generators : ι → G) (r : ℕ) where
  inclusion : (Fin r → ZMod 2) →ₗ[ZMod 2] V
  coordinates : V →ₗ[ZMod 2] (Fin r → ZMod 2)
  left_inverse : ∀ a, coordinates (inclusion a)=a
  generators_fixed : ∀ j a, ρ (generators j) (inclusion a)=inclusion a
  reconstruct : ∀ v, (∀ j, ρ (generators j) v=v) → inclusion (coordinates v)=v

namespace BinaryPairFixedCertificate

variable {ρ : Representation (ZMod 2) G V} {generators : ι → G} {r : ℕ}
    (C : BinaryPairFixedCertificate ρ generators r)
    (hgen : Subgroup.closure (Set.range generators)=⊤)

/-- The checked chart identifies the actual invariant subspace. -/
def invariantsEquiv : (Fin r → ZMod 2) ≃ₗ[ZMod 2] ρ.invariants where
  toFun a := ⟨C.inclusion a,
    (binaryPair_invariants_iff_generators ρ generators hgen _).mpr
      (fun j => C.generators_fixed j a)⟩
  invFun v := C.coordinates v.val
  left_inv := C.left_inverse
  right_inv v := Subtype.ext (C.reconstruct v.val
    ((binaryPair_invariants_iff_generators ρ generators hgen _).mp v.property))
  map_add' a b := Subtype.ext (C.inclusion.map_add a b)
  map_smul' a b := Subtype.ext (C.inclusion.map_smul a b)

include C hgen

theorem invariants_finrank : Module.finrank (ZMod 2) ρ.invariants=r := by
  rw [← (C.invariantsEquiv hgen).finrank_eq]
  simp

/-- The actual quotient-section capacity is proved from finite linear
checks, not supplied as a numerical certificate premise. -/
theorem capacity [Finite V] (hG : IsPGroup 2 G) :
    representationSchurCapacity ρ=(r : ℝ) := by
  rw [pGroup_representationSchurCapacity hG ρ,C.invariants_finrank hgen]

end BinaryPairFixedCertificate
end SymmetricSubgroupAsymptotics
