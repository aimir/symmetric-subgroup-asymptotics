import SymmetricSubgroupAsymptotics.SchurPGroupCapacity
import SymmetricSubgroupAsymptotics.RepresentationGeneratorInvariants

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
