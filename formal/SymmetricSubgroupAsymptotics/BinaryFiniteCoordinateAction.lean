import SymmetricSubgroupAsymptotics.BinaryCoordinateFixedFactor
import SymmetricSubgroupAsymptotics.FiniteCayleyGroup
import SymmetricSubgroupAsymptotics.FinitePermutationEncoding

/-! Finite coordinate checks use literal numeric permutation rows. Their
equality to the original group action follows from the checked encoding,
without evaluating the well-founded words behind the row equivalence. -/
set_option autoImplicit false
noncomputable section
namespace SymmetricSubgroupAsymptotics

namespace EncodedCayleyCertificate
variable {w n : ℕ} {ι : Type*} {generators : ι → Equiv.Perm (Fin w)}
    (C : EncodedCayleyCertificate (permutationGeneratorEncoding generators) n)

theorem permutation_elements_apply (i : Fin n) (x : Fin w) :
    C.toCayley.elements i x=finFunctionFinEquiv.symm (C.rows i) x := by
  have h : permutationCode (C.toCayley.elements i)=C.rows i := C.encode_elements i
  rw [← h]
  simp only [permutationCode,Equiv.symm_apply_apply]

end EncodedCayleyCertificate

theorem binaryCoordinate_generatorDefects_apply {G ι : Type} [Group G] {w c : ℕ}
    (ρ : Representation (ZMod 2) G (Fin w → ZMod 2))
    (generators : ι → G) (C : BinaryCoordinateSpace w c) (v : Fin w → ZMod 2) :
    binaryCoordinate_generatorDefects ρ generators C v=
      fun j => C.defect (ρ (generators j) v-v) := rfl

end SymmetricSubgroupAsymptotics
