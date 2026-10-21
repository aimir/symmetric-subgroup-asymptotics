import SymmetricSubgroupAsymptotics.BinaryCoordinateDisplacementCertificate
import SymmetricSubgroupAsymptotics.RepresentationCoinvariantFiniteCertificate
import Mathlib.Algebra.Field.ZMod

/-! Reversible charts of a state and selected literal displacements give
an intrinsic head bound for that SAME original representation. -/
set_option autoImplicit false
noncomputable section
namespace SymmetricSubgroupAsymptotics
local instance : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩

/-- Only selected original generator displacements are needed; the row
list need not generate the whole acting group. -/
theorem binary_coinvariant_head_le_of_coordinate_displacements
    {G : Type} [Group G] {w d r q : ℕ}
    (rho : Representation (ZMod 2) G (Fin w → ZMod 2))
    (u : Fin q → G) (B : Subrepresentation rho)
    (C : BinaryCoordinateSpace w d) (D : BinaryCoordinateSpace w r)
    (hB : B.toSubmodule = C.space)
    (generatorIndex : Fin r → Fin q) (basisIndex : Fin r → Fin d)
    (hmove : ∀ j, D.inclusion (Pi.single j 1) =
      rho (u (generatorIndex j)) (C.inclusion (Pi.single (basisIndex j) 1)) -
        C.inclusion (Pi.single (basisIndex j) 1))
    (bound : ℕ) (hnum : d ≤ r + bound) :
    Module.finrank (ZMod 2) B.toRepresentation.Coinvariants ≤ bound := by
  have hC (j : Fin d) : C.inclusion (Pi.single j 1) ∈ B.toSubmodule := by
    rw [hB]
    exact ⟨Pi.single j 1, rfl⟩
  have hD : D.space ≤ B.toSubmodule := by
    apply D.le_of_basis_mem
    intro j
    rw [hmove]
    exact B.toSubmodule.sub_mem
      (B.apply_mem_toSubmodule _ (hC _)) (hC _)
  apply representationCoinvariants_finrank_le_of_displacementSubspace rho u B
    (D.submoduleOf B.toSubmodule hD) bound
  · apply D.submoduleOf_le_of_basis_mem B.toSubmodule hD
    intro j
    have he : (⟨D.inclusion (Pi.single j 1), hD ⟨Pi.single j 1, rfl⟩⟩ : B.toSubmodule) =
        ⟨rho (u (generatorIndex j)) (C.inclusion (Pi.single (basisIndex j) 1)) -
          C.inclusion (Pi.single (basisIndex j) 1),
          B.toSubmodule.sub_mem (B.apply_mem_toSubmodule _ (hC _)) (hC _)⟩ :=
      Subtype.ext (hmove j)
    rw [he]
    exact Submodule.subset_span
      ⟨⟨generatorIndex j, ⟨C.inclusion (Pi.single (basisIndex j) 1), hC _⟩⟩, rfl⟩
  · rw [D.submoduleOf_finrank]
    have hb : Module.finrank (ZMod 2) B.toSubmodule = d := by
      rw [hB]
      exact C.finrank
    rw [hb]
    exact hnum

end SymmetricSubgroupAsymptotics
