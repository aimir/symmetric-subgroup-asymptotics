import SymmetricSubgroupAsymptotics.BinaryCoordinateSpaces
import SymmetricSubgroupAsymptotics.RepresentationCoinvariantFiniteCertificate

/-!
# Coordinate certificates for finite displacement spaces

The eight-block frame exporter stores each invariant state and each checked
displacement subspace by a reversible binary-coordinate chart.  This file
turns a sparse list of literal generator displacements for the coordinate
basis into the submodule inclusion consumed by the coinvariant-head theorem.

The certificate never trusts the reported displacement dimension.  Its
dimension is the dimension of the reversible coordinate chart, and every
coordinate basis vector is reconstructed as a sum of literal terms
`rho(g) v - v` in the retained invariant state.
-/

set_option autoImplicit false
noncomputable section
open scoped BigOperators Classical

namespace SymmetricSubgroupAsymptotics

namespace BinaryCoordinateSpace

variable {w d : ℕ}

/-- A coordinate subspace, regarded as a submodule of an ambient submodule
which contains it. -/
def submoduleOf (C : BinaryCoordinateSpace w d)
    (B : Submodule (ZMod 2) (Fin w → ZMod 2)) (_hCB : C.space ≤ B) :
    Submodule (ZMod 2) B :=
  C.space.comap B.subtype

/-- The subtype presentation does not change the checked coordinate
dimension. -/
theorem submoduleOf_finrank (C : BinaryCoordinateSpace w d)
    (B : Submodule (ZMod 2) (Fin w → ZMod 2)) (hCB : C.space ≤ B) :
    Module.finrank (ZMod 2) (C.submoduleOf B hCB) = d := by
  change Module.finrank (ZMod 2) (C.space.comap B.subtype) = d
  rw [(Submodule.comapSubtypeEquivOfLe hCB).finrank_eq]
  exact C.finrank

/-- Containment of a coordinate subspace inside a submodule of `B` can be
checked only on the reversible coordinate basis. -/
theorem submoduleOf_le_of_basis_mem (C : BinaryCoordinateSpace w d)
    (B : Submodule (ZMod 2) (Fin w → ZMod 2)) (hCB : C.space ≤ B)
    (W : Submodule (ZMod 2) B)
    (hbasis : ∀ j,
      (⟨C.inclusion (Pi.single j 1),
        hCB ⟨Pi.single j 1, rfl⟩⟩ : B) ∈ W) :
    C.submoduleOf B hCB ≤ W := by
  intro x hx
  rcases x with ⟨v, hvB⟩
  change v ∈ C.space at hx
  obtain ⟨a, ha⟩ := hx
  have ha' : a = ∑ j, a j • Pi.single j (1 : ZMod 2) := by
    ext j
    simp [Pi.single_apply, mul_ite]
  change C.inclusion a = v at ha
  have hx : (⟨v, hvB⟩ : B) =
      ∑ j, a j •
        (⟨C.inclusion (Pi.single j 1),
          hCB ⟨Pi.single j 1, rfl⟩⟩ : B) := by
    apply Subtype.ext
    simp only [Submodule.coe_sum, Submodule.coe_smul]
    calc
      v = C.inclusion a := ha.symm
      _ = C.inclusion (∑ j, a j • Pi.single j (1 : ZMod 2)) :=
        congrArg C.inclusion ha'
      _ = ∑ j, a j • C.inclusion (Pi.single j 1) := by
        simp only [map_sum, map_smul]
  rw [hx]
  apply W.sum_mem
  intro j _
  exact W.smul_mem (a j) (hbasis j)

end BinaryCoordinateSpace

universe uG uI

variable {G : Type uG} {I : Type uI} [Group G] {w d : ℕ}
  (rho : Representation (ZMod 2) G (Fin w → ZMod 2))
  (generators : I → G) (B : Subrepresentation rho)

/-- Sparse proof that a reversible coordinate space lies in the literal
generator-displacement span of an invariant state.  Each coordinate basis
vector is an explicit sum of displayed generator displacements. -/
structure BinaryCoordinateDisplacementCertificate
    (C : BinaryCoordinateSpace w d) : Type (max 1 uI) where
  space_le_state : C.space ≤ B.toSubmodule
  termCount : Fin d → ℕ
  termGenerator : ∀ j, Fin (termCount j) → I
  termVector : ∀ j, Fin (termCount j) → B.toSubmodule
  basis_eq : ∀ j,
    (⟨C.inclusion (Pi.single j 1),
      space_le_state ⟨Pi.single j 1, rfl⟩⟩ : B.toSubmodule) =
      ∑ t, (⟨rho (generators (termGenerator j t)) (termVector j t).1 -
          (termVector j t).1,
        B.toSubmodule.sub_mem
          (B.apply_mem_toSubmodule
            (generators (termGenerator j t)) (termVector j t).2)
          (termVector j t).2⟩ : B.toSubmodule)

namespace BinaryCoordinateDisplacementCertificate

variable {rho : Representation (ZMod 2) G (Fin w → ZMod 2)}
  {generators : I → G} {B : Subrepresentation rho}
  {C : BinaryCoordinateSpace w d}
  (D : BinaryCoordinateDisplacementCertificate rho generators B C)

/-- The literal submodule of the state selected by the reversible
displacement chart. -/
def submodule : Submodule (ZMod 2) B.toSubmodule :=
  C.submoduleOf B.toSubmodule D.space_le_state

theorem finrank : Module.finrank (ZMod 2) D.submodule = d :=
  C.submoduleOf_finrank B.toSubmodule D.space_le_state

/-- Every checked coordinate basis vector is a sum of genuine retained
generator displacements. -/
theorem le_generatorDisplacementSpan :
    D.submodule ≤
      representationGeneratorDisplacementSpan
        (G := G) (I := I) rho generators B := by
  apply C.submoduleOf_le_of_basis_mem B.toSubmodule D.space_le_state
  intro j
  rw [D.basis_eq j]
  apply Submodule.sum_mem
  intro t _
  exact Submodule.subset_span ⟨⟨D.termGenerator j t, D.termVector j t⟩, rfl⟩

end BinaryCoordinateDisplacementCertificate

end SymmetricSubgroupAsymptotics

end
