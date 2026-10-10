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

/-- Forgetting the state subtype sends the checked displacement submodule
back to its literal coordinate space. -/
theorem submodule_map_subtype :
    D.submodule.map B.toSubmodule.subtype = C.space := by
  ext v
  constructor
  · rintro ⟨x, hx, rfl⟩
    exact hx
  · intro hv
    have hvB : v ∈ B.toSubmodule := D.space_le_state hv
    exact ⟨⟨v, hvB⟩, hv, rfl⟩

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

/-- If every displayed group-generator displacement of a coordinate basis
of the whole state lies in the checked displacement chart, then the chart
contains the complete retained-generator displacement span.  Together with
`le_generatorDisplacementSpan`, this lets a generated finite certificate
identify the intrinsic coinvariant kernel exactly. -/
theorem generatorDisplacementSpan_le_of_basis_mem
    {b : ℕ} (S : BinaryCoordinateSpace w b)
    (hstate : B.toSubmodule = S.space)
    (hbasis : ∀ i j,
      (⟨rho (generators i) (S.inclusion (Pi.single j 1)) -
          S.inclusion (Pi.single j 1),
        B.toSubmodule.sub_mem
          (B.apply_mem_toSubmodule (generators i) (by
            rw [hstate]
            exact ⟨Pi.single j 1, rfl⟩))
          (by
            rw [hstate]
            exact ⟨Pi.single j 1, rfl⟩)⟩ : B.toSubmodule) ∈
        D.submodule) :
    representationGeneratorDisplacementSpan rho generators B ≤
      D.submodule := by
  apply Submodule.span_le.mpr
  rintro _ ⟨⟨i, v⟩, rfl⟩
  let delta : B.toSubmodule →ₗ[ZMod 2] B.toSubmodule :=
    B.toRepresentation (generators i) - LinearMap.id
  have hSB : S.space ≤ B.toSubmodule := by
    rw [hstate]
  have hchart : S.submoduleOf B.toSubmodule hSB ≤
      D.submodule.comap delta := by
    apply S.submoduleOf_le_of_basis_mem B.toSubmodule hSB
    intro j
    change delta
      (⟨S.inclusion (Pi.single j 1),
        hSB ⟨Pi.single j 1, rfl⟩⟩ : B.toSubmodule) ∈ D.submodule
    simpa only [delta, LinearMap.sub_apply, LinearMap.id_apply] using hbasis i j
  have hv : v ∈ S.submoduleOf B.toSubmodule hSB := by
    change (v : Fin w → ZMod 2) ∈ S.space
    rw [← hstate]
    exact v.2
  have := hchart hv
  simpa only [Submodule.mem_comap, delta, LinearMap.sub_apply,
    LinearMap.id_apply] using this

/-- A full-state reverse basis check upgrades the generated displacement
certificate to an equality. -/
theorem generatorDisplacementSpan_eq_of_basis_mem
    {b : ℕ} (S : BinaryCoordinateSpace w b)
    (hstate : B.toSubmodule = S.space)
    (hbasis : ∀ i j,
      (⟨rho (generators i) (S.inclusion (Pi.single j 1)) -
          S.inclusion (Pi.single j 1),
        B.toSubmodule.sub_mem
          (B.apply_mem_toSubmodule (generators i) (by
            rw [hstate]
            exact ⟨Pi.single j 1, rfl⟩))
          (by
            rw [hstate]
            exact ⟨Pi.single j 1, rfl⟩)⟩ : B.toSubmodule) ∈
        D.submodule) :
    representationGeneratorDisplacementSpan rho generators B =
      D.submodule := by
  apply le_antisymm
  · exact D.generatorDisplacementSpan_le_of_basis_mem S hstate hbasis
  · exact D.le_generatorDisplacementSpan

end BinaryCoordinateDisplacementCertificate

end SymmetricSubgroupAsymptotics

end
