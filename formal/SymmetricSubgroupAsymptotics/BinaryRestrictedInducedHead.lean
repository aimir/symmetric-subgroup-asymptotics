import SymmetricSubgroupAsymptotics.BinaryInducedHead
import SymmetricSubgroupAsymptotics.InducedTernaryHead

/-!
# Binary heads after restricting an induced module

Mackey coordinates retain the literal twisted fibre on each orbit of a
binary subgroup.  Applying the intrinsic binary-grid theorem to every
coordinate bounds the head of an arbitrary original induced
subrepresentation.  When the binary subgroup is transitive and the degree
is eight or sixteen, there is one coordinate and the central-binomial width
is exactly three quarters of the degree for a two-dimensional fibre.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
open scoped Classical BigOperators

namespace SymmetricSubgroupAsymptotics

attribute [local instance]
  inducedMackeyComponentAddCommGroup inducedMackeyComponentModule

/-- Mackey projection for a subrepresentation which is assumed invariant
only under the restricting subgroup. -/
def inducedMackeyRestrictedSubmoduleCoordinate
    {k G V : Type} [Field k] [Group G] [Finite G]
    [AddCommGroup V] [Module k V]
    (H P : Subgroup G) (rho : Representation k H V)
    [Fintype (DoubleCoset.Quotient (H : Set G) (P : Set G))]
    (M : Subrepresentation
      ((Representation.ind H.subtype rho).comp P.subtype))
    (q : DoubleCoset.Quotient (H : Set G) (P : Set G)) :
    M.toRepresentation.IntertwiningMap
      (Representation.ind (inducedOrbitStabilizer H P q.out).subtype
        (inducedOrbitFibre H P rho q.out)) where
  toLinearMap := (LinearMap.proj q).comp
    ((inducedMackeyDecomposition H P rho).toLinearMap.comp
      M.toSubmodule.subtype)
  isIntertwining' p := by
    apply LinearMap.ext
    intro v
    exact inducedMackeyDecomposition_equivariant H P rho p v.1 q

theorem inducedMackeyRestrictedSubmoduleCoordinate_injective
    {k G V : Type} [Field k] [Group G] [Finite G]
    [AddCommGroup V] [Module k V]
    (H P : Subgroup G) (rho : Representation k H V)
    [Fintype (DoubleCoset.Quotient (H : Set G) (P : Set G))]
    (M : Subrepresentation
      ((Representation.ind H.subtype rho).comp P.subtype)) :
    Function.Injective (fun v q ↦
      inducedMackeyRestrictedSubmoduleCoordinate H P rho M q v) := by
  intro v z h
  apply Subtype.ext
  apply (inducedMackeyDecomposition H P rho).injective
  exact h

/-- Coordinatewise binary-grid head bound when the numerator is invariant
only under the restricting binary subgroup. -/
theorem induced_binaryGroupRestriction_head_bound
    {G V : Type} [Group G] [Finite G]
    [AddCommGroup V] [Module (ZMod 2) V]
    [FiniteDimensional (ZMod 2) V]
    (H P : Subgroup G) (hP : IsPGroup 2 P)
    (rho : Representation (ZMod 2) H V)
    [Fintype (DoubleCoset.Quotient (H : Set G) (P : Set G))]
    (M : Subrepresentation
      ((Representation.ind H.subtype rho).comp P.subtype))
    (j : DoubleCoset.Quotient (H : Set G) (P : Set G) → ℕ)
    (hindex : ∀ q,
      (inducedOrbitStabilizer H P q.out).index = 2 ^ j q) :
    Module.finrank (ZMod 2)
        (primeActionCharacters 2
          (representationGroupAction M.toRepresentation)) ≤
      ∑ q, Module.finrank (ZMod 2) V * (j q).choose (j q / 2) := by
  letI := induced_finiteDimensional H rho
  apply representationCharacterHead_le_coordinates
    (fun q ↦ inducedMackeyComponent H P rho q)
    M.toRepresentation
    (fun q ↦ Representation.ind
      (inducedOrbitStabilizer H P q.out).subtype
      (inducedOrbitFibre H P rho q.out))
    (fun q ↦ Module.finrank (ZMod 2) V *
      (j q).choose (j q / 2))
    ?_ (inducedMackeyRestrictedSubmoduleCoordinate H P rho M)
    (inducedMackeyRestrictedSubmoduleCoordinate_injective H P rho M)
  intro q S
  rw [(representationCharacterHeadEquiv S.toRepresentation).finrank_eq]
  exact twoGroup_induced_subrepresentationHead_le
    (G := P) hP (inducedOrbitStabilizer H P q.out)
      (inducedOrbitFibre H P rho q.out) (j q) (hindex q) S

/-- Coordinatewise binary-grid head bound for the restriction of an
arbitrary subrepresentation of an original induced module. -/
theorem induced_binaryGroupOrbit_head_bound
    {G V : Type} [Group G] [Finite G]
    [AddCommGroup V] [Module (ZMod 2) V]
    [FiniteDimensional (ZMod 2) V]
    (H P : Subgroup G) (hP : IsPGroup 2 P)
    (rho : Representation (ZMod 2) H V)
    [Fintype (DoubleCoset.Quotient (H : Set G) (P : Set G))]
    (M : Subrepresentation (Representation.ind H.subtype rho))
    (j : DoubleCoset.Quotient (H : Set G) (P : Set G) → ℕ)
    (hindex : ∀ q,
      (inducedOrbitStabilizer H P q.out).index = 2 ^ j q) :
    Module.finrank (ZMod 2)
        (primeActionCharacters 2
          (representationGroupAction M.toRepresentation)) ≤
      ∑ q, Module.finrank (ZMod 2) V * (j q).choose (j q / 2) := by
  letI := induced_finiteDimensional H rho
  apply (representationCharacterHead_le_restriction
    M.toRepresentation P.subtype).trans
  apply representationCharacterHead_le_coordinates
    (fun q ↦ inducedMackeyComponent H P rho q)
    (M.toRepresentation.comp P.subtype)
    (fun q ↦ Representation.ind
      (inducedOrbitStabilizer H P q.out).subtype
      (inducedOrbitFibre H P rho q.out))
    (fun q ↦ Module.finrank (ZMod 2) V *
      (j q).choose (j q / 2))
    ?_ (inducedMackeySubmoduleCoordinate H P rho M)
    (inducedMackeySubmoduleCoordinate_injective H P rho M)
  intro q S
  rw [(representationCharacterHeadEquiv S.toRepresentation).finrank_eq]
  exact twoGroup_induced_subrepresentationHead_le
    (G := P) hP (inducedOrbitStabilizer H P q.out)
      (inducedOrbitFibre H P rho q.out) (j q) (hindex q) S

/-- On a transitive binary restriction of degree eight or sixteen, every
subrepresentation of an induced two-space has head at most three quarters
of the original degree. -/
theorem inducedTwoSpace_binaryTransitiveRestriction_four_mul_head_le_three_mul_index
    {G V : Type} [Group G] [Finite G]
    [AddCommGroup V] [Module (ZMod 2) V]
    [FiniteDimensional (ZMod 2) V]
    (H P : Subgroup G) (hP : IsPGroup 2 P)
    (rho : Representation (ZMod 2) H V)
    (hdim : Module.finrank (ZMod 2) V = 2)
    [MulAction.IsPretransitive P (G ⧸ H)]
    (hdegree : H.index = 8 ∨ H.index = 16)
    (M : Subrepresentation
      ((Representation.ind H.subtype rho).comp P.subtype)) :
    4 * Module.finrank (ZMod 2)
        (primeActionCharacters 2
          (representationGroupAction M.toRepresentation)) ≤
      3 * H.index := by
  let D := DoubleCoset.Quotient (H : Set G) (P : Set G)
  let O := MulAction.orbitRel.Quotient P (G ⧸ H)
  letI : Subsingleton O :=
    (MulAction.pretransitive_iff_subsingleton_quotient P (G ⧸ H)).mp
      inferInstance
  letI : Subsingleton D :=
    (inducedDoubleCosetOrbitEquiv H P).subsingleton
  letI : Unique D :=
    { default := DoubleCoset.mk H P 1
      uniq := fun _ ↦ Subsingleton.elim _ _ }
  letI : Fintype D := Fintype.ofFinite D
  rcases hdegree with h8 | h16
  · let j : D → ℕ := fun _ ↦ 3
    have hcomponentIndex : ∀ q : D,
        (inducedOrbitStabilizer H P q.out).index = 2 ^ j q := by
      intro q
      have hsum := inducedMackey_index_sum H P
      have hq : q = default := Subsingleton.elim _ _
      subst q
      simpa only [j, Fintype.sum_unique] using hsum.trans h8
    have hhead := induced_binaryGroupRestriction_head_bound
      H P hP rho M j hcomponentIndex
    simp only [j, hdim, Fintype.sum_unique] at hhead
    norm_num [Nat.choose] at hhead ⊢
    omega
  · let j : D → ℕ := fun _ ↦ 4
    have hcomponentIndex : ∀ q : D,
        (inducedOrbitStabilizer H P q.out).index = 2 ^ j q := by
      intro q
      have hsum := inducedMackey_index_sum H P
      have hq : q = default := Subsingleton.elim _ _
      subst q
      simpa only [j, Fintype.sum_unique] using hsum.trans h16
    have hhead := induced_binaryGroupRestriction_head_bound
      H P hP rho M j hcomponentIndex
    simp only [j, hdim, Fintype.sum_unique] at hhead
    norm_num [Nat.choose] at hhead ⊢
    omega

end SymmetricSubgroupAsymptotics

end
