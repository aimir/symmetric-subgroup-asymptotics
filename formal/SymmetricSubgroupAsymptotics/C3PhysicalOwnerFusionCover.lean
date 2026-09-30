import SymmetricSubgroupAsymptotics.C3HighNestedCarrier
import SymmetricSubgroupAsymptotics.C3PhysicalOwnerBranches
import SymmetricSubgroupAsymptotics.Non2TransitiveActionClasses
import SymmetricSubgroupAsymptotics.PrimeLayerVanishing

/-!
# Sending the high-C3 physical owner into the non-2 fusion menu

The strict relative-head inequality already carried by a high-C3 owner
forces its selected orbit image to be non-2.  We may therefore delete that
same literal orbit, rather than choosing another orbit of the complete
subgroup, and send the complete physical subgroup into the canonical
non-2 fusion family.  The complementary coordinate still contains the
outer regular-C3 block and every correlation with the untouched points.
-/

set_option autoImplicit false
noncomputable section
open scoped Classical

namespace SymmetricSubgroupAsymptotics

/-- A positive ternary relative head inside a normal subgroup is incompatible
with the ambient group being a 2-group.  This is the only prime-separation
fact needed to put the retained high-C3 orbit into the general non-2 menu. -/
theorem strict_ternaryRelativeHead_not_isPGroup_two
    {A Ω : Type*} [Group A] [Finite A] [Finite Ω]
    (N : Subgroup A) [N.Normal]
    (hHigh : 3 * Nat.card Ω <
      20 * Module.finrank (ZMod 3) (primeRelativeCharacters 3 N)) :
    ¬ IsPGroup 2 A := by
  intro hA
  have hN : IsPGroup 2 N := hA.to_subgroup N
  have hzero : Module.finrank (ZMod 3)
      (primeRelativeCharacters 3 N) = 0 :=
    primeRelativeHead_power_group 3 N 2 (by decide) hN
  rw [hzero] at hHigh
  omega

namespace C3HighNestedCarrier

/-- Delete the actual orbit stored in a high-C3 witness and choose only its
non-2 conjugacy-class representative.  No source, complement, or physical
weight is changed. -/
theorem Data.mem_non2CanonicalFamily
    {b : ℕ}
    (H : Subgroup (ternaryRegularAction × Equiv.Perm (Fin b)))
    (C : Data H) :
    ∃ (w : ℕ) (hn : w ≤ b + 3)
      (i : Non2TransitiveActionClass (Fin w)),
      relabelSubgroup (outerPointEquiv b) (physicalSubgroup H) ∈
        FusionWidthCanonicalFamily i.representative hn (fun _ => True) := by
  let w := Nat.card C.orbit.orbit
  letI : C.normal.Normal := C.normal_normal
  have hnon2 : ¬ IsPGroup 2
      (OrbitProfileFromOrbits.orbitImage
        (C3ComplementSource b H) C.orbit) :=
    strict_ternaryRelativeHead_not_isPGroup_two C.normal C.high
  obtain ⟨i, eO, himage⟩ := Non2TransitiveActionClass.orbit_cover
    (C3ComplementSource b H) C.orbit rfl hnon2
  have hn : w ≤ b + 3 := by
    have hwb := width_le H C.orbit (show Nat.card C.orbit.orbit = w from rfl)
    omega
  refine ⟨w, hn, i, ?_⟩
  exact mem_widthCanonicalFamily H C rfl i.representative eO himage
    (fun _ => True) trivial

end C3HighNestedCarrier

/-- Every classified complete high-C3 owner enters a canonical non-2 orbit
family by deleting the orbit retained in its own witness.  The theorem keeps
the branch classification in its premise; the target forgets only the
classification because numerical owner predicates are attached later. -/
theorem c3PhysicalStructuralOwnerBranch_mem_non2CanonicalFamily
    {k : C3PhysicalOwnerKind} {n : ℕ}
    {G : Subgroup (Equiv.Perm (Fin n))}
    (hG : C3PhysicalStructuralOwnerBranch k n G) :
    ∃ (w : ℕ) (hn : w ≤ n)
      (i : Non2TransitiveActionClass (Fin w)),
      G ∈ FusionWidthCanonicalFamily i.representative hn (fun _ => True) := by
  rcases hG with ⟨b, e, H, hphysical, _, o, N, hN, hHigh, hOwner, hk⟩
  have hdegree : b + 3 = n := by
    have hcard := Nat.card_congr e
    have hternary : Nat.card TernaryCyclic = 3 := by
      rw [Nat.card_congr RepeatedMarkerOwnerBound.ternaryFinEquiv,
        Nat.card_fin]
    rw [Nat.card_sum, hternary, Nat.card_fin, Nat.card_fin] at hcard
    omega
  subst n
  let C : C3HighNestedCarrier.Data H :=
    ⟨o, N, hN, hHigh⟩
  let w := Nat.card o.orbit
  have hnon2 : ¬ IsPGroup 2
      (OrbitProfileFromOrbits.orbitImage (C3ComplementSource b H) o) :=
    strict_ternaryRelativeHead_not_isPGroup_two N hHigh
  obtain ⟨i, eO, himage⟩ := Non2TransitiveActionClass.orbit_cover
    (C3ComplementSource b H) o rfl hnon2
  have hn : w ≤ b + 3 := by
    have hwb := C3HighNestedCarrier.width_le H o
      (show Nat.card o.orbit = w from rfl)
    omega
  refine ⟨w, hn, i, ?_⟩
  rw [← hphysical]
  exact C3HighNestedCarrier.mem_widthCanonicalFamily_of_relabel
    H C rfl i.representative eO himage e (fun _ => True) trivial

end SymmetricSubgroupAsymptotics

end
