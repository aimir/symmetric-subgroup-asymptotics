import SymmetricSubgroupAsymptotics.C3PhysicalOwnerFirstFusion
import SymmetricSubgroupAsymptotics.TernaryHighActionDegrees

/-!
# Finite widths for the high-C3 first-owner cover

The general non-2 action index is allowed to have arbitrary width.  In the
first c=1 application the retained strict high pair and the four named
ternary inputs force the deleted owner orbit to one of six literal widths.
This file records that finite reduction on the same witness used by the
first-owner fusion chart.
-/

set_option autoImplicit false
noncomputable section
open scoped Classical

namespace SymmetricSubgroupAsymptotics

inductive C3HighWidthLabel
  | three | four | six | nine | twelve | twentySeven
  deriving DecidableEq, Fintype

def C3HighWidthLabel.width : C3HighWidthLabel → ℕ
  | .three => 3
  | .four => 4
  | .six => 6
  | .nine => 9
  | .twelve => 12
  | .twentySeven => 27

theorem C3HighWidthLabel.width_pos (d : C3HighWidthLabel) : 0 < d.width := by
  cases d <;> decide

theorem C3HighWidthLabel.exists_of_degree_menu {w : ℕ}
    (h : w = 3 ∨ w = 4 ∨ w = 6 ∨ w = 9 ∨ w = 12 ∨ w = 27) :
    ∃ d : C3HighWidthLabel, d.width = w := by
  rcases h with h3 | h4 | h6 | h9 | h12 | h27
  · exact ⟨.three, h3.symm⟩
  · exact ⟨.four, h4.symm⟩
  · exact ⟨.six, h6.symm⟩
  · exact ⟨.nine, h9.symm⟩
  · exact ⟨.twelve, h12.symm⟩
  · exact ⟨.twentySeven, h27.symm⟩

abbrev C3HighActionIndex :=
  Σ d : C3HighWidthLabel, Non2TransitiveActionClass (Fin d.width)

def c3HighAction (j : C3HighActionIndex) :
    Subgroup (Equiv.Perm (Fin j.1.width)) :=
  j.2.representative

/-- The selected first-owner orbit in the c=1 audit has one of six fixed
widths and enters the exact general non-2 first-owner family at that width. -/
theorem c3PhysicalStructuralBranch_firstOwner_mem_finiteNon2CanonicalFamily
    (hChief : PrimitiveTernaryChiefWeightBound (fun r => r / 3))
    (hWeight : PrimitiveTernaryThreeTenthsWeightBound)
    (hPrimitive : PrimitiveTernaryStrictHeadBound)
    (h18 : DegreeEighteenTernaryHeadBound)
    {n : ℕ} {G : Subgroup (Equiv.Perm (Fin n))}
    (hordinary : ¬ IsCriticalSubgroup n G)
    (owner : Fin 4)
    (howner : FirstOwned (c3PhysicalStructuralBranchMenu n) owner G) :
    ∃ (d : C3HighWidthLabel) (hn : d.width ≤ n)
      (i : Non2TransitiveActionClass (Fin d.width)),
      G ∈ FusionWidthCanonicalFamily
        (non2FirstOwnerAction d.width (owner, i)) hn
        (non2FirstOwnerPredicate c3PhysicalStructuralBranchMenu
          d.width (owner, i) (n - d.width)) := by
  rcases howner.1 with ⟨b, e, H, hphysical, o, N, hN,
    hHigh, hEarlier, hk⟩
  let A := OrbitProfileFromOrbits.orbitImage (C3ComplementSource b H) o
  letI : MulAction.IsPretransitive A o.orbit :=
    orbitImage_pretransitive (C3ComplementSource b H) o
  letI : N.Normal := hN
  have hdegrees : Nat.card o.orbit = 3 ∨ Nat.card o.orbit = 4 ∨
      Nat.card o.orbit = 6 ∨ Nat.card o.orbit = 9 ∨
      Nat.card o.orbit = 12 ∨ Nat.card o.orbit = 27 :=
    ternaryHigh_action_degree_menu
      hChief hWeight hPrimitive h18 N hHigh
  obtain ⟨d, hd⟩ := C3HighWidthLabel.exists_of_degree_menu hdegrees
  have hdegree : b + 3 = n := by
    have hcard := Nat.card_congr e
    have hternary : Nat.card TernaryCyclic = 3 := by
      rw [Nat.card_congr RepeatedMarkerOwnerBound.ternaryFinEquiv,
        Nat.card_fin]
    rw [Nat.card_sum, hternary, Nat.card_fin, Nat.card_fin] at hcard
    omega
  subst n
  let C : C3HighNestedCarrier.Data H := ⟨o, N, hN, hHigh⟩
  have hordinary' : ¬ IsCriticalSubgroup (b + 3)
      (relabelSubgroup e (C3HighNestedCarrier.physicalSubgroup H)) := by
    rwa [hphysical]
  have howner' : FirstOwned (c3PhysicalStructuralBranchMenu (b + 3)) owner
      (relabelSubgroup e (C3HighNestedCarrier.physicalSubgroup H)) := by
    rwa [hphysical]
  obtain ⟨hn, i, hmem⟩ := C.mem_non2FirstOwnerCanonicalFamily_atWidth
    c3PhysicalStructuralBranchMenu c3PhysicalStructuralBranchMenu_natural
      H hd.symm e hordinary' owner howner'
  exact ⟨d, hn, i, by simpa only [hphysical] using hmem⟩

end SymmetricSubgroupAsymptotics

end
