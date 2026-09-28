import SymmetricSubgroupAsymptotics.Non2UnipotentPrefixPhysicalOwner
import SymmetricSubgroupAsymptotics.Non2NoSelectedResidual
import SymmetricSubgroupAsymptotics.Non2OutsideOrbitMenu
import SymmetricSubgroupAsymptotics.RepeatedMarkerOwnerBound

/-!
# Exhaustion after the physical E7 unipotent-prefix owner

The active residual alphabet is orbitwise: every original orbit image is
binary, the natural three-point `S3` action, or one of the eight selected
unipotent-prefix pair actions.  This formulation retains the literal orbit
and its actual pair frame.  If a complete subgroup is still residual after
the concrete E7-UP-H/C owner, the selected alternative is impossible.
Consequently the whole subgroup satisfies the already counted repeated-marker
`Fits` predicate.

This closes both application interfaces without a new numerical row.  An
outside-`Fits` residual cannot exist, and the marker-free O02 residual enters
the intrinsic `O^2` contradiction.  Marked states are routed into the existing
complete repeated-marker owner, which already has the typed binary handoff.
-/

set_option autoImplicit false
noncomputable section
open scoped Classical

namespace SymmetricSubgroupAsymptotics
namespace Non2UnipotentPrefixFiniteMenu

/-- One actual orbit is a selected eight-width UP pair orbit.  The frame is
retained propositionally, so it creates no counted frame multiplicity. -/
def SelectedUPPairOrbitAt {n : ℕ}
    (H : Subgroup (Equiv.Perm (Fin n)))
    (o : OrbitProfileFromOrbits.Orbit H) : Prop :=
  ∃ d : PairCountLabel,
    Nat.card o.orbit = d.sourceDegree ∧
      ¬ IsPGroup 2 (OrbitProfileFromOrbits.orbitImage H o) ∧
      Nonempty (BinaryPairFrame
        (OrbitProfileFromOrbits.orbitImage H o) (Fin d.pairCount))

/-- The exact post-alphabet orbit trichotomy.  The natural-`S3` clause is
the literal original three-point action used by the repeated-marker owner. -/
def UPResidualOrbitCovered {n : ℕ}
    (H : Subgroup (Equiv.Perm (Fin n))) : Prop :=
  ∀ o : OrbitProfileFromOrbits.Orbit H,
    IsPGroup 2 (OrbitProfileFromOrbits.orbitImage H o) ∨
      (∃ e : Fin 3 ≃ o.orbit,
        relabelSubgroup e oddMarkerActionSubgroup =
          OrbitProfileFromOrbits.orbitImage H o) ∨
      SelectedUPPairOrbitAt H o

theorem hasSelectedUPPairOrbit_iff {n : ℕ}
    (H : Subgroup (Equiv.Perm (Fin n))) :
    HasSelectedUPPairOrbit H ↔
      ∃ o : OrbitProfileFromOrbits.Orbit H, SelectedUPPairOrbitAt H o := by
  constructor
  · rintro ⟨d, o, hw, hnon2, hframe⟩
    exact ⟨o, d, hw, hnon2, hframe⟩
  · rintro ⟨o, d, hw, hnon2, hframe⟩
    exact ⟨d, o, hw, hnon2, hframe⟩

/-- Removing every selected UP orbit from the orbitwise trichotomy leaves
exactly the complete binary/natural-`S3` alphabet. -/
theorem fits_of_UPResidualOrbitCovered_of_noSelected
    {n : ℕ} (H : Subgroup (Equiv.Perm (Fin n)))
    (hcover : UPResidualOrbitCovered H)
    (hnone : ¬ HasSelectedUPPairOrbit H) :
    RepeatedMarkerOrbitProfiles.Fits H := by
  intro o
  rcases hcover o with hbinary | hmarker | hselected
  · exact Or.inl hbinary
  · exact Or.inr hmarker
  · exact False.elim
      (hnone ((hasSelectedUPPairOrbit_iff H).2 ⟨o, hselected⟩))

/-- A first-owned E7 residual satisfying the active orbit alphabet is already
in the complete repeated-marker owner. -/
theorem fits_of_firstOwned_e7UPResidual
    (hTracey : TraceyBinaryFormulaInput)
    (hExceptional : TraceyBinaryExceptionalThreeInput)
    {n : ℕ} (H : Subgroup (Equiv.Perm (Fin n)))
    (hordinary : ¬ IsCriticalSubgroup n H)
    (howner : FirstOwned
      (ownerOrResidualEligible
        (e7UPPhysicalOwnerMenu hTracey hExceptional) n)
      (Fin.last 2) H)
    (hcover : UPResidualOrbitCovered H) :
    RepeatedMarkerOrbitProfiles.Fits H := by
  apply fits_of_UPResidualOrbitCovered_of_noSelected H hcover
  intro hUP
  exact not_firstOwned_e7UPResidual_of_selectedUPPairOrbit
    hTracey hExceptional H hordinary hUP howner

/-- The orbitwise residual theorem closes the entire outside-`Fits` child:
if such a subgroup were unowned, the appended residual branch would be first,
forcing `Fits` and contradicting its literal source predicate. -/
theorem e7UPPhysicalOwnerMenu_covers_outside
    (hTracey : TraceyBinaryFormulaInput)
    (hExceptional : TraceyBinaryExceptionalThreeInput)
    {n : ℕ} (H : Subgroup (Equiv.Perm (Fin n)))
    (hH : H ∈ RepeatedMarkerOwnerBound.OutsideFitsSubgroupSetAt n)
    (hcover : UPResidualOrbitCovered H) :
    ∃ j : Fin 2,
      e7UPPhysicalOwnerMenu hTracey hExceptional n j H := by
  by_contra hnone
  have hunowned : ∀ j : Fin 2,
      ¬ e7UPPhysicalOwnerMenu hTracey hExceptional n j H := by
    intro j hj
    exact hnone ⟨j, hj⟩
  have howner : FirstOwned
      (ownerOrResidualEligible
        (e7UPPhysicalOwnerMenu hTracey hExceptional) n)
      (Fin.last 2) H :=
    (firstOwned_ownerOrResidual_last_iff
      (e7UPPhysicalOwnerMenu hTracey hExceptional) H).2 hunowned
  exact hH.2 (fits_of_firstOwned_e7UPResidual
    hTracey hExceptional H hH.1 howner hcover)

/-- The complete residual state after E7, before splitting marker-free O02
from marked O03.  Its orbitwise alphabet is part of the physical state. -/
structure AfterE7Residual
    (hTracey : TraceyBinaryFormulaInput)
    (hExceptional : TraceyBinaryExceptionalThreeInput)
    (n : ℕ) where
  subgroup : Subgroup (Equiv.Perm (Fin n))
  ordinary : ¬ IsCriticalSubgroup n subgroup
  residual : FirstOwned
    (ownerOrResidualEligible
      (e7UPPhysicalOwnerMenu hTracey hExceptional) n)
    (Fin.last 2) subgroup
  orbitCovered : UPResidualOrbitCovered subgroup

theorem AfterE7Residual.fits
    (hTracey : TraceyBinaryFormulaInput)
    (hExceptional : TraceyBinaryExceptionalThreeInput)
    {n : ℕ} (S : AfterE7Residual hTracey hExceptional n) :
    RepeatedMarkerOrbitProfiles.Fits S.subgroup :=
  fits_of_firstOwned_e7UPResidual hTracey hExceptional S.subgroup
    S.ordinary S.residual S.orbitCovered

/-- The marked O03 remainder is not a new outside-frontier family: every
post-E7 residual enters the already checked complete `Fits` owner with its
literal subgroup unchanged. -/
def afterE7ResidualEmbedding
    (hTracey : TraceyBinaryFormulaInput)
    (hExceptional : TraceyBinaryExceptionalThreeInput)
    (N epsilon : ℕ) :
    AfterE7Residual hTracey hExceptional (2 * N + epsilon) ↪
      RepeatedMarkerOwnerBound.OrdinaryFullFamily N epsilon where
  toFun S := ⟨S.subgroup, S.fits hTracey hExceptional, S.ordinary⟩
  inj' := by
    intro S T h
    have hsub : S.subgroup = T.subgroup := congrArg
      (fun K : RepeatedMarkerOwnerBound.OrdinaryFullFamily N epsilon => K.1) h
    cases S
    cases T
    simp_all

/-- The complete marker-free O02 state after E7.  Every hypothesis is an
intrinsic property of the same original subgroup. -/
structure O02AfterE7Residual
    (hTracey : TraceyBinaryFormulaInput)
    (hExceptional : TraceyBinaryExceptionalThreeInput)
    (n : ℕ) extends AfterE7Residual hTracey hExceptional n where
  markerFree :
    RepeatedMarkerOrbitProfiles.orbitCount subgroup 1 +
      RepeatedMarkerOrbitProfiles.orbitCount subgroup 3 = 0
  nontrivialTwoResidual : terminalTwoResidual subgroup ≠ ⊥

/-- Full O02 exhaustion after E7, including nonabelian proper subdirect
products: the selected branch is E7-owned, while the remaining simultaneous
orbit image is a `2`-group and has trivial literal `O^2` residual. -/
theorem o02AfterE7Residual_isEmpty
    (hTracey : TraceyBinaryFormulaInput)
    (hExceptional : TraceyBinaryExceptionalThreeInput)
    (n : ℕ) :
    IsEmpty (O02AfterE7Residual hTracey hExceptional n) := by
  refine ⟨?_⟩
  intro S
  have hfits : RepeatedMarkerOrbitProfiles.Fits S.subgroup :=
    S.toAfterE7Residual.fits hTracey hExceptional
  let T : NoSelectedNonbinaryResidual (Fin n) :=
    ⟨S.subgroup, hfits, S.markerFree, S.nontrivialTwoResidual⟩
  letI : IsEmpty (NoSelectedNonbinaryResidual (Fin n)) :=
    noSelectedNonbinaryResidual_isEmpty (Fin n)
  exact isEmptyElim T

end Non2UnipotentPrefixFiniteMenu
end SymmetricSubgroupAsymptotics

end
