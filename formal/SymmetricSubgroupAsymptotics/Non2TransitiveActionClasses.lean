import SymmetricSubgroupAsymptotics.FusionOrbitRepresentativeCharts
import SymmetricSubgroupAsymptotics.FusionWidthPhysical
import SymmetricSubgroupAsymptotics.OrbitProfileFromOrbits
import Mathlib.Data.Quot

/-!
# Complete original non-2 transitive action representatives

The growing complete-quotient transfer is indexed by actual transitive
permutation actions, modulo conjugacy on their original point set.  This file
constructs that index without an abstract-group replacement and proves that
every literal non-2 orbit enters one chosen representative family while its
entire complementary action is retained.
-/

set_option autoImplicit false
noncomputable section
open scoped Classical Pointwise

namespace SymmetricSubgroupAsymptotics

/-- Actual transitive permutation subgroups which are not 2-groups. -/
abbrev Non2TransitiveAction (X : Type) :=
  {U : Subgroup (Equiv.Perm X) //
    ¬ IsPGroup 2 U ∧ MulAction.IsPretransitive U X}

/-- Equality of non-2 action classes is ambient permutation conjugacy on the
same original point set. -/
def non2TransitiveActionSetoid (X : Type) : Setoid (Non2TransitiveAction X) where
  r A B := ∃ c : Equiv.Perm X, MulAut.conj c • A.1 = B.1
  iseqv := {
    refl := fun A => ⟨1, by rw [map_one, one_smul]⟩
    symm := by
      rintro A B ⟨c, hc⟩
      refine ⟨c⁻¹, ?_⟩
      rw [← hc, ← mul_smul, ← map_mul, inv_mul_cancel, map_one, one_smul]
    trans := by
      rintro A B C ⟨c, hc⟩ ⟨d, hd⟩
      refine ⟨d * c, ?_⟩
      rw [map_mul, mul_smul, hc, hd] }

/-- The complete conjugacy-class index for original non-2 transitive
actions. -/
abbrev Non2TransitiveActionClass (X : Type) :=
  Quotient (non2TransitiveActionSetoid X)

namespace Non2TransitiveActionClass

variable {X : Type}

instance instFinite [Finite X] : Finite (Non2TransitiveActionClass X) := by
  unfold Non2TransitiveActionClass
  infer_instance

instance instFintype [Finite X] : Fintype (Non2TransitiveActionClass X) :=
  Fintype.ofFinite _

/-- One literal original permutation subgroup chosen from each class. -/
def representative (i : Non2TransitiveActionClass X) :
    Subgroup (Equiv.Perm X) :=
  i.out.1

theorem representative_not_isPGroup (i : Non2TransitiveActionClass X) :
    ¬ IsPGroup 2 i.representative :=
  i.out.2.1

instance representative_pretransitive (i : Non2TransitiveActionClass X) :
    MulAction.IsPretransitive i.representative X :=
  i.out.2.2

/-- Conjugate chosen representatives have the same class label. -/
theorem representative_separated
    (i j : Non2TransitiveActionClass X) (c : Equiv.Perm X)
    (hc : MulAut.conj c • i.representative = j.representative) : i = j := by
  have h : Quotient.mk (non2TransitiveActionSetoid X) i.out =
      Quotient.mk (non2TransitiveActionSetoid X) j.out :=
    Quotient.sound ⟨c, hc⟩
  exact (Quotient.out_eq i).symm.trans (h.trans (Quotient.out_eq j))

/-- Every actual non-2 transitive subgroup is conjugate, on its original
points, to one chosen representative. -/
theorem representative_cover (U : Subgroup (Equiv.Perm X))
    (hU : ¬ IsPGroup 2 U) (htrans : MulAction.IsPretransitive U X) :
    ∃ i : Non2TransitiveActionClass X, ∃ c : Equiv.Perm X,
      MulAut.conj c • U = i.representative := by
  let A : Non2TransitiveAction X := ⟨U, hU, htrans⟩
  let i : Non2TransitiveActionClass X := Quotient.mk _ A
  obtain ⟨c, hc⟩ := Quotient.mk_out (s := non2TransitiveActionSetoid X) A
  refine ⟨i, c⁻¹, ?_⟩
  change MulAut.conj c • i.representative = U at hc
  rw [← hc, ← mul_smul, ← map_mul, inv_mul_cancel, map_one, one_smul]

private theorem relabel_eq_conj (c : Equiv.Perm X)
    (V : Subgroup (Equiv.Perm X)) :
    relabelSubgroup c V = MulAut.conj c • V := by
  change V.map c.permCongrHom.toMonoidHom = _
  rw [Subgroup.pointwise_smul_def]
  congr 1

section OriginalOrbits

variable [Fintype X] (H : Subgroup (Equiv.Perm X))

/-- Every literal non-2 orbit image is conjugate to one chosen original
action representative of the same exact degree.  The target equivalence is
kept explicit so that the complementary action can later be charted without
forgetting any correlations with this orbit. -/
theorem orbit_cover {w : ℕ} (o : OrbitProfileFromOrbits.Orbit H)
    (hcard : Nat.card o.orbit = w)
    (hnon2 : ¬ IsPGroup 2 (OrbitProfileFromOrbits.orbitImage H o)) :
    ∃ i : Non2TransitiveActionClass (Fin w), ∃ e : Fin w ≃ o.orbit,
      relabelSubgroup e i.representative =
        OrbitProfileFromOrbits.orbitImage H o := by
  letI : Fintype o.orbit := Fintype.ofFinite _
  let e : Fin w ≃ o.orbit := (Finite.equivFinOfCardEq hcard).symm
  let V : Subgroup (Equiv.Perm (Fin w)) :=
    relabelSubgroup e.symm (OrbitProfileFromOrbits.orbitImage H o)
  have hV : ¬ IsPGroup 2 V := by
    intro hp
    have hp' := hp.map e.permCongrHom.toMonoidHom
    change IsPGroup 2 (relabelSubgroup e V) at hp'
    have heV : relabelSubgroup e V =
        OrbitProfileFromOrbits.orbitImage H o := by
      dsimp only [V]
      exact relabelSubgroup_symm e.symm _
    rw [heV] at hp'
    exact hnon2 hp'
  have htrans : MulAction.IsPretransitive V (Fin w) := by
    constructor
    intro x y
    obtain ⟨h,hh⟩ := MulAction.exists_smul_eq H (e x) (e y)
    let v : V := ⟨e.symm.permCongr (MulAction.toPermHom H o.orbit h), by
      change _ ∈ (OrbitProfileFromOrbits.orbitImage H o).map
        e.symm.permCongrHom.toMonoidHom
      exact ⟨MulAction.toPermHom H o.orbit h, ⟨h,rfl⟩, rfl⟩⟩
    refine ⟨v, ?_⟩
    change e.symm (h • e x) = y
    rw [hh, Equiv.symm_apply_apply]
  obtain ⟨i,c,hc⟩ := representative_cover V hV htrans
  have hc' : relabelSubgroup c V = i.representative :=
    (relabel_eq_conj c V).trans hc
  refine ⟨i, c.symm.trans e, ?_⟩
  change relabelSubgroup (c.symm.trans e) i.representative = _
  calc
    _ = relabelSubgroup e (relabelSubgroup c.symm i.representative) :=
      (relabelSubgroup_trans c.symm e i.representative).symm
    _ = relabelSubgroup e V := by rw [← hc', relabelSubgroup_symm]
    _ = _ := relabelSubgroup_symm e.symm
      (OrbitProfileFromOrbits.orbitImage H o)

end OriginalOrbits

end Non2TransitiveActionClass

namespace FusionOrbitRepresentativeCharts

/-- Every actual non-2 orbit enters one chosen original action family.  The
same subgroup supplies both restriction coordinates, so the complement and
all correlations with it remain literal. -/
theorem exists_non2_canonicalFamily {n w : ℕ}
    (H : Subgroup (Equiv.Perm (Fin n))) (x : Fin n)
    (hw : Nat.card (MulAction.orbit H x) = w)
    (hP : ¬ IsPGroup 2 (FusionActualOrbitCharts.orbitImage H x))
    (hn : w ≤ n) :
    ∃ i : Non2TransitiveActionClass (Fin w),
      H ∈ FusionWidthCanonicalFamily i.representative hn (fun _ => True) := by
  have hchart :
      ¬ IsPGroup 2 (FusionActualOrbitCharts.chartAction H x hw) := by
    intro hp
    exact hP (hp.of_equiv (FusionActualOrbitCharts.imageEquiv H x hw).symm)
  obtain ⟨i, c, hc⟩ := Non2TransitiveActionClass.representative_cover
    (FusionActualOrbitCharts.chartAction H x hw) hchart
      (FusionActualOrbitCharts.chartAction_transitive H x hw)
  refine ⟨i, fusionWidthCanonicalFamily_of_chart i.representative hn H
    (chart H x hw c) (chart_preserves H x hw c) ?_
      (fun _ => True) trivial⟩
  exact (projection_eq H x hw c).trans hc

end FusionOrbitRepresentativeCharts

end SymmetricSubgroupAsymptotics

end
