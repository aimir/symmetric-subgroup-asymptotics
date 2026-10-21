import SymmetricSubgroupAsymptotics.RepresentationIntrinsicRadicalDisplacement
import SymmetricSubgroupAsymptotics.LinearOrbitWitnessCardBound

/-! A few original orbit points per nonzero quotient representative
replace a full stabilizer count. The full intrinsic radical supplies
both invariance and state-killing on the SAME original representation. -/
set_option autoImplicit false
noncomputable section
namespace SymmetricSubgroupAsymptotics

theorem submodule_le_of_intrinsic_radical_orbit_witnesses
    {k G V C : Type*} [Field k] [Group G] [Finite G]
    [AddCommGroup V] [Module k V] [AddCommGroup C] [Module k C]
    (rho : Representation k G V) (W : Subrepresentation rho)
    (S R : Submodule k V) (hS : W.toSubmodule = S)
    (hR : (Representation.Coinvariants.ker W.toRepresentation).map
      W.toSubmodule.subtype = R)
    (projection : V →ₗ[k] C) (sectionMap : C →ₗ[k] V)
    (hdefect : ∀ v, v - sectionMap (projection v) ∈ S)
    (m : ℕ)
    (hwitness : ∀ c : C, c ≠ 0 → ∃ u : Fin m → G,
      ∀ i j : Fin m, i ≠ j →
        rho (u i) (sectionMap c) - rho (u j) (sectionMap c) ∉ R)
    (D : Subgroup G) (hlarge : Nat.card G < m * Nat.card D)
    (K : Submodule k V)
    (hfixed : ∀ d : D, ∀ v ∈ K, rho (d : G) v - v ∈ R) : K ≤ S := by
  have hkill (g : G) (v : V) (hv : v ∈ S) : rho g v - v ∈ R :=
    subrepresentation_displacement_mem_of_radical_eq rho W S R hS hR g v hv
  have hRS : R ≤ S := by
    rw [← hR, ← hS]
    rintro z ⟨w, _, rfl⟩
    exact w.property
  have hstable (g : G) (z : V) (hz : z ∈ R) : rho g z ∈ R := by
    simpa only [sub_add_cancel] using R.add_mem (hkill g z (hRS hz)) hz
  intro v hv
  by_contra hvS
  have hc : projection v ≠ 0 := by
    intro hz
    have hd := hdefect v
    rw [hz, map_zero, sub_zero] at hd
    exact hvS hd
  obtain ⟨u, hu⟩ := hwitness (projection v) hc
  have hsep (i j : Fin m) (hne : i ≠ j) : rho (u i) v - rho (u j) v ∉ R := by
    intro hbad
    have hi := hkill (u i) _ (hdefect v)
    have hj := hkill (u j) _ (hdefect v)
    rw [map_sub] at hi hj
    have hd : (rho (u i) v - rho (u j) v) -
        (rho (u i) (sectionMap (projection v)) -
          rho (u j) (sectionMap (projection v))) ∈ R := by
      convert R.sub_mem hi hj using 1 <;> abel
    apply hu i j hne
    convert R.sub_mem hbad hd using 1 <;> abel
  have hcard := subgroup_card_mul_le_of_linear_orbit_witnesses
    rho R hstable v u hsep D (fun d => hfixed d v hv)
  exact (not_lt_of_ge hcard) hlarge

end SymmetricSubgroupAsymptotics
