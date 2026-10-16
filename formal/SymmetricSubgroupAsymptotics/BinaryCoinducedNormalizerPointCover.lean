import SymmetricSubgroupAsymptotics.CoinducedNormalizerOrbitHead
import SymmetricSubgroupAsymptotics.BinaryPairTernaryOrbitHead

/-! Bounded point witnesses for an original binary-plane frame. An actual
Sylow-three subgroup kills every fixed-point fibre. One element normalizing
that Sylow may join its moving orbits. A cover by n displayed combined
orbits therefore bounds every subrepresentation head by 2n, independently
of the chosen original local epimorphism and its twist. -/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
open scoped Classical

namespace SymmetricSubgroupAsymptotics.BinaryCoinducedNormalizerPointCover

variable {G : Type} [Group G] [Finite G]

private def active (H P A : Subgroup G)
    [Fintype (DoubleCoset.Quotient (H : Set G) (A : Set G))] :=
  Finset.univ.filter (fun q : DoubleCoset.Quotient (H : Set G) (A : Set G) =>
    inducedOrbitStabilizer H P q.out ≠ ⊤)

omit [Finite G] in
private theorem active_card_le (H P A : Subgroup G)
    [Fintype (DoubleCoset.Quotient (H : Set G) (A : Set G))]
    {n : ℕ} (representative : Fin n → G ⧸ H)
    (cover : ∀ z : G ⧸ H, z ∈ MulAction.fixedPoints P (G ⧸ H) ∨
      ∃ j : Fin n, z ∈ MulAction.orbit A (representative j)) :
    (active H P A).card ≤ n := by
  have chooseOrbit (q : active H P A) : ∃ j : Fin n,
      inducedDoubleCosetToOrbit H A q.1 = Quotient.mk'' (representative j) := by
    have hnot : inducedOrbitStabilizer H P q.1.out ≠ ⊤ :=
      (Finset.mem_filter.mp q.2).2
    let z : G ⧸ H := ((q.1.out⁻¹ : G) : G ⧸ H)
    rcases cover z with hz | ⟨j, hj⟩
    · apply False.elim
      apply hnot
      rw [inducedOrbitStabilizer_eq]
      apply top_unique
      intro p _
      exact hz p
    · refine ⟨j, ?_⟩
      have hq : inducedDoubleCosetToOrbit H A q.1 = Quotient.mk'' z :=
        (congrArg (inducedDoubleCosetToOrbit H A) (DoubleCoset.out_eq' H A q.1)).symm
      apply hq.trans
      apply Quotient.sound
      exact (MulAction.orbitRel_apply).mpr hj
  let index : active H P A → Fin n := fun q => Classical.choose (chooseOrbit q)
  have hinj : Function.Injective index := by
    intro q r h
    apply Subtype.ext
    apply inducedDoubleCosetToOrbit_injective H A
    exact (Classical.choose_spec (chooseOrbit q)).trans
      ((congrArg (fun j : Fin n =>
        (Quotient.mk'' (representative j) : MulAction.orbitRel.Quotient A (G ⧸ H))) h).trans
          (Classical.choose_spec (chooseOrbit r)).symm)
  simpa only [Nat.card_eq_fintype_card, Fintype.card_coe, Fintype.card_fin] using
    Nat.card_le_card_of_injective index hinj

local instance normalizerPointCover_three : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩

/-- Only a point-orbit cover is required; all vanishing local fibres are
proved from the actual ambient Sylow and original local epimorphism. -/
theorem head_le_twice_cover
    {L V : Type} [Group L] [Finite L] [AddCommGroup V] [Module (ZMod 2) V]
    [FiniteDimensional (ZMod 2) V]
    (H : Subgroup G) (P : Sylow 3 G) (g : G)
    (hg : g ∈ Subgroup.normalizer ((P : Subgroup G) : Set G))
    {n : ℕ} (representative : Fin n → G ⧸ H)
    (cover : ∀ z : G ⧸ H, z ∈ MulAction.fixedPoints P (G ⧸ H) ∨
      ∃ j : Fin n, z ∈ MulAction.orbit ↥((P : Subgroup G) ⊔ Subgroup.zpowers g)
        (representative j))
    (f : H →* L) (hf : Function.Surjective f)
    (rho : Representation (ZMod 2) L V) (hL : Nat.card L = 3 ∨ Nat.card L = 6)
    (hdim : Module.finrank (ZMod 2) V = 2) (hrho : Function.Injective rho)
    (B : Subrepresentation (Representation.coind H.subtype (rho.comp f))) :
    Module.finrank (ZMod 2)
      (B.toRepresentation.IntertwiningMap (Representation.trivial (ZMod 2) G (ZMod 2)))
      ≤ 2 * n := by
  let A : Subgroup G := (P : Subgroup G) ⊔ Subgroup.zpowers g
  have hPA : (P : Subgroup G) ≤ A := le_sup_left
  letI : Finite (DoubleCoset.Quotient (H : Set G) (A : Set G)) :=
    Finite.of_injective (inducedDoubleCosetToOrbit H A)
      (inducedDoubleCosetToOrbit_injective H A)
  letI : Fintype (DoubleCoset.Quotient (H : Set G) (A : Set G)) := Fintype.ofFinite _
  have hcount : (active H (P : Subgroup G) A).card ≤ n :=
    active_card_le H (P : Subgroup G) A representative cover
  have hodd : ¬ 2 ∣ Nat.card P := by
    obtain ⟨m, hm⟩ := P.isPGroup'.exists_card_eq
    rw [hm]
    intro h
    exact (by decide : ¬ 2 ∣ 3) (Nat.prime_two.dvd_of_dvd_pow h)
  have hunit : IsUnit (Nat.card P : ZMod 2) :=
    isUnit_iff_ne_zero.mpr ((ZMod.natCast_eq_zero_iff (Nat.card P) 2).not.mpr hodd)
  have hinactive : ∀ q, q ∉ active H (P : Subgroup G) A →
      CoinducedOrbitFixedHead.fibreFixedSpace H A (rho.comp f) q = ⊥ := by
    intro q hq
    have hfull : inducedOrbitStabilizer H (P : Subgroup G) q.out = ⊤ := by
      simpa only [active, Finset.mem_filter, Finset.mem_univ, true_and, not_not] using hq
    exact BinaryCoinducedSylowOrbitHead.fibre_invariants_eq_bot_of_sylow_full_stabilizer
      H P A hPA f hf rho hL hdim hrho q.out hfull
  have hhead := CoinducedNormalizerOrbitHead.subrepresentation_head_le_active
    H (P : Subgroup G) (rho.comp f) g hunit hg
    (active H (P : Subgroup G) A) hinactive B
  rw [hdim] at hhead
  omega

/-- Concrete certificates can be checked on the original physical points.
The original point stabilizer and its given local epimorphism are unchanged. -/
theorem head_le_twice_cover_on_points
    {X L V : Type} [MulAction G X] [MulAction.IsPretransitive G X]
    [Group L] [Finite L] [AddCommGroup V] [Module (ZMod 2) V]
    [FiniteDimensional (ZMod 2) V]
    (x : X) (P : Sylow 3 G) (g : G)
    (hg : g ∈ Subgroup.normalizer ((P : Subgroup G) : Set G))
    {n : ℕ} (representative : Fin n → X)
    (cover : ∀ z : X, z ∈ MulAction.fixedPoints P X ∨
      ∃ j : Fin n, z ∈ MulAction.orbit ↥((P : Subgroup G) ⊔ Subgroup.zpowers g)
        (representative j))
    (f : MulAction.stabilizer G x →* L) (hf : Function.Surjective f)
    (rho : Representation (ZMod 2) L V) (hL : Nat.card L = 3 ∨ Nat.card L = 6)
    (hdim : Module.finrank (ZMod 2) V = 2) (hrho : Function.Injective rho)
    (B : Subrepresentation
      (Representation.coind (MulAction.stabilizer G x).subtype (rho.comp f))) :
    Module.finrank (ZMod 2)
      (B.toRepresentation.IntertwiningMap (Representation.trivial (ZMod 2) G (ZMod 2)))
      ≤ 2 * n := by
  let H := MulAction.stabilizer G x
  let e : G ⧸ H ≃ X := BinaryPairTernaryOrbitHead.pointCosetEquiv x
  apply head_le_twice_cover H P g hg (fun j => e.symm (representative j)) _
    f hf rho hL hdim hrho B
  intro z
  rcases cover (e z) with hz | ⟨j, hj⟩
  · left
    intro p
    apply e.injective
    change BinaryPairTernaryOrbitHead.pointCosetEquiv x ((p : G) • z) = e z
    rw [BinaryPairTernaryOrbitHead.pointCosetEquiv_smul]
    exact hz p
  · right
    obtain ⟨a, ha⟩ := MulAction.mem_orbit_iff.mp hj
    refine ⟨j, MulAction.mem_orbit_iff.mpr ⟨a, ?_⟩⟩
    apply e.injective
    change BinaryPairTernaryOrbitHead.pointCosetEquiv x
      ((a : G) • e.symm (representative j)) = e z
    rw [BinaryPairTernaryOrbitHead.pointCosetEquiv_smul, e.apply_symm_apply]
    exact ha

end SymmetricSubgroupAsymptotics.BinaryCoinducedNormalizerPointCover

end
