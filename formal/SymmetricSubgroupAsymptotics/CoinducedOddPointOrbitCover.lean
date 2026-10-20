import SymmetricSubgroupAsymptotics.CoinducedOrbitFixedHead
import SymmetricSubgroupAsymptotics.BinaryPairTernaryOrbitHead

/-! An odd subgroup with a small cover of the original point action gives
a uniform head bound for every coinduced local representation. This uses
all orbit fibres, so neither a Sylow condition nor a local quotient-kernel
classification is needed. The local conjugation twists remain unchanged. -/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
open scoped Classical

namespace SymmetricSubgroupAsymptotics.CoinducedOddPointOrbitCover

variable {k G V : Type} [Field k] [Group G] [Finite G]
    [AddCommGroup V] [Module k V] [FiniteDimensional k V]

theorem head_le_of_coset_cover (H A : Subgroup G)
    (hodd : IsUnit (Nat.card A : k)) {n : ℕ}
    (representative : Fin n → G ⧸ H)
    (cover : ∀ z : G ⧸ H, ∃ j : Fin n, z ∈ MulAction.orbit A (representative j))
    (rho : Representation k H V)
    (B : Subrepresentation (Representation.coind H.subtype rho)) :
    Module.finrank k
      (B.toRepresentation.IntertwiningMap (Representation.trivial k G k)) ≤
      n * Module.finrank k V := by
  let orbitMap : Fin n → MulAction.orbitRel.Quotient A (G ⧸ H) :=
    fun j => Quotient.mk'' (representative j)
  have honto : Function.Surjective orbitMap := by
    intro q
    refine Quotient.inductionOn q ?_
    intro z
    obtain ⟨j, hj⟩ := cover z
    exact ⟨j, (Quotient.sound ((MulAction.orbitRel_apply).mpr hj)).symm⟩
  have hcount : Nat.card (DoubleCoset.Quotient (H : Set G) (A : Set G)) ≤ n := by
    rw [Nat.card_congr (inducedDoubleCosetOrbitEquiv H A)]
    simpa only [Nat.card_fin] using Nat.card_le_card_of_surjective orbitMap honto
  letI : Finite (DoubleCoset.Quotient (H : Set G) (A : Set G)) :=
    Finite.of_injective (inducedDoubleCosetToOrbit H A)
      (inducedDoubleCosetToOrbit_injective H A)
  letI : Fintype (DoubleCoset.Quotient (H : Set G) (A : Set G)) := Fintype.ofFinite _
  have hhead := CoinducedOrbitFixedHead.subrepresentation_head_le_active
    H A rho hodd Finset.univ (by intro q hq; simp at hq) B
  have hc : (Finset.univ : Finset
      (DoubleCoset.Quotient (H : Set G) (A : Set G))).card ≤ n := by
    simpa only [Finset.card_univ, Nat.card_eq_fintype_card] using hcount
  exact hhead.trans (Nat.mul_le_mul_right _ hc)

/-- Only orbit equations on the actual original points are used. -/
theorem head_le_of_point_cover
    {X : Type} [MulAction G X] [MulAction.IsPretransitive G X]
    (x : X) (A : Subgroup G) (hodd : IsUnit (Nat.card A : k)) {n : ℕ}
    (representative : Fin n → X)
    (cover : ∀ z : X, ∃ j : Fin n, z ∈ MulAction.orbit A (representative j))
    (rho : Representation k (MulAction.stabilizer G x) V)
    (B : Subrepresentation
      (Representation.coind (MulAction.stabilizer G x).subtype rho)) :
    Module.finrank k
      (B.toRepresentation.IntertwiningMap (Representation.trivial k G k)) ≤
      n * Module.finrank k V := by
  let H := MulAction.stabilizer G x
  let e : G ⧸ H ≃ X := BinaryPairTernaryOrbitHead.pointCosetEquiv x
  apply head_le_of_coset_cover H A hodd (fun j => e.symm (representative j)) _ rho B
  intro z
  obtain ⟨j, a, ha⟩ := (cover (e z)).imp (fun j hj => MulAction.mem_orbit_iff.mp hj)
  refine ⟨j, MulAction.mem_orbit_iff.mpr ⟨a, ?_⟩⟩
  apply e.injective
  change BinaryPairTernaryOrbitHead.pointCosetEquiv x
    ((a : G) • e.symm (representative j)) = e z
  rw [BinaryPairTernaryOrbitHead.pointCosetEquiv_smul, e.apply_symm_apply]
  exact ha

/-- A displayed odd power suffices; the exact element order and ambient
group order do not need to be computed. -/
theorem binary_head_le_of_odd_cyclic_cover
    {X W : Type} [MulAction G X] [MulAction.IsPretransitive G X]
    [AddCommGroup W] [Module (ZMod 2) W] [FiniteDimensional (ZMod 2) W]
    (x : X) (g : G) (m : ℕ) (hmodd : ¬ 2 ∣ m) (hgm : g ^ m = 1)
    {n : ℕ} (representative : Fin n → X)
    (cover : ∀ z : X, ∃ j : Fin n, ∃ e : ℕ, g ^ e • representative j = z)
    (rho : Representation (ZMod 2) (MulAction.stabilizer G x) W)
    (B : Subrepresentation
      (Representation.coind (MulAction.stabilizer G x).subtype rho)) :
    Module.finrank (ZMod 2)
      (B.toRepresentation.IntertwiningMap (Representation.trivial (ZMod 2) G (ZMod 2))) ≤
      n * Module.finrank (ZMod 2) W := by
  let A := Subgroup.zpowers g
  have hcard : Nat.card A ∣ m := by
    rw [Nat.card_zpowers]
    exact orderOf_dvd_of_pow_eq_one hgm
  have hAodd : ¬ 2 ∣ Nat.card A := fun h => hmodd (h.trans hcard)
  have hunit : IsUnit (Nat.card A : ZMod 2) :=
    isUnit_iff_ne_zero.mpr ((ZMod.natCast_eq_zero_iff (Nat.card A) 2).not.mpr hAodd)
  apply head_le_of_point_cover x A hunit representative _ rho B
  intro z
  obtain ⟨j, e, he⟩ := cover z
  exact ⟨j, MulAction.mem_orbit_iff.mpr
    ⟨⟨g ^ e, A.pow_mem (Subgroup.mem_zpowers g) e⟩, he⟩⟩

end SymmetricSubgroupAsymptotics.CoinducedOddPointOrbitCover

end
