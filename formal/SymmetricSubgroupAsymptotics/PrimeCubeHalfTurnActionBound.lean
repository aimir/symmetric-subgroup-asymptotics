import SymmetricSubgroupAsymptotics.PrimeCubeCentralSubgroupBounds
import Mathlib.GroupTheory.GroupAction.Quotient

/-! A half-turn on the projective lines of an extraspecial prime-cube
subgroup forces two distinct large orbits. Only the absence of a fixed
index-prime overgroup of the derived subgroup is used: no transitivity
on all projective lines or prescribed order of the normalizer is assumed. -/
set_option autoImplicit false
noncomputable section
namespace SymmetricSubgroupAsymptotics.PrimeCubeHalfTurnActionBound
open MulAction PrimeCubeCentralSubgroupBounds

variable {R X : Type*} [Group R] [Finite R] [Finite X] [MulAction R X]
variable {p : ℕ}

private theorem stabilizer_card_one_or_prime (hp : p.Prime)
    (hR : Nat.card R = p ^ 3) (hZ : Nat.card (commutator R) = p)
    (x : X) (hx : ¬ commutator R ≤ stabilizer R x) :
    Nat.card (stabilizer R x) = 1 ∨ Nat.card (stabilizer R x) = p := by
  have hsmall := card_le_prime_of_not_contains_derived hp hR
    (commutator R) (stabilizer R x) rfl hx
  obtain ⟨e, _, he⟩ := (Nat.dvd_prime_pow hp).mp
    (hR ▸ (stabilizer R x).card_subgroup_dvd_card)
  have hle : e ≤ 1 := (Nat.pow_le_pow_iff_right hp.one_lt).mp
    (by simpa only [he, pow_one] using hsmall)
  interval_cases e
  · exact Or.inl (by simpa only [pow_zero] using he)
  · exact Or.inr (by simpa only [pow_one] using he)

theorem twist_not_mem_orbit (hp : p.Prime)
    (hR : Nat.card R = p ^ 3) (hZ : Nat.card (commutator R) = p)
    (α : MulAut R) (τ : Equiv.Perm X)
    (hτ : ∀ (r : R) (x : X), τ (r • x) = α r • τ x)
    (hline : ∀ F : Subgroup R, commutator R ≤ F → F.index = p →
      F.map α.toMonoidHom ≠ F)
    (x : X) (hx : ¬ commutator R ≤ stabilizer R x)
    (hU : Nat.card (stabilizer R x) = p) :
    τ x ∉ orbit R x := by
  let U := stabilizer R x
  let F := U ⊔ commutator R
  have hinf : U ⊓ commutator R = ⊥ :=
    inf_eq_bot_of_prime_center_not_le hp _ _ hZ hx
  have hFi : F.index = p := sup_index_eq_prime hp hR _ _ hZ hU hinf
  have hFN : F.Normal := normal_sup_of_derived_le _ U le_rfl
  have hCZ : (commutator R).map α.toMonoidHom = commutator R :=
    Subgroup.characteristic_iff_map_eq.mp inferInstance α
  rintro ⟨r, hr⟩
  change r • x = τ x at hr
  have hUmap : U.map α.toMonoidHom ≤ F := by
    rintro v ⟨u, hu, rfl⟩
    have hu' : u • x = x := hu
    have hv : r⁻¹ * α u * r ∈ U := by
      change (r⁻¹ * α u * r) • x = x
      calc
        (r⁻¹ * α u * r) • x = r⁻¹ • (α u • (r • x)) := by
          simp only [mul_smul]
        _ = r⁻¹ • (α u • τ x) := by rw [hr]
        _ = r⁻¹ • τ (u • x) := by rw [hτ]
        _ = r⁻¹ • τ x := by rw [hu']
        _ = x := by rw [← hr]; exact inv_smul_smul r x
    have hvF : r⁻¹ * α u * r ∈ F := (show U ≤ F from le_sup_left) hv
    have hc := hFN.conj_mem _ hvF r
    have he : r * (r⁻¹ * α u * r) * r⁻¹ = α u := by group
    exact he ▸ hc
  have hmap : F.map α.toMonoidHom ≤ F := by
    change (U ⊔ commutator R).map α.toMonoidHom ≤ U ⊔ commutator R
    rw [Subgroup.map_sup, hCZ]
    exact sup_le hUmap le_sup_right
  have heq : F.map α.toMonoidHom = F :=
    Subgroup.eq_of_le_of_card_ge hmap
      (by rw [Subgroup.card_map_of_injective α.injective])
  exact hline F le_sup_right hFi heq

theorem card_ge_two_prime_square (hp : p.Prime)
    (hR : Nat.card R = p ^ 3) (hZ : Nat.card (commutator R) = p)
    (α : MulAut R) (τ : Equiv.Perm X)
    (hτ : ∀ (r : R) (x : X), τ (r • x) = α r • τ x)
    (hline : ∀ F : Subgroup R, commutator R ≤ F → F.index = p →
      F.map α.toMonoidHom ≠ F)
    (x : X) (hx : ¬ commutator R ≤ stabilizer R x) :
    2 * p ^ 2 ≤ Nat.card X := by
  classical
  have hmul : Nat.card (orbit R x) * Nat.card (stabilizer R x) = p ^ 3 := by
    rw [← Nat.card_prod, Nat.card_congr (orbitProdStabilizerEquivGroup R x), hR]
  rcases stabilizer_card_one_or_prime hp hR hZ x hx with hU | hU
  · have hO : Nat.card (orbit R x) = p ^ 3 := by simpa only [hU, mul_one] using hmul
    have hle : Nat.card (orbit R x) ≤ Nat.card X :=
      Nat.card_le_card_of_injective (fun y : orbit R x => y.val) Subtype.val_injective
    have hp2 : 2 * p ^ 2 ≤ p ^ 3 := by
      calc
        2 * p ^ 2 ≤ p * p ^ 2 := Nat.mul_le_mul_right _ hp.two_le
        _ = p ^ 3 := by ring
    exact hp2.trans (hO ▸ hle)
  · have hO : Nat.card (orbit R x) = p ^ 2 := by
      apply Nat.eq_of_mul_eq_mul_right hp.pos
      simpa only [hU, pow_succ] using hmul
    have hnot := twist_not_mem_orbit hp hR hZ α τ hτ hline x hx hU
    have hcross (u v : orbit R x) : u.val ≠ τ v.val := by
      intro he
      obtain ⟨r, hr⟩ := v.property
      obtain ⟨s, hs⟩ := u.property
      change r • x = v.val at hr
      change s • x = u.val at hs
      apply hnot
      refine ⟨(α r)⁻¹ * s, ?_⟩
      change ((α r)⁻¹ * s) • x = τ x
      rw [mul_smul, hs, he, ← hr, hτ]
      exact inv_smul_smul (α r) (τ x)
    let f : (orbit R x ⊕ orbit R x) → X := Sum.elim Subtype.val (τ ∘ Subtype.val)
    have hf : Function.Injective f := by
      rintro (u | u) (v | v) he
      · exact congrArg Sum.inl (Subtype.ext he)
      · exact (hcross u v he).elim
      · exact (hcross v u he.symm).elim
      · exact congrArg Sum.inr (Subtype.ext (τ.injective he))
    have hcard := Nat.card_le_card_of_injective f hf
    rw [Nat.card_sum, hO] at hcard
    omega

end SymmetricSubgroupAsymptotics.PrimeCubeHalfTurnActionBound
