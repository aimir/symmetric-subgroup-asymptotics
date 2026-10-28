import SymmetricSubgroupAsymptotics.PrimeCubeHalfTurnActionBound

/-! Arbitrarily many distinct normalizer translates of a literal group
orbit. This extends the two-orbit bound without assuming transitivity
on a projective-line set or enumerating any group elements. -/
set_option autoImplicit false
noncomputable section
namespace SymmetricSubgroupAsymptotics.PrimeCubeCompatibleOrbitPacking
open MulAction
variable {R X : Type*} [Group R] [Finite R] [Finite X] [MulAction R X]

theorem compatible_powers (α : MulAut R) (τ : Equiv.Perm X)
    (hτ : ∀ r : R, ∀ x : X, τ (r • x) = α r • τ x)
    (k : ℕ) (r : R) (x : X) : (τ ^ k) (r • x) = (α ^ k) r • (τ ^ k) x := by
  induction k with
  | zero => rfl
  | succ k ih =>
    rw [pow_succ', Equiv.Perm.mul_apply, ih, hτ, pow_succ', MulAut.mul_apply]
    rfl

theorem card_mul_orbit_le (α : MulAut R) (τ : Equiv.Perm X)
    (hτ : ∀ r : R, ∀ x : X, τ (r • x) = α r • τ x) (x : X) (m : ℕ)
    (hreturn : ∀ k : ℕ, 0 < k → k < m → (τ ^ k) x ∉ orbit R x) :
    m * Nat.card (orbit R x) ≤ Nat.card X := by
  classical
  let f : Fin m × orbit R x → X := fun z => (τ ^ z.1.val) z.2.val
  have hcross (i j : Fin m) (hij : i.val < j.val) (u v : orbit R x) :
      (τ ^ i.val) u.val ≠ (τ ^ j.val) v.val := by
    intro he
    let d := j.val - i.val
    have hd0 : 0 < d := Nat.sub_pos_of_lt hij
    have hdm : d < m := (Nat.sub_le _ _).trans_lt j.isLt
    have hdiff : u.val = (τ ^ d) v.val := by
      apply (τ ^ i.val).injective
      calc
        (τ ^ i.val) u.val = (τ ^ j.val) v.val := he
        _ = (τ ^ i.val) ((τ ^ d) v.val) := by
          rw [← Equiv.Perm.mul_apply, ← pow_add]
          rw [Nat.add_sub_of_le hij.le]
    obtain ⟨r, hr⟩ := u.property
    obtain ⟨s, hs⟩ := v.property
    change r • x = u.val at hr
    change s • x = v.val at hs
    apply hreturn d hd0 hdm
    refine ⟨((α ^ d) s)⁻¹ * r, ?_⟩
    change (((α ^ d) s)⁻¹ * r) • x = (τ ^ d) x
    rw [mul_smul, hr, hdiff, ← hs, compatible_powers α τ hτ]
    exact inv_smul_smul ((α ^ d) s) ((τ ^ d) x)
  have hf : Function.Injective f := by
    rintro ⟨i, u⟩ ⟨j, v⟩ he
    have hij : i = j := by
      apply Fin.ext
      rcases lt_trichotomy i.val j.val with h | h | h
      · exact (hcross i j h u v he).elim
      · exact h
      · exact (hcross j i h v u he.symm).elim
    subst j
    exact Prod.ext rfl (Subtype.ext ((τ ^ i.val).injective he))
  have hh := Nat.card_le_card_of_injective f hf
  simpa only [Nat.card_prod, Nat.card_fin] using hh

theorem card_ge_mul_prime_square {p : ℕ} (hp : p.Prime)
    (hR : Nat.card R = p ^ 3) (hZ : Nat.card (commutator R) = p)
    (α : MulAut R) (τ : Equiv.Perm X)
    (hτ : ∀ r : R, ∀ x : X, τ (r • x) = α r • τ x)
    (m : ℕ) (hmp : m ≤ p)
    (hline : ∀ k : ℕ, 0 < k → k < m → ∀ F : Subgroup R,
      commutator R ≤ F → F.index = p → F.map (α ^ k).toMonoidHom ≠ F)
    (x : X) (hx : ¬ commutator R ≤ stabilizer R x) :
    m * p ^ 2 ≤ Nat.card X := by
  have hsmall := PrimeCubeCentralSubgroupBounds.card_le_prime_of_not_contains_derived
    hp hR (commutator R) (stabilizer R x) rfl hx
  obtain ⟨e, _, he⟩ := (Nat.dvd_prime_pow hp).mp
    (hR ▸ (stabilizer R x).card_subgroup_dvd_card)
  have hle : e ≤ 1 := (Nat.pow_le_pow_iff_right hp.one_lt).mp
    (by simpa only [he, pow_one] using hsmall)
  have hmul : Nat.card (orbit R x) * Nat.card (stabilizer R x) = p ^ 3 := by
    rw [← Nat.card_prod, Nat.card_congr (orbitProdStabilizerEquivGroup R x), hR]
  interval_cases e
  · have ho : Nat.card (orbit R x) = p ^ 3 := by simpa only [he, pow_zero, mul_one] using hmul
    have hsub : Nat.card (orbit R x) ≤ Nat.card X :=
      Nat.card_le_card_of_injective (fun y : orbit R x => y.val) Subtype.val_injective
    calc
      m * p ^ 2 ≤ p * p ^ 2 := Nat.mul_le_mul_right _ hmp
      _ = p ^ 3 := by ring
      _ ≤ Nat.card X := ho ▸ hsub
  · have hu : Nat.card (stabilizer R x) = p := by simpa only [pow_one] using he
    have ho : Nat.card (orbit R x) = p ^ 2 := by
      apply Nat.eq_of_mul_eq_mul_right hp.pos
      simpa only [hu, pow_succ] using hmul
    have hh := card_mul_orbit_le α τ hτ x m (fun k hk hkm =>
      PrimeCubeHalfTurnActionBound.twist_not_mem_orbit hp hR hZ
        (α ^ k) (τ ^ k) (compatible_powers α τ hτ k) (hline k hk hkm) x hx hu)
    simpa only [ho] using hh

end SymmetricSubgroupAsymptotics.PrimeCubeCompatibleOrbitPacking
