import SymmetricSubgroupAsymptotics.CFSGSymplecticInitialTori

/-! The first two positive long-root groups are actual conjugates of
the original terminal negative root. These are genuine elements of the
same elementary group, with exact natural matrix coordinates. -/
set_option autoImplicit false
noncomputable section
namespace SymmetricSubgroupAsymptotics.CFSGSymplecticSerreMatrices

theorem coxeter_transvection_conjugation (K : Type) [Field K] (r : ℕ)
    (u : elementaryRootGroup K (r + 1)) (i j : Index (r + 1)) (hij : i ≠ j) (a : K)
    (hu : (u.val : Mat K (r + 1)) = Matrix.transvection i j a) :
    ((coxeterWeyl K r * u * (coxeterWeyl K r)⁻¹).val : Mat K (r + 1)) =
      Matrix.transvection (coxeterCycle r i) (coxeterCycle r j)
        (coxeterSign K r i * a / coxeterSign K r j) := by
  have he : u.val = CFSGMonomialUnitRootAction.transvectionUnit i j hij a :=
    Units.ext hu
  have h := CFSGMonomialUnitRootAction.monomial_conjugation (coxeterWeyl K r).val
    (coxeterCycle r).symm (coxeterSign K r ∘ (coxeterCycle r).symm)
    (coxeterWeyl_monomial K r) hij a
    (by simpa only [Function.comp_apply, Equiv.symm_symm, Equiv.symm_apply_apply]
      using coxeterSign_ne_zero K r j)
  rw [← he] at h
  have hv := congrArg Units.val h
  simpa only [Units.val_mul,
    CFSGMonomialUnitRootAction.transvectionUnit_val, Equiv.symm_symm,
    Function.comp_apply, Equiv.symm_apply_apply] using hv

def firstLongRoot (K : Type) [Field K] (r : ℕ) (a : K) : elementaryRootGroup K (r + 1) :=
  coxeterWeyl K r * elementaryRoot K (r + 1) true (Fin.last r) (-a) *
    (coxeterWeyl K r)⁻¹

def secondLongRoot (K : Type) [Field K] (r : ℕ) (a : K) : elementaryRootGroup K (r + 1) :=
  coxeterWeyl K r * firstLongRoot K r a * (coxeterWeyl K r)⁻¹

theorem firstLongRoot_coe (K : Type) [Field K] (r : ℕ) (a : K) :
    ((firstLongRoot K r a).val : Mat K (r + 1)) =
      Matrix.transvection (Sum.inl (0 : Fin (r + 1))) (Sum.inr 0) a := by
  have h := coxeter_transvection_conjugation K r
    (elementaryRoot K (r + 1) true (Fin.last r) (-a))
    (Sum.inr (Fin.last r)) (Sum.inl (Fin.last r)) (by intro h; cases h) (-a)
    (terminal_negative_coe K r (-a))
  change ((firstLongRoot K r a).val : Mat K (r + 1)) = _ at h
  rw [coxeterCycle_inl_last, coxeterCycle_inr_last] at h
  simp only [coxeterSign, if_true] at h
  have hc : (-1 : K) ^ (r + 1) * (-a) / (-1 : K) ^ r = a := by
    rw [pow_succ]
    field_simp
  simpa only [hc] using h

theorem secondLongRoot_coe (K : Type) [Field K] (r : ℕ) (hr : 0 < r) (a : K) :
    ((secondLongRoot K r a).val : Mat K (r + 1)) =
      Matrix.transvection (Sum.inl (⟨1, by omega⟩ : Fin (r + 1)))
        (Sum.inr (⟨1, by omega⟩ : Fin (r + 1))) a := by
  have h := coxeter_transvection_conjugation K r (firstLongRoot K r a)
    (Sum.inl (0 : Fin (r + 1))) (Sum.inr 0) (by intro h; cases h) a
    (firstLongRoot_coe K r a)
  change ((secondLongRoot K r a).val : Mat K (r + 1)) = _ at h
  have hn : (0 : Fin (r + 1)) ≠ Fin.last r := by
    intro he
    have hv := congrArg Fin.val he
    change 0 = r at hv
    omega
  have hp0 : coxeterCycle r (Sum.inl (0 : Fin (r + 1))) =
      Sum.inl (⟨1, Nat.succ_lt_succ hr⟩ : Fin (r + 1)) := coxeterCycle_inl_of_lt r 0 hr
  have hn0 : coxeterCycle r (Sum.inr (0 : Fin (r + 1))) =
      Sum.inr (⟨1, Nat.succ_lt_succ hr⟩ : Fin (r + 1)) := coxeterCycle_inr_of_lt r 0 hr
  simpa only [hp0, hn0, coxeterSign, hn, if_false, one_mul, div_one] using h

end SymmetricSubgroupAsymptotics.CFSGSymplecticSerreMatrices
