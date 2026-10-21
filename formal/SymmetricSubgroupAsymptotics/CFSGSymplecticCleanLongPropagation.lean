import SymmetricSubgroupAsymptotics.CFSGSymplecticFirstLowerLongRoot
import SymmetricSubgroupAsymptotics.CFSGSymplecticLongRootCommutation

/-! Exact propagation by the cleaned mixed word, before the pure Weyl
word has been recovered. Every membership remains in the original
subgroup or its injective inclusion in the same matrix-unit group. -/
set_option autoImplicit false
noncomputable section
namespace SymmetricSubgroupAsymptotics.CFSGSymplecticSerreMatrices
open CFSGMonomialUnitRootAction

theorem cleanMixed_upper_step (K : Type) [Field K] (r : ℕ) (hr : 0 < r)
    (H : Subgroup ((Mat K (r + 1))ˣ)) (hY : (cleanMixedWeyl K r).val ∈ H)
    (j : Fin (r + 1)) (hj : j.val < r)
    (hRoot : ∀ a : K, transvectionUnit (Sum.inl j : Index (r + 1)) (Sum.inr j)
      (by intro h; cases h) a ∈ H) :
    ∀ b : K, transvectionUnit
      (Sum.inl (⟨j.val + 1, Nat.succ_lt_succ hj⟩ : Fin (r + 1)) : Index (r + 1))
      (Sum.inr (⟨j.val + 1, Nat.succ_lt_succ hj⟩ : Fin (r + 1)))
      (by intro h; cases h) b ∈ H := by
  let k : Fin (r + 1) := ⟨j.val + 1, Nat.succ_lt_succ hj⟩
  have hp : coxeterCycle r (Sum.inl j) = Sum.inl k := coxeterCycle_inl_of_lt r j.val hj
  have hn : coxeterCycle r (Sum.inr j) = Sum.inr k := coxeterCycle_inr_of_lt r j.val hj
  have hk : k ≠ 0 := by
    intro h
    have hv := congrArg Fin.val h
    change j.val + 1 = 0 at hv
    omega
  have hh := CFSGTwistedMonomialRootTransport.full_root_transfer H
    (initialShortRoot K r 1).val (coxeterWeyl K r).val hY
    (coxeterCycle r).symm (coxeterSign K r ∘ (coxeterCycle r).symm)
    (coxeterWeyl_monomial K r)
    (fun i => coxeterSign_ne_zero K r ((coxeterCycle r).symm i))
    (show (Sum.inl j : Index (r + 1)) ≠ Sum.inr j by intro h; cases h) hRoot (by
      intro b
      simpa only [Equiv.symm_symm, hp, hn] using
        initialShort_commutes_upper_long K r hr k hk 1 b)
  simpa only [Equiv.symm_symm, hp, hn] using hh

theorem cleanMixed_upper_last_to_lower_zero (K : Type) [Field K] (r : ℕ) (hr : 0 < r)
    (H : Subgroup ((Mat K (r + 1))ˣ)) (hY : (cleanMixedWeyl K r).val ∈ H)
    (hRoot : ∀ a : K, transvectionUnit
      (Sum.inl (Fin.last r) : Index (r + 1)) (Sum.inr (Fin.last r))
      (by intro h; cases h) a ∈ H) :
    ∀ b : K, transvectionUnit (Sum.inr (0 : Fin (r + 1)) : Index (r + 1)) (Sum.inl 0)
      (by intro h; cases h) b ∈ H := by
  have hh := CFSGTwistedMonomialRootTransport.full_root_transfer H
    (initialShortRoot K r 1).val (coxeterWeyl K r).val hY
    (coxeterCycle r).symm (coxeterSign K r ∘ (coxeterCycle r).symm)
    (coxeterWeyl_monomial K r)
    (fun i => coxeterSign_ne_zero K r ((coxeterCycle r).symm i))
    (show (Sum.inl (Fin.last r) : Index (r + 1)) ≠ Sum.inr (Fin.last r) by intro h; cases h)
    hRoot (by
      intro b
      simpa only [Equiv.symm_symm, coxeterCycle_inl_last, coxeterCycle_inr_last] using
        initialShort_commutes_lower_zero K r hr 1 b)
  simpa only [Equiv.symm_symm, coxeterCycle_inl_last, coxeterCycle_inr_last] using hh

theorem firstLowerLongRoot_mem_of_cleanMixed (K : Type) [Field K] (r : ℕ) (hr : 0 < r)
    (H : Subgroup (elementaryRootGroup K (r + 1)))
    (hY : cleanMixedWeyl K r ∈ H) (hupper : ∀ a : K, firstLongRoot K r a ∈ H) :
    ∀ a : K, firstLowerLongRoot K r a ∈ H := by
  let H' := H.map (elementaryRootGroup K (r + 1)).subtype
  have hY' : (cleanMixedWeyl K r).val ∈ H' := ⟨_, hY, rfl⟩
  have h0 : ∀ a : K, transvectionUnit (Sum.inl (0 : Fin (r + 1)) : Index (r + 1))
      (Sum.inr 0) (by intro h; cases h) a ∈ H' := by
    intro a
    refine ⟨firstLongRoot K r a, hupper a, ?_⟩
    exact Units.ext (firstLongRoot_coe K r a)
  have aux : ∀ k : ℕ, ∀ hk : k ≤ r, ∀ a : K,
      transvectionUnit (Sum.inl (⟨k, by omega⟩ : Fin (r + 1)) : Index (r + 1))
        (Sum.inr (⟨k, by omega⟩ : Fin (r + 1))) (by intro h; cases h) a ∈ H' := by
    intro k
    induction k with
    | zero => intro hk; exact h0
    | succ k ih =>
      intro hk
      exact cleanMixed_upper_step K r hr H' hY' (⟨k, by omega⟩ : Fin (r + 1)) (by change k < r; omega)
        (ih (by omega))
  have hlast : ∀ a : K, transvectionUnit (Sum.inl (Fin.last r) : Index (r + 1))
      (Sum.inr (Fin.last r)) (by intro h; cases h) a ∈ H' := aux r le_rfl
  have hlow := cleanMixed_upper_last_to_lower_zero K r hr H' hY' hlast
  intro a
  have hm : (firstLowerLongRoot K r a).val ∈ H' := by
    have he : (firstLowerLongRoot K r a).val = transvectionUnit
        (Sum.inr (0 : Fin (r + 1)) : Index (r + 1)) (Sum.inl 0) (by intro h; cases h) a :=
      Units.ext (firstLowerLongRoot_coe K r a)
    rw [he]
    exact hlow a
  obtain ⟨u, hu, he⟩ := hm
  have he' : u = firstLowerLongRoot K r a := Subtype.ext he
  exact he' ▸ hu

end SymmetricSubgroupAsymptotics.CFSGSymplecticSerreMatrices
