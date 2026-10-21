import SymmetricSubgroupAsymptotics.CFSGSymplecticSignedChainRoots

/-! The two genuine signed Coxeter steps across the terminal pair
carry the last positive-side short line to the first negative-side
short line. Both signs cancel; no characteristic-two simplification
is used. -/
set_option autoImplicit false
noncomputable section
namespace SymmetricSubgroupAsymptotics.CFSGSymplecticSerreMatrices

theorem coxeter_single_twice (K : Type) [Field K] (r : ℕ) (i j : Index (r + 1)) :
    ((coxeterWeyl K r).val : Mat K (r + 1)) *
      (((coxeterWeyl K r).val : Mat K (r + 1)) * Matrix.single i j 1 *
        (↑((coxeterWeyl K r).val⁻¹) : Mat K (r + 1))) *
      (↑((coxeterWeyl K r).val⁻¹) : Mat K (r + 1)) =
      ((coxeterSign K r i / coxeterSign K r j) *
        (coxeterSign K r (coxeterCycle r i) / coxeterSign K r (coxeterCycle r j))) •
        Matrix.single (coxeterCycle r (coxeterCycle r i)) (coxeterCycle r (coxeterCycle r j)) 1 := by
  rw [coxeter_single_conjugation, Matrix.mul_smul, Matrix.smul_mul,
    coxeter_single_conjugation, smul_smul]

theorem coxeter_chain_crossing (K : Type) [Field K] (s : ℕ) :
    ((coxeterWeyl K (s + 1)).val : Mat K (s + 2)) *
      (((coxeterWeyl K (s + 1)).val : Mat K (s + 2)) *
        signedChainRoot K (s + 1) false (Fin.last s) *
        (↑((coxeterWeyl K (s + 1)).val⁻¹) : Mat K (s + 2))) *
      (↑((coxeterWeyl K (s + 1)).val⁻¹) : Mat K (s + 2)) =
      signedChainRoot K (s + 1) true (0 : Fin (s + 1)) := by
  let p : Fin (s + 2) := (Fin.last s).castSucc
  have hprev : p.val < s + 1 := by change s < s + 1; omega
  have hp : coxeterCycle (s + 1) (Sum.inl p) = Sum.inl (Fin.last (s + 1)) :=
    coxeterCycle_inl_of_lt (s + 1) p.val hprev
  have hn : coxeterCycle (s + 1) (Sum.inr p) = Sum.inr (Fin.last (s + 1)) :=
    coxeterCycle_inr_of_lt (s + 1) p.val hprev
  have hp0 : coxeterCycle (s + 1) (Sum.inl (0 : Fin (s + 2))) =
      Sum.inl (⟨1, by omega⟩ : Fin (s + 2)) := coxeterCycle_inl_of_lt (s + 1) 0 (by omega)
  have hn0 : coxeterCycle (s + 1) (Sum.inr (0 : Fin (s + 2))) =
      Sum.inr (⟨1, by omega⟩ : Fin (s + 2)) := coxeterCycle_inr_of_lt (s + 1) 0 (by omega)
  have hpn : p ≠ Fin.last (s + 1) := by
    intro h
    have hv := congrArg Fin.val h
    change s = s + 1 at hv
    omega
  have hzn : (0 : Fin (s + 2)) ≠ Fin.last (s + 1) := by
    intro h
    have hv := congrArg Fin.val h
    change 0 = s + 1 at hv
    omega
  have hsucc : (Fin.last s).succ = Fin.last (s + 1) := Fin.ext rfl
  simp only [signedChainRoot, coordinatePoint, Bool.not_false, Bool.not_true, Bool.false_eq_true,
    if_false, if_true, hsucc, mul_sub, sub_mul, coxeter_single_twice,
    show (Fin.last s).castSucc = p from rfl, hp, hn,
    coxeterCycle_inl_last, coxeterCycle_inr_last, hp0, hn0, coxeterSign,
    hpn, hzn, if_false, if_true, div_one, one_div, one_mul,
    mul_inv_cancel₀ (pow_ne_zero _ (neg_ne_zero.mpr (one_ne_zero : (1 : K) ≠ 0))),
    inv_mul_cancel₀ (pow_ne_zero _ (neg_ne_zero.mpr (one_ne_zero : (1 : K) ≠ 0))), one_smul]
  rfl

end SymmetricSubgroupAsymptotics.CFSGSymplecticSerreMatrices
