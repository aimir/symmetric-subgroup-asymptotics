import SymmetricSubgroupAsymptotics.CFSGSymplecticLinearSimilitudes
import SymmetricSubgroupAsymptotics.CFSGSymplecticFullGroup
import SymmetricSubgroupAsymptotics.CFSGProjectiveLinearPointAction

/-! The actual alternating similitude group, with an explicit multiplier
splitting. The original form-preserving group is its literal unit-multiplier
fibre. -/
set_option autoImplicit false
noncomputable section
namespace SymmetricSubgroupAsymptotics.CFSGSymplecticSimilitudeGroup
open CFSGSymplecticSerreMatrices CFSGSymplecticTransvectionGeometry
variable {K : Type} [Field K]

abbrev LinearGroup (n : ℕ) := (Index n → K) ≃ₗ[K] (Index n → K)

def isometries (n : ℕ) : Subgroup (LinearGroup (K := K) n) where
  carrier := {e | ∀ v w, pairing n (e v) (e w) = pairing n v w}
  one_mem' := fun _ _ => rfl
  mul_mem' := by
    intro e f he hf v w
    exact (he (f v) (f w)).trans (hf v w)
  inv_mem' := by
    intro e he v w
    have h := he (e.symm v) (e.symm w)
    simpa only [LinearEquiv.apply_symm_apply] using h.symm

def similitudes (n : ℕ) : Subgroup (LinearGroup (K := K) n) where
  carrier := {e | ∃ c : K, c ≠ 0 ∧ ∀ v w, pairing n (e v) (e w) = c * pairing n v w}
  one_mem' := ⟨1, one_ne_zero, fun _ _ => (one_mul _).symm⟩
  mul_mem' := by
    rintro e f ⟨c, hc, he⟩ ⟨d, hd, hf⟩
    refine ⟨c * d, mul_ne_zero hc hd, fun v w => ?_⟩
    change pairing n (e (f v)) (e (f w)) = _
    rw [he, hf, mul_assoc]
  inv_mem' := by
    rintro e ⟨c, hc, he⟩
    refine ⟨c⁻¹, inv_ne_zero hc, fun v w => ?_⟩
    have h := he (e.symm v) (e.symm w)
    simp only [LinearEquiv.apply_symm_apply] at h
    change pairing n (e.symm v) (e.symm w) = _
    rw [h, ← mul_assoc, inv_mul_cancel₀ hc, one_mul]

def scale (n : ℕ) (c : Kˣ) : LinearGroup (K := K) n where
  toFun v := Sum.elim (fun i => (c : K) * v (Sum.inl i)) (fun i => v (Sum.inr i))
  invFun v := Sum.elim (fun i => ((c⁻¹ : Kˣ) : K) * v (Sum.inl i)) (fun i => v (Sum.inr i))
  left_inv v := by funext i; cases i <;> simp [← mul_assoc]
  right_inv v := by funext i; cases i <;> simp [← mul_assoc]
  map_add' v w := by funext i; cases i <;> simp [mul_add]
  map_smul' a v := by funext i; cases i <;> simp [mul_left_comm]

theorem scale_pos (n : ℕ) (c : Kˣ) (v : Index n → K) (i : Fin n) :
    scale n c v (Sum.inl i) = (c : K) * v (Sum.inl i) := rfl

theorem scale_neg (n : ℕ) (c : Kˣ) (v : Index n → K) (i : Fin n) :
    scale n c v (Sum.inr i) = v (Sum.inr i) := rfl

theorem scale_pairing (n : ℕ) (c : Kˣ) (v w : Index n → K) :
    pairing n (scale n c v) (scale n c w) = (c : K) * pairing n v w := by
  simp only [pairing, scale_pos, scale_neg, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i _
  ring

def scaleInGroup (n : ℕ) (c : Kˣ) : similitudes (K := K) n :=
  ⟨scale n c, c, c.ne_zero, scale_pairing n c⟩

theorem multiplier_unique (n : ℕ) (hn : 0 < n) (e : LinearGroup (K := K) n)
    (c d : K) (hc : ∀ v w, pairing n (e v) (e w) = c * pairing n v w)
    (hd : ∀ v w, pairing n (e v) (e w) = d * pairing n v w) : c = d := by
  let i : Fin n := ⟨0, hn⟩
  have h := (hc (Pi.single (Sum.inl i) 1) (Pi.single (Sum.inr i) 1)).symm.trans
    (hd (Pi.single (Sum.inl i) 1) (Pi.single (Sum.inr i) 1))
  simpa only [pairing_neg_basis, Pi.single_eq_same, mul_one] using h

def multiplier (n : ℕ) (e : similitudes (K := K) n) : Kˣ :=
  Units.mk0 (Classical.choose e.property) (Classical.choose_spec e.property).1

theorem multiplier_spec (n : ℕ) (e : similitudes (K := K) n) (v w : Index n → K) :
    pairing n (e.val v) (e.val w) = (multiplier n e : K) * pairing n v w :=
  (Classical.choose_spec e.property).2 v w

theorem multiplier_eq (n : ℕ) (hn : 0 < n) (e : similitudes (K := K) n) (c : Kˣ)
    (he : ∀ v w, pairing n (e.val v) (e.val w) = (c : K) * pairing n v w) :
    multiplier n e = c := by
  apply Units.ext
  exact multiplier_unique n hn e.val _ _ (multiplier_spec n e) he

def normalized (n : ℕ) (e : similitudes (K := K) n) : isometries (K := K) n :=
  ⟨scale n (multiplier n e)⁻¹ * e.val, by
    intro v w
    change pairing n (scale n (multiplier n e)⁻¹ (e.val v))
      (scale n (multiplier n e)⁻¹ (e.val w)) = _
    rw [scale_pairing, multiplier_spec, ← mul_assoc, Units.val_inv_eq_inv_val,
      inv_mul_cancel₀ (multiplier n e).ne_zero, one_mul]⟩

theorem scale_mul_inv (n : ℕ) (c : Kˣ) : scale n c * scale n c⁻¹ = 1 := by
  apply LinearEquiv.ext
  intro v
  funext i
  cases i <;> simp [scale, LinearEquiv.mul_apply, ← mul_assoc]

def decomposeEquiv (n : ℕ) (hn : 0 < n) :
    similitudes (K := K) n ≃ Kˣ × isometries (K := K) n where
  toFun e := (multiplier n e, normalized n e)
  invFun p := ⟨scale n p.1 * p.2.val,
    ⟨p.1, p.1.ne_zero, fun v w => by
      change pairing n (scale n p.1 (p.2.val v)) (scale n p.1 (p.2.val w)) = _
      rw [scale_pairing, p.2.property]⟩⟩
  left_inv e := by
    apply Subtype.ext
    change scale n (multiplier n e) * (scale n (multiplier n e)⁻¹ * e.val) = e.val
    rw [← mul_assoc, scale_mul_inv, one_mul]
  right_inv p := by
    have hm : multiplier n ⟨scale n p.1 * p.2.val, by
        refine ⟨p.1, p.1.ne_zero, fun v w => ?_⟩
        change pairing n (scale n p.1 (p.2.val v)) (scale n p.1 (p.2.val w)) = _
        rw [scale_pairing, p.2.property]⟩ = p.1 := by
      apply multiplier_eq n hn
      intro v w
      change pairing n (scale n p.1 (p.2.val v)) (scale n p.1 (p.2.val w)) = _
      rw [scale_pairing, p.2.property]
    apply Prod.ext hm
    apply Subtype.ext
    change scale n _ * (scale n p.1 * p.2.val) = p.2.val
    rw [hm, ← mul_assoc]
    have hscale := scale_mul_inv n p.1⁻¹
    simp only [inv_inv] at hscale
    rw [hscale, one_mul]

end SymmetricSubgroupAsymptotics.CFSGSymplecticSimilitudeGroup
