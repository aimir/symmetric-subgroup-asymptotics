import SymmetricSubgroupAsymptotics.CFSGOrthogonalDNegativeDilation
import SymmetricSubgroupAsymptotics.CFSGDiagonalMatrixUnits
import SymmetricSubgroupAsymptotics.CFSGOrthogonalDIndexPositiveGraph

/-! The actual MATRIX similitude group of the original split quadratic
form. Every nonzero multiplier is realized by literal negative-coordinate
dilation. An explicit bijection with Kˣ times the original isometry
group gives its cardinality, without any group-order formula. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
open scoped Matrix
namespace SymmetricSubgroupAsymptotics.CFSGOrthogonalDSimilitudeGroup
open Matrix CFSGOrthogonalDSerreMatrices CFSGOrthogonalDIndexQuadraticForm
open CFSGOrthogonalDIndexBundledQuadratic CFSGOrthogonalDIndexPositiveGraph
variable (K : Type) [Field K]

def similitudes (r : ℕ) : Subgroup (Mat K r)ˣ where
  carrier := {g | ∃ c : Kˣ, ∀ x, splitQ K ((g : Mat K r) *ᵥ x) = (c : K) * splitQ K x}
  one_mem' := ⟨1, fun x => by simp⟩
  mul_mem' := by
    rintro g h ⟨c, hc⟩ ⟨d, hd⟩
    refine ⟨c * d, fun x => ?_⟩
    change splitQ K (((g : Mat K r) * (h : Mat K r)) *ᵥ x) = _
    rw [← Matrix.mulVec_mulVec, hc, hd, Units.val_mul, mul_assoc]
  inv_mem' := by
    rintro g ⟨c, hc⟩
    refine ⟨c⁻¹, fun x => ?_⟩
    have h := hc (((g⁻¹ : (Mat K r)ˣ) : Mat K r) *ᵥ x)
    rw [Matrix.mulVec_mulVec, Units.mul_inv, Matrix.one_mulVec] at h
    rw [h, Units.val_inv_eq_inv_val, ← mul_assoc, inv_mul_cancel₀ c.ne_zero, one_mul]

def negativeWeightsHom (r : ℕ) : Kˣ →* (Index r → Kˣ) where
  toFun c := Sum.elim (fun _ => 1) (fun _ => c)
  map_one' := by funext i; cases i <;> rfl
  map_mul' c d := by funext i; cases i <;> simp

def negativeScaleHom (r : ℕ) : Kˣ →* (Mat K r)ˣ :=
  (CFSGDiagonalMatrixUnits.diagonalHom (Index r) K).comp (negativeWeightsHom K r)

theorem negativeScale_action (r : ℕ) (c : Kˣ) (v : Index r → K) :
    (negativeScaleHom K r c : Mat K r) *ᵥ v = CFSGOrthogonalDNegativeDilation.map K r (c : K) v := by
  change Matrix.diagonal (fun i => (negativeWeightsHom K r c i : K)) *ᵥ v = _
  funext i
  rw [Matrix.mulVec_diagonal]
  cases i <;> simp [negativeWeightsHom, CFSGOrthogonalDNegativeDilation.map]

theorem negativeScale_quadratic (r : ℕ) (c : Kˣ) (v : Index r → K) :
    splitQ K ((negativeScaleHom K r c : Mat K r) *ᵥ v) = (c : K) * splitQ K v := by
  rw [negativeScale_action]
  have h := CFSGOrthogonalDNegativeDilation.map_quadratic K r (c : K) v
  simpa only [splitQuadraticForm_apply] using h

def multiplier (r : ℕ) (g : similitudes K r) : Kˣ := Classical.choose g.property

theorem multiplier_spec (r : ℕ) (g : similitudes K r) (v : Index r → K) :
    splitQ K ((g.val : Mat K r) *ᵥ v) = (multiplier K r g : K) * splitQ K v :=
  Classical.choose_spec g.property v

theorem multiplier_unique (r : ℕ) (hr : 0 < r) (g : (Mat K r)ˣ) (c d : Kˣ)
    (hc : ∀ v, splitQ K ((g : Mat K r) *ᵥ v) = (c : K) * splitQ K v)
    (hd : ∀ v, splitQ K ((g : Mat K r) *ᵥ v) = (d : K) * splitQ K v) : c = d := by
  let i : Fin r := ⟨0, hr⟩
  let v : Index r → K := Sum.elim (Pi.single i 1) (Pi.single i 1)
  have hv : splitQ K v = 1 := by
    simp [splitQ, v, leftPart, rightPart]
  apply Units.ext
  have h := (hc v).symm.trans (hd v)
  simpa only [hv, mul_one] using h

theorem multiplier_eq (r : ℕ) (hr : 0 < r) (g : similitudes K r) (c : Kˣ)
    (hc : ∀ v, splitQ K ((g.val : Mat K r) *ᵥ v) = (c : K) * splitQ K v) :
    multiplier K r g = c :=
  multiplier_unique K r hr g.val _ _ (multiplier_spec K r g) hc

def normalized (r : ℕ) (g : similitudes K r) : quadraticPreserving K r :=
  ⟨negativeScaleHom K r (multiplier K r g)⁻¹ * g.val, by
    intro v
    change splitQ K (((negativeScaleHom K r (multiplier K r g)⁻¹ : Mat K r) *
      (g.val : Mat K r)) *ᵥ v) = _
    rw [← Matrix.mulVec_mulVec, negativeScale_quadratic, multiplier_spec,
      Units.val_inv_eq_inv_val, ← mul_assoc, inv_mul_cancel₀ (multiplier K r g).ne_zero, one_mul]⟩

def assemble (r : ℕ) (c : Kˣ) (g : quadraticPreserving K r) : similitudes K r :=
  ⟨negativeScaleHom K r c * g.val, c, by
    intro v
    change splitQ K (((negativeScaleHom K r c : Mat K r) * (g.val : Mat K r)) *ᵥ v) = _
    rw [← Matrix.mulVec_mulVec, negativeScale_quadratic, g.property]⟩

theorem multiplier_assemble (r : ℕ) (hr : 0 < r) (c : Kˣ) (g : quadraticPreserving K r) :
    multiplier K r (assemble K r c g) = c := by
  apply multiplier_eq K r hr
  intro v
  change splitQ K (((negativeScaleHom K r c : Mat K r) * (g.val : Mat K r)) *ᵥ v) = _
  rw [← Matrix.mulVec_mulVec, negativeScale_quadratic, g.property]

def decomposeEquiv (r : ℕ) (hr : 0 < r) :
    similitudes K r ≃ Kˣ × quadraticPreserving K r where
  toFun g := (multiplier K r g, normalized K r g)
  invFun p := assemble K r p.1 p.2
  left_inv g := by
    apply Subtype.ext
    change negativeScaleHom K r (multiplier K r g) *
      (negativeScaleHom K r (multiplier K r g)⁻¹ * g.val) = g.val
    rw [← mul_assoc, ← map_mul, mul_inv_cancel, map_one, one_mul]
  right_inv p := by
    have hm := multiplier_assemble K r hr p.1 p.2
    apply Prod.ext hm
    apply Subtype.ext
    change negativeScaleHom K r (multiplier K r (assemble K r p.1 p.2))⁻¹ *
      (negativeScaleHom K r p.1 * p.2.val) = p.2.val
    rw [hm, ← mul_assoc, ← map_mul, inv_mul_cancel, map_one, one_mul]

theorem similitudes_card [Finite K] (r : ℕ) (hr : 0 < r) :
    Nat.card (similitudes K r) = Nat.card Kˣ * Nat.card (quadraticPreserving K r) :=
  (Nat.card_congr (decomposeEquiv K r hr)).trans (Nat.card_prod _ _)

end SymmetricSubgroupAsymptotics.CFSGOrthogonalDSimilitudeGroup
