import SymmetricSubgroupAsymptotics.AdditiveNonzeroOrbitIndex
import SymmetricSubgroupAsymptotics.CFSGSymplecticNaturalVectorOrbit

/-! The literal elementary symplectic matrices act transitively on
nonzero natural vectors. Their actual action bounds the index of any
subgroup preserving a nonzero additive subgroup; no full-field
linearity or larger symplectic-group recognition is an input. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
open scoped Matrix

namespace SymmetricSubgroupAsymptotics.CFSGSymplecticAdditiveOrbitIndex

open CFSGSymplecticSerreMatrices
variable (K : Type) [Field K]

@[reducible] def naturalAction (n : ℕ) : MulAction (elementaryRootGroup K n) (Index n → K) where
  smul g v := (g.val : Mat K n) *ᵥ v
  one_smul v := Matrix.one_mulVec v
  mul_smul g h v :=
    (Matrix.mulVec_mulVec v (g.val : Mat K n) (h.val : Mat K n)).symm

local instance naturalActionInstance (n : ℕ) :
    MulAction (elementaryRootGroup K n) (Index n → K) := naturalAction K n

theorem exists_map_nonzero (r : ℕ) (hr : 0 < r)
    (v w : Index (r + 1) → K) (hv : v ≠ 0) (hw : w ≠ 0) :
    ∃ g : elementaryRootGroup K (r + 1), (g.val : Mat K (r + 1)) *ᵥ v = w := by
  obtain ⟨a, ha⟩ := exists_elementary_mulVec_first_basis K r hr v hv
  obtain ⟨b, hb⟩ := exists_elementary_mulVec_first_basis K r hr w hw
  let e : Index (r + 1) → K := Pi.single (Sum.inl 0) 1
  have ha' : a • e = v := ha
  have hb' : b • e = w := hb
  refine ⟨b * a⁻¹, ?_⟩
  change (b * a⁻¹) • v = w
  calc
    _ = (b * a⁻¹) • (a • e) := congrArg (fun z => (b * a⁻¹) • z) ha'.symm
    _ = b • e := by
      have heq : (b * a⁻¹) * a = b := by rw [mul_assoc, inv_mul_cancel, mul_one]
      exact (Matrix.mulVec_mulVec e ((b * a⁻¹).val : Mat K (r + 1))
        (a.val : Mat K (r + 1))).trans
          (congrArg (fun g : elementaryRootGroup K (r + 1) =>
            (g.val : Mat K (r + 1)) *ᵥ e) heq)
    _ = w := hb'

/-- Both W and the subgroup whose index occurs here are actual
subgroups of the literal matrix action. -/
theorem card_le_additive_subgroup_card_mul_index [Finite K]
    (r : ℕ) (hr : 0 < r) (L : Subgroup (elementaryRootGroup K (r + 1)))
    (W : AddSubgroup (Index (r + 1) → K))
    (hW : ∀ g ∈ L, ∀ w ∈ W, (g.val : Mat K (r + 1)) *ᵥ w ∈ W)
    (v : Index (r + 1) → K) (hvW : v ∈ W) (hv : v ≠ 0) :
    Nat.card K ^ (2 * (r + 1)) ≤ Nat.card W * L.index := by
  have hz (g : elementaryRootGroup K (r + 1)) : g • (0 : Index (r + 1) → K) = 0 :=
    Matrix.mulVec_zero _
  have ht (x y : Index (r + 1) → K) (hx : x ≠ 0) (hy : y ≠ 0) :
      ∃ g : elementaryRootGroup K (r + 1), g • x = y :=
    exists_map_nonzero K r hr x y hx hy
  have h := AdditiveNonzeroOrbitIndex.card_le_subgroup_card_mul_index
    hz ht L W hW v hvW hv
  simpa only [Nat.card_fun, Nat.card_sum, Nat.card_fin, ← two_mul] using h

end SymmetricSubgroupAsymptotics.CFSGSymplecticAdditiveOrbitIndex
