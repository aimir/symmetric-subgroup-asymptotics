import SymmetricSubgroupAsymptotics.CFSGSymplecticAllNaturalTransvections

/-! Nontrivial natural transvections determine their original
projective vector line. Full parameter root subgroups have exactly
these labels, in every characteristic. -/
set_option autoImplicit false
noncomputable section
namespace SymmetricSubgroupAsymptotics.CFSGSymplecticTransvectionGeometry
open CFSGSymplecticSerreMatrices
variable {K : Type} [Field K]

theorem transvection_smul (r : ℕ) (v : Index r → K) (c a : K) :
    transvection r (c • v) a = transvection r v (a * c ^ 2) := by
  apply LinearEquiv.ext
  intro x
  funext i
  simp only [transvection_apply, pairing_smul_left, Pi.add_apply, Pi.smul_apply, smul_eq_mul]
  ring

theorem transvection_eq_imp_smul (r : ℕ) (v w : Index r → K) (a b : K)
    (hv : v ≠ 0) (ha : a ≠ 0) (he : transvection r v a = transvection r w b) :
    ∃ c : K, c ≠ 0 ∧ v = c • w := by
  obtain ⟨x, hx⟩ := exists_pairing_ne_zero r v hv
  let α : K := a * pairing r v x
  let β : K := b * pairing r w x
  have hα : α ≠ 0 := mul_ne_zero ha hx
  have hsmul : α • v = β • w := by
    have h := congrArg (fun T : (Index r → K) ≃ₗ[K] (Index r → K) => T x) he
    exact add_left_cancel h
  have hβ : β ≠ 0 := by
    intro hz
    have hn : α • v ≠ 0 := smul_ne_zero hα hv
    apply hn
    rw [hsmul, hz, zero_smul]
  refine ⟨α⁻¹ * β, mul_ne_zero (inv_ne_zero hα) hβ, ?_⟩
  calc
    v = α⁻¹ • (α • v) := by rw [smul_smul, inv_mul_cancel₀ hα, one_smul]
    _ = (α⁻¹ * β) • w := by rw [hsmul, smul_smul]

theorem transvection_eq_iff (r : ℕ) (v w : Index r → K) (a b : K)
    (hv : v ≠ 0) (hw : w ≠ 0) (ha : a ≠ 0) :
    transvection r v a = transvection r w b ↔
      ∃ c : K, c ≠ 0 ∧ v = c • w ∧ b = a * c ^ 2 := by
  constructor
  · intro he
    obtain ⟨c, hc, hvc⟩ := transvection_eq_imp_smul r v w a b hv ha he
    refine ⟨c, hc, hvc, ?_⟩
    rw [hvc, transvection_smul] at he
    exact ((transvection_parameter_injective r w hw) he).symm
  · rintro ⟨c, _, hvc, hb⟩
    rw [hvc, transvection_smul, ← hb]

def naturalRootHom (r : ℕ) (v : Index r → K) :
    Multiplicative K →* ((Index r → K) ≃ₗ[K] (Index r → K)) where
  toFun a := transvection r v a.toAdd
  map_one' := transvection_zero r v
  map_mul' a b := transvection_add r v a.toAdd b.toAdd

def naturalRootLine (r : ℕ) (v : Index r → K) :
    Subgroup ((Index r → K) ≃ₗ[K] (Index r → K)) := (naturalRootHom r v).range

theorem naturalRootLine_smul (r : ℕ) (v : Index r → K) (c : K) (hc : c ≠ 0) :
    naturalRootLine r (c • v) = naturalRootLine r v := by
  ext T
  constructor
  · rintro ⟨a, rfl⟩
    refine ⟨Multiplicative.ofAdd (a.toAdd * c ^ 2), ?_⟩
    exact (transvection_smul r v c a.toAdd).symm
  · rintro ⟨a, rfl⟩
    refine ⟨Multiplicative.ofAdd (a.toAdd / c ^ 2), ?_⟩
    change transvection r (c • v) (a.toAdd / c ^ 2) = transvection r v a.toAdd
    rw [transvection_smul, div_mul_cancel₀ _ (pow_ne_zero 2 hc)]

theorem naturalRootLine_eq_iff (r : ℕ) (v w : Index r → K) (hv : v ≠ 0) :
    naturalRootLine r v = naturalRootLine r w ↔ ∃ c : K, c ≠ 0 ∧ v = c • w := by
  constructor
  · intro he
    have hm : transvection r v 1 ∈ naturalRootLine r v := ⟨Multiplicative.ofAdd 1, rfl⟩
    rw [he] at hm
    obtain ⟨a, ha⟩ := hm
    exact transvection_eq_imp_smul r v w 1 a.toAdd hv one_ne_zero ha.symm
  · rintro ⟨c, hc, hvc⟩
    rw [hvc]
    exact naturalRootLine_smul r w c hc

end SymmetricSubgroupAsymptotics.CFSGSymplecticTransvectionGeometry
