import SymmetricSubgroupAsymptotics.LinearSemidirectTranslationSubgroups
import SymmetricSubgroupAsymptotics.NormalFGeneratorBounds

/-! A reusable proper normal subgroup in a linear semidirect product.
Its mixed commutator is charged to the SAME invariant translation space.
The subgroup need not contain the whole translation kernel. -/
set_option autoImplicit false
noncomputable section
open scoped commutatorElement
namespace SymmetricSubgroupAsymptotics.LinearSemidirectCoprimeSocleBounds
open SemidirectProduct
variable {p : ℕ} [Fact p.Prime] {R V : Type}
    [Group R] [AddCommGroup V] [Module (ZMod p) V]
    [FiniteDimensional (ZMod p) V]
    (rho : R →* (V ≃ₗ[ZMod p] V))

theorem commutator_translation (g : Model rho) (v : V) :
    ⁅g, (inl (Multiplicative.ofAdd v) : Model rho)⁆ =
      inl (Multiplicative.ofAdd (rho g.right v - v)) := by
  change (g * inl (Multiplicative.ofAdd v) * g⁻¹) *
    (inl (Multiplicative.ofAdd v))⁻¹ = _
  rw [conjugate_translation, ← map_inv, ← map_mul]
  simp only [linearAction, sub_eq_add_neg]
  rfl


theorem commutator_central_complement (z : R) (hz : z ∈ Subgroup.center R)
    (g : Model rho) :
    ⁅(inr z : Model rho), g⁆ =
      inl (Multiplicative.ofAdd (rho z g.left.toAdd - g.left.toAdd)) := by
  have hh : ⁅(inr z : Model rho), (inr g.right : Model rho)⁆ = 1 := by
    rw [← map_commutatorElement]
    have hc : ⁅z, g.right⁆ = 1 :=
      commutatorElement_eq_one_iff_mul_comm.mpr
        (Subgroup.mem_center_iff.mp hz g.right).symm
    rw [hc, map_one]
  conv_lhs => rw [← inl_left_mul_inr_right g]
  rw [commutatorElement_mul_right_eq_mul_conj, hh, mul_one, mul_inv_cancel_right]
  exact commutator_translation rho (inr z) g.left.toAdd

def properNormalGenerators (B : Submodule (ZMod p) V) (z : R) :
    B ⊕ Unit → Model rho
  | .inl b => inl (Multiplicative.ofAdd b.val)
  | .inr _ => inr z

def properNormalF (B : Submodule (ZMod p) V) (z : R) : Subgroup (Model rho) :=
  Subgroup.closure (Set.range (properNormalGenerators rho B z))

theorem translationSpace_le_properNormalF
    (B C : Submodule (ZMod p) V) (hCB : C ≤ B) (z : R) :
    translationSpace rho C ≤ properNormalF rho B z := by
  intro g hg
  have he : g = (inl g.left : Model rho) := by
    apply SemidirectProduct.ext
    · rfl
    · exact hg.1
  rw [he]
  exact Subgroup.subset_closure
    ⟨Sum.inl (⟨g.left.toAdd, hCB hg.2⟩ : B), rfl⟩

theorem properNormalF_mixedCommutator_le
    (B C : Submodule (ZMod p) V) (z : R)
    (hz : z ∈ Subgroup.center R)
    (hC : ∀ r v, v ∈ C → rho r v ∈ C)
    (hBdisp : ∀ r v, v ∈ B → rho r v - v ∈ C)
    (hzdisp : ∀ v, rho z v - v ∈ C) :
    ⁅properNormalF rho B z, (⊤ : Subgroup (Model rho))⁆ ≤ translationSpace rho C := by
  letI := translationSpace_normal rho C hC
  have hg : Subgroup.closure (Set.range (fun g : Model rho => g)) = ⊤ := by simp
  rw [← hg]
  apply mixedCommutator_le_of_generator_checks
  intro i g
  cases i with
  | inl b =>
      change ⁅(inl (Multiplicative.ofAdd b.val) : Model rho), g⁆ ∈ _
      rw [← commutatorElement_inv, commutator_translation]
      exact (translationSpace rho C).inv_mem ⟨rfl, hBdisp g.right b.val b.property⟩
  | inr _ =>
      change ⁅(inr z : Model rho), g⁆ ∈ _
      rw [commutator_central_complement rho z hz]
      exact ⟨rfl, hzdisp g.left.toAdd⟩

theorem properNormalF_normal
    (B C : Submodule (ZMod p) V) (z : R) (hCB : C ≤ B)
    (hz : z ∈ Subgroup.center R)
    (hC : ∀ r v, v ∈ C → rho r v ∈ C)
    (hBdisp : ∀ r v, v ∈ B → rho r v - v ∈ C)
    (hzdisp : ∀ v, rho z v - v ∈ C) : (properNormalF rho B z).Normal :=
  Subgroup.commutator_top_right_le_iff.mp
    ((properNormalF_mixedCommutator_le rho B C z hz hC hBdisp hzdisp).trans
      (translationSpace_le_properNormalF rho B C hCB z))

end SymmetricSubgroupAsymptotics.LinearSemidirectCoprimeSocleBounds
