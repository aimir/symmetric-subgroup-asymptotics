import SymmetricSubgroupAsymptotics.CFSGCosetDataIndex
import SymmetricSubgroupAsymptotics.CFSGConnectedRootParameterField
import Mathlib.GroupTheory.GroupAction.ConjAct
import Mathlib.Tactic.Group

/-! Count semilinear root-parameter actions modulo a proved scalar
subgroup. This does not assume a classification of automorphisms: the
actual common-field formula, root-parameter faithfulness, and scalar lift
are explicit inputs discharged by the later original-model consumers. -/
set_option autoImplicit false
noncomputable section
namespace SymmetricSubgroupAsymptotics.CFSGSemilinearRootCosetIndex
open CFSGCosetDataIndex
variable {K G A B I : Type*} [Field K] [Finite K] [Group G]
    [Group A] [Group B] [Fintype I]

theorem scalar_lift_index_le (u : I → K → G) (ρ : A →* MulAut G)
    (hfaith : ∀ a b : A, (∀ i x, ρ a (u i x) = ρ b (u i x)) → a = b)
    (hsem : ∀ a : A, ∃ (σ : K ≃+* K) (c : I → Kˣ), ∀ i x,
      ρ a (u i x) = u i ((c i : K) * σ x))
    (lift : B →* A) (χ : B →* (I → Kˣ))
    (hscalar : ∀ t i x, ρ (lift t) (u i x) = u i ((χ t i : K) * x)) :
    lift.range.index ≤ χ.range.index * Nat.card (K ≃+* K) := by
  classical
  letI : Finite (K ≃+* K) := Finite.of_injective
    (fun σ : K ≃+* K => (σ : K → K)) DFunLike.coe_injective
  letI : Finite Kˣ := Finite.of_injective (fun t : Kˣ => (t : K)) Units.val_injective
  choose σ c hs using hsem
  apply index_le_of_coset_data lift.range χ.range c σ
  intro a b hc hσ
  have hmem : (c a)⁻¹ * c b ∈ χ.range := QuotientGroup.eq.mp hc
  obtain ⟨t, ht⟩ := hmem
  have hscale (i : I) : χ t i * c a i = c b i := by
    have hi := congrFun ht i
    change χ t i = (c a i)⁻¹ * c b i at hi
    rw [hi]
    calc
      ((c a i)⁻¹ * c b i) * c a i = ((c a i)⁻¹ * c a i) * c b i := by ac_rfl
      _ = c b i := by rw [inv_mul_cancel, one_mul]
  have hscale_val (i : I) : (χ t i : K) * (c a i : K) = (c b i : K) :=
    congrArg Units.val (hscale i)
  have hb : lift t * a = b := by
    apply hfaith
    intro i x
    calc
      ρ (lift t * a) (u i x) = ρ (lift t) (ρ a (u i x)) := by rw [map_mul]; rfl
      _ = ρ (lift t) (u i ((c a i : K) * σ a x)) := congrArg (ρ (lift t)) (hs a i x)
      _ = u i ((χ t i : K) * ((c a i : K) * σ a x)) := hscalar t i _
      _ = u i ((c b i : K) * σ b x) := by rw [← mul_assoc, hscale_val, hσ]
      _ = ρ b (u i x) := (hs b i x).symm
  refine ⟨t⁻¹, ?_⟩
  rw [map_inv, ← hb]
  group

end SymmetricSubgroupAsymptotics.CFSGSemilinearRootCosetIndex
