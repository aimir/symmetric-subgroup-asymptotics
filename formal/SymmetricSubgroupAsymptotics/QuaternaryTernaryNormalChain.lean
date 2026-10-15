import SymmetricSubgroupAsymptotics.QuaternaryTernaryInvariantPlane
import SymmetricSubgroupAsymptotics.BinaryFourAugmentationActions
import SymmetricSubgroupAsymptotics.FiniteNormalChainGenerators
import SymmetricSubgroupAsymptotics.NormalGeneratorTypeSharing
import Mathlib.GroupTheory.SpecificGroups.Cyclic.Basic

/-! Every normal subgroup of the displayed `C4^2 ⋊ C3` is normally cyclic.
Inside the original translation kernel this is the invariant-submodule
chain over `ZMod 4`. Outside it, an explicit inverse of `r - 1` forces
the entire translation kernel. No group or normal-subgroup census is used. -/

set_option autoImplicit false
noncomputable section

namespace SymmetricSubgroupAsymptotics
namespace QuaternaryTernaryNormalChain

open QuaternaryTernaryInvariantPlane SemidirectProduct

abbrev Ternary := Multiplicative (ZMod 3)

def action : Ternary →* MulAut (Multiplicative Plane) :=
  BinaryFourBlockAugmentation.powersHom 3 cycle.toAddEquiv.toMultiplicative (by
    apply MulEquiv.ext
    intro x
    change cycle (cycle (cycle x.toAdd)) = x.toAdd
    exact congrArg (fun f : Plane ≃ₗ[Scalar] Plane => f x.toAdd) cycle_cube)

abbrev Model := Multiplicative Plane ⋊[action] Ternary

instance : Finite Model :=
  Finite.of_equiv (Multiplicative Plane × Ternary) SemidirectProduct.equivProd.symm

def translationKernel : Subgroup Model := (rightHom : Model →* Ternary).ker

instance : translationKernel.Normal :=
  inferInstanceAs (rightHom : Model →* Ternary).ker.Normal

theorem action_generator (x : Plane) :
    action (Multiplicative.ofAdd 1) (Multiplicative.ofAdd x) =
      Multiplicative.ofAdd (cycle x) := by
  change (cycle.toAddEquiv.toMultiplicative ^ (1 : ZMod 3).val)
    (Multiplicative.ofAdd x) = Multiplicative.ofAdd (cycle x)
  rw [ZMod.val_one, pow_one]
  rfl

theorem conjugate_translation (g : Model) (v : Multiplicative Plane) :
    g * inl v * g⁻¹ = inl (action g.right v) := by
  conv_lhs => rw [← inl_left_mul_inr_right g]
  have h : (inr g.right : Model) * inl v * (inr g.right)⁻¹ =
      inl (action g.right v) := by
    rw [← map_inv]
    exact (inl_aut _ _).symm
  calc
    (inl g.left * inr g.right : Model) * inl v * (inl g.left * inr g.right)⁻¹ =
        (inl g.left : Model) *
          ((inr g.right : Model) * inl v * (inr g.right)⁻¹) * (inl g.left)⁻¹ := by
      group
    _ = (inl (g.left * action g.right v * g.left⁻¹) : Model) := by
      rw [h, ← map_inv, ← map_mul, ← map_mul]
    _ = _ := by rw [mul_comm g.left, mul_inv_cancel_right]

def normalSpace (N : Subgroup Model) : Submodule Scalar Plane :=
  AddSubgroup.toZModSubmodule 4
    (Subgroup.toAddSubgroup' (N.comap (inl : Multiplicative Plane →* Model)))

theorem normalSpace_cycle (N : Subgroup Model) (hN : N.Normal)
    (x : Plane) (hx : x ∈ normalSpace N) : cycle x ∈ normalSpace N := by
  have h := hN.conj_mem (inl (Multiplicative.ofAdd x)) hx
    (inr (Multiplicative.ofAdd (1 : ZMod 3)))
  rw [conjugate_translation, right_inr, action_generator] at h
  exact h

theorem le_of_normalSpace_le (A B : Subgroup Model) (hA : A ≤ translationKernel)
    (hAB : normalSpace A ≤ normalSpace B) : A ≤ B := by
  intro g hg
  have hgr : g.right = 1 := hA hg
  have hform : (inl g.left : Model) = g := SemidirectProduct.ext rfl hgr.symm
  have hx : g.left.toAdd ∈ normalSpace A := by
    change (inl g.left : Model) ∈ A
    rw [hform]
    exact hg
  have hy := hAB hx
  change (inl g.left : Model) ∈ B at hy
  exact hform ▸ hy

/-- For a nonidentity ternary action, `r + 2` is the inverse of `r - 1`
over `ZMod 4`, since `r² + r + 1 = 0` and `-3 = 1`. -/
theorem action_difference_inverse (z : Ternary) (hz : z ≠ 1) (x : Plane) :
    let y := (action z (Multiplicative.ofAdd x)).toAdd + (2 : Scalar) • x
    (action z (Multiplicative.ofAdd y)).toAdd - y = x := by
  have h : ∀ z : Ternary, z ≠ 1 → ∀ x : Plane,
      let y := (action z (Multiplicative.ofAdd x)).toAdd + (2 : Scalar) • x
      (action z (Multiplicative.ofAdd y)).toAdd - y = x := by
    decide +kernel
  exact h z hz x

theorem kernel_cover (N : Subgroup Model) (hN : N.Normal)
    (hNE : ¬ N ≤ translationKernel) : translationKernel ≤ N := by
  classical
  obtain ⟨g, hgN, hgE⟩ := Set.not_subset.mp hNE
  have hgr : g.right ≠ 1 := hgE
  intro e he
  let v : Plane := (action g.right e.left).toAdd + (2 : Scalar) • e.left.toAdd
  let t : Model := inl (Multiplicative.ofAdd v)
  have hc : g * t * g⁻¹ * t⁻¹ ∈ N := by
    have h := hN.conj_mem g⁻¹ (N.inv_mem hgN) t
    simpa only [mul_assoc] using N.mul_mem hgN h
  have hcomm : g * t * g⁻¹ * t⁻¹ = e := by
    dsimp only [t]
    rw [conjugate_translation, ← map_inv, ← map_mul]
    apply SemidirectProduct.ext
    · apply Multiplicative.toAdd.injective
      change (action g.right (Multiplicative.ofAdd v)).toAdd + -v = e.left.toAdd
      simpa only [sub_eq_add_neg] using action_difference_inverse g.right hgr e.left.toAdd
    · exact (show e.right = 1 from he).symm
  exact hcomm ▸ hc

theorem ternary_subgroup_total (A B : Subgroup Ternary) : A ≤ B ∨ B ≤ A := by
  have hcard : Nat.card Ternary = 3 := by
    rw [Nat.card_congr (Multiplicative.toAdd : Ternary ≃ ZMod 3), Nat.card_zmod]
  letI : Fact (Nat.card Ternary).Prime := ⟨by rw [hcard]; decide⟩
  rcases A.eq_bot_or_eq_top_of_prime_card with h | h
  · left; rw [h]; exact bot_le
  · right; rw [h]; exact le_top

theorem normal_total (A B : Subgroup Model) (hA : A.Normal) (hB : B.Normal) :
    A ≤ B ∨ B ≤ A := by
  classical
  by_cases hAK : A ≤ translationKernel
  · by_cases hBK : B ≤ translationKernel
    · rcases invariant_submodule_total (normalSpace A) (normalSpace B)
          (normalSpace_cycle A hA) (normalSpace_cycle B hB) with h | h
      · exact Or.inl (le_of_normalSpace_le A B hAK h)
      · exact Or.inr (le_of_normalSpace_le B A hBK h)
    · exact Or.inl (hAK.trans (kernel_cover B hB hBK))
  · by_cases hBK : B ≤ translationKernel
    · exact Or.inr (hBK.trans (kernel_cover A hA hAK))
    · let pi : Model →* Ternary := rightHom
      have hKA : pi.ker ≤ A := kernel_cover A hA hAK
      have hKB : pi.ker ≤ B := kernel_cover B hB hBK
      rcases ternary_subgroup_total (A.map pi) (B.map pi) with h | h
      · left
        calc
          A = (A.map pi).comap pi := (Subgroup.comap_map_eq_self hKA).symm
          _ ≤ (B.map pi).comap pi := Subgroup.comap_mono h
          _ = B := Subgroup.comap_map_eq_self hKB
      · right
        calc
          B = (B.map pi).comap pi := (Subgroup.comap_map_eq_self hKB).symm
          _ ≤ (A.map pi).comap pi := Subgroup.comap_mono h
          _ = A := Subgroup.comap_map_eq_self hKA

theorem normal_generating_singletons : ∀ N : Subgroup Model, N.Normal →
    ∃ x : Fin 1 → Model, Subgroup.normalClosure (Set.range x) = N :=
  normal_generating_singletons_of_finite_normal_total normal_total

theorem normalGen_le_one (N : Subgroup Model) [N.Normal] : MarkedC4.normalGen N ≤ 1 := by
  obtain ⟨x, hx⟩ := normal_generating_singletons N inferInstance
  exact normalGen_le_of_fin_tuple x hx

theorem socle_of_surjective {Q : Type} [Group Q] (pi : Model →* Q)
    (hpi : Function.Surjective pi) : SocleNormalGeneratorBound Q 1 :=
  normal_generating_tuples_of_surjective pi hpi normal_generating_singletons
    (finiteGroupSocle Q) inferInstance

theorem quotientSocle (N : Subgroup Model) [N.Normal] :
    SocleNormalGeneratorBound (Model ⧸ N) 1 :=
  socle_of_surjective (QuotientGroup.mk' N) (QuotientGroup.mk'_surjective N)

end QuaternaryTernaryNormalChain
end SymmetricSubgroupAsymptotics

end
