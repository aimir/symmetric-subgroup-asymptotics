import SymmetricSubgroupAsymptotics.QuaternaryTernaryNormalChain
import SymmetricSubgroupAsymptotics.QuaternaryTernaryCyclicSubmodules
import SymmetricSubgroupAsymptotics.NormalImageKernelGeneratorTransfer
import SymmetricSubgroupAsymptotics.CoprimeCyclicQuotientSocles
import Mathlib.GroupTheory.SpecificGroups.Cyclic

/-! Uniform normal-generator width one for a fixed `C4` factor times
the displayed `C4² ⋊ C3`. The translation argument pairs the fixed and
nontrivial ternary types. Outside translations, commutators force the
plane kernel of the actual map onto the cyclic group `C4 × C3`. -/

set_option autoImplicit false
noncomputable section
open scoped Classical

namespace SymmetricSubgroupAsymptotics
namespace QuaternaryTripleTernaryNormalGenerators

open QuaternaryTernaryInvariantPlane QuaternaryTernaryCyclicSubmodules SemidirectProduct

abbrev Model := Multiplicative Scalar × QuaternaryTernaryNormalChain.Model
abbrev CyclicQuotient := Multiplicative Scalar × QuaternaryTernaryNormalChain.Ternary

def translation : Multiplicative Coordinates →* Model where
  toFun x := (Multiplicative.ofAdd x.toAdd.1, inl (Multiplicative.ofAdd x.toAdd.2))
  map_one' := rfl
  map_mul' x y := by
    apply Prod.ext
    · rfl
    · exact (inl : Multiplicative Plane →* QuaternaryTernaryNormalChain.Model).map_mul _ _

def ternaryProjection : Model →* QuaternaryTernaryNormalChain.Ternary :=
  (rightHom : QuaternaryTernaryNormalChain.Model →*
    QuaternaryTernaryNormalChain.Ternary).comp (MonoidHom.snd _ _)

def translationKernel : Subgroup Model := ternaryProjection.ker

instance : translationKernel.Normal := inferInstanceAs ternaryProjection.ker.Normal

def normalSpace (N : Subgroup Model) : Submodule Scalar Coordinates :=
  AddSubgroup.toZModSubmodule 4 (Subgroup.toAddSubgroup' (N.comap translation))

theorem normalSpace_cycle (N : Subgroup Model) (hN : N.Normal)
    (x : Coordinates) (hx : x ∈ normalSpace N) : fullCycle x ∈ normalSpace N := by
  let c : Model := (1, inr (Multiplicative.ofAdd (1 : ZMod 3)))
  have h := hN.conj_mem (translation (Multiplicative.ofAdd x)) hx c
  have hid : c * translation (Multiplicative.ofAdd x) * c⁻¹ =
      translation (Multiplicative.ofAdd (fullCycle x)) := by
    apply Prod.ext
    · change 1 * Multiplicative.ofAdd x.1 * 1⁻¹ = Multiplicative.ofAdd x.1
      simp
    · change (inr (Multiplicative.ofAdd (1 : ZMod 3)) :
          QuaternaryTernaryNormalChain.Model) * inl (Multiplicative.ofAdd x.2) *
          (inr (Multiplicative.ofAdd (1 : ZMod 3)))⁻¹ =
        inl (Multiplicative.ofAdd (cycle x.2))
      rw [QuaternaryTernaryNormalChain.conjugate_translation, right_inr,
        QuaternaryTernaryNormalChain.action_generator]
  change translation (Multiplicative.ofAdd (fullCycle x)) ∈ N
  exact hid ▸ h

theorem translation_form (g : Model) (hg : g ∈ translationKernel) :
    translation (Multiplicative.ofAdd (g.1.toAdd, g.2.left.toAdd)) = g := by
  apply Prod.ext
  · rfl
  · apply SemidirectProduct.ext
    · rfl
    · exact (show g.2.right = 1 from hg).symm

theorem inside_normalGen_le_one (N : Subgroup Model) [N.Normal]
    (hNE : N ≤ translationKernel) : MarkedC4.normalGen N ≤ 1 := by
  obtain ⟨v, hv, hgen⟩ := exists_cyclic_vector (normalSpace N)
    (normalSpace_cycle N inferInstance)
  let x : Fin 1 → Model := fun _ => translation (Multiplicative.ofAdd v)
  let L := Subgroup.normalClosure (Set.range x)
  have hLN : L ≤ N := by
    apply Subgroup.normalClosure_le_normal
    rintro _ ⟨i, rfl⟩
    exact hv
  have hvL : v ∈ normalSpace L :=
    Subgroup.subset_normalClosure (Set.mem_range_self (0 : Fin 1))
  have hspaces : normalSpace N ≤ normalSpace L :=
    hgen (normalSpace L) (normalSpace_cycle L inferInstance) hvL
  apply normalGen_le_of_fin_tuple x
  apply le_antisymm hLN
  intro g hg
  have hform := translation_form g (hNE hg)
  have hvN : (g.1.toAdd, g.2.left.toAdd) ∈ normalSpace N := by
    change translation (Multiplicative.ofAdd (g.1.toAdd, g.2.left.toAdd)) ∈ N
    rwa [hform]
  have hvL := hspaces hvN
  change translation (Multiplicative.ofAdd (g.1.toAdd, g.2.left.toAdd)) ∈ L at hvL
  exact hform ▸ hvL

def quotientMap : Model →* CyclicQuotient where
  toFun g := (g.1, g.2.right)
  map_one' := rfl
  map_mul' _ _ := rfl

theorem quotientMap_surjective : Function.Surjective quotientMap := by
  intro q
  exact ⟨(q.1, inr q.2), rfl⟩

theorem quotientMap_kernel_le : quotientMap.ker ≤ translationKernel := by
  intro g hg
  exact congrArg Prod.snd (MonoidHom.mem_ker.mp hg)

theorem quotientMap_kernel_cover (N : Subgroup Model) (hN : N.Normal)
    (hNE : ¬ N ≤ translationKernel) : quotientMap.ker ≤ N := by
  obtain ⟨g, hgN, hgE⟩ := Set.not_subset.mp hNE
  have hgr : g.2.right ≠ 1 := hgE
  intro e he
  have he₁ : e.1 = 1 := congrArg Prod.fst (MonoidHom.mem_ker.mp he)
  have he₂ : e.2.right = 1 := congrArg Prod.snd (MonoidHom.mem_ker.mp he)
  let v : Plane :=
    (QuaternaryTernaryNormalChain.action g.2.right e.2.left).toAdd +
      (2 : Scalar) • e.2.left.toAdd
  let t : Model := (1, inl (Multiplicative.ofAdd v))
  have hc : g * t * g⁻¹ * t⁻¹ ∈ N := by
    have h := hN.conj_mem g⁻¹ (N.inv_mem hgN) t
    simpa only [mul_assoc] using N.mul_mem hgN h
  have hcomm : g * t * g⁻¹ * t⁻¹ = e := by
    apply Prod.ext
    · change g.1 * 1 * g.1⁻¹ * 1⁻¹ = e.1
      simp [he₁]
    · change g.2 * inl (Multiplicative.ofAdd v) * g.2⁻¹ *
          (inl (Multiplicative.ofAdd v))⁻¹ = e.2
      rw [QuaternaryTernaryNormalChain.conjugate_translation, ← map_inv, ← map_mul]
      apply SemidirectProduct.ext
      · apply Multiplicative.toAdd.injective
        change (QuaternaryTernaryNormalChain.action g.2.right
          (Multiplicative.ofAdd v)).toAdd + -v = e.2.left.toAdd
        simpa only [sub_eq_add_neg] using
          QuaternaryTernaryNormalChain.action_difference_inverse g.2.right hgr e.2.left.toAdd
      · exact he₂.symm
  exact hcomm ▸ hc

instance : IsCyclic CyclicQuotient := by
  apply Group.isCyclic_prod_iff.mpr
  refine ⟨inferInstance, inferInstance, ?_⟩
  have hfour : Nat.card (Multiplicative Scalar) = 4 := by
    rw [Nat.card_congr (Multiplicative.toAdd : Multiplicative Scalar ≃ Scalar), Nat.card_zmod]
  have hthree : Nat.card QuaternaryTernaryNormalChain.Ternary = 3 := by
    rw [Nat.card_congr (Multiplicative.toAdd :
      QuaternaryTernaryNormalChain.Ternary ≃ ZMod 3), Nat.card_zmod]
  rw [hfour, hthree]
  decide

theorem normalGen_le_one (N : Subgroup Model) [N.Normal] : MarkedC4.normalGen N ≤ 1 := by
  by_cases hNE : N ≤ translationKernel
  · exact inside_normalGen_le_one N hNE
  · letI : (N.map quotientMap).Normal :=
      (inferInstance : N.Normal).map quotientMap quotientMap_surjective
    exact normalGen_le_of_kernel_cover_outside quotientMap quotientMap_surjective
      translationKernel quotientMap_kernel_le quotientMap_kernel_cover N hNE
      (CoprimeCyclicQuotientSocles.normalGen_le_one_of_isCyclic (N.map quotientMap))

theorem normal_generating_singletons : ∀ N : Subgroup Model, N.Normal →
    ∃ x : Fin 1 → Model, Subgroup.normalClosure (Set.range x) = N := by
  intro N hN
  letI := hN
  exact exists_normal_generating_tuple_of_normalGen_le N (normalGen_le_one N)

theorem socle_of_surjective {Q : Type} [Group Q] (pi : Model →* Q)
    (hpi : Function.Surjective pi) : SocleNormalGeneratorBound Q 1 :=
  normal_generating_tuples_of_surjective pi hpi normal_generating_singletons
    (finiteGroupSocle Q) inferInstance

theorem quotientSocle (N : Subgroup Model) [N.Normal] :
    SocleNormalGeneratorBound (Model ⧸ N) 1 :=
  socle_of_surjective (QuotientGroup.mk' N) (QuotientGroup.mk'_surjective N)

end QuaternaryTripleTernaryNormalGenerators
end SymmetricSubgroupAsymptotics

end
