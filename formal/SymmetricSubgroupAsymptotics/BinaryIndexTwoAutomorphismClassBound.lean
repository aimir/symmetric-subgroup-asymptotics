import SymmetricSubgroupAsymptotics.AutomorphismIndexTwoAffineChart
import SymmetricSubgroupAsymptotics.BinaryEightElementSemidirectClassBound
import Mathlib.Algebra.Field.ZMod

/-! An actual faithful automorphism action preserving a binary subgroup
of order eight and index two embeds in its literal affine semidirect
group. The checked all-subgroup affine-eight estimate gives24 classes.
The module structure is restricted from the same original module. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
open scoped Classical
namespace SymmetricSubgroupAsymptotics.BinaryIndexTwoAutomorphismClassBound

variable {N G : Type} [CommGroup N] [Group G] [Finite N] [Finite G]
    {p : ℕ} [Fact p.Prime] [Module (ZMod p) (Additive N)]

theorem class_card_le_twentyFour (hp : p=2) (K : Subgroup N)
    (hK : Nat.card K=8) (hindex : K.index=2)
    (φ : G →* MulAut N) (hφ : Function.Injective φ)
    (hstable : ∀ (g : G) (n : N), φ g n ∈ K ↔ n ∈ K) :
    Nat.card (ConjClasses G) ≤ 24 := by
  have hproper : K≠⊤ := by
    intro ht
    rw [ht,Subgroup.index_top] at hindex
    omega
  have hex : ∃ a : N, a∉K := by
    by_contra h
    apply hproper
    apply top_unique
    intro a _
    by_contra ha
    exact h ⟨a,ha⟩
  obtain ⟨a,ha⟩ := hex
  let W : Submodule (ZMod p) (Additive N) :=
    AddSubgroup.toZModSubmodule p (Subgroup.toAddSubgroup K)
  let eW : Additive K ≃+ W := {
    toFun := fun k => ⟨Additive.ofMul k.toMul.val,k.toMul.property⟩
    invFun := fun v => Additive.ofMul ⟨v.val.toMul,v.property⟩
    left_inv := fun _ => rfl
    right_inv := fun _ => rfl
    map_add' := fun _ _ => rfl }
  letI : Module (ZMod p) (Additive K) := eW.module (ZMod p)
  letI : Finite (MulAut K) := Finite.of_injective
    (fun f : MulAut K => (f : K → K)) DFunLike.coe_injective
  let f := AutomorphismIndexTwoAffineChart.affineHom K hindex φ hstable a
  have hf : Function.Injective f :=
    AutomorphismIndexTwoAffineChart.affineHom_injective K hindex φ hφ hstable a ha
  let e := MonoidHom.ofInjective hf
  letI : Finite f.range := Finite.of_surjective f.rangeRestrict f.rangeRestrict_surjective
  have hc : Nat.card (ConjClasses G) ≤ Nat.card (ConjClasses f.range) :=
    Nat.card_le_card_of_surjective (ConjClasses.map e.symm.toMonoidHom)
      (ConjClasses.map_surjective e.symm.surjective)
  exact hc.trans (BinaryEightElementSemidirectClassBound.subgroup_class_card_le_twentyFour
    hp hK (MonoidHom.id (MulAut K)) (fun _ _ h => h) f.range)

end SymmetricSubgroupAsymptotics.BinaryIndexTwoAutomorphismClassBound
