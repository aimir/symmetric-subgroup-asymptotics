import SymmetricSubgroupAsymptotics.InvariantLinePlaneFunctionalChart
import SymmetricSubgroupAsymptotics.TernaryFunctionalKernelParabolicClassBound
import Mathlib.LinearAlgebra.Matrix.GeneralLinearGroup.Card

/-! The SAME faithful ternary three-dimensional linear group has at
most78 classes whenever it preserves an actual line or plane. Lines
are passed to their actual dual annihilator; no nonzero transitivity
or invariant complement is assumed. The full linear group order bound
is obtained from the generic matrix cardinality formula. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
open scoped Classical
namespace SymmetricSubgroupAsymptotics.TernaryThreeInvariantSubspaceClassBound
open LinearContragredientSmallSpaceAction

variable {K V G : Type} [Field K] [AddCommGroup V] [Module K V] [Group G]
    [Finite K] [Finite V] [Finite G]

omit [Finite K] in
private theorem finrank_eq_three (hK : Nat.card K=3) (hV : Nat.card V=27) :
    Module.finrank K V=3 := by
  have hh := Module.natCard_eq_pow_finrank (K:=K) (V:=V)
  rw [hV,hK] at hh
  exact Nat.pow_right_injective (by decide : 2≤(3:ℕ)) hh.symm

theorem linearEquiv_card_eq_elevenTwoThirtyTwo
    (hK : Nat.card K=3) (hV : Nat.card V=27) :
    Nat.card (V ≃ₗ[K] V)=11232 := by
  letI : Fintype K := Fintype.ofFinite K
  letI : FiniteDimensional K V := Module.Finite.of_finite
  let b := Module.finBasisOfFinrankEq K V (finrank_eq_three hK hV)
  let e := (Matrix.GeneralLinearGroup.toLin' b).trans
    (LinearMap.GeneralLinearGroup.generalLinearEquiv K V)
  have hKF : Fintype.card K=3 := by simpa only [Nat.card_eq_fintype_card] using hK
  rw [Nat.card_congr e.symm.toEquiv,Matrix.card_GL_field,hKF]
  norm_num [Fin.prod_univ_succ]

theorem class_card_le_seventyEight_of_invariant_kernel
    (hK : Nat.card K=3) (hV : Nat.card V=27)
    (ρ : G →* (V ≃ₗ[K] V)) (hρ : Function.Injective ρ)
    (ℓ : Module.Dual K V) (hℓ : ℓ≠0)
    (hstable : ∀ (g : G) (v : V), ℓ (ρ g v)=0 ↔ ℓ v=0) :
    Nat.card (ConjClasses G)≤78 := by
  let N := Multiplicative V
  let eA : Additive N ≃+ V := {
    toFun := fun n => n.toMul.toAdd
    invFun := fun v => Additive.ofMul (Multiplicative.ofAdd v)
    left_inv := fun _ => rfl
    right_inv := fun _ => rfl
    map_add' := fun _ _ => rfl }
  letI : Module K (Additive N) := eA.module K
  let eL : Additive N ≃ₗ[K] V := eA.linearEquiv K
  let φ : G →* MulAut N := {
    toFun := fun g => (ρ g).toAddEquiv.toMultiplicative
    map_one' := by
      apply MulEquiv.ext
      intro v
      change ρ 1 v.toAdd=v.toAdd
      rw [ρ.map_one]
      rfl
    map_mul' := fun g h => by
      apply MulEquiv.ext
      intro v
      change ρ (g*h) v.toAdd=ρ g (ρ h v.toAdd)
      rw [ρ.map_mul]
      rfl }
  have hφ : Function.Injective φ := by
    intro g h he
    apply hρ
    apply LinearEquiv.ext
    intro v
    exact congrArg (fun f : MulAut N => (f (Multiplicative.ofAdd v)).toAdd) he
  let τ : G →* (Additive N ≃ₗ[K] Additive N) := {
    toFun := fun g => eL.trans ((ρ g).trans eL.symm)
    map_one' := by
      apply LinearEquiv.ext
      intro n
      change eL.symm (ρ 1 (eL n))=n
      rw [ρ.map_one]
      exact eL.symm_apply_apply n
    map_mul' := fun g h => by
      apply LinearEquiv.ext
      intro n
      change eL.symm (ρ (g*h) (eL n))=
        eL.symm (ρ g (eL (eL.symm (ρ h (eL n)))))
      rw [eL.apply_symm_apply,ρ.map_mul]
      rfl }
  let m : Module.Dual K (Additive N) := ℓ.comp eL.toLinearMap
  have hm : m≠0 := by
    intro hz
    apply hℓ
    apply LinearMap.ext
    intro v
    have hh := DFunLike.congr_fun hz (eL.symm v)
    change ℓ (eL (eL.symm v))=0 at hh
    simpa only [eL.apply_symm_apply] using hh
  have hcompat (g : G) (n : N) : τ g (Additive.ofMul n)=Additive.ofMul (φ g n) := by
    apply eL.injective
    change eL (eL.symm (ρ g (eL (Additive.ofMul n))))=ρ g n.toAdd
    rw [eL.apply_symm_apply]
    rfl
  have hstableM (g : G) (n : Additive N) : m (τ g n)=0 ↔ m n=0 := by
    change ℓ (eL (eL.symm (ρ g (eL n))))=0 ↔ ℓ (eL n)=0
    rw [eL.apply_symm_apply]
    exact hstable g (eL n)
  exact TernaryFunctionalKernelParabolicClassBound.class_card_le_seventyEight
    (K:=K) (N:=N) (G:=G) hK hV φ hφ τ hcompat m hm hstableM

theorem class_card_le_seventyEight_of_invariant_plane
    (hK : Nat.card K=3) (hV : Nat.card V=27)
    (ρ : G →* (V ≃ₗ[K] V)) (hρ : Function.Injective ρ)
    (W : Submodule K V) (hplane : Module.finrank K W=2)
    (hW : ∀ (g : G) (v : V), v∈W → ρ g v∈W) :
    Nat.card (ConjClasses G)≤78 := by
  letI : FiniteDimensional K V := Module.Finite.of_finite
  have hd := finrank_eq_three hK hV
  obtain ⟨ℓ,hℓ,hstable⟩ :=
    InvariantLinePlaneFunctionalChart.exists_invariant_kernel_functional_of_codimension_one
      ρ W (by omega) hW
  exact class_card_le_seventyEight_of_invariant_kernel hK hV ρ hρ ℓ hℓ hstable

theorem class_card_le_seventyEight_of_invariant_line
    (hK : Nat.card K=3) (hV : Nat.card V=27)
    (ρ : G →* (V ≃ₗ[K] V)) (hρ : Function.Injective ρ)
    (W : Submodule K V) (hline : Module.finrank K W=1)
    (hW : ∀ (g : G) (v : V), v∈W → ρ g v∈W) :
    Nat.card (ConjClasses G)≤78 := by
  letI : FiniteDimensional K V := Module.Finite.of_finite
  letI : Finite (Module.Dual K V) := Finite.of_injective
    (fun ℓ : Module.Dual K V => (ℓ : V → K)) DFunLike.coe_injective
  have hdual : Nat.card (Module.Dual K V)=27 := by
    rw [Module.natCard_eq_pow_finrank (K:=K) (V:=Module.Dual K V),Subspace.dual_finrank_eq,
      ←Module.natCard_eq_pow_finrank (K:=K) (V:=V)]
    exact hV
  obtain ⟨ℓ,hℓ,hstable⟩ :=
    InvariantLinePlaneFunctionalChart.exists_invariant_kernel_functional_on_dual_of_line_in_three
      ρ W (finrank_eq_three hK hV) hline hW
  exact class_card_le_seventyEight_of_invariant_kernel hK hdual (contragredient ρ)
    (contragredient_injective ρ hρ) ℓ hℓ hstable

end SymmetricSubgroupAsymptotics.TernaryThreeInvariantSubspaceClassBound
