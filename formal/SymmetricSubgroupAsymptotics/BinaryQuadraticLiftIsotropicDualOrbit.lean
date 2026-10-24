import SymmetricSubgroupAsymptotics.BinaryQuadraticLiftDualOrbit
import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas

/-! A normalized binary central character already has a sufficiently
large dual orbit under transvections from ONE totally isotropic coordinate
space. No full symplectic action or quadratic-type classification is
assumed. The kernel of its literal restriction supplies all parameters. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
namespace SymmetricSubgroupAsymptotics.BinaryQuadraticLiftIsotropicDualOrbit
open BinaryQuadraticRefinementTransvections BinaryQuadraticLiftAction
open BinaryQuadraticLiftDualOrbit
variable {K I G : Type} [Field K] [CharP K 2] [Fintype I] [Group G]

theorem dual_orbit_card_lower [Finite K] (hK : Nat.card K=2)
    (ρ : G →* Vector (K := K) (I := I) ≃ₗ[K] Vector (K := K) (I := I))
    (hB : ∀ g v w, polar (ρ g v) (ρ g w)=polar v w)
    (htransY : ∀ v : I → K, ∃ g : G, ∀ x, ρ g x=transvectionMap (0,v) x)
    (φ : Module.Dual K (Coordinates (K := K) (I := I))) (hφ : φ (0,1)=1)
    (hI : 0<Fintype.card I) :
    Nat.card K^(Fintype.card I-1) ≤
      Nat.card (InvariantAnnihilatorOrbitIndex.dualOrbit (liftHom hK ρ hB) φ) := by
  classical
  letI : Finite (Module.Dual K (Coordinates (K := K) (I := I))) := Module.finite_of_finite K
  let L : (I → K) →ₗ[K] K := φ.comp
    ((LinearMap.inl K (Vector (K := K) (I := I)) K).comp
      (LinearMap.inr K (I → K) (I → K)))
  have hr : Module.finrank K L.range ≤ 1 := by
    simpa only [Module.finrank_self] using Submodule.finrank_le L.range
  have hdim := L.finrank_range_add_finrank_ker
  rw [Module.finrank_fintype_fun_eq_card] at hdim
  have hk : Fintype.card I-1 ≤ Module.finrank K L.ker := by omega
  have hc : Nat.card K^(Fintype.card I-1) ≤ Nat.card L.ker := by
    rw [Module.natCard_eq_pow_finrank (K := K) (V := L.ker)]
    exact Nat.pow_le_pow_right Nat.card_pos hk
  obtain ⟨a,b,hcoeff⟩ := exists_refinement_coefficients φ
  let Z := {v : Vector (K := K) (I := I) // refinement a b v=0}
  let j : L.ker → Z := fun v => ⟨(0,v.val),by
    have hv : φ ((0,v.val),0)=0 := v.property
    rw [←hcoeff]
    change q0 (0,v.val)+φ ((0,v.val),0)=0
    simpa only [q0,zero_dotProduct,zero_add] using hv⟩
  let g : (I → K) → G := fun v => Classical.choose (htransY v)
  have hg (v : I → K) (x : Vector (K := K) (I := I)) :
      ρ (g v) x=transvectionMap (0,v) x := Classical.choose_spec (htransY v) x
  let R := InvariantAnnihilatorOrbitIndex.dualOrbit (liftHom hK ρ hB) φ
  let f : L.ker → R := fun v =>
    ⟨φ.comp (liftHom hK ρ hB (g v.val)).toLinearMap,by
      refine ⟨(g v.val)⁻¹,?_⟩
      rw [inv_inv]⟩
  have hformula (v : L.ker) (x : Vector (K := K) (I := I)) :
      refinementOfFunctional (f v).val x=refinement a b (transvectionMap (0,v.val) x) := by
    change refinementOfFunctional
      (φ.comp (liftHom hK ρ hB (g v.val)).toLinearMap) x = _
    rw [refinementOfFunctional_comp_lift hK ρ hB φ hφ,hcoeff,hg]
  have hf : Function.Injective f := by
    intro v w he
    have hj : j v=j w := by
      apply transvection_chart_injective hK a b
      funext x
      change refinement a b (transvectionMap (0,v.val) x)=
        refinement a b (transvectionMap (0,w.val) x)
      rw [←hformula v x,←hformula w x]
      exact congrArg (fun ψ : Module.Dual K (Coordinates (K := K) (I := I)) =>
        refinementOfFunctional ψ x) (congrArg (fun y : R => y.val) he)
    exact Subtype.ext (congrArg (fun y : Z => y.val.2) hj)
  exact hc.trans (Nat.card_le_card_of_injective f hf)

end SymmetricSubgroupAsymptotics.BinaryQuadraticLiftIsotropicDualOrbit
