import SymmetricSubgroupAsymptotics.BinaryQuadraticLiftAction
import SymmetricSubgroupAsymptotics.InvariantAnnihilatorOrbitIndex
import Mathlib.LinearAlgebra.Pi
import Mathlib.LinearAlgebra.Prod

/-! Normalized central characters of the constructed binary point lift
are genuine quadratic refinements. Literal transvections at singular
vectors inject into their actual dual orbit; a lower orbit bound is
proved from words containing those transvections, not assumed. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
open scoped BigOperators

namespace SymmetricSubgroupAsymptotics.BinaryQuadraticLiftDualOrbit
open BinaryQuadraticRefinementTransvections BinaryQuadraticLiftAction
variable {K I G : Type} [Field K] [CharP K 2] [Fintype I] [Group G]

omit [CharP K 2] in
theorem exists_refinement_coefficients
    (φ : Module.Dual K (Coordinates (K := K) (I := I))) :
    ∃ a b : I → K, ∀ v : Vector (K := K) (I := I),
      refinementOfFunctional φ v = refinement a b v := by
  classical
  let L : Vector (K := K) (I := I) →ₗ[K] K :=
    φ.comp (LinearMap.inl K (Vector (K := K) (I := I)) K)
  let L1 : (I → K) →ₗ[K] K := L.comp (LinearMap.inl K (I → K) (I → K))
  let L2 : (I → K) →ₗ[K] K := L.comp (LinearMap.inr K (I → K) (I → K))
  let a : I → K := fun i => L1 (fun j => if i=j then 1 else 0)
  let b : I → K := fun i => L2 (fun j => if i=j then 1 else 0)
  have hfirst (x : I → K) : L1 x = dotProduct a x := by
    calc
      _ = ∑ i, x i*a i := by
        simpa only [smul_eq_mul] using LinearMap.pi_apply_eq_sum_univ L1 x
      _ = _ := Finset.sum_congr rfl (fun _ _ => mul_comm _ _)
  have hsecond (x : I → K) : L2 x = dotProduct b x := by
    calc
      _ = ∑ i, x i*b i := by
        simpa only [smul_eq_mul] using LinearMap.pi_apply_eq_sum_univ L2 x
      _ = _ := Finset.sum_congr rfl (fun _ _ => mul_comm _ _)
  have hsplit (v : Vector (K := K) (I := I)) : L v = L1 v.1+L2 v.2 := by
    have hs : v = (v.1,0)+(0,v.2) := by apply Prod.ext <;> simp
    calc
      _ = L ((v.1,0)+(0,v.2)) := congrArg L hs
      _ = _ := map_add L _ _
  refine ⟨a,b,?_⟩
  intro v
  change q0 v+L v = dotProduct v.1 v.2+dotProduct a v.1+dotProduct b v.2
  rw [hsplit, hfirst, hsecond]
  exact (add_assoc _ _ _).symm

/-- The only structural group input is that its ACTUAL linear action
contains every displayed natural transvection. -/
theorem dual_orbit_card_lower [Finite K] (hK : Nat.card K = 2)
    (ρ : G →* Vector (K := K) (I := I) ≃ₗ[K] Vector (K := K) (I := I))
    (hB : ∀ g v w, polar (ρ g v) (ρ g w) = polar v w)
    (htransvection : ∀ v : Vector (K := K) (I := I),
      ∃ g : G, ∀ x, ρ g x = transvectionMap v x)
    (φ : Module.Dual K (Coordinates (K := K) (I := I))) (hφ : φ (0,1) = 1) :
    (Nat.card K ^ Fintype.card I-1)*Nat.card K^(Fintype.card I-1) ≤
      Nat.card (InvariantAnnihilatorOrbitIndex.dualOrbit (liftHom hK ρ hB) φ) := by
  classical
  letI : Finite (Module.Dual K (Coordinates (K := K) (I := I))) :=
    Module.finite_of_finite K
  obtain ⟨a,b,hcoeff⟩ := exists_refinement_coefficients φ
  let Z := {v : Vector (K := K) (I := I) // refinement a b v = 0}
  let g : Vector (K := K) (I := I) → G := fun v => Classical.choose (htransvection v)
  have hg (v x : Vector (K := K) (I := I)) : ρ (g v) x = transvectionMap v x :=
    Classical.choose_spec (htransvection v) x
  let R := InvariantAnnihilatorOrbitIndex.dualOrbit (liftHom hK ρ hB) φ
  let f : Z → R := fun v =>
    ⟨φ.comp (liftHom hK ρ hB (g v.val)).toLinearMap, by
      refine ⟨(g v.val)⁻¹, ?_⟩
      rw [inv_inv]⟩
  have hformula (v : Z) (x : Vector (K := K) (I := I)) :
      refinementOfFunctional (f v).val x = refinement a b (transvectionMap v.val x) := by
    change refinementOfFunctional
      (φ.comp (liftHom hK ρ hB (g v.val)).toLinearMap) x = _
    rw [refinementOfFunctional_comp_lift hK ρ hB φ hφ, hcoeff, hg]
  have hf : Function.Injective f := by
    intro v w he
    apply transvection_chart_injective hK a b
    funext x
    change refinement a b (transvectionMap v.val x) = refinement a b (transvectionMap w.val x)
    rw [← hformula v x, ← hformula w x]
    exact congrArg (fun ψ : Module.Dual K (Coordinates (K := K) (I := I)) =>
      refinementOfFunctional ψ x) (congrArg (fun y : R => y.val) he)
  exact (zero_card_lower a b).trans (Nat.card_le_card_of_injective f hf)

end SymmetricSubgroupAsymptotics.BinaryQuadraticLiftDualOrbit
