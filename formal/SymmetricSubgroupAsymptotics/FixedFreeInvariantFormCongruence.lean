import SymmetricSubgroupAsymptotics.BilinearRelativeUnit
import SymmetricSubgroupAsymptotics.UnitaryResolventTraceOne
import SymmetricSubgroupAsymptotics.FiniteCommutingTraceOneNorm
import Mathlib.Algebra.Group.Commute.Units

/-! Two symmetric nondegenerate forms preserved by the SAME fixed-point-
free operator in characteristic two are congruent by an actual operator
in its centralizer. The norm root is constructed in the actual finite
star-stable commutative subring, not supplied as a form-classification
or conjugacy-fibre hypothesis. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section

namespace SymmetricSubgroupAsymptotics.FixedFreeInvariantFormCongruence
open BilinearRelativeUnit BilinearAdjointStarRing InvariantBilinearFormCentralizer

variable {K V : Type*} [Field K] [CharP K 2]
    [AddCommGroup V] [Module K V] [Finite V] [Nontrivial V]

theorem exists_commuting_congruence
    (B C : LinearMap.BilinForm K V) (hB : B.Nondegenerate) (hC : C.Nondegenerate)
    (hBs : B.IsSymm) (hCs : C.IsSymm) (A : V ≃ₗ[K] V)
    (hBA : ∀ x y : V, B (A x) (A y)=B x y)
    (hCA : ∀ x y : V, C (A x) (A y)=C x y)
    (hfixed : ∀ x : V, A x=x → x=0) :
    ∃ T : V ≃ₗ[K] V, Commute T.toLinearMap A.toLinearMap ∧
      ∀ x y : V, B (T x) (T y)=C x y := by
  letI : Module.Finite K V := Module.Finite.of_finite
  let E := Module.End K V
  letI : Finite E :=
    Finite.of_injective (fun T:E => (T:V→V)) LinearMap.coe_injective
  letI : CharP E 2 := charP_of_injective_ringHom
    (f := algebraMap K E) (algebraMap K E).injective 2
  letI := adjointStarRing B hB hBs
  let a : Eˣ := LinearMap.GeneralLinearGroup.ofLinearEquiv A
  let F : E := A.toLinearMap+1
  have hinj : Function.Injective F := by
    intro x y hxy
    have hz : F (x-y)=0 := by rw [map_sub,hxy,sub_self]
    have hF : F=A.toLinearMap-1 := by
      change A.toLinearMap+1=A.toLinearMap-1
      rw [sub_eq_add_neg,CharTwo.neg_eq]
    rw [hF] at hz
    change A (x-y)-(x-y)=0 at hz
    exact sub_eq_zero.mp (hfixed (x-y) (sub_eq_zero.mp hz))
  let b : Eˣ := LinearMap.GeneralLinearGroup.ofLinearEquiv
    (LinearEquiv.ofBijective F (Finite.injective_iff_bijective.mp hinj))
  have hb : (b:E)=(a:E)+1 := rfl
  have ha : star (a:E)=(↑(a⁻¹):E) :=
    isometry_adjoint_inverse B hB hBs A hBA
  let u : E := (b⁻¹:Eˣ)
  have hu : u+star u=1 := UnitaryResolventTraceOne.inverse_shift_trace_one a b ha hb
  let s : Eˣ := relativeUnit B hB C hC
  have hs : star (s:E)=(s:E) := relativeUnit_selfadjoint B hB hBs C hC hCs
  have hSA : Commute (s:E) A.toLinearMap := relativeUnit_commutes B hB C hC A hBA hCA
  have hSb : Commute (s:E) (b:E) := by
    rw [hb]
    exact hSA.add_right (Commute.one_right _)
  have hSu : Commute (s:E) u := hSb.units_inv_right
  have hAb : Commute A.toLinearMap (b:E) := by
    rw [hb]
    exact (Commute.refl _).add_right (Commute.one_right _)
  have hAu : Commute A.toLinearMap u := hAb.units_inv_right
  obtain ⟨t,ht,hcentral⟩ :=
    FiniteCommutingTraceOneNorm.exists_unit_norm_commuting u hu s hs hSu.symm
  have hAt : Commute A.toLinearMap (t:E) := hcentral A.toLinearMap hAu hSA.symm
  have hSt : Commute (s:E) (t:E) := hcentral (s:E) hSu (Commute.refl _)
  have hreverse : star (t:E)*(t:E)=(s:E) := by
    have he : (t:E)*(star (t:E)*(t:E))=(t:E)*(s:E) := by
      rw [←mul_assoc,ht]
      exact hSt.eq
    have hc := congrArg (fun x:E => (↑(t⁻¹):E)*x) he
    simpa only [←mul_assoc,Units.inv_mul,one_mul] using hc
  let T : V ≃ₗ[K] V := LinearMap.GeneralLinearGroup.toLinearEquiv t
  refine ⟨T,hAt.symm,?_⟩
  intro x y
  calc
    B (T x) (T y) = B (star (t:E) ((t:E) x)) y :=
      (adjoint_apply B hB (t:E) ((t:E) x) y).symm
    _ = B ((s:E) x) y := congrArg (fun R:E => B (R x) y) hreverse
    _ = C x y := operatorEquiv_apply B hB C x y

end SymmetricSubgroupAsymptotics.FixedFreeInvariantFormCongruence
