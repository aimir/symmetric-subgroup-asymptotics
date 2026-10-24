import SymmetricSubgroupAsymptotics.BinaryQuadraticRefinementTransvections
import Mathlib.Algebra.CharP.Two

/-! A binary symplectic linear action lifts to the additive point-radical
coordinates by the genuine quadratic correction Q0(v)+Q0(gv). Its dual
central-value-one slice acts on quadratic refinements. This constructs
the action; it does not assume a split action on the central coordinate. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section

namespace SymmetricSubgroupAsymptotics.BinaryQuadraticLiftAction
open BinaryQuadraticRefinementTransvections
variable {K I G : Type} [Field K] [CharP K 2] [Fintype I] [Group G]

abbrev Vector := Space (K := K) (I := I)
abbrev Coordinates := Vector (K := K) (I := I) × K

def q0 (v : Vector (K := K) (I := I)) : K := dotProduct v.1 v.2

omit [CharP K 2] in
private theorem q0_add (v w : Vector (K := K) (I := I)) :
    q0 (v+w) = q0 v+q0 w+polar v w := by
  simp only [q0, polar, Prod.fst_add, Prod.snd_add, add_dotProduct, dotProduct_add]
  ring

private def liftFun (ρ : G →* Vector (K := K) (I := I) ≃ₗ[K] Vector (K := K) (I := I))
    (g : G) (a : Coordinates (K := K) (I := I)) : Coordinates (K := K) (I := I) :=
  (ρ g a.1,a.2+q0 a.1+q0 (ρ g a.1))

private theorem liftFun_one
    (ρ : G →* Vector (K := K) (I := I) ≃ₗ[K] Vector (K := K) (I := I))
    (a : Coordinates (K := K) (I := I)) : liftFun ρ 1 a = a := by
  apply Prod.ext
  · change ρ 1 a.1 = a.1
    rw [map_one]
    rfl
  · change a.2+q0 a.1+q0 (ρ 1 a.1) = a.2
    rw [map_one]
    change a.2+q0 a.1+q0 a.1 = a.2
    rw [add_assoc, CharTwo.add_self_eq_zero, add_zero]

private theorem liftFun_mul
    (ρ : G →* Vector (K := K) (I := I) ≃ₗ[K] Vector (K := K) (I := I))
    (g h : G) (a : Coordinates (K := K) (I := I)) :
    liftFun ρ (g*h) a = liftFun ρ g (liftFun ρ h a) := by
  apply Prod.ext
  · change ρ (g*h) a.1 = ρ g (ρ h a.1)
    rw [map_mul]
    rfl
  · change a.2+q0 a.1+q0 (ρ (g*h) a.1) =
      (a.2+q0 a.1+q0 (ρ h a.1))+q0 (ρ h a.1)+q0 (ρ g (ρ h a.1))
    rw [map_mul]
    change a.2+q0 a.1+q0 (ρ g (ρ h a.1)) = _
    have hz := CharTwo.add_self_eq_zero (q0 (ρ h a.1))
    linear_combination -hz

omit [CharP K 2] in
private theorem nonzero_eq_one [Finite K] (hK : Nat.card K = 2) (c : K) (hc : c ≠ 0) :
    c = 1 := by
  letI : Fintype K := Fintype.ofFinite K
  have hs : c^2=c := by
    simpa only [← Nat.card_eq_fintype_card, hK] using FiniteField.pow_card c
  have hp : c*(c-1)=0 := by linear_combination hs
  exact sub_eq_zero.mp ((mul_eq_zero.mp hp).resolve_left hc)

private def liftLinearMap [Finite K] (hK : Nat.card K = 2)
    (ρ : G →* Vector (K := K) (I := I) ≃ₗ[K] Vector (K := K) (I := I))
    (hB : ∀ g v w, polar (ρ g v) (ρ g w) = polar v w) (g : G) :
    Coordinates (K := K) (I := I) →ₗ[K] Coordinates (K := K) (I := I) where
  toFun := liftFun ρ g
  map_add' a b := by
    apply Prod.ext
    · change ρ g (a.1+b.1) = ρ g a.1+ρ g b.1
      exact map_add (ρ g) _ _
    · change (a.2+b.2)+q0 (a.1+b.1)+q0 (ρ g (a.1+b.1)) =
        (a.2+q0 a.1+q0 (ρ g a.1))+(b.2+q0 b.1+q0 (ρ g b.1))
      rw [map_add, q0_add, q0_add, hB]
      have hz := CharTwo.add_self_eq_zero (polar a.1 b.1)
      linear_combination hz
  map_smul' c a := by
    by_cases hc : c = 0
    · subst c
      simp [liftFun, q0]
    · have hc1 := nonzero_eq_one hK c hc
      subst c
      simp

def liftHom [Finite K] (hK : Nat.card K = 2)
    (ρ : G →* Vector (K := K) (I := I) ≃ₗ[K] Vector (K := K) (I := I))
    (hB : ∀ g v w, polar (ρ g v) (ρ g w) = polar v w) :
    G →* Coordinates (K := K) (I := I) ≃ₗ[K] Coordinates (K := K) (I := I) where
  toFun g := {
    toLinearMap := liftLinearMap hK ρ hB g
    invFun := liftFun ρ g⁻¹
    left_inv a := by
      change liftFun ρ g⁻¹ (liftFun ρ g a) = a
      rw [← liftFun_mul, inv_mul_cancel, liftFun_one]
    right_inv a := by
      change liftFun ρ g (liftFun ρ g⁻¹ a) = a
      rw [← liftFun_mul, mul_inv_cancel, liftFun_one] }
  map_one' := by
    apply LinearEquiv.ext
    intro a
    exact liftFun_one ρ a
  map_mul' g h := by
    apply LinearEquiv.ext
    intro a
    exact liftFun_mul ρ g h a

theorem liftHom_apply [Finite K] (hK : Nat.card K = 2)
    (ρ : G →* Vector (K := K) (I := I) ≃ₗ[K] Vector (K := K) (I := I))
    (hB : ∀ g v w, polar (ρ g v) (ρ g w) = polar v w)
    (g : G) (a : Coordinates (K := K) (I := I)) :
    liftHom hK ρ hB g a = (ρ g a.1,a.2+q0 a.1+q0 (ρ g a.1)) := rfl

theorem liftHom_central [Finite K] (hK : Nat.card K = 2)
    (ρ : G →* Vector (K := K) (I := I) ≃ₗ[K] Vector (K := K) (I := I))
    (hB : ∀ g v w, polar (ρ g v) (ρ g w) = polar v w) (g : G) (c : K) :
    liftHom hK ρ hB g (0,c) = (0,c) := by
  rw [liftHom_apply, map_zero]
  simp only [q0, Prod.fst_zero, Prod.snd_zero, zero_dotProduct, add_zero]

def refinementOfFunctional (φ : Module.Dual K (Coordinates (K := K) (I := I)))
    (v : Vector (K := K) (I := I)) : K := q0 v+φ (v,0)

theorem refinementOfFunctional_comp_lift [Finite K] (hK : Nat.card K = 2)
    (ρ : G →* Vector (K := K) (I := I) ≃ₗ[K] Vector (K := K) (I := I))
    (hB : ∀ g v w, polar (ρ g v) (ρ g w) = polar v w)
    (φ : Module.Dual K (Coordinates (K := K) (I := I))) (hφ : φ (0,1) = 1)
    (g : G) (v : Vector (K := K) (I := I)) :
    refinementOfFunctional (φ.comp (liftHom hK ρ hB g).toLinearMap) v =
      refinementOfFunctional φ (ρ g v) := by
  change q0 v+φ (liftHom hK ρ hB g (v,0)) = q0 (ρ g v)+φ (ρ g v,0)
  rw [liftHom_apply]
  have he : (ρ g v,(0 : K)+q0 v+q0 (ρ g v)) =
      (ρ g v,0)+(q0 v+q0 (ρ g v)) • (0,1) := by
    apply Prod.ext <;> simp
  rw [he, map_add, map_smul, hφ]
  simp only [smul_eq_mul, mul_one]
  have hz := CharTwo.add_self_eq_zero (q0 v)
  linear_combination hz

end SymmetricSubgroupAsymptotics.BinaryQuadraticLiftAction
