import SymmetricSubgroupAsymptotics.CFSGFiniteCommutingParameterHom
import SymmetricSubgroupAsymptotics.CFSGAdditiveParameterConjugation

/-! A literal signed permutation of additive coordinates transports a
commuting root product.  The proof tests the actual one-coordinate
parameters and uses their universal property; no invariant total order
or field-linear fixed-subgroup assumption is needed. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
namespace SymmetricSubgroupAsymptotics.CFSGCommutingParameterTwist
open CFSGFiniteCommutingParameterHom
variable {K G : Type*} [CommRing K] [Group G] {m : ℕ}

def coefficientMap (sigma : K ≃+* K) (p : Equiv.Perm (Fin m)) (w : Fin m → ℤ) :
    (Fin m → K) →+ (Fin m → K) where
  toFun v i := (w (p.symm i) : K) * sigma (v (p.symm i))
  map_zero' := by ext i; simp only [Pi.zero_apply, map_zero, mul_zero]
  map_add' a b := by ext i; simp only [Pi.add_apply, map_add, mul_add]

theorem coefficientMap_single (sigma : K ≃+* K) (p : Equiv.Perm (Fin m))
    (w : Fin m → ℤ) (i : Fin m) (a : K) :
    coefficientMap sigma p w (Pi.single i a) =
      Pi.single (p i) ((w i : K) * sigma a) := by
  ext j
  change (w (p.symm j) : K) * sigma ((Pi.single i a : Fin m → K) (p.symm j)) =
    (Pi.single (p i) ((w i : K) * sigma a) : Fin m → K) j
  by_cases hj : j = p i
  · subst j
    rw [p.symm_apply_apply, Pi.single_eq_same, Pi.single_eq_same]
  · have hji : p.symm j ≠ i := by
      intro he
      apply hj
      simpa only [p.apply_symm_apply] using congrArg p he
    rw [Pi.single_eq_of_ne hji, Pi.single_eq_of_ne hj, map_zero, mul_zero]

theorem map_parameterHom (sigma : K ≃+* K) (p : Equiv.Perm (Fin m))
    (w : Fin m → ℤ) (f : Fin m → Multiplicative K →* G)
    (hcomm : Pairwise (fun i j => ∀ a b, Commute (f i a) (f j b)))
    (phi : G →* G)
    (h : ∀ i a, phi (f i (Multiplicative.ofAdd a)) =
      f (p i) (Multiplicative.ofAdd ((w i : K) * sigma a))) (v : Fin m → K) :
    phi (parameterHom f hcomm (Multiplicative.ofAdd v)) =
      parameterHom f hcomm (Multiplicative.ofAdd (coefficientMap sigma p w v)) := by
  let lhs := phi.comp (parameterHom f hcomm)
  let rhs := (parameterHom f hcomm).comp (coefficientMap sigma p w).toMultiplicative
  have he : lhs = rhs := by
    apply CFSGAdditiveParameterConjugation.hom_ext
    intro i a
    change phi (parameterHom f hcomm (Multiplicative.ofAdd (Pi.single i a))) =
      parameterHom f hcomm
        (Multiplicative.ofAdd (coefficientMap sigma p w (Pi.single i a)))
    rw [parameterHom_single, coefficientMap_single, parameterHom_single]
    exact h i a
  exact DFunLike.congr_fun he (Multiplicative.ofAdd v)

end SymmetricSubgroupAsymptotics.CFSGCommutingParameterTwist
