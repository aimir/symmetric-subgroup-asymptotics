import SymmetricSubgroupAsymptotics.CFSGSymplecticFullGroup
import SymmetricSubgroupAsymptotics.CFSGSymplecticNaturalBilinearClassGeometry
import SymmetricSubgroupAsymptotics.BilinearFixedFreeConjugacyFusion

/-! The original elementary matrices are the literal full preserver
group of their natural bilinear form. Fixed-free general-linear fusion
therefore holds in the SAME original elementary group, including in
characteristic two. No matrix-group recognition is assumed. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
open scoped Matrix

namespace SymmetricSubgroupAsymptotics.CFSGSymplecticPolarEquivalence
open CFSGSymplecticSerreMatrices CFSGSymplecticStabilizerCoordinates
open CFSGSymplecticPointAffineHom CFSGSymplecticNaturalBilinearClassGeometry
open QuadraticIsometryPolarStabilizer
variable (K : Type) [Field K]

def matrixLinearEquiv (r : ℕ) : (Mat K r)ˣ ≃* ((Index r → K) ≃ₗ[K] (Index r → K)) :=
  Matrix.GeneralLinearGroup.toLin.trans
    (LinearMap.GeneralLinearGroup.generalLinearEquiv K (Index r → K))

def polarHom (r : ℕ) : elementaryRootGroup K r →*
    polarPreservers (naturalPairing K r) where
  toFun g := ⟨naturalLinearHom K r g, fun x y =>
    CFSGSymplecticTransvectionGeometry.elementary_preserves_pairing r g x y⟩
  map_one' := Subtype.ext (map_one (naturalLinearHom K r))
  map_mul' g h := Subtype.ext (map_mul (naturalLinearHom K r) g h)

theorem polarHom_injective (r : ℕ) : Function.Injective (polarHom K r) := by
  intro g h he
  exact MatrixUnitBilinearIsometryOrderBound.naturalLinearHom_injective K (Index r)
    (elementaryRootGroup K r) (congrArg Subtype.val he)

theorem polarHom_surjective (r : ℕ) : Function.Surjective (polarHom K r) := by
  intro a
  let u := (matrixLinearEquiv K r).symm a.val
  have he : matrixLinearEquiv K r u = a.val := (matrixLinearEquiv K r).apply_symm_apply _
  have hu : PreservesPairing r (u : Mat K r) := by
    intro x y
    change naturalPairing K r (matrixLinearEquiv K r u x)
      (matrixLinearEquiv K r u y) = naturalPairing K r x y
    rw [he]
    exact a.property x y
  refine ⟨⟨u, all_formPreserving_elementary K r u hu⟩, ?_⟩
  exact Subtype.ext he

def elementaryPolarEquiv (r : ℕ) : elementaryRootGroup K r ≃*
    polarPreservers (naturalPairing K r) :=
  MulEquiv.ofBijective (polarHom K r) ⟨polarHom_injective K r, polarHom_surjective K r⟩

theorem naturalPairing_isSymm [CharP K 2] (r : ℕ) : (naturalPairing K r).IsSymm := by
  constructor
  intro x y
  exact (CFSGSymplecticTransvectionGeometry.pairing_swap r x y).trans (CharTwo.neg_eq _)

theorem isConj_of_fixedFree [Finite K] [CharP K 2] (r : ℕ) (hr : 0 < r)
    (g h : elementaryRootGroup K r)
    (hfixed : ∀ x : Index r → K, naturalLinearHom K r g x = x → x = 0)
    (hconj : IsConj (naturalLinearHom K r g) (naturalLinearHom K r h)) : IsConj g h := by
  letI : Nonempty (Index r) := ⟨Sum.inl ⟨0,hr⟩⟩
  let e := elementaryPolarEquiv K r
  have hc : IsConj (e g) (e h) :=
    BilinearFixedFreeConjugacyFusion.isConj_of_fixedFree (naturalPairing K r)
      (naturalPairing_nondegenerate K r) (naturalPairing_isSymm K r)
      (e g) (e h) hfixed hconj
  have hh := e.symm.toMonoidHom.map_isConj hc
  change IsConj (e.symm (e g)) (e.symm (e h)) at hh
  simpa only [e.symm_apply_apply] using hh

end SymmetricSubgroupAsymptotics.CFSGSymplecticPolarEquivalence
