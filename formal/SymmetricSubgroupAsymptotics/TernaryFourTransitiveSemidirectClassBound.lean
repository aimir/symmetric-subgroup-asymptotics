import SymmetricSubgroupAsymptotics.TernarySignedCoordinateSelfDual
import SymmetricSubgroupAsymptotics.TernaryFourBinaryTopFixedClassWeight
import SymmetricSubgroupAsymptotics.TernaryWreathAffineSemidirectEquiv

/-! Exact signed-coordinate class weights hold for every actual
projected subgroup. The checked binary-small-top weight then gives360
classes in the corresponding full translation extension. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
open scoped Classical BigOperators
namespace SymmetricSubgroupAsymptotics.TernaryFourTransitiveSemidirectClassBound
open TernarySignedWreathLinearEquiv TernaryFourProperModuleSignKernel
open SignedMonomialCoordinateSelfDual SignedMonomialStabilizerClassBound
open TernaryWreathAffineSemidirectEquiv

local instance : Module (ZMod 3) (Additive (Multiplicative (Fin 4 → ZMod 3))) :=
  inferInstanceAs (Module (ZMod 3) (Fin 4 → ZMod 3))

theorem class_weighted_identity (R : Subgroup Signed) :
    Nat.card R*Nat.card (ConjClasses
      (Multiplicative (Fin 4 → ZMod 3) ⋊[(translationAction (Fin 4)).comp R.subtype] R))=
    ∑v : Fin 4 → ZMod 3,
      Nat.card (fixedSubgroup ((linearHom (Fin 4)).comp R.subtype) v)*
        Nat.card (ConjClasses (fixedSubgroup ((linearHom (Fin 4)).comp R.subtype) v)) := by
  let ρ := (linearHom (Fin 4)).comp R.subtype
  let φ := (translationAction (Fin 4)).comp R.subtype
  letI : Finite (Module.Dual (ZMod 3) (Fin 4 → ZMod 3)) := Finite.of_injective
    (fun ℓ : Module.Dual (ZMod 3) (Fin 4 → ZMod 3) =>
      (ℓ : (Fin 4 → ZMod 3) → ZMod 3)) DFunLike.coe_injective
  letI : Fintype (Module.Dual (ZMod 3) (Fin 4 → ZMod 3)) := Fintype.ofFinite _
  let d : Module.Dual (ZMod 3) (Fin 4 → ZMod 3) → ℕ := fun ℓ =>
    Nat.card (AbelianSemidirectDualClassIdentity.dualStabilizer
      (N:=Multiplicative (Fin 4 → ZMod 3)) ρ ℓ)*
      Nat.card (ConjClasses (AbelianSemidirectDualClassIdentity.dualStabilizer
        (N:=Multiplicative (Fin 4 → ZMod 3)) ρ ℓ))
  calc
    _=∑ℓ,d ℓ := AbelianSemidirectDualClassIdentity.class_weighted_identity φ ρ
      (fun (_g : R) (_n : Multiplicative (Fin 4 → ZMod 3)) => rfl)
    _=∑v : Fin 4 → ZMod 3,d (coordinateDualEquiv v) :=
      ((coordinateDualEquiv (I:=Fin 4) (K:=ZMod 3)).toEquiv.sum_comp d).symm
    _=_ := by
      apply Finset.sum_congr rfl
      intro v _
      change Nat.card (AbelianSemidirectDualClassIdentity.dualStabilizer
        (N:=Multiplicative (Fin 4 → ZMod 3)) ρ (coordinateDualEquiv v))*
          Nat.card (ConjClasses (AbelianSemidirectDualClassIdentity.dualStabilizer
            (N:=Multiplicative (Fin 4 → ZMod 3)) ρ (coordinateDualEquiv v)))=_
      rw [TernarySignedCoordinateSelfDual.dualStabilizer_eq_fixedSubgroup R v]

theorem class_card_le_threeSixty (R : Subgroup Signed)
    (htrans : ∀ i j : Fin 4,∃g : R,topHom R g i=j)
    (hQ : Nat.card (topHom R).range≤8) :
    Nat.card (ConjClasses
      (Multiplicative (Fin 4 → ZMod 3) ⋊[(translationAction (Fin 4)).comp R.subtype] R))≤360 := by
  have hbound : Nat.card R*Nat.card (ConjClasses
      (Multiplicative (Fin 4 → ZMod 3) ⋊[(translationAction (Fin 4)).comp R.subtype] R))≤
      Nat.card R*360 := by
    rw [class_weighted_identity]
    exact (TernaryFourBinaryTopFixedClassWeight.sum_fixed_class_weight_le R htrans hQ).trans_eq
      (Nat.mul_comm _ _)
  exact Nat.le_of_mul_le_mul_left hbound (Nat.card_pos (α:=R))

end SymmetricSubgroupAsymptotics.TernaryFourTransitiveSemidirectClassBound
