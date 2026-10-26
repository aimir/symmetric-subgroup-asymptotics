import SymmetricSubgroupAsymptotics.TernarySignedCoordinateSelfDual
import SymmetricSubgroupAsymptotics.TernaryFourSignedFixedClassWeight
import SymmetricSubgroupAsymptotics.TernaryWreathAffineSemidirectEquiv

/-! The full translation extension of an ACTUAL signed subgroup onto S4
has at most 330 classes. Exact dual stabilizer weights are transported
through the coordinate pairing before cancellation; the complement is
never enlarged to a different group. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
open scoped Classical BigOperators
namespace SymmetricSubgroupAsymptotics.TernaryFourSaturatedSemidirectClassBound
open TernarySignedWreathLinearEquiv TernaryFourProperModuleSignKernel
open SignedMonomialCoordinateSelfDual SignedMonomialStabilizerClassBound
open AbelianSemidirectDualClassIdentity

local instance : Module (ZMod 3) (Additive (Multiplicative (Fin 4 → ZMod 3))) :=
  inferInstanceAs (Module (ZMod 3) (Fin 4 → ZMod 3))

theorem class_card_le_threeThirty (R : Subgroup Signed)
    (ht : Function.Surjective (topHom R)) :
    Nat.card (ConjClasses
      (Multiplicative (Fin 4 → ZMod 3) ⋊[
        (TernaryWreathAffineSemidirectEquiv.translationAction (Fin 4)).comp R.subtype] R))≤
      330 := by
  let ρ := (linearHom (Fin 4)).comp R.subtype
  let φ := (TernaryWreathAffineSemidirectEquiv.translationAction (Fin 4)).comp R.subtype
  letI : Finite (Module.Dual (ZMod 3) (Fin 4 → ZMod 3)) := Finite.of_injective
    (fun ℓ : Module.Dual (ZMod 3) (Fin 4 → ZMod 3) =>
      (ℓ : (Fin 4 → ZMod 3) → ZMod 3)) DFunLike.coe_injective
  letI : Fintype (Module.Dual (ZMod 3) (Fin 4 → ZMod 3)) := Fintype.ofFinite _
  let d : Module.Dual (ZMod 3) (Fin 4 → ZMod 3) → ℕ := fun ℓ =>
    Nat.card (dualStabilizer (N:=Multiplicative (Fin 4 → ZMod 3)) ρ ℓ)*
      Nat.card (ConjClasses (dualStabilizer (N:=Multiplicative (Fin 4 → ZMod 3)) ρ ℓ))
  have hsum : (∑ℓ,d ℓ)=(∑v : Fin 4 → ZMod 3,
      Nat.card (fixedSubgroup ρ v)*Nat.card (ConjClasses (fixedSubgroup ρ v))) := by
    calc
      _=∑v : Fin 4 → ZMod 3,d (coordinateDualEquiv v) :=
        ((coordinateDualEquiv (I:=Fin 4) (K:=ZMod 3)).toEquiv.sum_comp d).symm
      _=_ := by
        apply Finset.sum_congr rfl
        intro v _
        change Nat.card (dualStabilizer (N:=Multiplicative (Fin 4 → ZMod 3)) ρ
          (coordinateDualEquiv v))*
            Nat.card (ConjClasses (dualStabilizer (N:=Multiplicative (Fin 4 → ZMod 3)) ρ
              (coordinateDualEquiv v)))=_
        rw [TernarySignedCoordinateSelfDual.dualStabilizer_eq_fixedSubgroup R v]
  have hweighted := class_weighted_identity φ ρ
    (fun (_g : R) (_n : Multiplicative (Fin 4 → ZMod 3)) => rfl)
  have hbound : Nat.card R*Nat.card (ConjClasses
      (Multiplicative (Fin 4 → ZMod 3) ⋊[φ] R))≤Nat.card R*330 := by
    calc
      _=∑ℓ,d ℓ := hweighted
      _=∑v : Fin 4 → ZMod 3,
          Nat.card (fixedSubgroup ρ v)*Nat.card (ConjClasses (fixedSubgroup ρ v)) := hsum
      _≤330*Nat.card R := TernaryFourSignedFixedClassWeight.sum_fixed_class_weight_le R ht
      _=Nat.card R*330 := Nat.mul_comm _ _
  exact Nat.le_of_mul_le_mul_left hbound (Nat.card_pos (α:=R))

end SymmetricSubgroupAsymptotics.TernaryFourSaturatedSemidirectClassBound
