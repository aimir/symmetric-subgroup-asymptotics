import SymmetricSubgroupAsymptotics.CFSGGTwoCharacteristicThreeMiddleCoordinateEquiv
import SymmetricSubgroupAsymptotics.CFSGGTwoCharacteristicThreeMiddleCentralWords
import Mathlib.GroupTheory.Subgroup.Center

/-! The whole three-coordinate centre of the literal ordinary middle
complement, including at q=3. Two actual endpoint test elements give the
reverse centre containment; this is not a guessed Heisenberg recognition. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
namespace SymmetricSubgroupAsymptotics.CFSGGTwoCharacteristicThreeMiddleCentralCoordinates
open CFSGGTwoCharacteristicThreeMiddleCoordinateEquiv
open CFSGGTwoCharacteristicThreeMiddleFiveCoordinates
open CFSGGTwoCharacteristicThreeMiddleCentralWords
variable (K : Type) [Field K] [CharP K 3]

def endpointHom : Middle K →* Multiplicative (Fin 2 → K) where
  toFun u := Multiplicative.ofAdd ![coordinates K u 0,coordinates K u 3]
  map_one' := by
    rw [coordinates_one]
    apply congrArg Multiplicative.ofAdd
    funext i
    fin_cases i <;> rfl
  map_mul' u v := by
    change Multiplicative.ofAdd ![coordinates K (u*v) 0,coordinates K (u*v) 3] = _
    rw [coordinates_mul]
    apply congrArg Multiplicative.ofAdd
    funext i
    fin_cases i <;> rfl

theorem endpointHom_word (v : Fin 5 → K) :
    endpointHom K (word K v) = Multiplicative.ofAdd ![v 0,v 3] := by
  change Multiplicative.ofAdd ![coordinates K (word K v) 0,coordinates K (word K v) 3] = _
  rw [coordinates_word]

theorem endpointHom_surjective : Function.Surjective (endpointHom K) := by
  intro v
  refine ⟨word K ![v.toAdd 0,0,0,v.toAdd 1,0],?_⟩
  rw [endpointHom_word]
  apply congrArg Multiplicative.ofAdd
  funext i
  fin_cases i <;> rfl

def centralHom : Multiplicative (Fin 3 → K) →* Middle K where
  toFun a := word K ![0,a.toAdd 0,a.toAdd 1,0,a.toAdd 2]
  map_one' := by
    apply (coordinateEquiv K).symm.injective
    change coordinates K (word K ![0,0,0,0,0]) = coordinates K 1
    rw [coordinates_word,coordinates_one]
    funext i
    fin_cases i <;> rfl
  map_mul' a b := by
    apply (coordinateEquiv K).symm.injective
    change coordinates K (word K ![0,(a*b).toAdd 0,(a*b).toAdd 1,0,(a*b).toAdd 2]) =
      coordinates K (word K ![0,a.toAdd 0,a.toAdd 1,0,a.toAdd 2]*
        word K ![0,b.toAdd 0,b.toAdd 1,0,b.toAdd 2])
    rw [word_mul,coordinates_word,coordinates_word]
    funext i
    fin_cases i <;> simp [multiplyCoordinates]

theorem centralHom_val (a : Multiplicative (Fin 3 → K)) :
    (centralHom K a).val = centralWord K a.toAdd := by
  rw [centralWord_modelWord]
  rfl

theorem centralHom_injective : Function.Injective (centralHom K) := by
  intro a b he
  have h := congrArg Subtype.val he
  rw [centralHom_val,centralHom_val] at h
  exact centralWord_injective K h

theorem centralHom_range : (centralHom K).range = (endpointHom K).ker := by
  ext u
  constructor
  · rintro ⟨a,rfl⟩
    change endpointHom K (word K ![0,a.toAdd 0,a.toAdd 1,0,a.toAdd 2]) = 1
    rw [endpointHom_word]
    apply congrArg Multiplicative.ofAdd
    funext i
    fin_cases i <;> rfl
  · intro hu
    have hb : coordinates K u 0 = 0 := congrArg (fun a : Multiplicative (Fin 2 → K) => a.toAdd 0) hu
    have he : coordinates K u 3 = 0 := congrArg (fun a : Multiplicative (Fin 2 → K) => a.toAdd 1) hu
    refine ⟨Multiplicative.ofAdd ![coordinates K u 1,coordinates K u 2,coordinates K u 4],?_⟩
    apply (coordinateEquiv K).symm.injective
    change coordinates K (word K ![0,coordinates K u 1,coordinates K u 2,0,coordinates K u 4]) = _
    rw [coordinates_word]
    funext i
    fin_cases i
    · exact hb.symm
    · rfl
    · rfl
    · exact he.symm
    · rfl

theorem center_eq_endpointKer : Subgroup.center (Middle K) = (endpointHom K).ker := by
  apply le_antisymm
  · intro u hu
    have htest (v : Fin 5 → K) :
        multiplyCoordinates K v (coordinates K u) = multiplyCoordinates K (coordinates K u) v := by
      have h := congrArg (coordinates K) (Subgroup.mem_center_iff.mp hu (word K v))
      simpa only [coordinates_mul,coordinates_word] using h
    have hb : coordinates K u 0 = 0 := by
      have h := congrFun (htest ![0,0,0,1,0]) 4
      change 0+coordinates K u 4+coordinates K u 0*1 = coordinates K u 4+0+0*coordinates K u 3 at h
      simp only [zero_add,add_zero,mul_one,zero_mul] at h
      exact add_left_cancel (h.trans (add_zero _).symm)
    have he : coordinates K u 3 = 0 := by
      have h := congrFun (htest ![1,0,0,0,0]) 4
      change 0+coordinates K u 4+coordinates K u 0*0 = coordinates K u 4+0+1*coordinates K u 3 at h
      simp only [zero_add,add_zero,mul_zero,one_mul] at h
      exact add_left_cancel (h.symm.trans (add_zero _).symm)
    change Multiplicative.ofAdd ![coordinates K u 0,coordinates K u 3] = 1
    rw [hb,he]
    apply congrArg Multiplicative.ofAdd
    funext i
    fin_cases i <;> rfl
  · intro u hu
    have hb : coordinates K u 0 = 0 := congrArg (fun a : Multiplicative (Fin 2 → K) => a.toAdd 0) hu
    have he : coordinates K u 3 = 0 := congrArg (fun a : Multiplicative (Fin 2 → K) => a.toAdd 1) hu
    apply Subgroup.mem_center_iff.mpr
    intro v
    apply (coordinateEquiv K).symm.injective
    change coordinates K (v*u) = coordinates K (u*v)
    rw [coordinates_mul,coordinates_mul]
    funext i
    fin_cases i <;> simp [multiplyCoordinates,hb,he,add_comm]

theorem center_card [Finite K] : Nat.card (Subgroup.center (Middle K)) = Nat.card K^3 := by
  let e : Multiplicative (Fin 3 → K) ≃* Subgroup.center (Middle K) :=
    (MonoidHom.ofInjective (centralHom_injective K)).trans
      (MulEquiv.subgroupCongr ((centralHom_range K).trans (center_eq_endpointKer K).symm))
  rw [←Nat.card_congr e.toEquiv]
  change Nat.card (Fin 3 → K) = _
  rw [Nat.card_fun,Nat.card_fin]

end SymmetricSubgroupAsymptotics.CFSGGTwoCharacteristicThreeMiddleCentralCoordinates
