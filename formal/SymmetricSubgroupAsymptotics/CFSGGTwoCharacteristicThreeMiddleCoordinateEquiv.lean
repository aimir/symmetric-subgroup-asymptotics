import SymmetricSubgroupAsymptotics.CFSGGTwoCharacteristicThreeMiddleFiveCoordinates

/-! Coordinates on the SAME actual ordinary middle complement. The
bijection and product law are derived from its proved word range. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
namespace SymmetricSubgroupAsymptotics.CFSGGTwoCharacteristicThreeMiddleCoordinateEquiv
open CFSG.Models.Chevalley CFSGGTwoPositiveSixWord CFSGGTwoPositiveCoordinateKernels
open CFSGGTwoCharacteristicThreeMiddleFiveCoordinates
variable (K : Type) [Field K] [CharP K 3]

abbrev Middle := complement K 0

def word (v : Fin 5 → K) : Middle K := ⟨middleWord K v,middleWord_mem_complement K v⟩

theorem word_val (v : Fin 5 → K) : (word K v).val = middleWord K v := rfl

def coordinateEquiv : (Fin 5 → K) ≃ Middle K := Equiv.ofBijective (word K) (by
  constructor
  · intro v w he
    exact middleWord_injective K (congrArg Subtype.val he)
  · intro u
    obtain ⟨v,hv⟩ := (mem_complement_iff_middleWord K u.val).mp u.property
    exact ⟨v,Subtype.ext hv⟩)

def coordinates (u : Middle K) : Fin 5 → K := (coordinateEquiv K).symm u

theorem coordinates_word (v : Fin 5 → K) : coordinates K (word K v) = v :=
  (coordinateEquiv K).symm_apply_apply v

theorem word_coordinates (u : Middle K) : word K (coordinates K u) = u :=
  (coordinateEquiv K).apply_symm_apply u

theorem word_mul (v w : Fin 5 → K) :
    word K v*word K w = word K (multiplyCoordinates K v w) :=
  Subtype.ext (middleWord_mul K v w)

theorem coordinates_mul (u v : Middle K) :
    coordinates K (u*v) = multiplyCoordinates K (coordinates K u) (coordinates K v) := by
  obtain ⟨a,rfl⟩ := (coordinateEquiv K).surjective u
  obtain ⟨b,rfl⟩ := (coordinateEquiv K).surjective v
  change coordinates K (word K a*word K b) =
    multiplyCoordinates K (coordinates K (word K a)) (coordinates K (word K b))
  rw [word_mul,coordinates_word,coordinates_word,coordinates_word]

theorem coordinates_one : coordinates K (1 : Middle K) = 0 := by
  have hz : extendCoordinates K (0 : Fin 5 → K) = 0 := by
    funext i
    fin_cases i <;> rfl
  have hw : word K (0 : Fin 5 → K) = 1 := by
    apply Subtype.ext
    change modelWord K (extendCoordinates K 0) = 1
    rw [hz,CFSGGTwoPositiveWordSubgroup.modelWord_zero]
  rw [←hw,coordinates_word]

theorem middle_card [Finite K] : Nat.card (Middle K) = Nat.card K^5 := by
  rw [←Nat.card_congr (coordinateEquiv K),Nat.card_fun,Nat.card_fin]

end SymmetricSubgroupAsymptotics.CFSGGTwoCharacteristicThreeMiddleCoordinateEquiv
