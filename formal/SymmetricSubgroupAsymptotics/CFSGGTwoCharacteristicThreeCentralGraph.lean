import SymmetricSubgroupAsymptotics.CFSGHeisenbergFiniteFieldIsotropy
import Mathlib.Data.Fin.VecNotation

/-! Arbitrary additive central intersections over the field of three
elements. Missing the highest parameter excludes the whole vertical line;
an actual sign flip then kills the graph without larger-field linearity. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
namespace SymmetricSubgroupAsymptotics.CFSGGTwoCharacteristicThreeCentralGraph
variable (K : Type) [Field K] [Finite K] [CharP K 3]

def vertical : K →+ (Fin 3 → K) where
  toFun z := ![0,0,z]
  map_zero' := by funext i; fin_cases i <;> rfl
  map_add' z w := by funext i; fin_cases i <;> simp

def flip (v : Fin 3 → K) : Fin 3 → K := ![-v 0,-v 1,v 2]

theorem vertical_preimage_eq_bot (hcard : Nat.card K = 3)
    (C : AddSubgroup (Fin 3 → K)) (h1 : vertical K 1 ∉ C) :
    C.comap (vertical K) = ⊥ := by
  letI : Fact (Nat.Prime 3) := ⟨by decide⟩
  have hD : C.comap (vertical K) ≠ ⊤ := by
    intro he
    apply h1
    change (1 : K) ∈ C.comap (vertical K)
    rw [he]
    trivial
  have hc := CFSGHeisenbergFiniteFieldIsotropy.proper_additive_card_mul_prime_le
    (K := K) 3 (C.comap (vertical K)) hD
  rw [hcard] at hc
  exact (C.comap (vertical K)).eq_bot_of_card_le (by omega)

theorem third_eq_zero_of_flip (hcard : Nat.card K = 3)
    (C : AddSubgroup (Fin 3 → K)) (h1 : vertical K 1 ∉ C)
    (hflip : ∀ v ∈ C, flip K v ∈ C) : ∀ v ∈ C, v 2 = 0 := by
  intro v hv
  have hs := C.add_mem hv (hflip v hv)
  have he : v+flip K v = vertical K (v 2+v 2) := by
    funext i
    fin_cases i <;> simp [flip,vertical]
  rw [he] at hs
  have hD : v 2+v 2 ∈ C.comap (vertical K) := hs
  rw [vertical_preimage_eq_bot K hcard C h1] at hD
  have hz : v 2+v 2 = 0 := AddSubgroup.mem_bot.mp hD
  have htwo : (2 : K) ≠ 0 :=
    CharP.cast_ne_zero_of_ne_of_prime (R := K) (p := 3) (by decide : Nat.Prime 2) (by decide)
  exact (mul_eq_zero.mp (show (2 : K)*v 2 = 0 by simpa only [two_mul] using hz)).resolve_left htwo

theorem eq_horizontal_of_flip_card (hcard : Nat.card K = 3)
    (C : AddSubgroup (Fin 3 → K)) (h1 : vertical K 1 ∉ C)
    (hflip : ∀ v ∈ C, flip K v ∈ C) (hC : Nat.card C = Nat.card K^2) :
    C = (LinearMap.proj (2 : Fin 3) : (Fin 3 → K) →ₗ[K] K).toAddMonoidHom.ker := by
  let H := (LinearMap.proj (2 : Fin 3) : (Fin 3 → K) →ₗ[K] K).toAddMonoidHom.ker
  have hle : C ≤ H := third_eq_zero_of_flip K hcard C h1 hflip
  let e : H ≃ (Fin 2 → K) :=
    { toFun := fun v => ![v.val 0,v.val 1]
      invFun := fun v => ⟨![v 0,v 1,0],rfl⟩
      left_inv := by
        intro v
        apply Subtype.ext
        funext i
        fin_cases i
        · rfl
        · rfl
        · exact v.property.symm
      right_inv := by intro v; funext i; fin_cases i <;> rfl }
  have hH : Nat.card H = Nat.card K^2 := by
    rw [Nat.card_congr e,Nat.card_fun,Nat.card_fin]
  exact AddSubgroup.eq_of_le_of_card_ge hle (by rw [hH,hC])

end SymmetricSubgroupAsymptotics.CFSGGTwoCharacteristicThreeCentralGraph
