import SymmetricSubgroupAsymptotics.C4CoordinateSurjectiveQuotient
import SymmetricSubgroupAsymptotics.FiniteTopKernelHomLiftCount

/-! Homomorphisms into an actual subgroup of C4^c use exactly c full
C4 characters. Quotient images keep the same bound without an elementary
or split-kernel assumption. -/
set_option autoImplicit false
noncomputable section
namespace SymmetricSubgroupAsymptotics.C4CoordinateHomCount
abbrev C4 := Multiplicative (ZMod 4)
variable {K F : Type} [Group K] [Group F] [Finite K] [Finite F] {c : ℕ}

 theorem card_le (e : K →* (Fin c → C4)) (he : Function.Injective e) :
    Nat.card (F →* K) ≤ Nat.card (F →* C4)^c := by
  letI : Finite (F →* C4) := Finite.of_injective
    (fun f : F →* C4 => (f : F → C4)) DFunLike.coe_injective
  let enc : (F →* K) → (Fin c → (F →* C4)) :=
    fun f i => (Pi.evalMonoidHom (fun _ : Fin c => C4) i).comp (e.comp f)
  have hi : Function.Injective enc := by
    intro f g h
    ext x
    apply he
    funext i
    exact DFunLike.congr_fun (congrFun h i) x
  exact (Nat.card_le_card_of_injective enc hi).trans_eq (by simp [Nat.card_fun])

 theorem quotient_card_le {A : Type} [Group A] [Finite A]
    (e : K →* (Fin c → C4)) (he : Function.Injective e)
    (q : K →* A) (hq : Function.Surjective q) :
    Nat.card (F →* A) ≤ Nat.card (F →* C4)^c := by
  obtain ⟨r,hr,j,hj⟩ := C4CoordinateSurjectiveQuotient.exists_embedding e he q hq
  letI : Finite (F →* C4) := Finite.of_injective
    (fun f : F →* C4 => (f : F → C4)) DFunLike.coe_injective
  have hp : 1 ≤ Nat.card (F →* C4) := Nat.card_pos
  exact (card_le j hj).trans (Nat.pow_le_pow_right hp hr)

end SymmetricSubgroupAsymptotics.C4CoordinateHomCount
