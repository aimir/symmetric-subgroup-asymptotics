import Mathlib.LinearAlgebra.FiniteDimensional.Basic
import Mathlib.LinearAlgebra.Dimension.Finrank
import Mathlib.LinearAlgebra.Dimension.Finite
import Mathlib.FieldTheory.Finite.Basic

/-! A binary vector space with at most four elements embeds in two
literal binary coordinates. Only its actual cardinality is used. -/
set_option autoImplicit false
noncomputable section
namespace SymmetricSubgroupAsymptotics.BinaryVectorOrderFourCoordinates
variable (V : Type) [AddCommGroup V] [Module (ZMod 2) V] [Finite V]

 theorem exists_injective (hcard : Nat.card V≤4) :
    ∃ q : V →ₗ[ZMod 2] (Fin 2 → ZMod 2),Function.Injective q := by
  letI : Module.Finite (ZMod 2) V := Module.Finite.of_finite
  let n := Module.finrank (ZMod 2) V
  have hn : n≤2 := by
    have hpow : 2^n≤2^2 := by
      have h := Module.natCard_eq_pow_finrank (K := ZMod 2) (V := V)
      simpa only [Nat.card_zmod] using h.symm.le.trans hcard
    exact (Nat.pow_le_pow_iff_right (by decide : 1<2)).mp hpow
  let e : V ≃ₗ[ZMod 2] (Fin n → ZMod 2) := LinearEquiv.ofFinrankEq _ _ (by simp [n])
  let pad : (Fin n → ZMod 2) →ₗ[ZMod 2] (Fin 2 → ZMod 2) :=
    { toFun := fun v i => if h : i.val<n then v ⟨i.val,h⟩ else 0
      map_add' := by
        intro v w
        funext i
        by_cases hi : i.val<n <;> simp [hi]
      map_smul' := by
        intro a v
        funext i
        by_cases hi : i.val<n <;> simp [hi] }
  refine ⟨pad.comp e.toLinearMap,?_⟩
  intro v w h
  apply e.injective
  funext i
  have hi : i.val<2 := lt_of_lt_of_le i.isLt hn
  have hh := congrFun h ⟨i.val,hi⟩
  change (if h : i.val<n then e v ⟨i.val,h⟩ else 0)=
    (if h : i.val<n then e w ⟨i.val,h⟩ else 0) at hh
  simpa only [dif_pos i.isLt] using hh

end SymmetricSubgroupAsymptotics.BinaryVectorOrderFourCoordinates
