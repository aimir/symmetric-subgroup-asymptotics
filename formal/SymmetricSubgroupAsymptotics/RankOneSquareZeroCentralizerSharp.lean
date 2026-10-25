import SymmetricSubgroupAsymptotics.RankOneSquareZeroCentralizer
import SymmetricSubgroupAsymptotics.ThreeDimensionalFixedVectorLinearMaps

/-! The actual kernel restriction of a rank-one square-zero centralizer
fixes its image vector. In dimension four over the binary field its two
remaining kernel images have capacities six and four, rather than six
independent choices twice. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
open scoped Classical
namespace SymmetricSubgroupAsymptotics.RankOneSquareZeroCentralizerSharp

variable {K V : Type*} [Field K] [AddCommGroup V] [Module K V] [Finite V]

theorem card_le (hK : Nat.card K = 2) (N : V →ₗ[K] V)
    (hN : ∀ x : V, N (N x) = 0) (hr : Module.finrank K N.range = 1)
    (hk : Module.finrank K N.ker = 3) (e : V ≃ₗ[K] V)
    (he : ∀ x : V, e x = x + N x) :
    Nat.card {a : V ≃ₗ[K] V // Commute e a} ≤
      Nat.card N.ker * ((Nat.card N.ker - Nat.card K) *
        (Nat.card N.ker - Nat.card K ^ 2)) := by
  letI : FiniteDimensional K V := Module.Finite.of_finite
  obtain ⟨v, hv⟩ : ∃ v : V, N v ≠ 0 := by
    by_contra hn
    have hall : ∀ v : V, N v = 0 := by simpa only [not_exists, not_not] using hn
    have hz : N = 0 := by ext v; exact hall v
    have hdim : Module.finrank K N.range = 0 := by
      rw [LinearMap.range_eq_bot.mpr hz]
      exact finrank_bot K V
    omega
  let W := N.ker
  let w : W := ⟨N v, hN v⟩
  have hw : w ≠ 0 := fun h => hv (congrArg Subtype.val h)
  let C := {a : V ≃ₗ[K] V // Commute e a}
  have hcomm (a : C) (x : V) : N (a.val x) = a.val (N x) := by
    have hh := congrArg (fun f : V ≃ₗ[K] V => f x) a.property
    change e (a.val x) = a.val (e x) at hh
    simp only [he, map_add] at hh
    exact add_left_cancel hh
  have hfix (a : C) : a.val (N v) = N v :=
    RankOneSquareZeroCentralizer.commuting_fixes_image hK N hr v hv a.val (hcomm a)
  let R (a : C) : W →ₗ[K] W :=
    (a.val.toLinearMap.comp W.subtype).codRestrict W (by
      intro x
      change N (a.val (x : V)) = 0
      rw [hcomm a, x.property, map_zero])
  have hRinj (a : C) : Function.Injective (R a) := by
    intro x y h
    apply Subtype.ext
    exact a.val.injective (congrArg (fun z : W => (z : V)) h)
  have hRfix (a : C) : R a w = w := by
    apply Subtype.ext
    exact hfix a
  let E := {f : W →ₗ[K] W // Function.Injective f ∧ f w = w}
  letI : Finite W := inferInstanceAs (Finite N.ker)
  letI : Finite E := Finite.of_injective (fun f : E => (f.val : W → W)) (by
    intro f g h
    apply Subtype.ext
    exact DFunLike.coe_injective h)
  let chart : C → {x : V // N x = N v} × E := fun a =>
    (⟨a.val v, (hcomm a v).trans (hfix a)⟩, ⟨R a, hRinj a, hRfix a⟩)
  have hchart : Function.Injective chart := by
    intro a a' haa
    have hval : a.val v = a'.val v :=
      congrArg (fun z : {x : V // N x = N v} × E => z.1.val) haa
    have hker (x : W) : a.val (x : V) = a'.val (x : V) :=
      congrArg (fun z : {x : V // N x = N v} × E => (z.2.val x : V)) haa
    apply Subtype.ext
    apply LinearEquiv.ext
    intro x
    obtain ⟨c, hc⟩ := RankOneSquareZeroCentralizer.range_scalar N hr v hv (N x) ⟨x, rfl⟩
    let y : W := ⟨x - c • v, by
      change N (x - c • v) = 0
      rw [map_sub, map_smul, hc, sub_self]⟩
    have hh := hker y
    change a.val (x - c • v) = a'.val (x - c • v) at hh
    rw [map_sub, map_sub, map_smul, map_smul, hval] at hh
    simpa only [sub_add_cancel] using congrArg (fun z : V => z + c • a'.val v) hh
  have hE : Nat.card E ≤ (Nat.card W - Nat.card K) * (Nat.card W - Nat.card K ^ 2) :=
    ThreeDimensionalFixedVectorLinearMaps.card_le hk w hw
  calc
    Nat.card C ≤ Nat.card ({x : V // N x = N v} × E) :=
      Nat.card_le_card_of_injective chart hchart
    _ = Nat.card N.ker * Nat.card E := by
      rw [Nat.card_prod, Nat.card_congr (RankOneSquareZeroCentralizer.fiberEquivKer N v)]
    _ ≤ Nat.card N.ker * ((Nat.card N.ker - Nat.card K) *
        (Nat.card N.ker - Nat.card K ^ 2)) := Nat.mul_le_mul_left _ hE

end SymmetricSubgroupAsymptotics.RankOneSquareZeroCentralizerSharp
