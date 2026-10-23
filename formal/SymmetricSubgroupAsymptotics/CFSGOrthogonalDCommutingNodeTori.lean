import SymmetricSubgroupAsymptotics.CFSGOrthogonalDForkNodeTori
import SymmetricSubgroupAsymptotics.CFSGCommutingPairedWord

/-! Paired node tori from paired root lines. This is generic field and
subgroup algebra: no original Serre source or extension-field carrier
is unfolded in the four-word rearrangement. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
namespace SymmetricSubgroupAsymptotics.CFSGOrthogonalDCommutingNodeTori
open CFSGOrthogonalDSerreMatrices CFSGOrthogonalDBinaryElements
open CFSGOrthogonalDForkNodeTori

theorem nodeTorus_pair_mem (K : Type) [Field K] (n : ℕ)
    (H : Subgroup (elementaryRootGroup K (n + 2)))
    (i j : Fin (n + 2)) (σ : K →+* K) (c : Kˣ)
    (hc : ∀ (e f : Bool) (a b : K),
      Commute (rootElement K (n + 2) e i a) (rootElement K (n + 2) f j b))
    (hp : ∀ (e : Bool) (a : K),
      rootElement K (n + 2) e i a * rootElement K (n + 2) e j (σ a) ∈ H) :
    nodeTorus K n i c * nodeTorus K n j (Units.map σ.toMonoidHom c) ∈ H := by
  let e : Fin 4 → Bool := ![false, true, false, true]
  let t : Fin 4 → K := ![(c : K) - 1, 1, (c : K)⁻¹ - 1, -(c : K)]
  let a : Fin 4 → elementaryRootGroup K (n + 2) := fun k =>
    rootElement K (n + 2) (e k) i (t k)
  let b : Fin 4 → elementaryRootGroup K (n + 2) := fun k =>
    rootElement K (n + 2) (e k) j (σ (t k))
  have hcomm (k l : Fin 4) : Commute (a k) (b l) := hc (e k) (e l) (t k) (σ (t l))
  have hm (k : Fin 4) : a k * b k ∈ H := hp (e k) (t k)
  have hw : (a 0 * b 0) * (a 1 * b 1) * (a 2 * b 2) * (a 3 * b 3) ∈ H :=
    H.mul_mem (H.mul_mem (H.mul_mem (hm 0) (hm 1)) (hm 2)) (hm 3)
  rw [CFSGCommutingPairedWord.four_pairs a b hcomm] at hw
  have ha : a 0 * a 1 * a 2 * a 3 = nodeTorus K n i c := rfl
  have hb : b 0 * b 1 * b 2 * b 3 = nodeTorus K n j (Units.map σ.toMonoidHom c) := by
    change rootElement K (n + 2) false j (σ ((c : K) - 1)) *
      rootElement K (n + 2) true j (σ 1) *
      rootElement K (n + 2) false j (σ ((c : K)⁻¹ - 1)) *
      rootElement K (n + 2) true j (σ (-(c : K))) = _
    simp only [map_sub, map_one, map_inv₀, map_neg]
    rfl
  simpa only [ha, hb] using hw

end SymmetricSubgroupAsymptotics.CFSGOrthogonalDCommutingNodeTori
