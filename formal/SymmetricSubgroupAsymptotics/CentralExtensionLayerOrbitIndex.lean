import SymmetricSubgroupAsymptotics.CentralExtensionSemidirectStabilizer
import SymmetricSubgroupAsymptotics.SubgroupInvariantSetOrbitIndex
import Mathlib.Algebra.Group.Action.End
import Mathlib.Data.Fintype.Card

/-! Orbit bounds on the characteristic layers of the actual radical
intersection. The projected subgroup and its index are the same in
both bounds and in the exact cardinal identity. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section

namespace SymmetricSubgroupAsymptotics.CentralExtensionLayerOrbitIndex

variable {T X : Type*} [Group T] [Group X]

def layerOrbit (ψ : T →* MulAut X) (v : X) : Set X :=
  {w | ∃ t : T, ψ t v = w}

theorem nonone_card [Finite X] :
    Nat.card {v : X // v ≠ 1} = Nat.card X - 1 := by
  classical
  letI : Fintype X := Fintype.ofFinite X
  simpa only [Nat.card_eq_fintype_card, Fintype.card_subtype_eq] using
    (Fintype.card_subtype_compl (fun v : X => v = 1))

/-- An invariant subgroup is counted without its identity. No transitivity
or scalar-orbit size is assumed here. -/
theorem orbit_card_le [Finite T] [Finite X]
    (ψ : T →* MulAut X) (L : Subgroup T) (W : Subgroup X)
    (hW : ∀ t ∈ L, ∀ v ∈ W, ψ t v ∈ W)
    (v : X) (hvW : v ∈ W) (hv : v ≠ 1) :
    Nat.card (layerOrbit ψ v) ≤ (Nat.card W - 1) * L.index := by
  letI : MulAction T X := MulAction.compHom X ψ
  let f : MulAction.orbit L v → {w : W // w ≠ 1} := fun w =>
    ⟨⟨w.val, by
      obtain ⟨t, ht⟩ := w.property
      rw [← ht]
      exact hW t.val t.property v hvW⟩, by
      intro hw
      obtain ⟨t, ht⟩ := w.property
      have hw' : w.val = 1 := congrArg (fun z : W => (z : X)) hw
      apply hv
      apply (ψ t.val).injective
      change ψ t.val v = w.val at ht
      exact (ht.trans hw').trans (map_one (ψ t.val)).symm⟩
  have hf : Function.Injective f := by
    intro w z he
    exact Subtype.ext (congrArg (fun x : {w : W // w ≠ 1} => ((x.val : W) : X)) he)
  have hcard : Nat.card (MulAction.orbit L v) ≤ Nat.card W - 1 := by
    calc
      _ ≤ Nat.card {w : W // w ≠ 1} := Nat.card_le_card_of_injective f hf
      _ = _ := nonone_card
  change Nat.card (MulAction.orbit T v) ≤ _
  exact (SubgroupInvariantSetOrbitIndex.orbit_card_le_subgroup_orbit_mul_index L v).trans
    (Nat.mul_le_mul_right L.index hcard)

variable {N V Z : Type*} [Group N] [Group Z] [CommGroup V]
    (φ : T →* MulAut N)

theorem quotient_orbit_card_le [Finite T] [Finite V]
    (π : N →* V) (ψ : T →* MulAut V)
    (hπ : ∀ t n, π (φ t n) = ψ t (π n))
    (M : Subgroup (N ⋊[φ] T)) (v : V)
    (hvW : v ∈ (M.comap SemidirectProduct.inl).map π) (hv : v ≠ 1) :
    Nat.card (layerOrbit ψ v) ≤
      (Nat.card ((M.comap SemidirectProduct.inl).map π) - 1) *
        (M.map SemidirectProduct.rightHom).index := by
  apply orbit_card_le ψ (M.map SemidirectProduct.rightHom)
    ((M.comap SemidirectProduct.inl).map π) _ v hvW hv
  exact CentralExtensionSemidirectStabilizer.quotient_action_mem_of_projected φ π ψ hπ M

theorem central_orbit_card_le [Finite T] [Finite Z]
    (ι : Z →* N) (χ : T →* MulAut Z)
    (hι : ∀ t z, φ t (ι z) = ι (χ t z))
    (hcentral : ∀ z, ι z ∈ Subgroup.center N)
    (M : Subgroup (N ⋊[φ] T)) (z : Z)
    (hzC : z ∈ (M.comap SemidirectProduct.inl).comap ι) (hz : z ≠ 1) :
    Nat.card (layerOrbit χ z) ≤
      (Nat.card ((M.comap SemidirectProduct.inl).comap ι) - 1) *
        (M.map SemidirectProduct.rightHom).index := by
  apply orbit_card_le χ (M.map SemidirectProduct.rightHom)
    ((M.comap SemidirectProduct.inl).comap ι) _ z hzC hz
  exact CentralExtensionSemidirectStabilizer.central_action_mem_of_projected
    φ ι χ hι hcentral M

end SymmetricSubgroupAsymptotics.CentralExtensionLayerOrbitIndex
