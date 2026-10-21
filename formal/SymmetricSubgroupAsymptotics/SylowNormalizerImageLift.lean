import Mathlib.GroupTheory.Sylow

/-! Frattini lifting with an exact image hypothesis.  Apply this in the
preimage of the desired quotient normalizer, taking N to be the preimage
of its normal Sylow subgroup. No splitting or chosen complement is used. -/
set_option autoImplicit false
noncomputable section

namespace SymmetricSubgroupAsymptotics.SylowNormalizerImageLift

variable {G H : Type*} [Group G] [Group H] {p : ℕ} [Fact p.Prime]

theorem map_normalizer_eq_top (f : G →* H) (hf : Function.Surjective f)
    (N : Subgroup G) [N.Normal] [Finite (Sylow p N)]
    (P : Sylow p N)
    (himage : N.map f = (P.map N.subtype).map f) :
    (Subgroup.normalizer (P.map N.subtype)).map f = ⊤ := by
  have hle : N.map f ≤ (Subgroup.normalizer (P.map N.subtype)).map f := by
    rw [himage]
    exact Subgroup.map_mono (P.map N.subtype).le_normalizer
  have hwhole := congrArg (fun K : Subgroup G => K.map f)
    (Sylow.normalizer_sup_eq_top P)
  change (Subgroup.normalizer (P.map N.subtype) ⊔ N).map f =
    (⊤ : Subgroup G).map f at hwhole
  rw [Subgroup.map_sup, Subgroup.map_top_of_surjective f hf,
    sup_eq_left.mpr hle] at hwhole
  exact hwhole

theorem exists_normalizing_lift (f : G →* H) (hf : Function.Surjective f)
    (N : Subgroup G) [N.Normal] [Finite (Sylow p N)]
    (P : Sylow p N)
    (himage : N.map f = (P.map N.subtype).map f) (h : H) :
    ∃ g : G, g ∈ Subgroup.normalizer (P.map N.subtype) ∧ f g = h := by
  have hm : h ∈ (Subgroup.normalizer (P.map N.subtype)).map f := by
    rw [map_normalizer_eq_top f hf N P himage]
    trivial
  exact hm

end SymmetricSubgroupAsymptotics.SylowNormalizerImageLift
