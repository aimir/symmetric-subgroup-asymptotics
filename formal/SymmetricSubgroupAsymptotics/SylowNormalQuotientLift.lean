import Mathlib.GroupTheory.Sylow

/-! A normal p-subgroup in an actual quotient lifts onto inside every
original Sylow p-subgroup. The source of the lift is its literal preimage
inside that Sylow, retaining the original epimorphism and all correlations. -/

set_option autoImplicit false
noncomputable section

namespace SymmetricSubgroupAsymptotics.SylowNormalQuotientLift

variable {p : ℕ} [Fact p.Prime] {G Q : Type} [Group G] [Finite G] [Group Q]
    (f : G →* Q) (hf : Function.Surjective f)
    (D : Subgroup Q) [D.Normal] (hD : IsPGroup p D) (P : Sylow p G)

include hD in
/-- Maximality of a Sylow absorbs every normal p-subgroup. -/
theorem normal_le_sylow (S : Sylow p Q) : D ≤ (S : Subgroup Q) := by
  have he : D ⊔ (S : Subgroup Q) = (S : Subgroup Q) :=
    S.3 (hD.to_sup_of_normal_left S.isPGroup') le_sup_right
  exact sup_eq_right.mp he

abbrev preimage : Subgroup P := D.comap (f.comp (P : Subgroup G).subtype)

def projection : preimage f D P →* D where
  toFun z := ⟨f ((z.1 : P) : G), z.2⟩
  map_one' := Subtype.ext f.map_one
  map_mul' x y := Subtype.ext (f.map_mul _ _)

include hf hD in
/-- Surjectivity is onto the displayed original normal subgroup, not a
separately chosen isomorphic model. -/
theorem projection_surjective : Function.Surjective (projection f D P) := by
  intro d
  have hd : (d : Q) ∈ (P : Subgroup G).map f :=
    normal_le_sylow D hD (P.mapSurjective hf) d.2
  obtain ⟨g, hg, he⟩ := hd
  let z : preimage f D P := ⟨⟨g, hg⟩, by
    change f g ∈ D
    exact he.symm ▸ d.2⟩
  exact ⟨z, Subtype.ext he⟩

end SymmetricSubgroupAsymptotics.SylowNormalQuotientLift

end
