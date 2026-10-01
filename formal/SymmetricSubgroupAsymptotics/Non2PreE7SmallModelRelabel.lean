import SymmetricSubgroupAsymptotics.Non2PreE7SmallModelToolkit
import SymmetricSubgroupAsymptotics.OrbitProfileAssembly

/-!
# Named actual actions as relabelings of model actions

A named actual action class is the image of an injective model action
`ι : G → Perm X`, relabeled by a bijection `X ≃ Fin w`.  Such an actual
subgroup is literally isomorphic to the model group, and its width is the
model degree.
-/

set_option autoImplicit false
noncomputable section

namespace SymmetricSubgroupAsymptotics

/-- The relabeled image of an injective model action is the model group. -/
def relabelModelEquiv {X : Type} {w : ℕ} {G : Type} [Group G] (ι : G →* Equiv.Perm X)
    (hι : Function.Injective ι) (e : X ≃ Fin w) {U : Subgroup (Equiv.Perm (Fin w))}
    (h : U = relabelSubgroup e ι.range) : U ≃* G := by
  have h' : relabelSubgroup e ι.range =
      ι.range.map (e.permCongrHom : Equiv.Perm X →* Equiv.Perm (Fin w)) := rfl
  exact (MulEquiv.subgroupCongr (h.trans h')).trans
    ((e.permCongrHom.subgroupMap ι.range).symm.trans (MonoidHom.ofInjective hι).symm)

/-- The width of a relabeled model action is the model degree. -/
theorem width_eq_of_relabel {X : Type} [Finite X] {w : ℕ} (e : X ≃ Fin w) :
    w = Nat.card X := by
  rw [Nat.card_congr e, Nat.card_fin]

end SymmetricSubgroupAsymptotics
