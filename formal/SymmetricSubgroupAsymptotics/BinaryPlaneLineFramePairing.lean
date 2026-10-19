import SymmetricSubgroupAsymptotics.BinaryPlaneInvariantLineFrame
import SymmetricSubgroupAsymptotics.BinaryPlanePermutationWreathCoordinates
import SymmetricSubgroupAsymptotics.TransitivePairingCount

/-! A genuine invariant local line family gives an actual equivariant
partner involution, including arbitrary original affine translations.
Its transport keeps the original points and original subgroup action. -/
set_option autoImplicit false
noncomputable section
namespace SymmetricSubgroupAsymptotics.BinaryPlaneLineFramePairing
open BinaryPlanePermutationAffineEquiv
open BinaryPlaneWreathNormalGenerators
abbrev Top := Equiv.Perm (Fin 4)
abbrev Affine := Model (R := Top) (I := Fin 4)
abbrev Point := Plane × Fin 4

def partner (v : Fin 4 → Plane) (p : Point) : Point := (p.1+v p.2,p.2)

theorem partner_involutive (v : Fin 4 → Plane) : Function.Involutive (partner v) := by
  intro p
  apply Prod.ext
  · change (p.1+v p.2)+v p.2=p.1
    rw [add_assoc,binaryVector_add_self,add_zero]
  · rfl

theorem partner_ne (v : Fin 4 → Plane) (hv : ∀ i, v i≠0) (p : Point) :
    partner v p≠p := by
  intro h
  apply hv p.2
  have he := congrArg Prod.fst h
  change p.1+v p.2=p.1 at he
  exact add_left_cancel (he.trans (add_zero p.1).symm)

theorem partner_equivariant (v : Fin 4 → Plane) (g : Affine)
    (hline : ∀ i : Fin 4,
      g.right.left (g.right.right i) (v i)=v (g.right.right i)) (p : Point) :
    partner v (BinaryPlanePermutationWreathCoordinates.pointAction g p)=
      BinaryPlanePermutationWreathCoordinates.pointAction g (partner v p) := by
  apply Prod.ext
  · change (g.left (g.right.right p.2)).toAdd+
      g.right.left (g.right.right p.2) p.1+v (g.right.right p.2)=
      (g.left (g.right.right p.2)).toAdd+
        g.right.left (g.right.right p.2) (p.1+v p.2)
    rw [map_add,hline,add_assoc]
  · rfl

/-- The original subgroup gets its actual partner FUNCTION, not merely an
abstract pair count or a pairing on a replacement quotient. -/
def originalPairing {X : Type} (U : Subgroup (Equiv.Perm X))
    (rho : U →* Affine) (chart : Point ≃ X)
    (hpoint : ∀ (u : U) p, chart (BinaryPlanePermutationWreathCoordinates.pointAction
      (rho u) p)=(u : Equiv.Perm X) (chart p))
    (v : Fin 4 → Plane) (hv : ∀ i, v i≠0)
    (hline : ∀ (u : U) (i : Fin 4),
      (rho u).right.left ((rho u).right.right i) (v i)=v ((rho u).right.right i)) :
    EquivariantPairing U X :=
  ⟨fun x => chart (partner v (chart.symm x)),by
    constructor
    · intro x
      change chart (partner v (chart.symm (chart (partner v (chart.symm x)))))=x
      rw [chart.symm_apply_apply,partner_involutive,chart.apply_symm_apply]
    · constructor
      · intro x hx
        apply partner_ne v hv (chart.symm x)
        have he := congrArg chart.symm hx
        simpa only [chart.symm_apply_apply] using he
      · intro u x
        have hx : chart.symm ((u : Equiv.Perm X) x)=
            BinaryPlanePermutationWreathCoordinates.pointAction (rho u) (chart.symm x) := by
          have he := congrArg chart.symm (hpoint u (chart.symm x))
          simpa only [chart.symm_apply_apply,chart.apply_symm_apply] using he.symm
        change chart (partner v (chart.symm ((u : Equiv.Perm X) x)))=
          (u : Equiv.Perm X) (chart (partner v (chart.symm x)))
        rw [hx,partner_equivariant v (rho u) (hline u)]
        exact hpoint u _⟩

end SymmetricSubgroupAsymptotics.BinaryPlaneLineFramePairing
