import SymmetricSubgroupAsymptotics.CubicBinaryQuotientCoordinates
import SymmetricSubgroupAsymptotics.ScalarFourHeadCount

/-! Convert simultaneous vector coordinates to actual group-kernel maps.
The retained chart and conjugation identity bind every coordinate to the
original denominator. -/
set_option autoImplicit false
noncomputable section
open scoped Classical
namespace SymmetricSubgroupAsymptotics
namespace CubicElementaryKernelCoordinates

variable {Q V : Type} [Group Q] [AddCommGroup V] [Module (ZMod 2) V]
  (top : Q →* CyclicThree) (rho : Representation (ZMod 2) CyclicThree V)
  (e : top.ker ≃* Multiplicative V) (D : CubicBinaryCoordinates rho)
  (hconj : ∀ q p, e (MulAut.conjNormal q p) =
    Multiplicative.ofAdd (rho (top q) (Multiplicative.toAdd (e p))))

def invariant (j : Fin 2) : top.ker →* Multiplicative (ZMod 2) :=
  (AddMonoidHom.toMultiplicative (D.invariant j).toAddMonoidHom).comp e.toMonoidHom

def scalar (j : Fin 2) : top.ker →* ScalarFour :=
  (AddMonoidHom.toMultiplicative (D.scalar j).toAddMonoidHom).comp e.toMonoidHom

include hconj in
theorem invariant_conj (q : Q) (p : top.ker) (j : Fin 2) :
    invariant top rho e D j (MulAut.conjNormal q p) = invariant top rho e D j p := by
  apply Multiplicative.toAdd.injective
  change D.invariant j (Multiplicative.toAdd (e (MulAut.conjNormal q p))) = _
  rw [hconj]
  exact D.invariant_fixed (top q) (Multiplicative.toAdd (e p)) j

include hconj in
theorem scalar_conj (q : Q) (p : top.ker) (j : Fin 2) :
    scalar top rho e D j (MulAut.conjNormal q p) =
      scalarFourTwist (Multiplicative.toAdd (top q)) (scalar top rho e D j p) := by
  apply Multiplicative.toAdd.injective
  change D.scalar j (Multiplicative.toAdd (e (MulAut.conjNormal q p))) = _
  rw [hconj]
  exact D.scalar_twisted (top q) (Multiplicative.toAdd (e p)) j

theorem joint : Function.Injective (fun p : top.ker =>
    ((invariant top rho e D 0 p, invariant top rho e D 1 p),
      (scalar top rho e D 0 p, scalar top rho e D 1 p))) := by
  intro p q he
  apply e.injective
  apply Multiplicative.toAdd.injective
  apply D.joint
  exact Prod.ext
    (Prod.ext
      (congrArg Multiplicative.toAdd (congrArg (fun z => z.1.1) he))
      (congrArg Multiplicative.toAdd (congrArg (fun z => z.1.2) he)))
    (Prod.ext
      (congrArg Multiplicative.toAdd (congrArg (fun z => z.2.1) he))
      (congrArg Multiplicative.toAdd (congrArg (fun z => z.2.2) he)))

include hconj in
/-- A nonzero scalar coordinate is onto on the actual kernel: its actual
image is omega-stable and the displayed F4 module is simple. -/
theorem scalar_surjective (htop : Function.Surjective top) (j : Fin 2)
    (hne : ∃ p : top.ker, scalar top rho e D j p ≠ 1) :
    Function.Surjective (scalar top rho e D j) := by
  obtain ⟨q,hq⟩ := htop (Multiplicative.ofAdd 1)
  obtain ⟨p,hp⟩ := hne
  have hrange : (scalar top rho e D j).range = ⊤ := by
    apply scalarFour_stable_eq_top _ _ (show scalar top rho e D j p ∈
      (scalar top rho e D j).range from ⟨p,rfl⟩) hp
    intro v hv
    obtain ⟨w,rfl⟩ := hv
    refine ⟨MulAut.conjNormal q w,?_⟩
    rw [scalar_conj top rho e D hconj,hq]
    rfl
  exact MonoidHom.range_eq_top.mp hrange

end CubicElementaryKernelCoordinates
end SymmetricSubgroupAsymptotics
end
