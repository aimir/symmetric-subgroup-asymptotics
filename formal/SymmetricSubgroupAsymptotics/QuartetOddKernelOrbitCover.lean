import SymmetricSubgroupAsymptotics.ProductBlockFrameKernelCoordinates
import Mathlib.GroupTheory.GroupAction.Quotient

/-! An actual cubic subgroup fixing the four quartet labels has at most
eight original point orbits if every local image is nontrivial. Different
quartets may use different elements; no common local cubic is assumed. -/
set_option autoImplicit false
noncomputable section
open scoped Classical
namespace SymmetricSubgroupAsymptotics.QuartetOddKernelOrbitCover

private theorem cubic_cover : ∀ p : Equiv.Perm (Fin 4),p^3=1 → p≠1 →
    ∃ a : Fin 2 → Fin 4,∀ x : Fin 4,∃ j : Fin 2,∃ m : Fin 3,
      (p^m.val) (a j)=x := by decide +kernel

variable {X : Type} [Finite X] {T : Subgroup (Equiv.Perm X)}
  (C : ProductBlockFrame T (Fin 4) (Fin 4))
  (P : Subgroup T) (hfix : P≤C.top.ker)

def kernelInclusion : P →* C.top.ker where
  toFun p := ⟨p.val,hfix p.property⟩
  map_one' := rfl
  map_mul' _ _ := rfl

def localMap (i : Fin 4) : P →* Equiv.Perm (Fin 4) :=
  (C.kernelCoordinate i).comp (kernelInclusion C P hfix)

omit [Finite X] in
 theorem point_action (p : P) (i b : Fin 4) :
    (p.val : T) • C.frame (i,b)=C.frame (i,localMap C P hfix i p b) := by
  apply C.frame.symm.injective
  rw [C.frame.symm_apply_apply]
  apply Prod.ext
  · have h := C.intertwine p.val (i,b)
    rw [show C.top p.val=1 from hfix p.property] at h
    exact h
  · rfl

 theorem orbit_card_le_eight
    (hcubic : ∀ p : P,p^3=1)
    (hlocal : ∀ i : Fin 4,∃ p : P,localMap C P hfix i p≠1) :
    Nat.card (MulAction.orbitRel.Quotient P X)≤8 := by
  choose p hp using hlocal
  have hcube (i : Fin 4) : localMap C P hfix i (p i)^3=1 := by
    rw [←map_pow,hcubic,map_one]
  choose a ha using fun i => cubic_cover (localMap C P hfix i (p i)) (hcube i) (hp i)
  let e : Fin 8 ≃ Fin 4×Fin 2 :=
    (finProdFinEquiv : Fin 4×Fin 2≃Fin (4*2)).symm
  let seed : Fin 8 → X := fun j => C.frame ((e j).1,a (e j).1 (e j).2)
  have hcover : ∀ x : X,∃ j : Fin 8,∃ g : P,g • seed j=x := by
    intro x
    let z := C.frame.symm x
    obtain ⟨j,m,hm⟩ := ha z.1 z.2
    refine ⟨finProdFinEquiv (z.1,j),(p z.1)^m.val,?_⟩
    change ((p z.1)^m.val : P).val •
      C.frame ((e (finProdFinEquiv (z.1,j))).1,
        a (e (finProdFinEquiv (z.1,j))).1 (e (finProdFinEquiv (z.1,j))).2)=x
    dsimp only [e]
    rw [Equiv.symm_apply_apply,point_action C P hfix,map_pow,hm]
    exact C.frame.apply_symm_apply x
  let O := MulAction.orbitRel.Quotient P X
  let f : Fin 8 → O := fun j => Quotient.mk'' (seed j)
  have hf : Function.Surjective f := by
    intro o
    obtain ⟨j,g,hg⟩ := hcover o.out
    refine ⟨j,?_⟩
    have he : (Quotient.mk'' (g • seed j) : O)=Quotient.mk'' (seed j) :=
      Quotient.sound (MulAction.mem_orbit (seed j) g)
    rw [hg] at he
    exact he.symm.trans (Quotient.out_eq' o)
  simpa only [Nat.card_fin] using Nat.card_le_card_of_surjective f hf

end SymmetricSubgroupAsymptotics.QuartetOddKernelOrbitCover
