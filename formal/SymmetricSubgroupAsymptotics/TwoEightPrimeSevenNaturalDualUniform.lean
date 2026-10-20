import SymmetricSubgroupAsymptotics.PrimeSevenEightOrbitCount
import SymmetricSubgroupAsymptotics.PermutationFunctionSelfDual
import Mathlib.Logic.Equiv.Fin.Basic

/-! A literal odd subgroup with order-seven images on both eight-point
fibres gives the whole actual sixteen-point natural dual module bound four.
The input records actual operators and points, not a module-capacity bound. -/
set_option autoImplicit false
noncomputable section
open scoped Classical
namespace SymmetricSubgroupAsymptotics

private theorem seven_image_orbit_cover
    (R : Subgroup (Equiv.Perm (Fin 8))) (hR : Nat.card R = 7) :
    ∃ r : Fin 2 → Fin 8, ∀ x : Fin 8,
      ∃ (j : Fin 2) (g : R), g • r j = x := by
  let O := MulAction.orbitRel.Quotient R (Fin 8)
  letI : Fintype O := Fintype.ofFinite O
  have hc : Fintype.card O ≤ 2 := by
    simpa only [O, Nat.card_eq_fintype_card] using
      primeSeven_eight_orbit_count hR (Nat.card_fin 8)
  let e : O ≃ Fin (Fintype.card O) := Fintype.equivFin O
  let orbitAt : Fin 2 → O := fun j => if hj : j.val < Fintype.card O then
    e.symm ⟨j.val, hj⟩ else Quotient.mk'' (0 : Fin 8)
  have honto : Function.Surjective orbitAt := by
    intro o
    let j : Fin 2 := ⟨(e o).val, lt_of_lt_of_le (e o).isLt hc⟩
    refine ⟨j, ?_⟩
    have hj : j.val < Fintype.card O := (e o).isLt
    simp only [orbitAt, dif_pos hj]
    exact e.symm_apply_apply o
  refine ⟨fun j => (orbitAt j).out, ?_⟩
  intro x
  obtain ⟨j, hj⟩ := honto (Quotient.mk'' x)
  have heq : (Quotient.mk'' (orbitAt j).out : O) = Quotient.mk'' x :=
    (Quotient.out_eq' (orbitAt j)).trans hj
  obtain ⟨g, hg⟩ := (Quotient.exact heq.symm : x ∈ MulAction.orbit R (orbitAt j).out)
  exact ⟨j, g, hg⟩

/-- Actual restriction to an odd subgroup is enough. Its two local images
are the faithful order-seven permutation groups used by orbit-stabilizer. -/
theorem twoEight_primeSeven_natural_uniform_four
    {G C X : Type} [Group G] [Group C] [Finite G] [Finite C]
    [MulAction G X] [Fintype X]
    [NeZero (Nat.card C : ZMod 2)]
    (f : C →* G) (points : X ≃ Fin 2 × Fin 8)
    (rho : Fin 2 → C →* Equiv.Perm (Fin 8))
    (hcard : ∀ i, Nat.card (rho i).range = 7)
    (hact : ∀ c x, points (f c • x) =
      ((points x).1, rho (points x).1 c (points x).2)) :
    UniformSubrepresentationGeneratorBound
      (permutationFunctionRepresentation (ZMod 2) G X) 4 := by
  choose r hr using fun i => seven_image_orbit_cover (rho i).range (hcard i)
  apply permutationFunctionRepresentation_uniform_of_restricted_orbitCover
    (k := ZMod 2) f
    (fun j : Fin 4 => let z := finProdFinEquiv.symm j
      points.symm (z.1, r z.1 z.2))
  intro x
  let i : Fin 2 := (points x).1
  obtain ⟨j, g, hg⟩ := hr i (points x).2
  obtain ⟨c, hc⟩ := g.property
  refine ⟨finProdFinEquiv (i, j), c, ?_⟩
  apply points.injective
  rw [hact]
  simp only [Equiv.symm_apply_apply, Equiv.apply_symm_apply]
  change (i, rho i c (r i j)) = points x
  have he : rho i c (r i j) = (points x).2 := by
    rw [hc]
    exact hg
  rw [he]

/-- The same actual orbit cover also bounds the natural dual. -/
theorem twoEight_primeSeven_natural_dual_uniform_four
    {G C X : Type} [Group G] [Group C] [Finite G] [Finite C]
    [MulAction G X] [Fintype X]
    [NeZero (Nat.card C : ZMod 2)]
    (f : C →* G) (points : X ≃ Fin 2 × Fin 8)
    (rho : Fin 2 → C →* Equiv.Perm (Fin 8))
    (hcard : ∀ i, Nat.card (rho i).range = 7)
    (hact : ∀ c x, points (f c • x) =
      ((points x).1, rho (points x).1 c (points x).2)) :
    UniformSubrepresentationGeneratorBound
      (permutationFunctionRepresentation (ZMod 2) G X).dual 4 :=
  permutationFunctionRepresentation_dual_uniform
    (twoEight_primeSeven_natural_uniform_four f points rho hcard hact)

end SymmetricSubgroupAsymptotics
