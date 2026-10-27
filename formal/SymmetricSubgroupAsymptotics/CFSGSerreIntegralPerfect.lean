import SymmetricSubgroupAsymptotics.CFSGSerreIntegralDividedPowerLie

/-! If each simple-root column has a minus-one Cartan entry, the literal
integral lattice is perfect. Stability of the bracket span follows from
the integral divided Leibniz identity, not from a basis assumption. -/
set_option autoImplicit false
noncomputable section
open scoped BigOperators
namespace SymmetricSubgroupAsymptotics.CFSGSerreIntegralPerfect
open CFSG.Models.Chevalley CFSGSerreDiagram CFSGSerreLocalNilpotence
open CFSGSerreIntegralLieAlgebra CFSGSerreIntegralDividedPowerLie
variable {r : ℕ} (A : Matrix (Fin r) (Fin r) ℤ)

def bracketSpan : Submodule ℤ (integralLattice A) :=
  Submodule.span ℤ (Set.range (fun xy : integralLattice A × integralLattice A => ⁅xy.1,xy.2⁆))

theorem bracket_mem (x y : integralLattice A) : ⁅x,y⁆ ∈ bracketSpan A :=
  Submodule.subset_span ⟨(x,y),rfl⟩

theorem dividedPower_mem (negative : Bool) (i : Fin r) (k : ℕ)
    (x : integralLattice A) (hx : x ∈ bracketSpan A) :
    integralOperator A negative i k x ∈ bracketSpan A := by
  induction hx using Submodule.span_induction with
  | mem z hz =>
    obtain ⟨⟨u,v⟩,rfl⟩ := hz
    rw [integralOperator_lie]
    exact (bracketSpan A).sum_mem fun j hj => bracket_mem A _ _
  | zero => simpa only [map_zero] using (bracketSpan A).zero_mem
  | add x y _ _ hx hy =>
    rw [map_add]
    exact (bracketSpan A).add_mem hx hy
  | smul a x _ hx =>
    rw [map_smul]
    exact (bracketSpan A).smul_mem a hx

theorem generators_mem (hneighbour : ∀ i : Fin r, ∃ j : Fin r, A j i = -1)
    (g : CartanMatrix.Generators (Fin r)) : latticeGenerator A g ∈ bracketSpan A := by
  cases g with
  | H i =>
    have he : ⁅latticeGenerator A (.E i),latticeGenerator A (.F i)⁆ =
        latticeGenerator A (.H i) := by
      apply Subtype.ext
      exact generator_EF_same A i
    rw [← he]
    exact bracket_mem A _ _
  | E i =>
    obtain ⟨j,hj⟩ := hneighbour i
    have he : ⁅latticeGenerator A (.H j),latticeGenerator A (.E i)⁆ =
        -latticeGenerator A (.E i) := by
      apply Subtype.ext
      change ⁅generator A (.H j),generator A (.E i)⁆ = -generator A (.E i)
      rw [generator_HE, hj]
      simp
    have hm : -latticeGenerator A (.E i) ∈ bracketSpan A :=
      he ▸ bracket_mem A _ _
    simpa only [neg_neg] using (bracketSpan A).neg_mem hm
  | F i =>
    obtain ⟨j,hj⟩ := hneighbour i
    have he : ⁅latticeGenerator A (.H j),latticeGenerator A (.F i)⁆ =
        latticeGenerator A (.F i) := by
      apply Subtype.ext
      change ⁅generator A (.H j),generator A (.F i)⁆ = generator A (.F i)
      rw [generator_HF, hj]
      simp
    exact he ▸ bracket_mem A _ _

theorem bracketSpan_eq_top
    (hneighbour : ∀ i : Fin r, ∃ j : Fin r, A j i = -1) : bracketSpan A = ⊤ := by
  let S := (bracketSpan A).map (integralLattice A).subtype
  have hle : integralLattice A ≤ S := by
    apply integralLattice_le_of_stable A S
    · intro g
      exact ⟨latticeGenerator A g,generators_mem A hneighbour g,rfl⟩
    · intro negative i k x hx
      obtain ⟨z,hz,hzx⟩ := hx
      refine ⟨integralOperator A negative i k z,
        dividedPower_mem A negative i k z hz,?_⟩
      change dividedPower A negative i k z.val = dividedPower A negative i k x
      exact congrArg (dividedPower A negative i k) hzx
  apply top_unique
  intro x hx
  obtain ⟨z,hz,hzx⟩ := hle x.property
  have he : z = x := Subtype.ext hzx
  exact he ▸ hz

end SymmetricSubgroupAsymptotics.CFSGSerreIntegralPerfect
