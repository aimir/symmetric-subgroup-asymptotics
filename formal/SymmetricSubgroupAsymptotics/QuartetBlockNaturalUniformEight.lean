import SymmetricSubgroupAsymptotics.QuartetBlockCyclicNaturalUniform
import SymmetricSubgroupAsymptotics.ProductBlockFrameTransitiveTop
import SymmetricSubgroupAsymptotics.TransitiveDerangement

/-! Every actual transitive system of four quartets has natural binary
uniform bound eight. A derangement of the actual four-point top has at
most two orbits, and its actual lift carries all four points over each
orbit seed. No local independence or split complement is assumed. -/
set_option autoImplicit false
noncomputable section
namespace SymmetricSubgroupAsymptotics.QuartetBlockNaturalUniformEight

private theorem derangement_cover : ∀ p : Equiv.Perm (Fin 4),
    (∀ i,p i≠i) → ∃ a : Fin 2 → Fin 4,
      ∀ i : Fin 4,∃ j : Fin 2,∃ m : Fin 4,(p^m.val) (a j)=i := by
  decide +kernel

variable {X : Type} [Fintype X] [DecidableEq X]
  {T : Subgroup (Equiv.Perm X)} (C : ProductBlockFrame T (Fin 4) (Fin 4))

 theorem uniform_of_cover (g : T) (a : Fin 2 → Fin 4)
    (hcover : ∀ i : Fin 4,∃ j : Fin 2,∃ m : ℕ,((C.top g)^m) (a j)=i) :
    UniformSubrepresentationGeneratorBound
      (permutationFunctionRepresentation (ZMod 2) T X) 8 := by
  let e : Fin 8 ≃ Fin 2×Fin 4 :=
    (finProdFinEquiv : Fin 2×Fin 4 ≃ Fin (2*4)).symm
  apply permutationFunctionRepresentation_uniform_of_polynomial_orbitCover
    g (fun j : Fin 8 => C.frame (a (e j).1,(e j).2))
  intro x
  let p := C.frame.symm x
  obtain ⟨j,m,hm⟩ := hcover p.1
  let y := ((g^m)⁻¹ : T) • x
  let b := (C.frame.symm y).2
  have hy : (C.frame.symm y).1=a j := by
    have h := C.intertwine ((g^m)⁻¹) p
    rw [C.frame.apply_symm_apply,map_inv,map_pow,←hm] at h
    simpa only [p,y,Equiv.Perm.inv_def,Equiv.symm_apply_apply] using h
  have hb : C.frame (a j,b)=y := by
    apply C.frame.symm.injective
    rw [C.frame.symm_apply_apply]
    exact Prod.ext hy.symm rfl
  refine ⟨finProdFinEquiv (j,b),m,?_⟩
  change (g^m) • C.frame (a (e (finProdFinEquiv (j,b))).1,
    (e (finProdFinEquiv (j,b))).2)=x
  dsimp only [e]
  rw [Equiv.symm_apply_apply,hb]
  exact smul_inv_smul (g^m) x

include C in
 theorem uniform [MulAction.IsPretransitive T X] :
    UniformSubrepresentationGeneratorBound
      (permutationFunctionRepresentation (ZMod 2) T X) 8 := by
  letI : MulAction.IsPretransitive C.top.range (Fin 4) :=
    ⟨C.top_range_transitive (fun x y => MulAction.exists_smul_eq T x y)⟩
  obtain ⟨c,hc⟩ := exists_fixedBy_eq_empty_of_pretransitive C.top.range (Fin 4)
  obtain ⟨g,hg⟩ := c.property
  have hmove : ∀ i : Fin 4,(C.top g) i≠i := by
    intro i hi
    have hm : i∈MulAction.fixedBy (Fin 4) c := by
      change c.val i=i
      rw [←hg]
      exact hi
    rw [hc] at hm
    exact hm
  obtain ⟨a,ha⟩ := derangement_cover (C.top g) hmove
  apply uniform_of_cover C g a
  intro i
  obtain ⟨j,m,hm⟩ := ha i
  exact ⟨j,m.val,hm⟩

end SymmetricSubgroupAsymptotics.QuartetBlockNaturalUniformEight
