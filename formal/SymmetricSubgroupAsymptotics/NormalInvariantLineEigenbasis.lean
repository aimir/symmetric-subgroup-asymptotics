import Mathlib.RepresentationTheory.Irreducible
import Mathlib.LinearAlgebra.Basis.VectorSpace
import Mathlib.LinearAlgebra.Dimension.StrongRankCondition
import Mathlib.Tactic.Group

/-! A line invariant under a normal subgroup produces an eigenbasis by
ambient irreducibility: all conjugate lines stay invariant under that
same normal subgroup, and their span is the whole original module. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
open scoped Classical
namespace SymmetricSubgroupAsymptotics.NormalInvariantLineEigenbasis
variable {k G V : Type} [Field k] [Group G] [AddCommGroup V] [Module k V]
    (rho : Representation k G V)

def orbitSpan (v : V) : Subrepresentation rho where
  toSubmodule := Submodule.span k (Set.range (fun g : G => rho g v))
  apply_mem_toSubmodule g w hw := by
    induction hw using Submodule.span_induction with
    | mem w hw =>
        obtain ⟨h,rfl⟩ := hw
        apply Submodule.subset_span
        refine ⟨g*h,?_⟩
        change rho (g*h) v=rho g (rho h v)
        rw [map_mul]
        rfl
    | zero => simpa only [map_zero] using
        (Submodule.span k (Set.range (fun g : G => rho g v))).zero_mem
    | add x y _ _ hx hy => simpa only [map_add] using
        (Submodule.span k (Set.range (fun g : G => rho g v))).add_mem hx hy
    | smul a x _ hx => simpa only [map_smul] using
        (Submodule.span k (Set.range (fun g : G => rho g v))).smul_mem a hx

theorem orbit_span_eq_top (hrho : Representation.IsIrreducible rho)
    (v : V) (hv : v≠0) :
    Submodule.span k (Set.range (fun g : G => rho g v))=⊤ := by
  letI : Representation.IsIrreducible rho := hrho
  have hm : v∈orbitSpan rho v := by
    apply Submodule.subset_span
    refine ⟨1,?_⟩
    change rho 1 v=v
    rw [map_one]
    rfl
  rcases eq_bot_or_eq_top (orbitSpan rho v) with hb|ht
  · have hbv : v∈(⊥ : Subrepresentation rho) := hb ▸ hm
    exact (hv hbv).elim
  · exact congrArg Subrepresentation.toSubmodule ht

variable [Finite V]

theorem exists_eigenbasis_three
    (hrho : Representation.IsIrreducible rho)
    (hdim : Module.finrank k V=3)
    (N : Subgroup G) [N.Normal] (v : V) (hv : v≠0)
    (hline : ∀ n : N,∃ a : k,rho n.val v=a • v) :
    ∃ b : Module.Basis (Fin 3) k V,
      ∀ (n : N) (i : Fin 3),∃ a : k,rho n.val (b i)=a • b i := by
  have hconj (n : N) (g : G) : ∃ a : k,rho n.val (rho g v)=a • rho g v := by
    let m : N := ⟨g⁻¹*n.val*g,by
      simpa only [inv_inv] using Subgroup.Normal.conj_mem
        (inferInstance : N.Normal) n.val n.property g⁻¹⟩
    obtain ⟨a,ha⟩ := hline m
    refine ⟨a,?_⟩
    have he : n.val*g=g*m.val := by dsimp only [m]; group
    calc
      _=rho (n.val*g) v := by rw [map_mul]; rfl
      _=rho (g*m.val) v := by rw [he]
      _=rho g (rho m.val v) := by rw [map_mul]; rfl
      _=a • rho g v := by rw [ha,map_smul]
  obtain ⟨s,hs,hspan,hli⟩ := exists_linearIndependent k
    (Set.range (fun g : G => rho g v))
  have htop := orbit_span_eq_top rho hrho v hv
  have hsp : ⊤ ≤ Submodule.span k (Set.range (Subtype.val : s → V)) := by
    simpa only [Subtype.range_coe_subtype,Set.setOf_mem_eq,hspan,htop]
      using (le_refl (⊤ : Submodule k V))
  let b : Module.Basis s k V := Module.Basis.mk hli hsp
  have hb (i : s) : b i=i.val := Module.Basis.mk_apply hli hsp i
  letI : Fintype s := Fintype.ofFinite s
  have hsCard : Nat.card s=3 := by
    have hc := Module.finrank_eq_card_basis b
    simpa only [hdim,Fintype.card_eq_nat_card] using hc.symm
  let e : s ≃ Fin 3 := Finite.equivFinOfCardEq hsCard
  refine ⟨b.reindex e,?_⟩
  intro n i
  obtain ⟨g,hg⟩ := hs (e.symm i).property
  have he : (b.reindex e) i=rho g v := by
    rw [Module.Basis.reindex_apply,hb]
    exact hg.symm
  rw [he]
  exact hconj n g

end SymmetricSubgroupAsymptotics.NormalInvariantLineEigenbasis
