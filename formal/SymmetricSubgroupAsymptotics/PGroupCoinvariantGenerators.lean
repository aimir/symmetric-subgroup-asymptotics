import SymmetricSubgroupAsymptotics.InducedSubrepresentationCount
import SymmetricSubgroupAsymptotics.RepresentationCoinvariantHead
import SymmetricSubgroupAsymptotics.RepresentationHeadExact
import SymmetricSubgroupAsymptotics.SchurPGroupCapacity
import SymmetricSubgroupAsymptotics.TraceyAffineInducedModuleInput
import Mathlib.LinearAlgebra.Basis.VectorSpace

/-!
# Generators from coinvariants for defining-characteristic p-groups

For a finite `p`-group over `F_p`, the least number of module generators is
the dimension of the coinvariant head.  This is the elementary Nakayama
argument needed to turn the sharp Sylow-restricted ternary head bounds into
actual generator bounds.

The proof below is intrinsic.  If lifts of a coinvariant basis generated a
proper submodule, the nonzero quotient would have a nonzero fixed vector in
its dual.  Equivalently its coinvariants would be nonzero, contradicting the
surjective zero map induced on coinvariants.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
open scoped Classical MonoidAlgebra

namespace SymmetricSubgroupAsymptotics

universe u

variable {p : ℕ} [Fact p.Prime]
variable {G V : Type u} [Group G]
  [AddCommGroup V] [Module (ZMod p) V]
  [Finite V] [FiniteDimensional (ZMod p) V]

omit [Finite V] [FiniteDimensional (ZMod p) V] in
private theorem coinvariants_map_surjective_of_surjective
    {W : Type u} [AddCommGroup W] [Module (ZMod p) W]
    (rho : Representation (ZMod p) G V)
    (sigma : Representation (ZMod p) G W)
    (f : rho.IntertwiningMap sigma)
    (hf : Function.Surjective f) :
    Function.Surjective (Representation.Coinvariants.map rho sigma f) := by
  intro y
  induction y using Representation.Coinvariants.induction_on with
  | _ y =>
      obtain ⟨x, rfl⟩ := hf y
      exact ⟨Representation.Coinvariants.mk rho x, rfl⟩

/-- For a defining-characteristic `p`-group representation, any tuple whose
images span the coinvariants already generates the original group-algebra
module. -/
theorem pGroup_representationGeneratedBy_of_coinvariant_span
    (hG : IsPGroup p G)
    (rho : Representation (ZMod p) G V)
    {n : ℕ} (v : Fin n → rho.asModule)
    (hspan : Submodule.span (ZMod p)
      (Set.range (fun i ↦ Representation.Coinvariants.mk rho
        (rho.asModuleEquiv (v i)))) = ⊤) :
    RepresentationGeneratedBy rho n := by
  let W : Submodule (ZMod p)[G] rho.asModule :=
    Submodule.span (ZMod p)[G] (Set.range v)
  by_contra hproper
  have hW : W ≠ ⊤ := by
    intro htop
    apply hproper
    exact ⟨v, htop⟩
  let M : Subrepresentation rho := Subrepresentation.ofSubmodule' W
  let sigma : Representation (ZMod p) G (V ⧸ M.toSubmodule) :=
    rho.quotient M.toSubmodule (fun g x hx ↦ M.apply_mem_toSubmodule g hx)
  let q : rho.IntertwiningMap sigma :=
    { toLinearMap := M.toSubmodule.mkQ
      isIntertwining' _ := rfl }
  let qC : rho.Coinvariants →ₗ[ZMod p] sigma.Coinvariants :=
    Representation.Coinvariants.map rho sigma q
  have hq : Function.Surjective q := M.toSubmodule.mkQ_surjective
  have hqC : Function.Surjective qC :=
    coinvariants_map_surjective_of_surjective rho sigma q hq
  have hqv : ∀ i, qC
      (Representation.Coinvariants.mk rho (rho.asModuleEquiv (v i))) = 0 := by
    intro i
    rw [Representation.Coinvariants.map_mk]
    have hvi : rho.asModuleEquiv (v i) ∈ M.toSubmodule := by
      change v i ∈ W
      exact Submodule.subset_span (Set.mem_range_self i)
    have hqvi : q (rho.asModuleEquiv (v i)) = 0 := by
      change M.toSubmodule.mkQ (rho.asModuleEquiv (v i)) = 0
      exact (Submodule.Quotient.mk_eq_zero M.toSubmodule).2 hvi
    rw [hqvi, map_zero]
  have hqCzero : qC = 0 := by
    apply LinearMap.ext_on_range hspan
    intro i
    simpa using hqv i
  letI : Finite (V ⧸ M.toSubmodule) :=
    Finite.of_surjective M.toSubmodule.mkQ M.toSubmodule.mkQ_surjective
  have hMlt : M.toSubmodule < ⊤ := lt_top_iff_ne_top.mpr (by
    intro htop
    apply hW
    apply SetLike.ext
    intro x
    have hx : x ∈ M.toSubmodule ↔
        x ∈ (⊤ : Submodule (ZMod p) V) := by
      rw [htop]
    simpa only [Submodule.mem_top] using hx)
  obtain ⟨x, hx⟩ := SetLike.exists_of_lt hMlt
  letI : Nontrivial (V ⧸ M.toSubmodule) :=
    ⟨⟨M.toSubmodule.mkQ x, 0, by
      intro heq
      apply hx.2
      exact (Submodule.Quotient.mk_eq_zero M.toSubmodule).mp heq⟩⟩
  letI : Finite (Module.Dual (ZMod p) (V ⧸ M.toSubmodule)) :=
    Module.finite_of_finite (ZMod p)
  obtain ⟨f, hf0, hfixed⟩ :=
    pGroup_representation_nonzero_fixed hG sigma.dual
  have hinv_ne : sigma.dual.invariants ≠ ⊥ := by
    intro hbot
    have hfmem : f ∈ sigma.dual.invariants := hfixed
    rw [hbot] at hfmem
    exact hf0 (by simpa only [Submodule.mem_bot] using hfmem)
  have hinv_pos : 0 < Module.finrank (ZMod p) sigma.dual.invariants :=
    Nat.zero_lt_one.trans_le (Submodule.one_le_finrank_iff.mpr hinv_ne)
  have hhead_pos : 0 < Module.finrank (ZMod p)
      (sigma.IntertwiningMap
        (Representation.trivial (ZMod p) G (ZMod p))) := by
    have h := hinv_pos
    have he : sigma.dual = sigma.linHom
        (Representation.trivial (ZMod p) G (ZMod p)) := by
      ext g l v
      rfl
    rw [he] at h
    rw [(Representation.invariantsEquivIntertwiningMap sigma
      (Representation.trivial (ZMod p) G (ZMod p))).finrank_eq] at h
    exact h
  have hcoinv_pos : 0 < Module.finrank (ZMod p) sigma.Coinvariants := by
    rw [← representationHead_finrank_eq_coinvariants sigma]
    exact hhead_pos
  haveI : Subsingleton sigma.Coinvariants := ⟨by
    intro a b
    obtain ⟨a, rfl⟩ := hqC a
    obtain ⟨b, rfl⟩ := hqC b
    rw [hqCzero]
    rfl⟩
  rw [Module.finrank_zero_of_subsingleton] at hcoinv_pos
  exact (Nat.lt_irrefl 0) hcoinv_pos

/-- A finite defining-characteristic `p`-group module is generated by the
dimension of its intrinsic coinvariants. -/
theorem pGroup_representationGeneratedBy_coinvariants
    (hG : IsPGroup p G)
    (rho : Representation (ZMod p) G V) :
    RepresentationGeneratedBy rho
      (Module.finrank (ZMod p) rho.Coinvariants) := by
  let b := Module.finBasis (ZMod p) rho.Coinvariants
  let lift : Fin (Module.finrank (ZMod p) rho.Coinvariants) → V :=
    fun i ↦ Classical.choose
      (Representation.Coinvariants.mk_surjective rho (b i))
  have hlift : ∀ i, Representation.Coinvariants.mk rho (lift i) = b i :=
    fun i ↦ Classical.choose_spec
      (Representation.Coinvariants.mk_surjective rho (b i))
  let v : Fin (Module.finrank (ZMod p) rho.Coinvariants) → rho.asModule :=
    fun i ↦ rho.asModuleEquiv.symm (lift i)
  refine pGroup_representationGeneratedBy_of_coinvariant_span hG rho v ?_
  have hfun : (fun i ↦ Representation.Coinvariants.mk rho
      (rho.asModuleEquiv (v i))) = b := by
    funext i
    simpa only [v, rho.asModuleEquiv.apply_symm_apply] using hlift i
  rw [hfun]
  exact b.span_eq

/-- A uniform bound for the intrinsic heads of all subrepresentations of a
`p`-group representation is therefore a uniform generator bound. -/
theorem pGroup_uniformSubrepresentationGeneratorBound_of_head_le
    (hG : IsPGroup p G)
    (rho : Representation (ZMod p) G V)
    (H : ℕ)
    (hhead : ∀ M : Subrepresentation rho,
      Module.finrank (ZMod p)
        (M.toRepresentation.IntertwiningMap
          (Representation.trivial (ZMod p) G (ZMod p))) ≤ H) :
    ∀ M : Subrepresentation rho,
      RepresentationGeneratedBy M.toRepresentation H := by
  intro M
  letI : Finite M.toSubmodule := Finite.of_injective
    M.toSubmodule.subtype M.toSubmodule.injective_subtype
  have hgen := pGroup_representationGeneratedBy_coinvariants
    hG M.toRepresentation
  rw [← representationHead_finrank_eq_coinvariants] at hgen
  exact representationGeneratedBy_mono M.toRepresentation (hhead M) hgen

end SymmetricSubgroupAsymptotics

end
