import SymmetricSubgroupAsymptotics.BinaryDisplacementSectionBounds
import Mathlib.LinearAlgebra.Pi

/-! The four-point calculation needed by the original maximal-section
argument. A large sum of fixed dimensions forces the literal intermediate
subspace to be the original constant line. All maps retain the original
action; no list of four-point groups or supplied head bound is used. -/
set_option autoImplicit false
noncomputable section
open scoped BigOperators Classical
attribute [local instance] Fintype.ofFinite

namespace SymmetricSubgroupAsymptotics.PermutationBinaryFourSection

section Transitive

variable {k G X : Type} [Field k] [Group G] [MulAction G X]
    [MulAction.IsPretransitive G X]

private theorem fixed_apply_eq (x y : X)
    (f : (permutationFunctionRepresentation k G X).invariants) : f.1 y=f.1 x := by
  obtain ⟨g,hg⟩ := MulAction.exists_smul_eq G x y
  have h := congrFun (f.property g) y
  change f.1 (g⁻¹ • y)=f.1 y at h
  rw [← hg,inv_smul_smul] at h
  simpa only [hg] using h.symm

/-- Fixed functions on the same transitive point set are the constant line. -/
def fixedEval (x : X) :
    (permutationFunctionRepresentation k G X).invariants ≃ₗ[k] k where
  toFun f := f.1 x
  invFun c := ⟨fun _ => c,fun _ => rfl⟩
  left_inv f := by
    apply Subtype.ext
    funext y
    exact (fixed_apply_eq x y f).symm
  right_inv _ := rfl
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

theorem invariants_finrank (x : X) :
    Module.finrank k (permutationFunctionRepresentation k G X).invariants=1 :=
  (fixedEval (k := k) (G := G) x).finrank_eq.trans (Module.finrank_self k)

private def fixedInclusion
    (S : Subrepresentation (permutationFunctionRepresentation k G X)) :
    S.toRepresentation.invariants →ₗ[k]
      (permutationFunctionRepresentation k G X).invariants where
  toFun f := ⟨f.1.1,fun g => congrArg Subtype.val (f.property g)⟩
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

theorem subrepresentation_invariants_le_one (x : X)
    (S : Subrepresentation (permutationFunctionRepresentation k G X)) :
    Module.finrank k S.toRepresentation.invariants≤1 := by
  have hi : Function.Injective (fixedInclusion S) := by
    intro f f' h
    apply Subtype.ext
    apply Subtype.ext
    exact congrArg (fun v : (permutationFunctionRepresentation k G X).invariants =>
      (v : X → k)) h
  have hd := ((fixedEval (k := k) (G := G) x).toLinearMap.comp
    (fixedInclusion S)).finrank_le_finrank_of_injective
      ((fixedEval (k := k) (G := G) x).injective.comp hi)
  simpa only [Module.finrank_self] using hd

private theorem permutation_single (g : G) (x : X) (c : k) :
    permutationFunctionRepresentation k G X g (Pi.single x c)=Pi.single (g • x) c := by
  classical
  funext y
  by_cases hy : y=g • x
  · subst y
    simp only [permutationFunctionRepresentation_apply,Pi.single_eq_same]
    change (Pi.single (M := fun _ : X => k) x c) (g⁻¹ • (g • x))=c
    exact (congrArg (Pi.single (M := fun _ : X => k) x c)
      (inv_smul_smul g x)).trans (Pi.single_eq_same (M := fun _ : X => k) x c)
  · have hx : g⁻¹ • y≠x := by
      intro he
      have hh := congrArg (fun z : X => g • z) he
      exact hy (by simpa only [smul_inv_smul] using hh)
    simp [permutationFunctionRepresentation_apply,hx,hy]

/-- An invariant quotient of the whole original transitive permutation
module is at most one dimensional, even in the modular characteristic. -/
theorem trivial_quotient_finrank_le_one [Finite X]
    {V : Type} [AddCommGroup V] [Module k V] [FiniteDimensional k V]
    (x : X) (q : (X → k) →ₗ[k] V) (hq : Function.Surjective q)
    (hfixed : ∀ (g : G) (f : X → k),
      q (permutationFunctionRepresentation k G X g f)=q f) :
    Module.finrank k V≤1 := by
  have he (y : X) : q (Pi.single y (1:k))=q (Pi.single x (1:k)) := by
    obtain ⟨g,hg⟩ := MulAction.exists_smul_eq G x y
    simpa only [permutation_single,hg] using hfixed g (Pi.single x (1:k))
  have hr : q.range≤Submodule.span k {q (Pi.single x (1:k))} := by
    rintro _ ⟨f,rfl⟩
    rw [← Finset.univ_sum_single f,map_sum]
    apply Submodule.sum_mem
    intro y _
    have hs : Pi.single y (f y)=(f y) • Pi.single y (1:k) := by
      funext z
      by_cases hz : z=y
      · subst z
        simp
      · simp [hz]
    rw [hs,map_smul,he y]
    exact Submodule.smul_mem _ _ (Submodule.subset_span (Set.mem_singleton _))
  have hd := Submodule.finrank_mono hr
  rw [LinearMap.range_eq_top.mpr hq,finrank_top] at hd
  exact hd.trans (by simpa using
    (finrank_span_le_card ({q (Pi.single x (1:k))} : Set V)))

end Transitive

section Four

variable {G X : Type} [Group G] [Finite G] [MulAction G X]
    [Finite X] [MulAction.IsPretransitive G X]
    (S : Subrepresentation (permutationFunctionRepresentation (ZMod 2) G X))

/-- Quotient by the literal original stable subspace. -/
def quotientRepresentation : Representation (ZMod 2) G ((X → ZMod 2) ⧸ S.toSubmodule) :=
  (permutationFunctionRepresentation (ZMod 2) G X).quotient S.toSubmodule
    (fun g => S.apply_mem_toSubmodule g)

private def quotientProjection :
    (⊤ : Subrepresentation (permutationFunctionRepresentation (ZMod 2) G X)).toRepresentation.IntertwiningMap
      (quotientRepresentation S) where
  toLinearMap := S.toSubmodule.mkQ.comp
    (⊤ : Submodule (ZMod 2) (X → ZMod 2)).subtype
  isIntertwining' _ := by
    apply LinearMap.ext
    intro _
    rfl

private theorem quotientProjection_surjective : Function.Surjective (quotientProjection S) := by
  intro v
  obtain ⟨f,hf⟩ := S.toSubmodule.mkQ_surjective v
  exact ⟨⟨f,Submodule.mem_top⟩,hf⟩

include S in
/-- At four original points, the boundary fixed-dimension sum forces
the intermediate subspace to be exactly the original constant line. -/
theorem boundary_forces_constant_line (hG : IsPGroup 2 G)
    (x : X) (hcard : Nat.card X=4)
    (hboundary : 3≤Module.finrank (ZMod 2) S.toRepresentation.invariants+
      Module.finrank (ZMod 2) (quotientRepresentation S).invariants) :
    Module.finrank (ZMod 2) S.toSubmodule=1 ∧
      S.toSubmodule=(permutationFunctionRepresentation (ZMod 2) G X).invariants ∧
      Module.finrank (ZMod 2) (quotientRepresentation S).invariants=2 := by
  have hdim : Module.finrank (ZMod 2) (X → ZMod 2)=4 := by
    simpa only [Module.finrank_pi,Nat.card_eq_fintype_card] using hcard
  have hsum := S.toSubmodule.finrank_quotient_add_finrank
  rw [hdim] at hsum
  have hs := subrepresentation_invariants_le_one x S
  have hsi := Submodule.finrank_le S.toRepresentation.invariants
  have hqi := Submodule.finrank_le (quotientRepresentation S).invariants
  have hq := binary_permutationSection_invariants_finrank_le
    (quotientRepresentation S) hG ⊤ (quotientProjection S)
    (quotientProjection_surjective S) x 2 (by simpa using hcard)
  change Module.finrank (ZMod 2) (quotientRepresentation S).invariants≤2 at hq
  have hsdim : Module.finrank (ZMod 2) S.toSubmodule=1 := by
    have hsrange : 1≤Module.finrank (ZMod 2) S.toSubmodule ∧
        Module.finrank (ZMod 2) S.toSubmodule≤2 := by omega
    by_contra hn
    have hs2 : Module.finrank (ZMod 2) S.toSubmodule=2 := by omega
    have hqt : Module.finrank (ZMod 2) ((X → ZMod 2) ⧸ S.toSubmodule)=2 := by omega
    have hq2 : Module.finrank (ZMod 2) (quotientRepresentation S).invariants=2 := by omega
    have hfull : (quotientRepresentation S).invariants=⊤ := by
      apply Submodule.eq_of_le_of_finrank_le le_top
      rw [finrank_top,hqt,hq2]
    have hone := trivial_quotient_finrank_le_one x S.toSubmodule.mkQ
      S.toSubmodule.mkQ_surjective (G := G) (by
        intro g f
        have hf : S.toSubmodule.mkQ f∈(quotientRepresentation S).invariants := by
          rw [hfull]
          exact Submodule.mem_top
        exact hf g)
    omega
  have hsfixed : Module.finrank (ZMod 2) S.toRepresentation.invariants=1 := by omega
  have hfull : S.toRepresentation.invariants=⊤ := by
    apply Submodule.eq_of_le_of_finrank_le le_top
    rw [finrank_top,hsdim,hsfixed]
  have hle : S.toSubmodule≤(permutationFunctionRepresentation (ZMod 2) G X).invariants := by
    intro f hf g
    have hh : (⟨f,hf⟩ : S.toSubmodule)∈S.toRepresentation.invariants := by
      rw [hfull]
      exact Submodule.mem_top
    exact congrArg Subtype.val (hh g)
  have he : S.toSubmodule=(permutationFunctionRepresentation (ZMod 2) G X).invariants := by
    apply Submodule.eq_of_le_of_finrank_le hle
    rw [invariants_finrank x,hsdim]
  exact ⟨hsdim,he,by omega⟩

end Four
end SymmetricSubgroupAsymptotics.PermutationBinaryFourSection
