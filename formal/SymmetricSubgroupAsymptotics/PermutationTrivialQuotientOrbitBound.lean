import SymmetricSubgroupAsymptotics.PermutationSubrepresentationHead
import SymmetricSubgroupAsymptotics.RepresentationCoinvariantHead
import SymmetricSubgroupAsymptotics.OriginalEquivariantQuotientEmbedding
import Mathlib.RepresentationTheory.Invariants

/-! A trivial quotient of an actual permutation subrepresentation is
bounded by the orbits of any one original acting element. The quotient
need not embed in the ambient permutation module. -/
set_option autoImplicit false
noncomputable section
namespace SymmetricSubgroupAsymptotics

variable {k G X W : Type} [Field k] [Group G] [Finite X]
    [MulAction G X] [AddCommGroup W] [Module k W]

/-- Retain the original submodule and the same actual quotient map. -/
theorem permutation_trivial_quotient_finrank_le_cyclic_orbits
    (M : Subrepresentation (permutationFunctionRepresentation k G X))
    (q : M.toSubmodule →ₗ[k] W) (hq : Function.Surjective q)
    (htrivial : ∀ (g : G) (m : M.toSubmodule),
      q (M.toRepresentation g m) = q m) (g : G) :
    Module.finrank k W ≤
      Nat.card (MulAction.orbitRel.Quotient (Subgroup.zpowers g) X) := by
  classical
  letI := Fintype.ofFinite X
  have hinvariant : ∀ a : G, q.comp (M.toRepresentation a) = q := by
    intro a
    apply LinearMap.ext
    exact htrivial a
  let q' : M.toRepresentation.Coinvariants →ₗ[k] W :=
    Representation.Coinvariants.lift M.toRepresentation q hinvariant
  have hq' : Function.Surjective q' := by
    intro w
    obtain ⟨m,hm⟩ := hq w
    exact ⟨Representation.Coinvariants.mk M.toRepresentation m,hm⟩
  have hdim : Module.finrank k W ≤
      Module.finrank k M.toRepresentation.Coinvariants :=
    LinearMap.finrank_le_finrank_of_surjective hq'
  rw [← representationHead_finrank_eq_coinvariants] at hdim
  exact hdim.trans (permutation_subrepresentationHead_le_cyclicOrbitCount M g)

/-- Original fixed functions descend to the actual orbit set. -/
def permutationInvariantsOrbitEval :
    (permutationFunctionRepresentation k G X).invariants →ₗ[k]
      (MulAction.orbitRel.Quotient G X → k) where
  toFun f := Quotient.lift (fun x : X => f.1 x) (by
    intro x y h
    obtain ⟨a,ha⟩ := h
    rw [← ha]
    have hf := congrFun (f.2 a⁻¹) y
    simpa only [permutationFunctionRepresentation_apply,inv_inv] using hf)
  map_add' f f' := by
    funext x
    refine Quotient.inductionOn x ?_
    intro y
    rfl
  map_smul' c f := by
    funext x
    refine Quotient.inductionOn x ?_
    intro y
    rfl

theorem permutationInvariantsOrbitEval_injective :
    Function.Injective (permutationInvariantsOrbitEval (k := k) (G := G) (X := X)) := by
  intro f f' h
  apply Subtype.ext
  funext x
  exact congrFun h (Quotient.mk (MulAction.orbitRel G X) x)

/-- An invertible-order acting group lets the SAME actual trivial quotient
embed in the original ambient fixed functions. No subgroup inheritance is
assumed, and the target does not receive independently chosen coordinates. -/
theorem permutation_trivial_quotient_finrank_le_orbits
    [Finite G] [NeZero (Nat.card G : k)]
    (M : Subrepresentation (permutationFunctionRepresentation k G X))
    (q : M.toSubmodule →ₗ[k] W) (hq : Function.Surjective q)
    (htrivial : ∀ (g : G) (m : M.toSubmodule),
      q (M.toRepresentation g m) = q m) :
    Module.finrank k W ≤ Nat.card (MulAction.orbitRel.Quotient G X) := by
  classical
  letI := Fintype.ofFinite X
  letI := Fintype.ofFinite (MulAction.orbitRel.Quotient G X)
  let f : M.toRepresentation.IntertwiningMap (Representation.trivial k G W) := {
    toLinearMap := q
    isIntertwining' := by
      intro g
      apply LinearMap.ext
      exact htrivial g }
  obtain ⟨i,hi⟩ := original_equivariant_quotient_embedding
    M.toRepresentation (Representation.trivial k G W) f hq
  let j : W →ₗ[k] (permutationFunctionRepresentation k G X).invariants := {
    toFun := fun w => ⟨(i w).1,by
      intro g
      have he := LinearMap.congr_fun (i.isIntertwining' g) w
      change i w = M.toRepresentation g (i w) at he
      exact (congrArg Subtype.val he).symm⟩
    map_add' := by
      intro x y
      apply Subtype.ext
      change ((i (x+y) : M.toSubmodule) : X → k) =
        ((i x : M.toSubmodule) : X → k) + ((i y : M.toSubmodule) : X → k)
      exact congrArg (fun z : M.toSubmodule => (z : X → k)) (i.map_add x y)
    map_smul' := by
      intro c x
      apply Subtype.ext
      change ((i (c • x) : M.toSubmodule) : X → k) =
        c • ((i x : M.toSubmodule) : X → k)
      exact congrArg (fun z : M.toSubmodule => (z : X → k)) (i.map_smul c x) }
  have hj : Function.Injective j := by
    intro x y h
    apply hi
    apply Subtype.ext
    have hh := congrArg (fun z : (permutationFunctionRepresentation k G X).invariants =>
      (z : X → k)) h
    change ((i x : M.toSubmodule) : X → k) = ((i y : M.toSubmodule) : X → k) at hh
    exact hh
  let he : W →ₗ[k] (MulAction.orbitRel.Quotient G X → k) :=
    (permutationInvariantsOrbitEval (k := k) (G := G) (X := X)).comp j
  have hinj : Function.Injective he := by
    intro x y h
    apply hj
    exact permutationInvariantsOrbitEval_injective (k := k) (G := G) (X := X)
      (show permutationInvariantsOrbitEval (j x) = permutationInvariantsOrbitEval (j y) from h)
  have hd := he.finrank_le_finrank_of_injective hinj
  simpa only [Module.finrank_pi,Nat.card_eq_fintype_card] using hd

end SymmetricSubgroupAsymptotics
end
