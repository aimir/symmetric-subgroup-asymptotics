import SymmetricSubgroupAsymptotics.BinaryInvariantCyclicGeneratorBound
import SymmetricSubgroupAsymptotics.RepresentationDualSubquotientGenerators

/-!
# Generators across a short exact sequence of representations

The pair-top tower has a natural permutation module with a stable
pair-constant submodule and a pair-sum quotient.  This file isolates the
general algebra needed there: generator bounds add across a short exact
sequence, and therefore uniform subrepresentation-generator bounds add
across an exact extension.

No splitting is chosen.  In particular, this applies to the nonsplit
defining-characteristic permutation modules occurring in the paired-eight
rows.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
open scoped Classical MonoidAlgebra

namespace SymmetricSubgroupAsymptotics

variable {k G A B C : Type*} [Field k] [Group G]
  [AddCommGroup A] [Module k A]
  [AddCommGroup B] [Module k B]
  [AddCommGroup C] [Module k C]

namespace RepresentationGeneratedBy

/-- Pulling a representation back along a surjective group map does not
change the number of module generators: the acting image is unchanged. -/
theorem comp_of_surjective
    {H : Type*} [Group H]
    (rho : Representation k G B)
    (f : H →* G) (hf : Function.Surjective f)
    {n : ℕ}
    (hgen : RepresentationGeneratedBy rho n) :
    RepresentationGeneratedBy (rho.comp f) n := by
  let rhoH : Representation k H B := rho.comp f
  obtain ⟨v, hv⟩ := hgen
  let w : Fin n → rhoH.asModule := fun j ↦
    rhoH.asModuleEquiv.symm (rho.asModuleEquiv (v j))
  let W : Submodule k[H] rhoH.asModule :=
    Submodule.span k[H] (Set.range w)
  let MH : Subrepresentation rhoH := Subrepresentation.ofSubmodule' W
  let MG : Subrepresentation rho :=
    { toSubmodule := MH.toSubmodule
      apply_mem_toSubmodule := by
        intro g x hx
        obtain ⟨h, rfl⟩ := hf g
        exact MH.apply_mem_toSubmodule h hx }
  have hle : Submodule.span k[G] (Set.range v) ≤ MG.asSubmodule := by
    apply Submodule.span_le.mpr
    rintro _ ⟨j, rfl⟩
    change rhoH.asModuleEquiv.symm (rho.asModuleEquiv (v j)) ∈ W
    exact Submodule.subset_span ⟨j, rfl⟩
  have hMG : MG.asSubmodule = ⊤ := by
    rw [hv] at hle
    exact top_unique hle
  refine ⟨w, ?_⟩
  change W = ⊤
  apply SetLike.ext
  intro x
  have hx : x ∈ MG.toSubmodule ↔ x ∈ (⊤ : Submodule k B) := by
    rw [hMG]
  simpa only [Submodule.mem_top] using hx

/-- Generators of the two ends of a short exact sequence, lifted arbitrarily
at the right end, together generate the middle representation. -/
theorem of_exact
    (sigma : Representation k G A)
    (rho : Representation k G B)
    (tau : Representation k G C)
    (i : sigma.IntertwiningMap rho)
    (q : rho.IntertwiningMap tau)
    (hi : Function.Injective i)
    (hq : Function.Surjective q)
    (hexact : LinearMap.range
        (Representation.IntertwiningMap.equivLinearMapAsModule sigma rho i) =
      LinearMap.ker
        (Representation.IntertwiningMap.equivLinearMapAsModule rho tau q))
    {m n : ℕ}
    (hsigma : RepresentationGeneratedBy sigma m)
    (htau : RepresentationGeneratedBy tau n) :
    RepresentationGeneratedBy rho (m + n) := by
  let I : sigma.asModule →ₗ[k[G]] rho.asModule :=
    Representation.IntertwiningMap.equivLinearMapAsModule sigma rho i
  let Q : rho.asModule →ₗ[k[G]] tau.asModule :=
    Representation.IntertwiningMap.equivLinearMapAsModule rho tau q
  have hQ : Function.Surjective Q := hq
  obtain ⟨a, ha⟩ := hsigma
  obtain ⟨c, hc⟩ := htau
  let lift : tau.asModule → rho.asModule := Function.surjInv hQ
  have hlift : Function.RightInverse lift Q :=
    Function.rightInverse_surjInv hQ
  let generator : Fin (m + n) → rho.asModule :=
    Fin.addCases (fun j ↦ I (a j)) (fun j ↦ lift (c j))
  let P : Submodule k[G] rho.asModule :=
    Submodule.span k[G] (Set.range generator)
  have hleft (j : Fin m) : I (a j) ∈ P := by
    apply Submodule.subset_span
    exact ⟨Fin.castAdd n j, by simp only [generator, Fin.addCases_left]⟩
  have hright (j : Fin n) : lift (c j) ∈ P := by
    apply Submodule.subset_span
    exact ⟨Fin.natAdd m j, by simp only [generator, Fin.addCases_right]⟩
  have hsource : ∀ x : sigma.asModule, I x ∈ P := by
    intro x
    have hx : x ∈ Submodule.span k[G] (Set.range a) := by
      rw [ha]
      exact Submodule.mem_top
    apply (show Submodule.span k[G] (Set.range a) ≤ P.comap I from ?_) hx
    apply Submodule.span_le.mpr
    rintro _ ⟨j, rfl⟩
    exact hleft j
  have hquotient : P.map Q = ⊤ := by
    apply top_unique
    rw [← hc]
    apply Submodule.span_le.mpr
    rintro _ ⟨j, rfl⟩
    refine ⟨lift (c j), hright j, ?_⟩
    exact hlift (c j)
  refine ⟨generator, top_unique ?_⟩
  intro x _hx
  have hxQ : Q x ∈ P.map Q := by
    rw [hquotient]
    exact Submodule.mem_top
  obtain ⟨y, hyP, hyQ⟩ := hxQ
  have hxyKer : x - y ∈ LinearMap.ker Q := by
    rw [LinearMap.mem_ker, map_sub, hyQ, sub_self]
  have hxyRange : x - y ∈ LinearMap.range I := by
    rw [hexact]
    exact hxyKer
  obtain ⟨z, hz⟩ := hxyRange
  have hzP : I z ∈ P := hsource z
  have hsum : (x - y) + y ∈ P := by
    rw [← hz]
    exact P.add_mem hzP hyP
  simpa only [sub_add_cancel] using hsum

end RepresentationGeneratedBy

/-- The inverse image of an invariant subrepresentation along an
intertwiner. -/
def intertwinerPreimage
    (sigma : Representation k G A)
    (rho : Representation k G B)
    (i : sigma.IntertwiningMap rho)
    (M : Subrepresentation rho) : Subrepresentation sigma where
  toSubmodule := M.toSubmodule.comap i.toLinearMap
  apply_mem_toSubmodule g x hx := by
    change i (sigma g x) ∈ M
    rw [Representation.IntertwiningMap.isIntertwining]
    exact M.apply_mem_toSubmodule g hx

/-- The image of an invariant subrepresentation along an intertwiner. -/
def intertwinerImage
    (rho : Representation k G B)
    (tau : Representation k G C)
    (q : rho.IntertwiningMap tau)
    (M : Subrepresentation rho) : Subrepresentation tau where
  toSubmodule := M.toSubmodule.map q.toLinearMap
  apply_mem_toSubmodule g y hy := by
    obtain ⟨x, hx, rfl⟩ := hy
    refine ⟨rho g x, M.apply_mem_toSubmodule g hx, ?_⟩
    exact Representation.IntertwiningMap.isIntertwining _ _ q g x

namespace UniformSubrepresentationGeneratorBound

/-- A uniform generator theorem pulls back along a surjective group map. -/
theorem comp_of_surjective
    {H : Type*} [Group H]
    (rho : Representation k G B)
    (f : H →* G) (hf : Function.Surjective f)
    {n : ℕ}
    (hgen : UniformSubrepresentationGeneratorBound rho n) :
    UniformSubrepresentationGeneratorBound (rho.comp f) n := by
  intro M
  let MG : Subrepresentation rho :=
    { toSubmodule := M.toSubmodule
      apply_mem_toSubmodule := by
        intro g x hx
        obtain ⟨h, rfl⟩ := hf g
        exact M.apply_mem_toSubmodule h hx }
  have h := RepresentationGeneratedBy.comp_of_surjective
    MG.toRepresentation f hf (hgen MG)
  simpa only [MG, Subrepresentation.toRepresentation] using h

/-- Uniform generator bounds add across a short exact sequence.  For an
invariant subrepresentation of the middle term, intersect with the left
term and take its image in the right term, then apply
`RepresentationGeneratedBy.of_exact` to that induced exact sequence. -/
theorem of_exact
    (sigma : Representation k G A)
    (rho : Representation k G B)
    (tau : Representation k G C)
    (i : sigma.IntertwiningMap rho)
    (q : rho.IntertwiningMap tau)
    (hi : Function.Injective i)
    (hexact : LinearMap.range
        (Representation.IntertwiningMap.equivLinearMapAsModule sigma rho i) =
      LinearMap.ker
        (Representation.IntertwiningMap.equivLinearMapAsModule rho tau q))
    {m n : ℕ}
    (hsigma : UniformSubrepresentationGeneratorBound sigma m)
    (htau : UniformSubrepresentationGeneratorBound tau n) :
    UniformSubrepresentationGeneratorBound rho (m + n) := by
  intro M
  let L : Subrepresentation sigma :=
    intertwinerPreimage sigma rho i M
  let R : Subrepresentation tau :=
    intertwinerImage rho tau q M
  let left : L.toRepresentation.IntertwiningMap M.toRepresentation :=
    { toLinearMap :=
        { toFun := fun x ↦ ⟨i x.1, x.2⟩
          map_add' := fun _ _ ↦ rfl
          map_smul' := fun _ _ ↦ rfl }
      isIntertwining' g := by
        apply LinearMap.ext
        intro x
        apply Subtype.ext
        exact Representation.IntertwiningMap.isIntertwining _ _ i g x.1 }
  let right : M.toRepresentation.IntertwiningMap R.toRepresentation :=
    { toLinearMap :=
        { toFun := fun x ↦ ⟨q x.1, ⟨x.1, x.2, rfl⟩⟩
          map_add' := fun _ _ ↦ rfl
          map_smul' := fun _ _ ↦ rfl }
      isIntertwining' g := by
        apply LinearMap.ext
        intro x
        apply Subtype.ext
        exact Representation.IntertwiningMap.isIntertwining _ _ q g x.1 }
  have hleft : Function.Injective left := by
    intro x y hxy
    apply Subtype.ext
    exact hi (congrArg Subtype.val hxy)
  have hright : Function.Surjective right := by
    intro y
    obtain ⟨x, hx, hxy⟩ := y.2
    refine ⟨⟨x, hx⟩, ?_⟩
    apply Subtype.ext
    exact hxy
  have hinducedExact : LinearMap.range
        (Representation.IntertwiningMap.equivLinearMapAsModule
          L.toRepresentation M.toRepresentation left) =
      LinearMap.ker
        (Representation.IntertwiningMap.equivLinearMapAsModule
          M.toRepresentation R.toRepresentation right) := by
    ext x
    constructor
    · rintro ⟨z, rfl⟩
      change q (i z.1) = 0
      have hiRange : i z.1 ∈ LinearMap.range
          (Representation.IntertwiningMap.equivLinearMapAsModule sigma rho i) :=
        ⟨z.1, rfl⟩
      rw [hexact] at hiRange
      exact hiRange
    · intro hx
      have hxKer : x.1 ∈ LinearMap.ker
          (Representation.IntertwiningMap.equivLinearMapAsModule rho tau q) := by
        exact congrArg Subtype.val hx
      rw [← hexact] at hxKer
      obtain ⟨z, hz⟩ := hxKer
      have hzL : z ∈ L := by
        change i z ∈ M
        rw [hz]
        exact x.2
      exact ⟨⟨z, hzL⟩, Subtype.ext hz⟩
  exact RepresentationGeneratedBy.of_exact
    L.toRepresentation M.toRepresentation R.toRepresentation
    left right hleft hright hinducedExact (hsigma L) (htau R)

end UniformSubrepresentationGeneratorBound

end SymmetricSubgroupAsymptotics

end
