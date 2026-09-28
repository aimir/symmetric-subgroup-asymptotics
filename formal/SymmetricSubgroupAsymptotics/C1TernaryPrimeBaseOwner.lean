import SymmetricSubgroupAsymptotics.DegreeTwelveCoherentTernaryCoordinates
import SymmetricSubgroupAsymptotics.TernaryA4SectionRegularEmbedding

/-!
# A nonsplit prime-base owner with all original normal axes retained

The witness consists only of the original onto natural-A4 top map and
injective equivariant coordinates on its actual ternary kernel. No chosen
complement, factorization of original group elements, or full-product
kernel equality is part of this owner predicate.

For every original normal subgroup N, the denominator is the literal image
of N intersected with the actual kernel. The resulting invariant section
has the descended regular-module embedding for each quotient action that
factors the original A4 action. This is structural owner data; no counting
or physical-weight theorem is asserted in this module.
-/

set_option autoImplicit false
noncomputable section
open scoped Classical

namespace SymmetricSubgroupAsymptotics

open TernaryA4InvariantSubmodules

/-- Minimal prime-base geometry on the original group. Proper correlated
kernel submodules are allowed; no classification of their image is needed. -/
structure C1TernaryPrimeBaseOwnerWitness (G : Type*) [Group G] where
  top : G →* A4
  top_surjective : Function.Surjective top
  coordinates : top.ker →* Multiplicative V
  coordinates_injective : Function.Injective coordinates
  coordinates_conjugation : ∀ (g : G) (k : top.ker),
    (coordinates (MulAut.conjNormal g k)).toAdd =
      coordinateAction (top g).1 (coordinates k).toAdd

def IsC1TernaryPrimeBaseOwner (G : Type*) [Group G] : Prop :=
  Nonempty (C1TernaryPrimeBaseOwnerWitness G)

namespace C1TernaryPrimeBaseOwnerWitness

variable {G : Type*} [Group G] (W : C1TernaryPrimeBaseOwnerWitness G)

def baseImage : Submodule Scalar V :=
  AddSubgroup.toZModSubmodule 3 (Subgroup.toAddSubgroup' W.coordinates.range)

@[simp] theorem mem_baseImage (v : V) :
    v ∈ W.baseImage ↔ ∃ k : W.top.ker, W.coordinates k = Multiplicative.ofAdd v := Iff.rfl

theorem baseImage_invariant : Invariant W.baseImage := by
  intro g hg v hv
  obtain ⟨a, ha⟩ := W.top_surjective ⟨g, hg⟩
  obtain ⟨k, hk⟩ := (W.mem_baseImage v).mp hv
  apply (W.mem_baseImage _).mpr
  refine ⟨MulAut.conjNormal a k, ?_⟩
  apply Multiplicative.toAdd.injective
  rw [W.coordinates_conjugation, ha]
  exact congrArg (coordinateAction g) (congrArg Multiplicative.toAdd hk)

/-- The original normal-axis intersection, without replacing it by an
arbitrary invariant submodule or discarding its physical correlations. -/
def axisCoordinates (N : Subgroup G) :
    (N ⊓ W.top.ker : Subgroup G) →* Multiplicative V :=
  W.coordinates.comp (Subgroup.inclusion inf_le_right)

def axisImage (N : Subgroup G) : Submodule Scalar V :=
  AddSubgroup.toZModSubmodule 3 (Subgroup.toAddSubgroup' (W.axisCoordinates N).range)

@[simp] theorem mem_axisImage (N : Subgroup G) (v : V) :
    v ∈ W.axisImage N ↔
      ∃ k : (N ⊓ W.top.ker : Subgroup G),
        W.axisCoordinates N k = Multiplicative.ofAdd v := Iff.rfl

theorem axisImage_le_baseImage (N : Subgroup G) : W.axisImage N ≤ W.baseImage := by
  intro v hv
  obtain ⟨k, hk⟩ := (W.mem_axisImage N v).mp hv
  exact (W.mem_baseImage v).mpr ⟨⟨(k : G), k.2.2⟩, hk⟩

/-- The section denominator records membership in the whole original N.
No assumption that N lies in the top kernel is made. -/
theorem coordinates_mem_axisImage_iff (N : Subgroup G) (k : W.top.ker) :
    (W.coordinates k).toAdd ∈ W.axisImage N ↔ (k : G) ∈ N := by
  constructor
  · intro hk
    obtain ⟨l, hl⟩ := (W.mem_axisImage N _).mp hk
    change W.coordinates (⟨(l : G), l.2.2⟩ : W.top.ker) = W.coordinates k at hl
    have he := congrArg (fun x : W.top.ker => (x : G)) (W.coordinates_injective hl)
    have he' : (l : G) = (k : G) := he
    exact he' ▸ l.2.1
  · intro hk
    exact (W.mem_axisImage N _).mpr ⟨⟨(k : G), hk, k.2⟩, rfl⟩

def coordinateVector (k : W.top.ker) : W.baseImage :=
  ⟨(W.coordinates k).toAdd, (W.mem_baseImage _).mpr ⟨k, rfl⟩⟩

/-- The same literal invariant section used by the regular embedding. -/
abbrev axisSection (N : Subgroup G) :=
  TernaryA4SectionRegularEmbedding.Section W.baseImage (W.axisImage N)

/-- The section projection has exactly the original intersection as its
kernel, including when N has a nontrivial image in the A4 top. -/
theorem axisSection_mk_eq_zero_iff (N : Subgroup G) (k : W.top.ker) :
    TernaryA4SectionRegularEmbedding.sectionMk W.baseImage (W.axisImage N)
      (W.coordinateVector k) = 0 ↔ (k : G) ∈ N := by
  rw [TernaryA4SectionRegularEmbedding.sectionMk, Submodule.mkQ_apply,
    Submodule.Quotient.mk_eq_zero]
  exact W.coordinates_mem_axisImage_iff N k

theorem axisImage_invariant (N : Subgroup G) [N.Normal] : Invariant (W.axisImage N) := by
  intro g hg v hv
  obtain ⟨a, ha⟩ := W.top_surjective ⟨g, hg⟩
  obtain ⟨k, hk⟩ := (W.mem_axisImage N v).mp hv
  apply (W.mem_axisImage N _).mpr
  refine ⟨MulAut.conjNormal a k, ?_⟩
  apply Multiplicative.toAdd.injective
  change (W.coordinates (MulAut.conjNormal a (⟨(k : G), k.2.2⟩ : W.top.ker))).toAdd = _
  rw [W.coordinates_conjugation, ha]
  exact congrArg (coordinateAction g) (congrArg Multiplicative.toAdd hk)

/-- Every original normal axis is retained in the section to which the
regular embedding applies. The quotient action is checked on all original
section representatives, and no group splitting is required. -/
theorem axis_descended_regular_embedding (N : Subgroup G) [N.Normal]
    {Q : Type*} [Group Q] (β : A4 →* Q) (hβ : Function.Surjective β)
    (ρ : Representation Scalar Q
      (TernaryA4SectionRegularEmbedding.Section W.baseImage (W.axisImage N)))
    (hρ : TernaryA4SectionRegularEmbedding.FactorsSection W.baseImage (W.axisImage N)
      W.baseImage_invariant β ρ) :
    ∃ F : ρ.IntertwiningMap (Representation.leftRegular Scalar Q), Function.Injective F :=
  TernaryA4SectionRegularEmbedding.descended_groupAlgebra_embedding
    W.baseImage (W.axisImage N) W.baseImage_invariant (W.axisImage_invariant N) β hβ ρ hρ

end C1TernaryPrimeBaseOwnerWitness

namespace DegreeTwelveCoherentTernaryCoordinates

variable {A X : Type} [Group A] [MulAction A X]

/-- The original top, with codomain restricted to its proved literal A4
image. This map is onto and retains exactly the original top kernel. -/
def a4Top (r : X ≃ Fin 4)
    (hr : labelledActionImage (A := A) r = alternatingGroup (Fin 4)) : A →* A4 :=
  (labelledActionHom r).codRestrict A4 (fun a => by
    change labelledActionHom r a ∈ alternatingGroup (Fin 4)
    rw [← hr]
    exact ⟨a, rfl⟩)

theorem a4Top_surjective (r : X ≃ Fin 4)
    (hr : labelledActionImage (A := A) r = alternatingGroup (Fin 4)) :
    Function.Surjective (a4Top r hr) := by
  intro g
  have hg := g.2
  change (g : Equiv.Perm (Fin 4)) ∈ alternatingGroup (Fin 4) at hg
  rw [← hr] at hg
  obtain ⟨a, ha⟩ := hg
  exact ⟨a, Subtype.ext ha⟩

theorem a4Top_kernel (r : X ≃ Fin 4)
    (hr : labelledActionImage (A := A) r = alternatingGroup (Fin 4)) :
    (a4Top r hr).ker = OriginalBlockClassBound.Kernel (A := A) (X := X) := by
  ext a
  constructor
  · intro ha
    apply r.permCongrHom.injective
    change r.permCongr (MulAction.toPermHom A X a) = r.permCongr 1
    have h : r.permCongr (MulAction.toPermHom A X a) = 1 := congrArg Subtype.val ha
    exact h.trans (map_one r.permCongrHom).symm
  · intro ha
    apply Subtype.ext
    change r.permCongr (MulAction.toPermHom A X a) = 1
    change MulAction.toPermHom A X a = 1 at ha
    rw [ha]
    exact map_one r.permCongrHom

variable {Ω : Type} [MulAction A Ω] [FaithfulSMul A Ω]
variable (b : Ω → X) (hb : ∀ (a : A) (ω : Ω), b (a • ω) = a • b ω)
variable [∀ x : X, Fintype (originalBlockFibre b x)]

/-- Actual coherent coordinates install the nonsplit prime-base witness.
No diagonal/full assumption is needed by the regular-embedding argument. -/
def primeBaseOwnerOfCoordinates (r : X ≃ Fin 4)
    (hr : labelledActionImage (A := A) r = alternatingGroup (Fin 4))
    (e : ∀ x : X, Fin 3 ≃ originalBlockFibre b x)
    (hSigns : DegreeThreeBlockInversionHead.coordinateSigns b hb = 1)
    (he : Coherent b hb e) : C1TernaryPrimeBaseOwnerWitness A where
  top := a4Top r hr
  top_surjective := a4Top_surjective r hr
  coordinates := subgroupCoordinates b hb r e hSigns (a4Top r hr).ker
    (a4Top_kernel r hr).le
  coordinates_injective := (kernelCoordinates_injective b hb r e hSigns).comp
    (Subgroup.inclusion_injective (a4Top_kernel r hr).le)
  coordinates_conjugation a k := subgroupCoordinates_conjugation b hb r e hSigns he
    (a4Top r hr).ker (a4Top_kernel r hr).le a k

end DegreeTwelveCoherentTernaryCoordinates

namespace OriginalMinimalBlock

variable {A Ω : Type} [Group A] [MulAction A Ω]
variable [MulAction.IsPretransitive A Ω] {ω₀ : Ω}
variable (D : OriginalMinimalBlock (A := A) ω₀)

/-- A strict original relative-head gain kills the fibre signs. Coherent
coordinates then install the owner without any diagonal/full classification
or choice of a complement of the original kernel. -/
theorem ternaryA4_primeBase_owner_of_rank_gt_top
    [Finite A] [Finite Ω] [FaithfulSMul A Ω] [Fintype D.Points]
    [∀ x : D.Points, Fintype (originalBlockFibre D.map x)]
    (N : Subgroup A) [N.Normal]
    (hFibre : Nat.card D.Fibre = 3)
    (hTop : IsNaturalA4Action D.Top D.Points)
    (hRank : Module.finrank (ZMod 3)
        (primeRelativeCharacters 3 (originalNormalRange D.topMap N)) <
      Module.finrank (ZMod 3) (primeRelativeCharacters 3 N)) :
    IsC1TernaryPrimeBaseOwner A := by
  have hSigns := D.ternaryBlock_coordinateSigns_eq_one_of_rank_gt_top N hFibre hRank
  obtain ⟨r, hr⟩ := DegreeTwelveCoherentTernaryCoordinates.naturalTop_original_label hTop
  obtain ⟨e, he⟩ := DegreeTwelveCoherentTernaryCoordinates.exists_coherent_charts
    D.map D.map_equivariant D.base (D.ternaryFibreCharts hFibre D.base) hTop hSigns
  exact ⟨DegreeTwelveCoherentTernaryCoordinates.primeBaseOwnerOfCoordinates
    D.map D.map_equivariant r hr e hSigns he⟩

/-- The saturated original 3-by-4 branch installs the intrinsic prime-base
owner. All data belong to the original A, independently of catalogue names. -/
theorem degreeTwelve_primeBase_owner
    [Finite A] [Finite Ω] [FaithfulSMul A Ω] [Fintype D.Points]
    [∀ x : D.Points, Fintype (originalBlockFibre D.map x)]
    (N : Subgroup A) [N.Normal]
    (hFibre : Nat.card D.Fibre = 3)
    (hTop : IsNaturalA4Action D.Top D.Points)
    (hOriginalRank : Module.finrank (ZMod 3) (primeRelativeCharacters 3 N) = 2)
    (hTopRank : Module.finrank (ZMod 3)
      (primeRelativeCharacters 3 (originalNormalRange D.topMap N)) = 1) :
    IsC1TernaryPrimeBaseOwner A :=
  D.ternaryA4_primeBase_owner_of_rank_gt_top N hFibre hTop
    (by rw [hOriginalRank, hTopRank]; decide)

end OriginalMinimalBlock
end SymmetricSubgroupAsymptotics

end
