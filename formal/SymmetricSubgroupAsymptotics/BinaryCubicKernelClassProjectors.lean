import SymmetricSubgroupAsymptotics.ModuleGeneratorFiniteSubgroupAverageSharing
import SymmetricSubgroupAsymptotics.RepresentationGeneratorRestrictionMaschke
import SymmetricSubgroupAsymptotics.BinaryPlaneNontrivialCubicFixedFree
import Mathlib.GroupTheory.PGroup

/-! Kernel-class projectors for an ACTUAL correlated cubic diagonal group.
Averages are constructed from its local projection kernels. Two colors
within each kernel class give two global seeds, shared across all classes.
No common fixed-free cubic element is required. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
open scoped Classical BigOperators MonoidAlgebra
attribute [local instance] Fintype.ofFinite

namespace SymmetricSubgroupAsymptotics.BinaryCubicKernelClassProjectors
open BinaryPlanePermutationAffineEquiv

variable {O I : Type} [Group O] [Finite O] [Fintype I] [DecidableEq I]
  (rho : Representation (ZMod 2) O (I → Plane))
  (L : I → O →* Linear)
  (happly : ∀ g v i, rho g v i=L i g (v i))

def localKernel (i : I) : Subgroup O := (L i).ker

private theorem average_formula (D : Subgroup O)
    [Invertible (Fintype.card D : ZMod 2)] (v : I → Plane) :
    (Representation.averageMap (rho.comp D.subtype)) v=
      ⅟(Fintype.card D : ZMod 2) • ∑ g : D, rho (g : O) v := by
  simp [Representation.averageMap,GroupAlgebra.average,map_sum,
    Representation.asAlgebraHom_of,LinearMap.smul_apply,Finset.sum_apply]

include happly in
private theorem average_coordinate_same (i j : I)
    [Invertible (Fintype.card (localKernel L i) : ZMod 2)]
    (he : localKernel L i=localKernel L j) (v : I → Plane) :
    ((Representation.averageMap (rho.comp (localKernel L i).subtype)) v) j=v j := by
  have htriv (g : localKernel L i) : L j (g : O)=1 := by
    have hg : (g : O)∈localKernel L j := he ▸ g.property
    exact hg
  rw [average_formula]
  change ⅟(Fintype.card (localKernel L i) : ZMod 2) •
    (∑ g : localKernel L i, rho (g : O) v) j=v j
  simp only [Finset.sum_apply,happly,htriv]
  change ⅟(Fintype.card (localKernel L i) : ZMod 2) •
    (∑ _g : localKernel L i, v j)=v j
  rw [Finset.sum_const,Finset.card_univ,← Nat.cast_smul_eq_nsmul (ZMod 2),
    smul_smul,invOf_mul_self,one_smul]

include happly in
private theorem average_coordinate_different (i j : I)
    [Invertible (Fintype.card (localKernel L i) : ZMod 2)]
    (hcubic : ∀ i g, L i g ^ 3=1)
    (hcards : ∀ i j, Nat.card (localKernel L i)=Nat.card (localKernel L j))
    (he : localKernel L i≠localKernel L j) (v : I → Plane) :
    ((Representation.averageMap (rho.comp (localKernel L i).subtype)) v) j=0 := by
  have hnot : ¬ localKernel L i≤localKernel L j := by
    intro hle
    exact he (Subgroup.eq_of_le_of_card_ge hle (by rw [hcards i j]))
  obtain ⟨g,hgi,hgj⟩ := Set.not_subset.mp hnot
  let h : localKernel L i := ⟨g,hgi⟩
  let w := (Representation.averageMap (rho.comp (localKernel L i).subtype)) v
  have hw := (Representation.averageMap_invariant (rho.comp (localKernel L i).subtype)) v h
  have hj := congrFun hw j
  change rho g w j=w j at hj
  rw [happly] at hj
  exact BinaryPlaneNontrivialCubicFixedFree.fixedFree (L j g) (hcubic j g) hgj (w j) hj

private theorem cubic_card_cast_one (hO : IsPGroup 3 O) (D : Subgroup O) :
    (Fintype.card D : ZMod 2)=1 := by
  letI : Fact (Nat.Prime 3) := ⟨by decide⟩
  obtain ⟨n,hn⟩ := (hO.to_subgroup D).exists_card_eq
  rw [← Nat.card_eq_fintype_card,hn,Nat.cast_pow,
    show ((3 : ℕ) : ZMod 2)=1 by decide +kernel,one_pow]

private def e0 : Plane := ![1,0]
private def e1 : Plane := ![0,1]

private theorem plane_alternative : ∀ v : Plane, v≠0 → v≠e0 →
    ∃ c : ZMod 2, v=e1+c • e0 := by decide +kernel

private theorem plane_decomposition (v : Plane) : v=v 0 • e0+v 1 • e1 := by
  funext i
  fin_cases i <;> simp [e0,e1]

include happly in
/-- Color classes are actual coordinate classes, not independent local
factors. The averages over their actual kernels are the projectors. -/
theorem generatedBy_two (hO : IsPGroup 3 O)
    (hcubic : ∀ i g, L i g ^ 3=1)
    (hnonzero : ∀ i, ∃ g, L i g≠1)
    (hcards : ∀ i j, Nat.card (localKernel L i)=Nat.card (localKernel L j))
    (color : I → Fin 2)
    (hcolor : ∀ i j, localKernel L i=localKernel L j → color i=color j → i=j) :
    RepresentationGeneratedBy rho 2 := by
  let seed : Fin 2 → I → Plane := fun c i => if color i=c then e0 else 0
  let code : Fin 2 → rho.asModule := fun c => rho.asModuleEquiv.symm (seed c)
  let P : Submodule (ZMod 2)[O] rho.asModule :=
    Submodule.span (ZMod 2)[O] (Set.range code)
  let W : Subrepresentation rho := Subrepresentation.ofSubmodule' P
  have hseed (c : Fin 2) : seed c∈W := by
    change rho.asModuleEquiv.symm (seed c)∈P
    exact Submodule.subset_span ⟨c,rfl⟩
  have hsingle0 (i : I) : Pi.single i e0∈W := by
    let D := localKernel L i
    letI : Invertible (Fintype.card D : ZMod 2) :=
      invertibleOfNonzero (by rw [cubic_card_cast_one hO D]; exact one_ne_zero)
    have havg : (Representation.averageMap (rho.comp D.subtype)) (seed (color i))∈W := by
      rw [average_formula]
      exact W.toSubmodule.smul_mem _ (W.toSubmodule.sum_mem
        (fun g _ => W.apply_mem_toSubmodule (g : O) (hseed (color i))))
    have heq : (Representation.averageMap (rho.comp D.subtype)) (seed (color i))=Pi.single i e0 := by
      funext j
      by_cases he : localKernel L i=localKernel L j
      · rw [average_coordinate_same rho L happly i j he]
        by_cases hc : color j=color i
        · have hji : j=i := hcolor j i he.symm hc
          subst j
          simp [seed]
        · have hji : j≠i := fun h => hc (congrArg color h)
          simp only [seed,hc,if_false,Pi.single_eq_of_ne hji]
      · rw [average_coordinate_different rho L happly i j hcubic hcards he]
        have hji : j≠i := by intro h; subst j; exact he rfl
        rw [Pi.single_eq_of_ne hji]
    rwa [heq] at havg
  have hsingle (i : I) (v : Plane) : Pi.single i v∈W := by
    obtain ⟨g,hg⟩ := hnonzero i
    have hact : rho g (Pi.single i e0)=Pi.single i (L i g e0) := by
      funext j
      rw [happly]
      by_cases hj : j=i
      · subst j; rw [Pi.single_eq_same,Pi.single_eq_same]
      · rw [Pi.single_eq_of_ne hj,Pi.single_eq_of_ne hj,map_zero]
    have hmem := W.apply_mem_toSubmodule g (hsingle0 i)
    rw [hact] at hmem
    have hn : L i g e0≠0 := by
      intro h
      exact (by decide +kernel : e0≠0)
        ((L i g).injective (h.trans (map_zero (L i g)).symm))
    have he : L i g e0≠e0 := by
      intro h
      exact (by decide +kernel : e0≠0)
        (BinaryPlaneNontrivialCubicFixedFree.fixedFree (L i g) (hcubic i g) hg e0 h)
    obtain ⟨c,hc⟩ := plane_alternative (L i g e0) hn he
    have hsingle1 : Pi.single i e1∈W := by
      have hm := W.toSubmodule.sub_mem hmem (W.toSubmodule.smul_mem c (hsingle0 i))
      have hc' : L i g e0-c • e0=e1 := by rw [hc,add_sub_cancel_right]
      rw [← Pi.single_smul,← Pi.single_sub,hc'] at hm
      exact hm
    have hm := W.toSubmodule.add_mem
      (W.toSubmodule.smul_mem (v 0) (hsingle0 i))
      (W.toSubmodule.smul_mem (v 1) hsingle1)
    rw [← Pi.single_smul,← Pi.single_smul,← Pi.single_add,← plane_decomposition v] at hm
    exact hm
  refine ⟨code,top_unique ?_⟩
  intro v _
  have hm := W.toSubmodule.sum_mem (fun i (_ : i∈Finset.univ) =>
    hsingle i (rho.asModuleEquiv v i))
  rw [LinearMap.sum_single_apply] at hm
  exact hm

include happly in
/-- Odd-group semisimplicity is used only AFTER the explicit ambient
seeds/projectors are constructed, so every actual section inherits two. -/
theorem uniform_two (hO : IsPGroup 3 O)
    (hcubic : ∀ i g, L i g ^ 3=1)
    (hnonzero : ∀ i, ∃ g, L i g≠1)
    (hcards : ∀ i j, Nat.card (localKernel L i)=Nat.card (localKernel L j))
    (color : I → Fin 2)
    (hcolor : ∀ i j, localKernel L i=localKernel L j → color i=color j → i=j) :
    UniformSubrepresentationGeneratorBound rho 2 := by
  letI : NeZero (Nat.card O : ZMod 2) := ⟨by
    rw [Nat.card_eq_fintype_card]
    have h := cubic_card_cast_one hO (⊤ : Subgroup O)
    have he : Nat.card (⊤ : Subgroup O)=Nat.card O := Subgroup.card_top
    rw [← Nat.card_eq_fintype_card,he,Nat.card_eq_fintype_card] at h
    rw [h]
    exact one_ne_zero⟩
  exact RepresentationGeneratedBy.uniform_of_invertible_order rho
    (generatedBy_two rho L happly hO hcubic hnonzero hcards color hcolor)

end SymmetricSubgroupAsymptotics.BinaryCubicKernelClassProjectors
