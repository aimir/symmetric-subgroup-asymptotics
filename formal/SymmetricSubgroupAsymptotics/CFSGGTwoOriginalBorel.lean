import SymmetricSubgroupAsymptotics.CFSGGTwoOriginalPositiveTorusAction
import SymmetricSubgroupAsymptotics.CFSGGTwoOriginalWeylTorusAction
import SymmetricSubgroupAsymptotics.CFSGGTwoSimpleBruhatComplement
import Mathlib.Algebra.Group.Subgroup.Pointwise

/-! The actual ordinary rank-two Borel U6*T2 in the SAME original Model.
Its factorization and simple complements are derived from explicit word
normalization. No fixed-Ree Borel, Bruhat cover or BN-pair is assumed. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
open scoped Pointwise
namespace SymmetricSubgroupAsymptotics.CFSGGTwoOriginalBorel
open CFSG.Models.Chevalley CFSGSerreModelRootGeneration
open CFSGGTwoOriginalRankTwoTorus CFSGGTwoOriginalPositiveTorusAction
open CFSGGTwoOriginalWeylTorusAction CFSGGTwoNaturalWeylTorusAction
open CFSGGTwoOriginalPositiveRootWords CFSGGTwoOriginalWeylSquares
open CFSGGTwoPositiveSixWord CFSGGTwoPositiveWordSubgroup
open CFSGGTwoPositiveCoordinateKernels CFSGGTwoSimpleBruhatComplement
variable (K : Type) [Field K] [CharP K 3]
local notation "A" => CartanMatrix.G₂

private theorem undo_conjugation {G : Type*} [Group G] (t g : G) :
    t⁻¹*(t*g*t⁻¹)*t=g := by group

private theorem double_conjugation {G : Type*} [Group G] (t g : G) :
    t*(t*g*t⁻¹)*t⁻¹=(t*t)*g*(t*t)⁻¹ := by group

private theorem normalizes_of_square {G : Type*} [Group G] (H : Subgroup G) (s : G)
    (hs : s*s∈H) (hc : ∀ g∈H,s*g*s⁻¹∈H) : s∈Subgroup.normalizer H := by
  apply Subgroup.mem_normalizer_iff.mpr
  intro g
  constructor
  · exact hc g
  · intro hg
    have h2 := hc _ hg
    rw [double_conjugation] at h2
    have h3 := H.mul_mem (H.mul_mem (H.inv_mem hs) h2) hs
    simpa only [undo_conjugation] using h3

def torus : Subgroup (Model A K) := (torusHom K).range

def borel : Subgroup (Model A K) := positiveWordGroup K⊔torus K

theorem positive_le_borel : positiveWordGroup K≤borel K := le_sup_left

theorem torus_le_borel : torus K≤borel K := le_sup_right

omit [CharP K 3] in
private theorem torusPair_inverse (t : Kˣ × Kˣ) :
    torusPair K t⁻¹=(torusPair K t)⁻¹ := by
  simpa only [torusHom_apply] using map_inv (torusHom K) t

theorem torusPair_conj_positive (t : Kˣ × Kˣ) (g : Model A K)
    (hg : g∈positiveWordGroup K) :
    torusPair K t*g*(torusPair K t)⁻¹∈positiveWordGroup K := by
  obtain ⟨x,rfl⟩ := hg
  exact ⟨scaleCoordinates K t x,(torusPair_modelWord K t x).symm⟩

theorem torus_le_positive_normalizer : torus K≤Subgroup.normalizer (positiveWordGroup K) := by
  rintro _ ⟨t,rfl⟩
  rw [torusHom_apply]
  apply Subgroup.mem_normalizer_iff.mpr
  intro g
  constructor
  · exact torusPair_conj_positive K t g
  · intro hg
    have hh := torusPair_conj_positive K t⁻¹ _ hg
    rw [torusPair_inverse] at hh
    simpa only [inv_inv,undo_conjugation] using hh

theorem borel_factor (g : Model A K) (hg : g∈borel K) :
    ∃ u∈positiveWordGroup K,∃ t∈torus K,g=u*t := by
  have he : (borel K:Set (Model A K))=
      (positiveWordGroup K:Set (Model A K))*(torus K:Set (Model A K)) :=
    Subgroup.coe_mul_of_right_le_normalizer_left _ _ (torus_le_positive_normalizer K)
  change g∈(borel K:Set (Model A K)) at hg
  rw [he] at hg
  obtain ⟨u,hu,t,ht,hm⟩ := hg
  exact ⟨u,hu,t,ht,hm.symm⟩

theorem simple_factor (i : Fin 2) (g : Model A K) (hg : g∈borel K) :
    ∃ v∈complement K i,∃ a : K,∃ t∈torus K,
      g=v*positiveModel K (simpleIndex i) a*t := by
  obtain ⟨u,hu,t,ht,hg⟩ := borel_factor K g hg
  obtain ⟨v,hv,a,ha⟩ := factor_positive K i ⟨u,hu⟩
  exact ⟨v,hv,a,t,ht,hg.trans (congrArg (fun z : Model A K => z*t) ha)⟩

omit [CharP K 3] in
private theorem torusNode_one (i : Fin 2) : torusNode K i 1=1 := by
  have h : weylParameter K i (-1)=(weylParameter K i 1)⁻¹ := by
    simp [weylParameter,mul_inv_rev,CFSGGTwoOriginalPositiveRootWords.modelRoot_inv,mul_assoc]
  simp only [torusNode,h,mul_inv_cancel]

theorem torusNode_mem (i : Fin 2) (c : Kˣ) : torusNode K i c∈torus K := by
  fin_cases i
  · refine ⟨(c,1),?_⟩
    simp only [torusHom_apply,torusPair,torusNode_one,mul_one]
    rfl
  · refine ⟨(1,c),?_⟩
    simp only [torusHom_apply,torusPair,torusNode_one,one_mul]
    rfl

theorem simple_square_mem_torus (i : Fin 2) : simpleWeyl K i*simpleWeyl K i∈torus K := by
  fin_cases i
  · change shortWord K*shortWord K∈torus K
    rw [shortWord_square]
    exact torusNode_mem K 0 (-1)
  · change longWord K*longWord K∈torus K
    rw [longWord_square]
    exact torusNode_mem K 1 (-1)

theorem simple_square_mem_borel (i : Fin 2) : simpleWeyl K i*simpleWeyl K i∈borel K :=
  torus_le_borel K (simple_square_mem_torus K i)

theorem short_torus_normalizer : shortWord K∈Subgroup.normalizer (torus K) := by
  apply normalizes_of_square (torus K) (shortWord K)
  · simpa only [shortWord_square] using torusNode_mem K 0 (-1)
  · rintro _ ⟨t,rfl⟩
    rw [torusHom_apply,shortWord_torusPair]
    exact ⟨shortTransform K t,torusHom_apply K _⟩

theorem long_torus_normalizer : longWord K∈Subgroup.normalizer (torus K) := by
  apply normalizes_of_square (torus K) (longWord K)
  · simpa only [longWord_square] using torusNode_mem K 1 (-1)
  · rintro _ ⟨t,rfl⟩
    rw [torusHom_apply,longWord_torusPair]
    exact ⟨longTransform K t,torusHom_apply K _⟩

theorem simple_torus_normalizer (i : Fin 2) :
    simpleWeyl K i∈Subgroup.normalizer (torus K) := by
  fin_cases i
  · exact short_torus_normalizer K
  · exact long_torus_normalizer K

end SymmetricSubgroupAsymptotics.CFSGGTwoOriginalBorel
