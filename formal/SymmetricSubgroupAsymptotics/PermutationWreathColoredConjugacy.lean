import SymmetricSubgroupAsymptotics.FiniteMultisetLabelMatching
import SymmetricSubgroupAsymptotics.PermutationCycleMatching
import SymmetricSubgroupAsymptotics.PermutationWreathBaseConjugacy
import Mathlib.Algebra.Group.Conj
import Mathlib.Tactic.Group

/-! Equal actual colored cycle data constructs a literal conjugator in
the full permutational wreath group. Both its top permutation and its
base potential are constructed, with no conjugacy classification premise. -/
set_option autoImplicit false
noncomputable section
open scoped Classical
namespace SymmetricSubgroupAsymptotics.PermutationWreathColoredConjugacy
open FiniteMultisetLabelMatching PermutationCycleDecomposition
  PermutationCycleCoboundary PermutationCycleMatching PermutationWreathBaseConjugacy
variable {D I : Type*} [CommGroup D] [Finite I]

def cycleLabels (σ : Equiv.Perm I) (f : I → D) (c : CycleIndex σ) : ℕ × D :=
  (cycleLength σ c,cycleProduct σ f c)

def coloredData (σ : Equiv.Perm I) (f : I → D) : Multiset (ℕ × D) := by
  letI : Fintype (CycleIndex σ) := Fintype.ofFinite _
  exact labelMultiset (cycleLabels σ f)

omit [Finite I] in
theorem top_conjugate_element (t σ : Equiv.Perm I) (f : I → D) :
    PermutationalWreathProduct.topHom t * element σ f *
        (PermutationalWreathProduct.topHom t)⁻¹=
      element (t*σ*t⁻¹) (fun i => f (t.symm i)) := by
  apply PermutationalWreathProduct.ext
  · funext i
    simp [PermutationalWreathProduct.topHom,element,
      PermutationalWreathProduct.mul_left,PermutationalWreathProduct.mul_right,
      PermutationalWreathProduct.inv_left]
  · simp [PermutationalWreathProduct.topHom,element,
      PermutationalWreathProduct.mul_right,PermutationalWreathProduct.inv_right,
      mul_inv_rev,mul_assoc]

theorem coloredData_eq_exists_conjugator (σ τ : Equiv.Perm I) (f g : I → D)
    (h : coloredData σ f=coloredData τ g) :
    ∃a : Wreath D I,a * element σ f * a⁻¹=element τ g := by
  letI : Fintype (CycleIndex σ) := Fintype.ofFinite _
  letI : Fintype (CycleIndex τ) := Fintype.ofFinite _
  have hlabel : labelMultiset (cycleLabels σ f)=labelMultiset (cycleLabels τ g) := h
  let e := matchingEquiv (cycleLabels σ f) (cycleLabels τ g) hlabel
  have he (c : CycleIndex σ) : cycleLabels τ g (e c)=cycleLabels σ f c :=
    matchingEquiv_spec (cycleLabels σ f) (cycleLabels τ g) hlabel c
  have hlen (c : CycleIndex σ) : cycleLength σ c=cycleLength τ (e c) :=
    (congrArg Prod.fst (he c)).symm
  have hprod (c : CycleIndex σ) : cycleProduct σ f c=cycleProduct τ g (e c) :=
    (congrArg Prod.snd (he c)).symm
  let t := pointEquiv σ τ e hlen
  let f' : I → D := fun i => f (t.symm i)
  have htop : t*σ*t⁻¹=τ := pointEquiv_conjugate σ τ e hlen
  have hpull : ∀c,cycleProduct τ f' c=cycleProduct τ g c := by
    intro c
    obtain ⟨d,rfl⟩ := e.surjective c
    exact (cycleProduct_transport σ τ e hlen f d).trans (hprod d)
  obtain ⟨v,hv⟩ := (cycleProducts_eq_iff_base_conjugate τ f' g).mp hpull
  have hconj : PermutationalWreathProduct.topHom t * element σ f *
      (PermutationalWreathProduct.topHom t)⁻¹=element τ f' := by
    simpa only [htop] using top_conjugate_element t σ f
  refine ⟨baseElement v * PermutationalWreathProduct.topHom t,?_⟩
  calc
    (baseElement v * PermutationalWreathProduct.topHom t) * element σ f *
        (baseElement v * PermutationalWreathProduct.topHom t)⁻¹=
      baseElement v * (PermutationalWreathProduct.topHom t * element σ f *
        (PermutationalWreathProduct.topHom t)⁻¹) * (baseElement v)⁻¹ := by group
    _=baseElement v * element τ f' * (baseElement v)⁻¹ := by rw [hconj]
    _=element τ g := hv

theorem coloredData_eq_isConj (σ τ : Equiv.Perm I) (f g : I → D)
    (h : coloredData σ f=coloredData τ g) : IsConj (element σ f) (element τ g) :=
  isConj_iff.mpr (coloredData_eq_exists_conjugator σ τ f g h)

def wreathColoredData (a : Wreath D I) : Multiset (ℕ × D) :=
  coloredData a.right⁻¹ a.left

omit [Finite I] in
theorem element_of_wreath (a : Wreath D I) : element a.right⁻¹ a.left=a := by
  apply PermutationalWreathProduct.ext
  · rfl
  · exact inv_inv a.right

theorem wreathColoredData_eq_isConj (a b : Wreath D I)
    (h : wreathColoredData a=wreathColoredData b) : IsConj a b := by
  have hc := coloredData_eq_isConj a.right⁻¹ b.right⁻¹ a.left b.left h
  simpa only [element_of_wreath] using hc

end SymmetricSubgroupAsymptotics.PermutationWreathColoredConjugacy
