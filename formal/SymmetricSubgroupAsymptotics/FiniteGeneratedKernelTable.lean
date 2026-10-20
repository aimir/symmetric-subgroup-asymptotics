import SymmetricSubgroupAsymptotics.GeneratedKernelNormalizer
import Mathlib.SetTheory.Cardinal.Finite

/-! A finite exact kernel chart inside a generated group. All group laws
and generator conjugations are literal identities in that group; the whole
generated group is never enumerated and the kernel need not be central. -/
set_option autoImplicit false
noncomputable section
namespace SymmetricSubgroupAsymptotics

structure FiniteGeneratedKernelTable {G I J : Type} [Group G] (source : J → G) where
  element : I → G
  element_injective : Function.Injective element
  identity : I
  identity_eq : element identity=1
  multiply : I → I → I
  multiply_eq : ∀ i j, element (multiply i j)=element i*element j
  inverse : I → I
  inverse_eq : ∀ i, element (inverse i)=(element i)⁻¹
  conjugate : J → Equiv.Perm I
  conjugate_eq : ∀ j i, element (conjugate j i)=source j*element i*(source j)⁻¹

namespace FiniteGeneratedKernelTable
variable {G I J : Type} [Group G] {source : J → G}
  (C : FiniteGeneratedKernelTable (I := I) source)

def subgroup : Subgroup G where
  carrier := Set.range C.element
  one_mem' := ⟨C.identity,C.identity_eq⟩
  mul_mem' := by rintro _ _ ⟨i,rfl⟩ ⟨j,rfl⟩; exact ⟨C.multiply i j,C.multiply_eq i j⟩
  inv_mem' := by rintro _ ⟨i,rfl⟩; exact ⟨C.inverse i,C.inverse_eq i⟩

def chart (i : I) : C.subgroup := ⟨C.element i,i,rfl⟩

theorem chart_injective : Function.Injective C.chart := by
  intro i j h
  exact C.element_injective (congrArg Subtype.val h)

theorem chart_surjective : Function.Surjective C.chart := by
  rintro ⟨g,i,hi⟩
  exact ⟨i,Subtype.ext hi⟩

def chartEquiv : I ≃ C.subgroup := Equiv.ofBijective C.chart
  ⟨C.chart_injective,C.chart_surjective⟩

def conjugateKernel (j : J) : Equiv.Perm C.subgroup :=
  (C.chartEquiv.symm.trans (C.conjugate j)).trans C.chartEquiv

theorem conjugateKernel_chart (j : J) (i : I) :
    C.conjugateKernel j (C.chart i)=C.chart (C.conjugate j i) := by
  change C.chartEquiv (C.conjugate j (C.chartEquiv.symm (C.chartEquiv i)))=_
  rw [C.chartEquiv.symm_apply_apply]
  rfl

theorem normal (hsource : Subgroup.closure (Set.range source)=⊤) : C.subgroup.Normal := by
  have hn : C.subgroup.subtype.range.Normal := GeneratedKernelNormalizer.range_normal
    source hsource C.subgroup.subtype C.conjugateKernel (by
      intro j k
      obtain ⟨i,rfl⟩ := C.chart_surjective k
      rw [C.conjugateKernel_chart]
      exact C.conjugate_eq j i)
  simpa only [Subgroup.range_subtype] using hn

instance subgroupFinite [Finite I] : Finite C.subgroup :=
  Finite.of_equiv I C.chartEquiv

end FiniteGeneratedKernelTable
end SymmetricSubgroupAsymptotics
