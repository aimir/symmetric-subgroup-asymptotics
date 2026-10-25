import SymmetricSubgroupAsymptotics.FiniteOrderedCycleGauge
import SymmetricSubgroupAsymptotics.FiniteMultisetLabelMatching
import SymmetricSubgroupAsymptotics.PermutationCycleMatching
import SymmetricSubgroupAsymptotics.PermutationWreathClassData
import SymmetricSubgroupAsymptotics.WreathCycleGaugeConjugacy

/-! Full symmetric wreath class codes over an arbitrary coefficient
group. Each cycle retains its length and the conjugacy class of its
ORDERED product. Equal codes construct actual top and base conjugators;
no commutative replacement or class-count formula is assumed. -/
set_option autoImplicit false
noncomputable section
open scoped Classical
namespace SymmetricSubgroupAsymptotics.PermutationWreathOrderedClassData
open PermutationCycleDecomposition PermutationCycleMatching FiniteMultisetLabelMatching
variable {C I : Type*} [Group C] [Finite I]

abbrev Wreath (C I : Type*) [Group C] :=
  PermutationalWreathProduct C (Equiv.Perm I) I

def element (σ : Equiv.Perm I) (f : I → C) : Wreath C I := ⟨f,σ⁻¹⟩

def cycleProduct (σ : Equiv.Perm I) (f : I → C) (c : CycleIndex σ) : C :=
  FiniteOrderedCycleGauge.product (fun j => f (pointChart σ ⟨c,j⟩))

theorem cycleProduct_transport (σ τ : Equiv.Perm I)
    (e : CycleIndex σ ≃ CycleIndex τ)
    (hlen : ∀ c, cycleLength σ c = cycleLength τ (e c)) (f : I → C)
    (c : CycleIndex σ) :
    cycleProduct τ (fun i => f ((pointEquiv σ τ e hlen).symm i)) (e c) =
      cycleProduct σ f c := by
  apply FiniteOrderedCycleGauge.product_finCongr (hlen c)
  intro j
  have hp := pointEquiv_apply σ τ e hlen c j
  have hs : (pointEquiv σ τ e hlen).symm
      (pointChart τ ⟨e c,finCongr (hlen c) j⟩) = pointChart σ ⟨c,j⟩ := by
    simpa only [Equiv.symm_apply_apply] using
      (congrArg (pointEquiv σ τ e hlen).symm hp).symm
  exact congrArg f hs

theorem exists_global_gauge (σ : Equiv.Perm I) (f g : I → C)
    (h : ∀ c, IsConj (cycleProduct σ f c) (cycleProduct σ g c)) :
    ∃ v : I → C, ∀ i, g i = v i * f i * (v (σ i))⁻¹ := by
  have hlocal : ∀ c : CycleIndex σ, ∃ v : Fin (cycleLength σ c) → C,
      ∀ j, g (pointChart σ ⟨c,j⟩) =
        v j * f (pointChart σ ⟨c,j⟩) * (v (finRotate _ j))⁻¹ := by
    intro c
    exact FiniteOrderedCycleGauge.exists_gauge_of_product_isConj _ _ _ (h c)
  let v : ∀ c : CycleIndex σ, Fin (cycleLength σ c) → C :=
    fun c => Classical.choose (hlocal c)
  refine ⟨fun i => v ((pointChart σ).symm i).1 ((pointChart σ).symm i).2,?_⟩
  intro i
  obtain ⟨⟨c,j⟩,rfl⟩ := (pointChart σ).surjective i
  dsimp only
  rw [← pointChart_rotate,Equiv.symm_apply_apply,Equiv.symm_apply_apply]
  exact Classical.choose_spec (hlocal c) j

def cycleLabels (σ : Equiv.Perm I) (f : I → C) (c : CycleIndex σ) :
    ℕ × ConjClasses C := (cycleLength σ c,ConjClasses.mk (cycleProduct σ f c))

def coloredData (σ : Equiv.Perm I) (f : I → C) : Multiset (ℕ × ConjClasses C) := by
  letI : Fintype (CycleIndex σ) := Fintype.ofFinite _
  exact labelMultiset (cycleLabels σ f)

omit [Finite I] in
theorem top_conjugate_element (t σ : Equiv.Perm I) (f : I → C) :
    PermutationalWreathProduct.topHom t * element σ f *
        (PermutationalWreathProduct.topHom t)⁻¹ =
      element (t*σ*t⁻¹) (fun i => f (t.symm i)) := by
  apply PermutationalWreathProduct.ext
  · funext i
    simp [PermutationalWreathProduct.topHom,element,
      PermutationalWreathProduct.mul_left,PermutationalWreathProduct.mul_right,
      PermutationalWreathProduct.inv_left]
  · simp [PermutationalWreathProduct.topHom,element,
      PermutationalWreathProduct.mul_right,PermutationalWreathProduct.inv_right,
      mul_inv_rev,mul_assoc]

theorem coloredData_eq_isConj (σ τ : Equiv.Perm I) (f g : I → C)
    (h : coloredData σ f = coloredData τ g) : IsConj (element σ f) (element τ g) := by
  letI : Fintype (CycleIndex σ) := Fintype.ofFinite _
  letI : Fintype (CycleIndex τ) := Fintype.ofFinite _
  have hlabel : labelMultiset (cycleLabels σ f) = labelMultiset (cycleLabels τ g) := h
  let e := matchingEquiv (cycleLabels σ f) (cycleLabels τ g) hlabel
  have he (c : CycleIndex σ) : cycleLabels τ g (e c) = cycleLabels σ f c :=
    matchingEquiv_spec (cycleLabels σ f) (cycleLabels τ g) hlabel c
  have hlen (c : CycleIndex σ) : cycleLength σ c = cycleLength τ (e c) :=
    (congrArg Prod.fst (he c)).symm
  have hprod (c : CycleIndex σ) : IsConj (cycleProduct σ f c) (cycleProduct τ g (e c)) :=
    ConjClasses.mk_eq_mk_iff_isConj.mp ((congrArg Prod.snd (he c)).symm)
  let t := pointEquiv σ τ e hlen
  let f' : I → C := fun i => f (t.symm i)
  have htop : t*σ*t⁻¹ = τ := pointEquiv_conjugate σ τ e hlen
  have hpull : ∀ c, IsConj (cycleProduct τ f' c) (cycleProduct τ g c) := by
    intro c
    obtain ⟨d,rfl⟩ := e.surjective c
    change IsConj (cycleProduct τ (fun i => f (t.symm i)) (e d)) _
    rw [cycleProduct_transport σ τ e hlen f d]
    exact hprod d
  obtain ⟨v,hv⟩ := exists_global_gauge τ f' g hpull
  have hbase : IsConj (element τ f') (element τ g) := by
    apply WreathCycleGaugeConjugacy.isConj_of_gauge (element τ f') (element τ g) rfl v
    intro i
    simpa only [element,inv_inv,Equiv.Perm.smul_def] using hv i
  have hconj : PermutationalWreathProduct.topHom t * element σ f *
      (PermutationalWreathProduct.topHom t)⁻¹ = element τ f' := by
    simpa only [htop] using top_conjugate_element t σ f
  exact (isConj_iff.mpr ⟨PermutationalWreathProduct.topHom t,hconj⟩).trans hbase

def classRepresentative (c : ConjClasses (Wreath C I)) : Wreath C I :=
  Classical.choose (ConjClasses.exists_rep c)

omit [Finite I] in
theorem mk_classRepresentative (c : ConjClasses (Wreath C I)) :
    ConjClasses.mk (classRepresentative c) = c :=
  Classical.choose_spec (ConjClasses.exists_rep c)

def classData (c : ConjClasses (Wreath C I)) :
    PermutationWreathClassData.ColoredParts (ConjClasses C) (Nat.card I) := by
  let a := classRepresentative c
  refine ⟨coloredData a.right⁻¹ a.left,?_,?_⟩
  · intro t ht
    letI : Fintype (CycleIndex a.right⁻¹) := Fintype.ofFinite _
    change t ∈ Finset.univ.val.map (cycleLabels a.right⁻¹ a.left) at ht
    obtain ⟨d,_,rfl⟩ := Multiset.mem_map.mp ht
    exact cycleLength_pos a.right⁻¹ d
  · letI : Fintype (CycleIndex a.right⁻¹) := Fintype.ofFinite _
    change ((Finset.univ.val.map (cycleLabels a.right⁻¹ a.left)).map Prod.fst).sum = Nat.card I
    rw [Multiset.map_map]
    exact PermutationWreathClassData.cycleLength_sum a.right⁻¹

theorem classData_injective : Function.Injective
    (classData : ConjClasses (Wreath C I) →
      PermutationWreathClassData.ColoredParts (ConjClasses C) (Nat.card I)) := by
  intro c d he
  have hcode := congrArg Subtype.val he
  have hc := coloredData_eq_isConj (classRepresentative c).right⁻¹
    (classRepresentative d).right⁻¹ (classRepresentative c).left
    (classRepresentative d).left hcode
  have hrecover (a : Wreath C I) : element a.right⁻¹ a.left = a := by
    apply PermutationalWreathProduct.ext
    · rfl
    · exact inv_inv a.right
  rw [hrecover,hrecover] at hc
  have hm := ConjClasses.mk_eq_mk_iff_isConj.mpr hc
  simpa only [mk_classRepresentative] using hm

end SymmetricSubgroupAsymptotics.PermutationWreathOrderedClassData
