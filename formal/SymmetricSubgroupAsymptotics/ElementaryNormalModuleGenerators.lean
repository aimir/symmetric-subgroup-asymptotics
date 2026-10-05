import SymmetricSubgroupAsymptotics.MinimalNormalCompositionCharts
import SymmetricSubgroupAsymptotics.NormalGeneratorTypeSharing
import SymmetricSubgroupAsymptotics.OriginalKernelNormalSubrepresentation
import SymmetricSubgroupAsymptotics.ActualWreathAffineCapacity

/-!
# Module generators give ambient normal generators

Let `E ◁ G` be an elementary abelian normal subgroup with its literal
prime-field chart.  A tuple which generates the quotient conjugation
representation normally generates `E` inside `G`: take the corresponding
elements of `E` and compare their ambient normal closure with the invariant
subspace recorded by the original-kernel chart.

This is the group-theoretic bridge needed by the affine block arguments.
It retains the original ambient conjugation action and does not replace an
actual correlated translation subgroup by a coordinate product.
-/

set_option autoImplicit false
noncomputable section
open scoped Classical MonoidAlgebra

namespace SymmetricSubgroupAsymptotics

/-- If a normal subgroup of an elementary ambient kernel is generated as
an invariant subrepresentation, the corresponding group elements normally
generate that literal subgroup in the original ambient group. -/
theorem normalGen_le_of_elementaryNormalSubrepresentation_generated
    {G : Type} [Group G] [Finite G]
    (E : Subgroup G) [E.Normal]
    (C : ElementaryMinimalNormalChart E)
    (H : Subgroup G) [H.Normal] (hHE : H ≤ E)
    (t : ℕ)
    (hgen : RepresentationGeneratedBy
      (C.originalKernelChart.normalSubrepresentation
        (QuotientGroup.mk' E) (QuotientGroup.mk'_surjective E)
        C.quotientRepresentation H).toRepresentation t) :
    MarkedC4.normalGen H ≤ t := by
  let q : G →* G ⧸ E := QuotientGroup.mk' E
  let A := C.quotientRepresentation
  let chart := C.originalKernelChart
  let MH : Subrepresentation A.ρ :=
    chart.normalSubrepresentation q (QuotientGroup.mk'_surjective E) A H
  obtain ⟨v, hv⟩ := hgen
  let u : Fin t → C.V := fun i ↦
    (MH.toRepresentation.asModuleEquiv.symm (v i)).1
  let e : Fin t → E := fun i ↦
    C.equiv.symm (Multiplicative.ofAdd (u i))
  let x : Fin t → G := fun i ↦ (e i : G)
  let K : Subgroup G := Subgroup.normalClosure (Set.range x)
  have chart_kernel (L : Subgroup G) :
      (chart.kernelCoordinates q A).ker ≤ L.subgroupOf q.ker := by
    intro k hk
    have hk1 : k = 1 := by
      apply chart.equiv.symm.injective
      exact (MonoidHom.mem_ker.mp hk).trans (map_one chart.equiv.symm).symm
    subst k
    exact Subgroup.one_mem _
  have coordinate_quotientKernelEquiv (a : C.V) :
      (chart.kernelCoordinates q A
        (C.quotientKernelEquiv (Multiplicative.ofAdd a))).toAdd = a := by
    change (C.equiv (C.equiv.symm (Multiplicative.ofAdd a))).toAdd = a
    rw [C.equiv.apply_symm_apply]
    rfl
  have huH (i : Fin t) : (e i : G) ∈ H := by
    let k : q.ker := C.quotientKernelEquiv
      (Multiplicative.ofAdd (u i))
    have hvi : u i ∈ MH :=
      (MH.toRepresentation.asModuleEquiv.symm (v i)).2
    have hkSpace : (chart.kernelCoordinates q A k).toAdd ∈
        chart.normalSpace q A H := by
      rw [coordinate_quotientKernelEquiv]
      exact hvi
    have hkSub : k ∈ H.subgroupOf q.ker :=
      (sectionSubgroupImage_mem_iff
        (chart.kernelCoordinates q A) (H.subgroupOf q.ker)
        (chart_kernel H) k).1 hkSpace
    simpa only [k, e, u, q, chart, A,
      ElementaryMinimalNormalChart.quotientKernelEquiv_coe,
      toAdd_ofAdd] using hkSub
  have hKH : K ≤ H := by
    exact Subgroup.normalClosure_le_normal (by
      rintro _ ⟨i, rfl⟩
      exact huH i)
  let MK : Subrepresentation A.ρ :=
    chart.normalSubrepresentation q (QuotientGroup.mk'_surjective E) A K
  have hMK_MH : MK.toSubmodule ≤ MH.toSubmodule := by
    intro a ha
    let k : q.ker := C.quotientKernelEquiv (Multiplicative.ofAdd a)
    have hkSpace : (chart.kernelCoordinates q A k).toAdd ∈
        chart.normalSpace q A K := by
      dsimp only [k]
      rw [coordinate_quotientKernelEquiv]
      exact ha
    have hkK : k ∈ K.subgroupOf q.ker :=
      (sectionSubgroupImage_mem_iff
        (chart.kernelCoordinates q A) (K.subgroupOf q.ker)
        (chart_kernel K) k).1 hkSpace
    have hkH : k ∈ H.subgroupOf q.ker := hKH hkK
    have hkHSpace : (chart.kernelCoordinates q A k).toAdd ∈
        chart.normalSpace q A H :=
      (sectionSubgroupImage_mem_iff
        (chart.kernelCoordinates q A) (H.subgroupOf q.ker)
        (chart_kernel H) k).2 hkH
    change a ∈ chart.normalSpace q A H
    rw [← coordinate_quotientKernelEquiv a]
    exact hkHSpace
  let WK : Subrepresentation MH.toRepresentation :=
    { toSubmodule := MK.toSubmodule.comap MH.toSubmodule.subtype
      apply_mem_toSubmodule := by
        intro g a ha
        change A.ρ g a.1 ∈ MK
        exact MK.apply_mem_toSubmodule g ha }
  have hvWK (i : Fin t) : v i ∈ WK.asSubmodule := by
    change u i ∈ MK
    let k : q.ker := C.quotientKernelEquiv
      (Multiplicative.ofAdd (u i))
    have hkK : (k : G) ∈ K := by
      apply Subgroup.subset_normalClosure
      exact ⟨i, by
        change (k : G) = x i
        simp only [k, x, e, u, q, A,
          ElementaryMinimalNormalChart.quotientKernelEquiv_coe]⟩
    have hkSub : k ∈ K.subgroupOf q.ker := hkK
    rw [← coordinate_quotientKernelEquiv (u i)]
    exact (sectionSubgroupImage_mem_iff
      (chart.kernelCoordinates q A) (K.subgroupOf q.ker)
      (chart_kernel K) k).2 hkSub
  have hspan_le :
      Submodule.span (ZMod C.p)[G ⧸ E] (Set.range v) ≤ WK.asSubmodule := by
    apply Submodule.span_le.mpr
    rintro _ ⟨i, rfl⟩
    exact hvWK i
  have hMH_MK : MH.toSubmodule ≤ MK.toSubmodule := by
    intro a ha
    let m : MH := ⟨a, ha⟩
    have hm : MH.toRepresentation.asModuleEquiv m ∈ WK.asSubmodule := by
      apply hspan_le
      rw [hv]
      exact Submodule.mem_top
    simpa only [WK, m] using hm
  have hsubrep : MK = MH := by
    apply Subrepresentation.toSubmodule_injective
    exact le_antisymm hMK_MH hMH_MK
  have hintersection : K.subgroupOf q.ker = H.subgroupOf q.ker :=
    (chart.normalSubrepresentation_eq_iff_intersection_eq
      q (QuotientGroup.mk'_surjective E) A K H).1 hsubrep
  have hHK : H ≤ K := by
    intro g hg
    let k : q.ker := ⟨g, by
      simpa only [q, QuotientGroup.ker_mk'] using hHE hg⟩
    have hkH : k ∈ H.subgroupOf q.ker := hg
    rw [← hintersection] at hkH
    exact hkH
  have hK : K = H := le_antisymm hKH hHK
  exact normalGen_le_of_fin_tuple x hK

/-- Ambient-inflated form of
`normalGen_le_of_elementaryNormalSubrepresentation_generated`.  This is the
form supplied directly by an actual-wreath induced-module theorem: the
normal subrepresentation is inflated along `G → G/E`, but its vectors and
its literal normal subgroup are unchanged. -/
theorem normalGen_le_of_elementaryNormalSubrepresentation_comp_generated
    {G : Type} [Group G] [Finite G]
    (E : Subgroup G) [E.Normal]
    (C : ElementaryMinimalNormalChart E)
    (H : Subgroup G) [H.Normal] (hHE : H ≤ E)
    (t : ℕ)
    (hgen : RepresentationGeneratedBy
      (ActualWreathAffineCapacity.subrepresentationComp (QuotientGroup.mk' E)
        C.quotientRepresentation.ρ
        (C.originalKernelChart.normalSubrepresentation
          (QuotientGroup.mk' E) (QuotientGroup.mk'_surjective E)
          C.quotientRepresentation H)).toRepresentation t) :
    MarkedC4.normalGen H ≤ t := by
  let q : G →* G ⧸ E := QuotientGroup.mk' E
  let A := C.quotientRepresentation
  let chart := C.originalKernelChart
  let MH0 : Subrepresentation A.ρ :=
    chart.normalSubrepresentation q (QuotientGroup.mk'_surjective E) A H
  let MH : Subrepresentation (A.ρ.comp q) :=
    ActualWreathAffineCapacity.subrepresentationComp q A.ρ MH0
  obtain ⟨v, hv⟩ := hgen
  let u : Fin t → C.V := fun i ↦
    (MH.toRepresentation.asModuleEquiv.symm (v i)).1
  let e : Fin t → E := fun i ↦
    C.equiv.symm (Multiplicative.ofAdd (u i))
  let x : Fin t → G := fun i ↦ (e i : G)
  let K : Subgroup G := Subgroup.normalClosure (Set.range x)
  have chart_kernel (L : Subgroup G) :
      (chart.kernelCoordinates q A).ker ≤ L.subgroupOf q.ker := by
    intro k hk
    have hk1 : k = 1 := by
      apply chart.equiv.symm.injective
      exact (MonoidHom.mem_ker.mp hk).trans (map_one chart.equiv.symm).symm
    subst k
    exact Subgroup.one_mem _
  have coordinate_quotientKernelEquiv (a : C.V) :
      (chart.kernelCoordinates q A
        (C.quotientKernelEquiv (Multiplicative.ofAdd a))).toAdd = a := by
    change (C.equiv (C.equiv.symm (Multiplicative.ofAdd a))).toAdd = a
    rw [C.equiv.apply_symm_apply]
    rfl
  have huH (i : Fin t) : (e i : G) ∈ H := by
    let k : q.ker := C.quotientKernelEquiv
      (Multiplicative.ofAdd (u i))
    have hvi : u i ∈ MH0 :=
      (MH.toRepresentation.asModuleEquiv.symm (v i)).2
    have hkSpace : (chart.kernelCoordinates q A k).toAdd ∈
        chart.normalSpace q A H := by
      rw [coordinate_quotientKernelEquiv]
      exact hvi
    have hkSub : k ∈ H.subgroupOf q.ker :=
      (sectionSubgroupImage_mem_iff
        (chart.kernelCoordinates q A) (H.subgroupOf q.ker)
        (chart_kernel H) k).1 hkSpace
    simpa only [k, e, u, q, chart, A,
      ElementaryMinimalNormalChart.quotientKernelEquiv_coe,
      toAdd_ofAdd] using hkSub
  have hKH : K ≤ H := by
    exact Subgroup.normalClosure_le_normal (by
      rintro _ ⟨i, rfl⟩
      exact huH i)
  let MK0 : Subrepresentation A.ρ :=
    chart.normalSubrepresentation q (QuotientGroup.mk'_surjective E) A K
  let MK : Subrepresentation (A.ρ.comp q) :=
    ActualWreathAffineCapacity.subrepresentationComp q A.ρ MK0
  have hMK_MH : MK.toSubmodule ≤ MH.toSubmodule := by
    intro a ha
    let k : q.ker := C.quotientKernelEquiv (Multiplicative.ofAdd a)
    have hkSpace : (chart.kernelCoordinates q A k).toAdd ∈
        chart.normalSpace q A K := by
      dsimp only [k]
      rw [coordinate_quotientKernelEquiv]
      exact ha
    have hkK : k ∈ K.subgroupOf q.ker :=
      (sectionSubgroupImage_mem_iff
        (chart.kernelCoordinates q A) (K.subgroupOf q.ker)
        (chart_kernel K) k).1 hkSpace
    have hkH : k ∈ H.subgroupOf q.ker := hKH hkK
    have hkHSpace : (chart.kernelCoordinates q A k).toAdd ∈
        chart.normalSpace q A H :=
      (sectionSubgroupImage_mem_iff
        (chart.kernelCoordinates q A) (H.subgroupOf q.ker)
        (chart_kernel H) k).2 hkH
    change a ∈ chart.normalSpace q A H
    rw [← coordinate_quotientKernelEquiv a]
    exact hkHSpace
  let WK : Subrepresentation MH.toRepresentation :=
    { toSubmodule := MK.toSubmodule.comap MH.toSubmodule.subtype
      apply_mem_toSubmodule := by
        intro g a ha
        change (A.ρ.comp q) g a.1 ∈ MK
        exact MK.apply_mem_toSubmodule g ha }
  have hvWK (i : Fin t) : v i ∈ WK.asSubmodule := by
    change u i ∈ MK
    let k : q.ker := C.quotientKernelEquiv
      (Multiplicative.ofAdd (u i))
    have hkK : (k : G) ∈ K := by
      apply Subgroup.subset_normalClosure
      exact ⟨i, by
        change (k : G) = x i
        simp only [k, x, e, u, q, A,
          ElementaryMinimalNormalChart.quotientKernelEquiv_coe]⟩
    have hkSub : k ∈ K.subgroupOf q.ker := hkK
    rw [← coordinate_quotientKernelEquiv (u i)]
    exact (sectionSubgroupImage_mem_iff
      (chart.kernelCoordinates q A) (K.subgroupOf q.ker)
      (chart_kernel K) k).2 hkSub
  have hspan_le :
      Submodule.span (ZMod C.p)[G] (Set.range v) ≤ WK.asSubmodule := by
    apply Submodule.span_le.mpr
    rintro _ ⟨i, rfl⟩
    exact hvWK i
  have hMH_MK : MH.toSubmodule ≤ MK.toSubmodule := by
    intro a ha
    let m : MH := ⟨a, ha⟩
    have hm : MH.toRepresentation.asModuleEquiv m ∈ WK.asSubmodule := by
      apply hspan_le
      rw [hv]
      exact Submodule.mem_top
    simpa only [WK, m] using hm
  have hsubrep0 : MK0 = MH0 := by
    apply Subrepresentation.toSubmodule_injective
    exact le_antisymm hMK_MH hMH_MK
  have hintersection : K.subgroupOf q.ker = H.subgroupOf q.ker :=
    (chart.normalSubrepresentation_eq_iff_intersection_eq
      q (QuotientGroup.mk'_surjective E) A K H).1 hsubrep0
  have hHK : H ≤ K := by
    intro g hg
    let k : q.ker := ⟨g, by
      simpa only [q, QuotientGroup.ker_mk'] using hHE hg⟩
    have hkH : k ∈ H.subgroupOf q.ker := hg
    rw [← hintersection] at hkH
    exact hkH
  have hK : K = H := le_antisymm hKH hHK
  exact normalGen_le_of_fin_tuple x hK

/-- A generating tuple for the literal quotient representation of an
elementary normal subgroup is an ambient normal-generating tuple for that
subgroup. -/
theorem normalGen_le_of_elementaryQuotientRepresentation_generated
    {G : Type} [Group G] [Finite G]
    (E : Subgroup G) [E.Normal]
    (C : ElementaryMinimalNormalChart E)
    (t : ℕ)
    (hgen : RepresentationGeneratedBy
      C.quotientRepresentation.ρ t) :
    MarkedC4.normalGen E ≤ t := by
  let q : G →* G ⧸ E := QuotientGroup.mk' E
  let A := C.quotientRepresentation
  let chart := C.originalKernelChart
  obtain ⟨v, hv⟩ := hgen
  let u : Fin t → C.V := fun i ↦ A.ρ.asModuleEquiv.symm (v i)
  let e : Fin t → E := fun i ↦
    C.equiv.symm (Multiplicative.ofAdd (u i))
  let x : Fin t → G := fun i ↦ (e i : G)
  let K : Subgroup G := Subgroup.normalClosure (Set.range x)
  have hxe (i : Fin t) : x i ∈ E := (e i).2
  have hKE : K ≤ E := by
    exact Subgroup.normalClosure_le_normal (by
      rintro _ ⟨i, rfl⟩
      exact hxe i)
  let W : Subrepresentation A.ρ :=
    chart.normalSubrepresentation q (QuotientGroup.mk'_surjective E) A K
  have hkernel :
      (chart.kernelCoordinates q A).ker ≤ K.subgroupOf q.ker := by
    intro k hk
    have hk1 : k = 1 := by
      apply chart.equiv.symm.injective
      exact (MonoidHom.mem_ker.mp hk).trans (map_one chart.equiv.symm).symm
    subst k
    exact Subgroup.one_mem _
  have hvW (i : Fin t) : v i ∈ W.asSubmodule := by
    change u i ∈ chart.normalSpace q A K
    let k : q.ker := C.quotientKernelEquiv
      (Multiplicative.ofAdd (u i))
    have hkK : (k : G) ∈ K := by
      apply Subgroup.subset_normalClosure
      exact ⟨i, by
        change (k : G) = x i
        simp only [k, x, e, u, A, q,
          ElementaryMinimalNormalChart.quotientKernelEquiv_coe]⟩
    have hkSub : k ∈ K.subgroupOf q.ker := hkK
    have hkCoord : (chart.kernelCoordinates q A k).toAdd = u i := by
      change (C.equiv (C.equiv.symm
        (Multiplicative.ofAdd (u i)))).toAdd = u i
      rw [C.equiv.apply_symm_apply]
      rfl
    rw [← hkCoord]
    exact (sectionSubgroupImage_mem_iff
      (chart.kernelCoordinates q A) (K.subgroupOf q.ker) hkernel k).2 hkSub
  have hspan_le :
      Submodule.span (ZMod C.p)[G ⧸ E] (Set.range v) ≤ W.asSubmodule := by
    apply Submodule.span_le.mpr
    rintro _ ⟨i, rfl⟩
    exact hvW i
  have hEK : E ≤ K := by
    intro g hg
    let eg : E := ⟨g, hg⟩
    let k : q.ker := C.quotientKernelEquiv (C.equiv eg)
    have hkW : A.ρ.asModuleEquiv (C.equiv eg).toAdd ∈ W.asSubmodule := by
      apply hspan_le
      rw [hv]
      exact Submodule.mem_top
    have hkCoord : (chart.kernelCoordinates q A k).toAdd =
        (C.equiv eg).toAdd := by
      change (C.equiv (C.equiv.symm (C.equiv eg))).toAdd =
        (C.equiv eg).toAdd
      rw [C.equiv.apply_symm_apply]
    have hkSpace : (chart.kernelCoordinates q A k).toAdd ∈
        chart.normalSpace q A K := by
      rw [hkCoord]
      exact hkW
    have hkSub : k ∈ K.subgroupOf q.ker :=
      (sectionSubgroupImage_mem_iff
        (chart.kernelCoordinates q A) (K.subgroupOf q.ker) hkernel k).1 hkSpace
    have hkVal : (k : G) = g := by
      change (C.equiv.symm (C.equiv eg) : E).1 = g
      rw [C.equiv.symm_apply_apply]
    exact hkVal ▸ hkSub
  have hK : K = E := le_antisymm hKE hEK
  exact normalGen_le_of_fin_tuple x hK

end SymmetricSubgroupAsymptotics

end
