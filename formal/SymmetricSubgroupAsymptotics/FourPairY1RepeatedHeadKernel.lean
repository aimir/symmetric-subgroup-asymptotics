import SymmetricSubgroupAsymptotics.FourPairY1RepeatedHeadMap
import SymmetricSubgroupAsymptotics.ScalarFourHeadedCentralPullback
import SymmetricSubgroupAsymptotics.ScalarFourRepeatedHeadKernelChart

/-! Original Y1 central kernel and surjectivity, checked in the existing
96-state source. Only pointwise finite predicates are reduced. This does
not enumerate original normals or assert the final all-normal source. -/
set_option autoImplicit false
set_option maxRecDepth 8192
noncomputable section
namespace SymmetricSubgroupAsymptotics.FourPairY1RepeatedHeadKernel
open PrimitiveAffineEightFrameRow21TopCertificate FourPairY1RepeatedHeadMap
private abbrev A := NaturalA4ScalarFourHead.G
local instance sourceGroup : Group Source := group

def centralIndex : Fin 96 := certificate.next (certificate.next certificate.identity 0) 2
def centralElement : Source := ⟨centralIndex⟩
private abbrev kernelRaw (i : Fin 96) : Prop :=
  ∀ x : Fin 4,
    (((sourceMap ⟨i⟩ : ScalarFourRepeatedHeadModel.G) : A × A).1 : Equiv.Perm (Fin 4)) x=x ∧
    (((sourceMap ⟨i⟩ : ScalarFourRepeatedHeadModel.G) : A × A).2 : Equiv.Perm (Fin 4)) x=x
private theorem kernel_checked : ∀ i : Fin 96,
    kernelRaw i ↔ i=certificate.identity ∨ i=centralIndex := by
  decide +kernel
private theorem central_distinct_checked : centralIndex ≠ certificate.identity := by
  decide +kernel
private theorem central_square_checked : centralElement^2=1 := by
  apply FiniteGroupRow.ext
  decide +kernel

private theorem map_eq_one_iff_raw (s : Source) : sourceMap s=1 ↔ kernelRaw s.index := by
  constructor
  · intro h x
    constructor
    · exact congrArg (fun g : ScalarFourRepeatedHeadModel.G =>
        ((g : A × A).1 : Equiv.Perm (Fin 4)) x) h
    · exact congrArg (fun g : ScalarFourRepeatedHeadModel.G =>
        ((g : A × A).2 : Equiv.Perm (Fin 4)) x) h
  · intro h
    apply Subtype.ext
    apply Prod.ext
    · apply Subtype.ext
      exact Equiv.ext (fun x => (h x).1)
    · apply Subtype.ext
      exact Equiv.ext (fun x => (h x).2)

theorem kernel_mem_iff (s : Source) : s∈sourceMap.ker ↔ s=1 ∨ s=centralElement := by
  rw [MonoidHom.mem_ker,map_eq_one_iff_raw,kernel_checked]
  constructor
  · rintro (h|h)
    · exact Or.inl (FiniteGroupRow.ext h)
    · exact Or.inr (FiniteGroupRow.ext h)
  · rintro (rfl|rfl)
    · exact Or.inl rfl
    · exact Or.inr rfl

private def kernelElement (i : Fin 2) : sourceMap.ker :=
  ⟨if i=0 then 1 else centralElement,by
    split_ifs
    · exact sourceMap.ker.one_mem
    · exact (kernel_mem_iff _).mpr (Or.inr rfl)⟩
private theorem kernelElement_bijective : Function.Bijective kernelElement := by
  constructor
  · intro i j h
    fin_cases i <;> fin_cases j
    · rfl
    · have he : (1 : Source)=centralElement := congrArg Subtype.val h
      exact False.elim (central_distinct_checked (congrArg FiniteGroupRow.index he).symm)
    · have he : centralElement=(1 : Source) := congrArg Subtype.val h
      exact False.elim (central_distinct_checked (congrArg FiniteGroupRow.index he))
    · rfl
  · intro z
    rcases (kernel_mem_iff z).mp z.2 with h|h
    · exact ⟨0,Subtype.ext h.symm⟩
    · exact ⟨1,Subtype.ext h.symm⟩

theorem kernel_card : Nat.card sourceMap.ker=2 := by
  rw [← Nat.card_congr (Equiv.ofBijective kernelElement kernelElement_bijective)]
  exact Nat.card_fin 2

theorem kernel_binary : IsPGroup 2 sourceMap.ker := by
  intro z
  refine ⟨1,?_⟩
  apply Subtype.ext
  change (z : Source) ^ (2 ^ 1) = 1
  rcases (kernel_mem_iff z).mp z.2 with h|h
  · rw [h,one_pow]
  · rw [h]
    exact central_square_checked

private theorem central_commutes_checked : ∀ (i : Fin 96) (x : Fin 8),
    ((originalEquiv centralElement : FourPairY1ActualFrame.Original) : Equiv.Perm (Fin 8))
      (((originalEquiv ⟨i⟩ : FourPairY1ActualFrame.Original) : Equiv.Perm (Fin 8)) x) =
    ((originalEquiv ⟨i⟩ : FourPairY1ActualFrame.Original) : Equiv.Perm (Fin 8))
      (((originalEquiv centralElement : FourPairY1ActualFrame.Original) : Equiv.Perm (Fin 8)) x) := by
  decide +kernel

theorem kernel_central (z : sourceMap.ker) (g : Source) : (z : Source)*g=g*(z : Source) := by
  rcases (kernel_mem_iff z).mp z.2 with h|h
  · rw [h,one_mul,mul_one]
  · rw [h]
    apply originalEquiv.injective
    apply Subtype.ext
    simpa only [map_mul] using Equiv.ext (central_commutes_checked g.index)

theorem sourceMap_surjective : Function.Surjective sourceMap := by
  have htarget : Nat.card ScalarFourRepeatedHeadModel.G=48 := by
    let t := ScalarFourRepeatedHeadModel.top
    have hk : Nat.card t.ker=16 := by
      rw [← Nat.card_congr ScalarFourRepeatedHeadModel.originalKernelChart.equiv.toEquiv]
      change Nat.card (Multiplicative ScalarFourRepeatedHeadModel.KernelVector)=16
      norm_num [ScalarFourRepeatedHeadModel.KernelVector,Nat.card_eq_fintype_card]
    have hr : Nat.card t.range=3 := by
      let e : t.range ≃ CyclicThree := Equiv.ofBijective Subtype.val (by
        constructor
        · exact Subtype.val_injective
        · intro c
          exact ⟨⟨c,ScalarFourRepeatedHeadModel.headed.top_surjective c⟩,rfl⟩)
      exact (Nat.card_congr e).trans (by norm_num [CyclicThree,Nat.card_eq_fintype_card])
    calc
      Nat.card ScalarFourRepeatedHeadModel.G=Nat.card t.ker*Nat.card t.range := by
        simpa only [Subgroup.index_ker] using t.ker.card_mul_index.symm
      _=48 := by rw [hk,hr]
  have hmul : Nat.card Source=Nat.card sourceMap.ker*Nat.card sourceMap.range := by
    simpa only [Subgroup.index_ker] using sourceMap.ker.card_mul_index.symm
  rw [source_card,kernel_card] at hmul
  have hrange : Nat.card sourceMap.range=Nat.card ScalarFourRepeatedHeadModel.G := by omega
  exact MonoidHom.range_eq_top.mp (sourceMap.range.eq_top_of_card_eq hrange)

/-- Actual original Y1 head, with central weight exactly three. -/
def headed : ScalarFourHeadedQuotient Source :=
  ScalarFourHeadedCentralPullback.headed ScalarFourRepeatedHeadModel.headed rfl
    sourceMap sourceMap_surjective kernel_central kernel_binary

theorem headed_weight : headed.weight=3 := by
  unfold headed
  rw [ScalarFourHeadedCentralPullback.weight_eq]
  rw [kernel_card]
  rfl

end SymmetricSubgroupAsymptotics.FourPairY1RepeatedHeadKernel
end
