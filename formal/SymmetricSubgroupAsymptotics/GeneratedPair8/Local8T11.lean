import SymmetricSubgroupAsymptotics.BinaryPairFiniteRows
import SymmetricSubgroupAsymptotics.GeneratedNormal8.Registry8T11
import SymmetricSubgroupAsymptotics.GeneratedPair8.Frames8T11

/-! All pair-type normal states of 8T11: original cuts, complete fixed
preimages, quotient covers and exact local gaps. All finite equations use
the Lean kernel. Character and transport records are separate branches. -/
set_option autoImplicit false
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option linter.unusedVariables false
set_option linter.unnecessarySeqFocus false
noncomputable section
namespace SymmetricSubgroupAsymptotics.BinaryPairLocal8T11
abbrev Source := FiniteGroupRow 16
local instance : Group Source := BinaryMenuCayley8T11.group
abbrev generators := BinaryNormal8T11.generators
abbrev top := BinaryPair8T11.Frame0.topHom
private def mask (i : Fin 17) : ℕ := (if i.val < 8 then (if i.val < 4 then (if i.val < 2 then (if i.val < 1 then 32768 else 32832) else (if i.val < 3 then 36960 else 41040)) else (if i.val < 6 then (if i.val < 5 then 33090 else 33345) else (if i.val < 7 then 33864 else 34884))) else (if i.val < 12 then (if i.val < 10 then (if i.val < 9 then 42330 else 39270) else (if i.val < 11 then 38505 else 43605)) else (if i.val < 14 then (if i.val < 13 then 49344 else 61680) else (if i.val < 15 then 50115 else (if i.val < 16 then 52428 else 65535)))))
private abbrev member (i : Fin 17) (x : Source) : Prop := mask i / 2^x.index.val % 2=1

private theorem member_iff (i : Fin 17) (x : Source) :
    member i x ↔ x∈(BinaryNormal8T11.states i).kernel := by
  fin_cases i
  · change member 0 x ↔ x∈Subgroup.closure (Set.range BinaryNormal8T11.N0.normalGenerators)
    rw [binaryNormalRow_mem_iff BinaryNormal8T11.N0.normalCertificate]
    have h : ∀ z : Fin 16, member 0 ⟨z⟩ ↔ ∃ j : Fin 1, BinaryNormal8T11.N0.normalCertificate.rows j=z := (by decide +kernel)
    exact h x.index
  · change member 1 x ↔ x∈Subgroup.closure (Set.range BinaryNormal8T11.N1.normalGenerators)
    rw [binaryNormalRow_mem_iff BinaryNormal8T11.N1.normalCertificate]
    have h : ∀ z : Fin 16, member 1 ⟨z⟩ ↔ ∃ j : Fin 2, BinaryNormal8T11.N1.normalCertificate.rows j=z := (by decide +kernel)
    exact h x.index
  · change member 2 x ↔ x∈Subgroup.closure (Set.range BinaryNormal8T11.N2.normalGenerators)
    rw [binaryNormalRow_mem_iff BinaryNormal8T11.N2.normalCertificate]
    have h : ∀ z : Fin 16, member 2 ⟨z⟩ ↔ ∃ j : Fin 4, BinaryNormal8T11.N2.normalCertificate.rows j=z := (by decide +kernel)
    exact h x.index
  · change member 3 x ↔ x∈Subgroup.closure (Set.range BinaryNormal8T11.N3.normalGenerators)
    rw [binaryNormalRow_mem_iff BinaryNormal8T11.N3.normalCertificate]
    have h : ∀ z : Fin 16, member 3 ⟨z⟩ ↔ ∃ j : Fin 4, BinaryNormal8T11.N3.normalCertificate.rows j=z := (by decide +kernel)
    exact h x.index
  · change member 4 x ↔ x∈Subgroup.closure (Set.range BinaryNormal8T11.N4.normalGenerators)
    rw [binaryNormalRow_mem_iff BinaryNormal8T11.N4.normalCertificate]
    have h : ∀ z : Fin 16, member 4 ⟨z⟩ ↔ ∃ j : Fin 4, BinaryNormal8T11.N4.normalCertificate.rows j=z := (by decide +kernel)
    exact h x.index
  · change member 5 x ↔ x∈Subgroup.closure (Set.range BinaryNormal8T11.N5.normalGenerators)
    rw [binaryNormalRow_mem_iff BinaryNormal8T11.N5.normalCertificate]
    have h : ∀ z : Fin 16, member 5 ⟨z⟩ ↔ ∃ j : Fin 4, BinaryNormal8T11.N5.normalCertificate.rows j=z := (by decide +kernel)
    exact h x.index
  · change member 6 x ↔ x∈Subgroup.closure (Set.range BinaryNormal8T11.N6.normalGenerators)
    rw [binaryNormalRow_mem_iff BinaryNormal8T11.N6.normalCertificate]
    have h : ∀ z : Fin 16, member 6 ⟨z⟩ ↔ ∃ j : Fin 4, BinaryNormal8T11.N6.normalCertificate.rows j=z := (by decide +kernel)
    exact h x.index
  · change member 7 x ↔ x∈Subgroup.closure (Set.range BinaryNormal8T11.N7.normalGenerators)
    rw [binaryNormalRow_mem_iff BinaryNormal8T11.N7.normalCertificate]
    have h : ∀ z : Fin 16, member 7 ⟨z⟩ ↔ ∃ j : Fin 4, BinaryNormal8T11.N7.normalCertificate.rows j=z := (by decide +kernel)
    exact h x.index
  · change member 8 x ↔ x∈Subgroup.closure (Set.range BinaryNormal8T11.N8.normalGenerators)
    rw [binaryNormalRow_mem_iff BinaryNormal8T11.N8.normalCertificate]
    have h : ∀ z : Fin 16, member 8 ⟨z⟩ ↔ ∃ j : Fin 8, BinaryNormal8T11.N8.normalCertificate.rows j=z := (by decide +kernel)
    exact h x.index
  · change member 9 x ↔ x∈Subgroup.closure (Set.range BinaryNormal8T11.N9.normalGenerators)
    rw [binaryNormalRow_mem_iff BinaryNormal8T11.N9.normalCertificate]
    have h : ∀ z : Fin 16, member 9 ⟨z⟩ ↔ ∃ j : Fin 8, BinaryNormal8T11.N9.normalCertificate.rows j=z := (by decide +kernel)
    exact h x.index
  · change member 10 x ↔ x∈Subgroup.closure (Set.range BinaryNormal8T11.N10.normalGenerators)
    rw [binaryNormalRow_mem_iff BinaryNormal8T11.N10.normalCertificate]
    have h : ∀ z : Fin 16, member 10 ⟨z⟩ ↔ ∃ j : Fin 8, BinaryNormal8T11.N10.normalCertificate.rows j=z := (by decide +kernel)
    exact h x.index
  · change member 11 x ↔ x∈Subgroup.closure (Set.range BinaryNormal8T11.N11.normalGenerators)
    rw [binaryNormalRow_mem_iff BinaryNormal8T11.N11.normalCertificate]
    have h : ∀ z : Fin 16, member 11 ⟨z⟩ ↔ ∃ j : Fin 8, BinaryNormal8T11.N11.normalCertificate.rows j=z := (by decide +kernel)
    exact h x.index
  · change member 12 x ↔ x∈Subgroup.closure (Set.range BinaryNormal8T11.N12.normalGenerators)
    rw [binaryNormalRow_mem_iff BinaryNormal8T11.N12.normalCertificate]
    have h : ∀ z : Fin 16, member 12 ⟨z⟩ ↔ ∃ j : Fin 4, BinaryNormal8T11.N12.normalCertificate.rows j=z := (by decide +kernel)
    exact h x.index
  · change member 13 x ↔ x∈Subgroup.closure (Set.range BinaryNormal8T11.N13.normalGenerators)
    rw [binaryNormalRow_mem_iff BinaryNormal8T11.N13.normalCertificate]
    have h : ∀ z : Fin 16, member 13 ⟨z⟩ ↔ ∃ j : Fin 8, BinaryNormal8T11.N13.normalCertificate.rows j=z := (by decide +kernel)
    exact h x.index
  · change member 14 x ↔ x∈Subgroup.closure (Set.range BinaryNormal8T11.N14.normalGenerators)
    rw [binaryNormalRow_mem_iff BinaryNormal8T11.N14.normalCertificate]
    have h : ∀ z : Fin 16, member 14 ⟨z⟩ ↔ ∃ j : Fin 8, BinaryNormal8T11.N14.normalCertificate.rows j=z := (by decide +kernel)
    exact h x.index
  · change member 15 x ↔ x∈Subgroup.closure (Set.range BinaryNormal8T11.N15.normalGenerators)
    rw [binaryNormalRow_mem_iff BinaryNormal8T11.N15.normalCertificate]
    have h : ∀ z : Fin 16, member 15 ⟨z⟩ ↔ ∃ j : Fin 8, BinaryNormal8T11.N15.normalCertificate.rows j=z := (by decide +kernel)
    exact h x.index
  · change member 16 x ↔ x∈Subgroup.closure (Set.range BinaryNormal8T11.N16.normalGenerators)
    rw [binaryNormalRow_mem_iff BinaryNormal8T11.N16.normalCertificate]
    have h : ∀ z : Fin 16, member 16 ⟨z⟩ ↔ ∃ j : Fin 16, BinaryNormal8T11.N16.normalCertificate.rows j=z := (by decide +kernel)
    exact h x.index

theorem kernel_eq : top.ker=BinaryNormal8T11.N12.kernel := by
  ext x
  change top x=1 ↔ x∈(BinaryNormal8T11.states 12).kernel
  rw [← member_iff]
  exact (show ∀ x : Source, top x=1 ↔ member 12 x from by decide +kernel) x

namespace N1

theorem intersection_eq : top.ker⊓BinaryNormal8T11.N1.kernel=BinaryNormal8T11.N1.kernel := by
  rw [kernel_eq]
  ext x
  change (x∈(BinaryNormal8T11.states 12).kernel ∧ x∈(BinaryNormal8T11.states 1).kernel) ↔ x∈(BinaryNormal8T11.states 1).kernel
  simp only [← member_iff]
  exact (show ∀ x : Source, (member 12 x ∧ member 1 x) ↔ member 1 x from by decide +kernel) x

theorem cut_le : BinaryNormal8T11.N12.kernel≤top.ker := by
  intro x hx
  have hk : x∈BinaryNormal8T11.N12.kernel := (member_iff 12 x).mp
    ((show ∀ x : Source, member 12 x → member 12 x from by decide +kernel) x ((member_iff 12 x).mpr hx))
  exact kernel_eq.symm ▸ hk

theorem intersection_le : top.ker⊓BinaryNormal8T11.N1.kernel≤BinaryNormal8T11.N12.kernel := by
  intro x hx
  have hx' : x∈BinaryNormal8T11.N1.kernel := intersection_eq ▸ hx
  apply (member_iff 12 x).mp
  exact (show ∀ x : Source, member 1 x → member 12 x from by decide +kernel) x ((member_iff 1 x).mpr hx')

theorem cut_central : ∀ j, ∀ x : BinaryNormal8T11.N12.kernel,
    (x:Source)⁻¹*(generators j*(x:Source)*(generators j)⁻¹)∈BinaryNormal8T11.N1.kernel := by
  have h : ∀ j, ∀ x : Source, member 12 x →
      member 1 (x⁻¹*(generators j*x*(generators j)⁻¹)) := by decide +kernel
  intro j x
  exact (member_iff 1 _).mp (h j x.val ((member_iff 12 x.val).mpr x.property))

theorem fixed_eq : binaryPairFixedSubgroup top.ker BinaryNormal8T11.N12.kernel=BinaryNormal8T11.N12.kernel := by
  rw [kernel_eq]
  ext x
  rw [binaryPairFixedSubgroup_mem_iff _ _ generators BinaryNormal8T11.generators_full]
  change (x∈(BinaryNormal8T11.states 12).kernel ∧ ∀ j,
    x⁻¹*(generators j*x*(generators j)⁻¹)∈(BinaryNormal8T11.states 12).kernel) ↔ x∈(BinaryNormal8T11.states 12).kernel
  simp only [← member_iff]
  exact (show ∀ x : Source, (member 12 x ∧ ∀ j,
    member 12 (x⁻¹*(generators j*x*(generators j)⁻¹))) ↔ member 12 x from by decide +kernel) x

/-- These are the actual selected cut lift generators from this record. -/
def recordedCutGenerators (j : Fin 2) : Source := ⟨((if j.val < 1 then 7 else 6) : Fin 16)⟩
private def cutWords (j : Fin 2) : List (Fin 2) := (if j.val < 1 then ([0] : List (Fin 2)) else ([0, 1] : List (Fin 2)))
private theorem cutWords_checked : ∀ j,
    ((cutWords j).map recordedCutGenerators).prod=BinaryNormal8T11.N12.normalGenerators j := by decide +kernel

theorem recorded_cut_eq : Subgroup.closure (Set.range recordedCutGenerators)=BinaryNormal8T11.N12.kernel := by
  apply le_antisymm
  · apply (Subgroup.closure_le _).mpr
    rintro _ ⟨j,rfl⟩
    exact (member_iff 12 _).mp
      ((show ∀ j, member 12 (recordedCutGenerators j) from by decide +kernel) j)
  · exact (BinaryNormalGeneratorWords.closure_le
      ({words := cutWords, equations := cutWords_checked} :
        BinaryNormalGeneratorWords BinaryNormal8T11.N12.normalGenerators recordedCutGenerators))

private def kernelPart (j : Fin 2) : Source := ⟨((if j.val < 1 then 7 else 7) : Fin 16)⟩
private def normalPart (j : Fin 2) : Source := ⟨((if j.val < 1 then 15 else 6) : Fin 16)⟩

theorem join_eq : top.ker⊔BinaryNormal8T11.N1.kernel=BinaryNormal8T11.N12.kernel := by
  apply le_antisymm
  · apply sup_le
    · intro x hx
      have hx' : x∈BinaryNormal8T11.N12.kernel := kernel_eq ▸ hx
      exact (member_iff 12 x).mp
        ((show ∀ x : Source, member 12 x → member 12 x from by decide +kernel) x ((member_iff 12 x).mpr hx'))
    · intro x hx
      exact (member_iff 12 x).mp
        ((show ∀ x : Source, member 1 x → member 12 x from by decide +kernel) x ((member_iff 1 x).mpr hx))
  · change Subgroup.closure (Set.range BinaryNormal8T11.N12.normalGenerators)≤_
    apply (Subgroup.closure_le _).mpr
    rintro _ ⟨j,rfl⟩
    have he : ∀ j, kernelPart j*normalPart j=BinaryNormal8T11.N12.normalGenerators j := by decide +kernel
    rw [← he j]
    apply Subgroup.mul_mem
    · apply (show top.ker≤top.ker⊔BinaryNormal8T11.N1.kernel from le_sup_left)
      rw [kernel_eq]
      exact (member_iff 12 _).mp ((show ∀ j, member 12 (kernelPart j) from by decide +kernel) j)
    · apply (show BinaryNormal8T11.N1.kernel≤top.ker⊔BinaryNormal8T11.N1.kernel from le_sup_right)
      exact (member_iff 1 _).mp ((show ∀ j, member 1 (normalPart j) from by decide +kernel) j)

private def cover0 : Equiv.Perm (Fin 4) where
  toFun x := (#[1,0,3,2] : Array (Fin 4))[x.val]!
  invFun x := (#[1,0,3,2] : Array (Fin 4))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel
private def cover1 : Equiv.Perm (Fin 4) where
  toFun x := (#[0,1,3,2] : Array (Fin 4))[x.val]!
  invFun x := (#[0,1,3,2] : Array (Fin 4))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel
private def cover2 : Equiv.Perm (Fin 4) where
  toFun x := (#[1,0,2,3] : Array (Fin 4))[x.val]!
  invFun x := (#[1,0,2,3] : Array (Fin 4))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel
private def cover3 : Equiv.Perm (Fin 4) where
  toFun x := (#[0,1,2,3] : Array (Fin 4))[x.val]!
  invFun x := (#[0,1,2,3] : Array (Fin 4))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

private def coverValues (i : Fin 16) : Equiv.Perm (Fin 4) := (if i.val < 8 then (if i.val < 4 then (if i.val < 2 then (if i.val < 1 then cover1 else cover1) else (if i.val < 3 then cover2 else cover2)) else (if i.val < 6 then (if i.val < 5 then cover0 else cover0) else (if i.val < 7 then cover3 else cover3))) else (if i.val < 12 then (if i.val < 10 then (if i.val < 9 then cover1 else cover1) else (if i.val < 11 then cover2 else cover2)) else (if i.val < 14 then (if i.val < 13 then cover0 else cover0) else (if i.val < 15 then cover3 else cover3))))
private def coverImages (j : Fin 3) : Equiv.Perm (Fin 4) := (if j.val < 1 then cover3 else (if j.val < 2 then cover2 else cover1))
private theorem cover_step : ∀ i j,
    coverValues (BinaryMenuCayley8T11.certificate.next i j)=coverValues i*coverImages j := (by decide +kernel)
private theorem cover_identity : coverValues BinaryMenuCayley8T11.certificate.identity=1 := by decide +kernel

def cover : Source →* Equiv.Perm (Fin 4) where
  toFun x := coverValues x.index
  map_one' := cover_identity
  map_mul' x y := by
    change coverValues (BinaryMenuCayley8T11.certificate.walk x.index
      (BinaryMenuCayley8T11.certificate.words y.index))=coverValues x.index*coverValues y.index
    rw [EncodedCayleyCertificate.values_walk _ coverValues coverImages cover_step,
      ← EncodedCayleyCertificate.values_word _ coverValues coverImages cover_step cover_identity]

theorem cover_kernel : cover.ker=top.ker⊔BinaryNormal8T11.N1.kernel := by
  rw [join_eq]
  ext x
  change cover x=1 ↔ x∈(BinaryNormal8T11.states 12).kernel
  rw [← member_iff]
  exact (show ∀ x : Source, cover x=1 ↔ member 12 x from by decide +kernel) x

/-- Every local numerical dimension follows from checked original subgroup
orders and maps; the selected original cut and full fixed preimage remain. -/
def certificate : BinaryPairLocalCertificate generators top BinaryNormal8T11.N1.kernel where
  cut := BinaryNormal8T11.N12.kernel
  cut_normal := inferInstance
  cut_le_kernel := cut_le
  intersection_le_cut := intersection_le
  central := cut_central
  cutDimension := 1
  fixedDimension := 0
  cut_card := by simp only [intersection_eq,BinaryNormal8T11.N12.kernel_card,BinaryNormal8T11.N1.kernel_card] <;> decide
  fixed_card := by simp only [fixed_eq,BinaryNormal8T11.N12.kernel_card,BinaryNormal8T11.N12.kernel_card] <;> decide
  coverDegree := 4
  cover := cover
  cover_kernel := cover_kernel
  width := 8
  gap := by decide

end N1

namespace N2

theorem intersection_eq : top.ker⊓BinaryNormal8T11.N2.kernel=BinaryNormal8T11.N1.kernel := by
  rw [kernel_eq]
  ext x
  change (x∈(BinaryNormal8T11.states 12).kernel ∧ x∈(BinaryNormal8T11.states 2).kernel) ↔ x∈(BinaryNormal8T11.states 1).kernel
  simp only [← member_iff]
  exact (show ∀ x : Source, (member 12 x ∧ member 2 x) ↔ member 1 x from by decide +kernel) x

theorem cut_le : BinaryNormal8T11.N12.kernel≤top.ker := by
  intro x hx
  have hk : x∈BinaryNormal8T11.N12.kernel := (member_iff 12 x).mp
    ((show ∀ x : Source, member 12 x → member 12 x from by decide +kernel) x ((member_iff 12 x).mpr hx))
  exact kernel_eq.symm ▸ hk

theorem intersection_le : top.ker⊓BinaryNormal8T11.N2.kernel≤BinaryNormal8T11.N12.kernel := by
  intro x hx
  have hx' : x∈BinaryNormal8T11.N1.kernel := intersection_eq ▸ hx
  apply (member_iff 12 x).mp
  exact (show ∀ x : Source, member 1 x → member 12 x from by decide +kernel) x ((member_iff 1 x).mpr hx')

theorem cut_central : ∀ j, ∀ x : BinaryNormal8T11.N12.kernel,
    (x:Source)⁻¹*(generators j*(x:Source)*(generators j)⁻¹)∈BinaryNormal8T11.N2.kernel := by
  have h : ∀ j, ∀ x : Source, member 12 x →
      member 2 (x⁻¹*(generators j*x*(generators j)⁻¹)) := by decide +kernel
  intro j x
  exact (member_iff 2 _).mp (h j x.val ((member_iff 12 x.val).mpr x.property))

theorem fixed_eq : binaryPairFixedSubgroup top.ker BinaryNormal8T11.N12.kernel=BinaryNormal8T11.N12.kernel := by
  rw [kernel_eq]
  ext x
  rw [binaryPairFixedSubgroup_mem_iff _ _ generators BinaryNormal8T11.generators_full]
  change (x∈(BinaryNormal8T11.states 12).kernel ∧ ∀ j,
    x⁻¹*(generators j*x*(generators j)⁻¹)∈(BinaryNormal8T11.states 12).kernel) ↔ x∈(BinaryNormal8T11.states 12).kernel
  simp only [← member_iff]
  exact (show ∀ x : Source, (member 12 x ∧ ∀ j,
    member 12 (x⁻¹*(generators j*x*(generators j)⁻¹))) ↔ member 12 x from by decide +kernel) x

/-- These are the actual selected cut lift generators from this record. -/
def recordedCutGenerators (j : Fin 2) : Source := ⟨((if j.val < 1 then 7 else 6) : Fin 16)⟩
private def cutWords (j : Fin 2) : List (Fin 2) := (if j.val < 1 then ([0] : List (Fin 2)) else ([0, 1] : List (Fin 2)))
private theorem cutWords_checked : ∀ j,
    ((cutWords j).map recordedCutGenerators).prod=BinaryNormal8T11.N12.normalGenerators j := by decide +kernel

theorem recorded_cut_eq : Subgroup.closure (Set.range recordedCutGenerators)=BinaryNormal8T11.N12.kernel := by
  apply le_antisymm
  · apply (Subgroup.closure_le _).mpr
    rintro _ ⟨j,rfl⟩
    exact (member_iff 12 _).mp
      ((show ∀ j, member 12 (recordedCutGenerators j) from by decide +kernel) j)
  · exact (BinaryNormalGeneratorWords.closure_le
      ({words := cutWords, equations := cutWords_checked} :
        BinaryNormalGeneratorWords BinaryNormal8T11.N12.normalGenerators recordedCutGenerators))

private def kernelPart (j : Fin 3) : Source := ⟨((if j.val < 1 then 7 else (if j.val < 2 then 7 else 7)) : Fin 16)⟩
private def normalPart (j : Fin 3) : Source := ⟨((if j.val < 1 then 15 else (if j.val < 2 then 6 else 5)) : Fin 16)⟩

theorem join_eq : top.ker⊔BinaryNormal8T11.N2.kernel=BinaryNormal8T11.N13.kernel := by
  apply le_antisymm
  · apply sup_le
    · intro x hx
      have hx' : x∈BinaryNormal8T11.N12.kernel := kernel_eq ▸ hx
      exact (member_iff 13 x).mp
        ((show ∀ x : Source, member 12 x → member 13 x from by decide +kernel) x ((member_iff 12 x).mpr hx'))
    · intro x hx
      exact (member_iff 13 x).mp
        ((show ∀ x : Source, member 2 x → member 13 x from by decide +kernel) x ((member_iff 2 x).mpr hx))
  · change Subgroup.closure (Set.range BinaryNormal8T11.N13.normalGenerators)≤_
    apply (Subgroup.closure_le _).mpr
    rintro _ ⟨j,rfl⟩
    have he : ∀ j, kernelPart j*normalPart j=BinaryNormal8T11.N13.normalGenerators j := by decide +kernel
    rw [← he j]
    apply Subgroup.mul_mem
    · apply (show top.ker≤top.ker⊔BinaryNormal8T11.N2.kernel from le_sup_left)
      rw [kernel_eq]
      exact (member_iff 12 _).mp ((show ∀ j, member 12 (kernelPart j) from by decide +kernel) j)
    · apply (show BinaryNormal8T11.N2.kernel≤top.ker⊔BinaryNormal8T11.N2.kernel from le_sup_right)
      exact (member_iff 2 _).mp ((show ∀ j, member 2 (normalPart j) from by decide +kernel) j)

private def cover0 : Equiv.Perm (Fin 2) where
  toFun x := (#[1,0] : Array (Fin 2))[x.val]!
  invFun x := (#[1,0] : Array (Fin 2))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel
private def cover1 : Equiv.Perm (Fin 2) where
  toFun x := (#[0,1] : Array (Fin 2))[x.val]!
  invFun x := (#[0,1] : Array (Fin 2))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

private def coverValues (i : Fin 16) : Equiv.Perm (Fin 2) := (if i.val < 8 then (if i.val < 4 then (if i.val < 2 then (if i.val < 1 then cover0 else cover0) else (if i.val < 3 then cover0 else cover0)) else (if i.val < 6 then (if i.val < 5 then cover1 else cover1) else (if i.val < 7 then cover1 else cover1))) else (if i.val < 12 then (if i.val < 10 then (if i.val < 9 then cover0 else cover0) else (if i.val < 11 then cover0 else cover0)) else (if i.val < 14 then (if i.val < 13 then cover1 else cover1) else (if i.val < 15 then cover1 else cover1))))
private def coverImages (j : Fin 3) : Equiv.Perm (Fin 2) := (if j.val < 1 then cover1 else (if j.val < 2 then cover0 else cover0))
private theorem cover_step : ∀ i j,
    coverValues (BinaryMenuCayley8T11.certificate.next i j)=coverValues i*coverImages j := (by decide +kernel)
private theorem cover_identity : coverValues BinaryMenuCayley8T11.certificate.identity=1 := by decide +kernel

def cover : Source →* Equiv.Perm (Fin 2) where
  toFun x := coverValues x.index
  map_one' := cover_identity
  map_mul' x y := by
    change coverValues (BinaryMenuCayley8T11.certificate.walk x.index
      (BinaryMenuCayley8T11.certificate.words y.index))=coverValues x.index*coverValues y.index
    rw [EncodedCayleyCertificate.values_walk _ coverValues coverImages cover_step,
      ← EncodedCayleyCertificate.values_word _ coverValues coverImages cover_step cover_identity]

theorem cover_kernel : cover.ker=top.ker⊔BinaryNormal8T11.N2.kernel := by
  rw [join_eq]
  ext x
  change cover x=1 ↔ x∈(BinaryNormal8T11.states 13).kernel
  rw [← member_iff]
  exact (show ∀ x : Source, cover x=1 ↔ member 13 x from by decide +kernel) x

/-- Every local numerical dimension follows from checked original subgroup
orders and maps; the selected original cut and full fixed preimage remain. -/
def certificate : BinaryPairLocalCertificate generators top BinaryNormal8T11.N2.kernel where
  cut := BinaryNormal8T11.N12.kernel
  cut_normal := inferInstance
  cut_le_kernel := cut_le
  intersection_le_cut := intersection_le
  central := cut_central
  cutDimension := 1
  fixedDimension := 0
  cut_card := by simp only [intersection_eq,BinaryNormal8T11.N12.kernel_card,BinaryNormal8T11.N1.kernel_card] <;> decide
  fixed_card := by simp only [fixed_eq,BinaryNormal8T11.N12.kernel_card,BinaryNormal8T11.N12.kernel_card] <;> decide
  coverDegree := 2
  cover := cover
  cover_kernel := cover_kernel
  width := 8
  gap := by decide

end N2

namespace N3

theorem intersection_eq : top.ker⊓BinaryNormal8T11.N3.kernel=BinaryNormal8T11.N1.kernel := by
  rw [kernel_eq]
  ext x
  change (x∈(BinaryNormal8T11.states 12).kernel ∧ x∈(BinaryNormal8T11.states 3).kernel) ↔ x∈(BinaryNormal8T11.states 1).kernel
  simp only [← member_iff]
  exact (show ∀ x : Source, (member 12 x ∧ member 3 x) ↔ member 1 x from by decide +kernel) x

theorem cut_le : BinaryNormal8T11.N12.kernel≤top.ker := by
  intro x hx
  have hk : x∈BinaryNormal8T11.N12.kernel := (member_iff 12 x).mp
    ((show ∀ x : Source, member 12 x → member 12 x from by decide +kernel) x ((member_iff 12 x).mpr hx))
  exact kernel_eq.symm ▸ hk

theorem intersection_le : top.ker⊓BinaryNormal8T11.N3.kernel≤BinaryNormal8T11.N12.kernel := by
  intro x hx
  have hx' : x∈BinaryNormal8T11.N1.kernel := intersection_eq ▸ hx
  apply (member_iff 12 x).mp
  exact (show ∀ x : Source, member 1 x → member 12 x from by decide +kernel) x ((member_iff 1 x).mpr hx')

theorem cut_central : ∀ j, ∀ x : BinaryNormal8T11.N12.kernel,
    (x:Source)⁻¹*(generators j*(x:Source)*(generators j)⁻¹)∈BinaryNormal8T11.N3.kernel := by
  have h : ∀ j, ∀ x : Source, member 12 x →
      member 3 (x⁻¹*(generators j*x*(generators j)⁻¹)) := by decide +kernel
  intro j x
  exact (member_iff 3 _).mp (h j x.val ((member_iff 12 x.val).mpr x.property))

theorem fixed_eq : binaryPairFixedSubgroup top.ker BinaryNormal8T11.N12.kernel=BinaryNormal8T11.N12.kernel := by
  rw [kernel_eq]
  ext x
  rw [binaryPairFixedSubgroup_mem_iff _ _ generators BinaryNormal8T11.generators_full]
  change (x∈(BinaryNormal8T11.states 12).kernel ∧ ∀ j,
    x⁻¹*(generators j*x*(generators j)⁻¹)∈(BinaryNormal8T11.states 12).kernel) ↔ x∈(BinaryNormal8T11.states 12).kernel
  simp only [← member_iff]
  exact (show ∀ x : Source, (member 12 x ∧ ∀ j,
    member 12 (x⁻¹*(generators j*x*(generators j)⁻¹))) ↔ member 12 x from by decide +kernel) x

/-- These are the actual selected cut lift generators from this record. -/
def recordedCutGenerators (j : Fin 2) : Source := ⟨((if j.val < 1 then 7 else 6) : Fin 16)⟩
private def cutWords (j : Fin 2) : List (Fin 2) := (if j.val < 1 then ([0] : List (Fin 2)) else ([0, 1] : List (Fin 2)))
private theorem cutWords_checked : ∀ j,
    ((cutWords j).map recordedCutGenerators).prod=BinaryNormal8T11.N12.normalGenerators j := by decide +kernel

theorem recorded_cut_eq : Subgroup.closure (Set.range recordedCutGenerators)=BinaryNormal8T11.N12.kernel := by
  apply le_antisymm
  · apply (Subgroup.closure_le _).mpr
    rintro _ ⟨j,rfl⟩
    exact (member_iff 12 _).mp
      ((show ∀ j, member 12 (recordedCutGenerators j) from by decide +kernel) j)
  · exact (BinaryNormalGeneratorWords.closure_le
      ({words := cutWords, equations := cutWords_checked} :
        BinaryNormalGeneratorWords BinaryNormal8T11.N12.normalGenerators recordedCutGenerators))

private def kernelPart (j : Fin 3) : Source := ⟨((if j.val < 1 then 7 else (if j.val < 2 then 7 else 6)) : Fin 16)⟩
private def normalPart (j : Fin 3) : Source := ⟨((if j.val < 1 then 15 else (if j.val < 2 then 6 else 13)) : Fin 16)⟩

theorem join_eq : top.ker⊔BinaryNormal8T11.N3.kernel=BinaryNormal8T11.N13.kernel := by
  apply le_antisymm
  · apply sup_le
    · intro x hx
      have hx' : x∈BinaryNormal8T11.N12.kernel := kernel_eq ▸ hx
      exact (member_iff 13 x).mp
        ((show ∀ x : Source, member 12 x → member 13 x from by decide +kernel) x ((member_iff 12 x).mpr hx'))
    · intro x hx
      exact (member_iff 13 x).mp
        ((show ∀ x : Source, member 3 x → member 13 x from by decide +kernel) x ((member_iff 3 x).mpr hx))
  · change Subgroup.closure (Set.range BinaryNormal8T11.N13.normalGenerators)≤_
    apply (Subgroup.closure_le _).mpr
    rintro _ ⟨j,rfl⟩
    have he : ∀ j, kernelPart j*normalPart j=BinaryNormal8T11.N13.normalGenerators j := by decide +kernel
    rw [← he j]
    apply Subgroup.mul_mem
    · apply (show top.ker≤top.ker⊔BinaryNormal8T11.N3.kernel from le_sup_left)
      rw [kernel_eq]
      exact (member_iff 12 _).mp ((show ∀ j, member 12 (kernelPart j) from by decide +kernel) j)
    · apply (show BinaryNormal8T11.N3.kernel≤top.ker⊔BinaryNormal8T11.N3.kernel from le_sup_right)
      exact (member_iff 3 _).mp ((show ∀ j, member 3 (normalPart j) from by decide +kernel) j)

private def cover0 : Equiv.Perm (Fin 2) where
  toFun x := (#[1,0] : Array (Fin 2))[x.val]!
  invFun x := (#[1,0] : Array (Fin 2))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel
private def cover1 : Equiv.Perm (Fin 2) where
  toFun x := (#[0,1] : Array (Fin 2))[x.val]!
  invFun x := (#[0,1] : Array (Fin 2))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

private def coverValues (i : Fin 16) : Equiv.Perm (Fin 2) := (if i.val < 8 then (if i.val < 4 then (if i.val < 2 then (if i.val < 1 then cover0 else cover0) else (if i.val < 3 then cover0 else cover0)) else (if i.val < 6 then (if i.val < 5 then cover1 else cover1) else (if i.val < 7 then cover1 else cover1))) else (if i.val < 12 then (if i.val < 10 then (if i.val < 9 then cover0 else cover0) else (if i.val < 11 then cover0 else cover0)) else (if i.val < 14 then (if i.val < 13 then cover1 else cover1) else (if i.val < 15 then cover1 else cover1))))
private def coverImages (j : Fin 3) : Equiv.Perm (Fin 2) := (if j.val < 1 then cover1 else (if j.val < 2 then cover0 else cover0))
private theorem cover_step : ∀ i j,
    coverValues (BinaryMenuCayley8T11.certificate.next i j)=coverValues i*coverImages j := (by decide +kernel)
private theorem cover_identity : coverValues BinaryMenuCayley8T11.certificate.identity=1 := by decide +kernel

def cover : Source →* Equiv.Perm (Fin 2) where
  toFun x := coverValues x.index
  map_one' := cover_identity
  map_mul' x y := by
    change coverValues (BinaryMenuCayley8T11.certificate.walk x.index
      (BinaryMenuCayley8T11.certificate.words y.index))=coverValues x.index*coverValues y.index
    rw [EncodedCayleyCertificate.values_walk _ coverValues coverImages cover_step,
      ← EncodedCayleyCertificate.values_word _ coverValues coverImages cover_step cover_identity]

theorem cover_kernel : cover.ker=top.ker⊔BinaryNormal8T11.N3.kernel := by
  rw [join_eq]
  ext x
  change cover x=1 ↔ x∈(BinaryNormal8T11.states 13).kernel
  rw [← member_iff]
  exact (show ∀ x : Source, cover x=1 ↔ member 13 x from by decide +kernel) x

/-- Every local numerical dimension follows from checked original subgroup
orders and maps; the selected original cut and full fixed preimage remain. -/
def certificate : BinaryPairLocalCertificate generators top BinaryNormal8T11.N3.kernel where
  cut := BinaryNormal8T11.N12.kernel
  cut_normal := inferInstance
  cut_le_kernel := cut_le
  intersection_le_cut := intersection_le
  central := cut_central
  cutDimension := 1
  fixedDimension := 0
  cut_card := by simp only [intersection_eq,BinaryNormal8T11.N12.kernel_card,BinaryNormal8T11.N1.kernel_card] <;> decide
  fixed_card := by simp only [fixed_eq,BinaryNormal8T11.N12.kernel_card,BinaryNormal8T11.N12.kernel_card] <;> decide
  coverDegree := 2
  cover := cover
  cover_kernel := cover_kernel
  width := 8
  gap := by decide

end N3

namespace N4

theorem intersection_eq : top.ker⊓BinaryNormal8T11.N4.kernel=BinaryNormal8T11.N1.kernel := by
  rw [kernel_eq]
  ext x
  change (x∈(BinaryNormal8T11.states 12).kernel ∧ x∈(BinaryNormal8T11.states 4).kernel) ↔ x∈(BinaryNormal8T11.states 1).kernel
  simp only [← member_iff]
  exact (show ∀ x : Source, (member 12 x ∧ member 4 x) ↔ member 1 x from by decide +kernel) x

theorem cut_le : BinaryNormal8T11.N12.kernel≤top.ker := by
  intro x hx
  have hk : x∈BinaryNormal8T11.N12.kernel := (member_iff 12 x).mp
    ((show ∀ x : Source, member 12 x → member 12 x from by decide +kernel) x ((member_iff 12 x).mpr hx))
  exact kernel_eq.symm ▸ hk

theorem intersection_le : top.ker⊓BinaryNormal8T11.N4.kernel≤BinaryNormal8T11.N12.kernel := by
  intro x hx
  have hx' : x∈BinaryNormal8T11.N1.kernel := intersection_eq ▸ hx
  apply (member_iff 12 x).mp
  exact (show ∀ x : Source, member 1 x → member 12 x from by decide +kernel) x ((member_iff 1 x).mpr hx')

theorem cut_central : ∀ j, ∀ x : BinaryNormal8T11.N12.kernel,
    (x:Source)⁻¹*(generators j*(x:Source)*(generators j)⁻¹)∈BinaryNormal8T11.N4.kernel := by
  have h : ∀ j, ∀ x : Source, member 12 x →
      member 4 (x⁻¹*(generators j*x*(generators j)⁻¹)) := by decide +kernel
  intro j x
  exact (member_iff 4 _).mp (h j x.val ((member_iff 12 x.val).mpr x.property))

theorem fixed_eq : binaryPairFixedSubgroup top.ker BinaryNormal8T11.N12.kernel=BinaryNormal8T11.N12.kernel := by
  rw [kernel_eq]
  ext x
  rw [binaryPairFixedSubgroup_mem_iff _ _ generators BinaryNormal8T11.generators_full]
  change (x∈(BinaryNormal8T11.states 12).kernel ∧ ∀ j,
    x⁻¹*(generators j*x*(generators j)⁻¹)∈(BinaryNormal8T11.states 12).kernel) ↔ x∈(BinaryNormal8T11.states 12).kernel
  simp only [← member_iff]
  exact (show ∀ x : Source, (member 12 x ∧ ∀ j,
    member 12 (x⁻¹*(generators j*x*(generators j)⁻¹))) ↔ member 12 x from by decide +kernel) x

/-- These are the actual selected cut lift generators from this record. -/
def recordedCutGenerators (j : Fin 2) : Source := ⟨((if j.val < 1 then 7 else 6) : Fin 16)⟩
private def cutWords (j : Fin 2) : List (Fin 2) := (if j.val < 1 then ([0] : List (Fin 2)) else ([0, 1] : List (Fin 2)))
private theorem cutWords_checked : ∀ j,
    ((cutWords j).map recordedCutGenerators).prod=BinaryNormal8T11.N12.normalGenerators j := by decide +kernel

theorem recorded_cut_eq : Subgroup.closure (Set.range recordedCutGenerators)=BinaryNormal8T11.N12.kernel := by
  apply le_antisymm
  · apply (Subgroup.closure_le _).mpr
    rintro _ ⟨j,rfl⟩
    exact (member_iff 12 _).mp
      ((show ∀ j, member 12 (recordedCutGenerators j) from by decide +kernel) j)
  · exact (BinaryNormalGeneratorWords.closure_le
      ({words := cutWords, equations := cutWords_checked} :
        BinaryNormalGeneratorWords BinaryNormal8T11.N12.normalGenerators recordedCutGenerators))

private def kernelPart (j : Fin 3) : Source := ⟨((if j.val < 1 then 7 else (if j.val < 2 then 7 else 7)) : Fin 16)⟩
private def normalPart (j : Fin 3) : Source := ⟨((if j.val < 1 then 1 else (if j.val < 2 then 15 else 6)) : Fin 16)⟩

theorem join_eq : top.ker⊔BinaryNormal8T11.N4.kernel=BinaryNormal8T11.N14.kernel := by
  apply le_antisymm
  · apply sup_le
    · intro x hx
      have hx' : x∈BinaryNormal8T11.N12.kernel := kernel_eq ▸ hx
      exact (member_iff 14 x).mp
        ((show ∀ x : Source, member 12 x → member 14 x from by decide +kernel) x ((member_iff 12 x).mpr hx'))
    · intro x hx
      exact (member_iff 14 x).mp
        ((show ∀ x : Source, member 4 x → member 14 x from by decide +kernel) x ((member_iff 4 x).mpr hx))
  · change Subgroup.closure (Set.range BinaryNormal8T11.N14.normalGenerators)≤_
    apply (Subgroup.closure_le _).mpr
    rintro _ ⟨j,rfl⟩
    have he : ∀ j, kernelPart j*normalPart j=BinaryNormal8T11.N14.normalGenerators j := by decide +kernel
    rw [← he j]
    apply Subgroup.mul_mem
    · apply (show top.ker≤top.ker⊔BinaryNormal8T11.N4.kernel from le_sup_left)
      rw [kernel_eq]
      exact (member_iff 12 _).mp ((show ∀ j, member 12 (kernelPart j) from by decide +kernel) j)
    · apply (show BinaryNormal8T11.N4.kernel≤top.ker⊔BinaryNormal8T11.N4.kernel from le_sup_right)
      exact (member_iff 4 _).mp ((show ∀ j, member 4 (normalPart j) from by decide +kernel) j)

private def cover0 : Equiv.Perm (Fin 2) where
  toFun x := (#[1,0] : Array (Fin 2))[x.val]!
  invFun x := (#[1,0] : Array (Fin 2))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel
private def cover1 : Equiv.Perm (Fin 2) where
  toFun x := (#[0,1] : Array (Fin 2))[x.val]!
  invFun x := (#[0,1] : Array (Fin 2))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

private def coverValues (i : Fin 16) : Equiv.Perm (Fin 2) := (if i.val < 8 then (if i.val < 4 then (if i.val < 2 then (if i.val < 1 then cover1 else cover1) else (if i.val < 3 then cover0 else cover0)) else (if i.val < 6 then (if i.val < 5 then cover0 else cover0) else (if i.val < 7 then cover1 else cover1))) else (if i.val < 12 then (if i.val < 10 then (if i.val < 9 then cover1 else cover1) else (if i.val < 11 then cover0 else cover0)) else (if i.val < 14 then (if i.val < 13 then cover0 else cover0) else (if i.val < 15 then cover1 else cover1))))
private def coverImages (j : Fin 3) : Equiv.Perm (Fin 2) := (if j.val < 1 then cover1 else (if j.val < 2 then cover0 else cover1))
private theorem cover_step : ∀ i j,
    coverValues (BinaryMenuCayley8T11.certificate.next i j)=coverValues i*coverImages j := (by decide +kernel)
private theorem cover_identity : coverValues BinaryMenuCayley8T11.certificate.identity=1 := by decide +kernel

def cover : Source →* Equiv.Perm (Fin 2) where
  toFun x := coverValues x.index
  map_one' := cover_identity
  map_mul' x y := by
    change coverValues (BinaryMenuCayley8T11.certificate.walk x.index
      (BinaryMenuCayley8T11.certificate.words y.index))=coverValues x.index*coverValues y.index
    rw [EncodedCayleyCertificate.values_walk _ coverValues coverImages cover_step,
      ← EncodedCayleyCertificate.values_word _ coverValues coverImages cover_step cover_identity]

theorem cover_kernel : cover.ker=top.ker⊔BinaryNormal8T11.N4.kernel := by
  rw [join_eq]
  ext x
  change cover x=1 ↔ x∈(BinaryNormal8T11.states 14).kernel
  rw [← member_iff]
  exact (show ∀ x : Source, cover x=1 ↔ member 14 x from by decide +kernel) x

/-- Every local numerical dimension follows from checked original subgroup
orders and maps; the selected original cut and full fixed preimage remain. -/
def certificate : BinaryPairLocalCertificate generators top BinaryNormal8T11.N4.kernel where
  cut := BinaryNormal8T11.N12.kernel
  cut_normal := inferInstance
  cut_le_kernel := cut_le
  intersection_le_cut := intersection_le
  central := cut_central
  cutDimension := 1
  fixedDimension := 0
  cut_card := by simp only [intersection_eq,BinaryNormal8T11.N12.kernel_card,BinaryNormal8T11.N1.kernel_card] <;> decide
  fixed_card := by simp only [fixed_eq,BinaryNormal8T11.N12.kernel_card,BinaryNormal8T11.N12.kernel_card] <;> decide
  coverDegree := 2
  cover := cover
  cover_kernel := cover_kernel
  width := 8
  gap := by decide

end N4

namespace N5

theorem intersection_eq : top.ker⊓BinaryNormal8T11.N5.kernel=BinaryNormal8T11.N1.kernel := by
  rw [kernel_eq]
  ext x
  change (x∈(BinaryNormal8T11.states 12).kernel ∧ x∈(BinaryNormal8T11.states 5).kernel) ↔ x∈(BinaryNormal8T11.states 1).kernel
  simp only [← member_iff]
  exact (show ∀ x : Source, (member 12 x ∧ member 5 x) ↔ member 1 x from by decide +kernel) x

theorem cut_le : BinaryNormal8T11.N12.kernel≤top.ker := by
  intro x hx
  have hk : x∈BinaryNormal8T11.N12.kernel := (member_iff 12 x).mp
    ((show ∀ x : Source, member 12 x → member 12 x from by decide +kernel) x ((member_iff 12 x).mpr hx))
  exact kernel_eq.symm ▸ hk

theorem intersection_le : top.ker⊓BinaryNormal8T11.N5.kernel≤BinaryNormal8T11.N12.kernel := by
  intro x hx
  have hx' : x∈BinaryNormal8T11.N1.kernel := intersection_eq ▸ hx
  apply (member_iff 12 x).mp
  exact (show ∀ x : Source, member 1 x → member 12 x from by decide +kernel) x ((member_iff 1 x).mpr hx')

theorem cut_central : ∀ j, ∀ x : BinaryNormal8T11.N12.kernel,
    (x:Source)⁻¹*(generators j*(x:Source)*(generators j)⁻¹)∈BinaryNormal8T11.N5.kernel := by
  have h : ∀ j, ∀ x : Source, member 12 x →
      member 5 (x⁻¹*(generators j*x*(generators j)⁻¹)) := by decide +kernel
  intro j x
  exact (member_iff 5 _).mp (h j x.val ((member_iff 12 x.val).mpr x.property))

theorem fixed_eq : binaryPairFixedSubgroup top.ker BinaryNormal8T11.N12.kernel=BinaryNormal8T11.N12.kernel := by
  rw [kernel_eq]
  ext x
  rw [binaryPairFixedSubgroup_mem_iff _ _ generators BinaryNormal8T11.generators_full]
  change (x∈(BinaryNormal8T11.states 12).kernel ∧ ∀ j,
    x⁻¹*(generators j*x*(generators j)⁻¹)∈(BinaryNormal8T11.states 12).kernel) ↔ x∈(BinaryNormal8T11.states 12).kernel
  simp only [← member_iff]
  exact (show ∀ x : Source, (member 12 x ∧ ∀ j,
    member 12 (x⁻¹*(generators j*x*(generators j)⁻¹))) ↔ member 12 x from by decide +kernel) x

/-- These are the actual selected cut lift generators from this record. -/
def recordedCutGenerators (j : Fin 2) : Source := ⟨((if j.val < 1 then 7 else 6) : Fin 16)⟩
private def cutWords (j : Fin 2) : List (Fin 2) := (if j.val < 1 then ([0] : List (Fin 2)) else ([0, 1] : List (Fin 2)))
private theorem cutWords_checked : ∀ j,
    ((cutWords j).map recordedCutGenerators).prod=BinaryNormal8T11.N12.normalGenerators j := by decide +kernel

theorem recorded_cut_eq : Subgroup.closure (Set.range recordedCutGenerators)=BinaryNormal8T11.N12.kernel := by
  apply le_antisymm
  · apply (Subgroup.closure_le _).mpr
    rintro _ ⟨j,rfl⟩
    exact (member_iff 12 _).mp
      ((show ∀ j, member 12 (recordedCutGenerators j) from by decide +kernel) j)
  · exact (BinaryNormalGeneratorWords.closure_le
      ({words := cutWords, equations := cutWords_checked} :
        BinaryNormalGeneratorWords BinaryNormal8T11.N12.normalGenerators recordedCutGenerators))

private def kernelPart (j : Fin 3) : Source := ⟨((if j.val < 1 then 6 else (if j.val < 2 then 7 else 7)) : Fin 16)⟩
private def normalPart (j : Fin 3) : Source := ⟨((if j.val < 1 then 9 else (if j.val < 2 then 15 else 6)) : Fin 16)⟩

theorem join_eq : top.ker⊔BinaryNormal8T11.N5.kernel=BinaryNormal8T11.N14.kernel := by
  apply le_antisymm
  · apply sup_le
    · intro x hx
      have hx' : x∈BinaryNormal8T11.N12.kernel := kernel_eq ▸ hx
      exact (member_iff 14 x).mp
        ((show ∀ x : Source, member 12 x → member 14 x from by decide +kernel) x ((member_iff 12 x).mpr hx'))
    · intro x hx
      exact (member_iff 14 x).mp
        ((show ∀ x : Source, member 5 x → member 14 x from by decide +kernel) x ((member_iff 5 x).mpr hx))
  · change Subgroup.closure (Set.range BinaryNormal8T11.N14.normalGenerators)≤_
    apply (Subgroup.closure_le _).mpr
    rintro _ ⟨j,rfl⟩
    have he : ∀ j, kernelPart j*normalPart j=BinaryNormal8T11.N14.normalGenerators j := by decide +kernel
    rw [← he j]
    apply Subgroup.mul_mem
    · apply (show top.ker≤top.ker⊔BinaryNormal8T11.N5.kernel from le_sup_left)
      rw [kernel_eq]
      exact (member_iff 12 _).mp ((show ∀ j, member 12 (kernelPart j) from by decide +kernel) j)
    · apply (show BinaryNormal8T11.N5.kernel≤top.ker⊔BinaryNormal8T11.N5.kernel from le_sup_right)
      exact (member_iff 5 _).mp ((show ∀ j, member 5 (normalPart j) from by decide +kernel) j)

private def cover0 : Equiv.Perm (Fin 2) where
  toFun x := (#[1,0] : Array (Fin 2))[x.val]!
  invFun x := (#[1,0] : Array (Fin 2))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel
private def cover1 : Equiv.Perm (Fin 2) where
  toFun x := (#[0,1] : Array (Fin 2))[x.val]!
  invFun x := (#[0,1] : Array (Fin 2))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

private def coverValues (i : Fin 16) : Equiv.Perm (Fin 2) := (if i.val < 8 then (if i.val < 4 then (if i.val < 2 then (if i.val < 1 then cover1 else cover1) else (if i.val < 3 then cover0 else cover0)) else (if i.val < 6 then (if i.val < 5 then cover0 else cover0) else (if i.val < 7 then cover1 else cover1))) else (if i.val < 12 then (if i.val < 10 then (if i.val < 9 then cover1 else cover1) else (if i.val < 11 then cover0 else cover0)) else (if i.val < 14 then (if i.val < 13 then cover0 else cover0) else (if i.val < 15 then cover1 else cover1))))
private def coverImages (j : Fin 3) : Equiv.Perm (Fin 2) := (if j.val < 1 then cover1 else (if j.val < 2 then cover0 else cover1))
private theorem cover_step : ∀ i j,
    coverValues (BinaryMenuCayley8T11.certificate.next i j)=coverValues i*coverImages j := (by decide +kernel)
private theorem cover_identity : coverValues BinaryMenuCayley8T11.certificate.identity=1 := by decide +kernel

def cover : Source →* Equiv.Perm (Fin 2) where
  toFun x := coverValues x.index
  map_one' := cover_identity
  map_mul' x y := by
    change coverValues (BinaryMenuCayley8T11.certificate.walk x.index
      (BinaryMenuCayley8T11.certificate.words y.index))=coverValues x.index*coverValues y.index
    rw [EncodedCayleyCertificate.values_walk _ coverValues coverImages cover_step,
      ← EncodedCayleyCertificate.values_word _ coverValues coverImages cover_step cover_identity]

theorem cover_kernel : cover.ker=top.ker⊔BinaryNormal8T11.N5.kernel := by
  rw [join_eq]
  ext x
  change cover x=1 ↔ x∈(BinaryNormal8T11.states 14).kernel
  rw [← member_iff]
  exact (show ∀ x : Source, cover x=1 ↔ member 14 x from by decide +kernel) x

/-- Every local numerical dimension follows from checked original subgroup
orders and maps; the selected original cut and full fixed preimage remain. -/
def certificate : BinaryPairLocalCertificate generators top BinaryNormal8T11.N5.kernel where
  cut := BinaryNormal8T11.N12.kernel
  cut_normal := inferInstance
  cut_le_kernel := cut_le
  intersection_le_cut := intersection_le
  central := cut_central
  cutDimension := 1
  fixedDimension := 0
  cut_card := by simp only [intersection_eq,BinaryNormal8T11.N12.kernel_card,BinaryNormal8T11.N1.kernel_card] <;> decide
  fixed_card := by simp only [fixed_eq,BinaryNormal8T11.N12.kernel_card,BinaryNormal8T11.N12.kernel_card] <;> decide
  coverDegree := 2
  cover := cover
  cover_kernel := cover_kernel
  width := 8
  gap := by decide

end N5

namespace N6

theorem intersection_eq : top.ker⊓BinaryNormal8T11.N6.kernel=BinaryNormal8T11.N1.kernel := by
  rw [kernel_eq]
  ext x
  change (x∈(BinaryNormal8T11.states 12).kernel ∧ x∈(BinaryNormal8T11.states 6).kernel) ↔ x∈(BinaryNormal8T11.states 1).kernel
  simp only [← member_iff]
  exact (show ∀ x : Source, (member 12 x ∧ member 6 x) ↔ member 1 x from by decide +kernel) x

theorem cut_le : BinaryNormal8T11.N12.kernel≤top.ker := by
  intro x hx
  have hk : x∈BinaryNormal8T11.N12.kernel := (member_iff 12 x).mp
    ((show ∀ x : Source, member 12 x → member 12 x from by decide +kernel) x ((member_iff 12 x).mpr hx))
  exact kernel_eq.symm ▸ hk

theorem intersection_le : top.ker⊓BinaryNormal8T11.N6.kernel≤BinaryNormal8T11.N12.kernel := by
  intro x hx
  have hx' : x∈BinaryNormal8T11.N1.kernel := intersection_eq ▸ hx
  apply (member_iff 12 x).mp
  exact (show ∀ x : Source, member 1 x → member 12 x from by decide +kernel) x ((member_iff 1 x).mpr hx')

theorem cut_central : ∀ j, ∀ x : BinaryNormal8T11.N12.kernel,
    (x:Source)⁻¹*(generators j*(x:Source)*(generators j)⁻¹)∈BinaryNormal8T11.N6.kernel := by
  have h : ∀ j, ∀ x : Source, member 12 x →
      member 6 (x⁻¹*(generators j*x*(generators j)⁻¹)) := by decide +kernel
  intro j x
  exact (member_iff 6 _).mp (h j x.val ((member_iff 12 x.val).mpr x.property))

theorem fixed_eq : binaryPairFixedSubgroup top.ker BinaryNormal8T11.N12.kernel=BinaryNormal8T11.N12.kernel := by
  rw [kernel_eq]
  ext x
  rw [binaryPairFixedSubgroup_mem_iff _ _ generators BinaryNormal8T11.generators_full]
  change (x∈(BinaryNormal8T11.states 12).kernel ∧ ∀ j,
    x⁻¹*(generators j*x*(generators j)⁻¹)∈(BinaryNormal8T11.states 12).kernel) ↔ x∈(BinaryNormal8T11.states 12).kernel
  simp only [← member_iff]
  exact (show ∀ x : Source, (member 12 x ∧ ∀ j,
    member 12 (x⁻¹*(generators j*x*(generators j)⁻¹))) ↔ member 12 x from by decide +kernel) x

/-- These are the actual selected cut lift generators from this record. -/
def recordedCutGenerators (j : Fin 2) : Source := ⟨((if j.val < 1 then 7 else 6) : Fin 16)⟩
private def cutWords (j : Fin 2) : List (Fin 2) := (if j.val < 1 then ([0] : List (Fin 2)) else ([0, 1] : List (Fin 2)))
private theorem cutWords_checked : ∀ j,
    ((cutWords j).map recordedCutGenerators).prod=BinaryNormal8T11.N12.normalGenerators j := by decide +kernel

theorem recorded_cut_eq : Subgroup.closure (Set.range recordedCutGenerators)=BinaryNormal8T11.N12.kernel := by
  apply le_antisymm
  · apply (Subgroup.closure_le _).mpr
    rintro _ ⟨j,rfl⟩
    exact (member_iff 12 _).mp
      ((show ∀ j, member 12 (recordedCutGenerators j) from by decide +kernel) j)
  · exact (BinaryNormalGeneratorWords.closure_le
      ({words := cutWords, equations := cutWords_checked} :
        BinaryNormalGeneratorWords BinaryNormal8T11.N12.normalGenerators recordedCutGenerators))

private def kernelPart (j : Fin 3) : Source := ⟨((if j.val < 1 then 7 else (if j.val < 2 then 7 else 7)) : Fin 16)⟩
private def normalPart (j : Fin 3) : Source := ⟨((if j.val < 1 then 10 else (if j.val < 2 then 15 else 6)) : Fin 16)⟩

theorem join_eq : top.ker⊔BinaryNormal8T11.N6.kernel=BinaryNormal8T11.N15.kernel := by
  apply le_antisymm
  · apply sup_le
    · intro x hx
      have hx' : x∈BinaryNormal8T11.N12.kernel := kernel_eq ▸ hx
      exact (member_iff 15 x).mp
        ((show ∀ x : Source, member 12 x → member 15 x from by decide +kernel) x ((member_iff 12 x).mpr hx'))
    · intro x hx
      exact (member_iff 15 x).mp
        ((show ∀ x : Source, member 6 x → member 15 x from by decide +kernel) x ((member_iff 6 x).mpr hx))
  · change Subgroup.closure (Set.range BinaryNormal8T11.N15.normalGenerators)≤_
    apply (Subgroup.closure_le _).mpr
    rintro _ ⟨j,rfl⟩
    have he : ∀ j, kernelPart j*normalPart j=BinaryNormal8T11.N15.normalGenerators j := by decide +kernel
    rw [← he j]
    apply Subgroup.mul_mem
    · apply (show top.ker≤top.ker⊔BinaryNormal8T11.N6.kernel from le_sup_left)
      rw [kernel_eq]
      exact (member_iff 12 _).mp ((show ∀ j, member 12 (kernelPart j) from by decide +kernel) j)
    · apply (show BinaryNormal8T11.N6.kernel≤top.ker⊔BinaryNormal8T11.N6.kernel from le_sup_right)
      exact (member_iff 6 _).mp ((show ∀ j, member 6 (normalPart j) from by decide +kernel) j)

private def cover0 : Equiv.Perm (Fin 2) where
  toFun x := (#[1,0] : Array (Fin 2))[x.val]!
  invFun x := (#[1,0] : Array (Fin 2))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel
private def cover1 : Equiv.Perm (Fin 2) where
  toFun x := (#[0,1] : Array (Fin 2))[x.val]!
  invFun x := (#[0,1] : Array (Fin 2))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

private def coverValues (i : Fin 16) : Equiv.Perm (Fin 2) := (if i.val < 8 then (if i.val < 4 then (if i.val < 2 then (if i.val < 1 then cover0 else cover0) else (if i.val < 3 then cover1 else cover1)) else (if i.val < 6 then (if i.val < 5 then cover0 else cover0) else (if i.val < 7 then cover1 else cover1))) else (if i.val < 12 then (if i.val < 10 then (if i.val < 9 then cover0 else cover0) else (if i.val < 11 then cover1 else cover1)) else (if i.val < 14 then (if i.val < 13 then cover0 else cover0) else (if i.val < 15 then cover1 else cover1))))
private def coverImages (j : Fin 3) : Equiv.Perm (Fin 2) := (if j.val < 1 then cover1 else (if j.val < 2 then cover1 else cover0))
private theorem cover_step : ∀ i j,
    coverValues (BinaryMenuCayley8T11.certificate.next i j)=coverValues i*coverImages j := (by decide +kernel)
private theorem cover_identity : coverValues BinaryMenuCayley8T11.certificate.identity=1 := by decide +kernel

def cover : Source →* Equiv.Perm (Fin 2) where
  toFun x := coverValues x.index
  map_one' := cover_identity
  map_mul' x y := by
    change coverValues (BinaryMenuCayley8T11.certificate.walk x.index
      (BinaryMenuCayley8T11.certificate.words y.index))=coverValues x.index*coverValues y.index
    rw [EncodedCayleyCertificate.values_walk _ coverValues coverImages cover_step,
      ← EncodedCayleyCertificate.values_word _ coverValues coverImages cover_step cover_identity]

theorem cover_kernel : cover.ker=top.ker⊔BinaryNormal8T11.N6.kernel := by
  rw [join_eq]
  ext x
  change cover x=1 ↔ x∈(BinaryNormal8T11.states 15).kernel
  rw [← member_iff]
  exact (show ∀ x : Source, cover x=1 ↔ member 15 x from by decide +kernel) x

/-- Every local numerical dimension follows from checked original subgroup
orders and maps; the selected original cut and full fixed preimage remain. -/
def certificate : BinaryPairLocalCertificate generators top BinaryNormal8T11.N6.kernel where
  cut := BinaryNormal8T11.N12.kernel
  cut_normal := inferInstance
  cut_le_kernel := cut_le
  intersection_le_cut := intersection_le
  central := cut_central
  cutDimension := 1
  fixedDimension := 0
  cut_card := by simp only [intersection_eq,BinaryNormal8T11.N12.kernel_card,BinaryNormal8T11.N1.kernel_card] <;> decide
  fixed_card := by simp only [fixed_eq,BinaryNormal8T11.N12.kernel_card,BinaryNormal8T11.N12.kernel_card] <;> decide
  coverDegree := 2
  cover := cover
  cover_kernel := cover_kernel
  width := 8
  gap := by decide

end N6

namespace N7

theorem intersection_eq : top.ker⊓BinaryNormal8T11.N7.kernel=BinaryNormal8T11.N1.kernel := by
  rw [kernel_eq]
  ext x
  change (x∈(BinaryNormal8T11.states 12).kernel ∧ x∈(BinaryNormal8T11.states 7).kernel) ↔ x∈(BinaryNormal8T11.states 1).kernel
  simp only [← member_iff]
  exact (show ∀ x : Source, (member 12 x ∧ member 7 x) ↔ member 1 x from by decide +kernel) x

theorem cut_le : BinaryNormal8T11.N12.kernel≤top.ker := by
  intro x hx
  have hk : x∈BinaryNormal8T11.N12.kernel := (member_iff 12 x).mp
    ((show ∀ x : Source, member 12 x → member 12 x from by decide +kernel) x ((member_iff 12 x).mpr hx))
  exact kernel_eq.symm ▸ hk

theorem intersection_le : top.ker⊓BinaryNormal8T11.N7.kernel≤BinaryNormal8T11.N12.kernel := by
  intro x hx
  have hx' : x∈BinaryNormal8T11.N1.kernel := intersection_eq ▸ hx
  apply (member_iff 12 x).mp
  exact (show ∀ x : Source, member 1 x → member 12 x from by decide +kernel) x ((member_iff 1 x).mpr hx')

theorem cut_central : ∀ j, ∀ x : BinaryNormal8T11.N12.kernel,
    (x:Source)⁻¹*(generators j*(x:Source)*(generators j)⁻¹)∈BinaryNormal8T11.N7.kernel := by
  have h : ∀ j, ∀ x : Source, member 12 x →
      member 7 (x⁻¹*(generators j*x*(generators j)⁻¹)) := by decide +kernel
  intro j x
  exact (member_iff 7 _).mp (h j x.val ((member_iff 12 x.val).mpr x.property))

theorem fixed_eq : binaryPairFixedSubgroup top.ker BinaryNormal8T11.N12.kernel=BinaryNormal8T11.N12.kernel := by
  rw [kernel_eq]
  ext x
  rw [binaryPairFixedSubgroup_mem_iff _ _ generators BinaryNormal8T11.generators_full]
  change (x∈(BinaryNormal8T11.states 12).kernel ∧ ∀ j,
    x⁻¹*(generators j*x*(generators j)⁻¹)∈(BinaryNormal8T11.states 12).kernel) ↔ x∈(BinaryNormal8T11.states 12).kernel
  simp only [← member_iff]
  exact (show ∀ x : Source, (member 12 x ∧ ∀ j,
    member 12 (x⁻¹*(generators j*x*(generators j)⁻¹))) ↔ member 12 x from by decide +kernel) x

/-- These are the actual selected cut lift generators from this record. -/
def recordedCutGenerators (j : Fin 2) : Source := ⟨((if j.val < 1 then 7 else 6) : Fin 16)⟩
private def cutWords (j : Fin 2) : List (Fin 2) := (if j.val < 1 then ([0] : List (Fin 2)) else ([0, 1] : List (Fin 2)))
private theorem cutWords_checked : ∀ j,
    ((cutWords j).map recordedCutGenerators).prod=BinaryNormal8T11.N12.normalGenerators j := by decide +kernel

theorem recorded_cut_eq : Subgroup.closure (Set.range recordedCutGenerators)=BinaryNormal8T11.N12.kernel := by
  apply le_antisymm
  · apply (Subgroup.closure_le _).mpr
    rintro _ ⟨j,rfl⟩
    exact (member_iff 12 _).mp
      ((show ∀ j, member 12 (recordedCutGenerators j) from by decide +kernel) j)
  · exact (BinaryNormalGeneratorWords.closure_le
      ({words := cutWords, equations := cutWords_checked} :
        BinaryNormalGeneratorWords BinaryNormal8T11.N12.normalGenerators recordedCutGenerators))

private def kernelPart (j : Fin 3) : Source := ⟨((if j.val < 1 then 6 else (if j.val < 2 then 7 else 7)) : Fin 16)⟩
private def normalPart (j : Fin 3) : Source := ⟨((if j.val < 1 then 11 else (if j.val < 2 then 15 else 6)) : Fin 16)⟩

theorem join_eq : top.ker⊔BinaryNormal8T11.N7.kernel=BinaryNormal8T11.N15.kernel := by
  apply le_antisymm
  · apply sup_le
    · intro x hx
      have hx' : x∈BinaryNormal8T11.N12.kernel := kernel_eq ▸ hx
      exact (member_iff 15 x).mp
        ((show ∀ x : Source, member 12 x → member 15 x from by decide +kernel) x ((member_iff 12 x).mpr hx'))
    · intro x hx
      exact (member_iff 15 x).mp
        ((show ∀ x : Source, member 7 x → member 15 x from by decide +kernel) x ((member_iff 7 x).mpr hx))
  · change Subgroup.closure (Set.range BinaryNormal8T11.N15.normalGenerators)≤_
    apply (Subgroup.closure_le _).mpr
    rintro _ ⟨j,rfl⟩
    have he : ∀ j, kernelPart j*normalPart j=BinaryNormal8T11.N15.normalGenerators j := by decide +kernel
    rw [← he j]
    apply Subgroup.mul_mem
    · apply (show top.ker≤top.ker⊔BinaryNormal8T11.N7.kernel from le_sup_left)
      rw [kernel_eq]
      exact (member_iff 12 _).mp ((show ∀ j, member 12 (kernelPart j) from by decide +kernel) j)
    · apply (show BinaryNormal8T11.N7.kernel≤top.ker⊔BinaryNormal8T11.N7.kernel from le_sup_right)
      exact (member_iff 7 _).mp ((show ∀ j, member 7 (normalPart j) from by decide +kernel) j)

private def cover0 : Equiv.Perm (Fin 2) where
  toFun x := (#[1,0] : Array (Fin 2))[x.val]!
  invFun x := (#[1,0] : Array (Fin 2))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel
private def cover1 : Equiv.Perm (Fin 2) where
  toFun x := (#[0,1] : Array (Fin 2))[x.val]!
  invFun x := (#[0,1] : Array (Fin 2))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

private def coverValues (i : Fin 16) : Equiv.Perm (Fin 2) := (if i.val < 8 then (if i.val < 4 then (if i.val < 2 then (if i.val < 1 then cover0 else cover0) else (if i.val < 3 then cover1 else cover1)) else (if i.val < 6 then (if i.val < 5 then cover0 else cover0) else (if i.val < 7 then cover1 else cover1))) else (if i.val < 12 then (if i.val < 10 then (if i.val < 9 then cover0 else cover0) else (if i.val < 11 then cover1 else cover1)) else (if i.val < 14 then (if i.val < 13 then cover0 else cover0) else (if i.val < 15 then cover1 else cover1))))
private def coverImages (j : Fin 3) : Equiv.Perm (Fin 2) := (if j.val < 1 then cover1 else (if j.val < 2 then cover1 else cover0))
private theorem cover_step : ∀ i j,
    coverValues (BinaryMenuCayley8T11.certificate.next i j)=coverValues i*coverImages j := (by decide +kernel)
private theorem cover_identity : coverValues BinaryMenuCayley8T11.certificate.identity=1 := by decide +kernel

def cover : Source →* Equiv.Perm (Fin 2) where
  toFun x := coverValues x.index
  map_one' := cover_identity
  map_mul' x y := by
    change coverValues (BinaryMenuCayley8T11.certificate.walk x.index
      (BinaryMenuCayley8T11.certificate.words y.index))=coverValues x.index*coverValues y.index
    rw [EncodedCayleyCertificate.values_walk _ coverValues coverImages cover_step,
      ← EncodedCayleyCertificate.values_word _ coverValues coverImages cover_step cover_identity]

theorem cover_kernel : cover.ker=top.ker⊔BinaryNormal8T11.N7.kernel := by
  rw [join_eq]
  ext x
  change cover x=1 ↔ x∈(BinaryNormal8T11.states 15).kernel
  rw [← member_iff]
  exact (show ∀ x : Source, cover x=1 ↔ member 15 x from by decide +kernel) x

/-- Every local numerical dimension follows from checked original subgroup
orders and maps; the selected original cut and full fixed preimage remain. -/
def certificate : BinaryPairLocalCertificate generators top BinaryNormal8T11.N7.kernel where
  cut := BinaryNormal8T11.N12.kernel
  cut_normal := inferInstance
  cut_le_kernel := cut_le
  intersection_le_cut := intersection_le
  central := cut_central
  cutDimension := 1
  fixedDimension := 0
  cut_card := by simp only [intersection_eq,BinaryNormal8T11.N12.kernel_card,BinaryNormal8T11.N1.kernel_card] <;> decide
  fixed_card := by simp only [fixed_eq,BinaryNormal8T11.N12.kernel_card,BinaryNormal8T11.N12.kernel_card] <;> decide
  coverDegree := 2
  cover := cover
  cover_kernel := cover_kernel
  width := 8
  gap := by decide

end N7

namespace N8

theorem intersection_eq : top.ker⊓BinaryNormal8T11.N8.kernel=BinaryNormal8T11.N1.kernel := by
  rw [kernel_eq]
  ext x
  change (x∈(BinaryNormal8T11.states 12).kernel ∧ x∈(BinaryNormal8T11.states 8).kernel) ↔ x∈(BinaryNormal8T11.states 1).kernel
  simp only [← member_iff]
  exact (show ∀ x : Source, (member 12 x ∧ member 8 x) ↔ member 1 x from by decide +kernel) x

theorem cut_le : BinaryNormal8T11.N12.kernel≤top.ker := by
  intro x hx
  have hk : x∈BinaryNormal8T11.N12.kernel := (member_iff 12 x).mp
    ((show ∀ x : Source, member 12 x → member 12 x from by decide +kernel) x ((member_iff 12 x).mpr hx))
  exact kernel_eq.symm ▸ hk

theorem intersection_le : top.ker⊓BinaryNormal8T11.N8.kernel≤BinaryNormal8T11.N12.kernel := by
  intro x hx
  have hx' : x∈BinaryNormal8T11.N1.kernel := intersection_eq ▸ hx
  apply (member_iff 12 x).mp
  exact (show ∀ x : Source, member 1 x → member 12 x from by decide +kernel) x ((member_iff 1 x).mpr hx')

theorem cut_central : ∀ j, ∀ x : BinaryNormal8T11.N12.kernel,
    (x:Source)⁻¹*(generators j*(x:Source)*(generators j)⁻¹)∈BinaryNormal8T11.N8.kernel := by
  have h : ∀ j, ∀ x : Source, member 12 x →
      member 8 (x⁻¹*(generators j*x*(generators j)⁻¹)) := by decide +kernel
  intro j x
  exact (member_iff 8 _).mp (h j x.val ((member_iff 12 x.val).mpr x.property))

theorem fixed_eq : binaryPairFixedSubgroup top.ker BinaryNormal8T11.N12.kernel=BinaryNormal8T11.N12.kernel := by
  rw [kernel_eq]
  ext x
  rw [binaryPairFixedSubgroup_mem_iff _ _ generators BinaryNormal8T11.generators_full]
  change (x∈(BinaryNormal8T11.states 12).kernel ∧ ∀ j,
    x⁻¹*(generators j*x*(generators j)⁻¹)∈(BinaryNormal8T11.states 12).kernel) ↔ x∈(BinaryNormal8T11.states 12).kernel
  simp only [← member_iff]
  exact (show ∀ x : Source, (member 12 x ∧ ∀ j,
    member 12 (x⁻¹*(generators j*x*(generators j)⁻¹))) ↔ member 12 x from by decide +kernel) x

/-- These are the actual selected cut lift generators from this record. -/
def recordedCutGenerators (j : Fin 2) : Source := ⟨((if j.val < 1 then 7 else 6) : Fin 16)⟩
private def cutWords (j : Fin 2) : List (Fin 2) := (if j.val < 1 then ([0] : List (Fin 2)) else ([0, 1] : List (Fin 2)))
private theorem cutWords_checked : ∀ j,
    ((cutWords j).map recordedCutGenerators).prod=BinaryNormal8T11.N12.normalGenerators j := by decide +kernel

theorem recorded_cut_eq : Subgroup.closure (Set.range recordedCutGenerators)=BinaryNormal8T11.N12.kernel := by
  apply le_antisymm
  · apply (Subgroup.closure_le _).mpr
    rintro _ ⟨j,rfl⟩
    exact (member_iff 12 _).mp
      ((show ∀ j, member 12 (recordedCutGenerators j) from by decide +kernel) j)
  · exact (BinaryNormalGeneratorWords.closure_le
      ({words := cutWords, equations := cutWords_checked} :
        BinaryNormalGeneratorWords BinaryNormal8T11.N12.normalGenerators recordedCutGenerators))

private def kernelPart (j : Fin 3) : Source := ⟨((if j.val < 1 then 7 else (if j.val < 2 then 7 else 7)) : Fin 16)⟩
private def normalPart (j : Fin 3) : Source := ⟨((if j.val < 1 then 10 else (if j.val < 2 then 1 else 6)) : Fin 16)⟩

theorem join_eq : top.ker⊔BinaryNormal8T11.N8.kernel=BinaryNormal8T11.N16.kernel := by
  apply le_antisymm
  · apply sup_le
    · intro x hx
      have hx' : x∈BinaryNormal8T11.N12.kernel := kernel_eq ▸ hx
      exact (member_iff 16 x).mp
        ((show ∀ x : Source, member 12 x → member 16 x from by decide +kernel) x ((member_iff 12 x).mpr hx'))
    · intro x hx
      exact (member_iff 16 x).mp
        ((show ∀ x : Source, member 8 x → member 16 x from by decide +kernel) x ((member_iff 8 x).mpr hx))
  · change Subgroup.closure (Set.range BinaryNormal8T11.N16.normalGenerators)≤_
    apply (Subgroup.closure_le _).mpr
    rintro _ ⟨j,rfl⟩
    have he : ∀ j, kernelPart j*normalPart j=BinaryNormal8T11.N16.normalGenerators j := by decide +kernel
    rw [← he j]
    apply Subgroup.mul_mem
    · apply (show top.ker≤top.ker⊔BinaryNormal8T11.N8.kernel from le_sup_left)
      rw [kernel_eq]
      exact (member_iff 12 _).mp ((show ∀ j, member 12 (kernelPart j) from by decide +kernel) j)
    · apply (show BinaryNormal8T11.N8.kernel≤top.ker⊔BinaryNormal8T11.N8.kernel from le_sup_right)
      exact (member_iff 8 _).mp ((show ∀ j, member 8 (normalPart j) from by decide +kernel) j)

private def cover0 : Equiv.Perm (Fin 0) where
  toFun := Fin.elim0
  invFun := Fin.elim0
  left_inv := fun x => Fin.elim0 x
  right_inv := fun x => Fin.elim0 x

private def coverValues (i : Fin 16) : Equiv.Perm (Fin 0) := (if i.val < 8 then (if i.val < 4 then (if i.val < 2 then (if i.val < 1 then cover0 else cover0) else (if i.val < 3 then cover0 else cover0)) else (if i.val < 6 then (if i.val < 5 then cover0 else cover0) else (if i.val < 7 then cover0 else cover0))) else (if i.val < 12 then (if i.val < 10 then (if i.val < 9 then cover0 else cover0) else (if i.val < 11 then cover0 else cover0)) else (if i.val < 14 then (if i.val < 13 then cover0 else cover0) else (if i.val < 15 then cover0 else cover0))))
private def coverImages (j : Fin 3) : Equiv.Perm (Fin 0) := (if j.val < 1 then cover0 else (if j.val < 2 then cover0 else cover0))
private theorem cover_step : ∀ i j,
    coverValues (BinaryMenuCayley8T11.certificate.next i j)=coverValues i*coverImages j := (by decide +kernel)
private theorem cover_identity : coverValues BinaryMenuCayley8T11.certificate.identity=1 := by decide +kernel

def cover : Source →* Equiv.Perm (Fin 0) where
  toFun x := coverValues x.index
  map_one' := cover_identity
  map_mul' x y := by
    change coverValues (BinaryMenuCayley8T11.certificate.walk x.index
      (BinaryMenuCayley8T11.certificate.words y.index))=coverValues x.index*coverValues y.index
    rw [EncodedCayleyCertificate.values_walk _ coverValues coverImages cover_step,
      ← EncodedCayleyCertificate.values_word _ coverValues coverImages cover_step cover_identity]

theorem cover_kernel : cover.ker=top.ker⊔BinaryNormal8T11.N8.kernel := by
  rw [join_eq]
  ext x
  change cover x=1 ↔ x∈(BinaryNormal8T11.states 16).kernel
  rw [← member_iff]
  exact (show ∀ x : Source, cover x=1 ↔ member 16 x from by decide +kernel) x

/-- Every local numerical dimension follows from checked original subgroup
orders and maps; the selected original cut and full fixed preimage remain. -/
def certificate : BinaryPairLocalCertificate generators top BinaryNormal8T11.N8.kernel where
  cut := BinaryNormal8T11.N12.kernel
  cut_normal := inferInstance
  cut_le_kernel := cut_le
  intersection_le_cut := intersection_le
  central := cut_central
  cutDimension := 1
  fixedDimension := 0
  cut_card := by simp only [intersection_eq,BinaryNormal8T11.N12.kernel_card,BinaryNormal8T11.N1.kernel_card] <;> decide
  fixed_card := by simp only [fixed_eq,BinaryNormal8T11.N12.kernel_card,BinaryNormal8T11.N12.kernel_card] <;> decide
  coverDegree := 0
  cover := cover
  cover_kernel := cover_kernel
  width := 8
  gap := by decide

end N8

namespace N9

theorem intersection_eq : top.ker⊓BinaryNormal8T11.N9.kernel=BinaryNormal8T11.N1.kernel := by
  rw [kernel_eq]
  ext x
  change (x∈(BinaryNormal8T11.states 12).kernel ∧ x∈(BinaryNormal8T11.states 9).kernel) ↔ x∈(BinaryNormal8T11.states 1).kernel
  simp only [← member_iff]
  exact (show ∀ x : Source, (member 12 x ∧ member 9 x) ↔ member 1 x from by decide +kernel) x

theorem cut_le : BinaryNormal8T11.N12.kernel≤top.ker := by
  intro x hx
  have hk : x∈BinaryNormal8T11.N12.kernel := (member_iff 12 x).mp
    ((show ∀ x : Source, member 12 x → member 12 x from by decide +kernel) x ((member_iff 12 x).mpr hx))
  exact kernel_eq.symm ▸ hk

theorem intersection_le : top.ker⊓BinaryNormal8T11.N9.kernel≤BinaryNormal8T11.N12.kernel := by
  intro x hx
  have hx' : x∈BinaryNormal8T11.N1.kernel := intersection_eq ▸ hx
  apply (member_iff 12 x).mp
  exact (show ∀ x : Source, member 1 x → member 12 x from by decide +kernel) x ((member_iff 1 x).mpr hx')

theorem cut_central : ∀ j, ∀ x : BinaryNormal8T11.N12.kernel,
    (x:Source)⁻¹*(generators j*(x:Source)*(generators j)⁻¹)∈BinaryNormal8T11.N9.kernel := by
  have h : ∀ j, ∀ x : Source, member 12 x →
      member 9 (x⁻¹*(generators j*x*(generators j)⁻¹)) := by decide +kernel
  intro j x
  exact (member_iff 9 _).mp (h j x.val ((member_iff 12 x.val).mpr x.property))

theorem fixed_eq : binaryPairFixedSubgroup top.ker BinaryNormal8T11.N12.kernel=BinaryNormal8T11.N12.kernel := by
  rw [kernel_eq]
  ext x
  rw [binaryPairFixedSubgroup_mem_iff _ _ generators BinaryNormal8T11.generators_full]
  change (x∈(BinaryNormal8T11.states 12).kernel ∧ ∀ j,
    x⁻¹*(generators j*x*(generators j)⁻¹)∈(BinaryNormal8T11.states 12).kernel) ↔ x∈(BinaryNormal8T11.states 12).kernel
  simp only [← member_iff]
  exact (show ∀ x : Source, (member 12 x ∧ ∀ j,
    member 12 (x⁻¹*(generators j*x*(generators j)⁻¹))) ↔ member 12 x from by decide +kernel) x

/-- These are the actual selected cut lift generators from this record. -/
def recordedCutGenerators (j : Fin 2) : Source := ⟨((if j.val < 1 then 7 else 6) : Fin 16)⟩
private def cutWords (j : Fin 2) : List (Fin 2) := (if j.val < 1 then ([0] : List (Fin 2)) else ([0, 1] : List (Fin 2)))
private theorem cutWords_checked : ∀ j,
    ((cutWords j).map recordedCutGenerators).prod=BinaryNormal8T11.N12.normalGenerators j := by decide +kernel

theorem recorded_cut_eq : Subgroup.closure (Set.range recordedCutGenerators)=BinaryNormal8T11.N12.kernel := by
  apply le_antisymm
  · apply (Subgroup.closure_le _).mpr
    rintro _ ⟨j,rfl⟩
    exact (member_iff 12 _).mp
      ((show ∀ j, member 12 (recordedCutGenerators j) from by decide +kernel) j)
  · exact (BinaryNormalGeneratorWords.closure_le
      ({words := cutWords, equations := cutWords_checked} :
        BinaryNormalGeneratorWords BinaryNormal8T11.N12.normalGenerators recordedCutGenerators))

private def kernelPart (j : Fin 3) : Source := ⟨((if j.val < 1 then 6 else (if j.val < 2 then 7 else 7)) : Fin 16)⟩
private def normalPart (j : Fin 3) : Source := ⟨((if j.val < 1 then 11 else (if j.val < 2 then 1 else 6)) : Fin 16)⟩

theorem join_eq : top.ker⊔BinaryNormal8T11.N9.kernel=BinaryNormal8T11.N16.kernel := by
  apply le_antisymm
  · apply sup_le
    · intro x hx
      have hx' : x∈BinaryNormal8T11.N12.kernel := kernel_eq ▸ hx
      exact (member_iff 16 x).mp
        ((show ∀ x : Source, member 12 x → member 16 x from by decide +kernel) x ((member_iff 12 x).mpr hx'))
    · intro x hx
      exact (member_iff 16 x).mp
        ((show ∀ x : Source, member 9 x → member 16 x from by decide +kernel) x ((member_iff 9 x).mpr hx))
  · change Subgroup.closure (Set.range BinaryNormal8T11.N16.normalGenerators)≤_
    apply (Subgroup.closure_le _).mpr
    rintro _ ⟨j,rfl⟩
    have he : ∀ j, kernelPart j*normalPart j=BinaryNormal8T11.N16.normalGenerators j := by decide +kernel
    rw [← he j]
    apply Subgroup.mul_mem
    · apply (show top.ker≤top.ker⊔BinaryNormal8T11.N9.kernel from le_sup_left)
      rw [kernel_eq]
      exact (member_iff 12 _).mp ((show ∀ j, member 12 (kernelPart j) from by decide +kernel) j)
    · apply (show BinaryNormal8T11.N9.kernel≤top.ker⊔BinaryNormal8T11.N9.kernel from le_sup_right)
      exact (member_iff 9 _).mp ((show ∀ j, member 9 (normalPart j) from by decide +kernel) j)

private def cover0 : Equiv.Perm (Fin 0) where
  toFun := Fin.elim0
  invFun := Fin.elim0
  left_inv := fun x => Fin.elim0 x
  right_inv := fun x => Fin.elim0 x

private def coverValues (i : Fin 16) : Equiv.Perm (Fin 0) := (if i.val < 8 then (if i.val < 4 then (if i.val < 2 then (if i.val < 1 then cover0 else cover0) else (if i.val < 3 then cover0 else cover0)) else (if i.val < 6 then (if i.val < 5 then cover0 else cover0) else (if i.val < 7 then cover0 else cover0))) else (if i.val < 12 then (if i.val < 10 then (if i.val < 9 then cover0 else cover0) else (if i.val < 11 then cover0 else cover0)) else (if i.val < 14 then (if i.val < 13 then cover0 else cover0) else (if i.val < 15 then cover0 else cover0))))
private def coverImages (j : Fin 3) : Equiv.Perm (Fin 0) := (if j.val < 1 then cover0 else (if j.val < 2 then cover0 else cover0))
private theorem cover_step : ∀ i j,
    coverValues (BinaryMenuCayley8T11.certificate.next i j)=coverValues i*coverImages j := (by decide +kernel)
private theorem cover_identity : coverValues BinaryMenuCayley8T11.certificate.identity=1 := by decide +kernel

def cover : Source →* Equiv.Perm (Fin 0) where
  toFun x := coverValues x.index
  map_one' := cover_identity
  map_mul' x y := by
    change coverValues (BinaryMenuCayley8T11.certificate.walk x.index
      (BinaryMenuCayley8T11.certificate.words y.index))=coverValues x.index*coverValues y.index
    rw [EncodedCayleyCertificate.values_walk _ coverValues coverImages cover_step,
      ← EncodedCayleyCertificate.values_word _ coverValues coverImages cover_step cover_identity]

theorem cover_kernel : cover.ker=top.ker⊔BinaryNormal8T11.N9.kernel := by
  rw [join_eq]
  ext x
  change cover x=1 ↔ x∈(BinaryNormal8T11.states 16).kernel
  rw [← member_iff]
  exact (show ∀ x : Source, cover x=1 ↔ member 16 x from by decide +kernel) x

/-- Every local numerical dimension follows from checked original subgroup
orders and maps; the selected original cut and full fixed preimage remain. -/
def certificate : BinaryPairLocalCertificate generators top BinaryNormal8T11.N9.kernel where
  cut := BinaryNormal8T11.N12.kernel
  cut_normal := inferInstance
  cut_le_kernel := cut_le
  intersection_le_cut := intersection_le
  central := cut_central
  cutDimension := 1
  fixedDimension := 0
  cut_card := by simp only [intersection_eq,BinaryNormal8T11.N12.kernel_card,BinaryNormal8T11.N1.kernel_card] <;> decide
  fixed_card := by simp only [fixed_eq,BinaryNormal8T11.N12.kernel_card,BinaryNormal8T11.N12.kernel_card] <;> decide
  coverDegree := 0
  cover := cover
  cover_kernel := cover_kernel
  width := 8
  gap := by decide

end N9

namespace N10

theorem intersection_eq : top.ker⊓BinaryNormal8T11.N10.kernel=BinaryNormal8T11.N1.kernel := by
  rw [kernel_eq]
  ext x
  change (x∈(BinaryNormal8T11.states 12).kernel ∧ x∈(BinaryNormal8T11.states 10).kernel) ↔ x∈(BinaryNormal8T11.states 1).kernel
  simp only [← member_iff]
  exact (show ∀ x : Source, (member 12 x ∧ member 10 x) ↔ member 1 x from by decide +kernel) x

theorem cut_le : BinaryNormal8T11.N12.kernel≤top.ker := by
  intro x hx
  have hk : x∈BinaryNormal8T11.N12.kernel := (member_iff 12 x).mp
    ((show ∀ x : Source, member 12 x → member 12 x from by decide +kernel) x ((member_iff 12 x).mpr hx))
  exact kernel_eq.symm ▸ hk

theorem intersection_le : top.ker⊓BinaryNormal8T11.N10.kernel≤BinaryNormal8T11.N12.kernel := by
  intro x hx
  have hx' : x∈BinaryNormal8T11.N1.kernel := intersection_eq ▸ hx
  apply (member_iff 12 x).mp
  exact (show ∀ x : Source, member 1 x → member 12 x from by decide +kernel) x ((member_iff 1 x).mpr hx')

theorem cut_central : ∀ j, ∀ x : BinaryNormal8T11.N12.kernel,
    (x:Source)⁻¹*(generators j*(x:Source)*(generators j)⁻¹)∈BinaryNormal8T11.N10.kernel := by
  have h : ∀ j, ∀ x : Source, member 12 x →
      member 10 (x⁻¹*(generators j*x*(generators j)⁻¹)) := by decide +kernel
  intro j x
  exact (member_iff 10 _).mp (h j x.val ((member_iff 12 x.val).mpr x.property))

theorem fixed_eq : binaryPairFixedSubgroup top.ker BinaryNormal8T11.N12.kernel=BinaryNormal8T11.N12.kernel := by
  rw [kernel_eq]
  ext x
  rw [binaryPairFixedSubgroup_mem_iff _ _ generators BinaryNormal8T11.generators_full]
  change (x∈(BinaryNormal8T11.states 12).kernel ∧ ∀ j,
    x⁻¹*(generators j*x*(generators j)⁻¹)∈(BinaryNormal8T11.states 12).kernel) ↔ x∈(BinaryNormal8T11.states 12).kernel
  simp only [← member_iff]
  exact (show ∀ x : Source, (member 12 x ∧ ∀ j,
    member 12 (x⁻¹*(generators j*x*(generators j)⁻¹))) ↔ member 12 x from by decide +kernel) x

/-- These are the actual selected cut lift generators from this record. -/
def recordedCutGenerators (j : Fin 2) : Source := ⟨((if j.val < 1 then 7 else 6) : Fin 16)⟩
private def cutWords (j : Fin 2) : List (Fin 2) := (if j.val < 1 then ([0] : List (Fin 2)) else ([0, 1] : List (Fin 2)))
private theorem cutWords_checked : ∀ j,
    ((cutWords j).map recordedCutGenerators).prod=BinaryNormal8T11.N12.normalGenerators j := by decide +kernel

theorem recorded_cut_eq : Subgroup.closure (Set.range recordedCutGenerators)=BinaryNormal8T11.N12.kernel := by
  apply le_antisymm
  · apply (Subgroup.closure_le _).mpr
    rintro _ ⟨j,rfl⟩
    exact (member_iff 12 _).mp
      ((show ∀ j, member 12 (recordedCutGenerators j) from by decide +kernel) j)
  · exact (BinaryNormalGeneratorWords.closure_le
      ({words := cutWords, equations := cutWords_checked} :
        BinaryNormalGeneratorWords BinaryNormal8T11.N12.normalGenerators recordedCutGenerators))

private def kernelPart (j : Fin 3) : Source := ⟨((if j.val < 1 then 7 else (if j.val < 2 then 6 else 7)) : Fin 16)⟩
private def normalPart (j : Fin 3) : Source := ⟨((if j.val < 1 then 10 else (if j.val < 2 then 9 else 6)) : Fin 16)⟩

theorem join_eq : top.ker⊔BinaryNormal8T11.N10.kernel=BinaryNormal8T11.N16.kernel := by
  apply le_antisymm
  · apply sup_le
    · intro x hx
      have hx' : x∈BinaryNormal8T11.N12.kernel := kernel_eq ▸ hx
      exact (member_iff 16 x).mp
        ((show ∀ x : Source, member 12 x → member 16 x from by decide +kernel) x ((member_iff 12 x).mpr hx'))
    · intro x hx
      exact (member_iff 16 x).mp
        ((show ∀ x : Source, member 10 x → member 16 x from by decide +kernel) x ((member_iff 10 x).mpr hx))
  · change Subgroup.closure (Set.range BinaryNormal8T11.N16.normalGenerators)≤_
    apply (Subgroup.closure_le _).mpr
    rintro _ ⟨j,rfl⟩
    have he : ∀ j, kernelPart j*normalPart j=BinaryNormal8T11.N16.normalGenerators j := by decide +kernel
    rw [← he j]
    apply Subgroup.mul_mem
    · apply (show top.ker≤top.ker⊔BinaryNormal8T11.N10.kernel from le_sup_left)
      rw [kernel_eq]
      exact (member_iff 12 _).mp ((show ∀ j, member 12 (kernelPart j) from by decide +kernel) j)
    · apply (show BinaryNormal8T11.N10.kernel≤top.ker⊔BinaryNormal8T11.N10.kernel from le_sup_right)
      exact (member_iff 10 _).mp ((show ∀ j, member 10 (normalPart j) from by decide +kernel) j)

private def cover0 : Equiv.Perm (Fin 0) where
  toFun := Fin.elim0
  invFun := Fin.elim0
  left_inv := fun x => Fin.elim0 x
  right_inv := fun x => Fin.elim0 x

private def coverValues (i : Fin 16) : Equiv.Perm (Fin 0) := (if i.val < 8 then (if i.val < 4 then (if i.val < 2 then (if i.val < 1 then cover0 else cover0) else (if i.val < 3 then cover0 else cover0)) else (if i.val < 6 then (if i.val < 5 then cover0 else cover0) else (if i.val < 7 then cover0 else cover0))) else (if i.val < 12 then (if i.val < 10 then (if i.val < 9 then cover0 else cover0) else (if i.val < 11 then cover0 else cover0)) else (if i.val < 14 then (if i.val < 13 then cover0 else cover0) else (if i.val < 15 then cover0 else cover0))))
private def coverImages (j : Fin 3) : Equiv.Perm (Fin 0) := (if j.val < 1 then cover0 else (if j.val < 2 then cover0 else cover0))
private theorem cover_step : ∀ i j,
    coverValues (BinaryMenuCayley8T11.certificate.next i j)=coverValues i*coverImages j := (by decide +kernel)
private theorem cover_identity : coverValues BinaryMenuCayley8T11.certificate.identity=1 := by decide +kernel

def cover : Source →* Equiv.Perm (Fin 0) where
  toFun x := coverValues x.index
  map_one' := cover_identity
  map_mul' x y := by
    change coverValues (BinaryMenuCayley8T11.certificate.walk x.index
      (BinaryMenuCayley8T11.certificate.words y.index))=coverValues x.index*coverValues y.index
    rw [EncodedCayleyCertificate.values_walk _ coverValues coverImages cover_step,
      ← EncodedCayleyCertificate.values_word _ coverValues coverImages cover_step cover_identity]

theorem cover_kernel : cover.ker=top.ker⊔BinaryNormal8T11.N10.kernel := by
  rw [join_eq]
  ext x
  change cover x=1 ↔ x∈(BinaryNormal8T11.states 16).kernel
  rw [← member_iff]
  exact (show ∀ x : Source, cover x=1 ↔ member 16 x from by decide +kernel) x

/-- Every local numerical dimension follows from checked original subgroup
orders and maps; the selected original cut and full fixed preimage remain. -/
def certificate : BinaryPairLocalCertificate generators top BinaryNormal8T11.N10.kernel where
  cut := BinaryNormal8T11.N12.kernel
  cut_normal := inferInstance
  cut_le_kernel := cut_le
  intersection_le_cut := intersection_le
  central := cut_central
  cutDimension := 1
  fixedDimension := 0
  cut_card := by simp only [intersection_eq,BinaryNormal8T11.N12.kernel_card,BinaryNormal8T11.N1.kernel_card] <;> decide
  fixed_card := by simp only [fixed_eq,BinaryNormal8T11.N12.kernel_card,BinaryNormal8T11.N12.kernel_card] <;> decide
  coverDegree := 0
  cover := cover
  cover_kernel := cover_kernel
  width := 8
  gap := by decide

end N10

namespace N11

theorem intersection_eq : top.ker⊓BinaryNormal8T11.N11.kernel=BinaryNormal8T11.N1.kernel := by
  rw [kernel_eq]
  ext x
  change (x∈(BinaryNormal8T11.states 12).kernel ∧ x∈(BinaryNormal8T11.states 11).kernel) ↔ x∈(BinaryNormal8T11.states 1).kernel
  simp only [← member_iff]
  exact (show ∀ x : Source, (member 12 x ∧ member 11 x) ↔ member 1 x from by decide +kernel) x

theorem cut_le : BinaryNormal8T11.N12.kernel≤top.ker := by
  intro x hx
  have hk : x∈BinaryNormal8T11.N12.kernel := (member_iff 12 x).mp
    ((show ∀ x : Source, member 12 x → member 12 x from by decide +kernel) x ((member_iff 12 x).mpr hx))
  exact kernel_eq.symm ▸ hk

theorem intersection_le : top.ker⊓BinaryNormal8T11.N11.kernel≤BinaryNormal8T11.N12.kernel := by
  intro x hx
  have hx' : x∈BinaryNormal8T11.N1.kernel := intersection_eq ▸ hx
  apply (member_iff 12 x).mp
  exact (show ∀ x : Source, member 1 x → member 12 x from by decide +kernel) x ((member_iff 1 x).mpr hx')

theorem cut_central : ∀ j, ∀ x : BinaryNormal8T11.N12.kernel,
    (x:Source)⁻¹*(generators j*(x:Source)*(generators j)⁻¹)∈BinaryNormal8T11.N11.kernel := by
  have h : ∀ j, ∀ x : Source, member 12 x →
      member 11 (x⁻¹*(generators j*x*(generators j)⁻¹)) := by decide +kernel
  intro j x
  exact (member_iff 11 _).mp (h j x.val ((member_iff 12 x.val).mpr x.property))

theorem fixed_eq : binaryPairFixedSubgroup top.ker BinaryNormal8T11.N12.kernel=BinaryNormal8T11.N12.kernel := by
  rw [kernel_eq]
  ext x
  rw [binaryPairFixedSubgroup_mem_iff _ _ generators BinaryNormal8T11.generators_full]
  change (x∈(BinaryNormal8T11.states 12).kernel ∧ ∀ j,
    x⁻¹*(generators j*x*(generators j)⁻¹)∈(BinaryNormal8T11.states 12).kernel) ↔ x∈(BinaryNormal8T11.states 12).kernel
  simp only [← member_iff]
  exact (show ∀ x : Source, (member 12 x ∧ ∀ j,
    member 12 (x⁻¹*(generators j*x*(generators j)⁻¹))) ↔ member 12 x from by decide +kernel) x

/-- These are the actual selected cut lift generators from this record. -/
def recordedCutGenerators (j : Fin 2) : Source := ⟨((if j.val < 1 then 7 else 6) : Fin 16)⟩
private def cutWords (j : Fin 2) : List (Fin 2) := (if j.val < 1 then ([0] : List (Fin 2)) else ([0, 1] : List (Fin 2)))
private theorem cutWords_checked : ∀ j,
    ((cutWords j).map recordedCutGenerators).prod=BinaryNormal8T11.N12.normalGenerators j := by decide +kernel

theorem recorded_cut_eq : Subgroup.closure (Set.range recordedCutGenerators)=BinaryNormal8T11.N12.kernel := by
  apply le_antisymm
  · apply (Subgroup.closure_le _).mpr
    rintro _ ⟨j,rfl⟩
    exact (member_iff 12 _).mp
      ((show ∀ j, member 12 (recordedCutGenerators j) from by decide +kernel) j)
  · exact (BinaryNormalGeneratorWords.closure_le
      ({words := cutWords, equations := cutWords_checked} :
        BinaryNormalGeneratorWords BinaryNormal8T11.N12.normalGenerators recordedCutGenerators))

private def kernelPart (j : Fin 3) : Source := ⟨((if j.val < 1 then 6 else (if j.val < 2 then 6 else 7)) : Fin 16)⟩
private def normalPart (j : Fin 3) : Source := ⟨((if j.val < 1 then 11 else (if j.val < 2 then 9 else 6)) : Fin 16)⟩

theorem join_eq : top.ker⊔BinaryNormal8T11.N11.kernel=BinaryNormal8T11.N16.kernel := by
  apply le_antisymm
  · apply sup_le
    · intro x hx
      have hx' : x∈BinaryNormal8T11.N12.kernel := kernel_eq ▸ hx
      exact (member_iff 16 x).mp
        ((show ∀ x : Source, member 12 x → member 16 x from by decide +kernel) x ((member_iff 12 x).mpr hx'))
    · intro x hx
      exact (member_iff 16 x).mp
        ((show ∀ x : Source, member 11 x → member 16 x from by decide +kernel) x ((member_iff 11 x).mpr hx))
  · change Subgroup.closure (Set.range BinaryNormal8T11.N16.normalGenerators)≤_
    apply (Subgroup.closure_le _).mpr
    rintro _ ⟨j,rfl⟩
    have he : ∀ j, kernelPart j*normalPart j=BinaryNormal8T11.N16.normalGenerators j := by decide +kernel
    rw [← he j]
    apply Subgroup.mul_mem
    · apply (show top.ker≤top.ker⊔BinaryNormal8T11.N11.kernel from le_sup_left)
      rw [kernel_eq]
      exact (member_iff 12 _).mp ((show ∀ j, member 12 (kernelPart j) from by decide +kernel) j)
    · apply (show BinaryNormal8T11.N11.kernel≤top.ker⊔BinaryNormal8T11.N11.kernel from le_sup_right)
      exact (member_iff 11 _).mp ((show ∀ j, member 11 (normalPart j) from by decide +kernel) j)

private def cover0 : Equiv.Perm (Fin 0) where
  toFun := Fin.elim0
  invFun := Fin.elim0
  left_inv := fun x => Fin.elim0 x
  right_inv := fun x => Fin.elim0 x

private def coverValues (i : Fin 16) : Equiv.Perm (Fin 0) := (if i.val < 8 then (if i.val < 4 then (if i.val < 2 then (if i.val < 1 then cover0 else cover0) else (if i.val < 3 then cover0 else cover0)) else (if i.val < 6 then (if i.val < 5 then cover0 else cover0) else (if i.val < 7 then cover0 else cover0))) else (if i.val < 12 then (if i.val < 10 then (if i.val < 9 then cover0 else cover0) else (if i.val < 11 then cover0 else cover0)) else (if i.val < 14 then (if i.val < 13 then cover0 else cover0) else (if i.val < 15 then cover0 else cover0))))
private def coverImages (j : Fin 3) : Equiv.Perm (Fin 0) := (if j.val < 1 then cover0 else (if j.val < 2 then cover0 else cover0))
private theorem cover_step : ∀ i j,
    coverValues (BinaryMenuCayley8T11.certificate.next i j)=coverValues i*coverImages j := (by decide +kernel)
private theorem cover_identity : coverValues BinaryMenuCayley8T11.certificate.identity=1 := by decide +kernel

def cover : Source →* Equiv.Perm (Fin 0) where
  toFun x := coverValues x.index
  map_one' := cover_identity
  map_mul' x y := by
    change coverValues (BinaryMenuCayley8T11.certificate.walk x.index
      (BinaryMenuCayley8T11.certificate.words y.index))=coverValues x.index*coverValues y.index
    rw [EncodedCayleyCertificate.values_walk _ coverValues coverImages cover_step,
      ← EncodedCayleyCertificate.values_word _ coverValues coverImages cover_step cover_identity]

theorem cover_kernel : cover.ker=top.ker⊔BinaryNormal8T11.N11.kernel := by
  rw [join_eq]
  ext x
  change cover x=1 ↔ x∈(BinaryNormal8T11.states 16).kernel
  rw [← member_iff]
  exact (show ∀ x : Source, cover x=1 ↔ member 16 x from by decide +kernel) x

/-- Every local numerical dimension follows from checked original subgroup
orders and maps; the selected original cut and full fixed preimage remain. -/
def certificate : BinaryPairLocalCertificate generators top BinaryNormal8T11.N11.kernel where
  cut := BinaryNormal8T11.N12.kernel
  cut_normal := inferInstance
  cut_le_kernel := cut_le
  intersection_le_cut := intersection_le
  central := cut_central
  cutDimension := 1
  fixedDimension := 0
  cut_card := by simp only [intersection_eq,BinaryNormal8T11.N12.kernel_card,BinaryNormal8T11.N1.kernel_card] <;> decide
  fixed_card := by simp only [fixed_eq,BinaryNormal8T11.N12.kernel_card,BinaryNormal8T11.N12.kernel_card] <;> decide
  coverDegree := 0
  cover := cover
  cover_kernel := cover_kernel
  width := 8
  gap := by decide

end N11

namespace N12

theorem intersection_eq : top.ker⊓BinaryNormal8T11.N12.kernel=BinaryNormal8T11.N12.kernel := by
  rw [kernel_eq]
  ext x
  change (x∈(BinaryNormal8T11.states 12).kernel ∧ x∈(BinaryNormal8T11.states 12).kernel) ↔ x∈(BinaryNormal8T11.states 12).kernel
  simp only [← member_iff]
  exact (show ∀ x : Source, (member 12 x ∧ member 12 x) ↔ member 12 x from by decide +kernel) x

theorem cut_le : BinaryNormal8T11.N12.kernel≤top.ker := by
  intro x hx
  have hk : x∈BinaryNormal8T11.N12.kernel := (member_iff 12 x).mp
    ((show ∀ x : Source, member 12 x → member 12 x from by decide +kernel) x ((member_iff 12 x).mpr hx))
  exact kernel_eq.symm ▸ hk

theorem intersection_le : top.ker⊓BinaryNormal8T11.N12.kernel≤BinaryNormal8T11.N12.kernel := by
  intro x hx
  have hx' : x∈BinaryNormal8T11.N12.kernel := intersection_eq ▸ hx
  apply (member_iff 12 x).mp
  exact (show ∀ x : Source, member 12 x → member 12 x from by decide +kernel) x ((member_iff 12 x).mpr hx')

theorem cut_central : ∀ j, ∀ x : BinaryNormal8T11.N12.kernel,
    (x:Source)⁻¹*(generators j*(x:Source)*(generators j)⁻¹)∈BinaryNormal8T11.N12.kernel := by
  have h : ∀ j, ∀ x : Source, member 12 x →
      member 12 (x⁻¹*(generators j*x*(generators j)⁻¹)) := by decide +kernel
  intro j x
  exact (member_iff 12 _).mp (h j x.val ((member_iff 12 x.val).mpr x.property))

theorem fixed_eq : binaryPairFixedSubgroup top.ker BinaryNormal8T11.N12.kernel=BinaryNormal8T11.N12.kernel := by
  rw [kernel_eq]
  ext x
  rw [binaryPairFixedSubgroup_mem_iff _ _ generators BinaryNormal8T11.generators_full]
  change (x∈(BinaryNormal8T11.states 12).kernel ∧ ∀ j,
    x⁻¹*(generators j*x*(generators j)⁻¹)∈(BinaryNormal8T11.states 12).kernel) ↔ x∈(BinaryNormal8T11.states 12).kernel
  simp only [← member_iff]
  exact (show ∀ x : Source, (member 12 x ∧ ∀ j,
    member 12 (x⁻¹*(generators j*x*(generators j)⁻¹))) ↔ member 12 x from by decide +kernel) x

/-- These are the actual selected cut lift generators from this record. -/
def recordedCutGenerators (j : Fin 2) : Source := ⟨((if j.val < 1 then 7 else 14) : Fin 16)⟩
private def cutWords (j : Fin 2) : List (Fin 2) := (if j.val < 1 then ([0] : List (Fin 2)) else ([1] : List (Fin 2)))
private theorem cutWords_checked : ∀ j,
    ((cutWords j).map recordedCutGenerators).prod=BinaryNormal8T11.N12.normalGenerators j := by decide +kernel

theorem recorded_cut_eq : Subgroup.closure (Set.range recordedCutGenerators)=BinaryNormal8T11.N12.kernel := by
  apply le_antisymm
  · apply (Subgroup.closure_le _).mpr
    rintro _ ⟨j,rfl⟩
    exact (member_iff 12 _).mp
      ((show ∀ j, member 12 (recordedCutGenerators j) from by decide +kernel) j)
  · exact (BinaryNormalGeneratorWords.closure_le
      ({words := cutWords, equations := cutWords_checked} :
        BinaryNormalGeneratorWords BinaryNormal8T11.N12.normalGenerators recordedCutGenerators))

private def kernelPart (j : Fin 2) : Source := ⟨((if j.val < 1 then 6 else 6) : Fin 16)⟩
private def normalPart (j : Fin 2) : Source := ⟨((if j.val < 1 then 14 else 7) : Fin 16)⟩

theorem join_eq : top.ker⊔BinaryNormal8T11.N12.kernel=BinaryNormal8T11.N12.kernel := by
  apply le_antisymm
  · apply sup_le
    · intro x hx
      have hx' : x∈BinaryNormal8T11.N12.kernel := kernel_eq ▸ hx
      exact (member_iff 12 x).mp
        ((show ∀ x : Source, member 12 x → member 12 x from by decide +kernel) x ((member_iff 12 x).mpr hx'))
    · intro x hx
      exact (member_iff 12 x).mp
        ((show ∀ x : Source, member 12 x → member 12 x from by decide +kernel) x ((member_iff 12 x).mpr hx))
  · change Subgroup.closure (Set.range BinaryNormal8T11.N12.normalGenerators)≤_
    apply (Subgroup.closure_le _).mpr
    rintro _ ⟨j,rfl⟩
    have he : ∀ j, kernelPart j*normalPart j=BinaryNormal8T11.N12.normalGenerators j := by decide +kernel
    rw [← he j]
    apply Subgroup.mul_mem
    · apply (show top.ker≤top.ker⊔BinaryNormal8T11.N12.kernel from le_sup_left)
      rw [kernel_eq]
      exact (member_iff 12 _).mp ((show ∀ j, member 12 (kernelPart j) from by decide +kernel) j)
    · apply (show BinaryNormal8T11.N12.kernel≤top.ker⊔BinaryNormal8T11.N12.kernel from le_sup_right)
      exact (member_iff 12 _).mp ((show ∀ j, member 12 (normalPart j) from by decide +kernel) j)

private def cover0 : Equiv.Perm (Fin 4) where
  toFun x := (#[1,0,3,2] : Array (Fin 4))[x.val]!
  invFun x := (#[1,0,3,2] : Array (Fin 4))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel
private def cover1 : Equiv.Perm (Fin 4) where
  toFun x := (#[0,1,3,2] : Array (Fin 4))[x.val]!
  invFun x := (#[0,1,3,2] : Array (Fin 4))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel
private def cover2 : Equiv.Perm (Fin 4) where
  toFun x := (#[1,0,2,3] : Array (Fin 4))[x.val]!
  invFun x := (#[1,0,2,3] : Array (Fin 4))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel
private def cover3 : Equiv.Perm (Fin 4) where
  toFun x := (#[0,1,2,3] : Array (Fin 4))[x.val]!
  invFun x := (#[0,1,2,3] : Array (Fin 4))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

private def coverValues (i : Fin 16) : Equiv.Perm (Fin 4) := (if i.val < 8 then (if i.val < 4 then (if i.val < 2 then (if i.val < 1 then cover1 else cover1) else (if i.val < 3 then cover2 else cover2)) else (if i.val < 6 then (if i.val < 5 then cover0 else cover0) else (if i.val < 7 then cover3 else cover3))) else (if i.val < 12 then (if i.val < 10 then (if i.val < 9 then cover1 else cover1) else (if i.val < 11 then cover2 else cover2)) else (if i.val < 14 then (if i.val < 13 then cover0 else cover0) else (if i.val < 15 then cover3 else cover3))))
private def coverImages (j : Fin 3) : Equiv.Perm (Fin 4) := (if j.val < 1 then cover3 else (if j.val < 2 then cover2 else cover1))
private theorem cover_step : ∀ i j,
    coverValues (BinaryMenuCayley8T11.certificate.next i j)=coverValues i*coverImages j := (by decide +kernel)
private theorem cover_identity : coverValues BinaryMenuCayley8T11.certificate.identity=1 := by decide +kernel

def cover : Source →* Equiv.Perm (Fin 4) where
  toFun x := coverValues x.index
  map_one' := cover_identity
  map_mul' x y := by
    change coverValues (BinaryMenuCayley8T11.certificate.walk x.index
      (BinaryMenuCayley8T11.certificate.words y.index))=coverValues x.index*coverValues y.index
    rw [EncodedCayleyCertificate.values_walk _ coverValues coverImages cover_step,
      ← EncodedCayleyCertificate.values_word _ coverValues coverImages cover_step cover_identity]

theorem cover_kernel : cover.ker=top.ker⊔BinaryNormal8T11.N12.kernel := by
  rw [join_eq]
  ext x
  change cover x=1 ↔ x∈(BinaryNormal8T11.states 12).kernel
  rw [← member_iff]
  exact (show ∀ x : Source, cover x=1 ↔ member 12 x from by decide +kernel) x

/-- Every local numerical dimension follows from checked original subgroup
orders and maps; the selected original cut and full fixed preimage remain. -/
def certificate : BinaryPairLocalCertificate generators top BinaryNormal8T11.N12.kernel where
  cut := BinaryNormal8T11.N12.kernel
  cut_normal := inferInstance
  cut_le_kernel := cut_le
  intersection_le_cut := intersection_le
  central := cut_central
  cutDimension := 0
  fixedDimension := 0
  cut_card := by simp only [intersection_eq,BinaryNormal8T11.N12.kernel_card,BinaryNormal8T11.N12.kernel_card] <;> decide
  fixed_card := by simp only [fixed_eq,BinaryNormal8T11.N12.kernel_card,BinaryNormal8T11.N12.kernel_card] <;> decide
  coverDegree := 4
  cover := cover
  cover_kernel := cover_kernel
  width := 8
  gap := by decide

end N12

namespace N13

theorem intersection_eq : top.ker⊓BinaryNormal8T11.N13.kernel=BinaryNormal8T11.N12.kernel := by
  rw [kernel_eq]
  ext x
  change (x∈(BinaryNormal8T11.states 12).kernel ∧ x∈(BinaryNormal8T11.states 13).kernel) ↔ x∈(BinaryNormal8T11.states 12).kernel
  simp only [← member_iff]
  exact (show ∀ x : Source, (member 12 x ∧ member 13 x) ↔ member 12 x from by decide +kernel) x

theorem cut_le : BinaryNormal8T11.N12.kernel≤top.ker := by
  intro x hx
  have hk : x∈BinaryNormal8T11.N12.kernel := (member_iff 12 x).mp
    ((show ∀ x : Source, member 12 x → member 12 x from by decide +kernel) x ((member_iff 12 x).mpr hx))
  exact kernel_eq.symm ▸ hk

theorem intersection_le : top.ker⊓BinaryNormal8T11.N13.kernel≤BinaryNormal8T11.N12.kernel := by
  intro x hx
  have hx' : x∈BinaryNormal8T11.N12.kernel := intersection_eq ▸ hx
  apply (member_iff 12 x).mp
  exact (show ∀ x : Source, member 12 x → member 12 x from by decide +kernel) x ((member_iff 12 x).mpr hx')

theorem cut_central : ∀ j, ∀ x : BinaryNormal8T11.N12.kernel,
    (x:Source)⁻¹*(generators j*(x:Source)*(generators j)⁻¹)∈BinaryNormal8T11.N13.kernel := by
  have h : ∀ j, ∀ x : Source, member 12 x →
      member 13 (x⁻¹*(generators j*x*(generators j)⁻¹)) := by decide +kernel
  intro j x
  exact (member_iff 13 _).mp (h j x.val ((member_iff 12 x.val).mpr x.property))

theorem fixed_eq : binaryPairFixedSubgroup top.ker BinaryNormal8T11.N12.kernel=BinaryNormal8T11.N12.kernel := by
  rw [kernel_eq]
  ext x
  rw [binaryPairFixedSubgroup_mem_iff _ _ generators BinaryNormal8T11.generators_full]
  change (x∈(BinaryNormal8T11.states 12).kernel ∧ ∀ j,
    x⁻¹*(generators j*x*(generators j)⁻¹)∈(BinaryNormal8T11.states 12).kernel) ↔ x∈(BinaryNormal8T11.states 12).kernel
  simp only [← member_iff]
  exact (show ∀ x : Source, (member 12 x ∧ ∀ j,
    member 12 (x⁻¹*(generators j*x*(generators j)⁻¹))) ↔ member 12 x from by decide +kernel) x

/-- These are the actual selected cut lift generators from this record. -/
def recordedCutGenerators (j : Fin 2) : Source := ⟨((if j.val < 1 then 7 else 14) : Fin 16)⟩
private def cutWords (j : Fin 2) : List (Fin 2) := (if j.val < 1 then ([0] : List (Fin 2)) else ([1] : List (Fin 2)))
private theorem cutWords_checked : ∀ j,
    ((cutWords j).map recordedCutGenerators).prod=BinaryNormal8T11.N12.normalGenerators j := by decide +kernel

theorem recorded_cut_eq : Subgroup.closure (Set.range recordedCutGenerators)=BinaryNormal8T11.N12.kernel := by
  apply le_antisymm
  · apply (Subgroup.closure_le _).mpr
    rintro _ ⟨j,rfl⟩
    exact (member_iff 12 _).mp
      ((show ∀ j, member 12 (recordedCutGenerators j) from by decide +kernel) j)
  · exact (BinaryNormalGeneratorWords.closure_le
      ({words := cutWords, equations := cutWords_checked} :
        BinaryNormalGeneratorWords BinaryNormal8T11.N12.normalGenerators recordedCutGenerators))

private def kernelPart (j : Fin 3) : Source := ⟨((if j.val < 1 then 6 else (if j.val < 2 then 6 else 6)) : Fin 16)⟩
private def normalPart (j : Fin 3) : Source := ⟨((if j.val < 1 then 14 else (if j.val < 2 then 7 else 13)) : Fin 16)⟩

theorem join_eq : top.ker⊔BinaryNormal8T11.N13.kernel=BinaryNormal8T11.N13.kernel := by
  apply le_antisymm
  · apply sup_le
    · intro x hx
      have hx' : x∈BinaryNormal8T11.N12.kernel := kernel_eq ▸ hx
      exact (member_iff 13 x).mp
        ((show ∀ x : Source, member 12 x → member 13 x from by decide +kernel) x ((member_iff 12 x).mpr hx'))
    · intro x hx
      exact (member_iff 13 x).mp
        ((show ∀ x : Source, member 13 x → member 13 x from by decide +kernel) x ((member_iff 13 x).mpr hx))
  · change Subgroup.closure (Set.range BinaryNormal8T11.N13.normalGenerators)≤_
    apply (Subgroup.closure_le _).mpr
    rintro _ ⟨j,rfl⟩
    have he : ∀ j, kernelPart j*normalPart j=BinaryNormal8T11.N13.normalGenerators j := by decide +kernel
    rw [← he j]
    apply Subgroup.mul_mem
    · apply (show top.ker≤top.ker⊔BinaryNormal8T11.N13.kernel from le_sup_left)
      rw [kernel_eq]
      exact (member_iff 12 _).mp ((show ∀ j, member 12 (kernelPart j) from by decide +kernel) j)
    · apply (show BinaryNormal8T11.N13.kernel≤top.ker⊔BinaryNormal8T11.N13.kernel from le_sup_right)
      exact (member_iff 13 _).mp ((show ∀ j, member 13 (normalPart j) from by decide +kernel) j)

private def cover0 : Equiv.Perm (Fin 2) where
  toFun x := (#[1,0] : Array (Fin 2))[x.val]!
  invFun x := (#[1,0] : Array (Fin 2))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel
private def cover1 : Equiv.Perm (Fin 2) where
  toFun x := (#[0,1] : Array (Fin 2))[x.val]!
  invFun x := (#[0,1] : Array (Fin 2))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

private def coverValues (i : Fin 16) : Equiv.Perm (Fin 2) := (if i.val < 8 then (if i.val < 4 then (if i.val < 2 then (if i.val < 1 then cover0 else cover0) else (if i.val < 3 then cover0 else cover0)) else (if i.val < 6 then (if i.val < 5 then cover1 else cover1) else (if i.val < 7 then cover1 else cover1))) else (if i.val < 12 then (if i.val < 10 then (if i.val < 9 then cover0 else cover0) else (if i.val < 11 then cover0 else cover0)) else (if i.val < 14 then (if i.val < 13 then cover1 else cover1) else (if i.val < 15 then cover1 else cover1))))
private def coverImages (j : Fin 3) : Equiv.Perm (Fin 2) := (if j.val < 1 then cover1 else (if j.val < 2 then cover0 else cover0))
private theorem cover_step : ∀ i j,
    coverValues (BinaryMenuCayley8T11.certificate.next i j)=coverValues i*coverImages j := (by decide +kernel)
private theorem cover_identity : coverValues BinaryMenuCayley8T11.certificate.identity=1 := by decide +kernel

def cover : Source →* Equiv.Perm (Fin 2) where
  toFun x := coverValues x.index
  map_one' := cover_identity
  map_mul' x y := by
    change coverValues (BinaryMenuCayley8T11.certificate.walk x.index
      (BinaryMenuCayley8T11.certificate.words y.index))=coverValues x.index*coverValues y.index
    rw [EncodedCayleyCertificate.values_walk _ coverValues coverImages cover_step,
      ← EncodedCayleyCertificate.values_word _ coverValues coverImages cover_step cover_identity]

theorem cover_kernel : cover.ker=top.ker⊔BinaryNormal8T11.N13.kernel := by
  rw [join_eq]
  ext x
  change cover x=1 ↔ x∈(BinaryNormal8T11.states 13).kernel
  rw [← member_iff]
  exact (show ∀ x : Source, cover x=1 ↔ member 13 x from by decide +kernel) x

/-- Every local numerical dimension follows from checked original subgroup
orders and maps; the selected original cut and full fixed preimage remain. -/
def certificate : BinaryPairLocalCertificate generators top BinaryNormal8T11.N13.kernel where
  cut := BinaryNormal8T11.N12.kernel
  cut_normal := inferInstance
  cut_le_kernel := cut_le
  intersection_le_cut := intersection_le
  central := cut_central
  cutDimension := 0
  fixedDimension := 0
  cut_card := by simp only [intersection_eq,BinaryNormal8T11.N12.kernel_card,BinaryNormal8T11.N12.kernel_card] <;> decide
  fixed_card := by simp only [fixed_eq,BinaryNormal8T11.N12.kernel_card,BinaryNormal8T11.N12.kernel_card] <;> decide
  coverDegree := 2
  cover := cover
  cover_kernel := cover_kernel
  width := 8
  gap := by decide

end N13

namespace N14

theorem intersection_eq : top.ker⊓BinaryNormal8T11.N14.kernel=BinaryNormal8T11.N12.kernel := by
  rw [kernel_eq]
  ext x
  change (x∈(BinaryNormal8T11.states 12).kernel ∧ x∈(BinaryNormal8T11.states 14).kernel) ↔ x∈(BinaryNormal8T11.states 12).kernel
  simp only [← member_iff]
  exact (show ∀ x : Source, (member 12 x ∧ member 14 x) ↔ member 12 x from by decide +kernel) x

theorem cut_le : BinaryNormal8T11.N12.kernel≤top.ker := by
  intro x hx
  have hk : x∈BinaryNormal8T11.N12.kernel := (member_iff 12 x).mp
    ((show ∀ x : Source, member 12 x → member 12 x from by decide +kernel) x ((member_iff 12 x).mpr hx))
  exact kernel_eq.symm ▸ hk

theorem intersection_le : top.ker⊓BinaryNormal8T11.N14.kernel≤BinaryNormal8T11.N12.kernel := by
  intro x hx
  have hx' : x∈BinaryNormal8T11.N12.kernel := intersection_eq ▸ hx
  apply (member_iff 12 x).mp
  exact (show ∀ x : Source, member 12 x → member 12 x from by decide +kernel) x ((member_iff 12 x).mpr hx')

theorem cut_central : ∀ j, ∀ x : BinaryNormal8T11.N12.kernel,
    (x:Source)⁻¹*(generators j*(x:Source)*(generators j)⁻¹)∈BinaryNormal8T11.N14.kernel := by
  have h : ∀ j, ∀ x : Source, member 12 x →
      member 14 (x⁻¹*(generators j*x*(generators j)⁻¹)) := by decide +kernel
  intro j x
  exact (member_iff 14 _).mp (h j x.val ((member_iff 12 x.val).mpr x.property))

theorem fixed_eq : binaryPairFixedSubgroup top.ker BinaryNormal8T11.N12.kernel=BinaryNormal8T11.N12.kernel := by
  rw [kernel_eq]
  ext x
  rw [binaryPairFixedSubgroup_mem_iff _ _ generators BinaryNormal8T11.generators_full]
  change (x∈(BinaryNormal8T11.states 12).kernel ∧ ∀ j,
    x⁻¹*(generators j*x*(generators j)⁻¹)∈(BinaryNormal8T11.states 12).kernel) ↔ x∈(BinaryNormal8T11.states 12).kernel
  simp only [← member_iff]
  exact (show ∀ x : Source, (member 12 x ∧ ∀ j,
    member 12 (x⁻¹*(generators j*x*(generators j)⁻¹))) ↔ member 12 x from by decide +kernel) x

/-- These are the actual selected cut lift generators from this record. -/
def recordedCutGenerators (j : Fin 2) : Source := ⟨((if j.val < 1 then 7 else 14) : Fin 16)⟩
private def cutWords (j : Fin 2) : List (Fin 2) := (if j.val < 1 then ([0] : List (Fin 2)) else ([1] : List (Fin 2)))
private theorem cutWords_checked : ∀ j,
    ((cutWords j).map recordedCutGenerators).prod=BinaryNormal8T11.N12.normalGenerators j := by decide +kernel

theorem recorded_cut_eq : Subgroup.closure (Set.range recordedCutGenerators)=BinaryNormal8T11.N12.kernel := by
  apply le_antisymm
  · apply (Subgroup.closure_le _).mpr
    rintro _ ⟨j,rfl⟩
    exact (member_iff 12 _).mp
      ((show ∀ j, member 12 (recordedCutGenerators j) from by decide +kernel) j)
  · exact (BinaryNormalGeneratorWords.closure_le
      ({words := cutWords, equations := cutWords_checked} :
        BinaryNormalGeneratorWords BinaryNormal8T11.N12.normalGenerators recordedCutGenerators))

private def kernelPart (j : Fin 3) : Source := ⟨((if j.val < 1 then 6 else (if j.val < 2 then 6 else 6)) : Fin 16)⟩
private def normalPart (j : Fin 3) : Source := ⟨((if j.val < 1 then 9 else (if j.val < 2 then 14 else 7)) : Fin 16)⟩

theorem join_eq : top.ker⊔BinaryNormal8T11.N14.kernel=BinaryNormal8T11.N14.kernel := by
  apply le_antisymm
  · apply sup_le
    · intro x hx
      have hx' : x∈BinaryNormal8T11.N12.kernel := kernel_eq ▸ hx
      exact (member_iff 14 x).mp
        ((show ∀ x : Source, member 12 x → member 14 x from by decide +kernel) x ((member_iff 12 x).mpr hx'))
    · intro x hx
      exact (member_iff 14 x).mp
        ((show ∀ x : Source, member 14 x → member 14 x from by decide +kernel) x ((member_iff 14 x).mpr hx))
  · change Subgroup.closure (Set.range BinaryNormal8T11.N14.normalGenerators)≤_
    apply (Subgroup.closure_le _).mpr
    rintro _ ⟨j,rfl⟩
    have he : ∀ j, kernelPart j*normalPart j=BinaryNormal8T11.N14.normalGenerators j := by decide +kernel
    rw [← he j]
    apply Subgroup.mul_mem
    · apply (show top.ker≤top.ker⊔BinaryNormal8T11.N14.kernel from le_sup_left)
      rw [kernel_eq]
      exact (member_iff 12 _).mp ((show ∀ j, member 12 (kernelPart j) from by decide +kernel) j)
    · apply (show BinaryNormal8T11.N14.kernel≤top.ker⊔BinaryNormal8T11.N14.kernel from le_sup_right)
      exact (member_iff 14 _).mp ((show ∀ j, member 14 (normalPart j) from by decide +kernel) j)

private def cover0 : Equiv.Perm (Fin 2) where
  toFun x := (#[1,0] : Array (Fin 2))[x.val]!
  invFun x := (#[1,0] : Array (Fin 2))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel
private def cover1 : Equiv.Perm (Fin 2) where
  toFun x := (#[0,1] : Array (Fin 2))[x.val]!
  invFun x := (#[0,1] : Array (Fin 2))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

private def coverValues (i : Fin 16) : Equiv.Perm (Fin 2) := (if i.val < 8 then (if i.val < 4 then (if i.val < 2 then (if i.val < 1 then cover1 else cover1) else (if i.val < 3 then cover0 else cover0)) else (if i.val < 6 then (if i.val < 5 then cover0 else cover0) else (if i.val < 7 then cover1 else cover1))) else (if i.val < 12 then (if i.val < 10 then (if i.val < 9 then cover1 else cover1) else (if i.val < 11 then cover0 else cover0)) else (if i.val < 14 then (if i.val < 13 then cover0 else cover0) else (if i.val < 15 then cover1 else cover1))))
private def coverImages (j : Fin 3) : Equiv.Perm (Fin 2) := (if j.val < 1 then cover1 else (if j.val < 2 then cover0 else cover1))
private theorem cover_step : ∀ i j,
    coverValues (BinaryMenuCayley8T11.certificate.next i j)=coverValues i*coverImages j := (by decide +kernel)
private theorem cover_identity : coverValues BinaryMenuCayley8T11.certificate.identity=1 := by decide +kernel

def cover : Source →* Equiv.Perm (Fin 2) where
  toFun x := coverValues x.index
  map_one' := cover_identity
  map_mul' x y := by
    change coverValues (BinaryMenuCayley8T11.certificate.walk x.index
      (BinaryMenuCayley8T11.certificate.words y.index))=coverValues x.index*coverValues y.index
    rw [EncodedCayleyCertificate.values_walk _ coverValues coverImages cover_step,
      ← EncodedCayleyCertificate.values_word _ coverValues coverImages cover_step cover_identity]

theorem cover_kernel : cover.ker=top.ker⊔BinaryNormal8T11.N14.kernel := by
  rw [join_eq]
  ext x
  change cover x=1 ↔ x∈(BinaryNormal8T11.states 14).kernel
  rw [← member_iff]
  exact (show ∀ x : Source, cover x=1 ↔ member 14 x from by decide +kernel) x

/-- Every local numerical dimension follows from checked original subgroup
orders and maps; the selected original cut and full fixed preimage remain. -/
def certificate : BinaryPairLocalCertificate generators top BinaryNormal8T11.N14.kernel where
  cut := BinaryNormal8T11.N12.kernel
  cut_normal := inferInstance
  cut_le_kernel := cut_le
  intersection_le_cut := intersection_le
  central := cut_central
  cutDimension := 0
  fixedDimension := 0
  cut_card := by simp only [intersection_eq,BinaryNormal8T11.N12.kernel_card,BinaryNormal8T11.N12.kernel_card] <;> decide
  fixed_card := by simp only [fixed_eq,BinaryNormal8T11.N12.kernel_card,BinaryNormal8T11.N12.kernel_card] <;> decide
  coverDegree := 2
  cover := cover
  cover_kernel := cover_kernel
  width := 8
  gap := by decide

end N14

namespace N15

theorem intersection_eq : top.ker⊓BinaryNormal8T11.N15.kernel=BinaryNormal8T11.N12.kernel := by
  rw [kernel_eq]
  ext x
  change (x∈(BinaryNormal8T11.states 12).kernel ∧ x∈(BinaryNormal8T11.states 15).kernel) ↔ x∈(BinaryNormal8T11.states 12).kernel
  simp only [← member_iff]
  exact (show ∀ x : Source, (member 12 x ∧ member 15 x) ↔ member 12 x from by decide +kernel) x

theorem cut_le : BinaryNormal8T11.N12.kernel≤top.ker := by
  intro x hx
  have hk : x∈BinaryNormal8T11.N12.kernel := (member_iff 12 x).mp
    ((show ∀ x : Source, member 12 x → member 12 x from by decide +kernel) x ((member_iff 12 x).mpr hx))
  exact kernel_eq.symm ▸ hk

theorem intersection_le : top.ker⊓BinaryNormal8T11.N15.kernel≤BinaryNormal8T11.N12.kernel := by
  intro x hx
  have hx' : x∈BinaryNormal8T11.N12.kernel := intersection_eq ▸ hx
  apply (member_iff 12 x).mp
  exact (show ∀ x : Source, member 12 x → member 12 x from by decide +kernel) x ((member_iff 12 x).mpr hx')

theorem cut_central : ∀ j, ∀ x : BinaryNormal8T11.N12.kernel,
    (x:Source)⁻¹*(generators j*(x:Source)*(generators j)⁻¹)∈BinaryNormal8T11.N15.kernel := by
  have h : ∀ j, ∀ x : Source, member 12 x →
      member 15 (x⁻¹*(generators j*x*(generators j)⁻¹)) := by decide +kernel
  intro j x
  exact (member_iff 15 _).mp (h j x.val ((member_iff 12 x.val).mpr x.property))

theorem fixed_eq : binaryPairFixedSubgroup top.ker BinaryNormal8T11.N12.kernel=BinaryNormal8T11.N12.kernel := by
  rw [kernel_eq]
  ext x
  rw [binaryPairFixedSubgroup_mem_iff _ _ generators BinaryNormal8T11.generators_full]
  change (x∈(BinaryNormal8T11.states 12).kernel ∧ ∀ j,
    x⁻¹*(generators j*x*(generators j)⁻¹)∈(BinaryNormal8T11.states 12).kernel) ↔ x∈(BinaryNormal8T11.states 12).kernel
  simp only [← member_iff]
  exact (show ∀ x : Source, (member 12 x ∧ ∀ j,
    member 12 (x⁻¹*(generators j*x*(generators j)⁻¹))) ↔ member 12 x from by decide +kernel) x

/-- These are the actual selected cut lift generators from this record. -/
def recordedCutGenerators (j : Fin 2) : Source := ⟨((if j.val < 1 then 7 else 14) : Fin 16)⟩
private def cutWords (j : Fin 2) : List (Fin 2) := (if j.val < 1 then ([0] : List (Fin 2)) else ([1] : List (Fin 2)))
private theorem cutWords_checked : ∀ j,
    ((cutWords j).map recordedCutGenerators).prod=BinaryNormal8T11.N12.normalGenerators j := by decide +kernel

theorem recorded_cut_eq : Subgroup.closure (Set.range recordedCutGenerators)=BinaryNormal8T11.N12.kernel := by
  apply le_antisymm
  · apply (Subgroup.closure_le _).mpr
    rintro _ ⟨j,rfl⟩
    exact (member_iff 12 _).mp
      ((show ∀ j, member 12 (recordedCutGenerators j) from by decide +kernel) j)
  · exact (BinaryNormalGeneratorWords.closure_le
      ({words := cutWords, equations := cutWords_checked} :
        BinaryNormalGeneratorWords BinaryNormal8T11.N12.normalGenerators recordedCutGenerators))

private def kernelPart (j : Fin 3) : Source := ⟨((if j.val < 1 then 6 else (if j.val < 2 then 6 else 6)) : Fin 16)⟩
private def normalPart (j : Fin 3) : Source := ⟨((if j.val < 1 then 11 else (if j.val < 2 then 14 else 7)) : Fin 16)⟩

theorem join_eq : top.ker⊔BinaryNormal8T11.N15.kernel=BinaryNormal8T11.N15.kernel := by
  apply le_antisymm
  · apply sup_le
    · intro x hx
      have hx' : x∈BinaryNormal8T11.N12.kernel := kernel_eq ▸ hx
      exact (member_iff 15 x).mp
        ((show ∀ x : Source, member 12 x → member 15 x from by decide +kernel) x ((member_iff 12 x).mpr hx'))
    · intro x hx
      exact (member_iff 15 x).mp
        ((show ∀ x : Source, member 15 x → member 15 x from by decide +kernel) x ((member_iff 15 x).mpr hx))
  · change Subgroup.closure (Set.range BinaryNormal8T11.N15.normalGenerators)≤_
    apply (Subgroup.closure_le _).mpr
    rintro _ ⟨j,rfl⟩
    have he : ∀ j, kernelPart j*normalPart j=BinaryNormal8T11.N15.normalGenerators j := by decide +kernel
    rw [← he j]
    apply Subgroup.mul_mem
    · apply (show top.ker≤top.ker⊔BinaryNormal8T11.N15.kernel from le_sup_left)
      rw [kernel_eq]
      exact (member_iff 12 _).mp ((show ∀ j, member 12 (kernelPart j) from by decide +kernel) j)
    · apply (show BinaryNormal8T11.N15.kernel≤top.ker⊔BinaryNormal8T11.N15.kernel from le_sup_right)
      exact (member_iff 15 _).mp ((show ∀ j, member 15 (normalPart j) from by decide +kernel) j)

private def cover0 : Equiv.Perm (Fin 2) where
  toFun x := (#[1,0] : Array (Fin 2))[x.val]!
  invFun x := (#[1,0] : Array (Fin 2))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel
private def cover1 : Equiv.Perm (Fin 2) where
  toFun x := (#[0,1] : Array (Fin 2))[x.val]!
  invFun x := (#[0,1] : Array (Fin 2))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

private def coverValues (i : Fin 16) : Equiv.Perm (Fin 2) := (if i.val < 8 then (if i.val < 4 then (if i.val < 2 then (if i.val < 1 then cover0 else cover0) else (if i.val < 3 then cover1 else cover1)) else (if i.val < 6 then (if i.val < 5 then cover0 else cover0) else (if i.val < 7 then cover1 else cover1))) else (if i.val < 12 then (if i.val < 10 then (if i.val < 9 then cover0 else cover0) else (if i.val < 11 then cover1 else cover1)) else (if i.val < 14 then (if i.val < 13 then cover0 else cover0) else (if i.val < 15 then cover1 else cover1))))
private def coverImages (j : Fin 3) : Equiv.Perm (Fin 2) := (if j.val < 1 then cover1 else (if j.val < 2 then cover1 else cover0))
private theorem cover_step : ∀ i j,
    coverValues (BinaryMenuCayley8T11.certificate.next i j)=coverValues i*coverImages j := (by decide +kernel)
private theorem cover_identity : coverValues BinaryMenuCayley8T11.certificate.identity=1 := by decide +kernel

def cover : Source →* Equiv.Perm (Fin 2) where
  toFun x := coverValues x.index
  map_one' := cover_identity
  map_mul' x y := by
    change coverValues (BinaryMenuCayley8T11.certificate.walk x.index
      (BinaryMenuCayley8T11.certificate.words y.index))=coverValues x.index*coverValues y.index
    rw [EncodedCayleyCertificate.values_walk _ coverValues coverImages cover_step,
      ← EncodedCayleyCertificate.values_word _ coverValues coverImages cover_step cover_identity]

theorem cover_kernel : cover.ker=top.ker⊔BinaryNormal8T11.N15.kernel := by
  rw [join_eq]
  ext x
  change cover x=1 ↔ x∈(BinaryNormal8T11.states 15).kernel
  rw [← member_iff]
  exact (show ∀ x : Source, cover x=1 ↔ member 15 x from by decide +kernel) x

/-- Every local numerical dimension follows from checked original subgroup
orders and maps; the selected original cut and full fixed preimage remain. -/
def certificate : BinaryPairLocalCertificate generators top BinaryNormal8T11.N15.kernel where
  cut := BinaryNormal8T11.N12.kernel
  cut_normal := inferInstance
  cut_le_kernel := cut_le
  intersection_le_cut := intersection_le
  central := cut_central
  cutDimension := 0
  fixedDimension := 0
  cut_card := by simp only [intersection_eq,BinaryNormal8T11.N12.kernel_card,BinaryNormal8T11.N12.kernel_card] <;> decide
  fixed_card := by simp only [fixed_eq,BinaryNormal8T11.N12.kernel_card,BinaryNormal8T11.N12.kernel_card] <;> decide
  coverDegree := 2
  cover := cover
  cover_kernel := cover_kernel
  width := 8
  gap := by decide

end N15

namespace N16

theorem intersection_eq : top.ker⊓BinaryNormal8T11.N16.kernel=BinaryNormal8T11.N12.kernel := by
  rw [kernel_eq]
  ext x
  change (x∈(BinaryNormal8T11.states 12).kernel ∧ x∈(BinaryNormal8T11.states 16).kernel) ↔ x∈(BinaryNormal8T11.states 12).kernel
  simp only [← member_iff]
  exact (show ∀ x : Source, (member 12 x ∧ member 16 x) ↔ member 12 x from by decide +kernel) x

theorem cut_le : BinaryNormal8T11.N12.kernel≤top.ker := by
  intro x hx
  have hk : x∈BinaryNormal8T11.N12.kernel := (member_iff 12 x).mp
    ((show ∀ x : Source, member 12 x → member 12 x from by decide +kernel) x ((member_iff 12 x).mpr hx))
  exact kernel_eq.symm ▸ hk

theorem intersection_le : top.ker⊓BinaryNormal8T11.N16.kernel≤BinaryNormal8T11.N12.kernel := by
  intro x hx
  have hx' : x∈BinaryNormal8T11.N12.kernel := intersection_eq ▸ hx
  apply (member_iff 12 x).mp
  exact (show ∀ x : Source, member 12 x → member 12 x from by decide +kernel) x ((member_iff 12 x).mpr hx')

theorem cut_central : ∀ j, ∀ x : BinaryNormal8T11.N12.kernel,
    (x:Source)⁻¹*(generators j*(x:Source)*(generators j)⁻¹)∈BinaryNormal8T11.N16.kernel := by
  have h : ∀ j, ∀ x : Source, member 12 x →
      member 16 (x⁻¹*(generators j*x*(generators j)⁻¹)) := by decide +kernel
  intro j x
  exact (member_iff 16 _).mp (h j x.val ((member_iff 12 x.val).mpr x.property))

theorem fixed_eq : binaryPairFixedSubgroup top.ker BinaryNormal8T11.N12.kernel=BinaryNormal8T11.N12.kernel := by
  rw [kernel_eq]
  ext x
  rw [binaryPairFixedSubgroup_mem_iff _ _ generators BinaryNormal8T11.generators_full]
  change (x∈(BinaryNormal8T11.states 12).kernel ∧ ∀ j,
    x⁻¹*(generators j*x*(generators j)⁻¹)∈(BinaryNormal8T11.states 12).kernel) ↔ x∈(BinaryNormal8T11.states 12).kernel
  simp only [← member_iff]
  exact (show ∀ x : Source, (member 12 x ∧ ∀ j,
    member 12 (x⁻¹*(generators j*x*(generators j)⁻¹))) ↔ member 12 x from by decide +kernel) x

/-- These are the actual selected cut lift generators from this record. -/
def recordedCutGenerators (j : Fin 2) : Source := ⟨((if j.val < 1 then 7 else 14) : Fin 16)⟩
private def cutWords (j : Fin 2) : List (Fin 2) := (if j.val < 1 then ([0] : List (Fin 2)) else ([1] : List (Fin 2)))
private theorem cutWords_checked : ∀ j,
    ((cutWords j).map recordedCutGenerators).prod=BinaryNormal8T11.N12.normalGenerators j := by decide +kernel

theorem recorded_cut_eq : Subgroup.closure (Set.range recordedCutGenerators)=BinaryNormal8T11.N12.kernel := by
  apply le_antisymm
  · apply (Subgroup.closure_le _).mpr
    rintro _ ⟨j,rfl⟩
    exact (member_iff 12 _).mp
      ((show ∀ j, member 12 (recordedCutGenerators j) from by decide +kernel) j)
  · exact (BinaryNormalGeneratorWords.closure_le
      ({words := cutWords, equations := cutWords_checked} :
        BinaryNormalGeneratorWords BinaryNormal8T11.N12.normalGenerators recordedCutGenerators))

private def kernelPart (j : Fin 3) : Source := ⟨((if j.val < 1 then 6 else (if j.val < 2 then 6 else 6)) : Fin 16)⟩
private def normalPart (j : Fin 3) : Source := ⟨((if j.val < 1 then 11 else (if j.val < 2 then 9 else 7)) : Fin 16)⟩

theorem join_eq : top.ker⊔BinaryNormal8T11.N16.kernel=BinaryNormal8T11.N16.kernel := by
  apply le_antisymm
  · apply sup_le
    · intro x hx
      have hx' : x∈BinaryNormal8T11.N12.kernel := kernel_eq ▸ hx
      exact (member_iff 16 x).mp
        ((show ∀ x : Source, member 12 x → member 16 x from by decide +kernel) x ((member_iff 12 x).mpr hx'))
    · intro x hx
      exact (member_iff 16 x).mp
        ((show ∀ x : Source, member 16 x → member 16 x from by decide +kernel) x ((member_iff 16 x).mpr hx))
  · change Subgroup.closure (Set.range BinaryNormal8T11.N16.normalGenerators)≤_
    apply (Subgroup.closure_le _).mpr
    rintro _ ⟨j,rfl⟩
    have he : ∀ j, kernelPart j*normalPart j=BinaryNormal8T11.N16.normalGenerators j := by decide +kernel
    rw [← he j]
    apply Subgroup.mul_mem
    · apply (show top.ker≤top.ker⊔BinaryNormal8T11.N16.kernel from le_sup_left)
      rw [kernel_eq]
      exact (member_iff 12 _).mp ((show ∀ j, member 12 (kernelPart j) from by decide +kernel) j)
    · apply (show BinaryNormal8T11.N16.kernel≤top.ker⊔BinaryNormal8T11.N16.kernel from le_sup_right)
      exact (member_iff 16 _).mp ((show ∀ j, member 16 (normalPart j) from by decide +kernel) j)

private def cover0 : Equiv.Perm (Fin 0) where
  toFun := Fin.elim0
  invFun := Fin.elim0
  left_inv := fun x => Fin.elim0 x
  right_inv := fun x => Fin.elim0 x

private def coverValues (i : Fin 16) : Equiv.Perm (Fin 0) := (if i.val < 8 then (if i.val < 4 then (if i.val < 2 then (if i.val < 1 then cover0 else cover0) else (if i.val < 3 then cover0 else cover0)) else (if i.val < 6 then (if i.val < 5 then cover0 else cover0) else (if i.val < 7 then cover0 else cover0))) else (if i.val < 12 then (if i.val < 10 then (if i.val < 9 then cover0 else cover0) else (if i.val < 11 then cover0 else cover0)) else (if i.val < 14 then (if i.val < 13 then cover0 else cover0) else (if i.val < 15 then cover0 else cover0))))
private def coverImages (j : Fin 3) : Equiv.Perm (Fin 0) := (if j.val < 1 then cover0 else (if j.val < 2 then cover0 else cover0))
private theorem cover_step : ∀ i j,
    coverValues (BinaryMenuCayley8T11.certificate.next i j)=coverValues i*coverImages j := (by decide +kernel)
private theorem cover_identity : coverValues BinaryMenuCayley8T11.certificate.identity=1 := by decide +kernel

def cover : Source →* Equiv.Perm (Fin 0) where
  toFun x := coverValues x.index
  map_one' := cover_identity
  map_mul' x y := by
    change coverValues (BinaryMenuCayley8T11.certificate.walk x.index
      (BinaryMenuCayley8T11.certificate.words y.index))=coverValues x.index*coverValues y.index
    rw [EncodedCayleyCertificate.values_walk _ coverValues coverImages cover_step,
      ← EncodedCayleyCertificate.values_word _ coverValues coverImages cover_step cover_identity]

theorem cover_kernel : cover.ker=top.ker⊔BinaryNormal8T11.N16.kernel := by
  rw [join_eq]
  ext x
  change cover x=1 ↔ x∈(BinaryNormal8T11.states 16).kernel
  rw [← member_iff]
  exact (show ∀ x : Source, cover x=1 ↔ member 16 x from by decide +kernel) x

/-- Every local numerical dimension follows from checked original subgroup
orders and maps; the selected original cut and full fixed preimage remain. -/
def certificate : BinaryPairLocalCertificate generators top BinaryNormal8T11.N16.kernel where
  cut := BinaryNormal8T11.N12.kernel
  cut_normal := inferInstance
  cut_le_kernel := cut_le
  intersection_le_cut := intersection_le
  central := cut_central
  cutDimension := 0
  fixedDimension := 0
  cut_card := by simp only [intersection_eq,BinaryNormal8T11.N12.kernel_card,BinaryNormal8T11.N12.kernel_card] <;> decide
  fixed_card := by simp only [fixed_eq,BinaryNormal8T11.N12.kernel_card,BinaryNormal8T11.N12.kernel_card] <;> decide
  coverDegree := 0
  cover := cover
  cover_kernel := cover_kernel
  width := 8
  gap := by decide

end N16

end SymmetricSubgroupAsymptotics.BinaryPairLocal8T11
