import SymmetricSubgroupAsymptotics.BinaryPairFiniteRows
import SymmetricSubgroupAsymptotics.GeneratedNormal8.Registry8T8
import SymmetricSubgroupAsymptotics.GeneratedPair8.Frames8T8

/-! All pair-type normal states of 8T8: original cuts, complete fixed
preimages, quotient covers and exact local gaps. All finite equations use
the Lean kernel. Character and transport records are separate branches. -/
set_option autoImplicit false
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option linter.unusedVariables false
set_option linter.unnecessarySeqFocus false
noncomputable section
namespace SymmetricSubgroupAsymptotics.BinaryPairLocal8T8
abbrev Source := FiniteGroupRow 16
local instance : Group Source := BinaryMenuCayley8T8.group
abbrev generators := BinaryNormal8T8.generators
abbrev top := BinaryPair8T8.Frame0.topHom
private def mask (i : Fin 7) : ℕ := (if i.val < 3 then (if i.val < 1 then 32768 else (if i.val < 2 then 32896 else 34948)) else (if i.val < 5 then (if i.val < 4 then 39333 else 52428) else (if i.val < 6 then 43670 else 65535)))
private abbrev member (i : Fin 7) (x : Source) : Prop := mask i / 2^x.index.val % 2=1

private theorem member_iff (i : Fin 7) (x : Source) :
    member i x ↔ x∈(BinaryNormal8T8.states i).kernel := by
  fin_cases i
  · change member 0 x ↔ x∈Subgroup.closure (Set.range BinaryNormal8T8.N0.normalGenerators)
    rw [binaryNormalRow_mem_iff BinaryNormal8T8.N0.normalCertificate]
    have h : ∀ z : Fin 16, member 0 ⟨z⟩ ↔ ∃ j : Fin 1, BinaryNormal8T8.N0.normalCertificate.rows j=z := (by decide +kernel)
    exact h x.index
  · change member 1 x ↔ x∈Subgroup.closure (Set.range BinaryNormal8T8.N1.normalGenerators)
    rw [binaryNormalRow_mem_iff BinaryNormal8T8.N1.normalCertificate]
    have h : ∀ z : Fin 16, member 1 ⟨z⟩ ↔ ∃ j : Fin 2, BinaryNormal8T8.N1.normalCertificate.rows j=z := (by decide +kernel)
    exact h x.index
  · change member 2 x ↔ x∈Subgroup.closure (Set.range BinaryNormal8T8.N2.normalGenerators)
    rw [binaryNormalRow_mem_iff BinaryNormal8T8.N2.normalCertificate]
    have h : ∀ z : Fin 16, member 2 ⟨z⟩ ↔ ∃ j : Fin 4, BinaryNormal8T8.N2.normalCertificate.rows j=z := (by decide +kernel)
    exact h x.index
  · change member 3 x ↔ x∈Subgroup.closure (Set.range BinaryNormal8T8.N3.normalGenerators)
    rw [binaryNormalRow_mem_iff BinaryNormal8T8.N3.normalCertificate]
    have h : ∀ z : Fin 16, member 3 ⟨z⟩ ↔ ∃ j : Fin 8, BinaryNormal8T8.N3.normalCertificate.rows j=z := (by decide +kernel)
    exact h x.index
  · change member 4 x ↔ x∈Subgroup.closure (Set.range BinaryNormal8T8.N4.normalGenerators)
    rw [binaryNormalRow_mem_iff BinaryNormal8T8.N4.normalCertificate]
    have h : ∀ z : Fin 16, member 4 ⟨z⟩ ↔ ∃ j : Fin 8, BinaryNormal8T8.N4.normalCertificate.rows j=z := (by decide +kernel)
    exact h x.index
  · change member 5 x ↔ x∈Subgroup.closure (Set.range BinaryNormal8T8.N5.normalGenerators)
    rw [binaryNormalRow_mem_iff BinaryNormal8T8.N5.normalCertificate]
    have h : ∀ z : Fin 16, member 5 ⟨z⟩ ↔ ∃ j : Fin 8, BinaryNormal8T8.N5.normalCertificate.rows j=z := (by decide +kernel)
    exact h x.index
  · change member 6 x ↔ x∈Subgroup.closure (Set.range BinaryNormal8T8.N6.normalGenerators)
    rw [binaryNormalRow_mem_iff BinaryNormal8T8.N6.normalCertificate]
    have h : ∀ z : Fin 16, member 6 ⟨z⟩ ↔ ∃ j : Fin 16, BinaryNormal8T8.N6.normalCertificate.rows j=z := (by decide +kernel)
    exact h x.index

theorem kernel_eq : top.ker=BinaryNormal8T8.N1.kernel := by
  ext x
  change top x=1 ↔ x∈(BinaryNormal8T8.states 1).kernel
  rw [← member_iff]
  exact (show ∀ x : Source, top x=1 ↔ member 1 x from by decide +kernel) x

namespace N0

theorem intersection_eq : top.ker⊓BinaryNormal8T8.N0.kernel=BinaryNormal8T8.N0.kernel := by
  rw [kernel_eq]
  ext x
  change (x∈(BinaryNormal8T8.states 1).kernel ∧ x∈(BinaryNormal8T8.states 0).kernel) ↔ x∈(BinaryNormal8T8.states 0).kernel
  simp only [← member_iff]
  exact (show ∀ x : Source, (member 1 x ∧ member 0 x) ↔ member 0 x from by decide +kernel) x

theorem cut_le : BinaryNormal8T8.N1.kernel≤top.ker := by
  intro x hx
  have hk : x∈BinaryNormal8T8.N1.kernel := (member_iff 1 x).mp
    ((show ∀ x : Source, member 1 x → member 1 x from by decide +kernel) x ((member_iff 1 x).mpr hx))
  exact kernel_eq.symm ▸ hk

theorem intersection_le : top.ker⊓BinaryNormal8T8.N0.kernel≤BinaryNormal8T8.N1.kernel := by
  intro x hx
  have hx' : x∈BinaryNormal8T8.N0.kernel := intersection_eq ▸ hx
  apply (member_iff 1 x).mp
  exact (show ∀ x : Source, member 0 x → member 1 x from by decide +kernel) x ((member_iff 0 x).mpr hx')

theorem cut_central : ∀ j, ∀ x : BinaryNormal8T8.N1.kernel,
    (x:Source)⁻¹*(generators j*(x:Source)*(generators j)⁻¹)∈BinaryNormal8T8.N0.kernel := by
  have h : ∀ j, ∀ x : Source, member 1 x →
      member 0 (x⁻¹*(generators j*x*(generators j)⁻¹)) := by decide +kernel
  intro j x
  exact (member_iff 0 _).mp (h j x.val ((member_iff 1 x.val).mpr x.property))

theorem fixed_eq : binaryPairFixedSubgroup top.ker BinaryNormal8T8.N1.kernel=BinaryNormal8T8.N1.kernel := by
  rw [kernel_eq]
  ext x
  rw [binaryPairFixedSubgroup_mem_iff _ _ generators BinaryNormal8T8.generators_full]
  change (x∈(BinaryNormal8T8.states 1).kernel ∧ ∀ j,
    x⁻¹*(generators j*x*(generators j)⁻¹)∈(BinaryNormal8T8.states 1).kernel) ↔ x∈(BinaryNormal8T8.states 1).kernel
  simp only [← member_iff]
  exact (show ∀ x : Source, (member 1 x ∧ ∀ j,
    member 1 (x⁻¹*(generators j*x*(generators j)⁻¹))) ↔ member 1 x from by decide +kernel) x

/-- These are the actual selected cut lift generators from this record. -/
def recordedCutGenerators (j : Fin 1) : Source := ⟨(7 : Fin 16)⟩
private def cutWords (j : Fin 1) : List (Fin 1) := ([0] : List (Fin 1))
private theorem cutWords_checked : ∀ j,
    ((cutWords j).map recordedCutGenerators).prod=BinaryNormal8T8.N1.normalGenerators j := by decide +kernel

theorem recorded_cut_eq : Subgroup.closure (Set.range recordedCutGenerators)=BinaryNormal8T8.N1.kernel := by
  apply le_antisymm
  · apply (Subgroup.closure_le _).mpr
    rintro _ ⟨j,rfl⟩
    exact (member_iff 1 _).mp
      ((show ∀ j, member 1 (recordedCutGenerators j) from by decide +kernel) j)
  · exact (BinaryNormalGeneratorWords.closure_le
      ({words := cutWords, equations := cutWords_checked} :
        BinaryNormalGeneratorWords BinaryNormal8T8.N1.normalGenerators recordedCutGenerators))

private def kernelPart (j : Fin 1) : Source := ⟨(7 : Fin 16)⟩
private def normalPart (j : Fin 1) : Source := ⟨(15 : Fin 16)⟩

theorem join_eq : top.ker⊔BinaryNormal8T8.N0.kernel=BinaryNormal8T8.N1.kernel := by
  apply le_antisymm
  · apply sup_le
    · intro x hx
      have hx' : x∈BinaryNormal8T8.N1.kernel := kernel_eq ▸ hx
      exact (member_iff 1 x).mp
        ((show ∀ x : Source, member 1 x → member 1 x from by decide +kernel) x ((member_iff 1 x).mpr hx'))
    · intro x hx
      exact (member_iff 1 x).mp
        ((show ∀ x : Source, member 0 x → member 1 x from by decide +kernel) x ((member_iff 0 x).mpr hx))
  · change Subgroup.closure (Set.range BinaryNormal8T8.N1.normalGenerators)≤_
    apply (Subgroup.closure_le _).mpr
    rintro _ ⟨j,rfl⟩
    have he : ∀ j, kernelPart j*normalPart j=BinaryNormal8T8.N1.normalGenerators j := by decide +kernel
    rw [← he j]
    apply Subgroup.mul_mem
    · apply (show top.ker≤top.ker⊔BinaryNormal8T8.N0.kernel from le_sup_left)
      rw [kernel_eq]
      exact (member_iff 1 _).mp ((show ∀ j, member 1 (kernelPart j) from by decide +kernel) j)
    · apply (show BinaryNormal8T8.N0.kernel≤top.ker⊔BinaryNormal8T8.N0.kernel from le_sup_right)
      exact (member_iff 0 _).mp ((show ∀ j, member 0 (normalPart j) from by decide +kernel) j)

private def cover0 : Equiv.Perm (Fin 4) where
  toFun x := (#[3,2,1,0] : Array (Fin 4))[x.val]!
  invFun x := (#[3,2,1,0] : Array (Fin 4))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel
private def cover1 : Equiv.Perm (Fin 4) where
  toFun x := (#[2,3,1,0] : Array (Fin 4))[x.val]!
  invFun x := (#[3,2,0,1] : Array (Fin 4))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel
private def cover2 : Equiv.Perm (Fin 4) where
  toFun x := (#[3,2,0,1] : Array (Fin 4))[x.val]!
  invFun x := (#[2,3,1,0] : Array (Fin 4))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel
private def cover3 : Equiv.Perm (Fin 4) where
  toFun x := (#[2,3,0,1] : Array (Fin 4))[x.val]!
  invFun x := (#[2,3,0,1] : Array (Fin 4))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel
private def cover4 : Equiv.Perm (Fin 4) where
  toFun x := (#[1,0,3,2] : Array (Fin 4))[x.val]!
  invFun x := (#[1,0,3,2] : Array (Fin 4))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel
private def cover5 : Equiv.Perm (Fin 4) where
  toFun x := (#[0,1,3,2] : Array (Fin 4))[x.val]!
  invFun x := (#[0,1,3,2] : Array (Fin 4))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel
private def cover6 : Equiv.Perm (Fin 4) where
  toFun x := (#[1,0,2,3] : Array (Fin 4))[x.val]!
  invFun x := (#[1,0,2,3] : Array (Fin 4))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel
private def cover7 : Equiv.Perm (Fin 4) where
  toFun x := (#[0,1,2,3] : Array (Fin 4))[x.val]!
  invFun x := (#[0,1,2,3] : Array (Fin 4))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

private def coverValues (i : Fin 16) : Equiv.Perm (Fin 4) := (if i.val < 8 then (if i.val < 4 then (if i.val < 2 then (if i.val < 1 then cover3 else cover2) else (if i.val < 3 then cover4 else cover5)) else (if i.val < 6 then (if i.val < 5 then cover1 else cover0) else (if i.val < 7 then cover6 else cover7))) else (if i.val < 12 then (if i.val < 10 then (if i.val < 9 then cover3 else cover2) else (if i.val < 11 then cover5 else cover4)) else (if i.val < 14 then (if i.val < 13 then cover0 else cover1) else (if i.val < 15 then cover6 else cover7))))
private def coverImages (j : Fin 2) : Equiv.Perm (Fin 4) := (if j.val < 1 then cover2 else cover6)
private theorem cover_step : ∀ i j,
    coverValues (BinaryMenuCayley8T8.certificate.next i j)=coverValues i*coverImages j := (by decide +kernel)
private theorem cover_identity : coverValues BinaryMenuCayley8T8.certificate.identity=1 := by decide +kernel

def cover : Source →* Equiv.Perm (Fin 4) where
  toFun x := coverValues x.index
  map_one' := cover_identity
  map_mul' x y := by
    change coverValues (BinaryMenuCayley8T8.certificate.walk x.index
      (BinaryMenuCayley8T8.certificate.words y.index))=coverValues x.index*coverValues y.index
    rw [EncodedCayleyCertificate.values_walk _ coverValues coverImages cover_step,
      ← EncodedCayleyCertificate.values_word _ coverValues coverImages cover_step cover_identity]

theorem cover_kernel : cover.ker=top.ker⊔BinaryNormal8T8.N0.kernel := by
  rw [join_eq]
  ext x
  change cover x=1 ↔ x∈(BinaryNormal8T8.states 1).kernel
  rw [← member_iff]
  exact (show ∀ x : Source, cover x=1 ↔ member 1 x from by decide +kernel) x

/-- Every local numerical dimension follows from checked original subgroup
orders and maps; the selected original cut and full fixed preimage remain. -/
def certificate : BinaryPairLocalCertificate generators top BinaryNormal8T8.N0.kernel where
  cut := BinaryNormal8T8.N1.kernel
  cut_normal := inferInstance
  cut_le_kernel := cut_le
  intersection_le_cut := intersection_le
  central := cut_central
  cutDimension := 1
  fixedDimension := 0
  cut_card := by simp only [intersection_eq,BinaryNormal8T8.N1.kernel_card,BinaryNormal8T8.N0.kernel_card] <;> decide
  fixed_card := by simp only [fixed_eq,BinaryNormal8T8.N1.kernel_card,BinaryNormal8T8.N1.kernel_card] <;> decide
  coverDegree := 4
  cover := cover
  cover_kernel := cover_kernel
  width := 8
  gap := by decide

end N0

namespace N1

theorem intersection_eq : top.ker⊓BinaryNormal8T8.N1.kernel=BinaryNormal8T8.N1.kernel := by
  rw [kernel_eq]
  ext x
  change (x∈(BinaryNormal8T8.states 1).kernel ∧ x∈(BinaryNormal8T8.states 1).kernel) ↔ x∈(BinaryNormal8T8.states 1).kernel
  simp only [← member_iff]
  exact (show ∀ x : Source, (member 1 x ∧ member 1 x) ↔ member 1 x from by decide +kernel) x

theorem cut_le : BinaryNormal8T8.N1.kernel≤top.ker := by
  intro x hx
  have hk : x∈BinaryNormal8T8.N1.kernel := (member_iff 1 x).mp
    ((show ∀ x : Source, member 1 x → member 1 x from by decide +kernel) x ((member_iff 1 x).mpr hx))
  exact kernel_eq.symm ▸ hk

theorem intersection_le : top.ker⊓BinaryNormal8T8.N1.kernel≤BinaryNormal8T8.N1.kernel := by
  intro x hx
  have hx' : x∈BinaryNormal8T8.N1.kernel := intersection_eq ▸ hx
  apply (member_iff 1 x).mp
  exact (show ∀ x : Source, member 1 x → member 1 x from by decide +kernel) x ((member_iff 1 x).mpr hx')

theorem cut_central : ∀ j, ∀ x : BinaryNormal8T8.N1.kernel,
    (x:Source)⁻¹*(generators j*(x:Source)*(generators j)⁻¹)∈BinaryNormal8T8.N1.kernel := by
  have h : ∀ j, ∀ x : Source, member 1 x →
      member 1 (x⁻¹*(generators j*x*(generators j)⁻¹)) := by decide +kernel
  intro j x
  exact (member_iff 1 _).mp (h j x.val ((member_iff 1 x.val).mpr x.property))

theorem fixed_eq : binaryPairFixedSubgroup top.ker BinaryNormal8T8.N1.kernel=BinaryNormal8T8.N1.kernel := by
  rw [kernel_eq]
  ext x
  rw [binaryPairFixedSubgroup_mem_iff _ _ generators BinaryNormal8T8.generators_full]
  change (x∈(BinaryNormal8T8.states 1).kernel ∧ ∀ j,
    x⁻¹*(generators j*x*(generators j)⁻¹)∈(BinaryNormal8T8.states 1).kernel) ↔ x∈(BinaryNormal8T8.states 1).kernel
  simp only [← member_iff]
  exact (show ∀ x : Source, (member 1 x ∧ ∀ j,
    member 1 (x⁻¹*(generators j*x*(generators j)⁻¹))) ↔ member 1 x from by decide +kernel) x

/-- These are the actual selected cut lift generators from this record. -/
def recordedCutGenerators (j : Fin 1) : Source := ⟨(7 : Fin 16)⟩
private def cutWords (j : Fin 1) : List (Fin 1) := ([0] : List (Fin 1))
private theorem cutWords_checked : ∀ j,
    ((cutWords j).map recordedCutGenerators).prod=BinaryNormal8T8.N1.normalGenerators j := by decide +kernel

theorem recorded_cut_eq : Subgroup.closure (Set.range recordedCutGenerators)=BinaryNormal8T8.N1.kernel := by
  apply le_antisymm
  · apply (Subgroup.closure_le _).mpr
    rintro _ ⟨j,rfl⟩
    exact (member_iff 1 _).mp
      ((show ∀ j, member 1 (recordedCutGenerators j) from by decide +kernel) j)
  · exact (BinaryNormalGeneratorWords.closure_le
      ({words := cutWords, equations := cutWords_checked} :
        BinaryNormalGeneratorWords BinaryNormal8T8.N1.normalGenerators recordedCutGenerators))

private def kernelPart (j : Fin 1) : Source := ⟨(7 : Fin 16)⟩
private def normalPart (j : Fin 1) : Source := ⟨(15 : Fin 16)⟩

theorem join_eq : top.ker⊔BinaryNormal8T8.N1.kernel=BinaryNormal8T8.N1.kernel := by
  apply le_antisymm
  · apply sup_le
    · intro x hx
      have hx' : x∈BinaryNormal8T8.N1.kernel := kernel_eq ▸ hx
      exact (member_iff 1 x).mp
        ((show ∀ x : Source, member 1 x → member 1 x from by decide +kernel) x ((member_iff 1 x).mpr hx'))
    · intro x hx
      exact (member_iff 1 x).mp
        ((show ∀ x : Source, member 1 x → member 1 x from by decide +kernel) x ((member_iff 1 x).mpr hx))
  · change Subgroup.closure (Set.range BinaryNormal8T8.N1.normalGenerators)≤_
    apply (Subgroup.closure_le _).mpr
    rintro _ ⟨j,rfl⟩
    have he : ∀ j, kernelPart j*normalPart j=BinaryNormal8T8.N1.normalGenerators j := by decide +kernel
    rw [← he j]
    apply Subgroup.mul_mem
    · apply (show top.ker≤top.ker⊔BinaryNormal8T8.N1.kernel from le_sup_left)
      rw [kernel_eq]
      exact (member_iff 1 _).mp ((show ∀ j, member 1 (kernelPart j) from by decide +kernel) j)
    · apply (show BinaryNormal8T8.N1.kernel≤top.ker⊔BinaryNormal8T8.N1.kernel from le_sup_right)
      exact (member_iff 1 _).mp ((show ∀ j, member 1 (normalPart j) from by decide +kernel) j)

private def cover0 : Equiv.Perm (Fin 4) where
  toFun x := (#[3,2,1,0] : Array (Fin 4))[x.val]!
  invFun x := (#[3,2,1,0] : Array (Fin 4))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel
private def cover1 : Equiv.Perm (Fin 4) where
  toFun x := (#[2,3,1,0] : Array (Fin 4))[x.val]!
  invFun x := (#[3,2,0,1] : Array (Fin 4))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel
private def cover2 : Equiv.Perm (Fin 4) where
  toFun x := (#[3,2,0,1] : Array (Fin 4))[x.val]!
  invFun x := (#[2,3,1,0] : Array (Fin 4))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel
private def cover3 : Equiv.Perm (Fin 4) where
  toFun x := (#[2,3,0,1] : Array (Fin 4))[x.val]!
  invFun x := (#[2,3,0,1] : Array (Fin 4))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel
private def cover4 : Equiv.Perm (Fin 4) where
  toFun x := (#[1,0,3,2] : Array (Fin 4))[x.val]!
  invFun x := (#[1,0,3,2] : Array (Fin 4))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel
private def cover5 : Equiv.Perm (Fin 4) where
  toFun x := (#[0,1,3,2] : Array (Fin 4))[x.val]!
  invFun x := (#[0,1,3,2] : Array (Fin 4))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel
private def cover6 : Equiv.Perm (Fin 4) where
  toFun x := (#[1,0,2,3] : Array (Fin 4))[x.val]!
  invFun x := (#[1,0,2,3] : Array (Fin 4))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel
private def cover7 : Equiv.Perm (Fin 4) where
  toFun x := (#[0,1,2,3] : Array (Fin 4))[x.val]!
  invFun x := (#[0,1,2,3] : Array (Fin 4))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

private def coverValues (i : Fin 16) : Equiv.Perm (Fin 4) := (if i.val < 8 then (if i.val < 4 then (if i.val < 2 then (if i.val < 1 then cover3 else cover2) else (if i.val < 3 then cover4 else cover5)) else (if i.val < 6 then (if i.val < 5 then cover1 else cover0) else (if i.val < 7 then cover6 else cover7))) else (if i.val < 12 then (if i.val < 10 then (if i.val < 9 then cover3 else cover2) else (if i.val < 11 then cover5 else cover4)) else (if i.val < 14 then (if i.val < 13 then cover0 else cover1) else (if i.val < 15 then cover6 else cover7))))
private def coverImages (j : Fin 2) : Equiv.Perm (Fin 4) := (if j.val < 1 then cover2 else cover6)
private theorem cover_step : ∀ i j,
    coverValues (BinaryMenuCayley8T8.certificate.next i j)=coverValues i*coverImages j := (by decide +kernel)
private theorem cover_identity : coverValues BinaryMenuCayley8T8.certificate.identity=1 := by decide +kernel

def cover : Source →* Equiv.Perm (Fin 4) where
  toFun x := coverValues x.index
  map_one' := cover_identity
  map_mul' x y := by
    change coverValues (BinaryMenuCayley8T8.certificate.walk x.index
      (BinaryMenuCayley8T8.certificate.words y.index))=coverValues x.index*coverValues y.index
    rw [EncodedCayleyCertificate.values_walk _ coverValues coverImages cover_step,
      ← EncodedCayleyCertificate.values_word _ coverValues coverImages cover_step cover_identity]

theorem cover_kernel : cover.ker=top.ker⊔BinaryNormal8T8.N1.kernel := by
  rw [join_eq]
  ext x
  change cover x=1 ↔ x∈(BinaryNormal8T8.states 1).kernel
  rw [← member_iff]
  exact (show ∀ x : Source, cover x=1 ↔ member 1 x from by decide +kernel) x

/-- Every local numerical dimension follows from checked original subgroup
orders and maps; the selected original cut and full fixed preimage remain. -/
def certificate : BinaryPairLocalCertificate generators top BinaryNormal8T8.N1.kernel where
  cut := BinaryNormal8T8.N1.kernel
  cut_normal := inferInstance
  cut_le_kernel := cut_le
  intersection_le_cut := intersection_le
  central := cut_central
  cutDimension := 0
  fixedDimension := 0
  cut_card := by simp only [intersection_eq,BinaryNormal8T8.N1.kernel_card,BinaryNormal8T8.N1.kernel_card] <;> decide
  fixed_card := by simp only [fixed_eq,BinaryNormal8T8.N1.kernel_card,BinaryNormal8T8.N1.kernel_card] <;> decide
  coverDegree := 4
  cover := cover
  cover_kernel := cover_kernel
  width := 8
  gap := by decide

end N1

namespace N2

theorem intersection_eq : top.ker⊓BinaryNormal8T8.N2.kernel=BinaryNormal8T8.N1.kernel := by
  rw [kernel_eq]
  ext x
  change (x∈(BinaryNormal8T8.states 1).kernel ∧ x∈(BinaryNormal8T8.states 2).kernel) ↔ x∈(BinaryNormal8T8.states 1).kernel
  simp only [← member_iff]
  exact (show ∀ x : Source, (member 1 x ∧ member 2 x) ↔ member 1 x from by decide +kernel) x

theorem cut_le : BinaryNormal8T8.N1.kernel≤top.ker := by
  intro x hx
  have hk : x∈BinaryNormal8T8.N1.kernel := (member_iff 1 x).mp
    ((show ∀ x : Source, member 1 x → member 1 x from by decide +kernel) x ((member_iff 1 x).mpr hx))
  exact kernel_eq.symm ▸ hk

theorem intersection_le : top.ker⊓BinaryNormal8T8.N2.kernel≤BinaryNormal8T8.N1.kernel := by
  intro x hx
  have hx' : x∈BinaryNormal8T8.N1.kernel := intersection_eq ▸ hx
  apply (member_iff 1 x).mp
  exact (show ∀ x : Source, member 1 x → member 1 x from by decide +kernel) x ((member_iff 1 x).mpr hx')

theorem cut_central : ∀ j, ∀ x : BinaryNormal8T8.N1.kernel,
    (x:Source)⁻¹*(generators j*(x:Source)*(generators j)⁻¹)∈BinaryNormal8T8.N2.kernel := by
  have h : ∀ j, ∀ x : Source, member 1 x →
      member 2 (x⁻¹*(generators j*x*(generators j)⁻¹)) := by decide +kernel
  intro j x
  exact (member_iff 2 _).mp (h j x.val ((member_iff 1 x.val).mpr x.property))

theorem fixed_eq : binaryPairFixedSubgroup top.ker BinaryNormal8T8.N1.kernel=BinaryNormal8T8.N1.kernel := by
  rw [kernel_eq]
  ext x
  rw [binaryPairFixedSubgroup_mem_iff _ _ generators BinaryNormal8T8.generators_full]
  change (x∈(BinaryNormal8T8.states 1).kernel ∧ ∀ j,
    x⁻¹*(generators j*x*(generators j)⁻¹)∈(BinaryNormal8T8.states 1).kernel) ↔ x∈(BinaryNormal8T8.states 1).kernel
  simp only [← member_iff]
  exact (show ∀ x : Source, (member 1 x ∧ ∀ j,
    member 1 (x⁻¹*(generators j*x*(generators j)⁻¹))) ↔ member 1 x from by decide +kernel) x

/-- These are the actual selected cut lift generators from this record. -/
def recordedCutGenerators (j : Fin 1) : Source := ⟨(7 : Fin 16)⟩
private def cutWords (j : Fin 1) : List (Fin 1) := ([0] : List (Fin 1))
private theorem cutWords_checked : ∀ j,
    ((cutWords j).map recordedCutGenerators).prod=BinaryNormal8T8.N1.normalGenerators j := by decide +kernel

theorem recorded_cut_eq : Subgroup.closure (Set.range recordedCutGenerators)=BinaryNormal8T8.N1.kernel := by
  apply le_antisymm
  · apply (Subgroup.closure_le _).mpr
    rintro _ ⟨j,rfl⟩
    exact (member_iff 1 _).mp
      ((show ∀ j, member 1 (recordedCutGenerators j) from by decide +kernel) j)
  · exact (BinaryNormalGeneratorWords.closure_le
      ({words := cutWords, equations := cutWords_checked} :
        BinaryNormalGeneratorWords BinaryNormal8T8.N1.normalGenerators recordedCutGenerators))

private def kernelPart (j : Fin 1) : Source := ⟨(7 : Fin 16)⟩
private def normalPart (j : Fin 1) : Source := ⟨(11 : Fin 16)⟩

theorem join_eq : top.ker⊔BinaryNormal8T8.N2.kernel=BinaryNormal8T8.N2.kernel := by
  apply le_antisymm
  · apply sup_le
    · intro x hx
      have hx' : x∈BinaryNormal8T8.N1.kernel := kernel_eq ▸ hx
      exact (member_iff 2 x).mp
        ((show ∀ x : Source, member 1 x → member 2 x from by decide +kernel) x ((member_iff 1 x).mpr hx'))
    · intro x hx
      exact (member_iff 2 x).mp
        ((show ∀ x : Source, member 2 x → member 2 x from by decide +kernel) x ((member_iff 2 x).mpr hx))
  · change Subgroup.closure (Set.range BinaryNormal8T8.N2.normalGenerators)≤_
    apply (Subgroup.closure_le _).mpr
    rintro _ ⟨j,rfl⟩
    have he : ∀ j, kernelPart j*normalPart j=BinaryNormal8T8.N2.normalGenerators j := by decide +kernel
    rw [← he j]
    apply Subgroup.mul_mem
    · apply (show top.ker≤top.ker⊔BinaryNormal8T8.N2.kernel from le_sup_left)
      rw [kernel_eq]
      exact (member_iff 1 _).mp ((show ∀ j, member 1 (kernelPart j) from by decide +kernel) j)
    · apply (show BinaryNormal8T8.N2.kernel≤top.ker⊔BinaryNormal8T8.N2.kernel from le_sup_right)
      exact (member_iff 2 _).mp ((show ∀ j, member 2 (normalPart j) from by decide +kernel) j)

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

private def coverValues (i : Fin 16) : Equiv.Perm (Fin 4) := (if i.val < 8 then (if i.val < 4 then (if i.val < 2 then (if i.val < 1 then cover0 else cover1) else (if i.val < 3 then cover3 else cover2)) else (if i.val < 6 then (if i.val < 5 then cover1 else cover0) else (if i.val < 7 then cover2 else cover3))) else (if i.val < 12 then (if i.val < 10 then (if i.val < 9 then cover0 else cover1) else (if i.val < 11 then cover2 else cover3)) else (if i.val < 14 then (if i.val < 13 then cover0 else cover1) else (if i.val < 15 then cover2 else cover3))))
private def coverImages (j : Fin 2) : Equiv.Perm (Fin 4) := (if j.val < 1 then cover1 else cover2)
private theorem cover_step : ∀ i j,
    coverValues (BinaryMenuCayley8T8.certificate.next i j)=coverValues i*coverImages j := (by decide +kernel)
private theorem cover_identity : coverValues BinaryMenuCayley8T8.certificate.identity=1 := by decide +kernel

def cover : Source →* Equiv.Perm (Fin 4) where
  toFun x := coverValues x.index
  map_one' := cover_identity
  map_mul' x y := by
    change coverValues (BinaryMenuCayley8T8.certificate.walk x.index
      (BinaryMenuCayley8T8.certificate.words y.index))=coverValues x.index*coverValues y.index
    rw [EncodedCayleyCertificate.values_walk _ coverValues coverImages cover_step,
      ← EncodedCayleyCertificate.values_word _ coverValues coverImages cover_step cover_identity]

theorem cover_kernel : cover.ker=top.ker⊔BinaryNormal8T8.N2.kernel := by
  rw [join_eq]
  ext x
  change cover x=1 ↔ x∈(BinaryNormal8T8.states 2).kernel
  rw [← member_iff]
  exact (show ∀ x : Source, cover x=1 ↔ member 2 x from by decide +kernel) x

/-- Every local numerical dimension follows from checked original subgroup
orders and maps; the selected original cut and full fixed preimage remain. -/
def certificate : BinaryPairLocalCertificate generators top BinaryNormal8T8.N2.kernel where
  cut := BinaryNormal8T8.N1.kernel
  cut_normal := inferInstance
  cut_le_kernel := cut_le
  intersection_le_cut := intersection_le
  central := cut_central
  cutDimension := 0
  fixedDimension := 0
  cut_card := by simp only [intersection_eq,BinaryNormal8T8.N1.kernel_card,BinaryNormal8T8.N1.kernel_card] <;> decide
  fixed_card := by simp only [fixed_eq,BinaryNormal8T8.N1.kernel_card,BinaryNormal8T8.N1.kernel_card] <;> decide
  coverDegree := 4
  cover := cover
  cover_kernel := cover_kernel
  width := 8
  gap := by decide

end N2

namespace N3

theorem intersection_eq : top.ker⊓BinaryNormal8T8.N3.kernel=BinaryNormal8T8.N1.kernel := by
  rw [kernel_eq]
  ext x
  change (x∈(BinaryNormal8T8.states 1).kernel ∧ x∈(BinaryNormal8T8.states 3).kernel) ↔ x∈(BinaryNormal8T8.states 1).kernel
  simp only [← member_iff]
  exact (show ∀ x : Source, (member 1 x ∧ member 3 x) ↔ member 1 x from by decide +kernel) x

theorem cut_le : BinaryNormal8T8.N1.kernel≤top.ker := by
  intro x hx
  have hk : x∈BinaryNormal8T8.N1.kernel := (member_iff 1 x).mp
    ((show ∀ x : Source, member 1 x → member 1 x from by decide +kernel) x ((member_iff 1 x).mpr hx))
  exact kernel_eq.symm ▸ hk

theorem intersection_le : top.ker⊓BinaryNormal8T8.N3.kernel≤BinaryNormal8T8.N1.kernel := by
  intro x hx
  have hx' : x∈BinaryNormal8T8.N1.kernel := intersection_eq ▸ hx
  apply (member_iff 1 x).mp
  exact (show ∀ x : Source, member 1 x → member 1 x from by decide +kernel) x ((member_iff 1 x).mpr hx')

theorem cut_central : ∀ j, ∀ x : BinaryNormal8T8.N1.kernel,
    (x:Source)⁻¹*(generators j*(x:Source)*(generators j)⁻¹)∈BinaryNormal8T8.N3.kernel := by
  have h : ∀ j, ∀ x : Source, member 1 x →
      member 3 (x⁻¹*(generators j*x*(generators j)⁻¹)) := by decide +kernel
  intro j x
  exact (member_iff 3 _).mp (h j x.val ((member_iff 1 x.val).mpr x.property))

theorem fixed_eq : binaryPairFixedSubgroup top.ker BinaryNormal8T8.N1.kernel=BinaryNormal8T8.N1.kernel := by
  rw [kernel_eq]
  ext x
  rw [binaryPairFixedSubgroup_mem_iff _ _ generators BinaryNormal8T8.generators_full]
  change (x∈(BinaryNormal8T8.states 1).kernel ∧ ∀ j,
    x⁻¹*(generators j*x*(generators j)⁻¹)∈(BinaryNormal8T8.states 1).kernel) ↔ x∈(BinaryNormal8T8.states 1).kernel
  simp only [← member_iff]
  exact (show ∀ x : Source, (member 1 x ∧ ∀ j,
    member 1 (x⁻¹*(generators j*x*(generators j)⁻¹))) ↔ member 1 x from by decide +kernel) x

/-- These are the actual selected cut lift generators from this record. -/
def recordedCutGenerators (j : Fin 1) : Source := ⟨(7 : Fin 16)⟩
private def cutWords (j : Fin 1) : List (Fin 1) := ([0] : List (Fin 1))
private theorem cutWords_checked : ∀ j,
    ((cutWords j).map recordedCutGenerators).prod=BinaryNormal8T8.N1.normalGenerators j := by decide +kernel

theorem recorded_cut_eq : Subgroup.closure (Set.range recordedCutGenerators)=BinaryNormal8T8.N1.kernel := by
  apply le_antisymm
  · apply (Subgroup.closure_le _).mpr
    rintro _ ⟨j,rfl⟩
    exact (member_iff 1 _).mp
      ((show ∀ j, member 1 (recordedCutGenerators j) from by decide +kernel) j)
  · exact (BinaryNormalGeneratorWords.closure_le
      ({words := cutWords, equations := cutWords_checked} :
        BinaryNormalGeneratorWords BinaryNormal8T8.N1.normalGenerators recordedCutGenerators))

private def kernelPart (j : Fin 2) : Source := ⟨((if j.val < 1 then 7 else 7) : Fin 16)⟩
private def normalPart (j : Fin 2) : Source := ⟨((if j.val < 1 then 5 else 11) : Fin 16)⟩

theorem join_eq : top.ker⊔BinaryNormal8T8.N3.kernel=BinaryNormal8T8.N3.kernel := by
  apply le_antisymm
  · apply sup_le
    · intro x hx
      have hx' : x∈BinaryNormal8T8.N1.kernel := kernel_eq ▸ hx
      exact (member_iff 3 x).mp
        ((show ∀ x : Source, member 1 x → member 3 x from by decide +kernel) x ((member_iff 1 x).mpr hx'))
    · intro x hx
      exact (member_iff 3 x).mp
        ((show ∀ x : Source, member 3 x → member 3 x from by decide +kernel) x ((member_iff 3 x).mpr hx))
  · change Subgroup.closure (Set.range BinaryNormal8T8.N3.normalGenerators)≤_
    apply (Subgroup.closure_le _).mpr
    rintro _ ⟨j,rfl⟩
    have he : ∀ j, kernelPart j*normalPart j=BinaryNormal8T8.N3.normalGenerators j := by decide +kernel
    rw [← he j]
    apply Subgroup.mul_mem
    · apply (show top.ker≤top.ker⊔BinaryNormal8T8.N3.kernel from le_sup_left)
      rw [kernel_eq]
      exact (member_iff 1 _).mp ((show ∀ j, member 1 (kernelPart j) from by decide +kernel) j)
    · apply (show BinaryNormal8T8.N3.kernel≤top.ker⊔BinaryNormal8T8.N3.kernel from le_sup_right)
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

private def coverValues (i : Fin 16) : Equiv.Perm (Fin 2) := (if i.val < 8 then (if i.val < 4 then (if i.val < 2 then (if i.val < 1 then cover1 else cover0) else (if i.val < 3 then cover1 else cover0)) else (if i.val < 6 then (if i.val < 5 then cover0 else cover1) else (if i.val < 7 then cover0 else cover1))) else (if i.val < 12 then (if i.val < 10 then (if i.val < 9 then cover1 else cover0) else (if i.val < 11 then cover0 else cover1)) else (if i.val < 14 then (if i.val < 13 then cover1 else cover0) else (if i.val < 15 then cover0 else cover1))))
private def coverImages (j : Fin 2) : Equiv.Perm (Fin 2) := (if j.val < 1 then cover0 else cover0)
private theorem cover_step : ∀ i j,
    coverValues (BinaryMenuCayley8T8.certificate.next i j)=coverValues i*coverImages j := (by decide +kernel)
private theorem cover_identity : coverValues BinaryMenuCayley8T8.certificate.identity=1 := by decide +kernel

def cover : Source →* Equiv.Perm (Fin 2) where
  toFun x := coverValues x.index
  map_one' := cover_identity
  map_mul' x y := by
    change coverValues (BinaryMenuCayley8T8.certificate.walk x.index
      (BinaryMenuCayley8T8.certificate.words y.index))=coverValues x.index*coverValues y.index
    rw [EncodedCayleyCertificate.values_walk _ coverValues coverImages cover_step,
      ← EncodedCayleyCertificate.values_word _ coverValues coverImages cover_step cover_identity]

theorem cover_kernel : cover.ker=top.ker⊔BinaryNormal8T8.N3.kernel := by
  rw [join_eq]
  ext x
  change cover x=1 ↔ x∈(BinaryNormal8T8.states 3).kernel
  rw [← member_iff]
  exact (show ∀ x : Source, cover x=1 ↔ member 3 x from by decide +kernel) x

/-- Every local numerical dimension follows from checked original subgroup
orders and maps; the selected original cut and full fixed preimage remain. -/
def certificate : BinaryPairLocalCertificate generators top BinaryNormal8T8.N3.kernel where
  cut := BinaryNormal8T8.N1.kernel
  cut_normal := inferInstance
  cut_le_kernel := cut_le
  intersection_le_cut := intersection_le
  central := cut_central
  cutDimension := 0
  fixedDimension := 0
  cut_card := by simp only [intersection_eq,BinaryNormal8T8.N1.kernel_card,BinaryNormal8T8.N1.kernel_card] <;> decide
  fixed_card := by simp only [fixed_eq,BinaryNormal8T8.N1.kernel_card,BinaryNormal8T8.N1.kernel_card] <;> decide
  coverDegree := 2
  cover := cover
  cover_kernel := cover_kernel
  width := 8
  gap := by decide

end N3

namespace N4

theorem intersection_eq : top.ker⊓BinaryNormal8T8.N4.kernel=BinaryNormal8T8.N1.kernel := by
  rw [kernel_eq]
  ext x
  change (x∈(BinaryNormal8T8.states 1).kernel ∧ x∈(BinaryNormal8T8.states 4).kernel) ↔ x∈(BinaryNormal8T8.states 1).kernel
  simp only [← member_iff]
  exact (show ∀ x : Source, (member 1 x ∧ member 4 x) ↔ member 1 x from by decide +kernel) x

theorem cut_le : BinaryNormal8T8.N1.kernel≤top.ker := by
  intro x hx
  have hk : x∈BinaryNormal8T8.N1.kernel := (member_iff 1 x).mp
    ((show ∀ x : Source, member 1 x → member 1 x from by decide +kernel) x ((member_iff 1 x).mpr hx))
  exact kernel_eq.symm ▸ hk

theorem intersection_le : top.ker⊓BinaryNormal8T8.N4.kernel≤BinaryNormal8T8.N1.kernel := by
  intro x hx
  have hx' : x∈BinaryNormal8T8.N1.kernel := intersection_eq ▸ hx
  apply (member_iff 1 x).mp
  exact (show ∀ x : Source, member 1 x → member 1 x from by decide +kernel) x ((member_iff 1 x).mpr hx')

theorem cut_central : ∀ j, ∀ x : BinaryNormal8T8.N1.kernel,
    (x:Source)⁻¹*(generators j*(x:Source)*(generators j)⁻¹)∈BinaryNormal8T8.N4.kernel := by
  have h : ∀ j, ∀ x : Source, member 1 x →
      member 4 (x⁻¹*(generators j*x*(generators j)⁻¹)) := by decide +kernel
  intro j x
  exact (member_iff 4 _).mp (h j x.val ((member_iff 1 x.val).mpr x.property))

theorem fixed_eq : binaryPairFixedSubgroup top.ker BinaryNormal8T8.N1.kernel=BinaryNormal8T8.N1.kernel := by
  rw [kernel_eq]
  ext x
  rw [binaryPairFixedSubgroup_mem_iff _ _ generators BinaryNormal8T8.generators_full]
  change (x∈(BinaryNormal8T8.states 1).kernel ∧ ∀ j,
    x⁻¹*(generators j*x*(generators j)⁻¹)∈(BinaryNormal8T8.states 1).kernel) ↔ x∈(BinaryNormal8T8.states 1).kernel
  simp only [← member_iff]
  exact (show ∀ x : Source, (member 1 x ∧ ∀ j,
    member 1 (x⁻¹*(generators j*x*(generators j)⁻¹))) ↔ member 1 x from by decide +kernel) x

/-- These are the actual selected cut lift generators from this record. -/
def recordedCutGenerators (j : Fin 1) : Source := ⟨(7 : Fin 16)⟩
private def cutWords (j : Fin 1) : List (Fin 1) := ([0] : List (Fin 1))
private theorem cutWords_checked : ∀ j,
    ((cutWords j).map recordedCutGenerators).prod=BinaryNormal8T8.N1.normalGenerators j := by decide +kernel

theorem recorded_cut_eq : Subgroup.closure (Set.range recordedCutGenerators)=BinaryNormal8T8.N1.kernel := by
  apply le_antisymm
  · apply (Subgroup.closure_le _).mpr
    rintro _ ⟨j,rfl⟩
    exact (member_iff 1 _).mp
      ((show ∀ j, member 1 (recordedCutGenerators j) from by decide +kernel) j)
  · exact (BinaryNormalGeneratorWords.closure_le
      ({words := cutWords, equations := cutWords_checked} :
        BinaryNormalGeneratorWords BinaryNormal8T8.N1.normalGenerators recordedCutGenerators))

private def kernelPart (j : Fin 2) : Source := ⟨((if j.val < 1 then 7 else 7) : Fin 16)⟩
private def normalPart (j : Fin 2) : Source := ⟨((if j.val < 1 then 11 else 3) : Fin 16)⟩

theorem join_eq : top.ker⊔BinaryNormal8T8.N4.kernel=BinaryNormal8T8.N4.kernel := by
  apply le_antisymm
  · apply sup_le
    · intro x hx
      have hx' : x∈BinaryNormal8T8.N1.kernel := kernel_eq ▸ hx
      exact (member_iff 4 x).mp
        ((show ∀ x : Source, member 1 x → member 4 x from by decide +kernel) x ((member_iff 1 x).mpr hx'))
    · intro x hx
      exact (member_iff 4 x).mp
        ((show ∀ x : Source, member 4 x → member 4 x from by decide +kernel) x ((member_iff 4 x).mpr hx))
  · change Subgroup.closure (Set.range BinaryNormal8T8.N4.normalGenerators)≤_
    apply (Subgroup.closure_le _).mpr
    rintro _ ⟨j,rfl⟩
    have he : ∀ j, kernelPart j*normalPart j=BinaryNormal8T8.N4.normalGenerators j := by decide +kernel
    rw [← he j]
    apply Subgroup.mul_mem
    · apply (show top.ker≤top.ker⊔BinaryNormal8T8.N4.kernel from le_sup_left)
      rw [kernel_eq]
      exact (member_iff 1 _).mp ((show ∀ j, member 1 (kernelPart j) from by decide +kernel) j)
    · apply (show BinaryNormal8T8.N4.kernel≤top.ker⊔BinaryNormal8T8.N4.kernel from le_sup_right)
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

private def coverValues (i : Fin 16) : Equiv.Perm (Fin 2) := (if i.val < 8 then (if i.val < 4 then (if i.val < 2 then (if i.val < 1 then cover0 else cover0) else (if i.val < 3 then cover1 else cover1)) else (if i.val < 6 then (if i.val < 5 then cover0 else cover0) else (if i.val < 7 then cover1 else cover1))) else (if i.val < 12 then (if i.val < 10 then (if i.val < 9 then cover0 else cover0) else (if i.val < 11 then cover1 else cover1)) else (if i.val < 14 then (if i.val < 13 then cover0 else cover0) else (if i.val < 15 then cover1 else cover1))))
private def coverImages (j : Fin 2) : Equiv.Perm (Fin 2) := (if j.val < 1 then cover0 else cover1)
private theorem cover_step : ∀ i j,
    coverValues (BinaryMenuCayley8T8.certificate.next i j)=coverValues i*coverImages j := (by decide +kernel)
private theorem cover_identity : coverValues BinaryMenuCayley8T8.certificate.identity=1 := by decide +kernel

def cover : Source →* Equiv.Perm (Fin 2) where
  toFun x := coverValues x.index
  map_one' := cover_identity
  map_mul' x y := by
    change coverValues (BinaryMenuCayley8T8.certificate.walk x.index
      (BinaryMenuCayley8T8.certificate.words y.index))=coverValues x.index*coverValues y.index
    rw [EncodedCayleyCertificate.values_walk _ coverValues coverImages cover_step,
      ← EncodedCayleyCertificate.values_word _ coverValues coverImages cover_step cover_identity]

theorem cover_kernel : cover.ker=top.ker⊔BinaryNormal8T8.N4.kernel := by
  rw [join_eq]
  ext x
  change cover x=1 ↔ x∈(BinaryNormal8T8.states 4).kernel
  rw [← member_iff]
  exact (show ∀ x : Source, cover x=1 ↔ member 4 x from by decide +kernel) x

/-- Every local numerical dimension follows from checked original subgroup
orders and maps; the selected original cut and full fixed preimage remain. -/
def certificate : BinaryPairLocalCertificate generators top BinaryNormal8T8.N4.kernel where
  cut := BinaryNormal8T8.N1.kernel
  cut_normal := inferInstance
  cut_le_kernel := cut_le
  intersection_le_cut := intersection_le
  central := cut_central
  cutDimension := 0
  fixedDimension := 0
  cut_card := by simp only [intersection_eq,BinaryNormal8T8.N1.kernel_card,BinaryNormal8T8.N1.kernel_card] <;> decide
  fixed_card := by simp only [fixed_eq,BinaryNormal8T8.N1.kernel_card,BinaryNormal8T8.N1.kernel_card] <;> decide
  coverDegree := 2
  cover := cover
  cover_kernel := cover_kernel
  width := 8
  gap := by decide

end N4

namespace N5

theorem intersection_eq : top.ker⊓BinaryNormal8T8.N5.kernel=BinaryNormal8T8.N1.kernel := by
  rw [kernel_eq]
  ext x
  change (x∈(BinaryNormal8T8.states 1).kernel ∧ x∈(BinaryNormal8T8.states 5).kernel) ↔ x∈(BinaryNormal8T8.states 1).kernel
  simp only [← member_iff]
  exact (show ∀ x : Source, (member 1 x ∧ member 5 x) ↔ member 1 x from by decide +kernel) x

theorem cut_le : BinaryNormal8T8.N1.kernel≤top.ker := by
  intro x hx
  have hk : x∈BinaryNormal8T8.N1.kernel := (member_iff 1 x).mp
    ((show ∀ x : Source, member 1 x → member 1 x from by decide +kernel) x ((member_iff 1 x).mpr hx))
  exact kernel_eq.symm ▸ hk

theorem intersection_le : top.ker⊓BinaryNormal8T8.N5.kernel≤BinaryNormal8T8.N1.kernel := by
  intro x hx
  have hx' : x∈BinaryNormal8T8.N1.kernel := intersection_eq ▸ hx
  apply (member_iff 1 x).mp
  exact (show ∀ x : Source, member 1 x → member 1 x from by decide +kernel) x ((member_iff 1 x).mpr hx')

theorem cut_central : ∀ j, ∀ x : BinaryNormal8T8.N1.kernel,
    (x:Source)⁻¹*(generators j*(x:Source)*(generators j)⁻¹)∈BinaryNormal8T8.N5.kernel := by
  have h : ∀ j, ∀ x : Source, member 1 x →
      member 5 (x⁻¹*(generators j*x*(generators j)⁻¹)) := by decide +kernel
  intro j x
  exact (member_iff 5 _).mp (h j x.val ((member_iff 1 x.val).mpr x.property))

theorem fixed_eq : binaryPairFixedSubgroup top.ker BinaryNormal8T8.N1.kernel=BinaryNormal8T8.N1.kernel := by
  rw [kernel_eq]
  ext x
  rw [binaryPairFixedSubgroup_mem_iff _ _ generators BinaryNormal8T8.generators_full]
  change (x∈(BinaryNormal8T8.states 1).kernel ∧ ∀ j,
    x⁻¹*(generators j*x*(generators j)⁻¹)∈(BinaryNormal8T8.states 1).kernel) ↔ x∈(BinaryNormal8T8.states 1).kernel
  simp only [← member_iff]
  exact (show ∀ x : Source, (member 1 x ∧ ∀ j,
    member 1 (x⁻¹*(generators j*x*(generators j)⁻¹))) ↔ member 1 x from by decide +kernel) x

/-- These are the actual selected cut lift generators from this record. -/
def recordedCutGenerators (j : Fin 1) : Source := ⟨(7 : Fin 16)⟩
private def cutWords (j : Fin 1) : List (Fin 1) := ([0] : List (Fin 1))
private theorem cutWords_checked : ∀ j,
    ((cutWords j).map recordedCutGenerators).prod=BinaryNormal8T8.N1.normalGenerators j := by decide +kernel

theorem recorded_cut_eq : Subgroup.closure (Set.range recordedCutGenerators)=BinaryNormal8T8.N1.kernel := by
  apply le_antisymm
  · apply (Subgroup.closure_le _).mpr
    rintro _ ⟨j,rfl⟩
    exact (member_iff 1 _).mp
      ((show ∀ j, member 1 (recordedCutGenerators j) from by decide +kernel) j)
  · exact (BinaryNormalGeneratorWords.closure_le
      ({words := cutWords, equations := cutWords_checked} :
        BinaryNormalGeneratorWords BinaryNormal8T8.N1.normalGenerators recordedCutGenerators))

private def kernelPart (j : Fin 1) : Source := ⟨(7 : Fin 16)⟩
private def normalPart (j : Fin 1) : Source := ⟨(9 : Fin 16)⟩

theorem join_eq : top.ker⊔BinaryNormal8T8.N5.kernel=BinaryNormal8T8.N5.kernel := by
  apply le_antisymm
  · apply sup_le
    · intro x hx
      have hx' : x∈BinaryNormal8T8.N1.kernel := kernel_eq ▸ hx
      exact (member_iff 5 x).mp
        ((show ∀ x : Source, member 1 x → member 5 x from by decide +kernel) x ((member_iff 1 x).mpr hx'))
    · intro x hx
      exact (member_iff 5 x).mp
        ((show ∀ x : Source, member 5 x → member 5 x from by decide +kernel) x ((member_iff 5 x).mpr hx))
  · change Subgroup.closure (Set.range BinaryNormal8T8.N5.normalGenerators)≤_
    apply (Subgroup.closure_le _).mpr
    rintro _ ⟨j,rfl⟩
    have he : ∀ j, kernelPart j*normalPart j=BinaryNormal8T8.N5.normalGenerators j := by decide +kernel
    rw [← he j]
    apply Subgroup.mul_mem
    · apply (show top.ker≤top.ker⊔BinaryNormal8T8.N5.kernel from le_sup_left)
      rw [kernel_eq]
      exact (member_iff 1 _).mp ((show ∀ j, member 1 (kernelPart j) from by decide +kernel) j)
    · apply (show BinaryNormal8T8.N5.kernel≤top.ker⊔BinaryNormal8T8.N5.kernel from le_sup_right)
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

private def coverValues (i : Fin 16) : Equiv.Perm (Fin 2) := (if i.val < 8 then (if i.val < 4 then (if i.val < 2 then (if i.val < 1 then cover0 else cover1) else (if i.val < 3 then cover1 else cover0)) else (if i.val < 6 then (if i.val < 5 then cover1 else cover0) else (if i.val < 7 then cover0 else cover1))) else (if i.val < 12 then (if i.val < 10 then (if i.val < 9 then cover0 else cover1) else (if i.val < 11 then cover0 else cover1)) else (if i.val < 14 then (if i.val < 13 then cover0 else cover1) else (if i.val < 15 then cover0 else cover1))))
private def coverImages (j : Fin 2) : Equiv.Perm (Fin 2) := (if j.val < 1 then cover1 else cover0)
private theorem cover_step : ∀ i j,
    coverValues (BinaryMenuCayley8T8.certificate.next i j)=coverValues i*coverImages j := (by decide +kernel)
private theorem cover_identity : coverValues BinaryMenuCayley8T8.certificate.identity=1 := by decide +kernel

def cover : Source →* Equiv.Perm (Fin 2) where
  toFun x := coverValues x.index
  map_one' := cover_identity
  map_mul' x y := by
    change coverValues (BinaryMenuCayley8T8.certificate.walk x.index
      (BinaryMenuCayley8T8.certificate.words y.index))=coverValues x.index*coverValues y.index
    rw [EncodedCayleyCertificate.values_walk _ coverValues coverImages cover_step,
      ← EncodedCayleyCertificate.values_word _ coverValues coverImages cover_step cover_identity]

theorem cover_kernel : cover.ker=top.ker⊔BinaryNormal8T8.N5.kernel := by
  rw [join_eq]
  ext x
  change cover x=1 ↔ x∈(BinaryNormal8T8.states 5).kernel
  rw [← member_iff]
  exact (show ∀ x : Source, cover x=1 ↔ member 5 x from by decide +kernel) x

/-- Every local numerical dimension follows from checked original subgroup
orders and maps; the selected original cut and full fixed preimage remain. -/
def certificate : BinaryPairLocalCertificate generators top BinaryNormal8T8.N5.kernel where
  cut := BinaryNormal8T8.N1.kernel
  cut_normal := inferInstance
  cut_le_kernel := cut_le
  intersection_le_cut := intersection_le
  central := cut_central
  cutDimension := 0
  fixedDimension := 0
  cut_card := by simp only [intersection_eq,BinaryNormal8T8.N1.kernel_card,BinaryNormal8T8.N1.kernel_card] <;> decide
  fixed_card := by simp only [fixed_eq,BinaryNormal8T8.N1.kernel_card,BinaryNormal8T8.N1.kernel_card] <;> decide
  coverDegree := 2
  cover := cover
  cover_kernel := cover_kernel
  width := 8
  gap := by decide

end N5

namespace N6

theorem intersection_eq : top.ker⊓BinaryNormal8T8.N6.kernel=BinaryNormal8T8.N1.kernel := by
  rw [kernel_eq]
  ext x
  change (x∈(BinaryNormal8T8.states 1).kernel ∧ x∈(BinaryNormal8T8.states 6).kernel) ↔ x∈(BinaryNormal8T8.states 1).kernel
  simp only [← member_iff]
  exact (show ∀ x : Source, (member 1 x ∧ member 6 x) ↔ member 1 x from by decide +kernel) x

theorem cut_le : BinaryNormal8T8.N1.kernel≤top.ker := by
  intro x hx
  have hk : x∈BinaryNormal8T8.N1.kernel := (member_iff 1 x).mp
    ((show ∀ x : Source, member 1 x → member 1 x from by decide +kernel) x ((member_iff 1 x).mpr hx))
  exact kernel_eq.symm ▸ hk

theorem intersection_le : top.ker⊓BinaryNormal8T8.N6.kernel≤BinaryNormal8T8.N1.kernel := by
  intro x hx
  have hx' : x∈BinaryNormal8T8.N1.kernel := intersection_eq ▸ hx
  apply (member_iff 1 x).mp
  exact (show ∀ x : Source, member 1 x → member 1 x from by decide +kernel) x ((member_iff 1 x).mpr hx')

theorem cut_central : ∀ j, ∀ x : BinaryNormal8T8.N1.kernel,
    (x:Source)⁻¹*(generators j*(x:Source)*(generators j)⁻¹)∈BinaryNormal8T8.N6.kernel := by
  have h : ∀ j, ∀ x : Source, member 1 x →
      member 6 (x⁻¹*(generators j*x*(generators j)⁻¹)) := by decide +kernel
  intro j x
  exact (member_iff 6 _).mp (h j x.val ((member_iff 1 x.val).mpr x.property))

theorem fixed_eq : binaryPairFixedSubgroup top.ker BinaryNormal8T8.N1.kernel=BinaryNormal8T8.N1.kernel := by
  rw [kernel_eq]
  ext x
  rw [binaryPairFixedSubgroup_mem_iff _ _ generators BinaryNormal8T8.generators_full]
  change (x∈(BinaryNormal8T8.states 1).kernel ∧ ∀ j,
    x⁻¹*(generators j*x*(generators j)⁻¹)∈(BinaryNormal8T8.states 1).kernel) ↔ x∈(BinaryNormal8T8.states 1).kernel
  simp only [← member_iff]
  exact (show ∀ x : Source, (member 1 x ∧ ∀ j,
    member 1 (x⁻¹*(generators j*x*(generators j)⁻¹))) ↔ member 1 x from by decide +kernel) x

/-- These are the actual selected cut lift generators from this record. -/
def recordedCutGenerators (j : Fin 1) : Source := ⟨(7 : Fin 16)⟩
private def cutWords (j : Fin 1) : List (Fin 1) := ([0] : List (Fin 1))
private theorem cutWords_checked : ∀ j,
    ((cutWords j).map recordedCutGenerators).prod=BinaryNormal8T8.N1.normalGenerators j := by decide +kernel

theorem recorded_cut_eq : Subgroup.closure (Set.range recordedCutGenerators)=BinaryNormal8T8.N1.kernel := by
  apply le_antisymm
  · apply (Subgroup.closure_le _).mpr
    rintro _ ⟨j,rfl⟩
    exact (member_iff 1 _).mp
      ((show ∀ j, member 1 (recordedCutGenerators j) from by decide +kernel) j)
  · exact (BinaryNormalGeneratorWords.closure_le
      ({words := cutWords, equations := cutWords_checked} :
        BinaryNormalGeneratorWords BinaryNormal8T8.N1.normalGenerators recordedCutGenerators))

private def kernelPart (j : Fin 2) : Source := ⟨((if j.val < 1 then 7 else 7) : Fin 16)⟩
private def normalPart (j : Fin 2) : Source := ⟨((if j.val < 1 then 9 else 6) : Fin 16)⟩

theorem join_eq : top.ker⊔BinaryNormal8T8.N6.kernel=BinaryNormal8T8.N6.kernel := by
  apply le_antisymm
  · apply sup_le
    · intro x hx
      have hx' : x∈BinaryNormal8T8.N1.kernel := kernel_eq ▸ hx
      exact (member_iff 6 x).mp
        ((show ∀ x : Source, member 1 x → member 6 x from by decide +kernel) x ((member_iff 1 x).mpr hx'))
    · intro x hx
      exact (member_iff 6 x).mp
        ((show ∀ x : Source, member 6 x → member 6 x from by decide +kernel) x ((member_iff 6 x).mpr hx))
  · change Subgroup.closure (Set.range BinaryNormal8T8.N6.normalGenerators)≤_
    apply (Subgroup.closure_le _).mpr
    rintro _ ⟨j,rfl⟩
    have he : ∀ j, kernelPart j*normalPart j=BinaryNormal8T8.N6.normalGenerators j := by decide +kernel
    rw [← he j]
    apply Subgroup.mul_mem
    · apply (show top.ker≤top.ker⊔BinaryNormal8T8.N6.kernel from le_sup_left)
      rw [kernel_eq]
      exact (member_iff 1 _).mp ((show ∀ j, member 1 (kernelPart j) from by decide +kernel) j)
    · apply (show BinaryNormal8T8.N6.kernel≤top.ker⊔BinaryNormal8T8.N6.kernel from le_sup_right)
      exact (member_iff 6 _).mp ((show ∀ j, member 6 (normalPart j) from by decide +kernel) j)

private def cover0 : Equiv.Perm (Fin 0) where
  toFun := Fin.elim0
  invFun := Fin.elim0
  left_inv := fun x => Fin.elim0 x
  right_inv := fun x => Fin.elim0 x

private def coverValues (i : Fin 16) : Equiv.Perm (Fin 0) := (if i.val < 8 then (if i.val < 4 then (if i.val < 2 then (if i.val < 1 then cover0 else cover0) else (if i.val < 3 then cover0 else cover0)) else (if i.val < 6 then (if i.val < 5 then cover0 else cover0) else (if i.val < 7 then cover0 else cover0))) else (if i.val < 12 then (if i.val < 10 then (if i.val < 9 then cover0 else cover0) else (if i.val < 11 then cover0 else cover0)) else (if i.val < 14 then (if i.val < 13 then cover0 else cover0) else (if i.val < 15 then cover0 else cover0))))
private def coverImages (j : Fin 2) : Equiv.Perm (Fin 0) := (if j.val < 1 then cover0 else cover0)
private theorem cover_step : ∀ i j,
    coverValues (BinaryMenuCayley8T8.certificate.next i j)=coverValues i*coverImages j := (by decide +kernel)
private theorem cover_identity : coverValues BinaryMenuCayley8T8.certificate.identity=1 := by decide +kernel

def cover : Source →* Equiv.Perm (Fin 0) where
  toFun x := coverValues x.index
  map_one' := cover_identity
  map_mul' x y := by
    change coverValues (BinaryMenuCayley8T8.certificate.walk x.index
      (BinaryMenuCayley8T8.certificate.words y.index))=coverValues x.index*coverValues y.index
    rw [EncodedCayleyCertificate.values_walk _ coverValues coverImages cover_step,
      ← EncodedCayleyCertificate.values_word _ coverValues coverImages cover_step cover_identity]

theorem cover_kernel : cover.ker=top.ker⊔BinaryNormal8T8.N6.kernel := by
  rw [join_eq]
  ext x
  change cover x=1 ↔ x∈(BinaryNormal8T8.states 6).kernel
  rw [← member_iff]
  exact (show ∀ x : Source, cover x=1 ↔ member 6 x from by decide +kernel) x

/-- Every local numerical dimension follows from checked original subgroup
orders and maps; the selected original cut and full fixed preimage remain. -/
def certificate : BinaryPairLocalCertificate generators top BinaryNormal8T8.N6.kernel where
  cut := BinaryNormal8T8.N1.kernel
  cut_normal := inferInstance
  cut_le_kernel := cut_le
  intersection_le_cut := intersection_le
  central := cut_central
  cutDimension := 0
  fixedDimension := 0
  cut_card := by simp only [intersection_eq,BinaryNormal8T8.N1.kernel_card,BinaryNormal8T8.N1.kernel_card] <;> decide
  fixed_card := by simp only [fixed_eq,BinaryNormal8T8.N1.kernel_card,BinaryNormal8T8.N1.kernel_card] <;> decide
  coverDegree := 0
  cover := cover
  cover_kernel := cover_kernel
  width := 8
  gap := by decide

end N6

end SymmetricSubgroupAsymptotics.BinaryPairLocal8T8
