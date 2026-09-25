import SymmetricSubgroupAsymptotics.BinaryPairFiniteRows
import SymmetricSubgroupAsymptotics.GeneratedNormal8.Registry8T30
import SymmetricSubgroupAsymptotics.GeneratedPair8.Frames8T30

/-! All pair-type normal states of 8T30: original cuts, complete fixed
preimages, quotient covers and exact local gaps. All finite equations use
the Lean kernel. Character and transport records are separate branches. -/
set_option autoImplicit false
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option linter.unusedVariables false
set_option linter.unnecessarySeqFocus false
noncomputable section
namespace SymmetricSubgroupAsymptotics.BinaryPairLocal8T30
abbrev Source := FiniteGroupRow 64
local instance : Group Source := BinaryMenuCayley8T30.group
abbrev generators := BinaryNormal8T30.generators
abbrev top := BinaryPair8T30.Frame0.topHom
private def mask (i : Fin 13) : ℕ := (if i.val < 6 then (if i.val < 3 then (if i.val < 1 then 9223372036854775808 else (if i.val < 2 then 9223372036921884672 else 9799832790299049984)) else (if i.val < 4 then 9799870173694398720 else (if i.val < 5 then 9799851481996730880 else 11024980114793326080))) else (if i.val < 9 then (if i.val < 7 then 12249884446362216960 else (if i.val < 8 then 14699749187159851008 else 14699805262252880640)) else (if i.val < 11 then (if i.val < 10 then 14757226376558555955 else 14714161362241795020) else (if i.val < 12 then 18374966859414961920 else 18446744073709551615))))
private abbrev member (i : Fin 13) (x : Source) : Prop := mask i / 2^x.index.val % 2=1

private theorem member_iff (i : Fin 13) (x : Source) :
    member i x ↔ x∈(BinaryNormal8T30.states i).kernel := by
  fin_cases i
  · change member 0 x ↔ x∈Subgroup.closure (Set.range BinaryNormal8T30.N0.normalGenerators)
    rw [binaryNormalRow_mem_iff BinaryNormal8T30.N0.normalCertificate]
    have h : ∀ z : Fin 64, member 0 ⟨z⟩ ↔ ∃ j : Fin 1, BinaryNormal8T30.N0.normalCertificate.rows j=z := (Fin.addCases (m := 32) (n := 32) (Fin.addCases (m := 16) (n := 16) (by decide +kernel) (by decide +kernel)) (Fin.addCases (m := 16) (n := 16) (by decide +kernel) (by decide +kernel)))
    exact h x.index
  · change member 1 x ↔ x∈Subgroup.closure (Set.range BinaryNormal8T30.N1.normalGenerators)
    rw [binaryNormalRow_mem_iff BinaryNormal8T30.N1.normalCertificate]
    have h : ∀ z : Fin 64, member 1 ⟨z⟩ ↔ ∃ j : Fin 2, BinaryNormal8T30.N1.normalCertificate.rows j=z := (Fin.addCases (m := 32) (n := 32) (Fin.addCases (m := 16) (n := 16) (by decide +kernel) (by decide +kernel)) (Fin.addCases (m := 16) (n := 16) (by decide +kernel) (by decide +kernel)))
    exact h x.index
  · change member 2 x ↔ x∈Subgroup.closure (Set.range BinaryNormal8T30.N2.normalGenerators)
    rw [binaryNormalRow_mem_iff BinaryNormal8T30.N2.normalCertificate]
    have h : ∀ z : Fin 64, member 2 ⟨z⟩ ↔ ∃ j : Fin 4, BinaryNormal8T30.N2.normalCertificate.rows j=z := (Fin.addCases (m := 32) (n := 32) (Fin.addCases (m := 16) (n := 16) (by decide +kernel) (by decide +kernel)) (Fin.addCases (m := 16) (n := 16) (by decide +kernel) (by decide +kernel)))
    exact h x.index
  · change member 3 x ↔ x∈Subgroup.closure (Set.range BinaryNormal8T30.N3.normalGenerators)
    rw [binaryNormalRow_mem_iff BinaryNormal8T30.N3.normalCertificate]
    have h : ∀ z : Fin 64, member 3 ⟨z⟩ ↔ ∃ j : Fin 8, BinaryNormal8T30.N3.normalCertificate.rows j=z := (Fin.addCases (m := 32) (n := 32) (Fin.addCases (m := 16) (n := 16) (by decide +kernel) (by decide +kernel)) (Fin.addCases (m := 16) (n := 16) (by decide +kernel) (by decide +kernel)))
    exact h x.index
  · change member 4 x ↔ x∈Subgroup.closure (Set.range BinaryNormal8T30.N4.normalGenerators)
    rw [binaryNormalRow_mem_iff BinaryNormal8T30.N4.normalCertificate]
    have h : ∀ z : Fin 64, member 4 ⟨z⟩ ↔ ∃ j : Fin 8, BinaryNormal8T30.N4.normalCertificate.rows j=z := (Fin.addCases (m := 32) (n := 32) (Fin.addCases (m := 16) (n := 16) (by decide +kernel) (by decide +kernel)) (Fin.addCases (m := 16) (n := 16) (by decide +kernel) (by decide +kernel)))
    exact h x.index
  · change member 5 x ↔ x∈Subgroup.closure (Set.range BinaryNormal8T30.N5.normalGenerators)
    rw [binaryNormalRow_mem_iff BinaryNormal8T30.N5.normalCertificate]
    have h : ∀ z : Fin 64, member 5 ⟨z⟩ ↔ ∃ j : Fin 16, BinaryNormal8T30.N5.normalCertificate.rows j=z := (Fin.addCases (m := 32) (n := 32) (Fin.addCases (m := 16) (n := 16) (by decide +kernel) (by decide +kernel)) (Fin.addCases (m := 16) (n := 16) (by decide +kernel) (by decide +kernel)))
    exact h x.index
  · change member 6 x ↔ x∈Subgroup.closure (Set.range BinaryNormal8T30.N6.normalGenerators)
    rw [binaryNormalRow_mem_iff BinaryNormal8T30.N6.normalCertificate]
    have h : ∀ z : Fin 64, member 6 ⟨z⟩ ↔ ∃ j : Fin 16, BinaryNormal8T30.N6.normalCertificate.rows j=z := (Fin.addCases (m := 32) (n := 32) (Fin.addCases (m := 16) (n := 16) (by decide +kernel) (by decide +kernel)) (Fin.addCases (m := 16) (n := 16) (by decide +kernel) (by decide +kernel)))
    exact h x.index
  · change member 7 x ↔ x∈Subgroup.closure (Set.range BinaryNormal8T30.N7.normalGenerators)
    rw [binaryNormalRow_mem_iff BinaryNormal8T30.N7.normalCertificate]
    have h : ∀ z : Fin 64, member 7 ⟨z⟩ ↔ ∃ j : Fin 8, BinaryNormal8T30.N7.normalCertificate.rows j=z := (Fin.addCases (m := 32) (n := 32) (Fin.addCases (m := 16) (n := 16) (by decide +kernel) (by decide +kernel)) (Fin.addCases (m := 16) (n := 16) (by decide +kernel) (by decide +kernel)))
    exact h x.index
  · change member 8 x ↔ x∈Subgroup.closure (Set.range BinaryNormal8T30.N8.normalGenerators)
    rw [binaryNormalRow_mem_iff BinaryNormal8T30.N8.normalCertificate]
    have h : ∀ z : Fin 64, member 8 ⟨z⟩ ↔ ∃ j : Fin 16, BinaryNormal8T30.N8.normalCertificate.rows j=z := (Fin.addCases (m := 32) (n := 32) (Fin.addCases (m := 16) (n := 16) (by decide +kernel) (by decide +kernel)) (Fin.addCases (m := 16) (n := 16) (by decide +kernel) (by decide +kernel)))
    exact h x.index
  · change member 9 x ↔ x∈Subgroup.closure (Set.range BinaryNormal8T30.N9.normalGenerators)
    rw [binaryNormalRow_mem_iff BinaryNormal8T30.N9.normalCertificate]
    have h : ∀ z : Fin 64, member 9 ⟨z⟩ ↔ ∃ j : Fin 32, BinaryNormal8T30.N9.normalCertificate.rows j=z := (Fin.addCases (m := 32) (n := 32) (Fin.addCases (m := 16) (n := 16) (by decide +kernel) (by decide +kernel)) (Fin.addCases (m := 16) (n := 16) (by decide +kernel) (by decide +kernel)))
    exact h x.index
  · change member 10 x ↔ x∈Subgroup.closure (Set.range BinaryNormal8T30.N10.normalGenerators)
    rw [binaryNormalRow_mem_iff BinaryNormal8T30.N10.normalCertificate]
    have h : ∀ z : Fin 64, member 10 ⟨z⟩ ↔ ∃ j : Fin 32, BinaryNormal8T30.N10.normalCertificate.rows j=z := (Fin.addCases (m := 32) (n := 32) (Fin.addCases (m := 16) (n := 16) (by decide +kernel) (by decide +kernel)) (Fin.addCases (m := 16) (n := 16) (by decide +kernel) (by decide +kernel)))
    exact h x.index
  · change member 11 x ↔ x∈Subgroup.closure (Set.range BinaryNormal8T30.N11.normalGenerators)
    rw [binaryNormalRow_mem_iff BinaryNormal8T30.N11.normalCertificate]
    have h : ∀ z : Fin 64, member 11 ⟨z⟩ ↔ ∃ j : Fin 32, BinaryNormal8T30.N11.normalCertificate.rows j=z := (Fin.addCases (m := 32) (n := 32) (Fin.addCases (m := 16) (n := 16) (by decide +kernel) (by decide +kernel)) (Fin.addCases (m := 16) (n := 16) (by decide +kernel) (by decide +kernel)))
    exact h x.index
  · change member 12 x ↔ x∈Subgroup.closure (Set.range BinaryNormal8T30.N12.normalGenerators)
    rw [binaryNormalRow_mem_iff BinaryNormal8T30.N12.normalCertificate]
    have h : ∀ z : Fin 64, member 12 ⟨z⟩ ↔ ∃ j : Fin 64, BinaryNormal8T30.N12.normalCertificate.rows j=z := (Fin.addCases (m := 32) (n := 32) (Fin.addCases (m := 16) (n := 16) (by decide +kernel) (by decide +kernel)) (Fin.addCases (m := 16) (n := 16) (by decide +kernel) (by decide +kernel)))
    exact h x.index

theorem kernel_eq : top.ker=BinaryNormal8T30.N7.kernel := by
  ext x
  change top x=1 ↔ x∈(BinaryNormal8T30.states 7).kernel
  rw [← member_iff]
  exact (show ∀ x : Source, top x=1 ↔ member 7 x from by decide +kernel) x

namespace N2

theorem intersection_eq : top.ker⊓BinaryNormal8T30.N2.kernel=BinaryNormal8T30.N2.kernel := by
  rw [kernel_eq]
  ext x
  change (x∈(BinaryNormal8T30.states 7).kernel ∧ x∈(BinaryNormal8T30.states 2).kernel) ↔ x∈(BinaryNormal8T30.states 2).kernel
  simp only [← member_iff]
  exact (show ∀ x : Source, (member 7 x ∧ member 2 x) ↔ member 2 x from by decide +kernel) x

theorem cut_le : BinaryNormal8T30.N7.kernel≤top.ker := by
  intro x hx
  have hk : x∈BinaryNormal8T30.N7.kernel := (member_iff 7 x).mp
    ((show ∀ x : Source, member 7 x → member 7 x from by decide +kernel) x ((member_iff 7 x).mpr hx))
  exact kernel_eq.symm ▸ hk

theorem intersection_le : top.ker⊓BinaryNormal8T30.N2.kernel≤BinaryNormal8T30.N7.kernel := by
  intro x hx
  have hx' : x∈BinaryNormal8T30.N2.kernel := intersection_eq ▸ hx
  apply (member_iff 7 x).mp
  exact (show ∀ x : Source, member 2 x → member 7 x from by decide +kernel) x ((member_iff 2 x).mpr hx')

theorem cut_central : ∀ j, ∀ x : BinaryNormal8T30.N7.kernel,
    (x:Source)⁻¹*(generators j*(x:Source)*(generators j)⁻¹)∈BinaryNormal8T30.N2.kernel := by
  have h : ∀ j, ∀ x : Source, member 7 x →
      member 2 (x⁻¹*(generators j*x*(generators j)⁻¹)) := by decide +kernel
  intro j x
  exact (member_iff 2 _).mp (h j x.val ((member_iff 7 x.val).mpr x.property))

theorem fixed_eq : binaryPairFixedSubgroup top.ker BinaryNormal8T30.N7.kernel=BinaryNormal8T30.N7.kernel := by
  rw [kernel_eq]
  ext x
  rw [binaryPairFixedSubgroup_mem_iff _ _ generators BinaryNormal8T30.generators_full]
  change (x∈(BinaryNormal8T30.states 7).kernel ∧ ∀ j,
    x⁻¹*(generators j*x*(generators j)⁻¹)∈(BinaryNormal8T30.states 7).kernel) ↔ x∈(BinaryNormal8T30.states 7).kernel
  simp only [← member_iff]
  exact (show ∀ x : Source, (member 7 x ∧ ∀ j,
    member 7 (x⁻¹*(generators j*x*(generators j)⁻¹))) ↔ member 7 x from by decide +kernel) x

/-- These are the actual selected cut lift generators from this record. -/
def recordedCutGenerators (j : Fin 3) : Source := ⟨((if j.val < 1 then 27 else (if j.val < 2 then 30 else 26)) : Fin 64)⟩
private def cutWords (j : Fin 3) : List (Fin 3) := (if j.val < 1 then ([0] : List (Fin 3)) else (if j.val < 2 then ([1] : List (Fin 3)) else ([0, 1, 2] : List (Fin 3))))
private theorem cutWords_checked : ∀ j,
    ((cutWords j).map recordedCutGenerators).prod=BinaryNormal8T30.N7.normalGenerators j := by decide +kernel

theorem recorded_cut_eq : Subgroup.closure (Set.range recordedCutGenerators)=BinaryNormal8T30.N7.kernel := by
  apply le_antisymm
  · apply (Subgroup.closure_le _).mpr
    rintro _ ⟨j,rfl⟩
    exact (member_iff 7 _).mp
      ((show ∀ j, member 7 (recordedCutGenerators j) from by decide +kernel) j)
  · exact (BinaryNormalGeneratorWords.closure_le
      ({words := cutWords, equations := cutWords_checked} :
        BinaryNormalGeneratorWords BinaryNormal8T30.N7.normalGenerators recordedCutGenerators))

private def kernelPart (j : Fin 3) : Source := ⟨((if j.val < 1 then 27 else (if j.val < 2 then 26 else 27)) : Fin 64)⟩
private def normalPart (j : Fin 3) : Source := ⟨((if j.val < 1 then 63 else (if j.val < 2 then 59 else 59)) : Fin 64)⟩

theorem join_eq : top.ker⊔BinaryNormal8T30.N2.kernel=BinaryNormal8T30.N7.kernel := by
  apply le_antisymm
  · apply sup_le
    · intro x hx
      have hx' : x∈BinaryNormal8T30.N7.kernel := kernel_eq ▸ hx
      exact (member_iff 7 x).mp
        ((show ∀ x : Source, member 7 x → member 7 x from by decide +kernel) x ((member_iff 7 x).mpr hx'))
    · intro x hx
      exact (member_iff 7 x).mp
        ((show ∀ x : Source, member 2 x → member 7 x from by decide +kernel) x ((member_iff 2 x).mpr hx))
  · change Subgroup.closure (Set.range BinaryNormal8T30.N7.normalGenerators)≤_
    apply (Subgroup.closure_le _).mpr
    rintro _ ⟨j,rfl⟩
    have he : ∀ j, kernelPart j*normalPart j=BinaryNormal8T30.N7.normalGenerators j := by decide +kernel
    rw [← he j]
    apply Subgroup.mul_mem
    · apply (show top.ker≤top.ker⊔BinaryNormal8T30.N2.kernel from le_sup_left)
      rw [kernel_eq]
      exact (member_iff 7 _).mp ((show ∀ j, member 7 (kernelPart j) from by decide +kernel) j)
    · apply (show BinaryNormal8T30.N2.kernel≤top.ker⊔BinaryNormal8T30.N2.kernel from le_sup_right)
      exact (member_iff 2 _).mp ((show ∀ j, member 2 (normalPart j) from by decide +kernel) j)

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

private def coverValues (i : Fin 64) : Equiv.Perm (Fin 4) := (if i.val < 32 then (if i.val < 16 then (if i.val < 8 then (if i.val < 4 then (if i.val < 2 then (if i.val < 1 then cover3 else cover3) else (if i.val < 3 then cover2 else cover2)) else (if i.val < 6 then (if i.val < 5 then cover3 else cover3) else (if i.val < 7 then cover2 else cover2))) else (if i.val < 12 then (if i.val < 10 then (if i.val < 9 then cover4 else cover4) else (if i.val < 11 then cover5 else cover5)) else (if i.val < 14 then (if i.val < 13 then cover4 else cover4) else (if i.val < 15 then cover5 else cover5)))) else (if i.val < 24 then (if i.val < 20 then (if i.val < 18 then (if i.val < 17 then cover1 else cover1) else (if i.val < 19 then cover0 else cover0)) else (if i.val < 22 then (if i.val < 21 then cover1 else cover1) else (if i.val < 23 then cover0 else cover0))) else (if i.val < 28 then (if i.val < 26 then (if i.val < 25 then cover6 else cover6) else (if i.val < 27 then cover7 else cover7)) else (if i.val < 30 then (if i.val < 29 then cover6 else cover6) else (if i.val < 31 then cover7 else cover7))))) else (if i.val < 48 then (if i.val < 40 then (if i.val < 36 then (if i.val < 34 then (if i.val < 33 then cover3 else cover3) else (if i.val < 35 then cover2 else cover2)) else (if i.val < 38 then (if i.val < 37 then cover3 else cover3) else (if i.val < 39 then cover2 else cover2))) else (if i.val < 44 then (if i.val < 42 then (if i.val < 41 then cover4 else cover4) else (if i.val < 43 then cover5 else cover5)) else (if i.val < 46 then (if i.val < 45 then cover4 else cover4) else (if i.val < 47 then cover5 else cover5)))) else (if i.val < 56 then (if i.val < 52 then (if i.val < 50 then (if i.val < 49 then cover1 else cover1) else (if i.val < 51 then cover0 else cover0)) else (if i.val < 54 then (if i.val < 53 then cover1 else cover1) else (if i.val < 55 then cover0 else cover0))) else (if i.val < 60 then (if i.val < 58 then (if i.val < 57 then cover6 else cover6) else (if i.val < 59 then cover7 else cover7)) else (if i.val < 62 then (if i.val < 61 then cover6 else cover6) else (if i.val < 63 then cover7 else cover7))))))
private def coverImages (j : Fin 3) : Equiv.Perm (Fin 4) := (if j.val < 1 then cover7 else (if j.val < 2 then cover6 else cover2))
private theorem cover_step : ∀ i j,
    coverValues (BinaryMenuCayley8T30.certificate.next i j)=coverValues i*coverImages j := (Fin.addCases (m := 32) (n := 32) (Fin.addCases (m := 16) (n := 16) (by decide +kernel) (by decide +kernel)) (Fin.addCases (m := 16) (n := 16) (by decide +kernel) (by decide +kernel)))
private theorem cover_identity : coverValues BinaryMenuCayley8T30.certificate.identity=1 := by decide +kernel

def cover : Source →* Equiv.Perm (Fin 4) where
  toFun x := coverValues x.index
  map_one' := cover_identity
  map_mul' x y := by
    change coverValues (BinaryMenuCayley8T30.certificate.walk x.index
      (BinaryMenuCayley8T30.certificate.words y.index))=coverValues x.index*coverValues y.index
    rw [EncodedCayleyCertificate.values_walk _ coverValues coverImages cover_step,
      ← EncodedCayleyCertificate.values_word _ coverValues coverImages cover_step cover_identity]

theorem cover_kernel : cover.ker=top.ker⊔BinaryNormal8T30.N2.kernel := by
  rw [join_eq]
  ext x
  change cover x=1 ↔ x∈(BinaryNormal8T30.states 7).kernel
  rw [← member_iff]
  exact (show ∀ x : Source, cover x=1 ↔ member 7 x from by decide +kernel) x

/-- Every local numerical dimension follows from checked original subgroup
orders and maps; the selected original cut and full fixed preimage remain. -/
def certificate : BinaryPairLocalCertificate generators top BinaryNormal8T30.N2.kernel where
  cut := BinaryNormal8T30.N7.kernel
  cut_normal := inferInstance
  cut_le_kernel := cut_le
  intersection_le_cut := intersection_le
  central := cut_central
  cutDimension := 1
  fixedDimension := 0
  cut_card := by simp only [intersection_eq,BinaryNormal8T30.N7.kernel_card,BinaryNormal8T30.N2.kernel_card] <;> decide
  fixed_card := by simp only [fixed_eq,BinaryNormal8T30.N7.kernel_card,BinaryNormal8T30.N7.kernel_card] <;> decide
  coverDegree := 4
  cover := cover
  cover_kernel := cover_kernel
  width := 8
  gap := by decide

end N2

namespace N3

theorem intersection_eq : top.ker⊓BinaryNormal8T30.N3.kernel=BinaryNormal8T30.N2.kernel := by
  rw [kernel_eq]
  ext x
  change (x∈(BinaryNormal8T30.states 7).kernel ∧ x∈(BinaryNormal8T30.states 3).kernel) ↔ x∈(BinaryNormal8T30.states 2).kernel
  simp only [← member_iff]
  exact (show ∀ x : Source, (member 7 x ∧ member 3 x) ↔ member 2 x from by decide +kernel) x

theorem cut_le : BinaryNormal8T30.N7.kernel≤top.ker := by
  intro x hx
  have hk : x∈BinaryNormal8T30.N7.kernel := (member_iff 7 x).mp
    ((show ∀ x : Source, member 7 x → member 7 x from by decide +kernel) x ((member_iff 7 x).mpr hx))
  exact kernel_eq.symm ▸ hk

theorem intersection_le : top.ker⊓BinaryNormal8T30.N3.kernel≤BinaryNormal8T30.N7.kernel := by
  intro x hx
  have hx' : x∈BinaryNormal8T30.N2.kernel := intersection_eq ▸ hx
  apply (member_iff 7 x).mp
  exact (show ∀ x : Source, member 2 x → member 7 x from by decide +kernel) x ((member_iff 2 x).mpr hx')

theorem cut_central : ∀ j, ∀ x : BinaryNormal8T30.N7.kernel,
    (x:Source)⁻¹*(generators j*(x:Source)*(generators j)⁻¹)∈BinaryNormal8T30.N3.kernel := by
  have h : ∀ j, ∀ x : Source, member 7 x →
      member 3 (x⁻¹*(generators j*x*(generators j)⁻¹)) := by decide +kernel
  intro j x
  exact (member_iff 3 _).mp (h j x.val ((member_iff 7 x.val).mpr x.property))

theorem fixed_eq : binaryPairFixedSubgroup top.ker BinaryNormal8T30.N7.kernel=BinaryNormal8T30.N7.kernel := by
  rw [kernel_eq]
  ext x
  rw [binaryPairFixedSubgroup_mem_iff _ _ generators BinaryNormal8T30.generators_full]
  change (x∈(BinaryNormal8T30.states 7).kernel ∧ ∀ j,
    x⁻¹*(generators j*x*(generators j)⁻¹)∈(BinaryNormal8T30.states 7).kernel) ↔ x∈(BinaryNormal8T30.states 7).kernel
  simp only [← member_iff]
  exact (show ∀ x : Source, (member 7 x ∧ ∀ j,
    member 7 (x⁻¹*(generators j*x*(generators j)⁻¹))) ↔ member 7 x from by decide +kernel) x

/-- These are the actual selected cut lift generators from this record. -/
def recordedCutGenerators (j : Fin 3) : Source := ⟨((if j.val < 1 then 27 else (if j.val < 2 then 30 else 26)) : Fin 64)⟩
private def cutWords (j : Fin 3) : List (Fin 3) := (if j.val < 1 then ([0] : List (Fin 3)) else (if j.val < 2 then ([1] : List (Fin 3)) else ([0, 1, 2] : List (Fin 3))))
private theorem cutWords_checked : ∀ j,
    ((cutWords j).map recordedCutGenerators).prod=BinaryNormal8T30.N7.normalGenerators j := by decide +kernel

theorem recorded_cut_eq : Subgroup.closure (Set.range recordedCutGenerators)=BinaryNormal8T30.N7.kernel := by
  apply le_antisymm
  · apply (Subgroup.closure_le _).mpr
    rintro _ ⟨j,rfl⟩
    exact (member_iff 7 _).mp
      ((show ∀ j, member 7 (recordedCutGenerators j) from by decide +kernel) j)
  · exact (BinaryNormalGeneratorWords.closure_le
      ({words := cutWords, equations := cutWords_checked} :
        BinaryNormalGeneratorWords BinaryNormal8T30.N7.normalGenerators recordedCutGenerators))

private def kernelPart (j : Fin 4) : Source := ⟨((if j.val < 2 then (if j.val < 1 then 27 else 27) else (if j.val < 3 then 26 else 27)) : Fin 64)⟩
private def normalPart (j : Fin 4) : Source := ⟨((if j.val < 2 then (if j.val < 1 then 8 else 63) else (if j.val < 3 then 59 else 59)) : Fin 64)⟩

theorem join_eq : top.ker⊔BinaryNormal8T30.N3.kernel=BinaryNormal8T30.N8.kernel := by
  apply le_antisymm
  · apply sup_le
    · intro x hx
      have hx' : x∈BinaryNormal8T30.N7.kernel := kernel_eq ▸ hx
      exact (member_iff 8 x).mp
        ((show ∀ x : Source, member 7 x → member 8 x from by decide +kernel) x ((member_iff 7 x).mpr hx'))
    · intro x hx
      exact (member_iff 8 x).mp
        ((show ∀ x : Source, member 3 x → member 8 x from by decide +kernel) x ((member_iff 3 x).mpr hx))
  · change Subgroup.closure (Set.range BinaryNormal8T30.N8.normalGenerators)≤_
    apply (Subgroup.closure_le _).mpr
    rintro _ ⟨j,rfl⟩
    have he : ∀ j, kernelPart j*normalPart j=BinaryNormal8T30.N8.normalGenerators j := by decide +kernel
    rw [← he j]
    apply Subgroup.mul_mem
    · apply (show top.ker≤top.ker⊔BinaryNormal8T30.N3.kernel from le_sup_left)
      rw [kernel_eq]
      exact (member_iff 7 _).mp ((show ∀ j, member 7 (kernelPart j) from by decide +kernel) j)
    · apply (show BinaryNormal8T30.N3.kernel≤top.ker⊔BinaryNormal8T30.N3.kernel from le_sup_right)
      exact (member_iff 3 _).mp ((show ∀ j, member 3 (normalPart j) from by decide +kernel) j)

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

private def coverValues (i : Fin 64) : Equiv.Perm (Fin 4) := (if i.val < 32 then (if i.val < 16 then (if i.val < 8 then (if i.val < 4 then (if i.val < 2 then (if i.val < 1 then cover0 else cover0) else (if i.val < 3 then cover2 else cover2)) else (if i.val < 6 then (if i.val < 5 then cover0 else cover0) else (if i.val < 7 then cover2 else cover2))) else (if i.val < 12 then (if i.val < 10 then (if i.val < 9 then cover3 else cover3) else (if i.val < 11 then cover1 else cover1)) else (if i.val < 14 then (if i.val < 13 then cover3 else cover3) else (if i.val < 15 then cover1 else cover1)))) else (if i.val < 24 then (if i.val < 20 then (if i.val < 18 then (if i.val < 17 then cover2 else cover2) else (if i.val < 19 then cover0 else cover0)) else (if i.val < 22 then (if i.val < 21 then cover2 else cover2) else (if i.val < 23 then cover0 else cover0))) else (if i.val < 28 then (if i.val < 26 then (if i.val < 25 then cover1 else cover1) else (if i.val < 27 then cover3 else cover3)) else (if i.val < 30 then (if i.val < 29 then cover1 else cover1) else (if i.val < 31 then cover3 else cover3))))) else (if i.val < 48 then (if i.val < 40 then (if i.val < 36 then (if i.val < 34 then (if i.val < 33 then cover0 else cover0) else (if i.val < 35 then cover2 else cover2)) else (if i.val < 38 then (if i.val < 37 then cover0 else cover0) else (if i.val < 39 then cover2 else cover2))) else (if i.val < 44 then (if i.val < 42 then (if i.val < 41 then cover3 else cover3) else (if i.val < 43 then cover1 else cover1)) else (if i.val < 46 then (if i.val < 45 then cover3 else cover3) else (if i.val < 47 then cover1 else cover1)))) else (if i.val < 56 then (if i.val < 52 then (if i.val < 50 then (if i.val < 49 then cover2 else cover2) else (if i.val < 51 then cover0 else cover0)) else (if i.val < 54 then (if i.val < 53 then cover2 else cover2) else (if i.val < 55 then cover0 else cover0))) else (if i.val < 60 then (if i.val < 58 then (if i.val < 57 then cover1 else cover1) else (if i.val < 59 then cover3 else cover3)) else (if i.val < 62 then (if i.val < 61 then cover1 else cover1) else (if i.val < 63 then cover3 else cover3))))))
private def coverImages (j : Fin 3) : Equiv.Perm (Fin 4) := (if j.val < 1 then cover3 else (if j.val < 2 then cover1 else cover2))
private theorem cover_step : ∀ i j,
    coverValues (BinaryMenuCayley8T30.certificate.next i j)=coverValues i*coverImages j := (Fin.addCases (m := 32) (n := 32) (Fin.addCases (m := 16) (n := 16) (by decide +kernel) (by decide +kernel)) (Fin.addCases (m := 16) (n := 16) (by decide +kernel) (by decide +kernel)))
private theorem cover_identity : coverValues BinaryMenuCayley8T30.certificate.identity=1 := by decide +kernel

def cover : Source →* Equiv.Perm (Fin 4) where
  toFun x := coverValues x.index
  map_one' := cover_identity
  map_mul' x y := by
    change coverValues (BinaryMenuCayley8T30.certificate.walk x.index
      (BinaryMenuCayley8T30.certificate.words y.index))=coverValues x.index*coverValues y.index
    rw [EncodedCayleyCertificate.values_walk _ coverValues coverImages cover_step,
      ← EncodedCayleyCertificate.values_word _ coverValues coverImages cover_step cover_identity]

theorem cover_kernel : cover.ker=top.ker⊔BinaryNormal8T30.N3.kernel := by
  rw [join_eq]
  ext x
  change cover x=1 ↔ x∈(BinaryNormal8T30.states 8).kernel
  rw [← member_iff]
  exact (show ∀ x : Source, cover x=1 ↔ member 8 x from by decide +kernel) x

/-- Every local numerical dimension follows from checked original subgroup
orders and maps; the selected original cut and full fixed preimage remain. -/
def certificate : BinaryPairLocalCertificate generators top BinaryNormal8T30.N3.kernel where
  cut := BinaryNormal8T30.N7.kernel
  cut_normal := inferInstance
  cut_le_kernel := cut_le
  intersection_le_cut := intersection_le
  central := cut_central
  cutDimension := 1
  fixedDimension := 0
  cut_card := by simp only [intersection_eq,BinaryNormal8T30.N7.kernel_card,BinaryNormal8T30.N2.kernel_card] <;> decide
  fixed_card := by simp only [fixed_eq,BinaryNormal8T30.N7.kernel_card,BinaryNormal8T30.N7.kernel_card] <;> decide
  coverDegree := 4
  cover := cover
  cover_kernel := cover_kernel
  width := 8
  gap := by decide

end N3

namespace N4

theorem intersection_eq : top.ker⊓BinaryNormal8T30.N4.kernel=BinaryNormal8T30.N2.kernel := by
  rw [kernel_eq]
  ext x
  change (x∈(BinaryNormal8T30.states 7).kernel ∧ x∈(BinaryNormal8T30.states 4).kernel) ↔ x∈(BinaryNormal8T30.states 2).kernel
  simp only [← member_iff]
  exact (show ∀ x : Source, (member 7 x ∧ member 4 x) ↔ member 2 x from by decide +kernel) x

theorem cut_le : BinaryNormal8T30.N7.kernel≤top.ker := by
  intro x hx
  have hk : x∈BinaryNormal8T30.N7.kernel := (member_iff 7 x).mp
    ((show ∀ x : Source, member 7 x → member 7 x from by decide +kernel) x ((member_iff 7 x).mpr hx))
  exact kernel_eq.symm ▸ hk

theorem intersection_le : top.ker⊓BinaryNormal8T30.N4.kernel≤BinaryNormal8T30.N7.kernel := by
  intro x hx
  have hx' : x∈BinaryNormal8T30.N2.kernel := intersection_eq ▸ hx
  apply (member_iff 7 x).mp
  exact (show ∀ x : Source, member 2 x → member 7 x from by decide +kernel) x ((member_iff 2 x).mpr hx')

theorem cut_central : ∀ j, ∀ x : BinaryNormal8T30.N7.kernel,
    (x:Source)⁻¹*(generators j*(x:Source)*(generators j)⁻¹)∈BinaryNormal8T30.N4.kernel := by
  have h : ∀ j, ∀ x : Source, member 7 x →
      member 4 (x⁻¹*(generators j*x*(generators j)⁻¹)) := by decide +kernel
  intro j x
  exact (member_iff 4 _).mp (h j x.val ((member_iff 7 x.val).mpr x.property))

theorem fixed_eq : binaryPairFixedSubgroup top.ker BinaryNormal8T30.N7.kernel=BinaryNormal8T30.N7.kernel := by
  rw [kernel_eq]
  ext x
  rw [binaryPairFixedSubgroup_mem_iff _ _ generators BinaryNormal8T30.generators_full]
  change (x∈(BinaryNormal8T30.states 7).kernel ∧ ∀ j,
    x⁻¹*(generators j*x*(generators j)⁻¹)∈(BinaryNormal8T30.states 7).kernel) ↔ x∈(BinaryNormal8T30.states 7).kernel
  simp only [← member_iff]
  exact (show ∀ x : Source, (member 7 x ∧ ∀ j,
    member 7 (x⁻¹*(generators j*x*(generators j)⁻¹))) ↔ member 7 x from by decide +kernel) x

/-- These are the actual selected cut lift generators from this record. -/
def recordedCutGenerators (j : Fin 3) : Source := ⟨((if j.val < 1 then 27 else (if j.val < 2 then 30 else 26)) : Fin 64)⟩
private def cutWords (j : Fin 3) : List (Fin 3) := (if j.val < 1 then ([0] : List (Fin 3)) else (if j.val < 2 then ([1] : List (Fin 3)) else ([0, 1, 2] : List (Fin 3))))
private theorem cutWords_checked : ∀ j,
    ((cutWords j).map recordedCutGenerators).prod=BinaryNormal8T30.N7.normalGenerators j := by decide +kernel

theorem recorded_cut_eq : Subgroup.closure (Set.range recordedCutGenerators)=BinaryNormal8T30.N7.kernel := by
  apply le_antisymm
  · apply (Subgroup.closure_le _).mpr
    rintro _ ⟨j,rfl⟩
    exact (member_iff 7 _).mp
      ((show ∀ j, member 7 (recordedCutGenerators j) from by decide +kernel) j)
  · exact (BinaryNormalGeneratorWords.closure_le
      ({words := cutWords, equations := cutWords_checked} :
        BinaryNormalGeneratorWords BinaryNormal8T30.N7.normalGenerators recordedCutGenerators))

private def kernelPart (j : Fin 4) : Source := ⟨((if j.val < 2 then (if j.val < 1 then 26 else 27) else (if j.val < 3 then 26 else 27)) : Fin 64)⟩
private def normalPart (j : Fin 4) : Source := ⟨((if j.val < 2 then (if j.val < 1 then 44 else 63) else (if j.val < 3 then 59 else 59)) : Fin 64)⟩

theorem join_eq : top.ker⊔BinaryNormal8T30.N4.kernel=BinaryNormal8T30.N8.kernel := by
  apply le_antisymm
  · apply sup_le
    · intro x hx
      have hx' : x∈BinaryNormal8T30.N7.kernel := kernel_eq ▸ hx
      exact (member_iff 8 x).mp
        ((show ∀ x : Source, member 7 x → member 8 x from by decide +kernel) x ((member_iff 7 x).mpr hx'))
    · intro x hx
      exact (member_iff 8 x).mp
        ((show ∀ x : Source, member 4 x → member 8 x from by decide +kernel) x ((member_iff 4 x).mpr hx))
  · change Subgroup.closure (Set.range BinaryNormal8T30.N8.normalGenerators)≤_
    apply (Subgroup.closure_le _).mpr
    rintro _ ⟨j,rfl⟩
    have he : ∀ j, kernelPart j*normalPart j=BinaryNormal8T30.N8.normalGenerators j := by decide +kernel
    rw [← he j]
    apply Subgroup.mul_mem
    · apply (show top.ker≤top.ker⊔BinaryNormal8T30.N4.kernel from le_sup_left)
      rw [kernel_eq]
      exact (member_iff 7 _).mp ((show ∀ j, member 7 (kernelPart j) from by decide +kernel) j)
    · apply (show BinaryNormal8T30.N4.kernel≤top.ker⊔BinaryNormal8T30.N4.kernel from le_sup_right)
      exact (member_iff 4 _).mp ((show ∀ j, member 4 (normalPart j) from by decide +kernel) j)

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

private def coverValues (i : Fin 64) : Equiv.Perm (Fin 4) := (if i.val < 32 then (if i.val < 16 then (if i.val < 8 then (if i.val < 4 then (if i.val < 2 then (if i.val < 1 then cover0 else cover0) else (if i.val < 3 then cover2 else cover2)) else (if i.val < 6 then (if i.val < 5 then cover0 else cover0) else (if i.val < 7 then cover2 else cover2))) else (if i.val < 12 then (if i.val < 10 then (if i.val < 9 then cover3 else cover3) else (if i.val < 11 then cover1 else cover1)) else (if i.val < 14 then (if i.val < 13 then cover3 else cover3) else (if i.val < 15 then cover1 else cover1)))) else (if i.val < 24 then (if i.val < 20 then (if i.val < 18 then (if i.val < 17 then cover2 else cover2) else (if i.val < 19 then cover0 else cover0)) else (if i.val < 22 then (if i.val < 21 then cover2 else cover2) else (if i.val < 23 then cover0 else cover0))) else (if i.val < 28 then (if i.val < 26 then (if i.val < 25 then cover1 else cover1) else (if i.val < 27 then cover3 else cover3)) else (if i.val < 30 then (if i.val < 29 then cover1 else cover1) else (if i.val < 31 then cover3 else cover3))))) else (if i.val < 48 then (if i.val < 40 then (if i.val < 36 then (if i.val < 34 then (if i.val < 33 then cover0 else cover0) else (if i.val < 35 then cover2 else cover2)) else (if i.val < 38 then (if i.val < 37 then cover0 else cover0) else (if i.val < 39 then cover2 else cover2))) else (if i.val < 44 then (if i.val < 42 then (if i.val < 41 then cover3 else cover3) else (if i.val < 43 then cover1 else cover1)) else (if i.val < 46 then (if i.val < 45 then cover3 else cover3) else (if i.val < 47 then cover1 else cover1)))) else (if i.val < 56 then (if i.val < 52 then (if i.val < 50 then (if i.val < 49 then cover2 else cover2) else (if i.val < 51 then cover0 else cover0)) else (if i.val < 54 then (if i.val < 53 then cover2 else cover2) else (if i.val < 55 then cover0 else cover0))) else (if i.val < 60 then (if i.val < 58 then (if i.val < 57 then cover1 else cover1) else (if i.val < 59 then cover3 else cover3)) else (if i.val < 62 then (if i.val < 61 then cover1 else cover1) else (if i.val < 63 then cover3 else cover3))))))
private def coverImages (j : Fin 3) : Equiv.Perm (Fin 4) := (if j.val < 1 then cover3 else (if j.val < 2 then cover1 else cover2))
private theorem cover_step : ∀ i j,
    coverValues (BinaryMenuCayley8T30.certificate.next i j)=coverValues i*coverImages j := (Fin.addCases (m := 32) (n := 32) (Fin.addCases (m := 16) (n := 16) (by decide +kernel) (by decide +kernel)) (Fin.addCases (m := 16) (n := 16) (by decide +kernel) (by decide +kernel)))
private theorem cover_identity : coverValues BinaryMenuCayley8T30.certificate.identity=1 := by decide +kernel

def cover : Source →* Equiv.Perm (Fin 4) where
  toFun x := coverValues x.index
  map_one' := cover_identity
  map_mul' x y := by
    change coverValues (BinaryMenuCayley8T30.certificate.walk x.index
      (BinaryMenuCayley8T30.certificate.words y.index))=coverValues x.index*coverValues y.index
    rw [EncodedCayleyCertificate.values_walk _ coverValues coverImages cover_step,
      ← EncodedCayleyCertificate.values_word _ coverValues coverImages cover_step cover_identity]

theorem cover_kernel : cover.ker=top.ker⊔BinaryNormal8T30.N4.kernel := by
  rw [join_eq]
  ext x
  change cover x=1 ↔ x∈(BinaryNormal8T30.states 8).kernel
  rw [← member_iff]
  exact (show ∀ x : Source, cover x=1 ↔ member 8 x from by decide +kernel) x

/-- Every local numerical dimension follows from checked original subgroup
orders and maps; the selected original cut and full fixed preimage remain. -/
def certificate : BinaryPairLocalCertificate generators top BinaryNormal8T30.N4.kernel where
  cut := BinaryNormal8T30.N7.kernel
  cut_normal := inferInstance
  cut_le_kernel := cut_le
  intersection_le_cut := intersection_le
  central := cut_central
  cutDimension := 1
  fixedDimension := 0
  cut_card := by simp only [intersection_eq,BinaryNormal8T30.N7.kernel_card,BinaryNormal8T30.N2.kernel_card] <;> decide
  fixed_card := by simp only [fixed_eq,BinaryNormal8T30.N7.kernel_card,BinaryNormal8T30.N7.kernel_card] <;> decide
  coverDegree := 4
  cover := cover
  cover_kernel := cover_kernel
  width := 8
  gap := by decide

end N4

namespace N5

theorem intersection_eq : top.ker⊓BinaryNormal8T30.N5.kernel=BinaryNormal8T30.N2.kernel := by
  rw [kernel_eq]
  ext x
  change (x∈(BinaryNormal8T30.states 7).kernel ∧ x∈(BinaryNormal8T30.states 5).kernel) ↔ x∈(BinaryNormal8T30.states 2).kernel
  simp only [← member_iff]
  exact (show ∀ x : Source, (member 7 x ∧ member 5 x) ↔ member 2 x from by decide +kernel) x

theorem cut_le : BinaryNormal8T30.N7.kernel≤top.ker := by
  intro x hx
  have hk : x∈BinaryNormal8T30.N7.kernel := (member_iff 7 x).mp
    ((show ∀ x : Source, member 7 x → member 7 x from by decide +kernel) x ((member_iff 7 x).mpr hx))
  exact kernel_eq.symm ▸ hk

theorem intersection_le : top.ker⊓BinaryNormal8T30.N5.kernel≤BinaryNormal8T30.N7.kernel := by
  intro x hx
  have hx' : x∈BinaryNormal8T30.N2.kernel := intersection_eq ▸ hx
  apply (member_iff 7 x).mp
  exact (show ∀ x : Source, member 2 x → member 7 x from by decide +kernel) x ((member_iff 2 x).mpr hx')

theorem cut_central : ∀ j, ∀ x : BinaryNormal8T30.N7.kernel,
    (x:Source)⁻¹*(generators j*(x:Source)*(generators j)⁻¹)∈BinaryNormal8T30.N5.kernel := by
  have h : ∀ j, ∀ x : Source, member 7 x →
      member 5 (x⁻¹*(generators j*x*(generators j)⁻¹)) := by decide +kernel
  intro j x
  exact (member_iff 5 _).mp (h j x.val ((member_iff 7 x.val).mpr x.property))

theorem fixed_eq : binaryPairFixedSubgroup top.ker BinaryNormal8T30.N7.kernel=BinaryNormal8T30.N7.kernel := by
  rw [kernel_eq]
  ext x
  rw [binaryPairFixedSubgroup_mem_iff _ _ generators BinaryNormal8T30.generators_full]
  change (x∈(BinaryNormal8T30.states 7).kernel ∧ ∀ j,
    x⁻¹*(generators j*x*(generators j)⁻¹)∈(BinaryNormal8T30.states 7).kernel) ↔ x∈(BinaryNormal8T30.states 7).kernel
  simp only [← member_iff]
  exact (show ∀ x : Source, (member 7 x ∧ ∀ j,
    member 7 (x⁻¹*(generators j*x*(generators j)⁻¹))) ↔ member 7 x from by decide +kernel) x

/-- These are the actual selected cut lift generators from this record. -/
def recordedCutGenerators (j : Fin 3) : Source := ⟨((if j.val < 1 then 27 else (if j.val < 2 then 30 else 26)) : Fin 64)⟩
private def cutWords (j : Fin 3) : List (Fin 3) := (if j.val < 1 then ([0] : List (Fin 3)) else (if j.val < 2 then ([1] : List (Fin 3)) else ([0, 1, 2] : List (Fin 3))))
private theorem cutWords_checked : ∀ j,
    ((cutWords j).map recordedCutGenerators).prod=BinaryNormal8T30.N7.normalGenerators j := by decide +kernel

theorem recorded_cut_eq : Subgroup.closure (Set.range recordedCutGenerators)=BinaryNormal8T30.N7.kernel := by
  apply le_antisymm
  · apply (Subgroup.closure_le _).mpr
    rintro _ ⟨j,rfl⟩
    exact (member_iff 7 _).mp
      ((show ∀ j, member 7 (recordedCutGenerators j) from by decide +kernel) j)
  · exact (BinaryNormalGeneratorWords.closure_le
      ({words := cutWords, equations := cutWords_checked} :
        BinaryNormalGeneratorWords BinaryNormal8T30.N7.normalGenerators recordedCutGenerators))

private def kernelPart (j : Fin 5) : Source := ⟨((if j.val < 2 then (if j.val < 1 then 27 else 27) else (if j.val < 3 then 26 else (if j.val < 4 then 27 else 26))) : Fin 64)⟩
private def normalPart (j : Fin 5) : Source := ⟨((if j.val < 2 then (if j.val < 1 then 63 else 30) else (if j.val < 3 then 56 else (if j.val < 4 then 59 else 43))) : Fin 64)⟩

theorem join_eq : top.ker⊔BinaryNormal8T30.N5.kernel=BinaryNormal8T30.N11.kernel := by
  apply le_antisymm
  · apply sup_le
    · intro x hx
      have hx' : x∈BinaryNormal8T30.N7.kernel := kernel_eq ▸ hx
      exact (member_iff 11 x).mp
        ((show ∀ x : Source, member 7 x → member 11 x from by decide +kernel) x ((member_iff 7 x).mpr hx'))
    · intro x hx
      exact (member_iff 11 x).mp
        ((show ∀ x : Source, member 5 x → member 11 x from by decide +kernel) x ((member_iff 5 x).mpr hx))
  · change Subgroup.closure (Set.range BinaryNormal8T30.N11.normalGenerators)≤_
    apply (Subgroup.closure_le _).mpr
    rintro _ ⟨j,rfl⟩
    have he : ∀ j, kernelPart j*normalPart j=BinaryNormal8T30.N11.normalGenerators j := by decide +kernel
    rw [← he j]
    apply Subgroup.mul_mem
    · apply (show top.ker≤top.ker⊔BinaryNormal8T30.N5.kernel from le_sup_left)
      rw [kernel_eq]
      exact (member_iff 7 _).mp ((show ∀ j, member 7 (kernelPart j) from by decide +kernel) j)
    · apply (show BinaryNormal8T30.N5.kernel≤top.ker⊔BinaryNormal8T30.N5.kernel from le_sup_right)
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

private def coverValues (i : Fin 64) : Equiv.Perm (Fin 2) := (if i.val < 32 then (if i.val < 16 then (if i.val < 8 then (if i.val < 4 then (if i.val < 2 then (if i.val < 1 then cover0 else cover0) else (if i.val < 3 then cover0 else cover0)) else (if i.val < 6 then (if i.val < 5 then cover0 else cover0) else (if i.val < 7 then cover0 else cover0))) else (if i.val < 12 then (if i.val < 10 then (if i.val < 9 then cover1 else cover1) else (if i.val < 11 then cover1 else cover1)) else (if i.val < 14 then (if i.val < 13 then cover1 else cover1) else (if i.val < 15 then cover1 else cover1)))) else (if i.val < 24 then (if i.val < 20 then (if i.val < 18 then (if i.val < 17 then cover0 else cover0) else (if i.val < 19 then cover0 else cover0)) else (if i.val < 22 then (if i.val < 21 then cover0 else cover0) else (if i.val < 23 then cover0 else cover0))) else (if i.val < 28 then (if i.val < 26 then (if i.val < 25 then cover1 else cover1) else (if i.val < 27 then cover1 else cover1)) else (if i.val < 30 then (if i.val < 29 then cover1 else cover1) else (if i.val < 31 then cover1 else cover1))))) else (if i.val < 48 then (if i.val < 40 then (if i.val < 36 then (if i.val < 34 then (if i.val < 33 then cover0 else cover0) else (if i.val < 35 then cover0 else cover0)) else (if i.val < 38 then (if i.val < 37 then cover0 else cover0) else (if i.val < 39 then cover0 else cover0))) else (if i.val < 44 then (if i.val < 42 then (if i.val < 41 then cover1 else cover1) else (if i.val < 43 then cover1 else cover1)) else (if i.val < 46 then (if i.val < 45 then cover1 else cover1) else (if i.val < 47 then cover1 else cover1)))) else (if i.val < 56 then (if i.val < 52 then (if i.val < 50 then (if i.val < 49 then cover0 else cover0) else (if i.val < 51 then cover0 else cover0)) else (if i.val < 54 then (if i.val < 53 then cover0 else cover0) else (if i.val < 55 then cover0 else cover0))) else (if i.val < 60 then (if i.val < 58 then (if i.val < 57 then cover1 else cover1) else (if i.val < 59 then cover1 else cover1)) else (if i.val < 62 then (if i.val < 61 then cover1 else cover1) else (if i.val < 63 then cover1 else cover1))))))
private def coverImages (j : Fin 3) : Equiv.Perm (Fin 2) := (if j.val < 1 then cover1 else (if j.val < 2 then cover1 else cover0))
private theorem cover_step : ∀ i j,
    coverValues (BinaryMenuCayley8T30.certificate.next i j)=coverValues i*coverImages j := (Fin.addCases (m := 32) (n := 32) (Fin.addCases (m := 16) (n := 16) (by decide +kernel) (by decide +kernel)) (Fin.addCases (m := 16) (n := 16) (by decide +kernel) (by decide +kernel)))
private theorem cover_identity : coverValues BinaryMenuCayley8T30.certificate.identity=1 := by decide +kernel

def cover : Source →* Equiv.Perm (Fin 2) where
  toFun x := coverValues x.index
  map_one' := cover_identity
  map_mul' x y := by
    change coverValues (BinaryMenuCayley8T30.certificate.walk x.index
      (BinaryMenuCayley8T30.certificate.words y.index))=coverValues x.index*coverValues y.index
    rw [EncodedCayleyCertificate.values_walk _ coverValues coverImages cover_step,
      ← EncodedCayleyCertificate.values_word _ coverValues coverImages cover_step cover_identity]

theorem cover_kernel : cover.ker=top.ker⊔BinaryNormal8T30.N5.kernel := by
  rw [join_eq]
  ext x
  change cover x=1 ↔ x∈(BinaryNormal8T30.states 11).kernel
  rw [← member_iff]
  exact (show ∀ x : Source, cover x=1 ↔ member 11 x from by decide +kernel) x

/-- Every local numerical dimension follows from checked original subgroup
orders and maps; the selected original cut and full fixed preimage remain. -/
def certificate : BinaryPairLocalCertificate generators top BinaryNormal8T30.N5.kernel where
  cut := BinaryNormal8T30.N7.kernel
  cut_normal := inferInstance
  cut_le_kernel := cut_le
  intersection_le_cut := intersection_le
  central := cut_central
  cutDimension := 1
  fixedDimension := 0
  cut_card := by simp only [intersection_eq,BinaryNormal8T30.N7.kernel_card,BinaryNormal8T30.N2.kernel_card] <;> decide
  fixed_card := by simp only [fixed_eq,BinaryNormal8T30.N7.kernel_card,BinaryNormal8T30.N7.kernel_card] <;> decide
  coverDegree := 2
  cover := cover
  cover_kernel := cover_kernel
  width := 8
  gap := by decide

end N5

namespace N6

theorem intersection_eq : top.ker⊓BinaryNormal8T30.N6.kernel=BinaryNormal8T30.N2.kernel := by
  rw [kernel_eq]
  ext x
  change (x∈(BinaryNormal8T30.states 7).kernel ∧ x∈(BinaryNormal8T30.states 6).kernel) ↔ x∈(BinaryNormal8T30.states 2).kernel
  simp only [← member_iff]
  exact (show ∀ x : Source, (member 7 x ∧ member 6 x) ↔ member 2 x from by decide +kernel) x

theorem cut_le : BinaryNormal8T30.N7.kernel≤top.ker := by
  intro x hx
  have hk : x∈BinaryNormal8T30.N7.kernel := (member_iff 7 x).mp
    ((show ∀ x : Source, member 7 x → member 7 x from by decide +kernel) x ((member_iff 7 x).mpr hx))
  exact kernel_eq.symm ▸ hk

theorem intersection_le : top.ker⊓BinaryNormal8T30.N6.kernel≤BinaryNormal8T30.N7.kernel := by
  intro x hx
  have hx' : x∈BinaryNormal8T30.N2.kernel := intersection_eq ▸ hx
  apply (member_iff 7 x).mp
  exact (show ∀ x : Source, member 2 x → member 7 x from by decide +kernel) x ((member_iff 2 x).mpr hx')

theorem cut_central : ∀ j, ∀ x : BinaryNormal8T30.N7.kernel,
    (x:Source)⁻¹*(generators j*(x:Source)*(generators j)⁻¹)∈BinaryNormal8T30.N6.kernel := by
  have h : ∀ j, ∀ x : Source, member 7 x →
      member 6 (x⁻¹*(generators j*x*(generators j)⁻¹)) := by decide +kernel
  intro j x
  exact (member_iff 6 _).mp (h j x.val ((member_iff 7 x.val).mpr x.property))

theorem fixed_eq : binaryPairFixedSubgroup top.ker BinaryNormal8T30.N7.kernel=BinaryNormal8T30.N7.kernel := by
  rw [kernel_eq]
  ext x
  rw [binaryPairFixedSubgroup_mem_iff _ _ generators BinaryNormal8T30.generators_full]
  change (x∈(BinaryNormal8T30.states 7).kernel ∧ ∀ j,
    x⁻¹*(generators j*x*(generators j)⁻¹)∈(BinaryNormal8T30.states 7).kernel) ↔ x∈(BinaryNormal8T30.states 7).kernel
  simp only [← member_iff]
  exact (show ∀ x : Source, (member 7 x ∧ ∀ j,
    member 7 (x⁻¹*(generators j*x*(generators j)⁻¹))) ↔ member 7 x from by decide +kernel) x

/-- These are the actual selected cut lift generators from this record. -/
def recordedCutGenerators (j : Fin 3) : Source := ⟨((if j.val < 1 then 27 else (if j.val < 2 then 30 else 26)) : Fin 64)⟩
private def cutWords (j : Fin 3) : List (Fin 3) := (if j.val < 1 then ([0] : List (Fin 3)) else (if j.val < 2 then ([1] : List (Fin 3)) else ([0, 1, 2] : List (Fin 3))))
private theorem cutWords_checked : ∀ j,
    ((cutWords j).map recordedCutGenerators).prod=BinaryNormal8T30.N7.normalGenerators j := by decide +kernel

theorem recorded_cut_eq : Subgroup.closure (Set.range recordedCutGenerators)=BinaryNormal8T30.N7.kernel := by
  apply le_antisymm
  · apply (Subgroup.closure_le _).mpr
    rintro _ ⟨j,rfl⟩
    exact (member_iff 7 _).mp
      ((show ∀ j, member 7 (recordedCutGenerators j) from by decide +kernel) j)
  · exact (BinaryNormalGeneratorWords.closure_le
      ({words := cutWords, equations := cutWords_checked} :
        BinaryNormalGeneratorWords BinaryNormal8T30.N7.normalGenerators recordedCutGenerators))

private def kernelPart (j : Fin 5) : Source := ⟨((if j.val < 2 then (if j.val < 1 then 27 else 27) else (if j.val < 3 then 27 else (if j.val < 4 then 27 else 27))) : Fin 64)⟩
private def normalPart (j : Fin 5) : Source := ⟨((if j.val < 2 then (if j.val < 1 then 63 else 30) else (if j.val < 3 then 61 else (if j.val < 4 then 59 else 11))) : Fin 64)⟩

theorem join_eq : top.ker⊔BinaryNormal8T30.N6.kernel=BinaryNormal8T30.N11.kernel := by
  apply le_antisymm
  · apply sup_le
    · intro x hx
      have hx' : x∈BinaryNormal8T30.N7.kernel := kernel_eq ▸ hx
      exact (member_iff 11 x).mp
        ((show ∀ x : Source, member 7 x → member 11 x from by decide +kernel) x ((member_iff 7 x).mpr hx'))
    · intro x hx
      exact (member_iff 11 x).mp
        ((show ∀ x : Source, member 6 x → member 11 x from by decide +kernel) x ((member_iff 6 x).mpr hx))
  · change Subgroup.closure (Set.range BinaryNormal8T30.N11.normalGenerators)≤_
    apply (Subgroup.closure_le _).mpr
    rintro _ ⟨j,rfl⟩
    have he : ∀ j, kernelPart j*normalPart j=BinaryNormal8T30.N11.normalGenerators j := by decide +kernel
    rw [← he j]
    apply Subgroup.mul_mem
    · apply (show top.ker≤top.ker⊔BinaryNormal8T30.N6.kernel from le_sup_left)
      rw [kernel_eq]
      exact (member_iff 7 _).mp ((show ∀ j, member 7 (kernelPart j) from by decide +kernel) j)
    · apply (show BinaryNormal8T30.N6.kernel≤top.ker⊔BinaryNormal8T30.N6.kernel from le_sup_right)
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

private def coverValues (i : Fin 64) : Equiv.Perm (Fin 2) := (if i.val < 32 then (if i.val < 16 then (if i.val < 8 then (if i.val < 4 then (if i.val < 2 then (if i.val < 1 then cover0 else cover0) else (if i.val < 3 then cover0 else cover0)) else (if i.val < 6 then (if i.val < 5 then cover0 else cover0) else (if i.val < 7 then cover0 else cover0))) else (if i.val < 12 then (if i.val < 10 then (if i.val < 9 then cover1 else cover1) else (if i.val < 11 then cover1 else cover1)) else (if i.val < 14 then (if i.val < 13 then cover1 else cover1) else (if i.val < 15 then cover1 else cover1)))) else (if i.val < 24 then (if i.val < 20 then (if i.val < 18 then (if i.val < 17 then cover0 else cover0) else (if i.val < 19 then cover0 else cover0)) else (if i.val < 22 then (if i.val < 21 then cover0 else cover0) else (if i.val < 23 then cover0 else cover0))) else (if i.val < 28 then (if i.val < 26 then (if i.val < 25 then cover1 else cover1) else (if i.val < 27 then cover1 else cover1)) else (if i.val < 30 then (if i.val < 29 then cover1 else cover1) else (if i.val < 31 then cover1 else cover1))))) else (if i.val < 48 then (if i.val < 40 then (if i.val < 36 then (if i.val < 34 then (if i.val < 33 then cover0 else cover0) else (if i.val < 35 then cover0 else cover0)) else (if i.val < 38 then (if i.val < 37 then cover0 else cover0) else (if i.val < 39 then cover0 else cover0))) else (if i.val < 44 then (if i.val < 42 then (if i.val < 41 then cover1 else cover1) else (if i.val < 43 then cover1 else cover1)) else (if i.val < 46 then (if i.val < 45 then cover1 else cover1) else (if i.val < 47 then cover1 else cover1)))) else (if i.val < 56 then (if i.val < 52 then (if i.val < 50 then (if i.val < 49 then cover0 else cover0) else (if i.val < 51 then cover0 else cover0)) else (if i.val < 54 then (if i.val < 53 then cover0 else cover0) else (if i.val < 55 then cover0 else cover0))) else (if i.val < 60 then (if i.val < 58 then (if i.val < 57 then cover1 else cover1) else (if i.val < 59 then cover1 else cover1)) else (if i.val < 62 then (if i.val < 61 then cover1 else cover1) else (if i.val < 63 then cover1 else cover1))))))
private def coverImages (j : Fin 3) : Equiv.Perm (Fin 2) := (if j.val < 1 then cover1 else (if j.val < 2 then cover1 else cover0))
private theorem cover_step : ∀ i j,
    coverValues (BinaryMenuCayley8T30.certificate.next i j)=coverValues i*coverImages j := (Fin.addCases (m := 32) (n := 32) (Fin.addCases (m := 16) (n := 16) (by decide +kernel) (by decide +kernel)) (Fin.addCases (m := 16) (n := 16) (by decide +kernel) (by decide +kernel)))
private theorem cover_identity : coverValues BinaryMenuCayley8T30.certificate.identity=1 := by decide +kernel

def cover : Source →* Equiv.Perm (Fin 2) where
  toFun x := coverValues x.index
  map_one' := cover_identity
  map_mul' x y := by
    change coverValues (BinaryMenuCayley8T30.certificate.walk x.index
      (BinaryMenuCayley8T30.certificate.words y.index))=coverValues x.index*coverValues y.index
    rw [EncodedCayleyCertificate.values_walk _ coverValues coverImages cover_step,
      ← EncodedCayleyCertificate.values_word _ coverValues coverImages cover_step cover_identity]

theorem cover_kernel : cover.ker=top.ker⊔BinaryNormal8T30.N6.kernel := by
  rw [join_eq]
  ext x
  change cover x=1 ↔ x∈(BinaryNormal8T30.states 11).kernel
  rw [← member_iff]
  exact (show ∀ x : Source, cover x=1 ↔ member 11 x from by decide +kernel) x

/-- Every local numerical dimension follows from checked original subgroup
orders and maps; the selected original cut and full fixed preimage remain. -/
def certificate : BinaryPairLocalCertificate generators top BinaryNormal8T30.N6.kernel where
  cut := BinaryNormal8T30.N7.kernel
  cut_normal := inferInstance
  cut_le_kernel := cut_le
  intersection_le_cut := intersection_le
  central := cut_central
  cutDimension := 1
  fixedDimension := 0
  cut_card := by simp only [intersection_eq,BinaryNormal8T30.N7.kernel_card,BinaryNormal8T30.N2.kernel_card] <;> decide
  fixed_card := by simp only [fixed_eq,BinaryNormal8T30.N7.kernel_card,BinaryNormal8T30.N7.kernel_card] <;> decide
  coverDegree := 2
  cover := cover
  cover_kernel := cover_kernel
  width := 8
  gap := by decide

end N6

namespace N7

theorem intersection_eq : top.ker⊓BinaryNormal8T30.N7.kernel=BinaryNormal8T30.N7.kernel := by
  rw [kernel_eq]
  ext x
  change (x∈(BinaryNormal8T30.states 7).kernel ∧ x∈(BinaryNormal8T30.states 7).kernel) ↔ x∈(BinaryNormal8T30.states 7).kernel
  simp only [← member_iff]
  exact (show ∀ x : Source, (member 7 x ∧ member 7 x) ↔ member 7 x from by decide +kernel) x

theorem cut_le : BinaryNormal8T30.N7.kernel≤top.ker := by
  intro x hx
  have hk : x∈BinaryNormal8T30.N7.kernel := (member_iff 7 x).mp
    ((show ∀ x : Source, member 7 x → member 7 x from by decide +kernel) x ((member_iff 7 x).mpr hx))
  exact kernel_eq.symm ▸ hk

theorem intersection_le : top.ker⊓BinaryNormal8T30.N7.kernel≤BinaryNormal8T30.N7.kernel := by
  intro x hx
  have hx' : x∈BinaryNormal8T30.N7.kernel := intersection_eq ▸ hx
  apply (member_iff 7 x).mp
  exact (show ∀ x : Source, member 7 x → member 7 x from by decide +kernel) x ((member_iff 7 x).mpr hx')

theorem cut_central : ∀ j, ∀ x : BinaryNormal8T30.N7.kernel,
    (x:Source)⁻¹*(generators j*(x:Source)*(generators j)⁻¹)∈BinaryNormal8T30.N7.kernel := by
  have h : ∀ j, ∀ x : Source, member 7 x →
      member 7 (x⁻¹*(generators j*x*(generators j)⁻¹)) := by decide +kernel
  intro j x
  exact (member_iff 7 _).mp (h j x.val ((member_iff 7 x.val).mpr x.property))

theorem fixed_eq : binaryPairFixedSubgroup top.ker BinaryNormal8T30.N7.kernel=BinaryNormal8T30.N7.kernel := by
  rw [kernel_eq]
  ext x
  rw [binaryPairFixedSubgroup_mem_iff _ _ generators BinaryNormal8T30.generators_full]
  change (x∈(BinaryNormal8T30.states 7).kernel ∧ ∀ j,
    x⁻¹*(generators j*x*(generators j)⁻¹)∈(BinaryNormal8T30.states 7).kernel) ↔ x∈(BinaryNormal8T30.states 7).kernel
  simp only [← member_iff]
  exact (show ∀ x : Source, (member 7 x ∧ ∀ j,
    member 7 (x⁻¹*(generators j*x*(generators j)⁻¹))) ↔ member 7 x from by decide +kernel) x

/-- These are the actual selected cut lift generators from this record. -/
def recordedCutGenerators (j : Fin 3) : Source := ⟨((if j.val < 1 then 27 else (if j.val < 2 then 30 else 31)) : Fin 64)⟩
private def cutWords (j : Fin 3) : List (Fin 3) := (if j.val < 1 then ([0] : List (Fin 3)) else (if j.val < 2 then ([1] : List (Fin 3)) else ([2] : List (Fin 3))))
private theorem cutWords_checked : ∀ j,
    ((cutWords j).map recordedCutGenerators).prod=BinaryNormal8T30.N7.normalGenerators j := by decide +kernel

theorem recorded_cut_eq : Subgroup.closure (Set.range recordedCutGenerators)=BinaryNormal8T30.N7.kernel := by
  apply le_antisymm
  · apply (Subgroup.closure_le _).mpr
    rintro _ ⟨j,rfl⟩
    exact (member_iff 7 _).mp
      ((show ∀ j, member 7 (recordedCutGenerators j) from by decide +kernel) j)
  · exact (BinaryNormalGeneratorWords.closure_le
      ({words := cutWords, equations := cutWords_checked} :
        BinaryNormalGeneratorWords BinaryNormal8T30.N7.normalGenerators recordedCutGenerators))

private def kernelPart (j : Fin 3) : Source := ⟨((if j.val < 1 then 26 else (if j.val < 2 then 26 else 26)) : Fin 64)⟩
private def normalPart (j : Fin 3) : Source := ⟨((if j.val < 1 then 62 else (if j.val < 2 then 59 else 58)) : Fin 64)⟩

theorem join_eq : top.ker⊔BinaryNormal8T30.N7.kernel=BinaryNormal8T30.N7.kernel := by
  apply le_antisymm
  · apply sup_le
    · intro x hx
      have hx' : x∈BinaryNormal8T30.N7.kernel := kernel_eq ▸ hx
      exact (member_iff 7 x).mp
        ((show ∀ x : Source, member 7 x → member 7 x from by decide +kernel) x ((member_iff 7 x).mpr hx'))
    · intro x hx
      exact (member_iff 7 x).mp
        ((show ∀ x : Source, member 7 x → member 7 x from by decide +kernel) x ((member_iff 7 x).mpr hx))
  · change Subgroup.closure (Set.range BinaryNormal8T30.N7.normalGenerators)≤_
    apply (Subgroup.closure_le _).mpr
    rintro _ ⟨j,rfl⟩
    have he : ∀ j, kernelPart j*normalPart j=BinaryNormal8T30.N7.normalGenerators j := by decide +kernel
    rw [← he j]
    apply Subgroup.mul_mem
    · apply (show top.ker≤top.ker⊔BinaryNormal8T30.N7.kernel from le_sup_left)
      rw [kernel_eq]
      exact (member_iff 7 _).mp ((show ∀ j, member 7 (kernelPart j) from by decide +kernel) j)
    · apply (show BinaryNormal8T30.N7.kernel≤top.ker⊔BinaryNormal8T30.N7.kernel from le_sup_right)
      exact (member_iff 7 _).mp ((show ∀ j, member 7 (normalPart j) from by decide +kernel) j)

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

private def coverValues (i : Fin 64) : Equiv.Perm (Fin 4) := (if i.val < 32 then (if i.val < 16 then (if i.val < 8 then (if i.val < 4 then (if i.val < 2 then (if i.val < 1 then cover6 else cover6) else (if i.val < 3 then cover2 else cover2)) else (if i.val < 6 then (if i.val < 5 then cover6 else cover6) else (if i.val < 7 then cover2 else cover2))) else (if i.val < 12 then (if i.val < 10 then (if i.val < 9 then cover4 else cover4) else (if i.val < 11 then cover3 else cover3)) else (if i.val < 14 then (if i.val < 13 then cover4 else cover4) else (if i.val < 15 then cover3 else cover3)))) else (if i.val < 24 then (if i.val < 20 then (if i.val < 18 then (if i.val < 17 then cover1 else cover1) else (if i.val < 19 then cover5 else cover5)) else (if i.val < 22 then (if i.val < 21 then cover1 else cover1) else (if i.val < 23 then cover5 else cover5))) else (if i.val < 28 then (if i.val < 26 then (if i.val < 25 then cover0 else cover0) else (if i.val < 27 then cover7 else cover7)) else (if i.val < 30 then (if i.val < 29 then cover0 else cover0) else (if i.val < 31 then cover7 else cover7))))) else (if i.val < 48 then (if i.val < 40 then (if i.val < 36 then (if i.val < 34 then (if i.val < 33 then cover6 else cover6) else (if i.val < 35 then cover2 else cover2)) else (if i.val < 38 then (if i.val < 37 then cover6 else cover6) else (if i.val < 39 then cover2 else cover2))) else (if i.val < 44 then (if i.val < 42 then (if i.val < 41 then cover4 else cover4) else (if i.val < 43 then cover3 else cover3)) else (if i.val < 46 then (if i.val < 45 then cover4 else cover4) else (if i.val < 47 then cover3 else cover3)))) else (if i.val < 56 then (if i.val < 52 then (if i.val < 50 then (if i.val < 49 then cover1 else cover1) else (if i.val < 51 then cover5 else cover5)) else (if i.val < 54 then (if i.val < 53 then cover1 else cover1) else (if i.val < 55 then cover5 else cover5))) else (if i.val < 60 then (if i.val < 58 then (if i.val < 57 then cover0 else cover0) else (if i.val < 59 then cover7 else cover7)) else (if i.val < 62 then (if i.val < 61 then cover0 else cover0) else (if i.val < 63 then cover7 else cover7))))))
private def coverImages (j : Fin 3) : Equiv.Perm (Fin 4) := (if j.val < 1 then cover7 else (if j.val < 2 then cover0 else cover2))
private theorem cover_step : ∀ i j,
    coverValues (BinaryMenuCayley8T30.certificate.next i j)=coverValues i*coverImages j := (Fin.addCases (m := 32) (n := 32) (Fin.addCases (m := 16) (n := 16) (by decide +kernel) (by decide +kernel)) (Fin.addCases (m := 16) (n := 16) (by decide +kernel) (by decide +kernel)))
private theorem cover_identity : coverValues BinaryMenuCayley8T30.certificate.identity=1 := by decide +kernel

def cover : Source →* Equiv.Perm (Fin 4) where
  toFun x := coverValues x.index
  map_one' := cover_identity
  map_mul' x y := by
    change coverValues (BinaryMenuCayley8T30.certificate.walk x.index
      (BinaryMenuCayley8T30.certificate.words y.index))=coverValues x.index*coverValues y.index
    rw [EncodedCayleyCertificate.values_walk _ coverValues coverImages cover_step,
      ← EncodedCayleyCertificate.values_word _ coverValues coverImages cover_step cover_identity]

theorem cover_kernel : cover.ker=top.ker⊔BinaryNormal8T30.N7.kernel := by
  rw [join_eq]
  ext x
  change cover x=1 ↔ x∈(BinaryNormal8T30.states 7).kernel
  rw [← member_iff]
  exact (show ∀ x : Source, cover x=1 ↔ member 7 x from by decide +kernel) x

/-- Every local numerical dimension follows from checked original subgroup
orders and maps; the selected original cut and full fixed preimage remain. -/
def certificate : BinaryPairLocalCertificate generators top BinaryNormal8T30.N7.kernel where
  cut := BinaryNormal8T30.N7.kernel
  cut_normal := inferInstance
  cut_le_kernel := cut_le
  intersection_le_cut := intersection_le
  central := cut_central
  cutDimension := 0
  fixedDimension := 0
  cut_card := by simp only [intersection_eq,BinaryNormal8T30.N7.kernel_card,BinaryNormal8T30.N7.kernel_card] <;> decide
  fixed_card := by simp only [fixed_eq,BinaryNormal8T30.N7.kernel_card,BinaryNormal8T30.N7.kernel_card] <;> decide
  coverDegree := 4
  cover := cover
  cover_kernel := cover_kernel
  width := 8
  gap := by decide

end N7

namespace N8

theorem intersection_eq : top.ker⊓BinaryNormal8T30.N8.kernel=BinaryNormal8T30.N7.kernel := by
  rw [kernel_eq]
  ext x
  change (x∈(BinaryNormal8T30.states 7).kernel ∧ x∈(BinaryNormal8T30.states 8).kernel) ↔ x∈(BinaryNormal8T30.states 7).kernel
  simp only [← member_iff]
  exact (show ∀ x : Source, (member 7 x ∧ member 8 x) ↔ member 7 x from by decide +kernel) x

theorem cut_le : BinaryNormal8T30.N7.kernel≤top.ker := by
  intro x hx
  have hk : x∈BinaryNormal8T30.N7.kernel := (member_iff 7 x).mp
    ((show ∀ x : Source, member 7 x → member 7 x from by decide +kernel) x ((member_iff 7 x).mpr hx))
  exact kernel_eq.symm ▸ hk

theorem intersection_le : top.ker⊓BinaryNormal8T30.N8.kernel≤BinaryNormal8T30.N7.kernel := by
  intro x hx
  have hx' : x∈BinaryNormal8T30.N7.kernel := intersection_eq ▸ hx
  apply (member_iff 7 x).mp
  exact (show ∀ x : Source, member 7 x → member 7 x from by decide +kernel) x ((member_iff 7 x).mpr hx')

theorem cut_central : ∀ j, ∀ x : BinaryNormal8T30.N7.kernel,
    (x:Source)⁻¹*(generators j*(x:Source)*(generators j)⁻¹)∈BinaryNormal8T30.N8.kernel := by
  have h : ∀ j, ∀ x : Source, member 7 x →
      member 8 (x⁻¹*(generators j*x*(generators j)⁻¹)) := by decide +kernel
  intro j x
  exact (member_iff 8 _).mp (h j x.val ((member_iff 7 x.val).mpr x.property))

theorem fixed_eq : binaryPairFixedSubgroup top.ker BinaryNormal8T30.N7.kernel=BinaryNormal8T30.N7.kernel := by
  rw [kernel_eq]
  ext x
  rw [binaryPairFixedSubgroup_mem_iff _ _ generators BinaryNormal8T30.generators_full]
  change (x∈(BinaryNormal8T30.states 7).kernel ∧ ∀ j,
    x⁻¹*(generators j*x*(generators j)⁻¹)∈(BinaryNormal8T30.states 7).kernel) ↔ x∈(BinaryNormal8T30.states 7).kernel
  simp only [← member_iff]
  exact (show ∀ x : Source, (member 7 x ∧ ∀ j,
    member 7 (x⁻¹*(generators j*x*(generators j)⁻¹))) ↔ member 7 x from by decide +kernel) x

/-- These are the actual selected cut lift generators from this record. -/
def recordedCutGenerators (j : Fin 3) : Source := ⟨((if j.val < 1 then 27 else (if j.val < 2 then 30 else 31)) : Fin 64)⟩
private def cutWords (j : Fin 3) : List (Fin 3) := (if j.val < 1 then ([0] : List (Fin 3)) else (if j.val < 2 then ([1] : List (Fin 3)) else ([2] : List (Fin 3))))
private theorem cutWords_checked : ∀ j,
    ((cutWords j).map recordedCutGenerators).prod=BinaryNormal8T30.N7.normalGenerators j := by decide +kernel

theorem recorded_cut_eq : Subgroup.closure (Set.range recordedCutGenerators)=BinaryNormal8T30.N7.kernel := by
  apply le_antisymm
  · apply (Subgroup.closure_le _).mpr
    rintro _ ⟨j,rfl⟩
    exact (member_iff 7 _).mp
      ((show ∀ j, member 7 (recordedCutGenerators j) from by decide +kernel) j)
  · exact (BinaryNormalGeneratorWords.closure_le
      ({words := cutWords, equations := cutWords_checked} :
        BinaryNormalGeneratorWords BinaryNormal8T30.N7.normalGenerators recordedCutGenerators))

private def kernelPart (j : Fin 4) : Source := ⟨((if j.val < 2 then (if j.val < 1 then 26 else 26) else (if j.val < 3 then 26 else 26)) : Fin 64)⟩
private def normalPart (j : Fin 4) : Source := ⟨((if j.val < 2 then (if j.val < 1 then 44 else 62) else (if j.val < 3 then 59 else 58)) : Fin 64)⟩

theorem join_eq : top.ker⊔BinaryNormal8T30.N8.kernel=BinaryNormal8T30.N8.kernel := by
  apply le_antisymm
  · apply sup_le
    · intro x hx
      have hx' : x∈BinaryNormal8T30.N7.kernel := kernel_eq ▸ hx
      exact (member_iff 8 x).mp
        ((show ∀ x : Source, member 7 x → member 8 x from by decide +kernel) x ((member_iff 7 x).mpr hx'))
    · intro x hx
      exact (member_iff 8 x).mp
        ((show ∀ x : Source, member 8 x → member 8 x from by decide +kernel) x ((member_iff 8 x).mpr hx))
  · change Subgroup.closure (Set.range BinaryNormal8T30.N8.normalGenerators)≤_
    apply (Subgroup.closure_le _).mpr
    rintro _ ⟨j,rfl⟩
    have he : ∀ j, kernelPart j*normalPart j=BinaryNormal8T30.N8.normalGenerators j := by decide +kernel
    rw [← he j]
    apply Subgroup.mul_mem
    · apply (show top.ker≤top.ker⊔BinaryNormal8T30.N8.kernel from le_sup_left)
      rw [kernel_eq]
      exact (member_iff 7 _).mp ((show ∀ j, member 7 (kernelPart j) from by decide +kernel) j)
    · apply (show BinaryNormal8T30.N8.kernel≤top.ker⊔BinaryNormal8T30.N8.kernel from le_sup_right)
      exact (member_iff 8 _).mp ((show ∀ j, member 8 (normalPart j) from by decide +kernel) j)

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

private def coverValues (i : Fin 64) : Equiv.Perm (Fin 4) := (if i.val < 32 then (if i.val < 16 then (if i.val < 8 then (if i.val < 4 then (if i.val < 2 then (if i.val < 1 then cover0 else cover0) else (if i.val < 3 then cover2 else cover2)) else (if i.val < 6 then (if i.val < 5 then cover0 else cover0) else (if i.val < 7 then cover2 else cover2))) else (if i.val < 12 then (if i.val < 10 then (if i.val < 9 then cover3 else cover3) else (if i.val < 11 then cover1 else cover1)) else (if i.val < 14 then (if i.val < 13 then cover3 else cover3) else (if i.val < 15 then cover1 else cover1)))) else (if i.val < 24 then (if i.val < 20 then (if i.val < 18 then (if i.val < 17 then cover2 else cover2) else (if i.val < 19 then cover0 else cover0)) else (if i.val < 22 then (if i.val < 21 then cover2 else cover2) else (if i.val < 23 then cover0 else cover0))) else (if i.val < 28 then (if i.val < 26 then (if i.val < 25 then cover1 else cover1) else (if i.val < 27 then cover3 else cover3)) else (if i.val < 30 then (if i.val < 29 then cover1 else cover1) else (if i.val < 31 then cover3 else cover3))))) else (if i.val < 48 then (if i.val < 40 then (if i.val < 36 then (if i.val < 34 then (if i.val < 33 then cover0 else cover0) else (if i.val < 35 then cover2 else cover2)) else (if i.val < 38 then (if i.val < 37 then cover0 else cover0) else (if i.val < 39 then cover2 else cover2))) else (if i.val < 44 then (if i.val < 42 then (if i.val < 41 then cover3 else cover3) else (if i.val < 43 then cover1 else cover1)) else (if i.val < 46 then (if i.val < 45 then cover3 else cover3) else (if i.val < 47 then cover1 else cover1)))) else (if i.val < 56 then (if i.val < 52 then (if i.val < 50 then (if i.val < 49 then cover2 else cover2) else (if i.val < 51 then cover0 else cover0)) else (if i.val < 54 then (if i.val < 53 then cover2 else cover2) else (if i.val < 55 then cover0 else cover0))) else (if i.val < 60 then (if i.val < 58 then (if i.val < 57 then cover1 else cover1) else (if i.val < 59 then cover3 else cover3)) else (if i.val < 62 then (if i.val < 61 then cover1 else cover1) else (if i.val < 63 then cover3 else cover3))))))
private def coverImages (j : Fin 3) : Equiv.Perm (Fin 4) := (if j.val < 1 then cover3 else (if j.val < 2 then cover1 else cover2))
private theorem cover_step : ∀ i j,
    coverValues (BinaryMenuCayley8T30.certificate.next i j)=coverValues i*coverImages j := (Fin.addCases (m := 32) (n := 32) (Fin.addCases (m := 16) (n := 16) (by decide +kernel) (by decide +kernel)) (Fin.addCases (m := 16) (n := 16) (by decide +kernel) (by decide +kernel)))
private theorem cover_identity : coverValues BinaryMenuCayley8T30.certificate.identity=1 := by decide +kernel

def cover : Source →* Equiv.Perm (Fin 4) where
  toFun x := coverValues x.index
  map_one' := cover_identity
  map_mul' x y := by
    change coverValues (BinaryMenuCayley8T30.certificate.walk x.index
      (BinaryMenuCayley8T30.certificate.words y.index))=coverValues x.index*coverValues y.index
    rw [EncodedCayleyCertificate.values_walk _ coverValues coverImages cover_step,
      ← EncodedCayleyCertificate.values_word _ coverValues coverImages cover_step cover_identity]

theorem cover_kernel : cover.ker=top.ker⊔BinaryNormal8T30.N8.kernel := by
  rw [join_eq]
  ext x
  change cover x=1 ↔ x∈(BinaryNormal8T30.states 8).kernel
  rw [← member_iff]
  exact (show ∀ x : Source, cover x=1 ↔ member 8 x from by decide +kernel) x

/-- Every local numerical dimension follows from checked original subgroup
orders and maps; the selected original cut and full fixed preimage remain. -/
def certificate : BinaryPairLocalCertificate generators top BinaryNormal8T30.N8.kernel where
  cut := BinaryNormal8T30.N7.kernel
  cut_normal := inferInstance
  cut_le_kernel := cut_le
  intersection_le_cut := intersection_le
  central := cut_central
  cutDimension := 0
  fixedDimension := 0
  cut_card := by simp only [intersection_eq,BinaryNormal8T30.N7.kernel_card,BinaryNormal8T30.N7.kernel_card] <;> decide
  fixed_card := by simp only [fixed_eq,BinaryNormal8T30.N7.kernel_card,BinaryNormal8T30.N7.kernel_card] <;> decide
  coverDegree := 4
  cover := cover
  cover_kernel := cover_kernel
  width := 8
  gap := by decide

end N8

namespace N9

theorem intersection_eq : top.ker⊓BinaryNormal8T30.N9.kernel=BinaryNormal8T30.N7.kernel := by
  rw [kernel_eq]
  ext x
  change (x∈(BinaryNormal8T30.states 7).kernel ∧ x∈(BinaryNormal8T30.states 9).kernel) ↔ x∈(BinaryNormal8T30.states 7).kernel
  simp only [← member_iff]
  exact (show ∀ x : Source, (member 7 x ∧ member 9 x) ↔ member 7 x from by decide +kernel) x

theorem cut_le : BinaryNormal8T30.N7.kernel≤top.ker := by
  intro x hx
  have hk : x∈BinaryNormal8T30.N7.kernel := (member_iff 7 x).mp
    ((show ∀ x : Source, member 7 x → member 7 x from by decide +kernel) x ((member_iff 7 x).mpr hx))
  exact kernel_eq.symm ▸ hk

theorem intersection_le : top.ker⊓BinaryNormal8T30.N9.kernel≤BinaryNormal8T30.N7.kernel := by
  intro x hx
  have hx' : x∈BinaryNormal8T30.N7.kernel := intersection_eq ▸ hx
  apply (member_iff 7 x).mp
  exact (show ∀ x : Source, member 7 x → member 7 x from by decide +kernel) x ((member_iff 7 x).mpr hx')

theorem cut_central : ∀ j, ∀ x : BinaryNormal8T30.N7.kernel,
    (x:Source)⁻¹*(generators j*(x:Source)*(generators j)⁻¹)∈BinaryNormal8T30.N9.kernel := by
  have h : ∀ j, ∀ x : Source, member 7 x →
      member 9 (x⁻¹*(generators j*x*(generators j)⁻¹)) := by decide +kernel
  intro j x
  exact (member_iff 9 _).mp (h j x.val ((member_iff 7 x.val).mpr x.property))

theorem fixed_eq : binaryPairFixedSubgroup top.ker BinaryNormal8T30.N7.kernel=BinaryNormal8T30.N7.kernel := by
  rw [kernel_eq]
  ext x
  rw [binaryPairFixedSubgroup_mem_iff _ _ generators BinaryNormal8T30.generators_full]
  change (x∈(BinaryNormal8T30.states 7).kernel ∧ ∀ j,
    x⁻¹*(generators j*x*(generators j)⁻¹)∈(BinaryNormal8T30.states 7).kernel) ↔ x∈(BinaryNormal8T30.states 7).kernel
  simp only [← member_iff]
  exact (show ∀ x : Source, (member 7 x ∧ ∀ j,
    member 7 (x⁻¹*(generators j*x*(generators j)⁻¹))) ↔ member 7 x from by decide +kernel) x

/-- These are the actual selected cut lift generators from this record. -/
def recordedCutGenerators (j : Fin 3) : Source := ⟨((if j.val < 1 then 27 else (if j.val < 2 then 30 else 31)) : Fin 64)⟩
private def cutWords (j : Fin 3) : List (Fin 3) := (if j.val < 1 then ([0] : List (Fin 3)) else (if j.val < 2 then ([1] : List (Fin 3)) else ([2] : List (Fin 3))))
private theorem cutWords_checked : ∀ j,
    ((cutWords j).map recordedCutGenerators).prod=BinaryNormal8T30.N7.normalGenerators j := by decide +kernel

theorem recorded_cut_eq : Subgroup.closure (Set.range recordedCutGenerators)=BinaryNormal8T30.N7.kernel := by
  apply le_antisymm
  · apply (Subgroup.closure_le _).mpr
    rintro _ ⟨j,rfl⟩
    exact (member_iff 7 _).mp
      ((show ∀ j, member 7 (recordedCutGenerators j) from by decide +kernel) j)
  · exact (BinaryNormalGeneratorWords.closure_le
      ({words := cutWords, equations := cutWords_checked} :
        BinaryNormalGeneratorWords BinaryNormal8T30.N7.normalGenerators recordedCutGenerators))

private def kernelPart (j : Fin 4) : Source := ⟨((if j.val < 2 then (if j.val < 1 then 26 else 26) else (if j.val < 3 then 26 else 26)) : Fin 64)⟩
private def normalPart (j : Fin 4) : Source := ⟨((if j.val < 2 then (if j.val < 1 then 44 else 32) else (if j.val < 3 then 62 else 59)) : Fin 64)⟩

theorem join_eq : top.ker⊔BinaryNormal8T30.N9.kernel=BinaryNormal8T30.N9.kernel := by
  apply le_antisymm
  · apply sup_le
    · intro x hx
      have hx' : x∈BinaryNormal8T30.N7.kernel := kernel_eq ▸ hx
      exact (member_iff 9 x).mp
        ((show ∀ x : Source, member 7 x → member 9 x from by decide +kernel) x ((member_iff 7 x).mpr hx'))
    · intro x hx
      exact (member_iff 9 x).mp
        ((show ∀ x : Source, member 9 x → member 9 x from by decide +kernel) x ((member_iff 9 x).mpr hx))
  · change Subgroup.closure (Set.range BinaryNormal8T30.N9.normalGenerators)≤_
    apply (Subgroup.closure_le _).mpr
    rintro _ ⟨j,rfl⟩
    have he : ∀ j, kernelPart j*normalPart j=BinaryNormal8T30.N9.normalGenerators j := by decide +kernel
    rw [← he j]
    apply Subgroup.mul_mem
    · apply (show top.ker≤top.ker⊔BinaryNormal8T30.N9.kernel from le_sup_left)
      rw [kernel_eq]
      exact (member_iff 7 _).mp ((show ∀ j, member 7 (kernelPart j) from by decide +kernel) j)
    · apply (show BinaryNormal8T30.N9.kernel≤top.ker⊔BinaryNormal8T30.N9.kernel from le_sup_right)
      exact (member_iff 9 _).mp ((show ∀ j, member 9 (normalPart j) from by decide +kernel) j)

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

private def coverValues (i : Fin 64) : Equiv.Perm (Fin 2) := (if i.val < 32 then (if i.val < 16 then (if i.val < 8 then (if i.val < 4 then (if i.val < 2 then (if i.val < 1 then cover1 else cover1) else (if i.val < 3 then cover0 else cover0)) else (if i.val < 6 then (if i.val < 5 then cover1 else cover1) else (if i.val < 7 then cover0 else cover0))) else (if i.val < 12 then (if i.val < 10 then (if i.val < 9 then cover1 else cover1) else (if i.val < 11 then cover0 else cover0)) else (if i.val < 14 then (if i.val < 13 then cover1 else cover1) else (if i.val < 15 then cover0 else cover0)))) else (if i.val < 24 then (if i.val < 20 then (if i.val < 18 then (if i.val < 17 then cover0 else cover0) else (if i.val < 19 then cover1 else cover1)) else (if i.val < 22 then (if i.val < 21 then cover0 else cover0) else (if i.val < 23 then cover1 else cover1))) else (if i.val < 28 then (if i.val < 26 then (if i.val < 25 then cover0 else cover0) else (if i.val < 27 then cover1 else cover1)) else (if i.val < 30 then (if i.val < 29 then cover0 else cover0) else (if i.val < 31 then cover1 else cover1))))) else (if i.val < 48 then (if i.val < 40 then (if i.val < 36 then (if i.val < 34 then (if i.val < 33 then cover1 else cover1) else (if i.val < 35 then cover0 else cover0)) else (if i.val < 38 then (if i.val < 37 then cover1 else cover1) else (if i.val < 39 then cover0 else cover0))) else (if i.val < 44 then (if i.val < 42 then (if i.val < 41 then cover1 else cover1) else (if i.val < 43 then cover0 else cover0)) else (if i.val < 46 then (if i.val < 45 then cover1 else cover1) else (if i.val < 47 then cover0 else cover0)))) else (if i.val < 56 then (if i.val < 52 then (if i.val < 50 then (if i.val < 49 then cover0 else cover0) else (if i.val < 51 then cover1 else cover1)) else (if i.val < 54 then (if i.val < 53 then cover0 else cover0) else (if i.val < 55 then cover1 else cover1))) else (if i.val < 60 then (if i.val < 58 then (if i.val < 57 then cover0 else cover0) else (if i.val < 59 then cover1 else cover1)) else (if i.val < 62 then (if i.val < 61 then cover0 else cover0) else (if i.val < 63 then cover1 else cover1))))))
private def coverImages (j : Fin 3) : Equiv.Perm (Fin 2) := (if j.val < 1 then cover1 else (if j.val < 2 then cover0 else cover0))
private theorem cover_step : ∀ i j,
    coverValues (BinaryMenuCayley8T30.certificate.next i j)=coverValues i*coverImages j := (Fin.addCases (m := 32) (n := 32) (Fin.addCases (m := 16) (n := 16) (by decide +kernel) (by decide +kernel)) (Fin.addCases (m := 16) (n := 16) (by decide +kernel) (by decide +kernel)))
private theorem cover_identity : coverValues BinaryMenuCayley8T30.certificate.identity=1 := by decide +kernel

def cover : Source →* Equiv.Perm (Fin 2) where
  toFun x := coverValues x.index
  map_one' := cover_identity
  map_mul' x y := by
    change coverValues (BinaryMenuCayley8T30.certificate.walk x.index
      (BinaryMenuCayley8T30.certificate.words y.index))=coverValues x.index*coverValues y.index
    rw [EncodedCayleyCertificate.values_walk _ coverValues coverImages cover_step,
      ← EncodedCayleyCertificate.values_word _ coverValues coverImages cover_step cover_identity]

theorem cover_kernel : cover.ker=top.ker⊔BinaryNormal8T30.N9.kernel := by
  rw [join_eq]
  ext x
  change cover x=1 ↔ x∈(BinaryNormal8T30.states 9).kernel
  rw [← member_iff]
  exact (show ∀ x : Source, cover x=1 ↔ member 9 x from by decide +kernel) x

/-- Every local numerical dimension follows from checked original subgroup
orders and maps; the selected original cut and full fixed preimage remain. -/
def certificate : BinaryPairLocalCertificate generators top BinaryNormal8T30.N9.kernel where
  cut := BinaryNormal8T30.N7.kernel
  cut_normal := inferInstance
  cut_le_kernel := cut_le
  intersection_le_cut := intersection_le
  central := cut_central
  cutDimension := 0
  fixedDimension := 0
  cut_card := by simp only [intersection_eq,BinaryNormal8T30.N7.kernel_card,BinaryNormal8T30.N7.kernel_card] <;> decide
  fixed_card := by simp only [fixed_eq,BinaryNormal8T30.N7.kernel_card,BinaryNormal8T30.N7.kernel_card] <;> decide
  coverDegree := 2
  cover := cover
  cover_kernel := cover_kernel
  width := 8
  gap := by decide

end N9

namespace N10

theorem intersection_eq : top.ker⊓BinaryNormal8T30.N10.kernel=BinaryNormal8T30.N7.kernel := by
  rw [kernel_eq]
  ext x
  change (x∈(BinaryNormal8T30.states 7).kernel ∧ x∈(BinaryNormal8T30.states 10).kernel) ↔ x∈(BinaryNormal8T30.states 7).kernel
  simp only [← member_iff]
  exact (show ∀ x : Source, (member 7 x ∧ member 10 x) ↔ member 7 x from by decide +kernel) x

theorem cut_le : BinaryNormal8T30.N7.kernel≤top.ker := by
  intro x hx
  have hk : x∈BinaryNormal8T30.N7.kernel := (member_iff 7 x).mp
    ((show ∀ x : Source, member 7 x → member 7 x from by decide +kernel) x ((member_iff 7 x).mpr hx))
  exact kernel_eq.symm ▸ hk

theorem intersection_le : top.ker⊓BinaryNormal8T30.N10.kernel≤BinaryNormal8T30.N7.kernel := by
  intro x hx
  have hx' : x∈BinaryNormal8T30.N7.kernel := intersection_eq ▸ hx
  apply (member_iff 7 x).mp
  exact (show ∀ x : Source, member 7 x → member 7 x from by decide +kernel) x ((member_iff 7 x).mpr hx')

theorem cut_central : ∀ j, ∀ x : BinaryNormal8T30.N7.kernel,
    (x:Source)⁻¹*(generators j*(x:Source)*(generators j)⁻¹)∈BinaryNormal8T30.N10.kernel := by
  have h : ∀ j, ∀ x : Source, member 7 x →
      member 10 (x⁻¹*(generators j*x*(generators j)⁻¹)) := by decide +kernel
  intro j x
  exact (member_iff 10 _).mp (h j x.val ((member_iff 7 x.val).mpr x.property))

theorem fixed_eq : binaryPairFixedSubgroup top.ker BinaryNormal8T30.N7.kernel=BinaryNormal8T30.N7.kernel := by
  rw [kernel_eq]
  ext x
  rw [binaryPairFixedSubgroup_mem_iff _ _ generators BinaryNormal8T30.generators_full]
  change (x∈(BinaryNormal8T30.states 7).kernel ∧ ∀ j,
    x⁻¹*(generators j*x*(generators j)⁻¹)∈(BinaryNormal8T30.states 7).kernel) ↔ x∈(BinaryNormal8T30.states 7).kernel
  simp only [← member_iff]
  exact (show ∀ x : Source, (member 7 x ∧ ∀ j,
    member 7 (x⁻¹*(generators j*x*(generators j)⁻¹))) ↔ member 7 x from by decide +kernel) x

/-- These are the actual selected cut lift generators from this record. -/
def recordedCutGenerators (j : Fin 3) : Source := ⟨((if j.val < 1 then 27 else (if j.val < 2 then 30 else 31)) : Fin 64)⟩
private def cutWords (j : Fin 3) : List (Fin 3) := (if j.val < 1 then ([0] : List (Fin 3)) else (if j.val < 2 then ([1] : List (Fin 3)) else ([2] : List (Fin 3))))
private theorem cutWords_checked : ∀ j,
    ((cutWords j).map recordedCutGenerators).prod=BinaryNormal8T30.N7.normalGenerators j := by decide +kernel

theorem recorded_cut_eq : Subgroup.closure (Set.range recordedCutGenerators)=BinaryNormal8T30.N7.kernel := by
  apply le_antisymm
  · apply (Subgroup.closure_le _).mpr
    rintro _ ⟨j,rfl⟩
    exact (member_iff 7 _).mp
      ((show ∀ j, member 7 (recordedCutGenerators j) from by decide +kernel) j)
  · exact (BinaryNormalGeneratorWords.closure_le
      ({words := cutWords, equations := cutWords_checked} :
        BinaryNormalGeneratorWords BinaryNormal8T30.N7.normalGenerators recordedCutGenerators))

private def kernelPart (j : Fin 2) : Source := ⟨((if j.val < 1 then 26 else 26) : Fin 64)⟩
private def normalPart (j : Fin 2) : Source := ⟨((if j.val < 1 then 62 else 38) : Fin 64)⟩

theorem join_eq : top.ker⊔BinaryNormal8T30.N10.kernel=BinaryNormal8T30.N10.kernel := by
  apply le_antisymm
  · apply sup_le
    · intro x hx
      have hx' : x∈BinaryNormal8T30.N7.kernel := kernel_eq ▸ hx
      exact (member_iff 10 x).mp
        ((show ∀ x : Source, member 7 x → member 10 x from by decide +kernel) x ((member_iff 7 x).mpr hx'))
    · intro x hx
      exact (member_iff 10 x).mp
        ((show ∀ x : Source, member 10 x → member 10 x from by decide +kernel) x ((member_iff 10 x).mpr hx))
  · change Subgroup.closure (Set.range BinaryNormal8T30.N10.normalGenerators)≤_
    apply (Subgroup.closure_le _).mpr
    rintro _ ⟨j,rfl⟩
    have he : ∀ j, kernelPart j*normalPart j=BinaryNormal8T30.N10.normalGenerators j := by decide +kernel
    rw [← he j]
    apply Subgroup.mul_mem
    · apply (show top.ker≤top.ker⊔BinaryNormal8T30.N10.kernel from le_sup_left)
      rw [kernel_eq]
      exact (member_iff 7 _).mp ((show ∀ j, member 7 (kernelPart j) from by decide +kernel) j)
    · apply (show BinaryNormal8T30.N10.kernel≤top.ker⊔BinaryNormal8T30.N10.kernel from le_sup_right)
      exact (member_iff 10 _).mp ((show ∀ j, member 10 (normalPart j) from by decide +kernel) j)

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

private def coverValues (i : Fin 64) : Equiv.Perm (Fin 2) := (if i.val < 32 then (if i.val < 16 then (if i.val < 8 then (if i.val < 4 then (if i.val < 2 then (if i.val < 1 then cover0 else cover0) else (if i.val < 3 then cover1 else cover1)) else (if i.val < 6 then (if i.val < 5 then cover0 else cover0) else (if i.val < 7 then cover1 else cover1))) else (if i.val < 12 then (if i.val < 10 then (if i.val < 9 then cover1 else cover1) else (if i.val < 11 then cover0 else cover0)) else (if i.val < 14 then (if i.val < 13 then cover1 else cover1) else (if i.val < 15 then cover0 else cover0)))) else (if i.val < 24 then (if i.val < 20 then (if i.val < 18 then (if i.val < 17 then cover1 else cover1) else (if i.val < 19 then cover0 else cover0)) else (if i.val < 22 then (if i.val < 21 then cover1 else cover1) else (if i.val < 23 then cover0 else cover0))) else (if i.val < 28 then (if i.val < 26 then (if i.val < 25 then cover0 else cover0) else (if i.val < 27 then cover1 else cover1)) else (if i.val < 30 then (if i.val < 29 then cover0 else cover0) else (if i.val < 31 then cover1 else cover1))))) else (if i.val < 48 then (if i.val < 40 then (if i.val < 36 then (if i.val < 34 then (if i.val < 33 then cover0 else cover0) else (if i.val < 35 then cover1 else cover1)) else (if i.val < 38 then (if i.val < 37 then cover0 else cover0) else (if i.val < 39 then cover1 else cover1))) else (if i.val < 44 then (if i.val < 42 then (if i.val < 41 then cover1 else cover1) else (if i.val < 43 then cover0 else cover0)) else (if i.val < 46 then (if i.val < 45 then cover1 else cover1) else (if i.val < 47 then cover0 else cover0)))) else (if i.val < 56 then (if i.val < 52 then (if i.val < 50 then (if i.val < 49 then cover1 else cover1) else (if i.val < 51 then cover0 else cover0)) else (if i.val < 54 then (if i.val < 53 then cover1 else cover1) else (if i.val < 55 then cover0 else cover0))) else (if i.val < 60 then (if i.val < 58 then (if i.val < 57 then cover0 else cover0) else (if i.val < 59 then cover1 else cover1)) else (if i.val < 62 then (if i.val < 61 then cover0 else cover0) else (if i.val < 63 then cover1 else cover1))))))
private def coverImages (j : Fin 3) : Equiv.Perm (Fin 2) := (if j.val < 1 then cover1 else (if j.val < 2 then cover0 else cover1))
private theorem cover_step : ∀ i j,
    coverValues (BinaryMenuCayley8T30.certificate.next i j)=coverValues i*coverImages j := (Fin.addCases (m := 32) (n := 32) (Fin.addCases (m := 16) (n := 16) (by decide +kernel) (by decide +kernel)) (Fin.addCases (m := 16) (n := 16) (by decide +kernel) (by decide +kernel)))
private theorem cover_identity : coverValues BinaryMenuCayley8T30.certificate.identity=1 := by decide +kernel

def cover : Source →* Equiv.Perm (Fin 2) where
  toFun x := coverValues x.index
  map_one' := cover_identity
  map_mul' x y := by
    change coverValues (BinaryMenuCayley8T30.certificate.walk x.index
      (BinaryMenuCayley8T30.certificate.words y.index))=coverValues x.index*coverValues y.index
    rw [EncodedCayleyCertificate.values_walk _ coverValues coverImages cover_step,
      ← EncodedCayleyCertificate.values_word _ coverValues coverImages cover_step cover_identity]

theorem cover_kernel : cover.ker=top.ker⊔BinaryNormal8T30.N10.kernel := by
  rw [join_eq]
  ext x
  change cover x=1 ↔ x∈(BinaryNormal8T30.states 10).kernel
  rw [← member_iff]
  exact (show ∀ x : Source, cover x=1 ↔ member 10 x from by decide +kernel) x

/-- Every local numerical dimension follows from checked original subgroup
orders and maps; the selected original cut and full fixed preimage remain. -/
def certificate : BinaryPairLocalCertificate generators top BinaryNormal8T30.N10.kernel where
  cut := BinaryNormal8T30.N7.kernel
  cut_normal := inferInstance
  cut_le_kernel := cut_le
  intersection_le_cut := intersection_le
  central := cut_central
  cutDimension := 0
  fixedDimension := 0
  cut_card := by simp only [intersection_eq,BinaryNormal8T30.N7.kernel_card,BinaryNormal8T30.N7.kernel_card] <;> decide
  fixed_card := by simp only [fixed_eq,BinaryNormal8T30.N7.kernel_card,BinaryNormal8T30.N7.kernel_card] <;> decide
  coverDegree := 2
  cover := cover
  cover_kernel := cover_kernel
  width := 8
  gap := by decide

end N10

namespace N11

theorem intersection_eq : top.ker⊓BinaryNormal8T30.N11.kernel=BinaryNormal8T30.N7.kernel := by
  rw [kernel_eq]
  ext x
  change (x∈(BinaryNormal8T30.states 7).kernel ∧ x∈(BinaryNormal8T30.states 11).kernel) ↔ x∈(BinaryNormal8T30.states 7).kernel
  simp only [← member_iff]
  exact (show ∀ x : Source, (member 7 x ∧ member 11 x) ↔ member 7 x from by decide +kernel) x

theorem cut_le : BinaryNormal8T30.N7.kernel≤top.ker := by
  intro x hx
  have hk : x∈BinaryNormal8T30.N7.kernel := (member_iff 7 x).mp
    ((show ∀ x : Source, member 7 x → member 7 x from by decide +kernel) x ((member_iff 7 x).mpr hx))
  exact kernel_eq.symm ▸ hk

theorem intersection_le : top.ker⊓BinaryNormal8T30.N11.kernel≤BinaryNormal8T30.N7.kernel := by
  intro x hx
  have hx' : x∈BinaryNormal8T30.N7.kernel := intersection_eq ▸ hx
  apply (member_iff 7 x).mp
  exact (show ∀ x : Source, member 7 x → member 7 x from by decide +kernel) x ((member_iff 7 x).mpr hx')

theorem cut_central : ∀ j, ∀ x : BinaryNormal8T30.N7.kernel,
    (x:Source)⁻¹*(generators j*(x:Source)*(generators j)⁻¹)∈BinaryNormal8T30.N11.kernel := by
  have h : ∀ j, ∀ x : Source, member 7 x →
      member 11 (x⁻¹*(generators j*x*(generators j)⁻¹)) := by decide +kernel
  intro j x
  exact (member_iff 11 _).mp (h j x.val ((member_iff 7 x.val).mpr x.property))

theorem fixed_eq : binaryPairFixedSubgroup top.ker BinaryNormal8T30.N7.kernel=BinaryNormal8T30.N7.kernel := by
  rw [kernel_eq]
  ext x
  rw [binaryPairFixedSubgroup_mem_iff _ _ generators BinaryNormal8T30.generators_full]
  change (x∈(BinaryNormal8T30.states 7).kernel ∧ ∀ j,
    x⁻¹*(generators j*x*(generators j)⁻¹)∈(BinaryNormal8T30.states 7).kernel) ↔ x∈(BinaryNormal8T30.states 7).kernel
  simp only [← member_iff]
  exact (show ∀ x : Source, (member 7 x ∧ ∀ j,
    member 7 (x⁻¹*(generators j*x*(generators j)⁻¹))) ↔ member 7 x from by decide +kernel) x

/-- These are the actual selected cut lift generators from this record. -/
def recordedCutGenerators (j : Fin 3) : Source := ⟨((if j.val < 1 then 27 else (if j.val < 2 then 30 else 31)) : Fin 64)⟩
private def cutWords (j : Fin 3) : List (Fin 3) := (if j.val < 1 then ([0] : List (Fin 3)) else (if j.val < 2 then ([1] : List (Fin 3)) else ([2] : List (Fin 3))))
private theorem cutWords_checked : ∀ j,
    ((cutWords j).map recordedCutGenerators).prod=BinaryNormal8T30.N7.normalGenerators j := by decide +kernel

theorem recorded_cut_eq : Subgroup.closure (Set.range recordedCutGenerators)=BinaryNormal8T30.N7.kernel := by
  apply le_antisymm
  · apply (Subgroup.closure_le _).mpr
    rintro _ ⟨j,rfl⟩
    exact (member_iff 7 _).mp
      ((show ∀ j, member 7 (recordedCutGenerators j) from by decide +kernel) j)
  · exact (BinaryNormalGeneratorWords.closure_le
      ({words := cutWords, equations := cutWords_checked} :
        BinaryNormalGeneratorWords BinaryNormal8T30.N7.normalGenerators recordedCutGenerators))

private def kernelPart (j : Fin 5) : Source := ⟨((if j.val < 2 then (if j.val < 1 then 26 else 26) else (if j.val < 3 then 26 else (if j.val < 4 then 26 else 26))) : Fin 64)⟩
private def normalPart (j : Fin 5) : Source := ⟨((if j.val < 2 then (if j.val < 1 then 62 else 31) else (if j.val < 3 then 56 else (if j.val < 4 then 58 else 43))) : Fin 64)⟩

theorem join_eq : top.ker⊔BinaryNormal8T30.N11.kernel=BinaryNormal8T30.N11.kernel := by
  apply le_antisymm
  · apply sup_le
    · intro x hx
      have hx' : x∈BinaryNormal8T30.N7.kernel := kernel_eq ▸ hx
      exact (member_iff 11 x).mp
        ((show ∀ x : Source, member 7 x → member 11 x from by decide +kernel) x ((member_iff 7 x).mpr hx'))
    · intro x hx
      exact (member_iff 11 x).mp
        ((show ∀ x : Source, member 11 x → member 11 x from by decide +kernel) x ((member_iff 11 x).mpr hx))
  · change Subgroup.closure (Set.range BinaryNormal8T30.N11.normalGenerators)≤_
    apply (Subgroup.closure_le _).mpr
    rintro _ ⟨j,rfl⟩
    have he : ∀ j, kernelPart j*normalPart j=BinaryNormal8T30.N11.normalGenerators j := by decide +kernel
    rw [← he j]
    apply Subgroup.mul_mem
    · apply (show top.ker≤top.ker⊔BinaryNormal8T30.N11.kernel from le_sup_left)
      rw [kernel_eq]
      exact (member_iff 7 _).mp ((show ∀ j, member 7 (kernelPart j) from by decide +kernel) j)
    · apply (show BinaryNormal8T30.N11.kernel≤top.ker⊔BinaryNormal8T30.N11.kernel from le_sup_right)
      exact (member_iff 11 _).mp ((show ∀ j, member 11 (normalPart j) from by decide +kernel) j)

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

private def coverValues (i : Fin 64) : Equiv.Perm (Fin 2) := (if i.val < 32 then (if i.val < 16 then (if i.val < 8 then (if i.val < 4 then (if i.val < 2 then (if i.val < 1 then cover0 else cover0) else (if i.val < 3 then cover0 else cover0)) else (if i.val < 6 then (if i.val < 5 then cover0 else cover0) else (if i.val < 7 then cover0 else cover0))) else (if i.val < 12 then (if i.val < 10 then (if i.val < 9 then cover1 else cover1) else (if i.val < 11 then cover1 else cover1)) else (if i.val < 14 then (if i.val < 13 then cover1 else cover1) else (if i.val < 15 then cover1 else cover1)))) else (if i.val < 24 then (if i.val < 20 then (if i.val < 18 then (if i.val < 17 then cover0 else cover0) else (if i.val < 19 then cover0 else cover0)) else (if i.val < 22 then (if i.val < 21 then cover0 else cover0) else (if i.val < 23 then cover0 else cover0))) else (if i.val < 28 then (if i.val < 26 then (if i.val < 25 then cover1 else cover1) else (if i.val < 27 then cover1 else cover1)) else (if i.val < 30 then (if i.val < 29 then cover1 else cover1) else (if i.val < 31 then cover1 else cover1))))) else (if i.val < 48 then (if i.val < 40 then (if i.val < 36 then (if i.val < 34 then (if i.val < 33 then cover0 else cover0) else (if i.val < 35 then cover0 else cover0)) else (if i.val < 38 then (if i.val < 37 then cover0 else cover0) else (if i.val < 39 then cover0 else cover0))) else (if i.val < 44 then (if i.val < 42 then (if i.val < 41 then cover1 else cover1) else (if i.val < 43 then cover1 else cover1)) else (if i.val < 46 then (if i.val < 45 then cover1 else cover1) else (if i.val < 47 then cover1 else cover1)))) else (if i.val < 56 then (if i.val < 52 then (if i.val < 50 then (if i.val < 49 then cover0 else cover0) else (if i.val < 51 then cover0 else cover0)) else (if i.val < 54 then (if i.val < 53 then cover0 else cover0) else (if i.val < 55 then cover0 else cover0))) else (if i.val < 60 then (if i.val < 58 then (if i.val < 57 then cover1 else cover1) else (if i.val < 59 then cover1 else cover1)) else (if i.val < 62 then (if i.val < 61 then cover1 else cover1) else (if i.val < 63 then cover1 else cover1))))))
private def coverImages (j : Fin 3) : Equiv.Perm (Fin 2) := (if j.val < 1 then cover1 else (if j.val < 2 then cover1 else cover0))
private theorem cover_step : ∀ i j,
    coverValues (BinaryMenuCayley8T30.certificate.next i j)=coverValues i*coverImages j := (Fin.addCases (m := 32) (n := 32) (Fin.addCases (m := 16) (n := 16) (by decide +kernel) (by decide +kernel)) (Fin.addCases (m := 16) (n := 16) (by decide +kernel) (by decide +kernel)))
private theorem cover_identity : coverValues BinaryMenuCayley8T30.certificate.identity=1 := by decide +kernel

def cover : Source →* Equiv.Perm (Fin 2) where
  toFun x := coverValues x.index
  map_one' := cover_identity
  map_mul' x y := by
    change coverValues (BinaryMenuCayley8T30.certificate.walk x.index
      (BinaryMenuCayley8T30.certificate.words y.index))=coverValues x.index*coverValues y.index
    rw [EncodedCayleyCertificate.values_walk _ coverValues coverImages cover_step,
      ← EncodedCayleyCertificate.values_word _ coverValues coverImages cover_step cover_identity]

theorem cover_kernel : cover.ker=top.ker⊔BinaryNormal8T30.N11.kernel := by
  rw [join_eq]
  ext x
  change cover x=1 ↔ x∈(BinaryNormal8T30.states 11).kernel
  rw [← member_iff]
  exact (show ∀ x : Source, cover x=1 ↔ member 11 x from by decide +kernel) x

/-- Every local numerical dimension follows from checked original subgroup
orders and maps; the selected original cut and full fixed preimage remain. -/
def certificate : BinaryPairLocalCertificate generators top BinaryNormal8T30.N11.kernel where
  cut := BinaryNormal8T30.N7.kernel
  cut_normal := inferInstance
  cut_le_kernel := cut_le
  intersection_le_cut := intersection_le
  central := cut_central
  cutDimension := 0
  fixedDimension := 0
  cut_card := by simp only [intersection_eq,BinaryNormal8T30.N7.kernel_card,BinaryNormal8T30.N7.kernel_card] <;> decide
  fixed_card := by simp only [fixed_eq,BinaryNormal8T30.N7.kernel_card,BinaryNormal8T30.N7.kernel_card] <;> decide
  coverDegree := 2
  cover := cover
  cover_kernel := cover_kernel
  width := 8
  gap := by decide

end N11

namespace N12

theorem intersection_eq : top.ker⊓BinaryNormal8T30.N12.kernel=BinaryNormal8T30.N7.kernel := by
  rw [kernel_eq]
  ext x
  change (x∈(BinaryNormal8T30.states 7).kernel ∧ x∈(BinaryNormal8T30.states 12).kernel) ↔ x∈(BinaryNormal8T30.states 7).kernel
  simp only [← member_iff]
  exact (show ∀ x : Source, (member 7 x ∧ member 12 x) ↔ member 7 x from by decide +kernel) x

theorem cut_le : BinaryNormal8T30.N7.kernel≤top.ker := by
  intro x hx
  have hk : x∈BinaryNormal8T30.N7.kernel := (member_iff 7 x).mp
    ((show ∀ x : Source, member 7 x → member 7 x from by decide +kernel) x ((member_iff 7 x).mpr hx))
  exact kernel_eq.symm ▸ hk

theorem intersection_le : top.ker⊓BinaryNormal8T30.N12.kernel≤BinaryNormal8T30.N7.kernel := by
  intro x hx
  have hx' : x∈BinaryNormal8T30.N7.kernel := intersection_eq ▸ hx
  apply (member_iff 7 x).mp
  exact (show ∀ x : Source, member 7 x → member 7 x from by decide +kernel) x ((member_iff 7 x).mpr hx')

theorem cut_central : ∀ j, ∀ x : BinaryNormal8T30.N7.kernel,
    (x:Source)⁻¹*(generators j*(x:Source)*(generators j)⁻¹)∈BinaryNormal8T30.N12.kernel := by
  have h : ∀ j, ∀ x : Source, member 7 x →
      member 12 (x⁻¹*(generators j*x*(generators j)⁻¹)) := by decide +kernel
  intro j x
  exact (member_iff 12 _).mp (h j x.val ((member_iff 7 x.val).mpr x.property))

theorem fixed_eq : binaryPairFixedSubgroup top.ker BinaryNormal8T30.N7.kernel=BinaryNormal8T30.N7.kernel := by
  rw [kernel_eq]
  ext x
  rw [binaryPairFixedSubgroup_mem_iff _ _ generators BinaryNormal8T30.generators_full]
  change (x∈(BinaryNormal8T30.states 7).kernel ∧ ∀ j,
    x⁻¹*(generators j*x*(generators j)⁻¹)∈(BinaryNormal8T30.states 7).kernel) ↔ x∈(BinaryNormal8T30.states 7).kernel
  simp only [← member_iff]
  exact (show ∀ x : Source, (member 7 x ∧ ∀ j,
    member 7 (x⁻¹*(generators j*x*(generators j)⁻¹))) ↔ member 7 x from by decide +kernel) x

/-- These are the actual selected cut lift generators from this record. -/
def recordedCutGenerators (j : Fin 3) : Source := ⟨((if j.val < 1 then 27 else (if j.val < 2 then 30 else 31)) : Fin 64)⟩
private def cutWords (j : Fin 3) : List (Fin 3) := (if j.val < 1 then ([0] : List (Fin 3)) else (if j.val < 2 then ([1] : List (Fin 3)) else ([2] : List (Fin 3))))
private theorem cutWords_checked : ∀ j,
    ((cutWords j).map recordedCutGenerators).prod=BinaryNormal8T30.N7.normalGenerators j := by decide +kernel

theorem recorded_cut_eq : Subgroup.closure (Set.range recordedCutGenerators)=BinaryNormal8T30.N7.kernel := by
  apply le_antisymm
  · apply (Subgroup.closure_le _).mpr
    rintro _ ⟨j,rfl⟩
    exact (member_iff 7 _).mp
      ((show ∀ j, member 7 (recordedCutGenerators j) from by decide +kernel) j)
  · exact (BinaryNormalGeneratorWords.closure_le
      ({words := cutWords, equations := cutWords_checked} :
        BinaryNormalGeneratorWords BinaryNormal8T30.N7.normalGenerators recordedCutGenerators))

private def kernelPart (j : Fin 3) : Source := ⟨((if j.val < 1 then 26 else (if j.val < 2 then 26 else 26)) : Fin 64)⟩
private def normalPart (j : Fin 3) : Source := ⟨((if j.val < 1 then 38 else (if j.val < 2 then 31 else 56)) : Fin 64)⟩

theorem join_eq : top.ker⊔BinaryNormal8T30.N12.kernel=BinaryNormal8T30.N12.kernel := by
  apply le_antisymm
  · apply sup_le
    · intro x hx
      have hx' : x∈BinaryNormal8T30.N7.kernel := kernel_eq ▸ hx
      exact (member_iff 12 x).mp
        ((show ∀ x : Source, member 7 x → member 12 x from by decide +kernel) x ((member_iff 7 x).mpr hx'))
    · intro x hx
      exact (member_iff 12 x).mp
        ((show ∀ x : Source, member 12 x → member 12 x from by decide +kernel) x ((member_iff 12 x).mpr hx))
  · change Subgroup.closure (Set.range BinaryNormal8T30.N12.normalGenerators)≤_
    apply (Subgroup.closure_le _).mpr
    rintro _ ⟨j,rfl⟩
    have he : ∀ j, kernelPart j*normalPart j=BinaryNormal8T30.N12.normalGenerators j := by decide +kernel
    rw [← he j]
    apply Subgroup.mul_mem
    · apply (show top.ker≤top.ker⊔BinaryNormal8T30.N12.kernel from le_sup_left)
      rw [kernel_eq]
      exact (member_iff 7 _).mp ((show ∀ j, member 7 (kernelPart j) from by decide +kernel) j)
    · apply (show BinaryNormal8T30.N12.kernel≤top.ker⊔BinaryNormal8T30.N12.kernel from le_sup_right)
      exact (member_iff 12 _).mp ((show ∀ j, member 12 (normalPart j) from by decide +kernel) j)

private def cover0 : Equiv.Perm (Fin 0) where
  toFun := Fin.elim0
  invFun := Fin.elim0
  left_inv := fun x => Fin.elim0 x
  right_inv := fun x => Fin.elim0 x

private def coverValues (i : Fin 64) : Equiv.Perm (Fin 0) := (if i.val < 32 then (if i.val < 16 then (if i.val < 8 then (if i.val < 4 then (if i.val < 2 then (if i.val < 1 then cover0 else cover0) else (if i.val < 3 then cover0 else cover0)) else (if i.val < 6 then (if i.val < 5 then cover0 else cover0) else (if i.val < 7 then cover0 else cover0))) else (if i.val < 12 then (if i.val < 10 then (if i.val < 9 then cover0 else cover0) else (if i.val < 11 then cover0 else cover0)) else (if i.val < 14 then (if i.val < 13 then cover0 else cover0) else (if i.val < 15 then cover0 else cover0)))) else (if i.val < 24 then (if i.val < 20 then (if i.val < 18 then (if i.val < 17 then cover0 else cover0) else (if i.val < 19 then cover0 else cover0)) else (if i.val < 22 then (if i.val < 21 then cover0 else cover0) else (if i.val < 23 then cover0 else cover0))) else (if i.val < 28 then (if i.val < 26 then (if i.val < 25 then cover0 else cover0) else (if i.val < 27 then cover0 else cover0)) else (if i.val < 30 then (if i.val < 29 then cover0 else cover0) else (if i.val < 31 then cover0 else cover0))))) else (if i.val < 48 then (if i.val < 40 then (if i.val < 36 then (if i.val < 34 then (if i.val < 33 then cover0 else cover0) else (if i.val < 35 then cover0 else cover0)) else (if i.val < 38 then (if i.val < 37 then cover0 else cover0) else (if i.val < 39 then cover0 else cover0))) else (if i.val < 44 then (if i.val < 42 then (if i.val < 41 then cover0 else cover0) else (if i.val < 43 then cover0 else cover0)) else (if i.val < 46 then (if i.val < 45 then cover0 else cover0) else (if i.val < 47 then cover0 else cover0)))) else (if i.val < 56 then (if i.val < 52 then (if i.val < 50 then (if i.val < 49 then cover0 else cover0) else (if i.val < 51 then cover0 else cover0)) else (if i.val < 54 then (if i.val < 53 then cover0 else cover0) else (if i.val < 55 then cover0 else cover0))) else (if i.val < 60 then (if i.val < 58 then (if i.val < 57 then cover0 else cover0) else (if i.val < 59 then cover0 else cover0)) else (if i.val < 62 then (if i.val < 61 then cover0 else cover0) else (if i.val < 63 then cover0 else cover0))))))
private def coverImages (j : Fin 3) : Equiv.Perm (Fin 0) := (if j.val < 1 then cover0 else (if j.val < 2 then cover0 else cover0))
private theorem cover_step : ∀ i j,
    coverValues (BinaryMenuCayley8T30.certificate.next i j)=coverValues i*coverImages j := (Fin.addCases (m := 32) (n := 32) (Fin.addCases (m := 16) (n := 16) (by decide +kernel) (by decide +kernel)) (Fin.addCases (m := 16) (n := 16) (by decide +kernel) (by decide +kernel)))
private theorem cover_identity : coverValues BinaryMenuCayley8T30.certificate.identity=1 := by decide +kernel

def cover : Source →* Equiv.Perm (Fin 0) where
  toFun x := coverValues x.index
  map_one' := cover_identity
  map_mul' x y := by
    change coverValues (BinaryMenuCayley8T30.certificate.walk x.index
      (BinaryMenuCayley8T30.certificate.words y.index))=coverValues x.index*coverValues y.index
    rw [EncodedCayleyCertificate.values_walk _ coverValues coverImages cover_step,
      ← EncodedCayleyCertificate.values_word _ coverValues coverImages cover_step cover_identity]

theorem cover_kernel : cover.ker=top.ker⊔BinaryNormal8T30.N12.kernel := by
  rw [join_eq]
  ext x
  change cover x=1 ↔ x∈(BinaryNormal8T30.states 12).kernel
  rw [← member_iff]
  exact (show ∀ x : Source, cover x=1 ↔ member 12 x from by decide +kernel) x

/-- Every local numerical dimension follows from checked original subgroup
orders and maps; the selected original cut and full fixed preimage remain. -/
def certificate : BinaryPairLocalCertificate generators top BinaryNormal8T30.N12.kernel where
  cut := BinaryNormal8T30.N7.kernel
  cut_normal := inferInstance
  cut_le_kernel := cut_le
  intersection_le_cut := intersection_le
  central := cut_central
  cutDimension := 0
  fixedDimension := 0
  cut_card := by simp only [intersection_eq,BinaryNormal8T30.N7.kernel_card,BinaryNormal8T30.N7.kernel_card] <;> decide
  fixed_card := by simp only [fixed_eq,BinaryNormal8T30.N7.kernel_card,BinaryNormal8T30.N7.kernel_card] <;> decide
  coverDegree := 0
  cover := cover
  cover_kernel := cover_kernel
  width := 8
  gap := by decide

end N12

end SymmetricSubgroupAsymptotics.BinaryPairLocal8T30
