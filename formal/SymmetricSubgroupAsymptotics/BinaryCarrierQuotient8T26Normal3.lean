import SymmetricSubgroupAsymptotics.FiniteQuotientInvariantCertificates
import SymmetricSubgroupAsymptotics.BinaryCarrierRank8T26Normal3

/-! Complete the selected original 8T26 normal #3 row. The center is
counted through its original 16-element preimage, and the original derived
subgroup has an eight-row certificate. Both conclusions concern the literal
OriginalGroup/N; no abstract quotient or additional normal is substituted. -/
set_option autoImplicit false
noncomputable section
open scoped commutatorElement

namespace SymmetricSubgroupAsymptotics.BinaryCarrierQuotient8T26Normal3

open BinaryCarrierRank8T26Normal3

private def inverseCodes (i : Fin 64) : Fin (8^8) :=
  (#[342391,9777271,4603207,5520487,8859991,1521751,12858727,14038087,
    2206526,11641406,2739128,11109308,3271226,10609466,3771068,12174008,
    9245173,874993,4988389,5135809,989653,9392593,13505989,13391329,
    7384622,6467342,6852524,6999944,6352682,7532042,7917224,8031884,
    8745331,1407091,4488547,5667907,489811,9924691,13006147,13923427,
    3385886,10724126,2853788,11256728,2353946,11788826,3918488,12288668,
    1906933,10309873,6167749,6053089,10424533,2054353,14423269,14570689,
    14722862,15902222,15255464,15370124,15787562,14870282,16287404,16434824]
      : Array (Fin (8^8)))[i.val]!

private theorem decode_left : ∀ i : Fin 64, ∀ a : Fin 8,
    finFunctionFinEquiv.symm (inverseCodes i)
      (finFunctionFinEquiv.symm (BinaryMenuCayley8T26.certificate.rows i) a)=a := by
  decide +kernel

private theorem decode_right : ∀ i : Fin 64, ∀ a : Fin 8,
    finFunctionFinEquiv.symm (BinaryMenuCayley8T26.certificate.rows i)
      (finFunctionFinEquiv.symm (inverseCodes i) a)=a := by
  decide +kernel

/-- Decode only the existing authoritative source rows. -/
def sourcePermutation (i : Fin 64) : Equiv.Perm (Fin 8) where
  toFun := finFunctionFinEquiv.symm (BinaryMenuCayley8T26.certificate.rows i)
  invFun := finFunctionFinEquiv.symm (inverseCodes i)
  left_inv := decode_left i
  right_inv := decode_right i

theorem sourcePermutation_code (i : Fin 64) :
    permutationCode (sourcePermutation i)=BinaryMenuCayley8T26.certificate.rows i := by
  change finFunctionFinEquiv
    (finFunctionFinEquiv.symm (BinaryMenuCayley8T26.certificate.rows i))=_
  exact finFunctionFinEquiv.apply_symm_apply _

/-- Every decoded row is identified with the exact original Cayley element. -/
theorem sourcePermutation_eq (i : Fin 64) :
    sourcePermutation i=BinaryMenuCayley8T26.certificate.toCayley.elements i := by
  apply permutationCode_injective 8
  exact (sourcePermutation_code i).trans
    (BinaryMenuCayley8T26.certificate.encode_elements i).symm

def sourceElement (i : Fin 64) : OriginalGroup :=
  ⟨sourcePermutation i,(BinaryMenuCayley8T26.certificate.mem_closure_iff _).mpr
    ⟨i,(sourcePermutation_code i).symm⟩⟩

theorem sourceElement_bijective : Function.Bijective sourceElement := by
  constructor
  · intro i j h
    apply BinaryMenuCayley8T26.rows_injective
    exact (sourcePermutation_code i).symm.trans
      ((congrArg permutationCode (congrArg Subtype.val h)).trans (sourcePermutation_code j))
  · rintro ⟨g,hg⟩
    obtain ⟨i,hi⟩ := (BinaryMenuCayley8T26.certificate.mem_closure_iff g).mp hg
    refine ⟨i,Subtype.ext ?_⟩
    exact permutationCode_injective 8 ((sourcePermutation_code i).trans hi)

def sourceEquiv : Fin 64 ≃ OriginalGroup := Equiv.ofBijective sourceElement sourceElement_bijective

theorem mem_N_iff (g : OriginalGroup) :
    g ∈ N ↔ ∃ a : Fin 4, g=x^a.val := by
  classical
  rw [N_eq_zpowers,mem_zpowers_iff_mem_range_orderOf,x_order]
  constructor
  · intro hg
    obtain ⟨a,ha,he⟩ := Finset.mem_image.mp hg
    exact ⟨⟨a,Finset.mem_range.mp ha⟩,he.symm⟩
  · rintro ⟨a,ha⟩
    exact Finset.mem_image.mpr ⟨a.val,Finset.mem_range.mpr a.isLt,ha.symm⟩

/-- The selected mask contains exactly the original center preimage. -/
def centerMask (i : Fin 64) : Prop :=
  i ∈ ([1,5,9,13,18,22,26,30,32,36,40,44,51,55,59,63] : List (Fin 64))

instance centerMask_decidable : DecidablePred centerMask := fun i =>
  inferInstanceAs (Decidable
    (i ∈ ([1,5,9,13,18,22,26,30,32,36,40,44,51,55,59,63] : List (Fin 64))))

private theorem center_checked : ∀ i : Fin 64, centerMask i ↔
    ∀ j : Fin 3, ∃ a : Fin 4,
      ⁅sourcePermutation i,BinaryMenuCayley8T26.generators j⁆=
        normalPermutation^a.val :=
  Fin.addCases (m := 32) (n := 32)
    (Fin.addCases (m := 16) (n := 16) (by decide +kernel) (by decide +kernel))
    (Fin.addCases (m := 16) (n := 16) (by decide +kernel) (by decide +kernel))

theorem sourceElement_mem_centerPreimage (i : Fin 64) :
    sourceElement i ∈ quotientCenterPreimage N ↔ centerMask i := by
  rw [mem_quotientCenterPreimage_iff N originalGenerators originalGenerators_full]
  constructor
  · intro h
    apply (center_checked i).mpr
    intro j
    obtain ⟨a,ha⟩ := (mem_N_iff _).mp (h j)
    exact ⟨a,congrArg Subtype.val ha⟩
  · intro h j
    obtain ⟨a,ha⟩ := (center_checked i).mp h j
    exact (mem_N_iff _).mpr ⟨a,Subtype.ext ha⟩

private theorem centerMask_card : Fintype.card {i : Fin 64 // centerMask i}=16 := by
  decide +kernel

theorem centerPreimage_card : Nat.card (quotientCenterPreimage N)=16 := by
  let e : {i : Fin 64 // centerMask i} ≃ quotientCenterPreimage N :=
    sourceEquiv.subtypeEquiv (fun i => (sourceElement_mem_centerPreimage i).symm)
  exact (Nat.card_congr e).symm.trans
    (by simpa only [Nat.card_eq_fintype_card] using centerMask_card)

/-- Actual quotient-center field c=2. -/
theorem quotient_center_card : Nat.card (Subgroup.center (OriginalGroup ⧸ N))=2^2 := by
  have h := quotientCenter_card_mul N
  rw [card_N,centerPreimage_card] at h
  omega

def derivedGenerators (j : Fin 2) : OriginalGroup :=
  if j.val=0 then ⁅originalGenerators 0,originalGenerators 1⁆
  else ⁅originalGenerators 0,originalGenerators 2⁆

private def derivedPermutationGenerators (j : Fin 2) : Equiv.Perm (Fin 8) :=
  if j.val=0 then ⁅BinaryMenuCayley8T26.generators 0,BinaryMenuCayley8T26.generators 1⁆
  else ⁅BinaryMenuCayley8T26.generators 0,BinaryMenuCayley8T26.generators 2⁆

private theorem derivedGenerators_coe (j : Fin 2) :
    (derivedGenerators j : Equiv.Perm (Fin 8))=derivedPermutationGenerators j := by
  unfold derivedGenerators derivedPermutationGenerators
  split_ifs <;> rfl

private def derivedWords (i : Fin 8) : List (Fin 2) :=
  (#[[],[0],[1],[1,0],[1,1],[1,1,0],[1,1,1],[1,1,1,0]]
    : Array (List (Fin 2)))[i.val]!

def derivedRows (i : Fin 8) : OriginalGroup := ((derivedWords i).map derivedGenerators).prod

private def derivedPermutationRows (i : Fin 8) : Equiv.Perm (Fin 8) :=
  ((derivedWords i).map derivedPermutationGenerators).prod

theorem derivedRows_coe (i : Fin 8) :
    (derivedRows i : Equiv.Perm (Fin 8))=derivedPermutationRows i := by
  change OriginalGroup.subtype (((derivedWords i).map derivedGenerators).prod)=_
  rw [map_list_prod,List.map_map]
  have hf : OriginalGroup.subtype ∘ derivedGenerators=derivedPermutationGenerators := by
    funext j
    exact derivedGenerators_coe j
  rw [hf]
  rfl

private def derivedNext (i : Fin 8) (j : Fin 2) : Fin 8 :=
  ((#[#[1,2],#[0,3],#[3,4],#[2,5],#[5,6],#[4,7],#[7,0],#[6,1]]
    : Array (Array (Fin 8)))[i.val]!)[j.val]!

private theorem derived_edges : ∀ i j,
    derivedPermutationRows (derivedNext i j)=
      derivedPermutationRows i * derivedPermutationGenerators j := by
  decide +kernel

def derivedCertificate : FiniteCayleyCertificate derivedGenerators 8 where
  elements := derivedRows
  identity := 0
  identity_eq := rfl
  next := derivedNext
  next_eq i j := by
    apply Subtype.ext
    change (derivedRows (derivedNext i j) : Equiv.Perm (Fin 8))=
      (derivedRows i : Equiv.Perm (Fin 8)) * (derivedGenerators j : Equiv.Perm (Fin 8))
    rw [derivedRows_coe,derivedRows_coe,derivedGenerators_coe]
    exact derived_edges i j
  words := derivedWords
  words_eq _ := rfl

def D : Subgroup OriginalGroup := Subgroup.closure (Set.range derivedGenerators)

theorem derivedRows_mem (i : Fin 8) : derivedRows i ∈ D :=
  (derivedCertificate.mem_closure_iff _).mpr ⟨i,rfl⟩

private theorem derived_injective : Function.Injective derivedPermutationRows := by
  decide +kernel

theorem derived_card : Nat.card D=8 := by
  apply derivedCertificate.card_closure
  intro i j he
  apply derived_injective
  have h := congrArg Subtype.val he
  change (derivedRows i : Equiv.Perm (Fin 8))=(derivedRows j : Equiv.Perm (Fin 8)) at h
  simpa only [derivedRows_coe] using h

private theorem derived_positive : ∀ i : Fin 3, ∀ j : Fin 2, ∃ r : Fin 8,
    BinaryMenuCayley8T26.generators i * derivedPermutationGenerators j *
      (BinaryMenuCayley8T26.generators i)⁻¹=derivedPermutationRows r := by
  decide +kernel

private theorem derived_negative : ∀ i : Fin 3, ∀ j : Fin 2, ∃ r : Fin 8,
    (BinaryMenuCayley8T26.generators i)⁻¹ * derivedPermutationGenerators j *
      BinaryMenuCayley8T26.generators i=derivedPermutationRows r := by
  decide +kernel

instance derived_normal : D.Normal := by
  apply binaryNormal_of_generator_conjugates originalGenerators originalGenerators_full
    derivedGenerators
  · intro i j
    obtain ⟨r,hr⟩ := derived_positive i j
    have he : originalGenerators i * derivedGenerators j * (originalGenerators i)⁻¹=
        derivedRows r := by
      apply Subtype.ext
      change BinaryMenuCayley8T26.generators i * (derivedGenerators j : Equiv.Perm (Fin 8)) *
        (BinaryMenuCayley8T26.generators i)⁻¹=(derivedRows r : Equiv.Perm (Fin 8))
      rw [derivedGenerators_coe,derivedRows_coe]
      exact hr
    rw [he]
    exact derivedRows_mem r
  · intro i j
    obtain ⟨r,hr⟩ := derived_negative i j
    have he : (originalGenerators i)⁻¹ * derivedGenerators j * originalGenerators i=
        derivedRows r := by
      apply Subtype.ext
      change (BinaryMenuCayley8T26.generators i)⁻¹ * (derivedGenerators j : Equiv.Perm (Fin 8)) *
        BinaryMenuCayley8T26.generators i=(derivedRows r : Equiv.Perm (Fin 8))
      rw [derivedGenerators_coe,derivedRows_coe]
      exact hr
    rw [he]
    exact derivedRows_mem r

private theorem generator_commutators : ∀ i j : Fin 3, ∃ r : Fin 8,
    ⁅BinaryMenuCayley8T26.generators i,BinaryMenuCayley8T26.generators j⁆=
      derivedPermutationRows r := by
  decide +kernel

theorem derived_eq : commutator OriginalGroup=D := by
  apply le_antisymm
  · apply commutator_le_of_generator_commutators D originalGenerators originalGenerators_full
    intro i j
    obtain ⟨r,hr⟩ := generator_commutators i j
    have he : ⁅originalGenerators i,originalGenerators j⁆=derivedRows r := by
      apply Subtype.ext
      change ⁅BinaryMenuCayley8T26.generators i,BinaryMenuCayley8T26.generators j⁆=
        (derivedRows r : Equiv.Perm (Fin 8))
      rw [derivedRows_coe]
      exact hr
    rw [he]
    exact derivedRows_mem r
  · apply (Subgroup.closure_le _).mpr
    rintro _ ⟨j,rfl⟩
    have hc (a b : OriginalGroup) : ⁅a,b⁆ ∈ commutator OriginalGroup := by
      rw [commutator_def]
      exact Subgroup.commutator_mem_commutator (Subgroup.mem_top a) (Subgroup.mem_top b)
    unfold derivedGenerators
    split_ifs <;> exact hc _ _

/-- Actual quotient-derived field g=1. -/
theorem quotient_derived_card : Nat.card (commutator (OriginalGroup ⧸ N))=2^1 := by
  have h := quotientCommutator_card_mul N N_le_derived
  rw [card_N,derived_eq,derived_card] at h
  omega

/-- All six fields of the same original normal record, including its actual quotient. -/
theorem full_rank_binding :
    Module.finrank (ZMod 2) (primeRelativeCharacters 2 N)=1 ∧
    Nat.card N=2^2 ∧
    primeNormalHeadMax 2 (N ⊓ commutator OriginalGroup)=1 ∧
    Module.finrank (ZMod 2) (primeRelativeCharacters 2 (primeRelativeRadical 2 N))=1 ∧
    Nat.card (Subgroup.center (OriginalGroup ⧸ N))=2^2 ∧
    Nat.card (commutator (OriginalGroup ⧸ N))=2^1 :=
  ⟨kernel_head,card_N,axis_max_head,radical_head,quotient_center_card,quotient_derived_card⟩

end SymmetricSubgroupAsymptotics.BinaryCarrierQuotient8T26Normal3
