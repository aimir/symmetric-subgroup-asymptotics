import SymmetricSubgroupAsymptotics.BinaryRelativeIndexTwoRadical
import SymmetricSubgroupAsymptotics.BinaryMenuCayley8T26
import SymmetricSubgroupAsymptotics.BinaryNormalGeneratorChecks
import SymmetricSubgroupAsymptotics.PrimeSubdirectNormalRank

/-! Selected literal rank binding for master 8T26, normal #3 (one-based).
The original normal generator is (1 3 5 7)(2 8 6 4). Its square gives
the original relative radical. All normality checks use the three
original permutation generators; the four rank/order fields are derived.
This does not bind the quotient center/derived fields or other normals. -/
set_option autoImplicit false
noncomputable section
open scoped commutatorElement
namespace SymmetricSubgroupAsymptotics.BinaryCarrierRank8T26Normal3

abbrev OriginalGroup := Subgroup.closure (Set.range BinaryMenuCayley8T26.generators)

/-- Literal permutation from carrier_normals.jsonl.gz: 8T26 normals[2]. -/
def normalPermutation : Equiv.Perm (Fin 8) where
  toFun i := (#[2,7,4,1,6,3,0,5] : Array (Fin 8))[i.val]!
  invFun i := (#[6,3,0,5,2,7,4,1] : Array (Fin 8))[i.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

theorem normalPermutation_mem : normalPermutation ∈ OriginalGroup := by
  apply (BinaryMenuCayley8T26.certificate.mem_closure_iff normalPermutation).mpr
  exact ⟨40,by decide +kernel⟩

def x : OriginalGroup := ⟨normalPermutation,normalPermutation_mem⟩

def originalGenerators (j : Fin 3) : OriginalGroup :=
  ⟨BinaryMenuCayley8T26.generators j,Subgroup.subset_closure (Set.mem_range_self j)⟩

theorem originalGenerators_full :
    Subgroup.closure (Set.range originalGenerators)=⊤ :=
  binaryNormal_full_generators_of_equiv BinaryMenuCayley8T26.generators
    originalGenerators (MulEquiv.refl OriginalGroup) (fun _ => rfl)

theorem original_card : Nat.card OriginalGroup=64 := BinaryMenuCayley8T26.exact_card

theorem original_isPGroup : IsPGroup 2 OriginalGroup :=
  IsPGroup.of_card (show Nat.card OriginalGroup=2^6 from original_card)

def normalGenerators (_ : Fin 1) : OriginalGroup := x
def radicalGenerators (_ : Fin 1) : OriginalGroup := x^2

def N : Subgroup OriginalGroup := Subgroup.closure (Set.range normalGenerators)
def R : Subgroup OriginalGroup := Subgroup.closure (Set.range radicalGenerators)

theorem x_mem_N : x ∈ N := Subgroup.subset_closure ⟨0,rfl⟩
theorem square_mem_R : x^2 ∈ R := Subgroup.subset_closure ⟨0,rfl⟩

private theorem positive_conjugates : ∀ j : Fin 3, ∃ a : Fin 4,
    BinaryMenuCayley8T26.generators j * normalPermutation *
      (BinaryMenuCayley8T26.generators j)⁻¹=normalPermutation^a.val := by
  decide +kernel

private theorem negative_conjugates : ∀ j : Fin 3, ∃ a : Fin 4,
    (BinaryMenuCayley8T26.generators j)⁻¹ * normalPermutation *
      BinaryMenuCayley8T26.generators j=normalPermutation^a.val := by
  decide +kernel

instance normal_N : N.Normal := by
  apply binaryNormal_of_generator_conjugates originalGenerators originalGenerators_full
    normalGenerators
  · intro i j
    obtain ⟨a,ha⟩ := positive_conjugates i
    have he : originalGenerators i * normalGenerators j * (originalGenerators i)⁻¹=x^a.val :=
      Subtype.ext ha
    rw [he]
    exact N.pow_mem x_mem_N a.val
  · intro i j
    obtain ⟨a,ha⟩ := negative_conjugates i
    have he : (originalGenerators i)⁻¹ * normalGenerators j * originalGenerators i=x^a.val :=
      Subtype.ext ha
    rw [he]
    exact N.pow_mem x_mem_N a.val

private theorem positive_square : ∀ j : Fin 3,
    BinaryMenuCayley8T26.generators j * normalPermutation^2 *
      (BinaryMenuCayley8T26.generators j)⁻¹=normalPermutation^2 := by
  decide +kernel

private theorem negative_square : ∀ j : Fin 3,
    (BinaryMenuCayley8T26.generators j)⁻¹ * normalPermutation^2 *
      BinaryMenuCayley8T26.generators j=normalPermutation^2 := by
  decide +kernel

instance normal_R : R.Normal := by
  apply binaryNormal_of_generator_conjugates originalGenerators originalGenerators_full
    radicalGenerators
  · intro i j
    have he : originalGenerators i * radicalGenerators j * (originalGenerators i)⁻¹=x^2 :=
      Subtype.ext (positive_square i)
    rw [he]
    exact square_mem_R
  · intro i j
    have he : (originalGenerators i)⁻¹ * radicalGenerators j * originalGenerators i=x^2 :=
      Subtype.ext (negative_square i)
    rw [he]
    exact square_mem_R

theorem N_eq_zpowers : N=Subgroup.zpowers x := by
  rw [Subgroup.zpowers_eq_closure]
  unfold N normalGenerators
  congr 1
  ext y
  simp

theorem R_eq_zpowers : R=Subgroup.zpowers (x^2) := by
  rw [Subgroup.zpowers_eq_closure]
  unfold R radicalGenerators
  congr 1
  ext y
  simp

private theorem x_four : x^4=1 := by
  apply Subtype.ext
  change normalPermutation^4=1
  decide +kernel

private theorem x_square_ne : x^2 ≠ 1 := by
  intro he
  have h := congrArg Subtype.val he
  change normalPermutation^2=1 at h
  exact (by decide +kernel : normalPermutation^2 ≠ 1) h

theorem x_order : orderOf x=4 :=
  orderOf_eq_prime_pow (p := 2) (n := 1) x_square_ne x_four

theorem card_N : Nat.card N=4 := by
  rw [N_eq_zpowers,Nat.card_zpowers,x_order]

theorem card_R : Nat.card R=2 := by
  rw [R_eq_zpowers,Nat.card_zpowers,orderOf_pow' _ (by decide : (2 : ℕ) ≠ 0),x_order]
  norm_num

theorem R_le_N : R ≤ N := by
  apply (Subgroup.closure_le N).mpr
  rintro _ ⟨i,rfl⟩
  exact N.pow_mem x_mem_N 2

theorem R_le_squares :
    R ≤ Subgroup.closure (Set.range (fun n : N => (n : OriginalGroup)^2)) := by
  apply (Subgroup.closure_le _).mpr
  rintro _ ⟨i,rfl⟩
  exact Subgroup.subset_closure ⟨⟨x,x_mem_N⟩,rfl⟩

theorem radical_chain : primeRelativeRadical 2 N=R ∧
    primeRelativeRadical 2 R=⊥ ∧
    Module.finrank (ZMod 2) (primeRelativeCharacters 2 N)=1 ∧
    Module.finrank (ZMod 2) (primeRelativeCharacters 2 R)=1 :=
  binaryRelativeRadical_chain_four_two original_isPGroup R N R_le_N card_N card_R R_le_squares

theorem kernel_head : Module.finrank (ZMod 2) (primeRelativeCharacters 2 N)=1 :=
  radical_chain.2.2.1

theorem radical_head : Module.finrank (ZMod 2)
    (primeRelativeCharacters 2 (primeRelativeRadical 2 N))=1 := by
  have hdim (S T : Subgroup OriginalGroup) [S.Normal] [T.Normal] (h : S=T) :
      Module.finrank (ZMod 2) (primeRelativeCharacters 2 S)=
        Module.finrank (ZMod 2) (primeRelativeCharacters 2 T) := by
    subst T
    rfl
  exact (hdim _ _ radical_chain.1).trans radical_chain.2.2.2

/-- The same original normal lies in the actual original derived subgroup. -/
theorem N_le_derived : N ≤ commutator OriginalGroup := by
  have hx : x=⁅originalGenerators 0,originalGenerators 2⁆⁻¹ *
      ⁅originalGenerators 0,originalGenerators 1⁆ := by
    apply Subtype.ext
    change normalPermutation=⁅BinaryMenuCayley8T26.generators 0,
      BinaryMenuCayley8T26.generators 2⁆⁻¹ *
        ⁅BinaryMenuCayley8T26.generators 0,BinaryMenuCayley8T26.generators 1⁆
    decide +kernel
  have hc (a b : OriginalGroup) : ⁅a,b⁆ ∈ commutator OriginalGroup := by
    rw [commutator_def]
    exact Subgroup.commutator_mem_commutator (Subgroup.mem_top a) (Subgroup.mem_top b)
  apply (Subgroup.closure_le _).mpr
  rintro _ ⟨i,rfl⟩
  change x ∈ commutator OriginalGroup
  rw [hx]
  exact (commutator OriginalGroup).mul_mem
    ((commutator OriginalGroup).inv_mem (hc _ _)) (hc _ _)

/-- The maximum ranges over ALL original ambient normals, with no supplied
normal-list coverage. Proper subgroups of the actual order-four N have
cardinality below four; the remaining case is N itself. -/
theorem axis_max_head : primeNormalHeadMax 2 (N ⊓ commutator OriginalGroup)=1 := by
  apply Nat.le_antisymm
  · apply (primeNormalHeadMax_le_iff 2 _ 1).mpr
    intro M _ hM
    have hMN : M ≤ N := hM.trans inf_le_left
    by_cases he : M=N
    · subst M
      exact kernel_head.le
    · have hcard : Nat.card M < 4 := by
        by_contra hnot
        apply he
        apply Subgroup.eq_of_le_of_card_ge hMN
        rw [card_N]
        omega
      have hpow := primeCharacters_pow_finrank_le_card 2 M
      have habs : Module.finrank (ZMod 2) (PrimeCharacters 2 M) ≤ 1 := by
        by_contra hnot
        have htwo : 2 ≤ Module.finrank (ZMod 2) (PrimeCharacters 2 M) := by omega
        have hlarge : 4 ≤ 2 ^ Module.finrank (ZMod 2) (PrimeCharacters 2 M) :=
          Nat.pow_le_pow_right (by decide : 0 < 2) htwo
        omega
      exact (Submodule.finrank_le (primeRelativeCharacters 2 M)).trans habs
  · rw [← kernel_head]
    exact primeRelativeHead_le_normalHeadMax 2 _ N (le_inf le_rfl N_le_derived)

/-- The original k,n,m,a2 fields of the third 8T26 normal record.
Quotient center/derived fields (c,g) remain outside this selected binding. -/
theorem rank_binding :
    Module.finrank (ZMod 2) (primeRelativeCharacters 2 N)=1 ∧
    Nat.card N=2^2 ∧
    primeNormalHeadMax 2 (N ⊓ commutator OriginalGroup)=1 ∧
    Module.finrank (ZMod 2) (primeRelativeCharacters 2 (primeRelativeRadical 2 N))=1 :=
  ⟨kernel_head,card_N,axis_max_head,radical_head⟩

end SymmetricSubgroupAsymptotics.BinaryCarrierRank8T26Normal3
