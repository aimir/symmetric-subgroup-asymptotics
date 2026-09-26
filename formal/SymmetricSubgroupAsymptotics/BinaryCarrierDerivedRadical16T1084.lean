import SymmetricSubgroupAsymptotics.PrimeRelativeRadicalFiniteCertificate
import SymmetricSubgroupAsymptotics.BinaryCarrierDerivedOrder16T1084

/-! Selected original relative-derived radical certificate. Its 2
rows are actual words in generator squares and mixed commutators. The
whole original ambient tuple is retained for every normality test. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
open scoped commutatorElement

namespace SymmetricSubgroupAsymptotics.BinaryCarrierDerivedRadical16T1084

abbrev Original := BinaryCarrierDerivedOrder16T1084.Original
abbrev D := commutator Original
private abbrev g := BinaryActionData16.node1084Generators
private abbrev words := BinaryCarrierDerivedOrder16T1084.basisWords
private abbrev ambient := closureGenerators g
private abbrev basis := derivedWordGenerators g words

def ambientBasis (j : Fin 4) : Equiv.Perm (Fin 16) := (words j).eval g
private def seed : Fin 1 → Fin 4 ⊕ (Fin 4 × Fin 7) :=
  ![.inl 2]
private def candidate (j : Fin 1) : Original :=
  primeRelativeFiniteGenerators 2 ambient basis (seed j)
private def ambientCandidate (j : Fin 1) : Equiv.Perm (Fin 16) :=
  primeRelativeFiniteGenerators 2 g ambientBasis (seed j)
private def rowWords : Fin 2 → List (Fin 1) :=
  ![[],[0]]
def elements (i : Fin 2) : Original := ((rowWords i).map candidate).prod
def ambientRows (i : Fin 2) : Equiv.Perm (Fin 16) :=
  ((rowWords i).map ambientCandidate).prod
private def next (i : Fin 2) (j : Fin 1) : Fin 2 :=
  ![![1],![0]] i j
private def conjugateRow (i : Fin 7) (j : Fin 1) : Fin 2 :=
  ![![1],![1],![1],![1],![1],![1],![1]] i j
private def powerRow : Fin 4 → Fin 2 := ![0,0,1,0]
private def mixedRow (j : Fin 4) (i : Fin 7) : Fin 2 :=
  ![![0,0,0,0,0,0,0],![0,0,0,0,0,1,1],![0,0,1,0,1,1,1],![0,0,0,0,0,0,1]] j i

theorem basis_coe (j : Fin 4) :
    (basis j : Equiv.Perm (Fin 16)) = ambientBasis j :=
  closureGenerators_eval_coe g (words j)

private theorem candidate_coe (j : Fin 1) :
    (candidate j : Equiv.Perm (Fin 16)) = ambientCandidate j := by
  cases hs : seed j with
  | inl k =>
    change ((primeRelativeFiniteGenerators 2 ambient basis (seed j) : Original) : Equiv.Perm (Fin 16)) = _
    simp only [hs, primeRelativeFiniteGenerators, Sum.elim_inl, ambientCandidate]
    change (basis k : Equiv.Perm (Fin 16)) ^ 2 = ambientBasis k ^ 2
    rw [basis_coe]
  | inr ki =>
    change ((primeRelativeFiniteGenerators 2 ambient basis (seed j) : Original) : Equiv.Perm (Fin 16)) = _
    simp only [hs, primeRelativeFiniteGenerators, Sum.elim_inr, ambientCandidate]
    change ⁅(basis ki.1 : Equiv.Perm (Fin 16)), g ki.2⁆ = ⁅ambientBasis ki.1, g ki.2⁆
    rw [basis_coe]

theorem elements_coe (i : Fin 2) :
    (elements i : Equiv.Perm (Fin 16)) = ambientRows i := by
  change Original.subtype (((rowWords i).map candidate).prod) = _
  have hf : Original.subtype ∘ candidate = ambientCandidate := funext candidate_coe
  rw [map_list_prod, List.map_map, hf]
  rfl

private theorem next_pointwise : ∀ (i : Fin 2) (j : Fin 1) (x : Fin 16),
    ambientRows (next i j) x = (ambientRows i * ambientCandidate j) x := by decide +kernel
private theorem conjugate_pointwise : ∀ (i : Fin 7) (j : Fin 1) (x : Fin 16),
    ambientRows (conjugateRow i j) x = (g i * ambientCandidate j * (g i)⁻¹) x := by decide +kernel
private theorem power_pointwise : ∀ (j : Fin 4) (x : Fin 16),
    ambientRows (powerRow j) x = (ambientBasis j ^ 2) x := by decide +kernel
private theorem mixed_pointwise : ∀ (j : Fin 4) (i : Fin 7) (x : Fin 16),
    ambientRows (mixedRow j i) x = ⁅ambientBasis j, g i⁆ x := by decide +kernel
private theorem rows_injective_pointwise : ∀ (i j : Fin 2),
    (∀ x : Fin 16, ambientRows i x = ambientRows j x) → i = j := by decide +kernel

private def cayley : FiniteCayleyCertificate candidate 2 where
  elements := elements
  identity := 0
  identity_eq := rfl
  next := next
  next_eq := by
    intro i j
    apply Subtype.ext
    change (elements (next i j) : Equiv.Perm (Fin 16)) =
      (elements i : Equiv.Perm (Fin 16)) * (candidate j : Equiv.Perm (Fin 16))
    rw [elements_coe, elements_coe, candidate_coe]
    exact Equiv.ext (next_pointwise i j)
  words := rowWords
  words_eq _ := rfl

def certificate : PrimeRelativeRadicalFiniteCertificate 2 D ambient basis candidate 2 where
  cayley := cayley
  rows_injective := by
    intro i j h
    have he := congrArg Subtype.val h
    change (elements i : Equiv.Perm (Fin 16)) = (elements j : Equiv.Perm (Fin 16)) at he
    rw [elements_coe, elements_coe] at he
    exact rows_injective_pointwise i j (fun x => congrArg (fun f => f x) he)
  candidate_mem j := primeRelativeFiniteGenerators_mem 2 D ambient basis
    BinaryCarrierDerivedOrder16T1084.certificate.subgroup_eq_commutator (seed j)
  conjugateRow := conjugateRow
  conjugate_eq := by
    intro i j
    apply Subtype.ext
    change (elements (conjugateRow i j) : Equiv.Perm (Fin 16)) =
      g i * (candidate j : Equiv.Perm (Fin 16)) * (g i)⁻¹
    rw [elements_coe, candidate_coe]
    exact Equiv.ext (conjugate_pointwise i j)
  powerRow := powerRow
  power_eq := by
    intro j
    apply Subtype.ext
    change (elements (powerRow j) : Equiv.Perm (Fin 16)) = (basis j : Equiv.Perm (Fin 16)) ^ 2
    rw [elements_coe, basis_coe]
    exact Equiv.ext (power_pointwise j)
  mixedRow := mixedRow
  mixed_eq := by
    intro j i
    apply Subtype.ext
    change (elements (mixedRow j i) : Equiv.Perm (Fin 16)) =
      ⁅(basis j : Equiv.Perm (Fin 16)), g i⁆
    rw [elements_coe, basis_coe]
    exact Equiv.ext (mixed_pointwise j i)

theorem elements_mem_radical (i : Fin 2) : elements i ∈ primeRelativeRadical 2 D := by
  rw [← certificate.closure_eq_radical (closureGenerators_full g)
    BinaryCarrierDerivedOrder16T1084.certificate.subgroup_eq_commutator]
  exact (cayley.mem_closure_iff _).mpr ⟨i, rfl⟩

theorem card_relative_radical : Nat.card (primeRelativeRadical 2 D) = 2 :=
  certificate.card_radical (closureGenerators_full g)
    BinaryCarrierDerivedOrder16T1084.certificate.subgroup_eq_commutator

theorem relative_character_rank : Module.finrank (ZMod 2) (primeRelativeCharacters 2 D) = 3 := by
  have h := primeRelativeRadical_card_factorization 2 D
  rw [BinaryCarrierDerivedOrder16T1084.card_commutator, card_relative_radical] at h
  have hp : 2 ^ Module.finrank (ZMod 2) (primeRelativeCharacters 2 D) = 2 ^ 3 := by omega
  exact (Nat.pow_right_injective (by decide : 1 < (2 : ℕ))) hp

end SymmetricSubgroupAsymptotics.BinaryCarrierDerivedRadical16T1084
