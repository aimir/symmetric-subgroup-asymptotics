import SymmetricSubgroupAsymptotics.PrimeRelativeRadicalFiniteCertificate
import SymmetricSubgroupAsymptotics.BinaryCarrierDerivedOrder16T1082

/-! Two literal original-point rows certify the relative radical of the
actual derived subgroup. This retains conjugation by the original group;
the intrinsic Frattini subgroup of the derived group is not substituted. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
open scoped commutatorElement

namespace SymmetricSubgroupAsymptotics.BinaryCarrierDerivedRadical16T1082

abbrev Original := BinaryCarrierDerivedOrder16T1082.Original
private abbrev g := BinaryActionData16.node1082Generators
private abbrev words := BinaryCarrierDerivedOrder16T1082.basisWords
private abbrev ambient := closureGenerators g
private abbrev basis := derivedWordGenerators g words

private def ambientBasis (j : Fin 4) : Equiv.Perm (Fin 16) := (words j).eval g
private def ambientZ : Equiv.Perm (Fin 16) := ⁅ambientBasis 0, g 4⁆
private def candidate (_ : Fin 1) : Original := ⁅basis 0, ambient 4⁆
private def rowWords (i : Fin 2) : List (Fin 1) := ![[], [0]] i
private def elements (i : Fin 2) : Original := ((rowWords i).map candidate).prod
private def ambientRows (i : Fin 2) : Equiv.Perm (Fin 16) :=
  ((rowWords i).map (fun _ => ambientZ)).prod
private def next (i : Fin 2) (_ : Fin 1) : Fin 2 := ![1,0] i
private def mixed (j : Fin 4) (i : Fin 6) : Fin 2 :=
  ![![0,0,0,0,1,0], ![0,0,0,1,0,0],
    ![0,0,0,0,1,1], ![0,0,0,0,1,0]] j i

private theorem basis_coe (j : Fin 4) :
    (basis j : Equiv.Perm (Fin 16)) = ambientBasis j :=
  closureGenerators_eval_coe g (words j)

private theorem candidate_coe (j : Fin 1) :
    (candidate j : Equiv.Perm (Fin 16)) = ambientZ := by
  change ⁅(basis 0 : Equiv.Perm (Fin 16)), g 4⁆ = _
  rw [basis_coe]
  rfl

private theorem elements_coe (i : Fin 2) :
    (elements i : Equiv.Perm (Fin 16)) = ambientRows i := by
  change Original.subtype (((rowWords i).map candidate).prod) = _
  have hf : Original.subtype ∘ candidate = fun _ => ambientZ := by
    funext j
    exact candidate_coe j
  rw [map_list_prod, List.map_map, hf]
  rfl

private theorem next_pointwise : ∀ (i : Fin 2) (j : Fin 1) (x : Fin 16),
    ambientRows (next i j) x = (ambientRows i * ambientZ) x := by decide +kernel
private theorem conjugate_pointwise : ∀ (i : Fin 6) (x : Fin 16),
    ambientRows 1 x = (g i * ambientZ * (g i)⁻¹) x := by decide +kernel
private theorem power_pointwise : ∀ (j : Fin 4) (x : Fin 16),
    ambientRows 0 x = (ambientBasis j ^ 2) x := by decide +kernel
private theorem mixed_pointwise : ∀ (j : Fin 4) (i : Fin 6) (x : Fin 16),
    ambientRows (mixed j i) x = ⁅ambientBasis j, g i⁆ x := by decide +kernel
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

private def certificate : PrimeRelativeRadicalFiniteCertificate 2
    (commutator Original) ambient basis candidate 2 where
  cayley := cayley
  rows_injective := by
    intro i j h
    have he := congrArg Subtype.val h
    change (elements i : Equiv.Perm (Fin 16)) = (elements j : Equiv.Perm (Fin 16)) at he
    rw [elements_coe, elements_coe] at he
    exact rows_injective_pointwise i j (fun x => congrArg (fun f => f x) he)
  candidate_mem := by
    intro j
    exact commutator_mem_primeRelativeRadical 2 (commutator Original)
      ⟨basis 0, (words 0).eval_mem_commutator ambient⟩ (ambient 4)
  conjugateRow := fun _ _ => 1
  conjugate_eq := by
    intro i j
    apply Subtype.ext
    change (elements 1 : Equiv.Perm (Fin 16)) =
      g i * (candidate j : Equiv.Perm (Fin 16)) * (g i)⁻¹
    rw [elements_coe, candidate_coe]
    exact Equiv.ext (conjugate_pointwise i)
  powerRow := fun _ => 0
  power_eq := by
    intro j
    apply Subtype.ext
    change (elements 0 : Equiv.Perm (Fin 16)) = (basis j : Equiv.Perm (Fin 16)) ^ 2
    rw [elements_coe, basis_coe]
    exact Equiv.ext (power_pointwise j)
  mixedRow := mixed
  mixed_eq := by
    intro j i
    apply Subtype.ext
    change (elements (mixed j i) : Equiv.Perm (Fin 16)) =
      ⁅(basis j : Equiv.Perm (Fin 16)), g i⁆
    rw [elements_coe, basis_coe]
    exact Equiv.ext (mixed_pointwise j i)

/-- The exact radical uses the original group's conjugation action. -/
theorem card_relative_radical :
    Nat.card (primeRelativeRadical 2 (commutator Original)) = 2 :=
  certificate.card_radical (closureGenerators_full g)
    BinaryCarrierDerivedOrder16T1082.certificate.subgroup_eq_commutator

/-- Exact dimension of the original invariant derived-character space. -/
theorem relative_character_rank :
    Module.finrank (ZMod 2) (primeRelativeCharacters 2 (commutator Original)) = 3 := by
  have h := primeRelativeRadical_card_factorization 2 (commutator Original)
  rw [BinaryCarrierDerivedOrder16T1082.card_commutator, card_relative_radical] at h
  have hp : 2 ^ Module.finrank (ZMod 2)
      (primeRelativeCharacters 2 (commutator Original)) = 2 ^ 3 := by omega
  exact (Nat.pow_right_injective (by decide : 1 < (2 : ℕ))) hp

end SymmetricSubgroupAsymptotics.BinaryCarrierDerivedRadical16T1082
