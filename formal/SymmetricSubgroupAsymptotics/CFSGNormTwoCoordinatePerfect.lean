import SymmetricSubgroupAsymptotics.CFSGNormTwoCoordinateNormalRootGeneration
import SymmetricSubgroupAsymptotics.CFSGNormTwoCoordinatePositivePairCollecting
import Mathlib.GroupTheory.IsPerfect

/-! The actual canonical norm-two elementary group is perfect in rank
at least two over EVERY field. One integral coefficient-one A2 root
commutator supplies a full root line in the derived subgroup; proved
normal root generation then gives the whole group. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
namespace SymmetricSubgroupAsymptotics.CFSGNormTwoCoordinatePerfect
open CFSGIntegerMatrixPairing CFSGNormTwoRootPairing
open CFSGNormTwoGeckIntegralRealization CFSGNormTwoCoordinateDominantSupport
open CFSGNormTwoCoordinateNormalSimpleRootGeneration CFSGNormTwoCoordinateNormalRootGeneration
open CFSGNormTwoCoordinateElementaryRootParameters CFSGNormTwoCoordinatePositivePairCollecting
variable {r : ℕ} (A : Matrix (Fin r) (Fin r) ℤ) (hd : ∀ i, A i i = 2)
    (hs : A.transpose = A) (hp : (rationalMatrix A).PosDef)
    (ho : ∀ i j, i ≠ j → A i j ≤ 0)
    [Fintype (Roots A)] [DecidableEq (Roots A)]
    [(rootPairing A hs hp).IsReduced] [(rootPairing A hs hp).IsIrreducible]
local notation "s₀" => coordinateIndexEquiv A hd hs hp ho

include hd hs hp ho
theorem exists_adjacent_pair [Nontrivial (Fin r)] :
    ∃ i j : Fin r, i ≠ j ∧ A i j = -1 := by
  obtain ⟨i, j, hij⟩ := exists_pair_ne (Fin r)
  by_contra hn
  push Not at hn
  have hall : ∀ a : Fin r, a = i := by
    intro a
    apply coordinate_cartan_induction A hd hs hp ho (fun b => b = i) i a rfl
    intro b c hb hcb
    subst b
    by_contra hci
    exact hn c i hci (offdiagonal_nonzero_eq_neg_one A hd hs hp ho c i hci hcb)
  exact hij ((hall j).symm)

theorem commutator_eq_top (K : Type) [Field K] [Nontrivial (Fin r)] :
    commutator (ElementaryGroup A hd hs hp ho K) = ⊤ := by
  obtain ⟨i, j, hij, hA⟩ := exists_adjacent_pair A hd hs hp ho
  let k : Roots A := s₀ i
  let l : Roots A := s₀ j
  have hk : ∀ a, 0 ≤ k.val a := by
    intro a
    change 0 ≤ (Pi.single i (1 : ℤ) : Fin r → ℤ) a
    simp only [Pi.single_apply]
    split_ifs <;> norm_num
  have hl : ∀ a, 0 ≤ l.val a := by
    intro a
    change 0 ≤ (Pi.single j (1 : ℤ) : Fin r → ℤ) a
    simp only [Pi.single_apply]
    split_ifs <;> norm_num
  have hpair : integerPairing A k.val l.val = -1 := by
    change Matrix.toBilin' A (Pi.single i (1 : ℤ)) (Pi.single j (1 : ℤ)) = -1
    rw [Matrix.toBilin'_single]
    exact hA
  obtain ⟨ε, hε, he⟩ := positive_pair_commutator_sign A hd hs hp ho k l hk hl hpair
  let z := sumRoot A hs k l hpair
  apply normal_eq_top_of_selected_root_line A hd hs hp ho K
    (commutator (ElementaryGroup A hd hs hp ho K)) z
  intro a
  let x := elementarySelectedRootHom A hd hs hp ho K k (Multiplicative.ofAdd (1 : K))
  let y := elementarySelectedRootHom A hd hs hp ho K l (Multiplicative.ofAdd ((ε : K) * a))
  have hm : x * y * x⁻¹ * y⁻¹ ∈ commutator (ElementaryGroup A hd hs hp ho K) :=
    Subgroup.commutator_mem_commutator (Subgroup.mem_top x) (Subgroup.mem_top y)
  have hcomm : x * y * x⁻¹ * y⁻¹ =
      elementarySelectedRootHom A hd hs hp ho K z (Multiplicative.ofAdd a) := by
    apply Subtype.ext
    have hcoeff : (ε : K) * (1 * ((ε : K) * a)) = a := by
      rcases hε with rfl | rfl <;> simp
    have hh := he K 1 ((ε : K) * a)
    rw [hcoeff] at hh
    exact hh
  rwa [hcomm] at hm

theorem elementary_isPerfect (K : Type) [Field K] [Nontrivial (Fin r)] :
    Group.IsPerfect (ElementaryGroup A hd hs hp ho K) :=
  ⟨commutator_eq_top A hd hs hp ho K⟩

end SymmetricSubgroupAsymptotics.CFSGNormTwoCoordinatePerfect
