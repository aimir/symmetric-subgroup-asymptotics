import SymmetricSubgroupAsymptotics.PrimeSubdirectNormalRank
import SymmetricSubgroupAsymptotics.PrimeRelativeRadicalPresentation
import Mathlib.GroupTheory.Subgroup.Centralizer

/-! One literal centralizer bounds the relative heads of every original
normal subgroup inside a given subgroup. The commutator map is only a set
map: its fibres are centralizer cosets, even for nonabelian groups. No
enumeration, p-group hypothesis or homomorphism claim for that map is used.
-/
set_option autoImplicit false
noncomputable section
open scoped commutatorElement

namespace SymmetricSubgroupAsymptotics

variable {G : Type*} [Group G]

private theorem inv_mul_mem_centralizer_of_commutator_eq
    {a b g : G} (h : ⁅a,g⁆ = ⁅b,g⁆) :
    b⁻¹*a ∈ Subgroup.centralizer ({g} : Set G) := by
  have hc : a*g*a⁻¹ = b*g*b⁻¹ := by
    simpa only [commutatorElement_def, mul_assoc, inv_mul_cancel, mul_one] using
      congrArg (fun x : G => x*g) h
  apply Subgroup.mem_centralizer_singleton_iff.mpr
  calc
    (b⁻¹*a)*g = b⁻¹*(a*g*a⁻¹)*a := by group
    _ = b⁻¹*(b*g*b⁻¹)*a := by rw [hc]
    _ = g*(b⁻¹*a) := by group

variable (p : ℕ) [Fact p.Prime] [Finite G]

/-- Representatives of actual commutator fibres give an injection into
the actual radical times the literal centralizer intersection. The map
m ↦ [m,g] is not assumed to be a group homomorphism. -/
theorem primeRelativeHead_pow_le_centralizer_card
    (N : Subgroup G) [N.Normal] (g : G) :
    p ^ Module.finrank (ZMod p) (primeRelativeCharacters p N) ≤
      Nat.card ↥(N ⊓ Subgroup.centralizer ({g} : Set G)) := by
  let R := primeRelativeRadical p N
  let C := N ⊓ Subgroup.centralizer ({g} : Set G)
  let f : N → R := fun n =>
    ⟨⁅(n : G),g⁆, commutator_mem_primeRelativeRadical p N n g⟩
  let rep : R → N := Function.invFun f
  have hrep (n : N) : f (rep (f n)) = f n :=
    Function.invFun_eq ⟨n,rfl⟩
  let diff (n : N) : N := (rep (f n))⁻¹*n
  have hdiff (n : N) : (diff n : G) ∈ Subgroup.centralizer ({g} : Set G) := by
    have he : ⁅(n : G),g⁆ = ⁅(rep (f n) : G),g⁆ :=
      congrArg Subtype.val (hrep n).symm
    exact inv_mul_mem_centralizer_of_commutator_eq he
  let code : N → R × C := fun n =>
    (f n, ⟨(diff n : G), ⟨(diff n).2, hdiff n⟩⟩)
  have hinj : Function.Injective code := by
    intro a b he
    have hfirst : f a = f b := congrArg Prod.fst he
    have hsecond : (diff a : G) = (diff b : G) :=
      congrArg (fun z : R × C => (z.2 : G)) he
    have hd : diff a = diff b := Subtype.ext hsecond
    change (rep (f a))⁻¹*a = (rep (f b))⁻¹*b at hd
    rw [hfirst] at hd
    exact mul_left_cancel hd
  have hcard : Nat.card N ≤ Nat.card R * Nat.card C := by
    simpa only [Nat.card_prod] using Nat.card_le_card_of_injective code hinj
  have hfactor : Nat.card N =
      p ^ Module.finrank (ZMod p) (primeRelativeCharacters p N) * Nat.card R :=
    primeRelativeRadical_card_factorization p N
  rw [hfactor, Nat.mul_comm
    (p ^ Module.finrank (ZMod p) (primeRelativeCharacters p N)) (Nat.card R)] at hcard
  exact Nat.le_of_mul_le_mul_left hcard Nat.card_pos

/-- The maximum ranges over all original G-normal subgroups inside S.
The same single original conjugator is used for every one of them. -/
theorem primeNormalHeadMax_pow_le_centralizer_card
    (S : Subgroup G) (g : G) :
    p ^ primeNormalHeadMax p S ≤
      Nat.card ↥(S ⊓ Subgroup.centralizer ({g} : Set G)) := by
  obtain ⟨M,hM⟩ := primeNormalHeadMax_attained p S
  letI : M.1.Normal := M.2.1
  have h := primeRelativeHead_pow_le_centralizer_card p M.1 g
  change p ^ primeNormalHeadValue p M ≤
    Nat.card ↥(M.1 ⊓ Subgroup.centralizer ({g} : Set G)) at h
  rw [hM] at h
  exact h.trans (Subgroup.card_le_of_le (inf_le_inf M.2.2 le_rfl))

/-- A checked upper bound on one actual centralizer replaces all-normal
rank enumeration. No numerical head bound is supplied as a premise. -/
theorem primeNormalHeadMax_le_of_centralizer_card_le
    (S : Subgroup G) (g : G) (r : ℕ)
    (hcard : Nat.card ↥(S ⊓ Subgroup.centralizer ({g} : Set G)) ≤ p^r) :
    primeNormalHeadMax p S ≤ r :=
  (Nat.pow_le_pow_iff_right (Fact.out : p.Prime).one_lt).mp
    ((primeNormalHeadMax_pow_le_centralizer_card p S g).trans hcard)

/-- In particular, one original centralizer inside the actual derived
subgroup controls the complete original derived-normal rank. -/
theorem primeDerivedNormalRank_le_of_centralizer_card_le
    (g : G) (r : ℕ)
    (hcard : Nat.card ↥(commutator G ⊓ Subgroup.centralizer ({g} : Set G)) ≤ p^r) :
    primeDerivedNormalRank p G ≤ r :=
  primeNormalHeadMax_le_of_centralizer_card_le p (commutator G) g r hcard

end SymmetricSubgroupAsymptotics
