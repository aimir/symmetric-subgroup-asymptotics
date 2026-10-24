import SymmetricSubgroupAsymptotics.CoprimeNilpotentProductGenerators
import SymmetricSubgroupAsymptotics.PermutationPGroupOrdinaryGenerators
import Mathlib.GroupTheory.Nilpotent

/-! The ordinary-generator half-degree bound for every finite nilpotent
permutation group.  Its literal Sylow factors each act faithfully on the
same point set; coprime sharing combines their costs by a maximum.
This does not assert the all-subgroup McIver--Neumann input. -/
set_option autoImplicit false
noncomputable section
namespace SymmetricSubgroupAsymptotics.PermutationNilpotentOrdinaryGenerators
open CoprimeNilpotentProductGenerators

/-- Actual finite nilpotent Sylow decomposition transports a common
ordinary-generator bound on its Sylows to the original group. -/
theorem genRank_le_of_sylow_bounds (G : Type) [Group G] [Finite G]
    [Group.IsNilpotent G] (d : ℕ)
    (hbound : ∀(p : ℕ) [Fact p.Prime] (P : Sylow p G),MarkedC4.genRank P≤d) :
    MarkedC4.genRank G≤d := by
  classical
  let ps := (Nat.card G).primeFactors
  let P : ∀p:ps,Sylow p G := default
  have hn : ∀{p : ℕ} [Fact p.Prime] (Q : Sylow p G),Q.Normal := by
    intro p _ Q
    exact Sylow.normal_of_normalizerCondition Group.normalizerCondition_of_isNilpotent Q
  let E : (∀p:ps,∀Q:Sylow p G,Q)≃*(∀p:ps,P p) := by
    apply MulEquiv.piCongrRight
    intro p
    letI : Fact (p.val.Prime) := ⟨Nat.prime_of_mem_primeFactors p.property⟩
    letI := Sylow.unique_of_normal (P p) (hn (P p))
    exact MulEquiv.piUnique (fun Q:Sylow p G=>Q)
  let e : (∀p:ps,P p)≃*G := E.symm.trans (Sylow.directProductOfNormal hn)
  have hcop : Pairwise (fun p q:ps=>(Nat.card (P p)).Coprime (Nat.card (P q))) := by
    intro p q hpq
    letI : Fact (p.val.Prime) := ⟨Nat.prime_of_mem_primeFactors p.property⟩
    letI : Fact (q.val.Prime) := ⟨Nat.prime_of_mem_primeFactors q.property⟩
    exact IsPGroup.coprime_card_of_ne p.val q.val
      (fun h=>hpq (Subtype.ext h)) (P p).toSubgroup (P q).toSubgroup
      (P p).isPGroup' (P q).isPGroup'
  have hrank : ∀p:ps,MarkedC4.genRank (P p)≤d := by
    intro p
    letI : Fact (p.val.Prime) := ⟨Nat.prime_of_mem_primeFactors p.property⟩
    exact hbound p.val (P p)
  rw [←genRank_mulEquiv e]
  exact genRank_pi_le (fun p:ps=>P p) hcop d hrank

theorem genRank_le_half_degree (G X : Type) [Group G] [Finite G]
    [Group.IsNilpotent G] [Finite X] [MulAction G X] [FaithfulSMul G X] :
    MarkedC4.genRank G≤Nat.card X/2 := by
  apply genRank_le_of_sylow_bounds G (Nat.card X/2)
  intro p _ P
  obtain ⟨S,hgen,hcard⟩ :=
    PermutationPGroupOrdinaryGenerators.exists_half_degree_generators p P X P.isPGroup'
  exact (MarkedC4.genRank_le hgen).trans
    ((Nat.le_div_iff_mul_le (by decide : 0<2)).mpr
      (by simpa only [Nat.mul_comm] using hcard))

theorem exists_half_degree_generators (G X : Type) [Group G] [Finite G]
    [Group.IsNilpotent G] [Finite X] [MulAction G X] [FaithfulSMul G X] :
    ∃S:Finset G,Subgroup.closure (S:Set G)=⊤ ∧ 2*S.card≤Nat.card X := by
  obtain ⟨S,hS,hgen⟩ := MarkedC4.genRank_spec (G:=G)
  refine ⟨S,hgen,?_⟩
  calc
    2*S.card≤2*(Nat.card X/2) :=
      Nat.mul_le_mul_left 2 (hS.le.trans (genRank_le_half_degree G X))
    _≤Nat.card X := Nat.mul_div_le _ _

theorem subgroup_half_degree_generators (n : ℕ) (J : Subgroup (Equiv.Perm (Fin n)))
    [Group.IsNilpotent J] :
    ∃S:Finset J,Subgroup.closure (S:Set J)=⊤ ∧ 2*S.card≤n := by
  simpa only [Nat.card_fin] using exists_half_degree_generators J (Fin n)

end SymmetricSubgroupAsymptotics.PermutationNilpotentOrdinaryGenerators
