import SymmetricSubgroupAsymptotics.AutomorphismCyclicRestrictionCardinality
import SymmetricSubgroupAsymptotics.SimplePrimeSylowSuccessorIndexSquare

/-! One fixed-generator outer inequality for any actual prime-order
Sylow subgroup in a finite nonabelian simple source. No finite capacity
or named-group metadata is assumed. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
open scoped Classical Pointwise
namespace SymmetricSubgroupAsymptotics.PrimeCyclicSylowFixedFibreOuterBound
open PrimitiveSocleRawStructure OuterFixedElementEvaluationBound

variable {G : Type} [Group G] [Finite G] {p : ℕ} [Fact p.Prime]

def preservingAutomorphisms (P : Sylow p G) : Subgroup (MulAut G) :=
  MulAction.stabilizer (MulAut G) P

theorem normalize_sylow (P : Sylow p G) (f : MulAut G) :
    ∃ g : G, MulAut.conj g * f ∈ preservingAutomorphisms P := by
  obtain ⟨g,hg⟩ := MulAction.exists_smul_eq G (f • P) P
  refine ⟨g,?_⟩
  change (MulAut.conj g * f) • P = P
  rw [mul_smul]
  exact hg

theorem outer_mul_normalizer_eq_preserving [IsSimpleGroup G]
    (hn : ¬IsMulCommutative G) (P : Sylow p G) :
    Nat.card (Outer G) * Nat.card (Subgroup.normalizer (P : Set G)) =
      Nat.card (preservingAutomorphisms P) := by
  exact OuterAutomorphismSubgroupExactCardinality.outer_mul_subgroup_eq_automorphism_subgroup
    (preservingAutomorphisms P) (Subgroup.normalizer (P : Set G))
    (CFSGOuterCardinalityCancellation.conj_injective hn) (normalize_sylow P)
    (fun _ => Sylow.smul_eq_iff_mem_normalizer)

theorem preserving_card_le_fixed_mul_pred (P : Sylow p G) (hcard : Nat.card P = p)
    (a : G) (hgen : (P : Subgroup G) = Subgroup.zpowers a) :
    Nat.card (preservingAutomorphisms P) ≤
      Nat.card (fixedAutomorphisms a) * (p-1) := by
  have hpreserve : ∀ f : preservingAutomorphisms P, ∀ z : P,
      f.val z.val ∈ (P : Subgroup G) := by
    intro f z
    have hm := Subgroup.smul_mem_pointwise_smul z.val f.val (P : Subgroup G) z.property
    have he : f.val • (P : Subgroup G) = (P : Subgroup G) :=
      congrArg (fun Q : Sylow p G => (Q : Subgroup G)) f.property
    rwa [he] at hm
  have hfixed : fixedAutomorphisms a ≤ preservingAutomorphisms P := by
    intro f hf
    change f • P = P
    apply Sylow.ext
    change f • (P : Subgroup G) = (P : Subgroup G)
    rw [hgen]
    change (Subgroup.zpowers a).map f.toMonoidHom = Subgroup.zpowers a
    rw [MonoidHom.map_zpowers]
    change Subgroup.zpowers (f a) = Subgroup.zpowers a
    rw [show f a = a from hf]
  have hh := AutomorphismCyclicRestrictionCardinality.card_le_fixed_mul_aut
    (preservingAutomorphisms P) (P : Subgroup G) a hgen hpreserve hfixed
  letI : IsCyclic P := isCyclic_of_prime_card hcard
  have hAut : Nat.card (MulAut (P : Subgroup G)) = p-1 := by
    rw [IsCyclic.card_mulAut,hcard,Nat.totient_prime Fact.out]
  rw [hAut] at hh
  exact hh

theorem twice_prime_mul_outer_le_pred_mul_fixed [IsSimpleGroup G]
    (hn : ¬IsMulCommutative G) (P : Sylow p G) (hcard : Nat.card P = p)
    (a : G) (hgen : (P : Subgroup G) = Subgroup.zpowers a) :
    (2*p) * Nat.card (Outer G) ≤ (p-1) * Nat.card (fixedAutomorphisms a) := by
  have hN := SimplePrimeSylowSuccessorIndexSquare.normalizer_card_ge_twice_prime hn P hcard
  have he := outer_mul_normalizer_eq_preserving hn P
  have hh := preserving_card_le_fixed_mul_pred P hcard a hgen
  calc
    (2*p) * Nat.card (Outer G) ≤
        Nat.card (Subgroup.normalizer (P : Set G)) * Nat.card (Outer G) :=
      Nat.mul_le_mul_right _ hN
    _ = Nat.card (preservingAutomorphisms P) := by simpa only [Nat.mul_comm] using he
    _ ≤ Nat.card (fixedAutomorphisms a) * (p-1) := hh
    _ = (p-1) * Nat.card (fixedAutomorphisms a) := Nat.mul_comm _ _

end SymmetricSubgroupAsymptotics.PrimeCyclicSylowFixedFibreOuterBound
