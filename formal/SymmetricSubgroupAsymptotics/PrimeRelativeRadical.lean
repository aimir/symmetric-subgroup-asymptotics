import SymmetricSubgroupAsymptotics.PrimeCharacterSubgroupCapacity
import SymmetricSubgroupAsymptotics.PrimeRelativeCharacters

/-! The relative-character radical is an actual subgroup of the original
normal subgroup, embedded in the original ambient group. Evaluation is onto
its literal dual character space, and its kernel is stable under the whole
ambient conjugation action. No order or rank estimate is assumed. -/
set_option autoImplicit false
noncomputable section

namespace SymmetricSubgroupAsymptotics

variable (p : ℕ) [Fact p.Prime]
    {G : Type*} [Group G] (N : Subgroup G) [N.Normal]

/-- Evaluation of elements of the original N on all G-invariant characters. -/
def primeRelativeEvaluation : N →*
    Multiplicative (Module.Dual (ZMod p) (primeRelativeCharacters p N)) :=
  retainedCharacterEvaluation p (primeRelativeCharacters p N).subtype

@[simp] theorem primeRelativeEvaluation_apply
    (n : N) (χ : primeRelativeCharacters p N) :
    (primeRelativeEvaluation p N n).toAdd χ=χ.1 (Additive.ofMul n) := rfl

theorem primeRelativeEvaluation_surjective [Finite G] :
    Function.Surjective (primeRelativeEvaluation p N) := by
  intro x
  obtain ⟨y,hy⟩ := LinearMap.dualMap_surjective_of_injective
    (show Function.Injective (primeRelativeCharacters p N).subtype from
      Subtype.val_injective) x.toAdd
  obtain ⟨n,hn⟩ := primeAbelianizationMap_surjective p N y
  refine ⟨n.toMul,?_⟩
  apply Multiplicative.toAdd.injective
  change (primeRelativeCharacters p N).subtype.dualMap
    (primeAbelianizationMap p N n)=x.toAdd
  rw [hn]
  exact hy

/-- The exact evaluation kernel as a subgroup of N. -/
def primeRelativeRadicalKernel : Subgroup N := (primeRelativeEvaluation p N).ker

/-- The same literal kernel, embedded in the original ambient group G. -/
def primeRelativeRadical : Subgroup G := (primeRelativeRadicalKernel p N).map N.subtype

theorem mem_primeRelativeRadicalKernel_iff (n : N) :
    n ∈ primeRelativeRadicalKernel p N ↔
      ∀ χ : primeRelativeCharacters p N, χ.1 (Additive.ofMul n)=0 := by
  constructor
  · intro hn χ
    exact congrArg
      (fun a : Multiplicative (Module.Dual (ZMod p) (primeRelativeCharacters p N)) => a.toAdd χ)
      (show primeRelativeEvaluation p N n=1 from hn)
  · intro hn
    change primeRelativeEvaluation p N n=1
    apply Multiplicative.toAdd.injective
    ext χ
    exact hn χ

/-- Conjugation by every original ambient element fixes evaluation. -/
theorem primeRelativeEvaluation_conjugate (g : G) (n : N) :
    primeRelativeEvaluation p N
      (⟨g*(n : G)*g⁻¹,Subgroup.Normal.conj_mem inferInstance _ n.2 g⟩ : N) =
      primeRelativeEvaluation p N n := by
  apply Multiplicative.toAdd.injective
  ext χ
  exact χ.2 g n

theorem primeRelativeRadical_le : primeRelativeRadical p N ≤ N := by
  rintro x ⟨n,hn,rfl⟩
  exact n.2

theorem mem_primeRelativeRadical_iff (x : G) :
    x ∈ primeRelativeRadical p N ↔
      ∃ hx : x ∈ N, ∀ χ : primeRelativeCharacters p N,
        χ.1 (Additive.ofMul (⟨x,hx⟩ : N))=0 := by
  constructor
  · rintro ⟨n,hn,rfl⟩
    exact ⟨n.2,(mem_primeRelativeRadicalKernel_iff p N n).mp hn⟩
  · rintro ⟨hx,hχ⟩
    exact ⟨⟨x,hx⟩,(mem_primeRelativeRadicalKernel_iff p N ⟨x,hx⟩).mpr hχ,rfl⟩

@[simp] theorem coe_mem_primeRelativeRadical_iff (n : N) :
    (n : G) ∈ primeRelativeRadical p N ↔ n ∈ primeRelativeRadicalKernel p N := by
  constructor
  · rintro ⟨m,hm,he⟩
    have hmn : m=n := Subtype.ext he
    exact hmn ▸ hm
  · exact fun hn => ⟨n,hn,rfl⟩

/-- Normality holds in all of G, not only in N. -/
instance primeRelativeRadical_normal : (primeRelativeRadical p N).Normal := ⟨by
  rintro x ⟨n,hn,rfl⟩ g
  refine ⟨⟨g*(n : G)*g⁻¹,Subgroup.Normal.conj_mem inferInstance _ n.2 g⟩,?_,rfl⟩
  change primeRelativeEvaluation p N
    (⟨g*(n : G)*g⁻¹,Subgroup.Normal.conj_mem inferInstance _ n.2 g⟩ : N)=1
  rw [primeRelativeEvaluation_conjugate]
  exact hn⟩

/-- This equivalence is the original subgroup inclusion on every element. -/
def primeRelativeRadicalEquiv : primeRelativeRadicalKernel p N ≃*
    primeRelativeRadical p N :=
  (primeRelativeRadicalKernel p N).equivMapOfInjective N.subtype N.subtype_injective

@[simp] theorem primeRelativeRadicalEquiv_coe (r : primeRelativeRadicalKernel p N) :
    (primeRelativeRadicalEquiv p N r : G)=((r : N) : G) := rfl

/-- Every retained character annihilates the whole actual radical. -/
theorem primeRelativeRadicalKernel_le_character_ker (χ : primeRelativeCharacters p N) :
    primeRelativeRadicalKernel p N ≤ (AddMonoidHom.toMultiplicativeRight χ.1).ker := by
  intro n hn
  change χ.1 (Additive.ofMul n)=0
  exact (mem_primeRelativeRadicalKernel_iff p N n).mp hn χ

theorem primeRelativeRadical_le_mapped_character_ker (χ : primeRelativeCharacters p N) :
    primeRelativeRadical p N ≤
      ((AddMonoidHom.toMultiplicativeRight χ.1).ker).map N.subtype :=
  Subgroup.map_mono (primeRelativeRadicalKernel_le_character_ker p N χ)

/-- In particular, restriction of any original ambient character vanishes on R. -/
theorem primeRelativeRadical_le_ambient_character_ker (χ : PrimeCharacters p G) :
    primeRelativeRadical p N ≤ (AddMonoidHom.toMultiplicativeRight χ).ker := by
  rintro x ⟨n,hn,rfl⟩
  change χ (Additive.ofMul (n : G))=0
  exact (mem_primeRelativeRadicalKernel_iff p N n).mp hn (primeCharacterRestriction p N χ)

theorem primeRelativeRadical_le_ambient_evaluation_ker :
    primeRelativeRadical p N ≤ (primeAbelianizationGroupMap p G).ker := by
  intro x hx
  change primeAbelianizationMap p G (Additive.ofMul x)=0
  ext χ
  exact primeRelativeRadical_le_ambient_character_ker p N χ hx

/-- The actual relative quotient has exactly the order of its dual space. -/
theorem primeRelativeRadical_quotient_card [Finite G] :
    Nat.card (N ⧸ primeRelativeRadicalKernel p N) =
      p ^ Module.finrank (ZMod p) (primeRelativeCharacters p N) := by
  change Nat.card (N ⧸ (primeRelativeEvaluation p N).ker) =
    p ^ Module.finrank (ZMod p) (primeRelativeCharacters p N)
  rw [Nat.card_congr (QuotientGroup.quotientKerEquivOfSurjective
    (primeRelativeEvaluation p N) (primeRelativeEvaluation_surjective p N)).toEquiv]
  change Nat.card (Module.Dual (ZMod p) (primeRelativeCharacters p N)) = _
  rw [Module.natCard_eq_pow_finrank (K := ZMod p),Subspace.dual_finrank_eq,Nat.card_zmod]

/-- Exact order factorization uses R as an actual subgroup of the original G. -/
theorem primeRelativeRadical_card_factorization [Finite G] :
    Nat.card N = p ^ Module.finrank (ZMod p) (primeRelativeCharacters p N) *
      Nat.card (primeRelativeRadical p N) := by
  have hR : Nat.card (primeRelativeRadicalKernel p N)=Nat.card (primeRelativeRadical p N) :=
    Nat.card_congr (primeRelativeRadicalEquiv p N).toEquiv
  calc
    _ = Nat.card (N ⧸ primeRelativeRadicalKernel p N) *
        Nat.card (primeRelativeRadicalKernel p N) :=
      Subgroup.card_eq_card_quotient_mul_card_subgroup (primeRelativeRadicalKernel p N)
    _ = _ := by rw [primeRelativeRadical_quotient_card,hR]

end SymmetricSubgroupAsymptotics
