import SymmetricSubgroupAsymptotics.SimpleFactorFullSubdirectCount
import SymmetricSubgroupAsymptotics.SubdirectTailImage

/-! Complete labelled subdirect count in powers of one actual centerless
simple group. Every step retains the actual tail subgroup and its full
Goursat core; proper diagonals and all automorphism twists are counted.
No partition census, group order formula or displayed generating pair is
assumed. -/
set_option autoImplicit false
noncomputable section
open scoped Classical BigOperators
namespace SymmetricSubgroupAsymptotics.SimplePowerFullSubdirectCount

variable (T : Type) [Group T] [Finite T] [IsSimpleGroup T]

local instance subgroupFinite {G : Type} [Group G] [Finite G] : Finite (Subgroup G) :=
  Finite.of_injective (fun H : Subgroup G => (H : Set G)) SetLike.coe_injective

abbrev Family (n : ℕ) :=
  {H : Subgroup (Fin n → T) // ∀ i : Fin n,Function.Surjective (fun h : H => h.val i)}

abbrev SplitFamily (n : ℕ) :=
  {H : Subgroup (T × (Fin n → T)) //
    Function.Surjective (Prod.fst ∘ H.subtype) ∧
      ∀ i : Fin n,Function.Surjective (fun h : H => h.val.2 i)}

def splitEquiv (n : ℕ) : (Fin (n+1) → T) ≃* T × (Fin n → T) where
  toFun f := (f 0,fun i => f i.succ)
  invFun x := Fin.cases x.1 x.2
  left_inv f := by
    funext i
    exact Fin.cases rfl (fun _ => rfl) i
  right_inv x := by ext <;> rfl
  map_mul' _ _ := rfl

def toSplit (n : ℕ) (H : Family T (n+1)) : SplitFamily T n := by
  let e := splitEquiv T n
  refine ⟨H.val.map e.toMonoidHom,?_,?_⟩
  · intro t
    obtain ⟨h,hh⟩ := H.property 0 t
    exact ⟨⟨e h.val,⟨h.val,h.property,rfl⟩⟩,hh⟩
  · intro i t
    obtain ⟨h,hh⟩ := H.property i.succ t
    exact ⟨⟨e h.val,⟨h.val,h.property,rfl⟩⟩,hh⟩

theorem toSplit_injective (n : ℕ) : Function.Injective (toSplit T n) := by
  intro H K h
  apply Subtype.ext
  exact Subgroup.map_injective (splitEquiv T n).injective
    (congrArg (fun z : SplitFamily T n => z.val) h)

/-- The actual tail subgroup is kept once, before any simple attachment. -/
def tailCode (n : ℕ) (H : SplitFamily T n) :
    Σ L : Family T n,FullSubdirectGoursat.Full T L.val :=
  ⟨⟨SubdirectTailImage.tail H.val,fun i =>
    SubdirectTailImage.tail_coordinate_surjective H.val (fun v => v i) (H.property.2 i)⟩,
      SubdirectTailImage.full H.val H.property.1⟩

theorem tailCode_injective (n : ℕ) : Function.Injective (tailCode T n) := by
  intro H K h
  let forget : (Σ L : Family T n,FullSubdirectGoursat.Full T L.val) →
      (Σ L : Subgroup (Fin n → T),FullSubdirectGoursat.Full T L) :=
    fun z => ⟨z.1.val,z.2⟩
  have hh : SubdirectTailImage.code (⟨H.val,H.property.1⟩ :
      SubdirectTailImage.FirstFull T (Fin n → T))=
      SubdirectTailImage.code (⟨K.val,K.property.1⟩ :
        SubdirectTailImage.FirstFull T (Fin n → T)) := congrArg forget h
  have he := SubdirectTailImage.code_injective hh
  exact Subtype.ext (congrArg
    (fun z : SubdirectTailImage.FirstFull T (Fin n → T) => z.val) he)

theorem card_succ_le (hZ : IsCenterless T) (n : ℕ) :
    Nat.card (Family T (n+1)) ≤
      Nat.card (Family T n)*(2*(1+n*Nat.card (T ≃* T))) := by
  letI : Fintype (Family T n) := Fintype.ofFinite _
  have hfull (L : Family T n) : Nat.card (FullSubdirectGoursat.Full T L.val) ≤
      2*(1+n*Nat.card (T ≃* T)) := by
    have hh := SimpleFactorFullSubdirectCount.card_full_le_of_tail_embedding
      hZ n L.val.subtype L.val.subtype_injective
    exact_mod_cast hh
  calc
    Nat.card (Family T (n+1)) ≤ Nat.card (SplitFamily T n) :=
      Nat.card_le_card_of_injective (toSplit T n) (toSplit_injective T n)
    _ ≤ Nat.card (Σ L : Family T n,FullSubdirectGoursat.Full T L.val) :=
      Nat.card_le_card_of_injective (tailCode T n) (tailCode_injective T n)
    _ = ∑ L : Family T n,Nat.card (FullSubdirectGoursat.Full T L.val) := Nat.card_sigma
    _ ≤ ∑ _L : Family T n,(2*(1+n*Nat.card (T ≃* T))) :=
      Finset.sum_le_sum (fun L _ => hfull L)
    _ = Nat.card (Family T n)*(2*(1+n*Nat.card (T ≃* T))) := by
      simp only [Finset.sum_const,Finset.card_univ,smul_eq_mul,Nat.card_eq_fintype_card]

/-- An explicit O(n log n) labelled exponent for this entire nonabelian
simple-power subdirect sector, not merely a fixed attachment fibre. -/
theorem card_family_le (hZ : IsCenterless T) (n : ℕ) :
    Nat.card (Family T n) ≤ (2*(1+n*Nat.card (T ≃* T)))^n := by
  induction n with
  | zero =>
    haveI : Subsingleton (Family T 0) := ⟨by
      intro H K
      apply Subtype.ext
      ext v
      have hv : v=1 := Subsingleton.elim _ _
      simp only [hv,Subgroup.one_mem]⟩
    have hh := Nat.card_le_card_of_injective (fun _ : Family T 0 => ())
      (fun _ _ _ => Subsingleton.elim _ _)
    have h1 : Nat.card (Family T 0) ≤ 1 := by simpa only [Nat.card_unique] using hh
    simpa only [pow_zero] using h1
  | succ n ih =>
    have hb : 2*(1+n*Nat.card (T ≃* T)) ≤ 2*(1+(n+1)*Nat.card (T ≃* T)) := by
      nlinarith only [Nat.zero_le (Nat.card (T ≃* T))]
    calc
      Nat.card (Family T (n+1)) ≤
          Nat.card (Family T n)*(2*(1+n*Nat.card (T ≃* T))) := card_succ_le T hZ n
      _ ≤ (2*(1+(n+1)*Nat.card (T ≃* T)))^n*
          (2*(1+(n+1)*Nat.card (T ≃* T))) :=
        Nat.mul_le_mul (ih.trans (Nat.pow_le_pow_left hb n)) hb
      _ = (2*(1+(n+1)*Nat.card (T ≃* T)))^(n+1) := (pow_succ _ _).symm

end SymmetricSubgroupAsymptotics.SimplePowerFullSubdirectCount
