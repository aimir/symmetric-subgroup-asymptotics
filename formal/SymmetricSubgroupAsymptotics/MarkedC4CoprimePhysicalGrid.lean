import SymmetricSubgroupAsymptotics.MarkedC4CoprimeProductCharacters
import Mathlib.GroupTheory.GroupAction.Quotient
import Mathlib.GroupTheory.QuotientGroup.Basic

/-! Concrete Cartesian grids for coprime direct factors. Splitting of
point stabilizers is proved by powers, rather than assumed as grid data. -/
set_option autoImplicit false
noncomputable section
namespace SymmetricSubgroupAsymptotics.MarkedC4.CoprimePhysicalGrid

variable {P O : Type} [Group P] [Group O] [Finite P] [Finite O]

theorem fst_mem (hcop : Nat.Coprime (Nat.card P) (Nat.card O)) (K : Subgroup (P × O)) {p : P} {o : O} (hk : (p,o)∈K) :
    (p,1)∈K := by
  have hp : Nat.Coprime (Nat.card O) (orderOf p) :=
    Nat.Coprime.of_dvd_right (orderOf_dvd_natCard p) hcop.symm
  obtain ⟨m,hm⟩ := exists_pow_eq_self_of_coprime (x := p) hp
  have hmem := K.pow_mem (K.pow_mem hk (Nat.card O)) m
  have heq : ((p,o)^(Nat.card O))^m=(p,1) := by
    apply Prod.ext
    · simpa only [Prod.pow_fst] using hm
    · simp only [Prod.pow_snd,pow_card_eq_one',one_pow]
  exact heq ▸ hmem

theorem snd_mem (hcop : Nat.Coprime (Nat.card P) (Nat.card O)) (K : Subgroup (P × O)) {p : P} {o : O} (hk : (p,o)∈K) :
    (1,o)∈K := by
  have ho : Nat.Coprime (Nat.card P) (orderOf o) :=
    Nat.Coprime.of_dvd_right (orderOf_dvd_natCard o) hcop
  obtain ⟨m,hm⟩ := exists_pow_eq_self_of_coprime (x := o) ho
  have hmem := K.pow_mem (K.pow_mem hk (Nat.card P)) m
  have heq : ((p,o)^(Nat.card P))^m=(1,o) := by
    apply Prod.ext
    · simp only [Prod.pow_fst,pow_card_eq_one',one_pow]
    · simpa only [Prod.pow_snd] using hm
  exact heq ▸ hmem

/-- A literal subgroup is recovered from its two actual coordinate images. -/
theorem subgroup_eq_product (hcop : Nat.Coprime (Nat.card P) (Nat.card O)) (K : Subgroup (P × O)) :
    K=(K.map (MonoidHom.fst P O)).prod (K.map (MonoidHom.snd P O)) := by
  apply le_antisymm
  · intro x hx
    exact ⟨⟨x,hx,rfl⟩,⟨x,hx,rfl⟩⟩
  · rintro ⟨p,o⟩ ⟨hp,ho⟩
    obtain ⟨⟨p',o'⟩,hk,hp'⟩ := hp
    obtain ⟨⟨p'',o''⟩,hl,ho'⟩ := ho
    change p'=p at hp'
    change o''=o at ho'
    have ha : (p,1)∈K := hp' ▸ fst_mem hcop K hk
    have hb : (1,o)∈K := ho' ▸ snd_mem hcop K hl
    simpa only [Prod.mk_mul_mk,mul_one,one_mul] using K.mul_mem ha hb

/-- Recovery makes the projected-subgroup code injective. -/
theorem projection_code_injective (hcop : Nat.Coprime (Nat.card P) (Nat.card O)) : Function.Injective
    (fun K : Subgroup (P × O) => (K.map (MonoidHom.fst P O),K.map (MonoidHom.snd P O))) := by
  intro K L h
  have hp := congrArg Prod.fst h
  have ho := congrArg Prod.snd h
  change K.map (MonoidHom.fst P O) = L.map (MonoidHom.fst P O) at hp
  change K.map (MonoidHom.snd P O) = L.map (MonoidHom.snd P O) at ho
  calc
    K = _ := subgroup_eq_product hcop K
    _ = _ := by rw [hp,ho]
    _ = L := (subgroup_eq_product hcop L).symm

/-- The actual orbit is a Cartesian product of the two stabilizer coset
spaces. This is the physical Sylow grid once P/O are the binary/odd factors. -/
def orbitGrid (hcop : Nat.Coprime (Nat.card P) (Nat.card O)) {X : Type} [MulAction (P × O) X] (x : X) :
    MulAction.orbit (P × O) x ≃
      (P ⧸ ((MulAction.stabilizer (P × O) x).map (MonoidHom.fst P O))) ×
      (O ⧸ ((MulAction.stabilizer (P × O) x).map (MonoidHom.snd P O))) :=
  (MulAction.orbitEquivQuotientStabilizer (P × O) x).trans
    ((Equiv.cast (congrArg (fun K : Subgroup (P × O) => (P × O) ⧸ K)
      (subgroup_eq_product hcop (MulAction.stabilizer (P × O) x)))).trans
      (QuotientGroup.prodEquiv _ _))

/-- The grid has exactly the original orbit's physical cardinality. -/
theorem orbit_card (hcop : Nat.Coprime (Nat.card P) (Nat.card O)) {X : Type} [MulAction (P × O) X] (x : X) :
    Nat.card (MulAction.orbit (P × O) x)=
      Nat.card (P ⧸ ((MulAction.stabilizer (P × O) x).map (MonoidHom.fst P O))) *
      Nat.card (O ⧸ ((MulAction.stabilizer (P × O) x).map (MonoidHom.snd P O))) := by
  rw [Nat.card_congr (orbitGrid hcop x),Nat.card_prod]

/-- Singleton coordinates consume no retained support. -/
def activeDegree (n : ℕ) : ℕ := if n=1 then 0 else n

theorem activeDegree_budget {a d : ℕ} (ha : 0<a) (hd : 0<d) :
    activeDegree a+activeDegree d≤a*d := by
  by_cases ha1 : a=1
  · subst a
    simp only [activeDegree,ite_true,zero_add,one_mul]
    split_ifs <;> omega
  by_cases hd1 : d=1
  · subst d
    simp only [activeDegree,ite_true,add_zero,mul_one]
    split_ifs <;> omega
  have ha2 : 2≤a := by omega
  have hd2 : 2≤d := by omega
  simp only [activeDegree,if_neg ha1,if_neg hd1]
  have h1 := Nat.mul_le_mul_left a hd2
  have h2 := Nat.mul_le_mul_right d ha2
  nlinarith

/-- Both retained factor supports fit inside the actual original orbit.
Dropping singleton coordinates is essential to this physical inequality. -/
theorem orbit_support_budget (hcop : Nat.Coprime (Nat.card P) (Nat.card O)) {X : Type} [MulAction (P × O) X] (x : X) :
    activeDegree (Nat.card (P ⧸ ((MulAction.stabilizer (P × O) x).map (MonoidHom.fst P O)))) +
    activeDegree (Nat.card (O ⧸ ((MulAction.stabilizer (P × O) x).map (MonoidHom.snd P O)))) ≤
      Nat.card (MulAction.orbit (P × O) x) := by
  rw [orbit_card hcop x]
  exact activeDegree_budget Nat.card_pos Nat.card_pos

end SymmetricSubgroupAsymptotics.MarkedC4.CoprimePhysicalGrid
