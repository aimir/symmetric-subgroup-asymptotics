import Mathlib.Algebra.Group.Conj
import Mathlib.Algebra.Group.Subgroup.Basic
import Mathlib.SetTheory.Cardinal.Finite
import Mathlib.Tactic.FinCases

/-! A finite selected conjugacy orbit, not a group-element census.
Every row has an actual original-group conjugating word. Four transitions
certify closure under two actual generators and their inverses. Generation
then proves that this is the entire original conjugacy class. -/
set_option autoImplicit false
noncomputable section
namespace SymmetricSubgroupAsymptotics.FiniteGeneratedConjugacyOrbitCertificate

variable {G : Type*} [Group G] {m : ℕ}

def signedGenerator (x y : G) (s : Fin 4) : G :=
  match s.val with
  | 0 => x
  | 1 => x⁻¹
  | 2 => y
  | _ => y⁻¹

structure Certificate (x y representative : G) (rows : Fin m → G) where
  base : Fin m
  base_eq : rows base = representative
  conjugator : Fin m → G
  origins : ∀ i, rows i = conjugator i * representative * (conjugator i)⁻¹
  nextIndex : Fin 4 → Fin m → Fin m
  transitions : ∀ s i, rows (nextIndex s i) =
    signedGenerator x y s * rows i * (signedGenerator x y s)⁻¹

private def Preserves (rows : Fin m → G) (g : G) : Prop :=
  ∀ z, z ∈ Set.range rows → g*z*g⁻¹ ∈ Set.range rows

private theorem preserves_mul (rows : Fin m → G) (g h : G)
    (hg : Preserves rows g) (hh : Preserves rows h) : Preserves rows (g*h) := by
  intro z hz
  have h := hg _ (hh z hz)
  simpa only [mul_inv_rev, mul_assoc] using h

private def preservingSubgroup (rows : Fin m → G) : Subgroup G where
  carrier := {g | Preserves rows g ∧ Preserves rows g⁻¹}
  one_mem' := by
    constructor <;> intro z hz <;> simpa only [inv_one,one_mul,mul_one] using hz
  mul_mem' := by
    intro g h hg hh
    exact ⟨preserves_mul rows g h hg.1 hh.1,
      by simpa only [mul_inv_rev] using preserves_mul rows h⁻¹ g⁻¹ hh.2 hg.2⟩
  inv_mem' := by
    intro g hg
    exact ⟨hg.2, by simpa only [inv_inv] using hg.1⟩

variable {x y representative : G} {rows : Fin m → G}

theorem row_isConj (C : Certificate x y representative rows) (i : Fin m) :
    IsConj (rows i) representative := by
  apply IsConj.symm
  apply isConj_iff.mpr
  exact ⟨C.conjugator i,(C.origins i).symm⟩

theorem covers (C : Certificate x y representative rows)
    (hgen : Subgroup.closure ({x,y} : Set G) = ⊤)
    (z : G) (hz : IsConj z representative) : ∃ i, rows i = z := by
  have step (s : Fin 4) : Preserves rows (signedGenerator x y s) := by
    intro v hv
    obtain ⟨i,rfl⟩ := hv
    exact ⟨C.nextIndex s i,C.transitions s i⟩
  have hx : x ∈ preservingSubgroup rows := by
    exact ⟨step 0,step 1⟩
  have hy : y ∈ preservingSubgroup rows := by
    exact ⟨step 2,step 3⟩
  have htop : (⊤ : Subgroup G) ≤ preservingSubgroup rows := by
    rw [←hgen]
    apply (Subgroup.closure_le _).mpr
    rintro v (rfl | rfl)
    · exact hx
    · exact hy
  obtain ⟨g,hg⟩ := isConj_iff.mp hz.symm
  have hmem := (htop (Subgroup.mem_top g)).1 representative ⟨C.base,C.base_eq⟩
  rw [hg] at hmem
  exact hmem

def classMap (C : Certificate x y representative rows) (i : Fin m) :
    {z : G // IsConj z representative} := ⟨rows i,row_isConj C i⟩

theorem class_card_le (C : Certificate x y representative rows)
    (hgen : Subgroup.closure ({x,y} : Set G) = ⊤) :
    Nat.card {z : G // IsConj z representative} ≤ m := by
  have hs : Function.Surjective (classMap C) := by
    intro z
    obtain ⟨i,hi⟩ := covers C hgen z.val z.property
    exact ⟨i,Subtype.ext hi⟩
  simpa only [Nat.card_fin] using Nat.card_le_card_of_surjective (classMap C) hs

theorem class_card_eq (C : Certificate x y representative rows)
    (hgen : Subgroup.closure ({x,y} : Set G) = ⊤)
    (hinj : Function.Injective rows) :
    Nat.card {z : G // IsConj z representative} = m := by
  have hs : Function.Surjective (classMap C) := by
    intro z
    obtain ⟨i,hi⟩ := covers C hgen z.val z.property
    exact ⟨i,Subtype.ext hi⟩
  have hi : Function.Injective (classMap C) := by
    intro i j hij
    exact hinj (congrArg Subtype.val hij)
  exact (Nat.card_congr (Equiv.ofBijective (classMap C) ⟨hi,hs⟩)).symm.trans (Nat.card_fin m)

end SymmetricSubgroupAsymptotics.FiniteGeneratedConjugacyOrbitCertificate
