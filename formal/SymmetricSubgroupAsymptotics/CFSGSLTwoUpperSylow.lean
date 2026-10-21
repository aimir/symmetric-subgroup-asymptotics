import SymmetricSubgroupAsymptotics.CFSGSLTwoUpperRoots
import Mathlib.FieldTheory.Finite.Basic
import Mathlib.Algebra.Group.TypeTags.Finite
import Mathlib.GroupTheory.Sylow

/-! The actual upper-root subgroup is Sylow in defining characteristic.
The proof uses a nonzero fixed vector of a finite p-group, rather than
assuming the order of SL₂ or a Borel index formula. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
open scoped Classical
namespace SymmetricSubgroupAsymptotics.CFSGSLTwoUpperSylow
open Matrix CFSGTypeASLTwoWeyl CFSGSLTwoUpperRoots
variable {F : Type*} [Field F] [Finite F] {p : ℕ} [Fact p.Prime] [CharP F p]

omit [Fact p.Prime] in
theorem upperRoot_isPGroup : IsPGroup p (upperRoot (F:=F)) := by
  letI : Fintype F := Fintype.ofFinite F
  obtain ⟨n,_hp,hn⟩ := FiniteField.card F p
  have hAdd : IsPGroup p (Multiplicative F) := IsPGroup.of_card (n := n.val) (by
    simpa only [Nat.card_eq_fintype_card,Fintype.card_multiplicative] using hn)
  exact hAdd.of_surjective (upperHom (F:=F)).rangeRestrict
    (upperHom (F:=F)).rangeRestrict_surjective

theorem upperRoot_maximal (Q : Subgroup (SL2 (F:=F)))
    (hQ : IsPGroup p Q) (hUQ : upperRoot (F:=F) ≤ Q) : Q=upperRoot (F:=F) := by
  letI : Fintype F := Fintype.ofFinite F
  obtain ⟨n,_hp,hn⟩ := FiniteField.card F p
  have hpF : p ∣ Nat.card F := by
    rw [Nat.card_eq_fintype_card,hn]
    exact dvd_pow_self p (ne_of_gt n.property)
  have hcard : p ∣ Nat.card (Fin 2 → F) := by
    rw [Nat.card_fun,Nat.card_fin]
    exact hpF.trans (dvd_pow_self (Nat.card F) (by decide : 2≠0))
  have hzero : (0 : Fin 2 → F)∈MulAction.fixedPoints Q (Fin 2 → F) := by
    intro g
    exact smul_zero g
  obtain ⟨v,hv,hvne⟩ :=
    hQ.exists_fixed_point_of_prime_dvd_card_of_fixed_point (Fin 2 → F) hcard hzero
  have hu := congrFun (hv ⟨upper (1 : F),hUQ (upper_mem 1)⟩) 0
  change ((upper (1 : F)).val.mulVec v) 0=v 0 at hu
  simp only [Matrix.mulVec,dotProduct,Fin.sum_univ_two] at hu
  simp only [upper_entry00,upper_entry01,one_mul] at hu
  have hv1 : v 1=0 := add_eq_left.mp hu
  have hv0 : v 0≠0 := by
    intro hz
    apply hvne
    funext i
    fin_cases i <;> simp_all
  apply le_antisymm _ hUQ
  intro g hg
  have hfix := hv ⟨g,hg⟩
  have he0 := congrFun hfix 0
  have he1 := congrFun hfix 1
  change (g.val.mulVec v) 0=v 0 at he0
  change (g.val.mulVec v) 1=v 1 at he1
  simp only [Matrix.mulVec,dotProduct,Fin.sum_univ_two] at he0 he1
  simp only [hv1,mul_zero,add_zero] at he0 he1
  have hg00 : g.val 0 0=1 := mul_right_cancel₀ hv0 (he0.trans (one_mul (v 0)).symm)
  have hg10 : g.val 1 0=0 := (mul_eq_zero.mp he1).resolve_right hv0
  have hg11 : g.val 1 1=1 := by
    have hd := g.property
    simpa only [Matrix.det_fin_two,hg00,hg10,one_mul,mul_zero,sub_zero] using hd
  exact (mem_upperRoot_iff g).mpr ⟨hg00,hg10,hg11⟩

def upperSylow : Sylow p (SL2 (F:=F)) where
  toSubgroup := upperRoot
  isPGroup' := upperRoot_isPGroup
  is_maximal' := fun {Q} hQ hUQ => upperRoot_maximal Q hQ hUQ

@[simp] theorem upperSylow_coe :
    (upperSylow (F:=F) (p:=p) : Subgroup (SL2 (F:=F)))=upperRoot := rfl

end SymmetricSubgroupAsymptotics.CFSGSLTwoUpperSylow
