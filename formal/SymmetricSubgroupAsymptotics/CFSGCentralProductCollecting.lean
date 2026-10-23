import Mathlib.Algebra.BigOperators.Group.List.Basic
import Mathlib.Algebra.Group.TypeTags.Hom
import Mathlib.Tactic.Group

/-! Exact ordered-product collecting with a literal additive central
parameter. These two elementary list inductions preserve every parameter
and require no exponential, BCH identity or division. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
namespace SymmetricSubgroupAsymptotics.CFSGCentralProductCollecting
variable {J K G:Type*}[AddCommGroup K][Group G]
variable (Z:Multiplicative K→*G)(f:J→G)

private theorem word_commute (c:K) (h:∀i,Commute (f i) (Z (Multiplicative.ofAdd c)))
    (l:List J) : Commute ((l.map f).prod) (Z (Multiplicative.ofAdd c)) := by
  induction l with
  | nil => exact Commute.one_left _
  | cons i l ih => exact (h i).mul_left ih

theorem conjugate_word (g:G)(t:J→K)
    (hcentral:∀i c,Commute (f i) (Z (Multiplicative.ofAdd c)))
    (h:∀i,g*f i*g⁻¹=f i*Z (Multiplicative.ofAdd (t i)))
    (l:List J) : g*(l.map f).prod*g⁻¹=(l.map f).prod*Z (Multiplicative.ofAdd (l.map t).sum) := by
  induction l with
  | nil => simp
  | cons i l ih =>
    simp only [List.map_cons,List.prod_cons,List.sum_cons]
    have hc:=word_commute Z f (t i) (fun j=>hcentral j (t i)) l
    calc
      _=(g*f i*g⁻¹)*(g*(l.map f).prod*g⁻¹) := by group
      _=(f i*Z (Multiplicative.ofAdd (t i)))*((l.map f).prod*Z (Multiplicative.ofAdd (l.map t).sum)) := by rw [h i,ih]
      _=f i*(Z (Multiplicative.ofAdd (t i))*(l.map f).prod)*Z (Multiplicative.ofAdd (l.map t).sum) := by group
      _=f i*((l.map f).prod*Z (Multiplicative.ofAdd (t i)))*Z (Multiplicative.ofAdd (l.map t).sum) := by rw [hc.eq]
      _=(f i*(l.map f).prod)*(Z (Multiplicative.ofAdd (t i))*Z (Multiplicative.ofAdd (l.map t).sum)) := by group
      _=_ := by rw [←map_mul];rfl

theorem word_conjugate (x:G)(t:J→K)
    (hcentral:∀i c,Commute (f i) (Z (Multiplicative.ofAdd c)))
    (h:∀i,f i*x*(f i)⁻¹=x*Z (Multiplicative.ofAdd (t i)))
    (l:List J) : (l.map f).prod*x*((l.map f).prod)⁻¹=x*Z (Multiplicative.ofAdd (l.map t).sum) := by
  induction l with
  | nil => simp
  | cons i l ih =>
    simp only [List.map_cons,List.prod_cons,List.sum_cons]
    have hc:=hcentral i (l.map t).sum
    calc
      _=f i*((l.map f).prod*x*((l.map f).prod)⁻¹)*(f i)⁻¹ := by group
      _=f i*(x*Z (Multiplicative.ofAdd (l.map t).sum))*(f i)⁻¹ := by rw [ih]
      _=(f i*x*(f i)⁻¹)*(f i*Z (Multiplicative.ofAdd (l.map t).sum)*(f i)⁻¹) := by group
      _=(x*Z (Multiplicative.ofAdd (t i)))*Z (Multiplicative.ofAdd (l.map t).sum) := by rw [h i,hc.eq];group
      _=x*(Z (Multiplicative.ofAdd (t i))*Z (Multiplicative.ofAdd (l.map t).sum)) := by group
      _=_ := by rw [←map_mul];rfl

end SymmetricSubgroupAsymptotics.CFSGCentralProductCollecting
