import SymmetricSubgroupAsymptotics.CFSGReeGTwoPositiveCoordinates
import SymmetricSubgroupAsymptotics.CFSGReeGTwoFixedTorusAction
import SymmetricSubgroupAsymptotics.CFSGReeGTwoPositiveDerived

/-! Exact centre of the actual positive Ree group. Its final free
coordinate is a faithful additive field axis, on which the literal
fixed torus acts through all nonzero field scalars. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
namespace SymmetricSubgroupAsymptotics.CFSGReeGTwoPositiveCentre
open CFSGReeGTwoFieldParameters CFSGReeGTwoOriginalPositiveSubgroup
open CFSGReeGTwoPositiveCoordinates CFSGReeGTwoPositiveDerived
open CFSGReeGTwoFixedTorusAction CFSGReeGTwoOriginalTorus
open CFSGReeGTwoOriginalFixedWordChart CFSGGTwoNaturalPositiveTorusAction

theorem chart_mem_center_iff (m : ℕ) (x : Fin 3 → Field m) :
    fixedPositiveChart m x∈Subgroup.center (fixedPositiveGroup m) ↔
      x 0=0 ∧ x 1=0 := by
  constructor
  · intro hx
    have hc := congrFun ((chart_commute_iff m x ![0,1,0]).mp
      ((Subgroup.mem_center_iff.mp hx) (fixedPositiveChart m ![0,1,0])).symm) 2
    have h0 : x 0=0 := by
      have he : x 2=x 2-x 0 := by simpa [productCoordinates] using hc
      exact sub_eq_self.mp he.symm
    have ha := congrFun ((chart_commute_iff m x ![1,0,0]).mp
      ((Subgroup.mem_center_iff.mp hx) (fixedPositiveChart m ![1,0,0])).symm) 2
    refine ⟨h0,?_⟩
    have he : x 2-x 1=x 2 := by simpa [productCoordinates,h0] using ha
    exact sub_eq_self.mp he
  · rintro ⟨h0,h1⟩
    apply Subgroup.mem_center_iff.mpr
    intro g
    obtain ⟨y,rfl⟩ := fixedPositiveChart_surjective m g
    apply (chart_commute_iff m y x).mpr
    funext i
    fin_cases i <;> simp [productCoordinates,h0,h1,add_comm]

private theorem central_add (m : ℕ) (a b : Field m) :
    fixedPositiveChart m ![0,0,a]*fixedPositiveChart m ![0,0,b]=
      fixedPositiveChart m ![0,0,a+b] := by
  rw [chart_mul]
  apply congrArg (fixedPositiveChart m)
  funext i
  fin_cases i <;> simp [productCoordinates]

def centralHom (m : ℕ) : Multiplicative (Field m) →* fixedPositiveGroup m where
  toFun d := fixedPositiveChart m ![0,0,d.toAdd]
  map_one' := by
    have hz : (![0,0,(1 : Multiplicative (Field m)).toAdd] : Fin 3 → Field m)=0 := by
      funext i
      fin_cases i <;> rfl
    rw [hz,chart_zero]
  map_mul' a b := (central_add m a.toAdd b.toAdd).symm

theorem centralHom_injective (m : ℕ) : Function.Injective (centralHom m) := by
  intro a b h
  have he := congrFun (fixedPositiveChart_injective m h) 2
  exact congrArg Multiplicative.ofAdd he

theorem centralHom_range (m : ℕ) :
    (centralHom m).range=Subgroup.center (fixedPositiveGroup m) := by
  ext u
  constructor
  · rintro ⟨d,rfl⟩
    exact (chart_mem_center_iff m _).mpr ⟨rfl,rfl⟩
  · intro hu
    obtain ⟨x,hx⟩ := fixedPositiveChart_surjective m u
    have hp : x 0=0 ∧ x 1=0 := (chart_mem_center_iff m x).mp (hx ▸ hu)
    refine ⟨Multiplicative.ofAdd (x 2),?_⟩
    rw [←hx]
    apply congrArg (fixedPositiveChart m)
    funext i
    fin_cases i
    · exact hp.1.symm
    · exact hp.2.symm
    · rfl

theorem positive_center_card (m : ℕ) :
    Nat.card (Subgroup.center (fixedPositiveGroup m))=3^(2*m+1) := by
  rw [←centralHom_range]
  have hc : Nat.card (Multiplicative (Field m))=Nat.card (centralHom m).range :=
    Nat.card_congr (Equiv.ofInjective (centralHom m) (centralHom_injective m))
  exact hc.symm.trans (field_card m)

theorem torusAction_centralHom (m : ℕ) (t : (Field m)ˣ) (d : Field m) :
    fixedPositiveTorusAut m t (centralHom m (Multiplicative.ofAdd d))=
      centralHom m (Multiplicative.ofAdd (d*(t : Field m))) := by
  apply Subtype.ext
  change fixedTorusHom m t*fixedWord m ![0,0,d]*(fixedTorusHom m t)⁻¹=
    fixedWord m ![0,0,d*(t : Field m)]
  rw [fixedTorus_fixedWord]
  apply congrArg (fixedWord m)
  funext i
  fin_cases i <;> simp [fixedScaleCoordinates,rootScale]

theorem fixedPositiveTorusAut_injective (m : ℕ) :
    Function.Injective (fixedPositiveTorusAut m) := by
  intro a b he
  have hc := congrArg (fun f : MulAut (fixedPositiveGroup m) =>
    f (centralHom m (Multiplicative.ofAdd 1))) he
  dsimp only at hc
  rw [torusAction_centralHom,torusAction_centralHom,one_mul,one_mul] at hc
  have hv := centralHom_injective m hc
  exact Units.ext (congrArg Multiplicative.toAdd hv)

end SymmetricSubgroupAsymptotics.CFSGReeGTwoPositiveCentre
