import SymmetricSubgroupAsymptotics.SemisimpleSubdirectChart
import SymmetricSubgroupAsymptotics.SimpleProductAutomorphismCoordinates

/-! The degree form of a core-free full subdirect subgroup of a homogeneous
nonabelian simple power. Diagonal correlations are retained by Scott's
proved chart; no primitive-group classification is assumed. -/
set_option autoImplicit false
noncomputable section
open scoped Classical
namespace SymmetricSubgroupAsymptotics.PrimitiveSocleONanScottHelpers

/-- A full subdirect subgroup containing no whole original simple factor
has the exact diagonal degree form, including its required factor budget. -/
theorem subdirect_index_form
    {T : Type} [Group T] [Finite T] [IsSimpleGroup T]
    (hT : IsCenterless T) (k : ℕ) (K : Subgroup (Fin k → T))
    (honto : ∀ i, Function.Surjective
      ((Pi.evalMonoidHom (fun _ : Fin k => T) i).comp K.subtype))
    (hno : ∀ i, ¬ ∀ t : T, Pi.mulSingle i t∈K) :
    ∃ a : ℕ, k≤2*a ∧ K.index=Nat.card T ^ a := by
  letI : Fintype T := Fintype.ofFinite T
  obtain ⟨C⟩ := semisimpleGroupChartOrigins_of_subdirect (fun _ : Fin k => T)
    (fun _ => hT) K
    (fun i => (Pi.evalMonoidHom (fun _ : Fin k => T) i).comp K.subtype)
    honto (by intro x y h; apply Subtype.ext; exact h)
  let l := Fintype.card C.ι
  let e : K ≃* (Fin l → T) :=
    C.equiv.trans ((MulEquiv.piCongrRight C.factor_equiv).trans
      (MulEquiv.arrowCongr (Fintype.equivFin C.ι) (MulEquiv.refl T)))
  have hread (i : Fin k) :
      ∃ (j : Fin l) (a : MulAut T),
        ∀ z : Fin l → T, (e.symm z : Fin k → T) i=a (z j) := by
    let f := ((Pi.evalMonoidHom (fun _ : Fin k => T) i).comp
      K.subtype).comp e.symm.toMonoidHom
    have hf : Function.Surjective f := (honto i).comp e.symm.surjective
    exact SimpleProductAutomorphismCoordinates.surjective_factor hT f hf
  choose r a hr using hread
  have hsurj : Function.Surjective r := by
    intro j
    by_contra hn
    push Not at hn
    obtain ⟨t,ht⟩ := exists_ne (1 : T)
    have hz : e.symm (Pi.mulSingle j t)=1 := by
      apply Subtype.ext
      funext i
      rw [hr]
      simp only [Pi.mulSingle_eq_of_ne (hn i),map_one]
      rfl
    have he := congrFun (e.symm.injective (hz.trans e.symm.map_one.symm)) j
    exact ht (by simpa only [Pi.mulSingle_eq_same,Pi.one_apply] using he)
  have hpartner (i : Fin k) : ∃ i' : Fin k, i'≠i ∧ r i'=r i := by
    by_contra hn
    push Not at hn
    apply hno i
    intro t
    have he : (e.symm (Pi.mulSingle (r i) ((a i).symm t)) : Fin k → T)=
        Pi.mulSingle i t := by
      funext q
      rw [hr]
      by_cases hq : q=i
      · subst q
        simp only [Pi.mulSingle_eq_same,MulEquiv.apply_symm_apply]
      · have hroute : r q≠r i := hn q hq
        simp only [Pi.mulSingle_eq_of_ne hroute,Pi.mulSingle_eq_of_ne hq,map_one]
    exact he ▸ (e.symm _).property
  choose f hf using hsurj
  choose g hgf hgr using fun j => hpartner (f j)
  let F : Fin l×Bool → Fin k := fun z => if z.2 then g z.1 else f z.1
  have hF : Function.Injective F := by
    rintro ⟨j,b⟩ ⟨j',b'⟩ he
    have hroute : ∀ j b, r (F (j,b))=j := by
      intro j b
      cases b <;> simp only [F,Bool.false_eq_true,↓reduceIte,hf,hgr]
    have hj : j=j' := (hroute j b).symm.trans ((congrArg r he).trans (hroute j' b'))
    subst j'
    have hb : b=b' := by
      cases b <;> cases b' <;> try rfl
      · exact False.elim (hgf j he.symm)
      · exact False.elim (hgf j he)
    subst b'
    rfl
  have hcount : 2*l≤k := by
    have hc := Fintype.card_le_of_injective F hF
    simpa only [Fintype.card_prod,Fintype.card_fin,Fintype.card_bool,mul_comm] using hc
  have hcard : Nat.card K=Nat.card T ^ l := by
    rw [Nat.card_congr e.toEquiv,Nat.card_fun,Nat.card_fin]
  have hambient : Nat.card (Fin k → T)=Nat.card T ^ k := by
    rw [Nat.card_fun,Nat.card_fin]
  have heq := K.card_mul_index
  rw [hcard,hambient] at heq
  refine ⟨k-l,by omega,?_⟩
  have hlk : l≤k := by omega
  have hp : Nat.card T ^ l > 0 := pow_pos Nat.card_pos _
  apply Nat.eq_of_mul_eq_mul_left hp
  rw [heq,←pow_add,Nat.add_sub_of_le hlk]

end SymmetricSubgroupAsymptotics.PrimitiveSocleONanScottHelpers
