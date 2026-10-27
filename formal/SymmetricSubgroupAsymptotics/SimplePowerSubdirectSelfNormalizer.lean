import SymmetricSubgroupAsymptotics.SimplePowerFullSubdirectCount
import Mathlib.Tactic.Group

/-! Full subdirect powers of a centerless simple group are self-normalizing.
The induction keeps the actual tail and uses only the simple first axis;
no partition census or Scott classification is assumed. -/
set_option autoImplicit false
noncomputable section
namespace SymmetricSubgroupAsymptotics.SimplePowerSubdirectSelfNormalizer
open SimplePowerFullSubdirectCount

variable {T B : Type} [Group T] [Group B] [IsSimpleGroup T]

theorem product_normalizer_eq (hZ : IsCenterless T) (K : Subgroup (T × B))
    (hfirst : Function.Surjective (Prod.fst ∘ K.subtype))
    (htail : Subgroup.normalizer (SubdirectTailImage.tail K : Set B)=SubdirectTailImage.tail K) :
    Subgroup.normalizer (K : Set (T × B))=K := by
  apply le_antisymm ?_ K.le_normalizer
  intro g hg
  have hbN : g.2∈Subgroup.normalizer (SubdirectTailImage.tail K : Set B) :=
    Subgroup.le_normalizer_map (MonoidHom.snd T B) ⟨g,hg,rfl⟩
  rw [htail] at hbN
  obtain ⟨k,hk,hkb⟩ := hbN
  let u := g*k⁻¹
  have huN : u∈Subgroup.normalizer (K : Set (T × B)) :=
    (Subgroup.normalizer (K : Set (T × B))).mul_mem hg
      ((Subgroup.normalizer (K : Set (T × B))).inv_mem (K.le_normalizer hk))
  have hu2 : u.2=1 := by
    change g.2*k.2⁻¹=1
    change k.2=g.2 at hkb
    rw [hkb,mul_inv_cancel]
  have haxis : K.goursatFst.Normal := Subgroup.normal_goursatFst hfirst
  have huK : u∈K := by
    rcases haxis.eq_bot_or_eq_top with hb | ht
    · have hs : u.1=1 := by
        apply hZ u.1
        intro t
        obtain ⟨v,hv⟩ := hfirst t
        have hc := (Subgroup.mem_normalizer_iff.mp huN v.val).mp v.property
        have hm := K.mul_mem hc (K.inv_mem v.property)
        have ha : u.1*t*u.1⁻¹*t⁻¹∈K.goursatFst := by
          apply Subgroup.mem_goursatFst.mpr
          convert hm using 1
          apply Prod.ext
          · change u.1*t*u.1⁻¹*t⁻¹=u.1*v.val.1*u.1⁻¹*v.val.1⁻¹
            change v.val.1=t at hv
            rw [hv]
          · change 1=u.2*v.val.2*u.2⁻¹*v.val.2⁻¹
            rw [hu2]
            simp
        rw [hb,Subgroup.mem_bot] at ha
        calc
          u.1*t=(u.1*t*u.1⁻¹*t⁻¹)*(t*u.1) := by group
          _=t*u.1 := by rw [ha,one_mul]
      have hu : u=1 := Prod.ext hs hu2
      simpa only [hu] using K.one_mem
    · have ha : u.1∈K.goursatFst := by rw [ht]; trivial
      have hh := Subgroup.mem_goursatFst.mp ha
      have hu : u=(u.1,(1 : B)) := Prod.ext rfl hu2
      simpa only [←hu] using hh
  have hm := K.mul_mem huK hk
  have he : u*k=g := by dsimp only [u]; group
  exact he ▸ hm

theorem normalizer_eq (T : Type) [Group T] [Finite T] [IsSimpleGroup T]
    (hZ : IsCenterless T) (n : ℕ) (K : Subgroup (Fin n → T))
    (hfull : ∀ i : Fin n,Function.Surjective (fun k : K => k.val i)) :
    Subgroup.normalizer (K : Set (Fin n → T))=K := by
  induction n with
  | zero =>
    apply le_antisymm ?_ K.le_normalizer
    intro g _
    have hg : g=1 := Subsingleton.elim _ _
    simpa only [hg] using K.one_mem
  | succ n ih =>
    let H : Family T (n+1) := ⟨K,hfull⟩
    let P := toSplit T n H
    let L := (tailCode T n P).1
    have htail : Subgroup.normalizer (SubdirectTailImage.tail P.val : Set (Fin n → T))=
        SubdirectTailImage.tail P.val := ih L.val L.property
    have hp := product_normalizer_eq hZ P.val P.property.1 htail
    apply le_antisymm ?_ K.le_normalizer
    intro g hg
    let e := splitEquiv T n
    have hm := Subgroup.le_normalizer_map e.toMonoidHom ⟨g,hg,rfl⟩
    change e g∈Subgroup.normalizer (P.val : Set (T × (Fin n → T))) at hm
    rw [hp] at hm
    change e g∈K.map e.toMonoidHom at hm
    obtain ⟨v,hv,he⟩ := hm
    have he' : v=g := e.injective he
    exact he' ▸ hv

end SymmetricSubgroupAsymptotics.SimplePowerSubdirectSelfNormalizer
