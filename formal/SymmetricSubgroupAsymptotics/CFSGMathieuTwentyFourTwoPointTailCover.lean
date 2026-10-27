import SymmetricSubgroupAsymptotics.External.CFSG.Certificates.Mathieu24.Certificates.ChainOrbits
import SymmetricSubgroupAsymptotics.External.CFSG.Certificates.Mathieu24.Certificates.FinalStabilizer
import SymmetricSubgroupAsymptotics.CFSGMathieuTwentyFourPresentationWords
import Mathlib.Tactic.Group

/-! Constructive 82-slot tail cover of the SAME actual two-point
stabilizer, transported to the literal 8/11 swap frame. No Cardinality
import, complete group enumeration, or source representation surjectivity. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
open scoped Classical
namespace SymmetricSubgroupAsymptotics.CFSGMathieuTwentyFourTwoPointTailCover
open CFSG.Certificates.Mathieu24 M24Certificates
open M24Certificates.StabilizerChain M24Certificates.ChainOrbits M24Certificates.SteinerSystem

abbrev H0 := MulAction.stabilizer (MulAction.stabilizer M24 (23 : Fin 24)) (22 : Fin 24)
abbrev H1 := MulAction.stabilizer H0 (0 : Fin 24)
abbrev H2 := MulAction.stabilizer H1 (1 : Fin 24)
abbrev H3 := MulAction.stabilizer H2 (2 : Fin 24)
abbrev H4 := MulAction.stabilizer H3 (5 : Fin 24)
abbrev H5 := MulAction.stabilizer H4 (3 : Fin 24)

abbrev First := {i : Fin 24 // i ≠ 23 ∧ i ≠ 22}
abbrev Second := {i : Fin 24 // i ≠ 23 ∧ i ≠ 22 ∧ i ≠ 0}
abbrev Third := {i : Fin 24 // i ≠ 23 ∧ i ≠ 22 ∧ i ≠ 0 ∧ i ≠ 1}
abbrev Fourth := {i : Fin 24 // i ∈ blockB0ᶜ}
abbrev Fifth := {i : Fin 24 // i = 3 ∨ i = 4 ∨ i = 21}
abbrev Code := First × (Second × (Third × (Fourth × Fifth)))

def lift0 : H0 →* M24 :=
  (MulAction.stabilizer M24 (23 : Fin 24)).subtype.comp
    (MulAction.stabilizer (MulAction.stabilizer M24 (23 : Fin 24)) (22 : Fin 24)).subtype
def lift1 : H1 →* M24 := lift0.comp (MulAction.stabilizer H0 (0 : Fin 24)).subtype
def lift2 : H2 →* M24 := lift1.comp (MulAction.stabilizer H1 (1 : Fin 24)).subtype
def lift3 : H3 →* M24 := lift2.comp (MulAction.stabilizer H2 (2 : Fin 24)).subtype
def lift4 : H4 →* M24 := lift3.comp (MulAction.stabilizer H3 (5 : Fin 24)).subtype
def lift5 : H5 →* M24 := lift4.comp (MulAction.stabilizer H4 (3 : Fin 24)).subtype

def seed0 (i : First) : H0 := stab2322Element i.val i.property.1 i.property.2
def seed1 (i : Second) : H1 := stab23220Element i.val i.property.1 i.property.2.1 i.property.2.2
def seed2 (i : Third) : H2 :=
  stab232201Element i.val i.property.1 i.property.2.1 i.property.2.2.1 i.property.2.2.2
def seed3 (i : Fourth) : H3 := levelSixElement i.val i.property
def seed4 (i : Fifth) : H4 := levelSevenElement i.val i.property

def decode (c : Code) : M24 :=
  lift0 (seed0 c.1) * lift1 (seed1 c.2.1) * lift2 (seed2 c.2.2.1) *
    lift3 (seed3 c.2.2.2.1) * lift4 (seed4 c.2.2.2.2)

theorem decode_fixes_pair (c : Code) :
    (decode c).val (23 : Fin 24)=23 ∧ (decode c).val (22 : Fin 24)=22 := by
  have hfix (g : H0) : (lift0 g).val (23 : Fin 24)=23 ∧ (lift0 g).val (22 : Fin 24)=22 := by
    constructor
    · simpa only [lift0,MonoidHom.comp_apply,Subgroup.smul_def,Equiv.Perm.smul_def] using
        (MulAction.mem_stabilizer_iff.mp g.val.property)
    · simpa only [lift0,MonoidHom.comp_apply,Subgroup.smul_def,Equiv.Perm.smul_def] using
        (MulAction.mem_stabilizer_iff.mp g.property)
  have h0 := hfix (seed0 c.1)
  have h1 : (lift1 (seed1 c.2.1)).val 23=23 ∧ (lift1 (seed1 c.2.1)).val 22=22 :=
    hfix (seed1 c.2.1).val
  have h2 : (lift2 (seed2 c.2.2.1)).val 23=23 ∧ (lift2 (seed2 c.2.2.1)).val 22=22 :=
    hfix (seed2 c.2.2.1).val.val
  have h3 : (lift3 (seed3 c.2.2.2.1)).val 23=23 ∧ (lift3 (seed3 c.2.2.2.1)).val 22=22 :=
    hfix (seed3 c.2.2.2.1).val.val.val
  have h4 : (lift4 (seed4 c.2.2.2.2)).val 23=23 ∧ (lift4 (seed4 c.2.2.2.2)).val 22=22 :=
    hfix (seed4 c.2.2.2.2).val.val.val.val
  constructor
  · simp only [decode,Subgroup.coe_mul,Equiv.Perm.mul_apply,h0.1,h1.1,h2.1,h3.1,h4.1]
  · simp only [decode,Subgroup.coe_mul,Equiv.Perm.mul_apply,h0.2,h1.2,h2.2,h3.2,h4.2]

private def residual {A X : Type*} [Group A] [MulAction A X]
    (g t : A) (p : X) (ht : t • p = g • p) : MulAction.stabilizer A p :=
  ⟨t⁻¹*g,by
    change (t⁻¹*g) • p = p
    rw [mul_smul,←ht,inv_smul_smul]⟩

private theorem residual_factor {A X : Type*} [Group A] [MulAction A X]
    (g t : A) (p : X) (ht : t • p = g • p) :
    t*(residual g t p ht).val=g := mul_inv_cancel_left t g

theorem final_stabilizer_eq_one (g : H5) : g=1 := by
  have h23 : (lift5 g).val 23=23 := by
    simpa [lift5,lift4,lift3,lift2,lift1,lift0,Subgroup.smul_def,Equiv.Perm.smul_def] using
      (MulAction.mem_stabilizer_iff.mp g.val.val.val.val.val.val.property)
  have h22 : (lift5 g).val 22=22 := by
    simpa [lift5,lift4,lift3,lift2,lift1,lift0,Subgroup.smul_def,Equiv.Perm.smul_def] using
      (MulAction.mem_stabilizer_iff.mp g.val.val.val.val.val.property)
  have h0 : (lift5 g).val 0=0 := by
    simpa [lift5,lift4,lift3,lift2,lift1,lift0,Subgroup.smul_def,Equiv.Perm.smul_def] using
      (MulAction.mem_stabilizer_iff.mp g.val.val.val.val.property)
  have h1 : (lift5 g).val 1=1 := by
    simpa [lift5,lift4,lift3,lift2,lift1,lift0,Subgroup.smul_def,Equiv.Perm.smul_def] using
      (MulAction.mem_stabilizer_iff.mp g.val.val.val.property)
  have h2 : (lift5 g).val 2=2 := by
    simpa [lift5,lift4,lift3,lift2,lift1,lift0,Subgroup.smul_def,Equiv.Perm.smul_def] using
      (MulAction.mem_stabilizer_iff.mp g.val.val.property)
  have h5 : (lift5 g).val 5=5 := by
    simpa [lift5,lift4,lift3,lift2,lift1,lift0,Subgroup.smul_def,Equiv.Perm.smul_def] using
      (MulAction.mem_stabilizer_iff.mp g.val.property)
  have h3 : (lift5 g).val 3=3 := by
    simpa [lift5,lift4,lift3,lift2,lift1,lift0,Subgroup.smul_def,Equiv.Perm.smul_def] using
      (MulAction.mem_stabilizer_iff.mp g.property)
  have hp : (lift5 g).val=1 :=
    FinalStabilizer.fixed_base_preserves_octads_eq_one (lift5 g).val
      (M24_preserves_octads (lift5 g)).1 h23 h22 h0 h1 h2 h5 h3
  apply Subtype.ext
  apply Subtype.ext
  apply Subtype.ext
  apply Subtype.ext
  apply Subtype.ext
  apply Subtype.ext
  apply Subtype.ext
  exact Subtype.ext hp

private theorem final_orbit_mem (g : H4) :
    g • (3 : Fin 24) ∈ ({3,4,21} : Finset (Fin 24)) := by
  change g • (3 : Fin 24) ∈ (↑({3,4,21} : Finset (Fin 24)) : Set (Fin 24))
  rw [←stab23220125_orbit_three_eq]
  exact ⟨g,rfl⟩

theorem decode_surjective_on_two_point (g : H0) : ∃ c : Code, decode c=lift0 g := by
  have hi : g • (0 : Fin 24) ∈ ({i : Fin 24 | i ≠ 23 ∧ i ≠ 22} : Set (Fin 24)) := by
    rw [←stab2322_orbit_zero_eq]
    exact ⟨g,rfl⟩
  let i : First := ⟨g • (0 : Fin 24),hi⟩
  have hs0 : seed0 i • (0 : Fin 24)=g • (0 : Fin 24) := by
    change (Word.eval (levelThreeWord i.val)) 0=i.val
    exact levelThreeWord_maps_0_all i.val i.property.1 i.property.2
  obtain ⟨g1,hg1⟩ : ∃ u : H1, u=residual g (seed0 i) 0 hs0 := ⟨_,rfl⟩
  have hj : g1 • (1 : Fin 24) ∈ ({i : Fin 24 | i ≠ 23 ∧ i ≠ 22 ∧ i ≠ 0} : Set (Fin 24)) := by
    rw [←stab23220_orbit_one_eq]
    exact ⟨g1,rfl⟩
  let j : Second := ⟨g1 • (1 : Fin 24),hj⟩
  have hs1 : seed1 j • (1 : Fin 24)=g1 • (1 : Fin 24) := by
    change (Word.eval (levelFourWord j.val)) 1=j.val
    exact levelFourWord_maps_1_all j.val j.property.1 j.property.2.1 j.property.2.2
  obtain ⟨g2,hg2⟩ : ∃ u : H2, u=residual g1 (seed1 j) 1 hs1 := ⟨_,rfl⟩
  have hk : g2 • (2 : Fin 24) ∈ ({i : Fin 24 | i ≠ 23 ∧ i ≠ 22 ∧ i ≠ 0 ∧ i ≠ 1} : Set (Fin 24)) := by
    rw [←stab232201_orbit_two_eq]
    exact ⟨g2,rfl⟩
  let k : Third := ⟨g2 • (2 : Fin 24),hk⟩
  have hs2 : seed2 k • (2 : Fin 24)=g2 • (2 : Fin 24) := by
    change (Word.eval (levelFiveWord k.val)) 2=k.val
    exact levelFiveWord_maps_2_all k.val k.property.1 k.property.2.1 k.property.2.2.1 k.property.2.2.2
  obtain ⟨g3,hg3⟩ : ∃ u : H3, u=residual g2 (seed2 k) 2 hs2 := ⟨_,rfl⟩
  have hl : g3 • (5 : Fin 24) ∈ blockB0ᶜ := by
    change g3 • (5 : Fin 24) ∈ (↑(blockB0ᶜ) : Set (Fin 24))
    rw [←stab2322012_orbit_five_eq]
    exact ⟨g3,rfl⟩
  let l : Fourth := ⟨g3 • (5 : Fin 24),hl⟩
  have hs3 : seed3 l • (5 : Fin 24)=g3 • (5 : Fin 24) := by
    change (Word.eval (levelSixWord l.val)) 5=l.val
    exact levelSixWord_maps_5_all l.val l.property
  obtain ⟨g4,hg4⟩ : ∃ u : H4, u=residual g3 (seed3 l) 5 hs3 := ⟨_,rfl⟩
  have hm := final_orbit_mem g4
  let m : Fifth := ⟨g4 • (3 : Fin 24),mem_targets_iff _ hm⟩
  have hs4 : seed4 m • (3 : Fin 24)=g4 • (3 : Fin 24) := by
    change (Word.eval (levelSevenWord m.val)) 3=m.val
    exact levelSevenWord_maps_3_all m.val m.property
  obtain ⟨g5,hg5⟩ : ∃ u : H5, u=residual g4 (seed4 m) 3 hs4 := ⟨_,rfl⟩
  have he0 : lift0 (seed0 i)*lift1 g1=lift0 g := by
    rw [hg1]
    exact (map_mul lift0 (seed0 i) (residual g (seed0 i) 0 hs0).val).symm.trans (congrArg lift0 (residual_factor g (seed0 i) 0 hs0))
  have he1 : lift1 (seed1 j)*lift2 g2=lift1 g1 := by
    rw [hg2]
    exact (map_mul lift1 (seed1 j) (residual g1 (seed1 j) 1 hs1).val).symm.trans (congrArg lift1 (residual_factor g1 (seed1 j) 1 hs1))
  have he2 : lift2 (seed2 k)*lift3 g3=lift2 g2 := by
    rw [hg3]
    exact (map_mul lift2 (seed2 k) (residual g2 (seed2 k) 2 hs2).val).symm.trans (congrArg lift2 (residual_factor g2 (seed2 k) 2 hs2))
  have he3 : lift3 (seed3 l)*lift4 g4=lift3 g3 := by
    rw [hg4]
    exact (map_mul lift3 (seed3 l) (residual g3 (seed3 l) 5 hs3).val).symm.trans (congrArg lift3 (residual_factor g3 (seed3 l) 5 hs3))
  have he4 : lift4 (seed4 m)*lift5 g5=lift4 g4 := by
    rw [hg5]
    exact (map_mul lift4 (seed4 m) (residual g4 (seed4 m) 3 hs4).val).symm.trans (congrArg lift4 (residual_factor g4 (seed4 m) 3 hs4))
  have hlast : lift5 g5=1 := (congrArg lift5 (final_stabilizer_eq_one g5)).trans lift5.map_one
  refine ⟨(i,(j,(k,(l,m)))),?_⟩
  calc
    decode (i,(j,(k,(l,m)))) = decode (i,(j,(k,(l,m))))*lift5 g5 := by rw [hlast,mul_one]
    _ = lift0 g := by
      simp only [decode,mul_assoc]
      rw [he4,he3,he2,he1,he0]

theorem code_card : Nat.card Code=443520 := by
  have h0 : Nat.card First=22 := by rw [Nat.card_eq_fintype_card]; decide +kernel
  have h1 : Nat.card Second=21 := by rw [Nat.card_eq_fintype_card]; decide +kernel
  have h2 : Nat.card Third=20 := by rw [Nat.card_eq_fintype_card]; decide +kernel
  have h3 : Nat.card Fourth=16 := by rw [Nat.card_eq_fintype_card]; decide +kernel
  have h4 : Nat.card Fifth=3 := by rw [Nat.card_eq_fintype_card]; decide +kernel
  simp only [Code,Nat.card_prod,h0,h1,h2,h3,h4]

end SymmetricSubgroupAsymptotics.CFSGMathieuTwentyFourTwoPointTailCover

namespace SymmetricSubgroupAsymptotics.CFSGMathieuTwentyFourTwoPointTailCover
open CFSG.Certificates.Mathieu24 M24Certificates
open M24Certificates.StabilizerChain M24Certificates.ChainOrbits

private theorem mul_val_apply (g h : M24) (p : Fin 24) :
    (g*h).val p=g.val (h.val p) := rfl

private theorem inv_val_apply (g : M24) (p : Fin 24) :
    (g⁻¹).val p=g.val.symm p := rfl

private theorem inverse_point_ne (g : M24) (p q r : Fin 24)
    (hg : g.val p=q) (hne : r≠q) : g.val.symm r≠p := by
  intro he
  have hh := congrArg g.val he
  rw [g.val.apply_symm_apply,hg] at hh
  exact hne hh

private theorem lastStabilizerElement_at (i : Fin 24) (hi : i≠23) :
    (lastStabilizerElement i hi).val.val 22=i := by
  change (Word.eval (levelTwoWord i)) 22=i
  exact levelTwoWord_maps_22_all i hi

@[irreducible] def frameFirst : M24 := Word.toM24 (levelOneWord 8)

theorem frameFirst_at_twentyThree : frameFirst.val 23=(8 : Fin 24) := by
  unfold frameFirst
  change (Word.eval (levelOneWord 8)) 23=8
  exact levelOneWord_maps_last_all 8

private def frameSecondIndex : Fin 24 := frameFirst.val.symm 11

private theorem frameSecondIndex_ne : frameSecondIndex ≠ (23 : Fin 24) := by
  unfold frameSecondIndex
  exact inverse_point_ne frameFirst 23 8 11 frameFirst_at_twentyThree (by decide)

private def frameSecond : MulAction.stabilizer M24 (23 : Fin 24) :=
  lastStabilizerElement frameSecondIndex frameSecondIndex_ne

private theorem frameSecond_at_twentyThree : frameSecond.val.val 23=(23 : Fin 24) := by
  simpa only [Subgroup.smul_def,Equiv.Perm.smul_def] using
    (MulAction.mem_stabilizer_iff.mp frameSecond.property)

private theorem frameSecond_at_twentyTwo : frameSecond.val.val 22=frameSecondIndex := by
  unfold frameSecond
  exact lastStabilizerElement_at frameSecondIndex frameSecondIndex_ne

def transport : M24 := frameFirst*frameSecond.val

theorem transport_at_twentyThree : transport.val 23=(8 : Fin 24) := by
  rw [transport,mul_val_apply,frameSecond_at_twentyThree,frameFirst_at_twentyThree]

theorem transport_at_twentyTwo : transport.val 22=(11 : Fin 24) := by
  rw [transport,mul_val_apply,frameSecond_at_twentyTwo]
  unfold frameSecondIndex
  exact frameFirst.val.apply_symm_apply 11

private theorem x_inverse_eleven :
    CFSGMathieuTwentyFourPresentationWords.x.val.symm (11 : Fin 24)=8 := by
  rw [CFSGMathieuTwentyFourPresentationWords.x_coe_eq]
  decide +kernel

private theorem x_inverse_eight :
    CFSGMathieuTwentyFourPresentationWords.x.val.symm (8 : Fin 24)=11 := by
  rw [CFSGMathieuTwentyFourPresentationWords.x_coe_eq]
  decide +kernel

def swapDecode (c : Code) : M24 :=
  CFSGMathieuTwentyFourPresentationWords.x*transport*decode c*transport⁻¹

private theorem frame_recover {A : Type*} [Group A] (x t h : A) :
    x*t*(t⁻¹*x⁻¹*h*t)*t⁻¹=h := by group

private theorem abstract_swap_cover (x t h : M24)
    (ht23 : t.val 23=8) (ht22 : t.val 22=11)
    (hx11 : x.val.symm 11=8) (hx8 : x.val.symm 8=11)
    (hh8 : h.val 8=11) (hh11 : h.val 11=8) :
    ∃ c : Code, x*t*decode c*t⁻¹=h := by
  let k : M24 := t⁻¹*x⁻¹*h*t
  have hk23 : k.val (23 : Fin 24)=23 := by
    simp only [k,mul_val_apply,inv_val_apply,ht23,hh8,hx11]
    rw [←ht23]
    exact t.val.symm_apply_apply 23
  have hk22 : k.val (22 : Fin 24)=22 := by
    simp only [k,mul_val_apply,inv_val_apply,ht22,hh11,hx8]
    rw [←ht22]
    exact t.val.symm_apply_apply 22
  let g : H0 := ⟨⟨k,hk23⟩,hk22⟩
  obtain ⟨c,hc⟩ := decode_surjective_on_two_point g
  have he : decode c=k := hc
  refine ⟨c,?_⟩
  rw [he]
  exact frame_recover x t h

theorem swapDecode_surjective_on_swap (h : M24)
    (h8 : h.val (8 : Fin 24)=11) (h11 : h.val (11 : Fin 24)=8) :
    ∃ c : Code, swapDecode c=h := by
  exact abstract_swap_cover CFSGMathieuTwentyFourPresentationWords.x transport h
    transport_at_twentyThree transport_at_twentyTwo x_inverse_eleven x_inverse_eight h8 h11

end SymmetricSubgroupAsymptotics.CFSGMathieuTwentyFourTwoPointTailCover
