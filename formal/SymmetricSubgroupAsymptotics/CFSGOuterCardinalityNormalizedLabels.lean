import SymmetricSubgroupAsymptotics.CFSGCosetDataIndex
import SymmetricSubgroupAsymptotics.PrimitiveSocleRawSimpleIndex
import Mathlib.Algebra.Group.PUnit
import Mathlib.Tactic.Group

/-! Count outer automorphisms by finite labels of actual inner-normalized
representatives. Labels need not descend to cosets, and no subgroup of
field automorphisms or injective torus parameterization is required. -/
set_option autoImplicit false
set_option Elab.async false
namespace SymmetricSubgroupAsymptotics.CFSGOuterCardinalityNormalizedLabels
open PrimitiveSocleRawStructure CFSGCosetDataIndex
variable {G : Type} [Group G] {S : Type*} [Finite S]

theorem outer_card_le_of_normalized_labels
    (normal : MulAut G→MulAut G) (label : MulAut G→S)
    (hinner : ∀f,∃g:G,normal f=MulAut.conj g*f)
    (hsep : ∀f h,label f=label h→normal f=normal h) :
    Nat.card (Outer G)≤Nat.card S := by
  have hindex : (Inner G).index≤(⊤:Subgroup PUnit.{1}).index*Nat.card S :=
    index_le_of_coset_data (Inner G) (⊤:Subgroup PUnit.{1})
    (fun _:MulAut G=>(1:PUnit.{1})) label (by
      intro f h _ hlabel
      obtain ⟨a,ha⟩ := hinner f
      obtain ⟨b,hb⟩ := hinner h
      have he : MulAut.conj a*f=MulAut.conj b*h :=
        ha.symm.trans ((hsep f h hlabel).trans hb)
      have hfactor : f*h⁻¹=(MulAut.conj a)⁻¹*MulAut.conj b := by
        calc
          _=(MulAut.conj a)⁻¹*(MulAut.conj a*f)*h⁻¹ := by group
          _=_ := by rw [he];group
      rw [hfactor]
      exact (Inner G).mul_mem ((Inner G).inv_mem ⟨a,rfl⟩) ⟨b,rfl⟩)
  rw [Subgroup.index_top,one_mul] at hindex
  simpa only [Subgroup.index_eq_card] using hindex

end SymmetricSubgroupAsymptotics.CFSGOuterCardinalityNormalizedLabels
