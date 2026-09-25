import SymmetricSubgroupAsymptotics.BinaryAbelianization

/-! Binary characters of the complete product source. -/

set_option autoImplicit false
noncomputable section

namespace SymmetricSubgroupAsymptotics

variable (G T : Type*) [Group G] [Group T]

/-- Restriction to both actual factors, with inverse given by their sum. -/
def binaryCharactersProdEquiv :
    BinaryCharacters (G × T) ≃ₗ[ZMod 2] BinaryCharacters G × BinaryCharacters T where
  toFun χ :=
    ( { toFun := fun g => χ (Additive.ofMul (g.toMul,1))
        map_zero' := χ.map_zero
        map_add' := by
          intro g h
          have hχ := χ.map_add (Additive.ofMul (g.toMul,1)) (Additive.ofMul (h.toMul,1))
          change χ (Additive.ofMul (g.toMul * h.toMul,1*1)) = _ at hχ
          simpa only [mul_one] using hχ },
      { toFun := fun t => χ (Additive.ofMul (1,t.toMul))
        map_zero' := χ.map_zero
        map_add' := by
          intro t u
          have hχ := χ.map_add (Additive.ofMul (1,t.toMul)) (Additive.ofMul (1,u.toMul))
          change χ (Additive.ofMul (1*1,t.toMul * u.toMul)) = _ at hχ
          simpa only [mul_one] using hχ } )
  invFun χ :=
    { toFun := fun x => χ.1 (Additive.ofMul x.toMul.1) + χ.2 (Additive.ofMul x.toMul.2)
      map_zero' := by simp
      map_add' := by
        intro x y
        change χ.1 (Additive.ofMul x.toMul.1 + Additive.ofMul y.toMul.1) +
          χ.2 (Additive.ofMul x.toMul.2 + Additive.ofMul y.toMul.2) = _
        rw [map_add,map_add]
        abel }
  left_inv χ := by
    apply AddMonoidHom.ext
    intro x
    have hχ := χ.map_add (Additive.ofMul (x.toMul.1,1)) (Additive.ofMul (1,x.toMul.2))
    change χ (Additive.ofMul (x.toMul.1*1,1*x.toMul.2)) = _ at hχ
    rw [mul_one,one_mul] at hχ
    exact hχ.symm
  right_inv χ := by ext <;> simp
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

theorem binaryCharacterRank_prod [Finite G] [Finite T] :
    binaryCharacterRank (G × T) = binaryCharacterRank G + binaryCharacterRank T := by
  unfold binaryCharacterRank
  rw [(binaryCharactersProdEquiv G T).finrank_eq,Module.finrank_prod]

variable (U : Type*) [AddCommGroup U] [Module (ZMod 2) U]

/-- Characters on an elementary binary group are its actual linear dual. -/
def binaryVectorCharactersEquiv :
    BinaryCharacters (Multiplicative U) ≃ₗ[ZMod 2] Module.Dual (ZMod 2) U where
  toFun χ :=
    ({ toFun := fun u => χ (Additive.ofMul (Multiplicative.ofAdd u))
       map_zero' := χ.map_zero
       map_add' := χ.map_add } : U →+ ZMod 2).toZModLinearMap 2
  invFun f :=
    { toFun := fun u => f u.toMul.toAdd
      map_zero' := f.map_zero
      map_add' := f.map_add }
  left_inv _ := rfl
  right_inv _ := rfl
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

theorem binaryCharacterRank_multiplicative [Finite U] :
    binaryCharacterRank (Multiplicative U) = Module.finrank (ZMod 2) U := by
  unfold binaryCharacterRank
  rw [(binaryVectorCharactersEquiv U).finrank_eq,Subspace.dual_finrank_eq]

/-- The exact source exponent for an ordered vertical space and the entire
original exterior, including any nonabelian exterior structure. -/
theorem binaryCharacterRank_multiplicative_prod [Finite U] [Finite T] :
    binaryCharacterRank (Multiplicative U × T) =
      Module.finrank (ZMod 2) U + binaryCharacterRank T := by
  rw [binaryCharacterRank_prod,binaryCharacterRank_multiplicative]

end SymmetricSubgroupAsymptotics
