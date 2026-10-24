import SymmetricSubgroupAsymptotics.CFSGE6GeckProductTorusWeylAction

/-! A bounded six-by-six cocharacter certificate for middle torus
inversion. Six separate reflection steps avoid reduction of a nested
matrix product. The final monomial identity holds in every commutative
group, independently of a field or a group-realization assumption. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
open scoped Matrix
namespace SymmetricSubgroupAsymptotics.CFSGE6GeckMiddleTorusExponentCertificate
open CFSGIntegerMatrixPowerHom CFSGIntegerReflectionPowerHom
open CFSGE6GeckProductTorusWeylAction
local notation "A" => CartanMatrix.E₆

private def twoColumns (v w : Fin 6→ℤ) : Matrix (Fin 6) (Fin 6) ℤ :=
  fun i j=>if j=2 then v i else if j=3 then w i else 0

private def stages : Fin 7→Matrix (Fin 6) (Fin 6) ℤ := ![
  twoColumns ![0,0,1,0,1,0] ![0,0,0,1,0,0],
  twoColumns ![0,0,1,2,1,0] ![0,0,0,-1,0,0],
  twoColumns ![0,0,1,2,1,0] ![0,0,0,-1,-1,0],
  twoColumns ![0,0,1,2,1,0] ![0,0,-1,-1,-1,0],
  twoColumns ![0,0,1,0,1,0] ![0,0,-1,-1,-1,0],
  twoColumns ![0,0,1,0,-1,0] ![0,0,-1,-1,0,0],
  twoColumns ![0,0,-1,0,-1,0] ![0,0,0,-1,0,0]]

def middleProjection : Matrix (Fin 6) (Fin 6) ℤ := stages 0

private theorem stage_steps : ∀n : Fin 6,
    reflectionExponents A (![3,4,2,3,4,2] n)*stages n.castSucc=stages n.succ := by decide +kernel

private theorem final_stage : stages 6= -middleProjection := by decide +kernel

theorem middle_reflection_projection :
    wordReflectionExponents [2,4,3,2,4,3]*middleProjection= -middleProjection := by
  calc
    _=stages 6 := by
      change wordReflectionExponents [2,4,3,2,4,3]*stages 0=stages 6
      have h0 : reflectionExponents A 3*stages 0=stages 1 := stage_steps 0
      have h1 : reflectionExponents A 4*stages 1=stages 2 := stage_steps 1
      have h2 : reflectionExponents A 2*stages 2=stages 3 := stage_steps 2
      have h3 : reflectionExponents A 3*stages 3=stages 4 := stage_steps 3
      have h4 : reflectionExponents A 4*stages 4=stages 5 := stage_steps 4
      have h5 : reflectionExponents A 2*stages 5=stages 6 := stage_steps 5
      simp only [wordReflectionExponents,List.map_cons,List.map_nil,List.prod_cons,List.prod_nil,mul_one,mul_assoc]
      rw [h0,h1,h2,h3,h4,h5]
    _=_ := final_stage

private theorem projection_column_two : (fun i=>middleProjection i 2)=
    (Pi.single 2 (1:ℤ)+Pi.single 4 1 : Fin 6→ℤ) := by decide +kernel
private theorem projection_column_three : (fun i=>middleProjection i 3)=
    (Pi.single 3 (1:ℤ) : Fin 6→ℤ) := by decide +kernel

variable {G : Type*} [CommGroup G]

def middleTuple (b c : G) : Fin 6→G := Pi.mulSingle 2 b*Pi.mulSingle 4 b*Pi.mulSingle 3 c

theorem powerHom_middleProjection (b c : G) :
    powerHom middleProjection (Pi.mulSingle 2 b*Pi.mulSingle 3 c)=middleTuple b c := by
  rw [map_mul,powerHom_mulSingle,powerHom_mulSingle]
  funext i
  change b^(middleProjection i 2)*c^(middleProjection i 3)=
    (Pi.mulSingle 2 b : Fin 6→G) i*(Pi.mulSingle 4 b : Fin 6→G) i*(Pi.mulSingle 3 c : Fin 6→G) i
  rw [congrFun projection_column_two i,congrFun projection_column_three i]
  change b^((Pi.single 2 (1:ℤ) : Fin 6→ℤ) i+(Pi.single 4 (1:ℤ) : Fin 6→ℤ) i)*
    c^((Pi.single 3 (1:ℤ) : Fin 6→ℤ) i)=_
  rw [zpow_add]
  by_cases hi2 : i=2 <;> by_cases hi3 : i=3 <;> by_cases hi4 : i=4 <;>
    simp [Pi.single_apply,Pi.mulSingle_apply,hi2,hi3,hi4,eq_comm]

theorem middle_tuple_inverted (b c : G) :
    powerHom (wordReflectionExponents [2,4,3,2,4,3]) (middleTuple b c)=(middleTuple b c)⁻¹ := by
  rw [←powerHom_middleProjection b c,←powerHom_mul,middle_reflection_projection,powerHom_neg]

end SymmetricSubgroupAsymptotics.CFSGE6GeckMiddleTorusExponentCertificate
