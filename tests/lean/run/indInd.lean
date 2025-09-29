mutual
inductive Con : Type where
  | nil : Con
  | ext (Γ : Con) (A : Ty Γ) :  Con

inductive Ty : (Γ : Con) → Type where
  | U : Ty Γ
  | Pi (A : Ty Γ) (B : Ty (Con.ext Γ A)) :Ty Γ

end

noncomputable def Con.casesOn 
  {motive_1 : Con → Sort u} 
  (nil : motive_1 nil)
  (ext : (Γ : Con) → (A : Ty Γ) → motive_1 (Γ.ext A))
  (t : Con) : motive_1 t := @Con.recOn motive_1 (fun _ _ _ => PUnit) t nil (fun  Γ A _ _ => ext Γ A ) (fun _ => ⟨⟩) (fun _ _ _ _ _ => ⟨⟩)

noncomputable def Ty.casesOn
  {motive : (Γ : Con) → Ty Γ → Sort u} 
  (U : {Γ : Con} → motive Γ Ty.U)
  (Pi :
    {Γ : Con} → (A : Ty Γ) → (B : Ty (Γ.ext A)) → motive Γ (A.Pi B))
  {Γ : Con} (t : Ty Γ) : motive Γ t := @Ty.recOn (fun _ => PUnit) (fun Γ _ A => motive Γ A) _ t ⟨⟩ (fun _ _ _ _ => ⟨⟩) (fun _ => U) (fun A B _ _ _ => Pi A B)

def Con.below
  {motive_1 : Con → Sort u}
  {motive_2 : (Γ : Con) → motive_1 Γ → Ty Γ → Sort u}
  : Con → Sort (max 1 u) :=
  @Con.rec (fun _Γ => Sort (max 1 u)) (fun _Γ _Γ_IH _A => Sort (max 1 u))
    PUnit
    (fun Γ A Γ_IH A_IH => (motive_Γ : motive_1 Γ) ×' (motive_2 Γ motive_Γ A) ×' Γ_IH ×' A_IH)
    (@fun Γ motives_ty => (motive_1 Γ) ×' motives_ty)
    (@fun Γ A B Γ_IH A_IH B_IH => (motive_Γ : motive_1 Γ) ×' (motive_2 Γ motive_Γ A) ×'(motive_ΓextA : motive_1 (Γ.ext A)) ×' (motive_2 _ motive_ΓextA B) ×' Γ_IH ×' A_IH ×' B_IH)

def Ty.below
  {motive_1 : Con → Sort u}
  {motive_2 : (Γ : Con) → motive_1 Γ → Ty Γ → Sort u}
  : (Γ:  Con) → Ty Γ → Sort (max 1 u) :=
  @Ty.rec (fun _Γ => Sort (max 1 u)) (fun _Γ _Γ_IH _A => Sort (max 1 u))
    PUnit
    (fun Γ A Γ_IH A_IH => (motive_Γ : motive_1 Γ) ×' (motive_2 Γ motive_Γ A) ×' Γ_IH ×' A_IH)
    (@fun Γ motives_ty => (motive_1 Γ) ×' motives_ty)
    (@fun Γ A B Γ_IH A_IH B_IH => (motive_Γ : motive_1 Γ) ×' (motive_2 Γ motive_Γ A) ×'(motive_ΓextA : motive_1 (Γ.ext A)) ×' (motive_2 _ motive_ΓextA B) ×' Γ_IH ×' A_IH ×' B_IH)

noncomputable def Con.brecOn
  {motive_1 : Con → Sort u}
  {motive_2 : (Γ : Con) → motive_1 Γ → Ty Γ → Sort u}
  (minor1: ∀ Γ, Γ.below (motive_1 := motive_1) (motive_2 := motive_2) → motive_1 Γ)
  (minor2: ∀ Γ (A : Ty Γ), A.below (motive_1 := motive_1) (motive_2 := motive_2) → (Γ_IH : motive_1 Γ) → motive_2 Γ Γ_IH A)
  (Γ : Con) : motive_1 Γ :=
    @Con.recOn (fun Γ => motive_1 Γ ×' Γ.below (motive_1 := motive_1) (motive_2 := motive_2)) (fun Γ Γ_ih A => motive_2 Γ Γ_ih.1 A ×' @Ty.below motive_1 motive_2 Γ A) Γ
    ⟨minor1 nil ⟨⟩,⟨⟩⟩
    (fun Γ A Γ_IH A_IH => have := ⟨Γ_IH.1,A_IH.1,Γ_IH.2,A_IH.2⟩; ⟨minor1 (Γ.ext A) this,this⟩ )
    (@fun Γ Γ_IH => ⟨minor2 Γ Ty.U Γ_IH Γ_IH.fst,Γ_IH⟩)
    (@fun Γ A B Γ_IH A_IH B_IH =>
      have : @Ty.below motive_1 motive_2 Γ (A.Pi B) := ⟨Γ_IH.1,A_IH.1,minor1 _  ⟨Γ_IH.fst, ⟨A_IH.fst, Γ_IH.snd, A_IH.snd⟩⟩,minor2 _ _ B_IH.2 _,Γ_IH.2,A_IH.2,B_IH.2⟩
      ⟨minor2 _ _ this _,this⟩)
    |>.1

noncomputable def Ty.brecOn
  {motive_1 : Con → Sort u}
  {motive_2 : (Γ : Con) → motive_1 Γ → Ty Γ → Sort u}
  (minor1: ∀ Γ, Γ.below (motive_1 := motive_1) (motive_2 := motive_2) → motive_1 Γ)
  (minor2: ∀ Γ (A : Ty Γ), A.below (motive_1 := motive_1) (motive_2 := motive_2) → (Γ_IH : motive_1 Γ) → motive_2 Γ Γ_IH A)
  (Γ : Con) (A : Ty Γ) : motive_2 Γ (@Con.brecOn motive_1 motive_2 minor1 minor2 Γ) A :=
    @Ty.recOn (fun Γ => motive_1 Γ ×' Γ.below (motive_1 := motive_1) (motive_2 := motive_2)) (fun Γ Γ_ih A => motive_2 Γ Γ_ih.1 A ×' @Ty.below motive_1 motive_2 Γ A) Γ A
    ⟨minor1 .nil ⟨⟩,⟨⟩⟩
    (fun Γ A Γ_IH A_IH => ⟨minor1 (Γ.ext A)  ⟨Γ_IH.1,A_IH.1,Γ_IH.2,A_IH.2⟩,⟨Γ_IH.1,A_IH.1,Γ_IH.2,A_IH.2⟩⟩ )
    (@fun Γ Γ_IH => ⟨minor2 Γ Ty.U Γ_IH Γ_IH.fst,Γ_IH⟩)
    (@fun Γ A B Γ_IH A_IH B_IH =>
      have : @Ty.below motive_1 motive_2 Γ (A.Pi B) := ⟨Γ_IH.1,A_IH.1,minor1 _  ⟨Γ_IH.fst, ⟨A_IH.fst, Γ_IH.snd, A_IH.snd⟩⟩,minor2 _ _ B_IH.2 _,Γ_IH.2,A_IH.2,B_IH.2⟩
      ⟨minor2 _ _ this _,this⟩)
    |>.1

--set_option trace.Meta.Match.match true
--set_option trace.Elab.match true
--set_option trace.Elab.step true
set_option trace.Elab.definition.structural true
noncomputable def Ty.sizeOf {Γ : Con} (A : Ty Γ) : Nat :=
  match A with
    | .U => 0
    | .Pi A B => A.sizeOf + B.sizeOf +1
termination_by structural A


def foo : Nat → Bool
  | 0 => true
  | Nat.succ 0 => false
  | Nat.succ (.succ n) => foo n
