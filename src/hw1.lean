theorem easy (P Q: Prop) (HP : P) (HPQ: P → Q) : Q :=
    begin
        apply HPQ, -- now i just have to prove p -> Q
        exact HP -- i know HP of P 
    end

theorem prove_P_implies_Q (P Q : Prop)(HQ: Q): P → Q :=
    begin
        intro HP, -- assume HP of  P
        exact HQ,
    end

theorem P_implies_P (P: Prop) : P → P := 
    begin -- assume HP of P
        intro HP,
        apply HP
    end 

theorem needs_intros (P Q R : Prop)(HR : R): P → Q → R :=
    begin
        intro HP, 
        -- we have a proof of HP of P
        intro HQ,
        -- we have a proof of HQ of Q
        exact HR
    end 

theorem very_easy : true :=
begin
    exact trivial,
end


theorem very_hard : false :=
begin
    sorry,
end

theorem false_implies_false: false → false :=
    begin 
        intro Hfalse,
        exact Hfalse,
    end

theorem not_not (P: Prop): P → ¬ (¬ P) :=
                            -- ¬ P → ¬r P
begin
    intro HP,
    intro HnP,
    apply HnP,
    exact HP,
end

theorem contrapositive
  (P Q : Prop) (HPQ : P → Q) : ¬ Q → ¬ P :=
begin
    intro HnQ,
    intro HP,
    apply HnQ,
    apply HPQ,
    exact HP
end 
#print contrapositive

theorem P_imples_P_or_Q (P Q: Prop) (HP: P) : P ∨ Q :=
begin
    left,
    exact HP,
end
#print P_imples_P_or_Q

theorem Q_imples_P_or_Q (P Q: Prop) (HQ: Q): P ∨ Q :=
begin
    right,
    exact HQ,
end
#print Q_imples_P_or_Q

theorem or_symmetry (P Q: Prop): P ∨ Q → Q ∨ P :=
begin
    intro HPQ,
    cases HPQ with HP HQ,
    { right,
      exact HP,
    },
    { left,
      exact HQ,
    },
end
#print or_symmetry

theorem or_associative (P Q R: Prop):
P ∨ (Q ∨ R) → (P ∨ Q) ∨ R :=
begin
    intro HPQR,
    cases HPQR with HP HQR, 
    { 
        left,
      { 
          left,
          exact HP,
      } 
    },
    cases HQR with HQ' HR', 
    {
        left,
        {
            right,
            exact HQ',
        }
    },
    {   
        right,
        exact HR',
    }
end
#print or_associative


theorem and_definition (P Q: Prop)(HP : P)(HQ: Q): P ∧ Q :=
begin
    split,
        {exact HP,}
        {exact HQ,}
end
#print and_definition

theorem and_symmetric(P Q: Prop): P ∧ Q → Q ∧ P :=
begin 
    intro HPQ,
    cases HPQ with HP HQ,
    split,
        {exact HQ,},
        {exact HP,},
end
#print and_symmetric

theorem and_transitive(P Q R: Prop) :
(P ∧ Q) ∧ (Q ∧ R) → (P ∧ R) :=
begin
    intro HPQandHQR,
    cases HPQandHQR with HPQ HQR,
        cases HPQ with HP HQ,
            split, 
                {exact HP,},
        cases HQR with HQ' HR,
            exact HR,
end
#print and_transitive
