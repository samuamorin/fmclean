
section propositional

variables P Q R : Prop


------------------------------------------------
-- Proposições de dupla negaço:
------------------------------------------------

theorem doubleneg_intro :
  P → ¬¬P  :=
begin
  intro hp,
  intro np,
  exact np hp,
end

theorem doubleneg_elim :
  ¬¬P → P  :=
begin
  intro hnnp,
  by_cases p : P, --LEM cria dois dados novos P e ¬P
                  -- e dois jogos para cada um
  exact p, -- fecha o primeiro jogo com dado P
  exfalso, -- transforma alvo em boom  
  contradiction, -- tenho em meus dados ¬P e ¬¬P 
end

theorem doubleneg_law :
  ¬¬P ↔ P  :=
begin
  split,
  exact doubleneg_elim P, 
  exact doubleneg_intro P,
end

------------------------------------------------
-- Comutatividade dos ∨,∧:
------------------------------------------------

theorem disj_comm :
  (P ∨ Q) → (Q ∨ P)  :=
begin
  intro hor,
  cases hor with hp hq,
  -- case left
    right,
    exact hp,
  -- case rigth
    left,
    exact hq,
end

theorem conj_comm :
  (P ∧ Q) → (Q ∧ P)  :=
begin
  intro hand,
  cases hand with hp hq,
  split,
  -- left
    exact hq,
  -- rigth,
    exact hp,
end


------------------------------------------------
-- Proposições de interdefinabilidade dos →,∨:
------------------------------------------------

theorem impl_as_disj_converse :
  (¬P ∨ Q) → (P → Q)  :=
begin
  intro hor,
  intro hp,
  cases hor with hnp hq,
  -- left (¬P)
    contradiction,
  -- right (Q)
    exact hq,
end

theorem disj_as_impl :
  (P ∨ Q) → (¬P → Q)  :=
begin
  intro hor,
  intro hnp,
  cases hor with hp hq,
  -- left (P)
     contradiction,
  -- right (Q)
     exact hq,
end


------------------------------------------------
-- Proposições de contraposição:
------------------------------------------------

theorem impl_as_contrapositive :
  (P → Q) → (¬Q → ¬P)  :=
begin
  intro hpq,
  intro hnq,
  by_cases hp: P, -- LEM
     -- case LEM P
     have hq: Q := hpq hp,
     contradiction,
     -- case LEM ¬P
     exact hp,
end

theorem impl_as_contrapositive_converse :
  (¬Q → ¬P) → (P → Q)  :=
begin

  intro hnqnp,
  intro hp,
  by_cases hq: Q, -- LEM Q
  --- case LEM Q
     exact hq,
  --- case LEM ¬Q
     have hnp: ¬P := hnqnp hq,
     contradiction, 
end

theorem contrapositive_law :
  (P → Q) ↔ (¬Q → ¬P)  :=
begin
  split,
  -- visto do tópico do Ian, como reaproveitar teoremas 
  exact impl_as_contrapositive P Q,
  exact impl_as_contrapositive_converse P Q,
end


------------------------------------------------
-- A irrefutabilidade do LEM:
------------------------------------------------

theorem lem_irrefutable :
  ¬¬(P∨¬P)  :=
begin
  intro hnorp,
  have hpornp : P∨¬P,-- demonstrar algo nos dados
      right,
      intro hp,
      have hpornp : P∨¬P, -- demonstrar algo nos dados
         left,
         exact hp,
         contradiction,
      contradiction,
end



------------------------------------------------
-- A lei de Peirce
------------------------------------------------

theorem peirce_law_weak :
  ((P → Q) → P) → ¬¬P  :=
begin
  intro hpqp,
  intro hnp,
  have hpq: (P → Q),
     intro hp,
     contradiction,
  have hp : P := hpqp hpq,
  contradiction,
end


------------------------------------------------
-- Proposições de interdefinabilidade dos ∨,∧:
------------------------------------------------

theorem disj_as_negconj :
  P∨Q → ¬(¬P∧¬Q)  :=
begin
  intro hor,
  intro hnand,
  cases hnand with hnp hnq,
  cases hor with horp horq,
  -- case P
     contradiction,
  -- case Q
     contradiction,
end

theorem conj_as_negdisj :
  P∧Q → ¬(¬P∨¬Q)  :=
begin
  intro hand,
  intro hnor,
  cases hand with hp hq,
  cases hnor with hnp hnq,
  -- case ¬P
     contradiction,
  -- case ¬Q
     contradiction,
end


------------------------------------------------
-- As leis de De Morgan para ∨,∧:
------------------------------------------------

theorem demorgan_disj :
  ¬(P∨Q) → (¬P ∧ ¬Q)  :=
begin
   intro hnpq,
   split,
   --- Part L
      intro hp,
      have hor : P∨Q,
         left,
         exact hp,
      contradiction,
    --- Part R
      intro hq,
      have hor: P∨Q,
         right,
         exact hq,
      contradiction,
end

theorem demorgan_disj_converse :
  (¬P ∧ ¬Q) → ¬(P∨Q)  :=
begin
  intro hnpnq,
  intro hporq,
  cases hnpnq with hnp hnq,
  cases hporq with hp hq,
      -- case P
      contradiction,
      -- Case Q
      contradiction,
  ---
end

theorem demorgan_conj :
  ¬(P∧Q) → (¬Q ∨ ¬P)  :=
begin
  intro hnpq,
  by_cases lem: Q,
    --- lem Q
    right,
    intro hp,
    have hpandq : (P∧Q),
       split,
       exact hp,
       exact lem, 
    exact hnpq hpandq,
    --- lem ¬Q
    left,
    exact lem,
end

theorem demorgan_conj_converse :
  (¬Q ∨ ¬P) → ¬(P∧Q)  :=
begin
  intro hnqornp,
  intro hpandq,
  cases hpandq with hp hq,
  cases hnqornp with hnq hnp,
     --- case ¬Q
     contradiction,
     -- case ¬P
     contradiction,
end

theorem demorgan_conj_law :
  ¬(P∧Q) ↔ (¬Q ∨ ¬P)  :=
begin
  split,
  exact demorgan_conj P Q,
  exact demorgan_conj_converse P Q,
end

theorem demorgan_disj_law :
  ¬(P∨Q) ↔ (¬P ∧ ¬Q)  :=
begin
  split,
  exact demorgan_disj P Q,
  exact demorgan_disj_converse P Q,
end

------------------------------------------------
-- Proposições de distributividade dos ∨,∧:
------------------------------------------------

theorem distr_conj_disj :
  P∧(Q∨R) → (P∧Q)∨(P∧R)  :=
begin
  intro hpqr,
  cases hpqr with hp hqorr,
  right,
  split,
     exact hp,
     cases hqorr,

end

theorem distr_conj_disj_converse :
  (P∧Q)∨(P∧R) → P∧(Q∨R)  :=
begin
  sorry,
end

theorem distr_disj_conj :
  P∨(Q∧R) → (P∨Q)∧(P∨R)  :=
begin
  sorry,
end

theorem distr_disj_conj_converse :
  (P∨Q)∧(P∨R) → P∨(Q∧R)  :=
begin
  sorry,
end


------------------------------------------------
-- Currificação
------------------------------------------------

theorem curry_prop :
  ((P∧Q)→R) → (P→(Q→R))  :=
begin
  intro pandqr,
  intro hp,
  intro hq,
  have hpand: (P∧Q),
     split,
     exact hp,
     exact hq,
  exact pandqr hpand, 
end

theorem uncurry_prop :
  (P→(Q→R)) → ((P∧Q)→R)  :=
begin
  intro hpqr,
  intro pandq,
  cases pandq with hp hq,
  exact hpqr hp hq,
end


------------------------------------------------
-- Reflexividade da →:
------------------------------------------------

theorem impl_refl :
  P → P  :=
begin
  intro hp,
  exact hp,
end

------------------------------------------------
-- Weakening and contraction:
------------------------------------------------

theorem weaken_disj_right :
  P → (P∨Q)  :=
begin
  intro hp,
  left,
  exact hp,
end

theorem weaken_disj_left :
  Q → (P∨Q)  :=
begin
  intro hq,
  right,
  exact hq,
end

theorem weaken_conj_right :
  (P∧Q) → P  :=
begin
  intro pandq,
  exact pandq.left,
end

theorem weaken_conj_left :
  (P∧Q) → Q  :=
begin
  intro hpq,
  exact hpq.right,
end

theorem conj_idempot :
  (P∧P) ↔ P :=
begin
  split,
  intro pandp,
  exact pandp.right,
  intro hp,
  split,
     repeat{exact hp,},
end

theorem disj_idempot :
  (P∨P) ↔ P  :=
begin
  split,
  intro porp,
  cases porp,
   repeat{exact porp,},
  intro hp,
    left,
    exact hp,
end

end propositional


----------------------------------------------------------------


section predicate

variable U : Type
variables P Q : U -> Prop


------------------------------------------------
-- As leis de De Morgan para ∃,∀:
------------------------------------------------

theorem demorgan_exists :
  ¬(∃x, P x) → (∀x, ¬P x)  :=
begin
  sorry,
end

theorem demorgan_exists_converse :
  (∀x, ¬P x) → ¬(∃x, P x)  :=
begin
  sorry,
end

theorem demorgan_forall :
  ¬(∀x, P x) → (∃x, ¬P x)  :=
begin
  sorry,
end

theorem demorgan_forall_converse :
  (∃x, ¬P x) → ¬(∀x, P x)  :=
begin
  sorry,
end

theorem demorgan_forall_law :
  ¬(∀x, P x) ↔ (∃x, ¬P x)  :=
begin
  sorry,
end

theorem demorgan_exists_law :
  ¬(∃x, P x) ↔ (∀x, ¬P x)  :=
begin
  sorry,
end


------------------------------------------------
-- Proposições de interdefinabilidade dos ∃,∀:
------------------------------------------------

theorem exists_as_neg_forall :
  (∃x, P x) → ¬(∀x, ¬P x)  :=
begin
  sorry,
end

theorem forall_as_neg_exists :
  (∀x, P x) → ¬(∃x, ¬P x)  :=
begin
  sorry,
end

theorem forall_as_neg_exists_converse :
  ¬(∃x, ¬P x) → (∀x, P x)  :=
begin
  sorry,
end

theorem exists_as_neg_forall_converse :
  ¬(∀x, ¬P x) → (∃x, P x)  :=
begin
  sorry,
end

theorem forall_as_neg_exists_law :
  (∀x, P x) ↔ ¬(∃x, ¬P x)  :=
begin
  sorry,
end

theorem exists_as_neg_forall_law :
  (∃x, P x) ↔ ¬(∀x, ¬P x)  :=
begin
  sorry,
end


------------------------------------------------
--  Proposições de distributividade de quantificadores:
------------------------------------------------

theorem exists_conj_as_conj_exists :
  (∃x, P x ∧ Q x) → (∃x, P x) ∧ (∃x, Q x)  :=
begin
  sorry,
end

theorem exists_disj_as_disj_exists :
  (∃x, P x ∨ Q x) → (∃x, P x) ∨ (∃x, Q x)  :=
begin
  sorry,
end

theorem exists_disj_as_disj_exists_converse :
  (∃x, P x) ∨ (∃x, Q x) → (∃x, P x ∨ Q x)  :=
begin
  sorry,
end

theorem forall_conj_as_conj_forall :
  (∀x, P x ∧ Q x) → (∀x, P x) ∧ (∀x, Q x)  :=
begin
  sorry,
end

theorem forall_conj_as_conj_forall_converse :
  (∀x, P x) ∧ (∀x, Q x) → (∀x, P x ∧ Q x)  :=
begin
  sorry,
end


theorem forall_disj_as_disj_forall_converse :
  (∀x, P x) ∨ (∀x, Q x) → (∀x, P x ∨ Q x)  :=
begin
  sorry,
end


/- NOT THEOREMS --------------------------------

theorem forall_disj_as_disj_forall :
  (∀x, P x ∨ Q x) → (∀x, P x) ∨ (∀x, Q x)  :=
begin
end

theorem exists_conj_as_conj_exists_converse :
  (∃x, P x) ∧ (∃x, Q x) → (∃x, P x ∧ Q x)  :=
begin
end

---------------------------------------------- -/

end predicate
