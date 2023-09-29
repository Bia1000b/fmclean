
section propositional

variables P Q R : Prop


------------------------------------------------
-- Proposições de dupla negaço:
------------------------------------------------

theorem doubleneg_intro :
  P → ¬¬P  :=
begin
  intro p,
  intro pb,
  have b : false := pb p,
  contradiction,
  
end

theorem doubleneg_elim :
  ¬¬P → P  :=
begin
  intro nnp,
  by_cases h : P,
  exact h,
  have k : false := nnp h,
  exfalso,
  exact k,
end

theorem doubleneg_law :
  ¬¬P ↔ P  :=
begin
  split,
  intro nnp,
  by_cases h : P,
  exact h,
  have k : false := nnp h,
  exfalso,
  exact k,
  intro p,
  intro np,
  have w : false := np p,
  exact w,
end

------------------------------------------------
-- Comutatividade dos ∨,∧:
------------------------------------------------

theorem disj_comm :
  (P ∨ Q) → (Q ∨ P)  :=
begin
  intro pq,
  cases pq with hp hq,
  right,
  exact hp,
  left,
  exact hq,
end

theorem conj_comm :
  (P ∧ Q) → (Q ∧ P)  :=
begin
  intro pq,
  cases pq,
  split,
  exact pq_right,
  exact pq_left,
end


------------------------------------------------
-- Proposições de interdefinabilidade dos →,∨:
------------------------------------------------

theorem impl_as_disj_converse :
  (¬P ∨ Q) → (P → Q)  :=
begin
  intro npq,
  intro p,
  cases npq,
  have k : false := npq p,
  exfalso,
  exact k,
  exact npq,
end

theorem disj_as_impl :
  (P ∨ Q) → (¬P → Q)  :=
begin
  intro pq,
  intro np,
  cases pq,
  have k : false := np pq,
  exfalso,
  exact k,
  exact pq,
end


------------------------------------------------
-- Proposições de contraposição:
------------------------------------------------

theorem impl_as_contrapositive :
  (P → Q) → (¬Q → ¬P)  :=
begin
  intro pq,
  intro nq,
  intro p,
  have q := pq p,
  have k : false := nq q,
  exact k,
end

theorem impl_as_contrapositive_converse :
  (¬Q → ¬P) → (P → Q)  :=
begin
  intro nqnp,
  intro p,
  by_cases h: Q,
  exact h,
  have np := nqnp h,
  have k : false := np p,
  exfalso,
  exact k,
end

theorem contrapositive_law :
  (P → Q) ↔ (¬Q → ¬P)  :=
begin
  split,
  intro pq,
  intro nq,
  intro p,
  have q := pq p,
  have k : false := nq q,
  exact k,
  intro nqnp,
  intro p,
  by_cases h: Q,
  exact h,
  have np := nqnp h,
  have k : false := np p,
  exfalso,
  exact k,
end


------------------------------------------------
-- A irrefutabilidade do LEM:
------------------------------------------------

theorem lem_irrefutable :
  ¬¬(P∨¬P)  :=
begin
  intro k,
  by_cases h: P,
  apply k,
  left,
  exact h,
  apply k,
  right,
  exact h,
end


------------------------------------------------
-- A lei de Peirce
------------------------------------------------

theorem peirce_law_weak :
  ((P → Q) → P) → ¬¬P  :=
begin
  intro pqp,
  intro np,
  apply np,
  apply pqp,
  intro p,
  have k : false := np p,
  exfalso,
  exact k,
end


------------------------------------------------
-- Proposições de interdefinabilidade dos ∨,∧:
------------------------------------------------

theorem disj_as_negconj :
  P∨Q → ¬(¬P∧¬Q)  :=
begin
  intro pq,
  intro npnq,
  cases npnq,
  cases pq,
  have h : false := npnq_left pq,
  exact h,
  have k : false := npnq_right pq,
  exact k,
end

theorem conj_as_negdisj :
  P∧Q → ¬(¬P∨¬Q)  :=
begin
  intro pq,
  intro npnq,
  cases pq,
  cases npnq,
  have h : false := npnq pq_left,
  exact h,
  have k : false := npnq pq_right,
  exact k,
end


------------------------------------------------
-- As leis de De Morgan para ∨,∧:
------------------------------------------------

theorem demorgan_disj :
  ¬(P∨Q) → (¬P ∧ ¬Q)  :=
begin
  intro npq,
  split,
  intro p,
  apply npq,
  left,
  exact p,
  intro q,
  apply npq,
  right,
  exact q,
end

theorem demorgan_disj_converse :
  (¬P ∧ ¬Q) → ¬(P∨Q)  :=
begin
  intro npnq,
  intro pq,
  cases npnq,
  cases pq,
  apply npnq_left,
  exact pq,
  apply npnq_right,
  exact pq,
end

theorem demorgan_conj :
  ¬(P∧Q) → (¬Q ∨ ¬P)  :=
begin
  intro npq,
  by_cases h : Q,
  right,
  intro p,
  apply npq,
  split,
  exact p,
  exact h,
  left,
  exact h,
end

theorem demorgan_conj_converse :
  (¬Q ∨ ¬P) → ¬(P∧Q)  :=
begin
  intro nqnp,
  intro pq,
  cases pq,
  cases nqnp,
  apply nqnp,
  exact pq_right,
  apply nqnp,
  exact pq_left,
end

theorem demorgan_conj_law :
  ¬(P∧Q) ↔ (¬Q ∨ ¬P)  :=
begin
  split,
  intro npq,
  by_cases q : Q,
  right,
  intro p,
  apply npq,
  split,
  exact p,
  exact q,
  left,
  exact q,
  intro nqnp,
  intro pq,
  cases pq,
  cases nqnp,
  apply nqnp,
  exact pq_right,
  apply nqnp,
  exact pq_left,
end

theorem demorgan_disj_law :
  ¬(P∨Q) ↔ (¬P ∧ ¬Q)  :=
begin
  split,
  intro npq,
  split,
  intro p,
  apply npq,
  left,
  exact p,
  intro q,
  apply npq,
  right,
  exact q,
  intro npnq,
  intro pq,
  cases npnq,
  cases pq,
  apply npnq_left,
  exact pq,
  apply npnq_right,
  exact pq,
end

------------------------------------------------
-- Proposições de distributividade dos ∨,∧:
------------------------------------------------

theorem distr_conj_disj :
  P∧(Q∨R) → (P∧Q)∨(P∧R)  :=
begin
  intro pqr,
  cases pqr with p pqr_right,
  cases pqr_right with q r,
  left,
  split,
  exact p,
  exact q,
  right,
  split,
  exact p,
  exact r,
end

theorem distr_conj_disj_converse :
  (P∧Q)∨(P∧R) → P∧(Q∨R)  :=
begin
  intro pqpr,
  split,
  cases pqpr,
  cases pqpr,
  exact pqpr_left,
  cases pqpr,
  exact pqpr_left,
  cases pqpr,
  cases pqpr,
  left,
  exact pqpr_right,
  cases pqpr,
  right,
  exact pqpr_right,
end

theorem distr_disj_conj :
  P∨(Q∧R) → (P∨Q)∧(P∨R)  :=
begin
  intro pqr,
  split,
  cases pqr,
  left,
  exact pqr,
  cases pqr with q r,
  right,
  exact q,
  cases pqr with p qr,
  left,
  exact p,
  cases qr with q r,
  right,
  exact r,
end

theorem distr_disj_conj_converse :
  (P∨Q)∧(P∨R) → P∨(Q∧R)  :=
begin
  intro pqpr,
  cases pqpr with pq pr,
  cases pq,
  left,
  exact pq,
  cases pr,
  left,
  exact pr,
  right,
  split,
  exact pq,
  exact pr,
end


------------------------------------------------
-- Currificação
------------------------------------------------

theorem curry_prop :
  ((P∧Q)→R) → (P→(Q→R))  :=
begin
  intro pqr,
  intro p,
  intro q,
  have pq : P∧Q,
  split,
  exact p,
  exact q,
  apply pqr,
  exact pq,
end

theorem uncurry_prop :
  (P→(Q→R)) → ((P∧Q)→R)  :=
begin
  intro pqr,
  intro pq,
  cases pq with p q,
  apply pqr,
  exact p,
  exact q,
end


------------------------------------------------
-- Reflexividade da →:
------------------------------------------------

theorem impl_refl :
  P → P  :=
begin
  intro p,
  exact p,
end

------------------------------------------------
-- Weakening and contraction:
------------------------------------------------

theorem weaken_disj_right :
  P → (P∨Q)  :=
begin
  intro p,
  left,
  exact p,
end

theorem weaken_disj_left :
  Q → (P∨Q)  :=
begin
  intro q,
  right,
  exact q,
end

theorem weaken_conj_right :
  (P∧Q) → P  :=
begin
  intro pq,
  cases pq with p q,
  exact p,
end

theorem weaken_conj_left :
  (P∧Q) → Q  :=
begin
  intro pq,
  cases pq with p q,
  exact q,
end

theorem conj_idempot :
  (P∧P) ↔ P :=
begin
  split,
  intro pp,
  cases pp with p p,
  exact p,
  intro p,
  split,
  exact p,
  exact p,
end

theorem disj_idempot :
  (P∨P) ↔ P  :=
begin
  split,
  intro pp,
  cases pp with p p,
  exact p,
  exact p,
  intro p,
  left,
  exact p,
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
  intro h,
  intro a,
  intro pa,
  apply h,
  existsi a,
  exact pa,
end

theorem demorgan_exists_converse :
  (∀x, ¬P x) → ¬(∃x, P x)  :=
begin
  intro h,
  intro k,
  cases k with a ha,
  have w := h(a),
  apply w,
  exact ha,
end

theorem demorgan_forall :
  ¬(∀x, P x) → (∃x, ¬P x)  :=
begin
  intro h,
  by_contradiction kboom,
  apply h,
  intro a,
  by_contradiction wboom,
  apply kboom,
  existsi a,
  exact wboom, 
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
