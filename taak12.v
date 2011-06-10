Definition T:=R.
Variable P:T->B.
Variable Q:T->B.
Variable R:T->B.

Theorem tijd1:
    (forall t:T, t>=2 -> P t) ->
    (forall t:T, t>=3 -> P t).
Proof.
imp_i H.
all_i s.
imp_i H2.
imp_e (s >= 2).
all_e (forall x, x >= 2 -> P x) s.
assumption.
lin_solve.
Qed.

Theorem tijd2:
    (P 2) ->
    (forall t:T, P t -> Q (t+3)) ->
    (Q 5).
Proof.
imp_i H.
imp_i H2.
imp_e (P 2).
Focus 2.
assumption.
replace 5 with (2 + 3).
all_e (forall x, P x -> Q (x + 3)) 2.
assumption.
lin_solve.
Qed.

Theorem tijd3:
    (Q 0) ->
    (forall t:T, Q t -> (forall u:T, u>=t+2 -> P u)) ->
    (forall t:T, t>=3 -> P t).

Theorem tijd4:
    (forall t:T, P t -> Q (t+1) \/ Q (t+2)) ->
    (forall t:T, P t -> (exists u:T, u>=t+1 /\ Q u)).
Proof.
imp_i H.
all_i x.
imp_i H2.
dis_e (Q (x + 1) \/ Q (x + 2)) H3 H4.
imp_e (P x).
all_e (forall t:T, P t -> Q (t + 1) \/ Q (t + 2)) x.
assumption.
assumption.
exi_i (x + 1).
con_i.
lin_solve.
assumption.
exi_i (x + 2).
con_i.
lin_solve.
assumption.
Qed.

Theorem tijd5:
    (forall t:T, (exists u:T, u<=t-5 /\ Q u) -> P t) ->
    (forall t:T, Q t -> P (t+5)).

Theorem tijd6:
    (forall t:T, P t -> Q (t+2)) ->
    (forall t:T, Q t -> R (t+3)) ->
    (forall t:T, P t -> R (t+5)).
imp_i H.
imp_i H2.
all_i x.
imp_i H3.
replace (x + 5) with (x + 2 + 3).
imp_e (Q (x + 2)).
all_e (forall t:T, Q t -> R (t + 3)) (x + 2).
assumption.
imp_e (P x).
all_e (forall t:T, P t -> Q (t + 2)) x.
assumption.
assumption.
lin_solve.
Qed.

Theorem tijd7:
    (forall t:T, P t -> (exists u:T, u in (t+2,t+5] /\ Q u)) ->
    (forall t:T, P t -> (exists u:T, u in (t+1,t+6] /\ Q u)).

Theorem tijd8:
    (forall t:T, P t -> (exists u:T, u in (t+2,t+5] /\ Q u)) ->
    (forall t:T, P t -> (exists u:T, u in (t,t+3] /\ Q (u+2))).

Theorem tijd9:
    (forall t:T, P t -> (exists u:T, u in [t+2,t+5) /\ Q u)) ->
    (forall t:T, Q t -> R (t+3)) ->
    (forall t:T, P t -> (exists u:T, u in [t+5,t+8) /\ R u)).

Theorem tijd10:
    (forall t:T, P t -> (forall u:T, u<t-5 -> Q u)) ->
    (forall t:T, (exists u:T, t+5<u /\ P u) -> Q t).
Proof.
imp_i H.
all_i s.
imp_i H2.
exi_e (exists u:T, s + 5 < u /\ P u) y H3.
assumption.
imp_e (s < y - 5).
all_e (forall u:T, u < y - 5 -> Q u) s.
imp_e (P y).
all_e (forall t:T, P t -> (forall u:T, u < t - 5 -> Q u)) y.
assumption.
con_e2 (s + 5 < y).
assumption.
imp_e (s + 5 < y).
imp_i H43.
lin_solve.
con_e1 (P y).
assumption.
Qed.










