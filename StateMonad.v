Class Monad (M: Type -> Type) := {
  ret : forall {A}, A -> M A ;
  bind : forall {A B}, M A -> (A -> M B) -> M B
}.

Definition stateTrans (s:Type) (a:Type) : Type :=
  s -> s * a.

Definition st_ret (S A : Type) (a:A) : stateTrans S A :=
  fun s:S => (s,a).

Definition st_bind (S A B : Type) (st: stateTrans S A) (f: A -> stateTrans S B) : stateTrans S B :=
  fun s:S => f (snd (st s)) s.

Instance State_monad (S:Type) : Monad (stateTrans S) := {
  ret := st_ret S ;
  bind := st_bind S 
}.

Definition stateTransEx (S:Type) (A:Type) : Type :=
  S -> option (S * A).

Definition st_ret_ex (S A : Type) (a:A) : stateTransEx S A :=
  fun s:S => Some (s,a).

Definition st_bind_ex (S A B : Type) (st: stateTransEx S A) (f: A -> stateTransEx S B) : stateTransEx S B :=
  fun s:S => 
    match st s with 
    | Some x => f (snd x) s
    | None => None
    end.

Instance state_ex_monad (S:Type) : Monad (stateTransEx S) := {
  ret := st_ret_ex S;
  bind := st_bind_ex S
}.

Definition mzero (S A : Type) : stateTransEx S A :=
  fun s:S => None.

Definition mplus (S A : Type) (st0: stateTransEx S A) (st1: stateTransEx S A) : (stateTransEx S A) :=
  fun s:S =>
    match st0 s with
    | Some (s0,x) => Some (s0,x)
    | None => st1 s
    end.

Inductive Qstate  : Type :=
  | qstate : list nat -> list nat -> list nat -> Qstate.

Definition GetCols (q:Qstate) : list nat :=
  match q with
  | qstate c sw se => c
  end.

Definition GetSWDiags (q:Qstate) : list nat :=
  match q with
  | qstate c sw se => sw
  end.

Definition GetSEDiags (q:Qstate) : list nat :=
  match q with
  | qstate c sw se => se
  end.

Definition PutCols (c: list nat) (q:Qstate) : Qstate :=
  match q with 
  | qstate old_c sw se => qstate c sw se
  end.

Definition PutSWDiags (sw: list nat) (q:Qstate) : Qstate :=
  match q with 
  | qstate c old_sw se => qstate c sw se
  end.

Definition PutSEDiags (se: list nat) (q:Qstate) : Qstate :=
  match q with 
  | qstate c sw old_se => qstate c sw se
  end.

Fixpoint beq_nat n m : bool :=
  match n, m with
    | O, O => true
    | O, S _ => false
    | S _, O => false
    | S n1, S m1 => beq_nat n1 m1
  end.

Fixpoint nat_list_eq (l1 l2 : list nat) : bool :=
  match l1, l2 with
  | nil, nil => true
  | cons a b, cons c d => if beq_nat a c then nat_list_eq b d else false
  | _,_ => false
  end.

Notation "x :: l" := (cons x l) (at level 60, right associativity).
Notation "[ ]" := nil.
Notation "[ x ; .. ; y ]" := (cons x .. (cons y nil) ..).

Fixpoint guard (l:list nat) : bool :=
  match l with
  | nil => false
  | cons h t => if beq_nat h 1 then true else guard t
  end.

Definition tryPutCol (c:list nat) (q:Qstate) : Qstate  :=
  let cols := GetCols q in
  if guard cols then q else (PutCols c q).

Definition tryPutSWDiags (sw:list nat) (q:Qstate) : Qstate  :=
  let swdiags := GetSWDiags q in
  if guard swdiags then q else (PutSWDiags sw q).

Definition tryPutSEDiags (se:list nat) (q:Qstate) : Qstate  :=
  let sediags := GetSEDiags q in
  if guard sediags then q else (PutSEDiags se q).

Definition nat_to_list (n:nat) : list nat :=
  if beq_nat n 0 then [1;0;0;0;0;0;0;0] else
  if beq_nat n 1 then [0;1;0;0;0;0;0;0] else
  if beq_nat n 2 then [0;0;1;0;0;0;0;0] else
  if beq_nat n 3 then [0;0;0;1;0;0;0;0] else
  if beq_nat n 4 then [0;0;0;0;1;0;0;0] else
  if beq_nat n 5 then [0;0;0;0;0;1;0;0] else
  if beq_nat n 6 then [0;0;0;0;0;0;1;0] else
  if beq_nat n 7 then [0;0;0;0;0;0;0;1] else
  [].

Definition place (r c : nat) (q:Qstate) : Qstate :=
  let q0 := tryPutCol (nat_to_list c) q in
  let q1 := tryPutSWDiags (nat_to_list (c-r)) q0 in
  let q2 := tryPutSEDiags (nat_to_list (c+r)) q1 in
  q2.

Definition q:Qstate := qstate [0;0;0;0;0;0;0;0] [0;0;0;0;0;0;0;0] [0;0;0;0;0;0;0;0]. 

Compute GetCols q.
Compute place 0 0 q.
Compute GetCols q.
Compute guard (nat_to_list 2).
