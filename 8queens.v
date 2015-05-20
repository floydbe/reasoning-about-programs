Notation "x :: l" := (cons x l) (at level 60, right associativity).
Notation "[ ]" := nil.
Notation "[ x ; .. ; y ]" := (cons x .. (cons y nil) ..).

Fixpoint beq_nat n m : bool :=
  match n, m with
    | O, O => true
    | O, S _ => false
    | S _, O => false
    | S n1, S m1 => beq_nat n1 m1
  end.

Definition l_append (a:nat) (l:list nat) : list nat :=
  match l with
  | [] => [a]
  | h::t => a::(h::t)
  end.

Fixpoint l_in (a:nat) (l:list nat) : bool :=
  match l with
  | [] => false
  | h::t => if beq_nat a h then true else l_in a t
  end.

Inductive Qstate  : Type :=
  | qstate : list nat -> list nat -> list nat -> Qstate.

Definition GetCols (q:option Qstate) : list nat :=
  match q with
  | Some (qstate c sw se) => c
  | None => []
  end.

Definition GetSWDiags (q:option Qstate) : list nat :=
  match q with
  | Some (qstate c sw se) => sw
  | None => []
  end.

Definition GetSEDiags (q:option Qstate) : list nat :=
  match q with
  | Some (qstate c sw se) => se
  | None => []
  end.

Definition PutCols (n:nat) (q:option Qstate) : option Qstate :=
  match q with 
  | Some (qstate c sw se) => Some (qstate (l_append n c)  sw se)
  | None => None
  end.

Definition PutSWDiags (n:nat) (q:option Qstate) : option Qstate :=
  match q with 
  | Some (qstate c sw se) => Some (qstate c (l_append n sw) se)
  | None => None
  end.

Definition PutSEDiags (n:nat) (q:option Qstate) : option Qstate :=
  match q with 
  | Some (qstate c sw se) => Some (qstate c sw (l_append n se))
  | None => None
  end.

Definition tryPutCol (c:nat) (q:option Qstate) : option Qstate :=
  match q with
  | None => None
  | _ =>
    let cols := GetCols q in
    if l_in c cols then None else PutCols c q
  end.

Definition tryPutSWDiag (sw:nat) (q:option Qstate) : option Qstate :=
  match q with
  | None => None
  | _ => 
    let swdiags := GetSWDiags q in
    if l_in sw swdiags then None else PutSWDiags sw q
  end.

Definition tryPutSEDiag (se:nat) (q:option Qstate) : option Qstate :=
  match q with
  | None => None
  | _ =>
    let sediags := GetSEDiags q in
    if l_in se sediags then None else PutSEDiags se q
  end.

Definition place (r c : nat) (q:option Qstate) : option Qstate :=
  match q with
  | None => None
  | _ => 
    let q0 := tryPutCol c q in
    let q1 := tryPutSWDiag (c+7-r) q0 in
    let q2 := tryPutSEDiag (c+r) q1 in
    q2
  end.

Fixpoint tryEach (l:list nat) (q:option Qstate) (f: nat -> option Qstate ) : option Qstate :=
  match q with
  | None => None
  | _ =>
    match l with
    | [] => None
    | h::t => 
      match f h with
      | None => tryEach t q f
      | Some q0 => Some q0 
      end
    end
  end.

Fixpoint queens (r:nat) (cols:list nat) (q:option Qstate) : option Qstate :=
  match r with
  | O => q
  | S n => tryEach cols q (fun c => match place n c q with 
                                 | None => None
                                 | Some q0 => queens n cols (Some q0)
                                 end)
  end.


Definition q:option Qstate := Some (qstate [] [] []).

Definition solution := queens 8 ([0;1;2;3;4;5;6;7;8]) q.

Compute GetCols solution.