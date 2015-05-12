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

Definition Qstate :=
  (list nat * list nat * list nat) %type.

Definition GetCols :=
  fun q:Qstate => 
    match q with
    | (c,sw,se) => c
    end.

Definition GetSWDiags :=
  fun q:Qstate => 
    match q with
    | (c,sw,se) => sw
    end.

Definition GetSEDiags :=
  fun q:Qstate => 
    match q with
    | (c,sw,se) => se
    end.

Definition PutCols (c: list nat) :=
  fun q:Qstate => 
    match q with 
    | (old_c,sw,se) => (c,sw,se) %type
    end.

Definition PutSWDiags (sw: list nat) :=
  fun q:Qstate => 
    match q with 
    | (c,old_sw,se) => (c,sw,se) %type
    end.

Definition PutSEDiags (se: list nat) :=
  fun q:Qstate => 
    match q with 
    | (c,sw,old_se) => (c,sw,se) %type
    end.

Definition tryPutCol c :=
  cols = getCols
  match c with
  | cols => None
  | _ => PutCols c
  end.
