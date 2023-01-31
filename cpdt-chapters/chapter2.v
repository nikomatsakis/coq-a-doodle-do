Require Import Bool Arith List Cpdt.CpdtTactics.
Set Implicit Arguments.

Inductive binop : Set := Plus | Times.

Inductive exp : Set := 
| Const : nat -> exp 
| Binop : binop -> exp -> exp -> exp.

Definition binopDenote (b : binop) : nat -> nat -> nat :=
    match b with 
    | Plus => plus
    | Times => mult
    end.

Fixpoint expDenote (e : exp) : nat :=
    match e with
    | Const n => n
    | Binop b e1 e2 => (binopDenote b) (expDenote e1) (expDenote e2)
    end.

Eval simpl in expDenote (Const 42).

(* -------------------------------- *)

Inductive instr : Set :=
| iConst : nat -> instr
| iBinop : binop -> instr.

Definition prog := list instr.

Definition stack := list nat.

Definition instrDenote (i: instr) (s : stack) : option stack :=
    match i with
    | iConst n => Some (n :: s)
    | iBinop b =>
        match s with
        | arg1 :: arg2 :: s' =>
            Some ((binopDenote b) arg1 arg2 :: s')
        | _ =>
            None
        end
    end.

Fixpoint progDenote (p : prog) (s : stack) : option stack :=
    match p with
    | nil => Some s
    | i :: p' =>
        match instrDenote i s with
        | None => None
        | Some s' => progDenote p' s'
        end
    end.

Fixpoint compile (e : exp) : prog :=
    match e with
    | Const n => iConst n :: nil
    | Binop b e1 e2 => compile e2 ++ compile e1 ++ iBinop b :: nil
    end.

Eval simpl in (compile (Const 42)).

(* "Compiling e and executing it is the same as
   pushing the value of expDonte on the stack" *)
Lemma compile_correct' : forall e p s, 
    progDenote (compile e ++ p) s = progDenote p (expDenote e :: s).
    induction e; crush.

Theorem compile_correct : 
    forall e, progDenote (compile e) nil = Some (expDenote e :: nil).