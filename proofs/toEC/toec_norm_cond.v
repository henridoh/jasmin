From mathcomp Require Import ssreflect ssrfun ssrbool eqtype.
Require Import expr compiler_util.

(* Replace the comparisons [>] and [>=] by [<] and [<=] on swapped operands. *)

Section TOEC_NORM_COND.

Context `{asmop : asmOp}.

Fixpoint norm_cond_e (e : pexpr) : pexpr :=
  match e with
  | Pconst _ | Pbool _ | Parr_init _ _ | Pvar _ => e
  | Pget al aa ws x e => Pget al aa ws x (norm_cond_e e)
  | Psub aa ws len x e => Psub aa ws len x (norm_cond_e e)
  | Pload al ws e => Pload al ws (norm_cond_e e)
  | Papp1 o e => Papp1 o (norm_cond_e e)
  | Papp2 (Ogt k) e1 e2 => Papp2 (Olt k) (norm_cond_e e2) (norm_cond_e e1)
  | Papp2 (Oge k) e1 e2 => Papp2 (Ole k) (norm_cond_e e2) (norm_cond_e e1)
  | Papp2 o e1 e2 => Papp2 o (norm_cond_e e1) (norm_cond_e e2)
  | PappN o es => PappN o (map norm_cond_e es)
  | Pif ty b e1 e2 => Pif ty (norm_cond_e b) (norm_cond_e e1) (norm_cond_e e2)
  end.

Definition norm_cond_lv (x : lval) : lval :=
  match x with
  | Lnone _ _ | Lvar _ => x
  | Lmem al ws vi e => Lmem al ws vi (norm_cond_e e)
  | Laset al aa ws x e => Laset al aa ws x (norm_cond_e e)
  | Lasub aa ws len x e => Lasub aa ws len x (norm_cond_e e)
  end.

Fixpoint norm_cond_ea (a : eassert) : eassert :=
  match a with
  | Pexpr e => Pexpr (norm_cond_e e)
  | PappN_safety o es => PappN_safety o (map norm_cond_e es)
  | Pis_var_init _ => a
  | Pis_mem_init e1 e2 => Pis_mem_init (norm_cond_e e1) (norm_cond_e e2)
  | Pand a1 a2 => Pand (norm_cond_ea a1) (norm_cond_ea a2)
  end.

Fixpoint norm_cond_i (i : instr) : instr :=
  let 'MkI ii ir := i in
  MkI ii (
    match ir with
    | Cassgn x tg ty e => Cassgn (norm_cond_lv x) tg ty (norm_cond_e e)
    | Copn xs tg o es => Copn (map norm_cond_lv xs) tg o (map norm_cond_e es)
    | Csyscall xs o es => Csyscall (map norm_cond_lv xs) o (map norm_cond_e es)
    | Ccall xs f es => Ccall (map norm_cond_lv xs) f (map norm_cond_e es)
    | Cassert a => Cassert (a.1, norm_cond_ea a.2)
    | Cif e c1 c2 => Cif (norm_cond_e e) (map norm_cond_i c1) (map norm_cond_i c2)
    | Cfor x (d, lo, hi) c =>
        Cfor x (d, norm_cond_e lo, norm_cond_e hi) (map norm_cond_i c)
    | Cwhile a c1 e ii' c2 =>
        Cwhile a (map norm_cond_i c1) (norm_cond_e e) ii' (map norm_cond_i c2)
    end).

Definition norm_cond_fun {eft} (f : _fundef eft) : _fundef eft :=
  with_body f (map norm_cond_i (f_body f)).

Definition norm_cond_prog {pT : progT} (p : prog) : prog :=
  map_prog norm_cond_fun p.

End TOEC_NORM_COND.

