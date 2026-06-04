From mathcomp Require Import ssreflect ssrfun ssrbool eqtype ssralg word_ssrZ.
Require Import compiler_util pseudo_operator psem psem_facts.
Require Import ec_while.
Import Utf8.

Section PROOF.

#[local] Existing Instance progUnit.

Context
  {asm_op syscall_state : Type}
  {ep : EstateParams syscall_state}
  {spp : SemPexprParams}
  {sip : SemInstrParams asm_op syscall_state}.

#[local] Existing Instance sCP_unit.
#[local] Existing Instance nosubword.
#[local] Existing Instance indirect_c.
#[local] Existing Instance withassert.

Context {E E0: Type -> Type} {wE : with_Error E E0} {rE : EventRels E0}.

Context (p : prog) (ev:extra_val_t).
Definition p' := ec_while_prog p.

(* ------------------------------------------------- *)

Definition ec_while_spec :=
  {| rpreF_ := λ fn1 fn2 fs1 fs2,
       fn1 = fn2 /\ fs_rel eq fs1 fs2
   ; rpostF_ := λ fn1 fn2 fs1 fs2 fr1 fr2,
       fn1 = fn2 /\ fs_rel eq fr1 fr2
  |}.


Let Pi (i : instr) :=
   forall c', ec_while_i i = c'
              -> wequiv_rec p' p ev ev ec_while_spec eq c' [:: i] eq.

Let Pi_r (i:instr_r) := forall ii, Pi (MkI ii i).

Let Pc  (c:cmd) :=
   forall c', ec_while_c ec_while_i c = c'
              -> wequiv_rec p' p ev ev ec_while_spec eq c' c eq.

Lemma ec_while_sem_pre fn fsi fs :
  fs_rel eq fsi fs →
  sem_pre p' fn fsi = ok tt → sem_pre p fn fs = ok tt.
Proof.
  rewrite /sem_pre /p' => - [ <- <- <- ].
  rewrite get_map_prog_name.
  case assert_allowed => //=.
  by case: (get_fundef (p_funcs p) fn).
Qed.

Lemma ec_while_sem_post fr1 fr2 fs fsi fn:
  fs_rel eq fr1 fr2
  -> fvals fsi = fvals fs
  → sem_post p' fn (fvals fsi) fr1 = ok tt → sem_post p fn (fvals fs) fr2 = ok tt.
Proof.
  rewrite /sem_post /p' => - [ <- <- <- ] ->.
  rewrite get_map_prog_name.
  case assert_allowed => //=.
  by case: (get_fundef (p_funcs p) fn) => //= a.
Qed.

Lemma ec_while_i_nil i :
  ~ ec_while_i i = [::].
Proof.
  case: i => [] ii [] //.
  move=> ? l ? ? ? /=.
  by case: (ec_while_c ec_while_i l).
Qed.

Lemma ec_while_l fn : wiequiv_f p' p ev ev (rpreF (eS:= ec_while_spec)) fn fn (rpostF (eS:=ec_while_spec)).
Proof.
  apply wequiv_fun_ind_wa =>{} fn fn' fsi fs.
  move => [<- hrel] fdi.
  rewrite get_map_prog_name.
  case (get_fundef (p_funcs p) fn) => [fd | //] [= hcomp].
  exists fd => // hsem.
  split. by apply (ec_while_sem_pre hrel).
  move=> si hinit.
  exists si.
  - move: hinit.
    rewrite /p' /initialize_funcall /ec_while_fun /with_body /estate0 /f_params //=.
    case: hrel => <- <- <-.
    by subst.
  - exists eq, eq. split; first done; first last.
    * move=> fr1 fr2 [_ Hrel]. apply ec_while_sem_post. done. by case: hrel.
    * move=> i1 i2 o1 <- //= H. subst. by exists o1.
  clear -Pc Pi Pi_r hcomp hsem.
  apply (cmd_rect (Pr := Pi_r) (Pi := Pi) (Pc := Pc)).
  - easy.
  - rewrite /Pc /ec_while_c /= => c <-. by apply wequiv_nil.
  - move=> i c Hi Hc ? /= <-.
    rewrite -cat1s. eapply wequiv_cat. by apply Hi. by apply Hc.
  - move=> x tg ty e ii i <-. apply wequiv_assgn_eq.
    by apply wrequiv_eq. intro. by apply wrequiv_eq.
  - move=> xs t o es ii i <-. apply wequiv_opn_eq.
    by apply wrequiv_eq. intro. by apply wrequiv_eq.
  - move=> xs o es ii i <-. apply wequiv_syscall_eq. by move=>??->.
    by apply wrequiv_eq. intro. by apply wrequiv_eq.
    intro. by apply wrequiv_eq.
  - move=> a ii i <-. apply wequiv_assert_eq. split; first done.
    by apply wrequiv_eq. done.
  - move=> e c1 c2 Hc1 Hc2 ii i <-. apply wequiv_if_eq.
    by apply wrequiv_eq. case. by apply Hc1. by apply Hc2.
  - move=> v dir lo hi c Hc ii i <-. eapply wequiv_for_eq.
    done. by apply wrequiv_eq. intro. by apply wrequiv_eq.
    by apply Hc.
  - move=> a c e info c' Hc Hc' ii cf <-.
    simpl.
    admit.
  - move=> xs f es ii i <- /=.
    eapply wequiv_call_wa with (Pf:=rpreF (eS:=ec_while_spec)) (Qf:= rpostF (eS:=ec_while_spec)).
    + by apply wrequiv_eq.
    + move=> s1 s2 vs1 vs2 <- <-.
      by apply ec_while_sem_pre.
    + move=> s1 s2 vs1 vs2 <- <-.
      do? split; done.
    + move=> fs1 fs2 fr1 fr2 [_ Hpre] [_ Hpost].
      eapply ec_while_sem_post. done. by case: Hpre.
    + move=>???. by apply wequiv_fun_rec.
    + move=>fs1 fs2 fr1 fr2 Hpre [_ []] Hscs Hmem Hval.
      rewrite /upd_estate Hscs Hmem Hval. by apply wrequiv_eq.
  - by rewrite -hcomp.
Admitted.
