From mathcomp Require Import ssreflect ssrfun ssrbool eqtype ssralg word_ssrZ.
Require Import compiler_util pseudo_operator psem psem_facts.
Require Import ec_for.

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

Context (fresh_var_ident : v_kind -> instr_info -> string -> atype -> Ident.ident).

Context (p p' : prog) (ev : extra_val_t).
Hypothesis Hp : ec_for_prog fresh_var_ident p = ok p'.

Lemma eq_globs : p_globs p' = p_globs p.
Proof. by apply: rbindP Hp => ?? [= <-]. Qed.

Definition ec_for_spec :=
  {| rpreF_ := fun fn1 fn2 fs1 fs2 =>
       fn1 = fn2 /\ fs_rel eq fs1 fs2
   ; rpostF_ := fun fn1 fn2 fs1 fs2 fr1 fr2 =>
       fn1 = fn2 /\ fs_rel eq fr1 fr2
  |}.

Lemma ec_for_sem_pre fn fsi fs :
  fs_rel eq fsi fs ->
  sem_pre p' fn fsi = ok tt ->
  sem_pre p fn fs = ok tt.
Proof.
  
Admitted.

Lemma ec_for_sem_post fr1 fr2 fs fsi fn :
  fs_rel eq fr1 fr2 ->
  fvals fsi = fvals fs ->
  sem_post p' fn (fvals fsi) fr1 = ok tt ->
  sem_post p fn (fvals fs) fr2 = ok tt.
Proof.
  move=> Hrel Hfvals.
  rewrite /sem_post.
  case: assert_allowed => //=.
Admitted.

#[local] Lemma checker_st_eq_onP' : Checker_eq p' p checker_st_eq_on.
Proof. by apply checker_st_eq_onP; rewrite eq_globs. Qed.
#[local] Hint Resolve checker_st_eq_onP' : core.

Let Pi (i : instr) :=
  forall X, Sv.Subset (vars_I i) X ->
  forall i', ec_for_i fresh_var_ident X i = ok i' ->
  wequiv_rec p' p ev ev ec_for_spec (st_eq_on X) [:: i'] [:: i] (st_eq_on X).

Let Pi_r (ir : instr_r) := forall ii, Pi (MkI ii ir).

Let Pc (c : cmd) :=
  forall X, Sv.Subset (vars_c c) X ->
  forall c', ec_for_c fresh_var_ident X c = ok c' ->
  wequiv_rec p' p ev ev ec_for_spec (st_eq_on X) c' c (st_eq_on X).

Lemma wequiv_for_rename X ii dir lo hi c c' x x' :
  Sv.Subset (Sv.union (read_e lo) (Sv.union (read_e hi) (vars_c c))) X ->
  Sv.In (v_var x) X ->
  ~~ Sv.mem (v_var x') X ->
  wequiv_rec p' p ev ev ec_for_spec (st_eq_on X) c' c (st_eq_on X) ->
  wequiv_rec p' p ev ev ec_for_spec (st_eq_on X)
    [:: MkI ii (Cfor x' (dir, lo, hi)
                  (MkI ii (Cassgn (Lvar x) AT_inline (vtype x) (Plvar x')) :: c')) ]
    [:: MkI ii (Cfor x (dir, lo, hi) c) ]
    (st_eq_on X).
Proof.
  move=> HX Hx Hx' Hc.
  apply (wequiv_for (Pi := st_eq_on (Sv.remove x X))) => //.
  { rewrite eq_globs.
    apply wrequiv_sem_bound.
    move=>s t vs [H1 H2 H3] H4.
    exists vs; last exact values_uincl_refl.
    rewrite -H4.
    have -> : t = with_vm s (evm t)
      by destruct s,t; move: H1 H2 => /= <- <-.
    symmetry.
    apply read_es_eq_on_empty => el.
    have -> : Sv.Equal (read_es_rec Sv.empty [:: lo; hi]) (Sv.union (read_e hi) (read_e lo)).
    { rewrite /= !read_eE.
      clear. SvD.fsetdec. }
    intros. apply H3, HX. clear -HX H; SvD.fsetdec.
  }
  { admit.
  }
  { admit.
  }
Admitted.

Lemma subset_vars_c_cons i c V
  : Sv.Subset (vars_c (i :: c)) V
    -> Sv.Subset (vars_I i) V /\ Sv.Subset (vars_c c) V.
Proof.
  clear.
  rewrite vars_c_cons => H.
  split.
  - move=> x Hi.
    apply (SvP.MP.in_subset Hi).
    move=> el Hel. apply H.
    apply Sv.union_spec. by left.
  - move=> x Hi.
    apply H.
    apply Sv.union_spec. by right.
Qed.

Lemma ec_for_body : forall c, Pc c.
Proof.
  apply (cmd_rect (Pr := Pi_r) (Pi := Pi)).
  { easy. }
  { rewrite /Pc /ec_for_c /= => V HV c [<-]. by apply wequiv_nil. }
  { move=> i c Hi Hc V HV c'.
    apply rbindP => y Hy.
    apply rbindP => ys Hys [= <-].
    eapply wequiv_cons ; [ apply Hi
                         | apply Hc ]
    ; by case (subset_vars_c_cons HV).
  }
  { move=> x tg ty e ii V HV i [= <-].
    admit.
  }
  { move=> xs t o es ii V HV i [= <-].
    admit.
  }
  { move=> xs o es ii V HV i [= <-].
    admit.
  }
  { move=> a ii V HV i [= <-].
    apply wequiv_assert.
    split=>// s1 s2 [Hon1 Hon2 Hon3].
    rewrite eq_globs => <-.
    split; last done.
    apply eq_on_sem_eassert => // el Hel.
    symmetry; apply Hon3.
    rewrite vars_I_assert in HV.
    SvD.fsetdec.
  }
  { move=>e c1 c2 Hc1 Hc2 ii V HV i /=.
    t_xrbindP => ir c1' Hc1' c2' Hc2' <- <-.
    rewrite vars_I_if in HV.
    apply wequiv_if.
    - apply sem_cond_uincl.
      rewrite eq_globs => s t b [] H1 H2 H3 H.
      exists b => //.
      rewrite -H.
      have -> : t = with_vm s (evm t)
        by destruct s,t; move: H1 H2 => /= <- <-.
      symmetry.
      apply read_e_eq_on_empty.
      rewrite read_eE => el Hel.
      apply H3, HV. SvD.fsetdec.
    - case; [apply Hc1 | apply Hc2]
      ; try done; clear -HV; SvD.fsetdec.
  }
  (* Cfor *)
  { move=> v dir lo hi c Hc ii X. rewrite vars_I_for => hsub i' /=.
    t_xrbindP => ir'.
    t_xrbindP => c' hc'.
    case: ifPn => hwr.
    - move=> [= <-] <-.
      apply (wequiv_for_rel_eq (sip:=sip)) with checker_st_eq_on X X => //.
      + split=>//. rewrite /read_es /= !read_eE; SvD.fsetdec.
        split. SvD.fsetdec. done. SvD.fsetdec.
      + apply Hc => //.
        by clear -hsub; SvD.fsetdec.
    - t_xrbindP => Hassert /= <- <-.
      apply wequiv_for_rename => //.
      + by clear -hsub; SvD.fsetdec.
      + by clear -hsub; SvD.fsetdec.
      + apply Hc => //.
        SvD.fsetdec. }
  { move=> a c1 e ii' c2 Hc1 Hc2 ii V HV i /=.
    t_xrbindP => ir' c1' Hc1' c2' Hc2' <- <-.
    rewrite vars_I_while in HV.
    apply wequiv_while.
    - (* FIXME: exact repitition from if case *)
      apply sem_cond_uincl.
      rewrite eq_globs => s t b [] H1 H2 H3 H.
      exists b => //.
      rewrite -H.
      have -> : t = with_vm s (evm t)
        by destruct s,t; move: H1 H2 => /= <- <-.
      symmetry.
      apply read_e_eq_on_empty.
      rewrite read_eE => el Hel.
      apply H3, HV. SvD.fsetdec.
    - apply Hc1. clear -HV. SvD.fsetdec. done.
    - apply Hc2. clear -HV. SvD.fsetdec. done.
  }
  { move=> xs f es ii V HV i' [= <-] /=.
    rewrite vars_I_call in HV.
    eapply wequiv_call_wa
      with (Pf:=rpreF (eS:=ec_for_spec))
           (Qf:= rpostF (eS:=ec_for_spec))
           (Rv := eq).
    - rewrite eq_globs.
      move=> s t vs [H1 H2 H3] H4.
      have -> : t = with_vm s (evm t)
        by destruct s,t; move: H1 H2 => /= <- <-.
      exists vs. rewrite -H4. symmetry.
      apply read_es_eq_on_empty. rewrite read_esE => el Hel.
      apply H3, HV. SvD.fsetdec. done.
    - move=>???? []*.
      by apply: ec_for_sem_pre; last eassumption.
    - by move=>???? [].
    - move=> fs1 fs2 fr1 fr2 [_ Hpre] [_ Hpost].
      eapply ec_for_sem_post. assumption. by case: Hpre.
    - move=>???. by apply wequiv_fun_rec.
    - move=>fs1 fs2 fr1 fr2 Hpre [_ []] Hscs Hmem Hval.
      rewrite /upd_estate Hscs Hmem Hval.
      admit.
  }
Admitted.

Lemma ec_for_l fn :
  wiequiv_f p' p ev ev (rpreF (eS:= ec_for_spec)) fn fn (rpostF (eS:=ec_for_spec)).
Proof.
  apply wequiv_fun_ind_wa => {} fn fn' fsi fs.
  move=> [<- hrel] fdi hget'.
Admitted.

End PROOF.
