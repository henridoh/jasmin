From mathcomp Require Import ssreflect ssrfun ssrbool eqtype.
Require Import compiler_util psem.
Require Import toec_norm_cond.
Import Utf8.

Section PROOF.

#[local] Existing Instance progUnit.

Context
  {asm_op syscall_state : Type}
  {wa : WithAssert}
  {ep : EstateParams syscall_state}
  {spp : SemPexprParams}
  {sip : SemInstrParams asm_op syscall_state}.

#[local] Existing Instance sCP_unit.
#[local] Existing Instance nosubword.
#[local] Existing Instance indirect_c.

Context {E E0 : Type -> Type} {wE : with_Error E E0} {rE : EventRels E0}.

Context (p : prog) (ev : extra_val_t).

Notation p' := (norm_cond_prog p).

(* The rewriting preserves values: as a checker of the relational logic, the
   instruction cases then follow from the generic [wequiv_*_rel_eq] rules. *)

Definition check_es_nc (_ : unit) (es1 es2 : pexprs) (_ : unit) := es1 = map norm_cond_e es2.

Definition check_lvals_nc (_ : unit) (xs1 xs2 : lvals) (_ : unit) := xs1 = map norm_cond_lv xs2.

Lemma check_esP_rel_nc d es1 es2 d' :
  check_es_nc d es1 es2 d' -> forall s1 s2, st_eq d s1 s2 -> st_eq d' s1 s2.
Proof. done. Qed.

Definition checker_nc : Checker_e st_eq :=
  {| check_es := check_es_nc;
     check_lvals := check_lvals_nc;
     check_esP_rel := check_esP_rel_nc |}.

Definition check_a_nc (_ : unit) (a1 a2 : eassert) (_ : unit) :=
  a1 = norm_cond_ea a2.

Lemma check_aP_rel_nc d a1 a2 d' :
  check_a_nc d a1 a2 d' -> forall s1 s2, st_eq d s1 s2 -> st_eq d' s1 s2.
Proof. done. Qed.

Definition checker_a_nc : Checker_a st_eq :=
  {| check_a := check_a_nc;
     check_aP_rel := check_aP_rel_nc |}.

Definition is_ninc_op x :=
  match x with
  | Ogt k | Oge k => true
  | _ => false
  end.

Lemma norm_cond_esP (wdb : enforce_defined_variables) gd s :
  (forall e v,
     sem_pexpr gd s (norm_cond_e e) = ok v -> sem_pexpr gd s e = ok v) /\
  (forall es vs,
     sem_pexprs gd s (map norm_cond_e es) = ok vs -> sem_pexprs gd s es = ok vs).
Proof.
  apply pexprs_ind_pair.
  constructor => //.
  - move => e He es Hes vs /=.
    t_xrbindP => v' Hv' vs' Hvs' <-.
    by rewrite (He _ Hv') (Hes _ Hvs').
  - move=> > He v /=.
    apply rbindP => - [] // ? ? ->.
    t_xrbindP => > Hz Hzi ? Hw Hwv.
    by rewrite (He _ Hz) /= Hzi /= Hw /= Hwv.
  - move=> > He v /=.
    apply rbindP => - [] // ? ? ->.
    t_xrbindP => > Hz Hzi ? Hw Hwv.
    by rewrite (He _ Hz) /= Hzi /= Hw /= Hwv.
  - move=> > He v /=.
    t_xrbindP => z vz Hvz Hvz_ptr z1 Hz1 Hz1v.
    by rewrite (He _ Hvz) /= Hvz_ptr /= Hz1 /= Hz1v /=.
  - move=> > He v /=.
    t_xrbindP => v' Hv' Hop.
    by rewrite (He _ Hv') /= Hop.
  - move=> op e1 He1 e2 He2 v /=.
    case hninc : (is_ninc_op op).
    + case: op hninc => // c _ /=.
      1-2: t_xrbindP => v2 Hv2 v1 Hv1.
      1-2: rewrite (He1 _ Hv1) (He2 _ Hv2) /= /sem_sop2.
      1-2: t_xrbindP => v2' Hv2' v1' Hv1' r Hres <-.
      1-2: move: Hres.
      1-2: by destruct c
           ; apply rbindP => - [] Hcheck [= Htotal]
           ; rewrite Hv1' Hv2' /= -Htotal ?Z.gtb_ltb ?Z.geb_leb.
    + have -> /= :
        match op with
        | Ogt k => Papp2 (Olt k) (norm_cond_e e2) (norm_cond_e e1)
        | Oge k => Papp2 (Ole k) (norm_cond_e e2) (norm_cond_e e1)
        | _ => Papp2 op (norm_cond_e e1) (norm_cond_e e2)
        end = Papp2 op (norm_cond_e e1) (norm_cond_e e2)
        by case : op hninc => //=.
      t_xrbindP => v1 Hv1 v2 Hv2 Hv.
      by rewrite (He1 _ Hv1) (He2 _ Hv2) /= Hv.
  - move=> os es Hes v /=.
    t_xrbindP => vs Hvs <-.
    change (Let vs' := sem_pexprs gd s es in
            sem_opN os vs' = sem_opN os vs).
    by rewrite (Hes _ Hvs).
  -move=> t e He e1 He1 e2 He2 v /=.
   t_xrbindP => b vb Hvb Hb_vb z1 zv1 Hz1 Hzv1 z2 zv2 Hz2 Hzv2 <-.
   by rewrite (He _ Hvb) (He1 _ Hz1) (He2 _ Hz2) /= Hb_vb Hzv1 Hzv2.
Qed.

Lemma norm_cond_eP (wdb : enforce_defined_variables) i1 i2 e v :
  st_eq tt i1 i2 ->
  sem_pexpr (p_globs p') i1 (norm_cond_e e) = ok v ->
  sem_pexpr (p_globs p) i2 e = ok v.
Proof.
  move=>[Hsc Hmem Hvm] /= H.
  apply norm_cond_esP.
  move: H.
  rewrite (sem_pexpr_ext_eq _ _ Hvm) /with_vm /= Hsc Hmem.
  by destruct i2.
Qed.

Lemma checker_ncP : Checker_eq p' p checker_nc.
Proof.
  constructor.
  - move=> wdb1 wdb2 d es' es d' hok ->.
    elim: es. eexists; done.
    move=> e es IH /= s1 s2 o Heq H.
    exists o; last done.
    rewrite -H.
    specialize (IH s1 s2).
    admit.
  - admit.

Admitted.

Lemma checker_a_ncP : Checker_a_eq p' p checker_a_nc.
Proof. Admitted.

Lemma norm_cond_l fn :
  wiequiv_f p' p ev ev (rpreF (eS := eq_spec)) fn fn (rpostF (eS := eq_spec)).
Proof. Admitted.

End PROOF.

