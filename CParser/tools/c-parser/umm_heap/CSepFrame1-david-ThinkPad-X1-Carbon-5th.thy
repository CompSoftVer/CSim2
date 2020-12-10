(*
 * Copyright 2014, NICTA
 *
 * This software may be distributed and modified according to the terms of
 * the BSD 2-Clause license. Note that NO WARRANTY is provided.
 * See "LICENSE_BSD2.txt" for details.
 *
 * @TAG(NICTA_BSD)
 *)

(* License: BSD, terms see file ./LICENSE *)

theory CSepFrame1
imports SepTactic
begin

class heap_state_type'

instance heap_state_type' \<subseteq> type ..

consts
  hst_mem :: "'a::heap_state_type' \<Rightarrow> heap_mem"
  hst_mem_update :: "(heap_mem \<Rightarrow> heap_mem) \<Rightarrow> 'a::heap_state_type' \<Rightarrow> 'a"
  hst_htd :: "'a::heap_state_type' \<Rightarrow> heap_typ_desc"
  hst_htd_update :: "(heap_typ_desc \<Rightarrow> heap_typ_desc) \<Rightarrow> 'a::heap_state_type' \<Rightarrow> 'a"

class heap_state_type = heap_state_type' +
  assumes hst_htd_htd_update [simp]: "hst_htd (hst_htd_update d s) = d (hst_htd s)"
  assumes hst_mem_mem_update [simp]: "hst_mem (hst_mem_update h s) = h (hst_mem s)"
  assumes hst_htd_mem_update [simp]: "hst_htd (hst_mem_update h s) = hst_htd s"
  assumes hst_mem_htd_update [simp]: "hst_mem (hst_htd_update d s) = hst_mem s"

translations
  "s\<lparr> hst_mem := x\<rparr>" <= "CONST hst_mem_update (K_record x) s"
  "s\<lparr> hst_htd := x\<rparr>" <= "CONST hst_htd_update (K_record x) s"

definition lift_hst :: "'a::heap_state_type' \<Rightarrow> heap_state" where
  "lift_hst s \<equiv> lift_state (hst_mem s,hst_htd s)"

definition
  point_eq_mod :: "('a \<Rightarrow> 'b) \<Rightarrow> ('a \<Rightarrow> 'b) \<Rightarrow> 'a set \<Rightarrow> bool"
where
  "point_eq_mod f g X \<equiv> \<forall>x. x \<notin> X \<longrightarrow> f x = g x"

definition
  exec_fatal :: "('s,'b,'c,'e) com \<Rightarrow> ('s,'b,'c,'e) body \<Rightarrow> 's \<Rightarrow> bool"
where
  "exec_fatal C \<Gamma> s \<equiv> (\<exists>f. \<Gamma> \<turnstile>\<^sub>p \<langle>C,Normal s\<rangle> \<Rightarrow> Fault f) \<or>
      (\<Gamma> \<turnstile>\<^sub>p \<langle>C,Normal s\<rangle> \<Rightarrow> Stuck)"

definition
  exec_fatal_seq :: "('s,'b,'c) Language.com \<Rightarrow> ('s,'b,'c) Semantic.body \<Rightarrow> 's \<Rightarrow> bool"
where
  "exec_fatal_seq C \<Gamma> s \<equiv> (\<exists>f. \<Gamma> \<turnstile> \<langle>C,Normal s\<rangle> \<Rightarrow> Fault f) \<or>
      (\<Gamma> \<turnstile> \<langle>C,Normal s\<rangle> \<Rightarrow> Stuck)"

definition
  restrict_htd :: "'s::heap_state_type' \<Rightarrow> s_addr set \<Rightarrow> 's"
where
  "restrict_htd s X \<equiv> s\<lparr> hst_htd := restrict_s (hst_htd s) X \<rparr>"

definition
  restrict_safe_OK :: "'s \<Rightarrow> 's \<Rightarrow> ('s \<Rightarrow> ('s,'c) xstate) \<Rightarrow>
       s_addr set \<Rightarrow> ('s::heap_state_type','b,'c,'e) com \<Rightarrow> ('s,'b,'c,'e) body \<Rightarrow> bool"
where
  "restrict_safe_OK s t f X C \<Gamma> \<equiv>
      \<Gamma> \<turnstile>\<^sub>p \<langle>C,(Normal (restrict_htd s X))\<rangle> \<Rightarrow> f (restrict_htd t X) \<and>
      point_eq_mod (lift_state (hst_mem t,hst_htd t))
          (lift_state (hst_mem s,hst_htd s)) X"

definition
  restrict_safe_OK_seq :: "'s \<Rightarrow> 's \<Rightarrow> ('s \<Rightarrow> ('s,'c) xstate) \<Rightarrow>
       s_addr set \<Rightarrow> ('s::heap_state_type','b,'c) Language.com \<Rightarrow> ('s,'b,'c) Semantic.body \<Rightarrow> bool"
where
  "restrict_safe_OK_seq s t f X C \<Gamma> \<equiv>
      \<Gamma> \<turnstile> \<langle>C,(Normal (restrict_htd s X))\<rangle> \<Rightarrow> f (restrict_htd t X) \<and>
      point_eq_mod (lift_state (hst_mem t,hst_htd t))
          (lift_state (hst_mem s,hst_htd s)) X"

definition
  restrict_safe :: "'s \<Rightarrow> ('s,'c) xstate \<Rightarrow>
       ('s::heap_state_type','b,'c,'e) com \<Rightarrow> ('s,'b,'c,'e) body \<Rightarrow> bool"
where
  "restrict_safe s t C \<Gamma> \<equiv> \<forall>X. (case t of
      Normal t' \<Rightarrow> restrict_safe_OK s t' Normal X C \<Gamma> |
      Abrupt t' \<Rightarrow> restrict_safe_OK s t' Abrupt X C \<Gamma> |
      _ \<Rightarrow> False) \<or>
      exec_fatal C \<Gamma> (restrict_htd s X)"

definition
  restrict_safe_seq :: "'s \<Rightarrow> ('s,'c) xstate \<Rightarrow>
       ('s::heap_state_type','b,'c) Language.com \<Rightarrow> ('s,'b,'c) Semantic.body \<Rightarrow> bool"
where
  "restrict_safe_seq s t C \<Gamma> \<equiv> \<forall>X. (case t of
      Normal t' \<Rightarrow> restrict_safe_OK_seq s t' Normal X C \<Gamma> |
      Abrupt t' \<Rightarrow> restrict_safe_OK_seq s t' Abrupt X C \<Gamma> |
      _ \<Rightarrow> False) \<or>
      exec_fatal_seq C \<Gamma> (restrict_htd s X)"

definition
  mem_safe :: "('s::{heap_state_type',type},'b,'c,'e) com \<Rightarrow>
               ('s,'b,'c,'e) body \<Rightarrow> bool"
where
  "mem_safe C \<Gamma> \<equiv> \<forall>s t. \<Gamma> \<turnstile>\<^sub>p \<langle>C,Normal s\<rangle> \<Rightarrow> t \<longrightarrow>
      restrict_safe s t C \<Gamma>"

definition
  mem_safe_seq :: "('s::{heap_state_type',type},'b,'c) Language.com \<Rightarrow>
               ('s,'b,'c) Semantic.body \<Rightarrow> bool"
where
  "mem_safe_seq C \<Gamma> \<equiv> \<forall>s t. \<Gamma> \<turnstile> \<langle>C,Normal s\<rangle> \<Rightarrow> t \<longrightarrow>
      restrict_safe_seq s t C \<Gamma>"

definition
  point_eq_mod_safe :: "'s::{heap_state_type',type} set \<Rightarrow>
     ('s \<Rightarrow> 's) \<Rightarrow> ('s \<Rightarrow> s_addr \<Rightarrow> 'c) \<Rightarrow> bool"
where
  "point_eq_mod_safe P f g \<equiv> \<forall>s X. restrict_htd s X \<in> P \<longrightarrow>
      point_eq_mod (g (f s)) (g s) X"

definition
  comm_restrict :: "('s::{heap_state_type',type} \<Rightarrow> 's) \<Rightarrow> 's \<Rightarrow> s_addr set \<Rightarrow> bool"
where
  "comm_restrict f s X \<equiv> f (restrict_htd s X) = restrict_htd (f s) X"

definition
  comm_restrict_safe :: "'s set \<Rightarrow> ('s::{heap_state_type',type} \<Rightarrow> 's) \<Rightarrow> bool"
where
  "comm_restrict_safe P f \<equiv> \<forall>s X. restrict_htd s X \<in> P \<longrightarrow>
      comm_restrict f s X"

definition htd_ind :: "('a::{heap_state_type',type} \<Rightarrow> 'b) \<Rightarrow> bool" where
  "htd_ind f \<equiv> \<forall>x s. f s = f (hst_htd_update x s)"

definition mono_guard :: "'s::{heap_state_type',type} set \<Rightarrow> bool" where
  "mono_guard P \<equiv> \<forall>s X. restrict_htd s X \<in> P \<longrightarrow> s \<in> P"

definition expr_htd_ind :: "'s::{heap_state_type',type} set \<Rightarrow> bool" where
  "expr_htd_ind P \<equiv> \<forall>d s. s\<lparr> hst_htd := d \<rparr> \<in> P = (s \<in> P)"

(* primrec intra_safe_seq :: "('s::heap_state_type','b,'c) Language.com \<Rightarrow>  bool"
where
  "intra_safe_seq Language.Skip = True"
| "intra_safe_seq (Language.Basic f) = (comm_restrict_safe UNIV f \<and>
      point_eq_mod_safe UNIV f (\<lambda>s. lift_state (hst_mem s,hst_htd s)))"
| "intra_safe_seq (Language.Spec r) = (\<forall>\<Gamma>. mem_safe_seq (Language.Spec r) (\<Gamma> :: ('s,'b,'c) Semantic.body))"
| "intra_safe_seq (Language.Seq C D) = (intra_safe_seq C \<and> intra_safe_seq D)"
| "intra_safe_seq (Language.Cond P C D) = (expr_htd_ind P \<and> intra_safe_seq C \<and> intra_safe_seq D)"
| "intra_safe_seq (Language.While P C) = (expr_htd_ind P \<and> intra_safe_seq C)"
| "intra_safe_seq (Language.Call p) = True"
| "intra_safe_seq (Language.DynCom f) = (htd_ind f \<and> (\<forall>s. intra_safe_seq (f s)))"
| "intra_safe_seq (Language.Guard f P C) = (mono_guard P \<and> (case C of
      Language.Basic g \<Rightarrow> comm_restrict_safe P g \<and> (* point_eq_mod_safe P g hst_mem \<and> *)

                     point_eq_mod_safe P g (\<lambda>s. lift_state (hst_mem s,hst_htd s))
      | _ \<Rightarrow> intra_safe_seq C))"
| "intra_safe_seq Language.Throw = True"
| "intra_safe_seq (Language.Catch C D) = (intra_safe_seq C \<and> intra_safe_seq D)" *)

primrec intra_safe_seq :: "('s::heap_state_type','b,'c) Language.com \<Rightarrow>  bool"
where
  "intra_safe_seq Language.Skip = True"
| "intra_safe_seq (Language.Basic f) = (comm_restrict_safe UNIV f \<and>
      point_eq_mod_safe UNIV f (\<lambda>s. lift_state (hst_mem s,hst_htd s)))"
| "intra_safe_seq (Language.Spec r) = (\<forall>\<Gamma>. mem_safe_seq (Language.Spec r) (\<Gamma> :: ('s,'b,'c) Semantic.body))"
| "intra_safe_seq (Language.Seq C D) = (intra_safe_seq C \<and> intra_safe_seq D)"
| "intra_safe_seq (Language.Cond P C D) = (expr_htd_ind P \<and> intra_safe_seq C \<and> intra_safe_seq D)"
| "intra_safe_seq (Language.While P C) = (expr_htd_ind P \<and> intra_safe_seq C)"
| "intra_safe_seq (Language.Call p) = True"
| "intra_safe_seq (Language.DynCom f) = (htd_ind f \<and> (\<forall>s. intra_safe_seq (f s)))"
| "intra_safe_seq (Language.Guard f P C) = (mono_guard P \<and> (case C of
      Language.Basic g \<Rightarrow> comm_restrict_safe P g \<and> 
                     point_eq_mod_safe P g (\<lambda>s. lift_state (hst_mem s,hst_htd s))
      | _ \<Rightarrow> intra_safe_seq C))"
| "intra_safe_seq Language.Throw = True"
| "intra_safe_seq (Language.Catch C D) = (intra_safe_seq C \<and> intra_safe_seq D)" 

primrec intra_safe :: "('s::heap_state_type','b,'c,'e) com \<Rightarrow>  bool"
where
  "intra_safe Skip = True"
| "intra_safe (Basic f e)  = (comm_restrict_safe UNIV f \<and>
      point_eq_mod_safe UNIV f (\<lambda>s. lift_state (hst_mem s,hst_htd s)))"
| "intra_safe (Spec r e) = (\<forall>\<Gamma>. mem_safe (Spec r e) (\<Gamma> :: ('s,'b,'c,'e) body))"
| "intra_safe (Seq C D) = (intra_safe C \<and> intra_safe D)"
| "intra_safe (Cond P C D) = (expr_htd_ind P \<and> intra_safe C \<and> intra_safe D)"
| "intra_safe (While P C) = (expr_htd_ind P \<and> intra_safe C)"
| "intra_safe (Call p) = True"
| "intra_safe (DynCom f) = (htd_ind f \<and> (\<forall>s. intra_safe (f s)))"
| "intra_safe (Guard f P C) = (mono_guard P \<and> (case C of
      (Basic g e) \<Rightarrow> comm_restrict_safe P g \<and> 
                     point_eq_mod_safe P g (\<lambda>s. lift_state (hst_mem s,hst_htd s))
      | _ \<Rightarrow> intra_safe C))"
| "intra_safe Throw = True"
| "intra_safe (Catch C D) = (intra_safe C \<and> intra_safe D)"
| "intra_safe (Await b C e) = (expr_htd_ind b \<and> intra_safe_seq C)"

lemma noawaits_same_exec:
  assumes 
   a0:"\<Gamma>\<^sub>\<not>\<^sub>a \<turnstile> \<langle>c', s\<rangle> \<Rightarrow> t" and a1:"c' = sequential C\<^sub>p" and
   a0':"noawaits C\<^sub>p" and a2:"t\<noteq>Stuck"
  shows "\<Gamma> \<turnstile>\<^sub>p \<langle>C\<^sub>p, s\<rangle> \<Rightarrow> t"
  using a0 a0' a1 a2
proof(induct arbitrary: C\<^sub>p)
  case (Skip s)  
  then show ?case by (cases C\<^sub>p, auto simp:SemanticCon.exec.intros(1))
next
  case (Guard s g c t f)  
  then show ?case by (cases C\<^sub>p, auto simp:SemanticCon.exec.intros(2))
next
  case (GuardFault s g f c)
  then show ?case by (cases C\<^sub>p, auto simp:SemanticCon.exec.intros(3))
next
  case (Basic f s)
  then show ?case by (cases C\<^sub>p, auto simp:SemanticCon.exec.intros(5))
next
  case (Spec s t r)
  then show ?case by (cases C\<^sub>p, auto simp:SemanticCon.exec.intros(6))
next
  case (Seq c\<^sub>1 s s' c\<^sub>2 t)
  then obtain c1p c2p where "C\<^sub>p = Seq c1p c2p \<and> 
        c\<^sub>1 = sequential c1p \<and> 
        c\<^sub>2 = sequential c2p \<and> noawaits c1p \<and> noawaits c2p"
    by (cases C\<^sub>p, auto)
  then show ?case using Seq SemanticCon.exec.intros(8)
    by (metis SemanticCon.noStuck_start)    
next
  case (CondTrue s b c\<^sub>1 t c\<^sub>2)
  then show ?case by (cases C\<^sub>p, auto simp:SemanticCon.exec.intros(9))
next
  case (CondFalse s b c\<^sub>2 t c\<^sub>1)
  then show ?case by (cases C\<^sub>p, auto simp:SemanticCon.exec.intros(10))
next
  case (WhileTrue s b c s' t)
  then show ?case 
    apply (cases C\<^sub>p) 
    apply auto
    by (metis SemanticCon.noStuck_start SemanticCon.exec.WhileTrue WhileTrue.prems(1) WhileTrue.prems(2))
next
  case (WhileFalse s b c)
  then show ?case by (cases C\<^sub>p, auto simp:SemanticCon.exec.intros(14))
next
  case (Call p bdy s t)
  then have "C\<^sub>p = LanguageCon.com.Call p"
    by (cases C\<^sub>p,auto)
  moreover obtain bdyp where   " \<Gamma> p = Some (bdyp) \<and> bdy = sequential bdyp \<and> noawaits bdyp" 
    using Call lam1_seq no_await_some_some_p
    by (metis None_not_eq no_await_some_no_await)  
  ultimately show ?case using Call(3) Call(6)
    by (simp add: SemanticCon.exec.Call) 
next
  case (CallUndefined p s)
  then have "C\<^sub>p = LanguageCon.com.Call p"
    by (cases C\<^sub>p,auto)
  then show ?case
    using CallUndefined.prems(3) by blast    
next
  case (DynCom c s t)
  then show ?case by (cases C\<^sub>p, auto simp:SemanticCon.exec.intros(18))
next
  case (Throw s)
  then show ?case by (cases C\<^sub>p, auto simp:SemanticCon.exec.intros(19))
next
  case (CatchMatch c\<^sub>1 s s' c\<^sub>2 t)  
    then obtain c1p c2p where "C\<^sub>p = Catch c1p c2p \<and> 
        c\<^sub>1 = sequential c1p \<and> 
        c\<^sub>2 = sequential c2p \<and> noawaits c1p \<and> noawaits c2p"
    by (cases C\<^sub>p, auto)
  then show ?case using CatchMatch SemanticCon.exec.intros(21)
    by (metis SemanticCon.isAbr_simps(2) SemanticCon.isAbr_simps(4))
next
  case (CatchMiss c\<^sub>1 s t c\<^sub>2)
  then obtain c1p c2p where "C\<^sub>p = Catch c1p c2p \<and> 
        c\<^sub>1 = sequential c1p \<and> 
        c\<^sub>2 = sequential c2p \<and> noawaits c1p \<and> noawaits c2p"
    by (cases C\<^sub>p, auto)
  then show ?case using CatchMiss SemanticCon.exec.intros(22)
    by (metis Semantic.isAbr_def SemanticCon.isAbrE)
qed(auto)

lemma mem_safe_mem_safe_seq:
  assumes a0:"noawaits C\<^sub>p" and a1:"\<Gamma>\<^sub>\<not>\<^sub>a n = Some (sequential C\<^sub>p)" and a2:"\<Gamma> n = Some C\<^sub>p"  and
               a3:"mem_safe C\<^sub>p \<Gamma>"
             shows "mem_safe_seq (sequential C\<^sub>p) (\<Gamma>\<^sub>\<not>\<^sub>a)" 
  using a0 a1 a2 a3 unfolding mem_safe_def mem_safe_seq_def
proof(auto)
  fix s t
  assume a00:"\<Gamma>\<^sub>\<not>\<^sub>a\<turnstile> \<langle>sequential C\<^sub>p,Normal s\<rangle> \<Rightarrow> t"
  { assume "\<not> t=Stuck"
   then have "\<Gamma> \<turnstile>\<^sub>p \<langle>C\<^sub>p,Normal s\<rangle> \<Rightarrow> t" using noawaits_same_exec
     using a00 a1 a0 by blast
   then have "restrict_safe_seq s t (sequential C\<^sub>p) (\<Gamma>\<^sub>\<not>\<^sub>a)"
     sorry
  }
  moreover { assume a000:"t = Stuck"
    then have "restrict_safe_seq s t (sequential C\<^sub>p) (\<Gamma>\<^sub>\<not>\<^sub>a)"
      unfolding restrict_safe_seq_def exec_fatal_seq_def
      sorry
  } ultimately show "restrict_safe_seq s t (sequential C\<^sub>p) (\<Gamma>\<^sub>\<not>\<^sub>a)" by auto

qed

instance prod :: (heap_state_type',type) heap_state_type' ..
                                                 
overloading
  hs_mem_state \<equiv> hst_mem
  hs_mem_update_state \<equiv> hst_mem_update
  hs_htd_state \<equiv> hst_htd
  hs_htd_update_state \<equiv> hst_htd_update
begin
  definition hs_mem_state [simp]: "hs_mem_state \<equiv> hst_mem \<circ> globals"
  definition hs_mem_update_state [simp]: "hs_mem_update_state \<equiv> upd_globals \<circ> hst_mem_update"
  definition hs_htd_state[simp]: "hs_htd_state \<equiv> hst_htd \<circ> globals"
  definition hs_htd_update_state [simp]: "hs_htd_update_state \<equiv> upd_globals \<circ> hst_htd_update"
end

instance prod :: (heap_state_type,type) heap_state_type
  apply intro_classes
  apply (auto simp add: upd_globals_def globals_def)
  done

primrec
  intra_deps_seq :: "('s','b,'c) Language.com \<Rightarrow> 'b set"
where
  "intra_deps_seq Language.Skip = {}"
| "intra_deps_seq (Language.Basic f) = {}"
| "intra_deps_seq (Language.Spec r) = {}"
| "intra_deps_seq (Language.Seq C D) = (intra_deps_seq C \<union> intra_deps_seq D)"
| "intra_deps_seq (Language.Cond P C D) = (intra_deps_seq C \<union> intra_deps_seq D)"
| "intra_deps_seq (Language.While P C) = intra_deps_seq C"
| "intra_deps_seq (Language.Call p) = {p}"
| "intra_deps_seq (Language.DynCom f) = \<Union>{intra_deps_seq (f s) | s. True}"
| "intra_deps_seq (Language.Guard f P C) = intra_deps_seq C"
| "intra_deps_seq Language.Throw = {}"
| "intra_deps_seq (Language.Catch C D) = (intra_deps_seq C \<union> intra_deps_seq D)"

inductive_set
  proc_deps_seq :: "('s','b,'c) Language.com \<Rightarrow> ('s,'b,'c) Semantic.body \<Rightarrow> 'b set"
  for "C" :: "('s','b,'c) Language.com"
  and "\<Gamma>" :: "('s,'b,'c) Semantic.body"
where
  "x \<in> intra_deps_seq C \<Longrightarrow> x \<in> proc_deps_seq C \<Gamma>"
| "\<lbrakk> x \<in> proc_deps_seq C \<Gamma>; \<Gamma> x = Some D; y \<in> intra_deps_seq D \<rbrakk> \<Longrightarrow> y \<in> proc_deps_seq C \<Gamma>"

primrec
  intra_deps :: "('s','b,'c,'e) com \<Rightarrow> 'b set"
where
  "intra_deps Skip = {}"
| "intra_deps (Basic f e) = {}"
| "intra_deps (Spec r e) = {}"
| "intra_deps (Seq C D) = (intra_deps C \<union> intra_deps D)"
| "intra_deps (Cond P C D) = (intra_deps C \<union> intra_deps D)"
| "intra_deps (While P C) = intra_deps C"
| "intra_deps (Call p) = {p}"
| "intra_deps (DynCom f) = \<Union>{intra_deps (f s) | s. True}"
| "intra_deps (Guard f P C) = intra_deps C"
| "intra_deps Throw = {}"
| "intra_deps (Catch C D) = (intra_deps C \<union> intra_deps D)"
| "intra_deps (Await b C e) = intra_deps_seq C"


inductive_set
  proc_deps :: "('s','b,'c,'e) com \<Rightarrow> ('s,'b,'c,'e) body \<Rightarrow> 'b set"
  for "C" :: "('s','b,'c,'e) com"
  and "\<Gamma>" :: "('s,'b,'c,'e) body"
where
  "x \<in> intra_deps C \<Longrightarrow> x \<in> proc_deps C \<Gamma>"
| "\<lbrakk> x \<in> proc_deps C \<Gamma>; \<Gamma> x = Some D; y \<in> intra_deps D \<rbrakk> \<Longrightarrow> y \<in> proc_deps C \<Gamma>"


text \<open>----\<close>

lemma point_eq_mod_refl [simp]:
  "point_eq_mod f f X"
  by (simp add: point_eq_mod_def)

lemma point_eq_mod_subs:
  "\<lbrakk> point_eq_mod f g Y; Y \<subseteq> X \<rbrakk> \<Longrightarrow> point_eq_mod f g X"
  by (force simp: point_eq_mod_def)

lemma point_eq_mod_trans:
  "\<lbrakk> point_eq_mod x y X; point_eq_mod y z X \<rbrakk> \<Longrightarrow> point_eq_mod x z X"
  by (force simp: point_eq_mod_def)

lemma mem_safe_NormalD:
  "\<lbrakk> \<Gamma> \<turnstile>\<^sub>p \<langle>C,Normal s\<rangle> \<Rightarrow> Normal t; mem_safe C \<Gamma>;
      \<not> exec_fatal C \<Gamma> (restrict_htd s X) \<rbrakk> \<Longrightarrow>
      (\<Gamma> \<turnstile>\<^sub>p \<langle>C,(Normal (restrict_htd s X))\<rangle> \<Rightarrow> Normal (restrict_htd t X) \<and>
       point_eq_mod (lift_state (hst_mem t,hst_htd t))
          (lift_state (hst_mem s,hst_htd s)) X)"
  by (force simp: mem_safe_def restrict_safe_def restrict_safe_OK_def)

lemma mem_safe_seq_NormalD:
  "\<lbrakk> \<Gamma> \<turnstile> \<langle>C,Normal s\<rangle> \<Rightarrow> Normal t; mem_safe_seq C \<Gamma>;
      \<not> exec_fatal_seq C \<Gamma> (restrict_htd s X) \<rbrakk> \<Longrightarrow>
      (\<Gamma> \<turnstile> \<langle>C,(Normal (restrict_htd s X))\<rangle> \<Rightarrow> Normal (restrict_htd t X) \<and>
       point_eq_mod (lift_state (hst_mem t,hst_htd t))
          (lift_state (hst_mem s,hst_htd s)) X)"
  by (force simp: mem_safe_seq_def restrict_safe_seq_def restrict_safe_OK_seq_def)

lemma mem_safe_AbruptD:
  "\<lbrakk> \<Gamma> \<turnstile>\<^sub>p \<langle>C,Normal s\<rangle> \<Rightarrow> Abrupt t; mem_safe C \<Gamma>;
      \<not> exec_fatal C \<Gamma> (restrict_htd s X) \<rbrakk> \<Longrightarrow>
      (\<Gamma> \<turnstile>\<^sub>p \<langle>C,(Normal (restrict_htd s X))\<rangle> \<Rightarrow> Abrupt (restrict_htd t X) \<and>
       point_eq_mod (lift_state (hst_mem t,hst_htd t))
          (lift_state (hst_mem s,hst_htd s)) X)"
  by (force simp: mem_safe_def restrict_safe_def restrict_safe_OK_def)

lemma mem_safe_seq_AbruptD:
  "\<lbrakk> \<Gamma> \<turnstile> \<langle>C,Normal s\<rangle> \<Rightarrow> Abrupt t; mem_safe_seq C \<Gamma>;
      \<not> exec_fatal_seq C \<Gamma> (restrict_htd s X) \<rbrakk> \<Longrightarrow>
      (\<Gamma> \<turnstile> \<langle>C,(Normal (restrict_htd s X))\<rangle> \<Rightarrow> Abrupt (restrict_htd t X) \<and>
       point_eq_mod (lift_state (hst_mem t,hst_htd t))
          (lift_state (hst_mem s,hst_htd s)) X)"
  by (force simp: mem_safe_seq_def restrict_safe_seq_def restrict_safe_OK_seq_def)

lemma mem_safe_FaultD:
  "\<lbrakk> \<Gamma> \<turnstile>\<^sub>p \<langle>C,Normal s\<rangle> \<Rightarrow> Fault f; mem_safe C \<Gamma> \<rbrakk> \<Longrightarrow>
      exec_fatal C \<Gamma> (restrict_htd s X)"
  by (force simp: mem_safe_def restrict_safe_def)

lemma mem_safe_StuckD:
  "\<lbrakk> \<Gamma> \<turnstile>\<^sub>p \<langle>C,Normal s\<rangle> \<Rightarrow> Stuck; mem_safe C \<Gamma> \<rbrakk> \<Longrightarrow>
      exec_fatal C \<Gamma> (restrict_htd s X)"
  by (force simp: mem_safe_def restrict_safe_def)

lemma mem_safe_seq_FaultD:
  "\<lbrakk> \<Gamma> \<turnstile> \<langle>C,Normal s\<rangle> \<Rightarrow> Fault f; mem_safe_seq C \<Gamma> \<rbrakk> \<Longrightarrow>
      exec_fatal_seq C \<Gamma> (restrict_htd s X)"
  by (force simp: mem_safe_seq_def restrict_safe_seq_def)

lemma mem_safe_seq_StuckD:
  "\<lbrakk> \<Gamma> \<turnstile> \<langle>C,Normal s\<rangle> \<Rightarrow> Stuck; mem_safe_seq C \<Gamma> \<rbrakk> \<Longrightarrow>
      exec_fatal_seq C \<Gamma> (restrict_htd s X)"
  by (force simp: mem_safe_seq_def restrict_safe_seq_def)

lemma lift_state_d_restrict [simp]:
  "lift_state (h,(restrict_s d X)) = lift_state (h,d) |` X"
  by (auto simp: lift_state_def restrict_map_def restrict_s_def intro!: ext split: s_heap_index.splits)

lemma dom_merge_restrict [simp]:
  "(x ++ y) |` dom y = y"
  by (force simp: restrict_map_def None_com intro: ext)

lemma dom_compl_restrict [simp]:
  "x |` (UNIV - dom x) = Map.empty"
  by (force simp: restrict_map_def intro: ext)

lemma lift_state_point_eq_mod:
  "\<lbrakk> point_eq_mod (lift_state (h,d)) (lift_state (h',d')) X \<rbrakk> \<Longrightarrow>
      lift_state (h,d) |` (UNIV - X) =
          lift_state (h',d') |` (UNIV - X)"
  by (auto simp: point_eq_mod_def restrict_map_def intro: ext)

lemma htd_'_update_ind [simp]:
  "htd_ind f \<Longrightarrow> f (hst_htd_update x s) = f s"
  by (simp add: htd_ind_def)

lemma sep_frame':
  assumes orig_spec:  "\<forall>s. \<Gamma> \<turnstile> \<lbrace>s. P (f \<acute>(\<lambda>x. x)) (lift_hst \<acute>(\<lambda>x. x))\<rbrace>
                               C
                               \<lbrace>Q (g s \<acute>(\<lambda>x. x)) (lift_hst \<acute>(\<lambda>x. x))\<rbrace>"
      and hi_f: "htd_ind f" and hi_g: "htd_ind g"
      and hi_g': "\<forall>s. htd_ind (g s)"
      and safe: "mem_safe_seq (C::('s::heap_state_type,'b,'c) Language.com) \<Gamma>"
  shows "\<forall>s. \<Gamma> \<turnstile> \<lbrace>s. (P (f \<acute>(\<lambda>x. x)) \<and>\<^sup>* R (h \<acute>(\<lambda>x. x))) (lift_hst \<acute>(\<lambda>x. x))\<rbrace>
                 C
                 \<lbrace>(Q (g s \<acute>(\<lambda>x. x)) \<and>\<^sup>* R (h s)) (lift_hst \<acute>(\<lambda>x. x))\<rbrace>"
proof (rule, rule hoare_complete, simp only: valid_def, clarify)
  fix ta x
  assume ev: "\<Gamma>\<turnstile> \<langle>C,Normal x\<rangle> \<Rightarrow> ta" and
      pre: "(P (f x) \<and>\<^sup>* R (h x)) (lift_hst x)"
  then obtain s\<^sub>0 and s\<^sub>1 where pre_P: "P (f x) s\<^sub>0" and pre_R: "R (h x) s\<^sub>1" and
      disj: "s\<^sub>0 \<bottom> s\<^sub>1" and m: "lift_hst x = s\<^sub>1 ++ s\<^sub>0"
    by (clarsimp simp: sep_conj_def map_ac_simps)
  with orig_spec hi_f have nofault: "\<not> exec_fatal_seq C \<Gamma>
      (restrict_htd x (dom s\<^sub>0))"
    by (force simp: exec_fatal_seq_def image_def lift_hst_def cvalid_def valid_def
                    restrict_htd_def
              dest: hoare_sound)
  show "ta \<in> Normal ` {t. (Q (g x t) \<and>\<^sup>* R (h x)) (lift_hst t)}"
  proof (cases ta)
    case (Normal s)
    moreover with ev safe nofault have ev': "\<Gamma> \<turnstile>
        \<langle>C,Normal (x\<lparr> hst_htd := (restrict_s (hst_htd x) (dom s\<^sub>0)) \<rparr>)\<rangle> \<Rightarrow>
           Normal (s\<lparr> hst_htd := (restrict_s (hst_htd s) (dom s\<^sub>0)) \<rparr>)" and
        "point_eq_mod (lift_state (hst_mem s,hst_htd s))
            (lift_state (hst_mem x,hst_htd x)) (dom s\<^sub>0)"
      by (auto simp: restrict_htd_def dest: mem_safe_seq_NormalD)
    moreover with m disj have "s\<^sub>1 = lift_hst s |` (UNIV - dom s\<^sub>0)"
apply -
apply(clarsimp simp: lift_hst_def)
apply(subst lift_state_point_eq_mod)
 apply(drule sym)
 apply clarsimp
 apply fast
apply(simp add: lift_hst_def lift_state_point_eq_mod map_add_restrict)
apply(subst restrict_map_subdom, auto dest: map_disjD)
done
    ultimately show ?thesis using orig_spec hi_f hi_g hi_g' pre_P pre_R m
      by (force simp: cvalid_def valid_def image_def lift_hst_def
                      map_disj_def
                intro: sep_conjI dest: hoare_sound)
  next
    case (Abrupt s) with ev safe nofault orig_spec pre_P hi_f m show ?thesis
      by - (simp, drule spec, drule hoare_sound, drule_tac X="dom s\<^sub>0" in
            mem_safe_seq_AbruptD, assumption+,
            force simp: valid_def cvalid_def lift_hst_def restrict_htd_def)
  next
    case (Fault f) with ev safe nofault show ?thesis
      by (force dest: mem_safe_seq_FaultD)
  next
    case Stuck with ev safe nofault show ?thesis
      by (force dest: mem_safe_seq_StuckD)
  qed
qed

lemma sep_frame:
  "\<lbrakk> k = (\<lambda>s. (hst_mem s,hst_htd s));
      \<forall>s. \<Gamma> \<turnstile> \<lbrace>s. P (f \<acute>(\<lambda>x. x)) (lift_state (k \<acute>(\<lambda>x. x)))\<rbrace>
              C
              \<lbrace>Q (g s \<acute>(\<lambda>x. x)) (lift_state (k \<acute>(\<lambda>x. x)))\<rbrace>;
      htd_ind f; htd_ind g; \<forall>s. htd_ind (g s);
      mem_safe_seq (C::('s::heap_state_type,'b,'c) Language.com) \<Gamma> \<rbrakk> \<Longrightarrow>
      \<forall>s. \<Gamma> \<turnstile> \<lbrace>s. (P (f \<acute>(\<lambda>x. x)) \<and>\<^sup>* R (h \<acute>(\<lambda>x. x))) (lift_state (k \<acute>(\<lambda>x. x)))\<rbrace>
               C
               \<lbrace>(Q (g s \<acute>(\<lambda>x. x)) \<and>\<^sup>* R (h s)) (lift_state (k \<acute>(\<lambda>x. x)))\<rbrace>"
apply(simp only:)
apply(fold lift_hst_def)
apply(erule (4) sep_frame')
done


lemma point_eq_mod_safe [simp]:
  "\<lbrakk> point_eq_mod_safe P f g; restrict_htd s X \<in> P; x \<notin> X \<rbrakk> \<Longrightarrow>
      g (f s) x = (g s) x"
apply (simp add: point_eq_mod_safe_def point_eq_mod_def)
apply(case_tac x, force)
done

lemma comm_restrict_safe [simp]:
  "\<lbrakk> comm_restrict_safe P f; restrict_htd s X \<in> P \<rbrakk> \<Longrightarrow>
      restrict_htd (f s ) X = f (restrict_htd s X)"
  by (simp add: comm_restrict_safe_def comm_restrict_def)

lemma mono_guardD:
  "\<lbrakk> mono_guard P; restrict_htd s X \<in> P \<rbrakk> \<Longrightarrow> s \<in> P"
  by (unfold mono_guard_def, fast)

lemma expr_htd_ind:
  "expr_htd_ind P \<Longrightarrow> restrict_htd s X \<in> P = (s \<in> P)"
  by (simp add: expr_htd_ind_def restrict_htd_def)

lemmas exec_other_intros = exec.intros(1-3) exec.intros(5-16) exec.intros(18-19) exec.intros(21-)
lemmas seq_exec_other_intros = Semantic.exec.intros(1-3) Semantic.exec.intros(5-14) 
                               Semantic.exec.intros(16-17) Semantic.exec.intros(19-)

lemma exec_fatal_Seq:
  "exec_fatal C \<Gamma> s \<Longrightarrow> exec_fatal (C;;D) \<Gamma> s"
  by (force simp: exec_fatal_def intro: exec_other_intros)

lemma exec_fatal_Seq2:
  "\<lbrakk> \<Gamma> \<turnstile>\<^sub>p \<langle>C,Normal s\<rangle> \<Rightarrow> Normal t; exec_fatal D \<Gamma> t \<rbrakk> \<Longrightarrow> exec_fatal (C;;D) \<Gamma> s"
  by (force simp: exec_fatal_def intro: exec_other_intros)

lemma exec_fatal_seq_Seq:
  "exec_fatal_seq C \<Gamma> s \<Longrightarrow> exec_fatal_seq (Language.Seq C D) \<Gamma> s"
  by (force simp: exec_fatal_seq_def intro: seq_exec_other_intros)

lemma exec_fatal_seq_Seq2:
  "\<lbrakk> \<Gamma> \<turnstile> \<langle>C,Normal s\<rangle> \<Rightarrow> Normal t; exec_fatal_seq D \<Gamma> t \<rbrakk> \<Longrightarrow> exec_fatal_seq (Language.Seq C D) \<Gamma> s"
  by (force simp: exec_fatal_seq_def intro: seq_exec_other_intros)

lemma exec_fatal_Cond:
  "exec_fatal (Cond P C D) \<Gamma> s = (if s \<in> P then exec_fatal C \<Gamma> s else
      exec_fatal D \<Gamma> s)"
  by (force simp: exec_fatal_def intro: exec_other_intros
            elim: exec_Normal_elim_cases)

lemma exec_fatal_seq_Cond:
  "exec_fatal_seq (Language.Cond P C D) \<Gamma> s = (if s \<in> P then exec_fatal_seq C \<Gamma> s else
      exec_fatal_seq D \<Gamma> s)"
  by (force simp: exec_fatal_seq_def intro: seq_exec_other_intros
            elim: Semantic.exec_Normal_elim_cases)

lemma exec_fatal_While:
  "\<lbrakk> exec_fatal C \<Gamma> s; s \<in> P \<rbrakk> \<Longrightarrow> exec_fatal (While P C) \<Gamma> s"
  by (force simp: exec_fatal_def intro: exec_other_intros)

lemma exec_fatal_While2:
  "\<lbrakk> exec_fatal (While P C) \<Gamma> t; \<Gamma> \<turnstile>\<^sub>p \<langle>C,Normal s\<rangle> \<Rightarrow> Normal t; s \<in> P \<rbrakk> \<Longrightarrow>
      exec_fatal (While P C) \<Gamma> s"
  by (force simp: exec_fatal_def intro: exec_other_intros
            elim: exec_Normal_elim_cases)

lemma exec_fatal_seq_While:
  "\<lbrakk> exec_fatal_seq C \<Gamma> s; s \<in> P \<rbrakk> \<Longrightarrow> exec_fatal_seq (Language.While P C) \<Gamma> s"
  by (force simp: exec_fatal_seq_def intro:seq_exec_other_intros)

lemma exec_fatal_seq_While2:
  "\<lbrakk> exec_fatal_seq (Language.While P C) \<Gamma> t; \<Gamma> \<turnstile> \<langle>C,Normal s\<rangle> \<Rightarrow> Normal t; s \<in> P \<rbrakk> \<Longrightarrow>
      exec_fatal_seq (Language.While P C) \<Gamma> s"
  by (force simp: exec_fatal_seq_def intro: seq_exec_other_intros)


lemma exec_fatal_Call:
  "\<lbrakk> \<Gamma> p = Some C; exec_fatal C \<Gamma> s \<rbrakk> \<Longrightarrow> exec_fatal (Call p) \<Gamma> s"
  by (force simp: exec_fatal_def intro: exec_other_intros)


lemma exec_fatal_seq_Call:
  "\<lbrakk> \<Gamma> p = Some C; exec_fatal_seq C \<Gamma> s \<rbrakk> \<Longrightarrow> exec_fatal_seq (Language.Call p) \<Gamma> s"
  by (force simp: exec_fatal_seq_def intro: seq_exec_other_intros)

lemma exec_fatal_DynCom:
  "exec_fatal (f s) \<Gamma> s \<Longrightarrow> exec_fatal (DynCom f) \<Gamma> s"
  by (force simp: exec_fatal_def intro: exec_other_intros)


lemma exec_fatal_seq_DynCom:
  "exec_fatal_seq (f s) \<Gamma> s \<Longrightarrow> exec_fatal_seq (Language.DynCom f) \<Gamma> s"
  by (force simp: exec_fatal_seq_def intro: seq_exec_other_intros)

lemma exec_fatal_Guard:
  "exec_fatal (Guard f P C) \<Gamma> s = (s \<in> P \<longrightarrow> exec_fatal C \<Gamma> s)"
proof (cases "s \<in> P")
  case True thus ?thesis
    by (force simp: exec_fatal_def intro:exec_other_intros
              elim: exec_Normal_elim_cases)
next
  case False thus ?thesis
    by (force simp: exec_fatal_def intro: exec_other_intros)
qed

lemma exec_fatal_seq_Guard:
  "exec_fatal_seq (Language.Guard f P C) \<Gamma> s = (s \<in> P \<longrightarrow> exec_fatal_seq C \<Gamma> s)"
proof (cases "s \<in> P")
  case True thus ?thesis
    by (force simp: exec_fatal_seq_def intro: seq_exec_other_intros
              elim: Semantic.exec_Normal_elim_cases)
next
  case False thus ?thesis
    by (force simp: exec_fatal_seq_def intro: seq_exec_other_intros)
qed

lemma restrict_safe_seq_Guard:
  assumes restrict: "restrict_safe_seq s t C \<Gamma>"
  shows "restrict_safe_seq s t (Language.Guard f P C) \<Gamma>"
  using restrict 
  by (cases t; force simp:  restrict_safe_seq_def restrict_safe_OK_seq_def exec_fatal_seq_Guard
              intro: seq_exec_other_intros)

lemma restrict_safe_seq_Guard2:
  "\<lbrakk> s \<notin> P; mono_guard P \<rbrakk> \<Longrightarrow> restrict_safe_seq s (Fault f) (Language.Guard f P C) \<Gamma>"
  by (force simp: restrict_safe_seq_def exec_fatal_seq_def intro: seq_exec_other_intros
            dest: mono_guardD)

lemma restrict_safe_Guard:
  assumes restrict: "restrict_safe s t C \<Gamma>"
  shows "restrict_safe s t (Guard f P C) \<Gamma>"
proof (cases t)
  case (Normal s) with restrict show ?thesis
    by (force simp: restrict_safe_def restrict_safe_OK_def exec_fatal_Guard
              intro: exec_other_intros)
next
  case (Abrupt s) with restrict show ?thesis
    by (force simp: restrict_safe_def restrict_safe_OK_def exec_fatal_Guard
              intro:exec_other_intros)
next
  case (Fault f) with restrict show ?thesis
    by (force simp: restrict_safe_def exec_fatal_Guard)
next
  case Stuck with restrict show ?thesis
    by (force simp: restrict_safe_def exec_fatal_Guard)
qed

lemma restrict_safe_Guard2:
  "\<lbrakk> s \<notin> P; mono_guard P \<rbrakk> \<Longrightarrow> restrict_safe s (Fault f) (Guard f P C) \<Gamma>"
  by (force simp: restrict_safe_def exec_fatal_def intro: exec_other_intros
            dest: mono_guardD)

lemma exec_fatal_Catch:
  "exec_fatal C \<Gamma> s \<Longrightarrow> exec_fatal (TRY C CATCH D END) \<Gamma> s"
  by (force simp: exec_fatal_def intro: exec_other_intros)

lemma exec_fatal_Catch2:
  "\<lbrakk> \<Gamma> \<turnstile>\<^sub>p \<langle>C,Normal s\<rangle> \<Rightarrow> Abrupt t; exec_fatal D \<Gamma> t \<rbrakk> \<Longrightarrow>
      exec_fatal (TRY C CATCH D END) \<Gamma> s"
  by (force simp: exec_fatal_def intro: exec_other_intros)

lemma exec_fatal_seq_Catch:
  "exec_fatal_seq C \<Gamma> s \<Longrightarrow> exec_fatal_seq (Language.Catch C  D ) \<Gamma> s"
  by (force simp: exec_fatal_seq_def intro: seq_exec_other_intros)

lemma exec_fatal_seq_Catch2:
  "\<lbrakk> \<Gamma> \<turnstile> \<langle>C,Normal s\<rangle> \<Rightarrow> Abrupt t; exec_fatal_seq D \<Gamma> t \<rbrakk> \<Longrightarrow>
      exec_fatal_seq (Language.Catch C  D ) \<Gamma> s"
  by (force simp: exec_fatal_seq_def intro: seq_exec_other_intros)

lemma intra_safe_restrict_seq [rule_format]:
  assumes safe_env: "\<And>n C. \<Gamma> n = Some C \<Longrightarrow> intra_safe_seq C" and
      exec: "\<Gamma> \<turnstile> \<langle>C,s\<rangle> \<Rightarrow> t"
  shows "\<forall>s'. s = Normal s' \<longrightarrow> intra_safe_seq C \<longrightarrow> restrict_safe_seq s' t C \<Gamma>"
using exec
proof induct
  case (Skip s) thus ?case
    by (force simp: restrict_safe_seq_def restrict_safe_OK_seq_def intro: seq_exec_other_intros)
next
  case (Guard s' P C t f) show ?case
  proof (cases "\<exists>g. C = Language.Basic g")
    case False with Guard show ?thesis
      by - (clarsimp, split Language.com.splits, auto dest: restrict_safe_seq_Guard)
  next
    case True with Guard show ?thesis
      by (cases t) (force simp: restrict_safe_seq_def restrict_safe_OK_seq_def
                                point_eq_mod_safe_def exec_fatal_seq_Guard
                          intro:  seq_exec_other_intros
                          elim: Semantic.exec_Normal_elim_cases,
                    (fast elim: Semantic.exec_Normal_elim_cases)+)
  qed
next
  case (GuardFault C f P s) thus ?case
    by (force dest: restrict_safe_seq_Guard2)
next
  case (FaultProp C f) thus ?case by simp
next
  case (Basic f s) thus ?case
    by (force simp: restrict_safe_seq_def restrict_safe_OK_seq_def point_eq_mod_safe_def
              intro: seq_exec_other_intros)
next
  case (Spec r s t) thus ?case
    apply (clarsimp simp: mem_safe_seq_def)
    apply (fastforce intro: Semantic.exec.Spec)
    done
next
  case (SpecStuck r s) thus ?case
    apply clarsimp
    apply (erule_tac x=\<Gamma> in allE)
    apply (simp add: mem_safe_seq_def)
    apply (erule allE, erule allE, erule impE, erule Semantic.exec.SpecStuck)
    apply assumption
    done
next
  case (Seq C s sa D ta) show ?case
  proof (cases sa)
    case (Normal s') with Seq show ?thesis
      by (cases ta)
         (clarsimp simp: restrict_safe_seq_def restrict_safe_OK_seq_def,
          (drule_tac x=X in spec)+, auto intro: seq_exec_other_intros point_eq_mod_trans
                                               exec_fatal_seq_Seq exec_fatal_seq_Seq2)+
  next
    case (Abrupt s') with Seq show ?thesis
      by (force simp: restrict_safe_seq_def restrict_safe_OK_seq_def
                intro: seq_exec_other_intros dest: exec_fatal_seq_Seq
                elim: Semantic.exec_Normal_elim_cases)
  next
    case (Fault f) with Seq show ?thesis
      by (force simp: restrict_safe_seq_def dest: exec_fatal_seq_Seq)
  next
    case Stuck with Seq show ?thesis
      by (force simp: restrict_safe_seq_def dest: exec_fatal_seq_Seq)
  qed
next
  case (CondTrue s P C t D) thus ?case
    by (cases t)
       (auto simp: restrict_safe_seq_def restrict_safe_OK_seq_def exec_fatal_seq_Cond
             intro: seq_exec_other_intros dest: expr_htd_ind split: if_split_asm)
next
  case (CondFalse s P C t D) thus ?case
    by (cases t)
       (auto simp: restrict_safe_seq_def restrict_safe_OK_seq_def exec_fatal_seq_Cond
             intro: seq_exec_other_intros dest: expr_htd_ind split: if_split_asm)
next
  case (WhileTrue P C s s' t) show ?case
  proof (cases s')
    case (Normal sa) with WhileTrue show ?thesis
      by (cases t)
         (clarsimp simp: restrict_safe_seq_def restrict_safe_OK_seq_def,
          (drule_tac x=X in spec)+, auto simp: expr_htd_ind intro: seq_exec_other_intros
               point_eq_mod_trans exec_fatal_seq_While exec_fatal_seq_While2)+
  next
    case (Abrupt sa) with WhileTrue show ?thesis
      by (force simp: restrict_safe_seq_def restrict_safe_OK_seq_def expr_htd_ind
                intro: seq_exec_other_intros exec_fatal_seq_While
                elim: Semantic.exec_Normal_elim_cases)
  next
    case (Fault f) with WhileTrue show ?thesis
      by (force simp: restrict_safe_seq_def expr_htd_ind intro: exec_fatal_seq_While)
  next
    case Stuck with WhileTrue show ?thesis
      by (force simp: restrict_safe_seq_def expr_htd_ind intro: exec_fatal_seq_While)
  qed
next
  case (WhileFalse P C s) thus ?case
    by (force simp: restrict_safe_seq_def restrict_safe_OK_seq_def expr_htd_ind
              intro: seq_exec_other_intros)
next
  case (Call C p s t) with safe_env show ?case
    by (cases t)
       (auto simp: restrict_safe_seq_def restrict_safe_OK_seq_def
             intro: exec_fatal_seq_Call seq_exec_other_intros)
next
  case (CallUndefined p s) thus ?case
    by (force simp: restrict_safe_seq_def exec_fatal_seq_def intro: seq_exec_other_intros)

next
  case (StuckProp C) thus ?case by simp
next
  case (DynCom f s t) thus ?case
    by (cases t)
       (auto simp: restrict_safe_seq_def restrict_safe_OK_seq_def
                   restrict_htd_def
             intro!: seq_exec_other_intros exec_fatal_seq_DynCom)
next
  case (Throw s) thus ?case
    by (force simp: restrict_safe_seq_def restrict_safe_OK_seq_def intro: seq_exec_other_intros)
next
  case (AbruptProp C s) thus ?case by simp
next
  case (CatchMatch C D s s' t) thus ?case
    by (cases t)
       (clarsimp simp: restrict_safe_seq_def, drule_tac x=X in spec,
        auto simp: restrict_safe_OK_seq_def intro: seq_exec_other_intros point_eq_mod_trans
             dest: exec_fatal_seq_Catch exec_fatal_seq_Catch2)+
next
  case (CatchMiss C s t D) thus ?case
    by (cases t)
       (clarsimp simp: restrict_safe_seq_def, drule_tac x=X in spec,
        auto simp: restrict_safe_OK_seq_def intro: seq_exec_other_intros
             dest: exec_fatal_seq_Catch)+
qed

lemma intra_safe_intra_safe_seq:
  assumes a0:"\<And>n C. \<Gamma> n = Some C \<Longrightarrow> intra_safe C"
  shows "\<And>n C. \<Gamma>\<^sub>\<not>\<^sub>a n = Some C \<Longrightarrow> intra_safe_seq C"
proof-
  fix n C
  assume "\<Gamma>\<^sub>\<not>\<^sub>a n = Some C" 
  moreover obtain C\<^sub>p where  "C = sequential C\<^sub>p \<and> \<Gamma> n = Some C\<^sub>p \<and> noawaits C\<^sub>p" 
    by (meson lam1_seq no_await_some_no_await no_await_some_some_p not_Some_eq calculation)
  moreover have "intra_safe C\<^sub>p" using a0 calculation by auto
  ultimately show "intra_safe_seq C" using mem_safe_mem_safe_seq sorry
qed 

lemma intra_safe_restrict [rule_format]:
  assumes safe_env: "\<And>n C. \<Gamma> n = Some C \<Longrightarrow> intra_safe C" and
      exec: "\<Gamma> \<turnstile>\<^sub>p \<langle>C,s\<rangle> \<Rightarrow> t"
  shows "\<forall>s'. s = Normal s' \<longrightarrow> intra_safe C \<longrightarrow> restrict_safe s' t C \<Gamma>"
using exec
proof induct
  case (Skip s) thus ?case
    by (force simp: restrict_safe_def restrict_safe_OK_def intro: exec_other_intros)
next
  case (Guard s' P C t f) show ?case
  proof (cases "\<exists>g e. C = Basic g e")
    case False with Guard show ?thesis
      by - (clarsimp, split com.splits, auto dest: restrict_safe_Guard)
  next
    case True with Guard show ?thesis
      by (cases t) (force simp: restrict_safe_def restrict_safe_OK_def
                                point_eq_mod_safe_def exec_fatal_Guard
                          intro: exec_other_intros
                          elim: exec_Normal_elim_cases,
                    (fast elim: exec_Normal_elim_cases)+)
  qed
next
  case (GuardFault C f P s) thus ?case
    by (force dest: restrict_safe_Guard2)
next
  case (FaultProp C f) thus ?case by simp
next
  case (Basic f s) thus ?case
    by (force simp: restrict_safe_def restrict_safe_OK_def point_eq_mod_safe_def
              intro: exec_other_intros)
next
  case (Spec r s t) thus ?case
    apply (clarsimp simp: mem_safe_def)
    apply (fastforce intro: exec.Spec)
    done
next
  case (SpecStuck r s) thus ?case
    apply clarsimp
    apply (erule_tac x=\<Gamma> in allE)
    apply (simp add: mem_safe_def)
    apply (erule allE, erule allE, erule impE, erule exec.SpecStuck)
    apply assumption
    done
next
  case (Seq C s sa D ta) show ?case
  proof (cases sa)
    case (Normal s') with Seq show ?thesis
      by (cases ta)
         (clarsimp simp: restrict_safe_def restrict_safe_OK_def,
          (drule_tac x=X in spec)+, auto intro: exec_other_intros point_eq_mod_trans
                                               exec_fatal_Seq exec_fatal_Seq2)+
  next
    case (Abrupt s') with Seq show ?thesis
      by (force simp: restrict_safe_def restrict_safe_OK_def
                intro: exec_other_intros dest: exec_fatal_Seq
                elim: exec_Normal_elim_cases)
  next
    case (Fault f) with Seq show ?thesis
      by (force simp: restrict_safe_def dest: exec_fatal_Seq
                elim: exec_Normal_elim_cases)
  next
    case Stuck with Seq show ?thesis
      by (force simp: restrict_safe_def dest: exec_fatal_Seq
                elim: exec_Normal_elim_cases)
  qed
next
  case (CondTrue s P C t D) thus ?case
    by (cases t)
       (auto simp: restrict_safe_def restrict_safe_OK_def exec_fatal_Cond
             intro: exec_other_intros dest: expr_htd_ind split: if_split_asm)
next
  case (CondFalse s P C t D) thus ?case
    by (cases t)
       (auto simp: restrict_safe_def restrict_safe_OK_def exec_fatal_Cond
             intro: exec_other_intros dest: expr_htd_ind split: if_split_asm)
next
  case (WhileTrue P C s s' t) show ?case
  proof (cases s')
    case (Normal sa) with WhileTrue show ?thesis
      by (cases t)
         (clarsimp simp: restrict_safe_def restrict_safe_OK_def,
          (drule_tac x=X in spec)+, auto simp: expr_htd_ind intro: exec_other_intros
               point_eq_mod_trans exec_fatal_While exec_fatal_While2)+
  next
    case (Abrupt sa) with WhileTrue show ?thesis
      by (force simp: restrict_safe_def restrict_safe_OK_def expr_htd_ind
                intro: exec_other_intros exec_fatal_While
                elim: exec_Normal_elim_cases)
  next
    case (Fault f) with WhileTrue show ?thesis
      by (force simp: restrict_safe_def expr_htd_ind intro: exec_fatal_While)
  next
    case Stuck with WhileTrue show ?thesis
      by (force simp: restrict_safe_def expr_htd_ind intro: exec_fatal_While)
  qed
next
  case (AwaitTrue s b \<Gamma>\<^sub>p ca t)  
  then have "\<And>n C. \<Gamma>\<^sub>p n = Some C \<Longrightarrow> intra_safe_seq C"      
    by (meson safe_env intra_safe_intra_safe_seq)
  then have "\<forall>s'. Normal s = Normal s' \<longrightarrow> intra_safe_seq ca \<longrightarrow> restrict_safe_seq s' t ca \<Gamma>\<^sub>p"
    using intra_safe_restrict_seq AwaitTrue by blast
    then show ?case
      apply (cases t)
      apply (auto simp:  restrict_safe_def restrict_safe_OK_def exec_fatal_def exec_fatal_seq_def restrict_safe_seq_def mem_safe_seq_def
             intro: exec_other_intros dest: expr_htd_ind)
           apply (metis (no_types, lifting) AwaitTrue.hyps(1) AwaitTrue.hyps(2) exec.AwaitTrue expr_htd_ind restrict_safe_OK_seq_def)
          apply (metis (no_types, lifting) AwaitTrue.hyps(1) AwaitTrue.hyps(2) exec.AwaitTrue  expr_htd_ind restrict_safe_OK_seq_def)
         apply (metis AwaitTrue.hyps(1) AwaitTrue.hyps(2) exec.AwaitTrue  expr_htd_ind restrict_safe_OK_seq_def )
      apply (metis AwaitTrue.hyps(1) AwaitTrue.hyps(2) AwaitTrue.hyps(3) \<open>\<And>n C. \<Gamma>\<^sub>p n = Some C \<Longrightarrow> intra_safe_seq C\<close> exec.AwaitTrue exec_fatal_seq_def expr_htd_ind intra_safe_restrict_seq mem_safe_seq_AbruptD mem_safe_seq_def)
      apply (metis (full_types) AwaitTrue.hyps(1) AwaitTrue.hyps(2) exec.AwaitTrue expr_htd_ind_def restrict_htd_def)
      by (metis (no_types) AwaitTrue.hyps(1) AwaitTrue.hyps(2) exec.AwaitTrue expr_htd_ind_def restrict_htd_def)
next
  case (AwaitFalse s b ca) thus ?case
    by (simp add: exec.AwaitFalse expr_htd_ind restrict_safe_OK_def restrict_safe_def) 
next
  case (WhileFalse P C s) thus ?case
    by (force simp: restrict_safe_def restrict_safe_OK_def expr_htd_ind
              intro: exec_other_intros)
next
  case (Call C p s t) with safe_env show ?case
    by (cases t)
       (auto simp: restrict_safe_def restrict_safe_OK_def
             intro: exec_fatal_Call exec_other_intros)
next
  case (CallUndefined p s) thus ?case
    by (force simp: restrict_safe_def exec_fatal_def intro: exec_other_intros)

next
  case (StuckProp C) thus ?case by simp
next
  case (DynCom f s t) thus ?case
    by (cases t)
       (auto simp: restrict_safe_def restrict_safe_OK_def
                   restrict_htd_def
             intro!: exec_other_intros exec_fatal_DynCom)
next
  case (Throw s) thus ?case
    by (force simp: restrict_safe_def restrict_safe_OK_def intro: exec_other_intros)
next
  case (AbruptProp C s) thus ?case by simp
next
  case (CatchMatch C D s s' t) thus ?case
    by (cases t)
       (clarsimp simp: restrict_safe_def, drule_tac x=X in spec,
        auto simp: restrict_safe_OK_def intro: exec_other_intros point_eq_mod_trans
             dest: exec_fatal_Catch exec_fatal_Catch2)+
next
  case (CatchMiss C s t D) thus ?case
    by (cases t)
       (clarsimp simp: restrict_safe_def, drule_tac x=X in spec,
        auto simp: restrict_safe_OK_def intro: exec_other_intros
             dest: exec_fatal_Catch)+
qed

lemma intra_mem_safe:
  "\<lbrakk> \<And>n C. \<Gamma> n = Some C \<Longrightarrow> intra_safe C; intra_safe C \<rbrakk> \<Longrightarrow> mem_safe C \<Gamma>"
  by (force  simp: mem_safe_def intro: intra_safe_restrict)

lemma point_eq_mod_safe_triv:
  "(\<And>s. g (f s) = g s) \<Longrightarrow> point_eq_mod_safe P f g"
  by (simp add: point_eq_mod_safe_def point_eq_mod_def)

lemma comm_restrict_safe_triv:
  "(\<And>s X. f (s\<lparr> hst_htd := restrict_s (hst_htd s) X \<rparr>) =
      (f s)\<lparr> hst_htd := restrict_s (hst_htd (f s)) X \<rparr>) \<Longrightarrow> comm_restrict_safe P f"
  by (force simp: comm_restrict_safe_def comm_restrict_def restrict_htd_def)

lemma mono_guard_UNIV [simp]:
  "mono_guard UNIV"
  by (force simp: mono_guard_def)

lemma mono_guard_triv:
  "(\<And>s X. s\<lparr> hst_htd := X \<rparr> \<in> g \<Longrightarrow> s \<in> g) \<Longrightarrow> mono_guard g"
  by (unfold mono_guard_def, unfold restrict_htd_def, fast)

lemma mono_guard_triv2:
  "(\<And>s X. s\<lparr> hst_htd := X \<rparr> \<in> g = ((s::'a::heap_state_type') \<in> g)) \<Longrightarrow>
      mono_guard g"
  by (unfold mono_guard_def, unfold restrict_htd_def, fast)

lemma dom_restrict_s:
  "x \<in> dom_s (restrict_s d X) \<Longrightarrow> x \<in> dom_s d \<and> x \<in> X"
apply(auto simp: restrict_s_def dom_s_def split: if_split_asm)
done


lemma mono_guard_ptr_safe:
  "\<lbrakk> \<And>s. d s = hst_htd (s::'a::heap_state_type); htd_ind p \<rbrakk> \<Longrightarrow>
      mono_guard {s. ptr_safe (p s) (d s)}"
  apply (auto simp: mono_guard_def ptr_safe_def restrict_htd_def )
apply(drule (1) subsetD)
apply(drule dom_restrict_s)
apply simp
done

lemma point_eq_mod_safe_ptr_safe_update:
  "\<lbrakk> d = (hst_htd::'a::heap_state_type \<Rightarrow> heap_typ_desc);
      m = (\<lambda>s. hst_mem_update (heap_update (p s) ((v s)::'b::mem_type)) s);
      h = hst_mem; k = (\<lambda>s. lift_state (h s,d s)); htd_ind p \<rbrakk> \<Longrightarrow>
      point_eq_mod_safe {s. ptr_safe (p s) (d s)} m k"
  apply (auto simp: point_eq_mod_safe_def point_eq_mod_def ptr_safe_def heap_update_def
                 restrict_htd_def  lift_state_def
           intro!: heap_update_nmem_same split: s_heap_index.splits)
apply(subgoal_tac "(a,SIndexVal) \<in> s_footprint (p s)")
 apply(drule (1) subsetD)
 apply(drule dom_restrict_s, clarsimp)
apply(drule intvlD, clarsimp)
apply(erule s_footprintI2)
done

lemma field_ti_s_sub_typ:
  "field_lookup (export_uinfo (typ_info_t TYPE('b::mem_type))) f 0 = Some (typ_uinfo_t TYPE('a),b) \<Longrightarrow>
      s_footprint ((Ptr &(p\<rightarrow>f))::'a::mem_type ptr) \<subseteq> s_footprint (p::'b ptr)"
apply(drule field_ti_s_sub)
apply(simp add: s_footprint_def)
done

lemma ptr_safe_mono:
  "\<lbrakk> ptr_safe (p::'a::mem_type ptr) d; field_lookup (typ_info_t TYPE('a)) f 0
      = Some (t,n); export_uinfo t = typ_uinfo_t TYPE('b) \<rbrakk> \<Longrightarrow>
      ptr_safe ((Ptr &(p\<rightarrow>f))::'b::mem_type ptr) d"
apply(simp add: ptr_safe_def)
apply(drule field_lookup_export_uinfo_Some)
apply simp
apply(drule field_ti_s_sub_typ)
apply(erule (1) subset_trans)
done

lemma point_eq_mod_safe_ptr_safe_update_fl:
  "\<lbrakk> d = (hst_htd::'a::heap_state_type \<Rightarrow> heap_typ_desc);
      m = (\<lambda>s. hst_mem_update (heap_update (Ptr &((p s)\<rightarrow>f)) ((v s)::'b::mem_type)) s);
      h = hst_mem; k = (\<lambda>s. lift_state (h s,d s)); htd_ind p;
      field_lookup (typ_info_t TYPE('c)) f 0 = Some (t,n);
      export_uinfo t = typ_uinfo_t TYPE('b) \<rbrakk> \<Longrightarrow>
      point_eq_mod_safe {s. ptr_safe ((p::'a \<Rightarrow> 'c::mem_type ptr) s) (d s)} m k"
apply(drule (3) point_eq_mod_safe_ptr_safe_update)
 apply(simp only: htd_ind_def)
 apply clarify
apply(clarsimp simp: point_eq_mod_safe_def)
apply(drule_tac x=s in spec)
apply(drule_tac x=X in spec)
apply(erule impE)
 apply(erule (2) ptr_safe_mono)
apply simp
done

lemma point_eq_mod_safe_ptr_safe_tag:
  "\<lbrakk> d = (hst_htd::'a::heap_state_type \<Rightarrow> heap_typ_desc); h = hst_mem;
      m = (\<lambda>s. hst_htd_update (ptr_retyp (p s)) s);
      k = (\<lambda>s. lift_state (h s,d s));
      htd_ind p \<rbrakk> \<Longrightarrow>
      point_eq_mod_safe {s. ptr_safe ((p s)::'b::mem_type ptr) (d s)} m k"
apply(auto simp: point_eq_mod_safe_def point_eq_mod_def ptr_safe_def)
apply(subgoal_tac "(a,b) \<notin> s_footprint (p (restrict_htd s X))")
 prefer 2
 apply clarsimp
 apply(drule (1) subsetD)
 apply(clarsimp simp: restrict_htd_def)
 apply(drule dom_restrict_s, clarsimp)
 apply(thin_tac "P \<notin> Q" for P Q)
apply(auto simp: restrict_htd_def  lift_state_def split_def split: s_heap_index.splits split: option.splits)
     apply(subst (asm) ptr_retyp_d_eq_fst)
     apply(clarsimp split: if_split_asm)
     apply(erule notE)
     apply(drule intvlD, clarsimp)
     apply(erule s_footprintI2)
    apply(subst (asm) ptr_retyp_d_eq_fst)
    apply(clarsimp split: if_split_asm)
   apply(subst (asm) ptr_retyp_d_eq_snd)
   apply(clarsimp split: if_split_asm)
  apply(subst (asm) ptr_retyp_d_eq_snd)
  apply(clarsimp split: if_split_asm)
  apply(erule notE)
  apply(frule intvlD, clarsimp)
  apply(rule s_footprintI)
   apply(subst (asm) ptr_retyp_footprint)
    apply simp
   apply clarsimp
   apply(clarsimp simp: list_map_eq split: if_split_asm)
   apply(subst (asm) unat_of_nat)
   apply(subst (asm) mod_less)
    apply(subst len_of_addr_card)
    apply(erule less_trans)
    apply simp
   apply fast
  apply assumption
 apply(simp add: ptr_retyp_d_eq_snd)
 apply(clarsimp split: if_split_asm)
 apply(simp add: ptr_retyp_footprint)
 apply(clarsimp simp: list_map_eq split: if_split_asm)
 apply(erule notE)
 apply(drule intvlD, clarsimp)
 apply(rule s_footprintI)
  apply(subst (asm) unat_of_nat)
  apply(subst (asm) mod_less)
   apply(subst len_of_addr_card)
   apply(erule less_trans)
   apply simp
  apply assumption+
apply(simp add: ptr_retyp_d_eq_snd)
apply(clarsimp split: if_split_asm)
apply(simp add: ptr_retyp_footprint)
apply(clarsimp simp: list_map_eq split: if_split_asm)
apply(erule notE)
apply(drule intvlD, clarsimp)
apply(rule s_footprintI)
 apply(subst (asm) unat_of_nat)
 apply(subst (asm) mod_less)
  apply(subst len_of_addr_card)
  apply(erule less_trans)
  apply simp
 apply assumption+
apply(simp add: ptr_retyp_d_eq_snd)
apply(clarsimp split: if_split_asm)
apply(simp add: ptr_retyp_footprint)
apply(clarsimp simp: list_map_eq split: if_split_asm)
apply(erule notE)
apply(drule intvlD, clarsimp)
apply(rule s_footprintI)
 apply(subst (asm) unat_of_nat)
 apply(subst (asm) mod_less)
  apply(subst len_of_addr_card)
  apply(erule less_trans)
  apply simp
 apply assumption+
done

lemma comm_restrict_safe_ptr_safe_tag:
  fixes d::"'a::heap_state_type \<Rightarrow> heap_typ_desc"
  assumes fun_d: "d = hst_htd" and fun_upd:
      "m = (\<lambda>s. hst_htd_update (ptr_retyp (p s)) s)" and ind: "htd_ind p" and
      upd: "\<And>d d' (s::'a). hst_htd_update (d s) (hst_htd_update (d' s) s) =
                hst_htd_update ((d s) \<circ> (d' s)) s"
  shows "comm_restrict_safe {s. ptr_safe ((p s)::'b::mem_type ptr) (d s)}
          m"
proof (simp only: comm_restrict_safe_def comm_restrict_def, auto)
  fix s X
  assume "ptr_safe (p (restrict_htd s X)) (d (restrict_htd s X))"
  moreover from ind have p: "p (restrict_htd s X) = p s"
    by (simp add:  restrict_htd_def)
  ultimately have "ptr_retyp (p s) (restrict_s (hst_htd s) X) =
      restrict_s (ptr_retyp (p s) (hst_htd s))  X" using fun_d
apply -
apply(rule ext)
apply(auto simp: point_eq_mod_safe_def point_eq_mod_def ptr_safe_def)
apply(auto simp: restrict_htd_def )
apply(case_tac "x \<notin> {ptr_val (p s)..+size_of TYPE('b)}")
 apply(subst ptr_retyp_d)
  apply clarsimp
 apply(clarsimp simp: restrict_map_def restrict_s_def)
 apply(subst ptr_retyp_d)
  apply clarsimp
 apply simp
 apply(subst ptr_retyp_d)
  apply clarsimp
 apply simp
apply clarsimp
apply(subst ptr_retyp_footprint)
 apply fast
apply(clarsimp simp: restrict_map_def restrict_s_def)
apply(subst ptr_retyp_footprint)
 apply fast
apply simp
apply(subst ptr_retyp_footprint)
 apply fast
apply(rule)
 apply(subgoal_tac "(x,SIndexVal) \<in> s_footprint (p s)")
  apply(drule (1) subsetD)
  apply(clarsimp simp: dom_s_def)
 apply(drule intvlD, clarsimp)
 apply(erule s_footprintI2)
apply(rule ext)
apply(clarsimp simp: map_add_def list_map_eq)
apply(subgoal_tac "(x,SIndexTyp y) \<in> s_footprint (p s)")
 apply(drule (1) subsetD)
 apply(clarsimp simp: dom_s_def split: if_split_asm)
apply(drule intvlD, clarsimp)
apply(rule s_footprintI)
 apply(subst (asm) unat_simps)
 apply(subst (asm) mod_less)
  apply(subst len_of_addr_card)
  apply(erule less_trans)
  apply simp
 apply assumption+
done
  hence "((ptr_retyp (p s) \<circ> (%x _. x) (restrict_s (hst_htd s) X)::heap_typ_desc \<Rightarrow> heap_typ_desc) =
              (%x _. x) (restrict_s (ptr_retyp (p s) (hst_htd s)) X))"
    by - (rule ext, simp)
  moreover from upd have "hst_htd_update (ptr_retyp (p s))
        (hst_htd_update ((%x _. x) (restrict_s (hst_htd s) X)) s) =
         hst_htd_update (((ptr_retyp (p s)) \<circ> ((%x _. x) (restrict_s (hst_htd s) X)))) s" .
  moreover from upd have "hst_htd_update ((%x _. x) (restrict_s (ptr_retyp (p s) (hst_htd s)) X))
        (hst_htd_update (ptr_retyp (p s)) s) =
        hst_htd_update (((%x _. x) (restrict_s ((ptr_retyp (p s) (hst_htd s))) X)) \<circ> (ptr_retyp (p s)))
            s" .
  ultimately show "m (restrict_htd s X) =
          restrict_htd (m s) X" using fun_d fun_upd upd p
    by (simp add: restrict_htd_def o_def)
qed

lemmas intra_sc = hrs_comm comp_def hrs_htd_update_htd_update
  point_eq_mod_safe_triv comm_restrict_safe_triv mono_guard_triv2
  mono_guard_ptr_safe point_eq_mod_safe_ptr_safe_update
  point_eq_mod_safe_ptr_safe_tag comm_restrict_safe_ptr_safe_tag
  point_eq_mod_safe_ptr_safe_update_fl

declare expr_htd_ind_def [iff]
declare htd_ind_def [iff]


lemma noawaits_parallel:"noawaits (LanguageCon.parallel ca)"
  by(induct ca, auto)
(*
lemma "proc_deps_seq A (\<Gamma>\<^sub>\<not>\<^sub>a) \<subseteq> proc_deps (LanguageCon.parallel A) \<Gamma>"
  sorry
lemma proc_deps_par:"proc_deps (LanguageCon.parallel ca) (parallel_env \<Gamma>) = proc_deps_seq ca \<Gamma>"
  sorry *)

(* lemma "x \<in> intra_deps (Await b ca) \<Longrightarrow> 
       x \<in> proc_deps (LanguageCon.parallel ca) \<Gamma>"
proof(induct ca)
case Skip
  then show ?case by simp
next
  case (Basic x)
  then show ?case by simp
next
  case (Spec x)
  then show ?case by simp
next
  case (Seq ca1 ca2)
  then show ?case by simp
next
  case (Cond x1 ca1 ca2)
  then show ?case by simp
next
  case (While x1 ca)
  then show ?case by simp
next
  case (Call x)
  then show ?case by simp
next
case (DynCom x)
  then show ?case by simp
next
  case (Guard x1 x2a ca)
then show ?case by simp
next
  case Throw
  then show ?case by simp
next
  case (Catch ca1 ca2)
  then show ?case by simp
qed *)

(* lemma procs_deps_Await [simp]:
"proc_deps (Await b ca)  \<Gamma> = proc_deps (LanguageCon.parallel ca) \<Gamma>"
proof
  show "proc_deps (Await b ca) \<Gamma> \<subseteq> proc_deps (LanguageCon.parallel ca) \<Gamma>"
  proof
    fix x
    assume a0:"x \<in> proc_deps (Await b ca) \<Gamma>"
    then show "x \<in> proc_deps (LanguageCon.parallel ca) \<Gamma>"
    proof (induct)
      case (1 x)
      then show ?case   sorry
    next
      case (2 x D y)
      then show ?case sorry
    qed
  qed    
next
  show "proc_deps (LanguageCon.parallel ca) \<Gamma> \<subseteq> proc_deps (Await b ca) \<Gamma>"
    sorry
qed *)

lemma proc_deps_Skip [simp]:
  "proc_deps Skip \<Gamma> = {}"
  by (force elim: proc_deps.induct)

lemma proc_deps_Basic [simp]:
  "proc_deps (Basic f e) \<Gamma> = {}"
  by (force elim: proc_deps.induct)

lemma proc_deps_Spec [simp]:
  "proc_deps (Spec r e) \<Gamma> = {}"
  by (force elim: proc_deps.induct)

lemma proc_deps_Seq [simp]:
  "proc_deps (Seq C D) \<Gamma> = proc_deps C \<Gamma> \<union> proc_deps D \<Gamma>"
proof
  show "proc_deps (C;; D) \<Gamma> \<subseteq> proc_deps C \<Gamma> \<union> proc_deps D \<Gamma>"
    by - (rule, erule proc_deps.induct, auto intro: proc_deps.intros)
next
  show "proc_deps C \<Gamma> \<union> proc_deps D \<Gamma> \<subseteq> proc_deps (C;; D) \<Gamma>"
    by auto (erule proc_deps.induct, auto intro: proc_deps.intros)+
qed

lemma proc_deps_Cond [simp]:
  "proc_deps (Cond P C D) \<Gamma> = proc_deps C \<Gamma> \<union> proc_deps D \<Gamma>"
proof
  show "proc_deps (Cond P C D) \<Gamma> \<subseteq> proc_deps C \<Gamma> \<union> proc_deps D \<Gamma>"
    by - (rule, erule proc_deps.induct, auto intro: proc_deps.intros)
next
  show "proc_deps C \<Gamma> \<union> proc_deps D \<Gamma> \<subseteq> proc_deps (Cond P C D) \<Gamma>"
    by auto (erule proc_deps.induct, auto intro: proc_deps.intros)+
qed

lemma proc_deps_While [simp]:
  "proc_deps (While P C) \<Gamma> = proc_deps C \<Gamma>"
  by auto (erule proc_deps.induct, auto intro: proc_deps.intros)+

lemma proc_deps_Guard [simp]:
  "proc_deps (Guard f P C) \<Gamma> = proc_deps C \<Gamma>"
  by auto (erule proc_deps.induct, auto intro: proc_deps.intros)+

lemma proc_deps_Throw [simp]:
  "proc_deps Throw \<Gamma> = {}"
  by (force elim: proc_deps.induct)

lemma proc_deps_Catch [simp]:
  "proc_deps (Catch  C D) \<Gamma> = proc_deps C \<Gamma> \<union> proc_deps D \<Gamma>"
proof
  show "proc_deps (Catch C D) \<Gamma> \<subseteq> proc_deps C \<Gamma> \<union> proc_deps D \<Gamma>"
    by - (rule, erule proc_deps.induct, auto intro: proc_deps.intros)
next
  show "proc_deps C \<Gamma> \<union> proc_deps D \<Gamma> \<subseteq> proc_deps (Catch C D) \<Gamma>"
    by auto (erule proc_deps.induct, auto intro: proc_deps.intros)+
qed

lemma proc_deps_Call [simp]:
  "proc_deps (Call p) \<Gamma> = {p} \<union> (case \<Gamma> p of Some C \<Rightarrow>
      proc_deps C (\<Gamma>(p := None)) | _ \<Rightarrow> {})" (is "?X = ?Y \<union> ?Z")
proof
  show "?X \<subseteq> ?Y \<union> ?Z"
    by - (rule, erule proc_deps.induct,
          auto intro: proc_deps.intros,
          case_tac "xa = p", auto intro: proc_deps.intros split: option.splits)
next
  show "?Y \<union> ?Z \<subseteq> ?X"
  proof (clarsimp, rule)
    show "p \<in> ?X" by (force intro: proc_deps.intros)
  next
    show "?Z \<subseteq> ?X"
      by (split option.splits, rule, force intro: proc_deps.intros)
         (clarify, erule proc_deps.induct, (force intro: proc_deps.intros
          split: if_split_asm)+)
  qed
qed

lemma proc_deps_DynCom [simp]:
  "proc_deps (DynCom f) \<Gamma> = \<Union>{proc_deps (f s) \<Gamma> | s. True}"
  by auto (erule proc_deps.induct, force intro: proc_deps.intros,
           force intro: proc_deps.intros)+

lemma proc_deps_Skip_seq [simp]:
  "proc_deps_seq Language.Skip \<Gamma> = {}"
  by (force elim: proc_deps_seq.induct)

lemma proc_deps_Basic_seq [simp]:
  "proc_deps_seq (Language.Basic f) \<Gamma> = {}"
  by (force elim: proc_deps_seq.induct)

lemma proc_deps_Spec_seq [simp]:
  "proc_deps_seq (Language.Spec r) \<Gamma> = {}"
  by (force elim: proc_deps_seq.induct)

lemma proc_deps_Seq_seq [simp]:
  "proc_deps_seq (Language.Seq C D) \<Gamma> = proc_deps_seq C \<Gamma> \<union> proc_deps_seq D \<Gamma>"
proof
  show "proc_deps_seq (Language.com.Seq C D) \<Gamma> \<subseteq> proc_deps_seq C \<Gamma> \<union> proc_deps_seq D \<Gamma>"
    by - (rule, erule proc_deps_seq.induct, auto intro: proc_deps_seq.intros)
next
  show "proc_deps_seq C \<Gamma> \<union> proc_deps_seq D \<Gamma> \<subseteq> proc_deps_seq (Language.com.Seq C D) \<Gamma>"
    by auto (erule proc_deps_seq.induct, auto intro: proc_deps_seq.intros)+
qed

lemma proc_deps_Cond_seq [simp]:
  "proc_deps_seq (Language.Cond P C D) \<Gamma> = proc_deps_seq C \<Gamma> \<union> proc_deps_seq D \<Gamma>"
proof
  show "proc_deps_seq (Language.Cond P C D) \<Gamma> \<subseteq> proc_deps_seq C \<Gamma> \<union> proc_deps_seq D \<Gamma>"
    by - (rule, erule proc_deps_seq.induct, auto intro: proc_deps_seq.intros)
next
  show "proc_deps_seq C \<Gamma> \<union> proc_deps_seq D \<Gamma> \<subseteq> proc_deps_seq (Language.Cond P C D) \<Gamma>"
    by auto (erule proc_deps_seq.induct, auto intro: proc_deps_seq.intros)+
qed

lemma proc_deps_While_seq [simp]:
  "proc_deps_seq (Language.While P C) \<Gamma> = proc_deps_seq C \<Gamma>"
  by auto (erule proc_deps_seq.induct, auto intro: proc_deps_seq.intros)+

lemma proc_deps_Guard_seq [simp]:
  "proc_deps_seq (Language.Guard f P C) \<Gamma> = proc_deps_seq C \<Gamma>"
  by auto (erule proc_deps_seq.induct, auto intro: proc_deps_seq.intros)+

lemma proc_deps_Throw_seq [simp]:
  "proc_deps_seq Language.Throw \<Gamma> = {}"
  by (force elim: proc_deps_seq.induct)

lemma proc_deps_Catch_seq [simp]:
  "proc_deps_seq (Language.Catch  C D) \<Gamma> = proc_deps_seq C \<Gamma> \<union> proc_deps_seq D \<Gamma>"
proof
  show "proc_deps_seq (Language.Catch C D) \<Gamma> \<subseteq> proc_deps_seq C \<Gamma> \<union> proc_deps_seq D \<Gamma>"
    by - (rule, erule proc_deps_seq.induct, auto intro: proc_deps_seq.intros)
next
  show "proc_deps_seq C \<Gamma> \<union> proc_deps_seq D \<Gamma> \<subseteq> proc_deps_seq (Language.Catch C D) \<Gamma>"
    by auto (erule proc_deps_seq.induct, auto intro: proc_deps_seq.intros)+
qed

lemma proc_deps_Call_seq [simp]:
  "proc_deps_seq (Language.Call p) \<Gamma> = {p} \<union> (case \<Gamma> p of Some C \<Rightarrow>
      proc_deps_seq C (\<Gamma>(p := None)) | _ \<Rightarrow> {})" (is "?X = ?Y \<union> ?Z")
proof
  show "?X \<subseteq> ?Y \<union> ?Z"
    by - (rule, erule proc_deps_seq.induct,
          auto intro: proc_deps_seq.intros,
          case_tac "xa = p", auto intro: proc_deps_seq.intros split: option.splits)
next
  show "?Y \<union> ?Z \<subseteq> ?X"
  proof (clarsimp, rule)
    show "p \<in> ?X" by (force intro: proc_deps_seq.intros)
  next
    show "?Z \<subseteq> ?X"
      by (split option.splits, rule, force intro: proc_deps_seq.intros)
         (clarify, erule proc_deps_seq.induct, (force intro: proc_deps_seq.intros
          split: if_split_asm)+)
  qed
qed

lemma proc_deps_DynCom_seq [simp]:
  "proc_deps_seq (Language.DynCom f) \<Gamma> = \<Union>{proc_deps_seq (f s) \<Gamma> | s. True}"
  by auto (erule proc_deps_seq.induct, force intro: proc_deps_seq.intros,
           force intro: proc_deps_seq.intros)+

lemma proc_deps_restrict:
  "proc_deps C \<Gamma> \<subseteq> proc_deps C (\<Gamma>(p := None)) \<union> proc_deps (Call p) \<Gamma>"
proof rule
  fix xa
  assume mem: "xa \<in> proc_deps C \<Gamma>"
  hence "\<forall>p. xa \<in> proc_deps C (\<Gamma>(p := None)) \<union> proc_deps (Call p) \<Gamma>" (is "?X")
  using mem
  proof induct
    fix x
    assume "x \<in> intra_deps C"
    thus "\<forall>p. x \<in> proc_deps C (\<Gamma>(p := None)) \<union> proc_deps (Call p) \<Gamma>"
      by (force intro: proc_deps.intros)
  next
    fix D x y
    assume x:
      "x \<in> proc_deps C \<Gamma>"
      "x \<in> proc_deps C \<Gamma> \<Longrightarrow> \<forall>p. x \<in> proc_deps C (\<Gamma>(p := None)) \<union> proc_deps (Call p) \<Gamma>"
      "\<Gamma> x = Some D"
      "y \<in> intra_deps D"
      "y \<in> proc_deps C \<Gamma>"
    show "\<forall>p. y \<in> proc_deps C (\<Gamma>(p := None)) \<union> proc_deps (Call p) \<Gamma>"
    proof clarify
      fix p
      assume y: "y \<notin> proc_deps (Call p) \<Gamma>"
      show "y \<in> proc_deps C (\<Gamma>(p := None))"
      proof (cases "x=p")
        case True with x y show ?thesis
          by (force intro: proc_deps.intros)
      next
        case False with x y show ?thesis
          by (clarsimp, drule_tac x=p in spec)
             (auto intro: proc_deps.intros split: option.splits)
      qed
    qed
  qed
  thus "xa \<in> proc_deps C (\<Gamma>(p := None)) \<union> proc_deps (Call p) \<Gamma>" by simp
qed


lemma proc_deps_seq_restrict:
  "proc_deps_seq C \<Gamma> \<subseteq> proc_deps_seq C (\<Gamma>(p := None)) \<union> proc_deps_seq (Language.Call p) \<Gamma>"
proof rule
  fix xa
  assume mem: "xa \<in> proc_deps_seq C \<Gamma>"
  hence "\<forall>p. xa \<in> proc_deps_seq C (\<Gamma>(p := None)) \<union> proc_deps_seq (Language.Call p) \<Gamma>" (is "?X")
  using mem
  proof induct
    fix x
    assume "x \<in> intra_deps_seq C"
    thus "\<forall>p. x \<in> proc_deps_seq C (\<Gamma>(p := None)) \<union> proc_deps_seq (Language.Call p) \<Gamma>"
      by (force intro: proc_deps_seq.intros)
  next
    fix D x y
    assume x:
      "x \<in> proc_deps_seq C \<Gamma>"
      "x \<in> proc_deps_seq C \<Gamma> \<Longrightarrow> \<forall>p. x \<in> proc_deps_seq C (\<Gamma>(p := None)) \<union> proc_deps_seq (Language.Call p) \<Gamma>"
      "\<Gamma> x = Some D"
      "y \<in> intra_deps_seq D"
      "y \<in> proc_deps_seq C \<Gamma>"
    show "\<forall>p. y \<in> proc_deps_seq C (\<Gamma>(p := None)) \<union> proc_deps_seq (Language.Call p) \<Gamma>"
    proof clarify
      fix p
      assume y: "y \<notin> proc_deps_seq (Language.Call p) \<Gamma>"
      show "y \<in> proc_deps_seq C (\<Gamma>(p := None))"
      proof (cases "x=p")
        case True with x y show ?thesis
          by (force intro: proc_deps_seq.intros)
      next
        case False with x y show ?thesis
          by (clarsimp, drule_tac x=p in spec)
             (auto intro: proc_deps_seq.intros split: option.splits)
      qed
    qed
  qed
  thus "xa \<in> proc_deps_seq C (\<Gamma>(p := None)) \<union> proc_deps_seq (Language.Call p) \<Gamma>" by simp
qed



(* lemma equiv_proc_deps_seq1:
 "x \<in> proc_deps_seq C \<Gamma> \<Longrightarrow> x \<in> proc_deps (LanguageCon.parallel C) (parallel_env \<Gamma>)"
proof(induct C)
  case Skip
  then show ?case sorry
next
  case (Basic x)
  then show ?case sorry
next
case (Spec x)
then show ?case sorry
next
  case (Seq C1 C2)
  then show ?case sorry
next
  case (Cond x1 C1 C2)
  then show ?case sorry
next
  case (While x1 C)
then show ?case sorry
next
  case (Call x)
then show ?case sorry
next
  case (DynCom x)
  then show ?case sorry
next
  case (Guard x1 x2a C)
  then show ?case sorry
next
case Throw
  then show ?case sorry
next
  case (Catch C1 C2)
then show ?case sorry
qed
  case (1 x)
then show ?case sorry
next
  case (2 x D y)
  then show ?case sorry
qed
  *)


(* lemma equiv_proc_deps_seq2:
"x \<in> proc_deps (LanguageCon.parallel C) (parallel_env \<Gamma>) \<Longrightarrow> x \<in> proc_deps_seq C \<Gamma>"
sorry 

lemma "proc_deps_seq C \<Gamma> = proc_deps (LanguageCon.parallel C) (parallel_env \<Gamma>)"
  using equiv_proc_deps_seq1 equiv_proc_deps_seq2
  by (metis Collect_cong proc_deps_def proc_deps_seq_def 
     proc_deps_seqp_proc_deps_seq_eq proc_depsp_proc_deps_eq) *)

lemma exec_restrict2_seq:
   assumes exec: "\<Gamma> \<turnstile> \<langle>C,s\<rangle> \<Rightarrow> t"
  shows "\<And>X. proc_deps_seq C \<Gamma> \<subseteq> X \<Longrightarrow> \<Gamma> |` X \<turnstile> \<langle>C,s\<rangle> \<Rightarrow> t"
using exec
proof induct
  case (Call p C s t) thus ?case
    by  (insert proc_deps_seq_restrict [of C \<Gamma> p],
          auto intro!: seq_exec_other_intros split: option.splits)
next
  case (DynCom f s t) thus ?case
    by - (rule Semantic.exec.intros, simp, blast)
qed(auto intro: seq_exec_other_intros)+

lemma intra_seq_in_intra:
  assumes a0:"D = sequential d" and    
    a1:"y \<in> intra_deps_seq D" 
  shows "y \<in> intra_deps d"
  using a0 a1 
proof(induct d arbitrary: D y)
  case (DynCom x)
  then show ?case by fastforce
qed(auto)

lemma proc_deps_seq_subset1:"x \<in> proc_deps_seq ca  (\<Gamma>\<^sub>\<not>\<^sub>a) \<Longrightarrow> x \<in> proc_deps (Await b ca e)  \<Gamma>"
proof (induct rule:proc_deps_seq.induct)
  case (1 x)
  then show ?case 
     by (fastforce intro: proc_deps.intros(1))
next
  case (2 x D y)
  then obtain d where "\<Gamma> x = Some d \<and> D = sequential d"  
    using in_gamma_in_noawait_gamma lam1_seq[of "\<Gamma>\<^sub>\<not>\<^sub>a" "\<Gamma>" x D] by fast
  moreover have "y\<in> intra_deps d" using calculation 2 intra_seq_in_intra no_await_some_no_await 
    by fastforce 
  ultimately show ?case using 2 proc_deps.intros by auto 
qed  

lemma proc_deps_seq_subset:"proc_deps_seq ca  (\<Gamma>\<^sub>\<not>\<^sub>a) \<subseteq> proc_deps (Await b ca e)  \<Gamma>"
  using proc_deps_seq_subset1 by auto

lemma exec_restrict2_Await:
  assumes a0:"\<Gamma>\<^sub>\<not>\<^sub>a \<turnstile> \<langle>ca,Normal s\<rangle> \<Rightarrow> t" and a1:"proc_deps (Await b ca e)  \<Gamma> \<subseteq> X"
  shows "\<Gamma>\<^sub>\<not>\<^sub>a |\<^bsub>X\<^esub> \<turnstile> \<langle>ca,Normal s\<rangle> \<Rightarrow> t"
  apply (rule exec_restrict2_seq[OF a0])
  by (meson a1 dual_order.trans proc_deps_seq_subset)

lemma exec_restrict_seq:
  assumes exec: "\<Gamma>' \<turnstile> \<langle>C,s\<rangle> \<Rightarrow> t"
  shows "\<And>\<Gamma> X. \<lbrakk> \<Gamma>' = \<Gamma> |` X; proc_deps_seq C \<Gamma> \<subseteq> X \<rbrakk> \<Longrightarrow> \<Gamma> \<turnstile> \<langle>C,s\<rangle> \<Rightarrow> t"
using exec
proof induct
  case (Seq C D s sa ta) thus ?case by (force intro: seq_exec_other_intros)
next
  case (WhileTrue P C s s' t) thus ?case by (force intro: seq_exec_other_intros)
next
  case (Call p C s t) thus ?case
    by - (insert proc_deps_seq_restrict [of C \<Gamma> p], force intro: seq_exec_other_intros)
next
  case (DynCom f s t) thus ?case by (force intro: seq_exec_other_intros)
next
  case (CatchMatch C D s s' t) thus ?case by (force intro: seq_exec_other_intros)
qed (auto simp: intro: seq_exec_other_intros)

 lemma exec_restrict1_seq:
  assumes 
    a1:"(\<Gamma>|\<^bsub>X\<^esub>)\<^sub>\<not>\<^sub>a\<turnstile> \<langle>ca,Normal s\<rangle> \<Rightarrow> t" and    
    a3:"proc_deps (Await b ca e) \<Gamma> \<subseteq> X"
  shows "\<Gamma>\<^sub>\<not>\<^sub>a\<turnstile> \<langle>ca,Normal s\<rangle> \<Rightarrow> t"
   using exec_restrict_seq
   using a1 a3 proc_deps_seq_subset restrict_eq by fastforce

lemma exec_restrict_Await:
  assumes a0:"s \<in> b" and    
    a1:"(\<Gamma>|\<^bsub>X\<^esub>)\<^sub>\<not>\<^sub>a\<turnstile> \<langle>ca,Normal s\<rangle> \<Rightarrow> t" and
    a2:"proc_deps (Await b ca e) \<Gamma> \<subseteq> X"
  shows "\<Gamma>\<turnstile>\<^sub>p \<langle>Await b ca e,Normal s\<rangle> \<Rightarrow> t"
using a0 exec.intros exec_restrict1_seq[OF a1 a2] by fast

lemma exec_restrict:
  assumes exec: "\<Gamma>' \<turnstile>\<^sub>p \<langle>C,s\<rangle> \<Rightarrow> t"
  shows "\<And>\<Gamma> X. \<lbrakk> \<Gamma>' = \<Gamma> |` X; proc_deps C \<Gamma> \<subseteq> X \<rbrakk> \<Longrightarrow> \<Gamma> \<turnstile>\<^sub>p \<langle>C,s\<rangle> \<Rightarrow> t"
using exec
proof induct
  case (Seq C D s sa ta) thus ?case by (fastforce intro: exec_other_intros)
next
  case (WhileTrue P C s s' t) thus ?case by (fastforce intro: exec_other_intros)
next
  case (AwaitTrue s b \<Gamma>\<^sub>p ca t \<Gamma> X) thus ?case by (auto simp: exec_restrict_Await intro: exec_other_intros )
next
  case (Call p C s t) thus ?case
    by - (insert proc_deps_restrict [of C \<Gamma> p], fastforce intro: exec_other_intros)
next
  case (DynCom f s t) thus ?case by (fastforce intro: exec_other_intros)
next
  case (CatchMatch C D s s' t) thus ?case by (fastforce intro: exec_other_intros)
qed (auto simp: exec_restrict1_seq intro: exec_other_intros)



lemma exec_restrict2:
  assumes exec: "\<Gamma> \<turnstile>\<^sub>p \<langle>C,s\<rangle> \<Rightarrow> t"
  shows "\<And>X. proc_deps C \<Gamma> \<subseteq> X \<Longrightarrow> \<Gamma> |` X \<turnstile>\<^sub>p \<langle>C,s\<rangle> \<Rightarrow> t"
using exec
proof induct 
  case (Call p C s t) thus ?case
    by  (insert proc_deps_restrict [of C \<Gamma> p],
          auto intro!: exec_other_intros split: option.splits)
next
  case (DynCom f s t) thus ?case
    by - (rule exec.intros, simp, blast)
qed (auto simp: restrict_eq   exec_restrict2_Await intro: exec_other_intros)

lemma exec_restrict_eq:
  "\<Gamma> |` proc_deps C \<Gamma> \<turnstile>\<^sub>p \<langle>C,s\<rangle> \<Rightarrow> t = \<Gamma> \<turnstile>\<^sub>p \<langle>C,s\<rangle> \<Rightarrow> t"
  by (fast intro: exec_restrict exec_restrict2)
                        
lemma mem_safe_restrict:
  "mem_safe C \<Gamma> = mem_safe C (\<Gamma> |` proc_deps C \<Gamma>)"
  by (auto simp: mem_safe_def restrict_safe_def restrict_safe_OK_def
                 exec_restrict_eq exec_fatal_def
           split: xstate.splits)

end
