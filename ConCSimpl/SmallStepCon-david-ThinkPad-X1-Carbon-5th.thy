(*
    Author:      David Sanan
    Maintainer:  David Sanan, sanan at ntu edu sg
    License:     LGPL
*)

(*  Title:      SmallStepCon.thy
    Author:     David Sanan, NTU

Copyright (C) 2015-2016 David Sanan 
Some rights reserved, NTU
This library is free software; you can redistribute it and/or modify
it under the terms of the GNU Lesser General Public License as
published by the Free Software Foundation; either version 2.1 of the
License, or (at your option) any later version.

This library is distributed in the hope that it will be useful, but
WITHOUT ANY WARRANTY; without even the implied warranty of
MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE. See the GNU
Lesser General Public License for more details.

You should have received a copy of the GNU Lesser General Public
License along with this library; if not, write to the Free Software
Foundation, Inc., 59 Temple Place, Suite 330, Boston, MA 02111-1307
USA
*)

section {* Small-Step Semantics and Infinite Computations*} 

theory SmallStepCon imports "EmbSimpl.SmallStep" "SemanticCon" 
                            "TerminationCon"
                            (* "Sep_Algebra.Sep_Heap_Instance" 
                            "Actions.ActionsSemantics" *)
begin

text {* The redex of a statement is the substatement, which is actually altered
by the next step in the small-step semantics.
*}
primrec redex:: "('s,'p,'f,'e)com \<Rightarrow> ('s,'p,'f,'e)com"
where
"redex Skip = Skip" |
"redex (Basic f e) = (Basic f e)" |
"redex (Spec r e) = (Spec r e)" |
"redex (Seq c\<^sub>1 c\<^sub>2) = redex c\<^sub>1" |
"redex (Cond b c\<^sub>1 c\<^sub>2) = (Cond b c\<^sub>1 c\<^sub>2)" |
"redex (While b c) = (While b c)" |
"redex (Call p) = (Call p)" |
"redex (DynCom d) = (DynCom d)" |
"redex (Guard f b c) = (Guard f b c)" |
"redex (Throw) = Throw" |
"redex (Catch c\<^sub>1 c\<^sub>2) = redex c\<^sub>1" |
"redex (Await b c e) = (Await b c e)"

subsection {*Small-Step Computation: @{text "\<Gamma>\<turnstile>\<^sub>c(c, s) \<rightarrow> (c', s')"}*}

(* locale localsvars  =     
  fixes toSeq :: "(('g \<times> 'l \<times> 'l list),'f) xstate \<Rightarrow> ('s,'f) xstate"   
  fixes SegGl :: "'s \<Rightarrow> 'g"
  fixes SegLo ::"'s \<Rightarrow> 'l"

assumes SeqFault:"toSeq (Fault f) = Fault f" and
        SeqStuck:"toSeq (Stuck) = Stuck" and
        SeqNormal:"toSeq (Normal (g,l,ls)) = Normal s \<and> SegGl s = g \<and> SegLo s = l" and
        SeqEq:"toSeq (Normal (g,l,ls)) = toSeq (Normal (g,l,ls'))" and
        SeqEqAbr:"toSeq (Abrupt (g,l,ls)) = toSeq (Abrupt (g,l,ls'))" and
        SeqAbrupt:"toSeq (Abrupt (g,l,ls)) = Abrupt s \<and> SegGl s = g \<and> SegLo s = l" 
begin
primrec fromSeq ::"('s, 'f) xstate \<Rightarrow> 'l list \<Rightarrow> (('g \<times> 'l \<times> 'l list),'f) xstate"
  where "fromSeq (Normal s) locs = Normal (SegGl s, SegLo s, locs)"
  |"fromSeq (Abrupt s) locs = Abrupt (SegGl s, SegLo s, locs)"
  |"fromSeq (Fault f) locs = Fault f"
  |"fromSeq Stuck locs = Stuck"

lemma ParFault:"fromSeq (Fault f) ls = Fault f" and
      ParStuck:"fromSeq (Stuck) ls = Stuck" and
      ParNormal:"fromSeq (Normal s) ls = Normal (SegGl s, SegLo s, ls)" and
      ParAbrupt:"fromSeq (Abrupt s) ls = Abrupt (SegGl s, SegLo s, ls)"
  by auto

lemma abnormal_from_to:"\<forall>s'. s\<noteq>Normal s' \<and> s\<noteq>Abrupt s' \<Longrightarrow>  fromSeq (toSeq s) x = s" 
  by (cases s, auto simp add: SeqFault ParFault SeqStuck ParStuck)
  
lemma abnormal_to_from:"\<forall>s'. s\<noteq>Normal s' \<and> s\<noteq>Abrupt s' \<Longrightarrow>  toSeq (fromSeq s x) = s" 
  by (cases s, auto simp add: SeqFault ParFault SeqStuck ParStuck)  

lemma normal_to_from:"fromSeq (toSeq (Normal (g,l,ls))) x = Normal (g,l,x)"
  using SeqNormal ParNormal by (metis (full_types))

lemma normal_from_to:"toSeq (fromSeq (Normal s) x) = Normal s"
  using SeqNormal ParNormal by auto

lemma abrupt_to_from:"fromSeq (toSeq (Abrupt (g,l,ls))) x = Abrupt (g,l,x)"
  using SeqAbrupt ParAbrupt by (metis (full_types))

lemma abrutp_from_to:"toSeq (fromSeq (Abrupt s) x) = Abrupt s"
  using SeqAbrupt ParAbrupt by auto

lemma to_seq_distinct:
      "toSeq (Normal s1) \<noteq>  toSeq (Abrupt  s2) \<and>
       toSeq (Normal s1) \<noteq>  toSeq (Stuck) \<and>
       toSeq (Normal s1) \<noteq>  toSeq (Fault f) \<and>
       toSeq (Abrupt s2) \<noteq> toSeq (Stuck) \<and>
       toSeq (Abrupt s2) \<noteq> toSeq (Fault f) \<and>
       toSeq (Stuck) \<noteq> toSeq (Fault f)"
  using  SeqNormal SeqStuck  SeqAbrupt  SeqFault  
  by (smt prod_cases3 xstate.distinct)+

lemma from_seq_distinct:
      "fromSeq (Normal s1) \<noteq>  fromSeq (Abrupt  s2) \<and>
       fromSeq (Normal s1) \<noteq>  fromSeq (Stuck) \<and>
       fromSeq (Normal s1) \<noteq>  fromSeq (Fault f) \<and>
       fromSeq (Abrupt s2) \<noteq> fromSeq (Stuck) \<and>
       fromSeq (Abrupt s2) \<noteq> fromSeq (Fault f) \<and>
       fromSeq (Stuck) \<noteq> fromSeq (Fault f)"    
  using  ParFault ParStuck  ParAbrupt  ParNormal  
  by (smt prod_cases3 xstate.distinct)+

lemma toSeq_eq:"(toSeq (Normal (g,l,ls)) = toSeq (Normal (g',l',ls))) =  (g=g' \<and> l=l')"
  by (metis (full_types) SeqNormal)

lemma toSeq_diff:"(toSeq (Normal (g,l,ls)) \<noteq> toSeq (Normal (g',l',ls))) =  (g\<noteq>g' \<or> l\<noteq>l')"
  using toSeq_eq by auto
  
end *)
          (* and
          a4:"\<forall>i. i \<notin> id ` (localSet locs) \<longrightarrow> setLocal i locs loc = locs" and
          a5:"card (localSet locs) \<le> card (UNIV::'id set)" and
          a6:"\<forall>i. i \<notin> id ` (localSet locs) \<longrightarrow> getLocals locs i = None" and
          a7:"\<forall>id' id. id \<noteq> id' \<longrightarrow> getLocals (setLocal id locs loc) id' = getLocals locs id'" and
          a8:"\<forall>id1 id2. id1\<noteq>id2 \<and> id1 \<in> id ` (localSet locs) \<and> id2 \<in> id ` (localSet locs) \<longrightarrow> 
                       getLocals locs id1 \<noteq> getLocals locs id2" and
          a9:"\<forall>e1 e2. e1 \<in> (localSet locs) \<and> e2 \<in> (localSet locs) \<and> e1\<noteq>e2 \<longrightarrow> id e1 \<noteq> id e2" 
begin 


end
record g = x1::nat
record l = ids:: nat l1::nat

record gl = x1::nat ids::nat l1::nat
type_synonym ('l) ls = "'l list"

definition id1 ::"l \<Rightarrow> nat"
  where "id1 ml \<equiv> l.ids ml"

definition getLocal :: "gl \<Rightarrow> l"
  where "getLocal gls \<equiv> \<lparr>l.ids = gl.ids gls, l.l1 = gl.l1 gls\<rparr>"

definition getGlobal :: "gl \<Rightarrow> g"
  where "getGlobal gls \<equiv> \<lparr>g.x1 = gl.x1 gls\<rparr>"

definition toSeq :: "(g\<times>l) \<Rightarrow> gl"
  where "toSeq gls \<equiv> \<lparr>gl.x1 = (g.x1 (fst gls)), gl.ids = l.ids (snd gls), gl.l1 = l.l1 (snd gls)\<rparr>"

definition localSet ::"l ls \<Rightarrow> l set"
  where "localSet mlocs \<equiv> set mlocs"

definition getLocals ::"l ls \<Rightarrow> nat \<Rightarrow> l option"
  where "getLocals mlocs idn \<equiv> find (\<lambda>l. id1 l = idn) mlocs"

definition setLocal ::"nat \<Rightarrow> l ls \<Rightarrow> l \<Rightarrow> l ls"
  where "setLocal idn mlocs l \<equiv> if  find (\<lambda>l. id1 l = idn) mlocs = None then mlocs
                                else 
                                 let p = (SOME n. id1 (nth mlocs n) = idn) in
                                     mlocs[p:= l]"

interpretation localsvars getLocal getGlobal toSeq 
  apply (unfold_locales)
          apply (unfold getLocal_def toSeq_def getGlobal_def)
  by auto  
*) 

type_synonym ('s,'p,'f,'e) config = "('s,'p,'f,'e)com  \<times> ('s,'f) xstate"

inductive       
      "stepc"::"[('s,'p,'f,'e) body,('s,'p,'f,'e) config,('s,'p,'f,'e) config] \<Rightarrow> bool"
                                ("_\<turnstile>\<^sub>c (_ \<rightarrow>/ _)" [81,81,81] 100)  
  for \<Gamma>::"('s,'p,'f,'e) body"
where

  Basicc: "\<Gamma>\<turnstile>\<^sub>c(Basic f e,Normal s) \<rightarrow> (Skip,Normal (f s))"

| Specc: "(s,t) \<in> r \<Longrightarrow> \<Gamma>\<turnstile>\<^sub>c(Spec r e,Normal s) \<rightarrow> (Skip,Normal t)"
| SpecStuckc: "\<forall>t. (s,t) \<notin> r \<Longrightarrow> \<Gamma>\<turnstile>\<^sub>c(Spec r e,Normal s) \<rightarrow> (Skip,Stuck)"

| Guardc: "s\<in>g \<Longrightarrow> \<Gamma>\<turnstile>\<^sub>c(Guard f g c,Normal s) \<rightarrow> (c,Normal s)"
  
| GuardFaultc: "s\<notin>g \<Longrightarrow> \<Gamma>\<turnstile>\<^sub>c(Guard f g c,Normal s) \<rightarrow> (Skip,Fault f)"


| Seqc: "\<Gamma>\<turnstile>\<^sub>c(c\<^sub>1,s) \<rightarrow> (c\<^sub>1',s')
        \<Longrightarrow> 
        \<Gamma>\<turnstile>\<^sub>c(Seq c\<^sub>1 c\<^sub>2,s) \<rightarrow> (Seq c\<^sub>1' c\<^sub>2, s')"
| SeqSkipc: "\<Gamma>\<turnstile>\<^sub>c(Seq Skip c\<^sub>2,s) \<rightarrow> (c\<^sub>2, s)"
| SeqThrowc: "\<Gamma>\<turnstile>\<^sub>c(Seq Throw c\<^sub>2,Normal s) \<rightarrow> (Throw, Normal s)"

| CondTruec:  "s\<in>b \<Longrightarrow> \<Gamma>\<turnstile>\<^sub>c(Cond b c\<^sub>1 c\<^sub>2,Normal s) \<rightarrow> (c\<^sub>1,Normal s)"
| CondFalsec: "s\<notin>b \<Longrightarrow> \<Gamma>\<turnstile>\<^sub>c(Cond b c\<^sub>1 c\<^sub>2,Normal s) \<rightarrow> (c\<^sub>2,Normal s)"

| WhileTruec: "\<lbrakk>s\<in>b\<rbrakk> 
              \<Longrightarrow> 
              \<Gamma>\<turnstile>\<^sub>c(While b c,Normal s) \<rightarrow> (Seq c (While b c),Normal s)"

| WhileFalsec: "\<lbrakk>s\<notin>b\<rbrakk> 
               \<Longrightarrow> 
               \<Gamma>\<turnstile>\<^sub>c(While b c,Normal s) \<rightarrow> (Skip,Normal s)"


| Awaitc:  "\<lbrakk>s\<in>b; \<Gamma>1=\<Gamma>\<^sub>\<not>\<^sub>a ; \<Gamma>1\<turnstile>\<langle>ca1,Normal s\<rangle> \<Rightarrow> t; 
             \<not>(\<exists>t'. t = Abrupt t')\<rbrakk> \<Longrightarrow> 
            \<Gamma>\<turnstile>\<^sub>c(Await b ca1 e,Normal s) \<rightarrow> (Skip,t)"

| AwaitAbruptc: "\<lbrakk>s\<in>b; \<Gamma>1=\<Gamma>\<^sub>\<not>\<^sub>a ; \<Gamma>1\<turnstile>\<langle>ca1,Normal s\<rangle> \<Rightarrow> t; 
                  t = Abrupt t'\<rbrakk> \<Longrightarrow> 
                 \<Gamma>\<turnstile>\<^sub>c(Await b ca1 e,Normal s) \<rightarrow> (Throw,Normal t')"

| Callc: "\<lbrakk>\<Gamma> p = Some bdy ; bdy\<noteq>Call p\<rbrakk> \<Longrightarrow>
         \<Gamma>\<turnstile>\<^sub>c(Call p,Normal s) \<rightarrow> (bdy,Normal s)"

| CallUndefinedc: "\<Gamma> p=None \<Longrightarrow>
         \<Gamma>\<turnstile>\<^sub>c(Call p,Normal s) \<rightarrow> (Skip,Stuck)"

| DynComc: "\<Gamma>\<turnstile>\<^sub>c(DynCom c,Normal s) \<rightarrow> (c s,Normal s)"

| Catchc: "\<lbrakk>\<Gamma>\<turnstile>\<^sub>c(c\<^sub>1,s) \<rightarrow> (c\<^sub>1',s')\<rbrakk>
          \<Longrightarrow>
          \<Gamma>\<turnstile>\<^sub>c(Catch c\<^sub>1 c\<^sub>2,s) \<rightarrow> (Catch c\<^sub>1' c\<^sub>2,s')"

| CatchThrowc: "\<Gamma>\<turnstile>\<^sub>c(Catch Throw c\<^sub>2,Normal s) \<rightarrow> (c\<^sub>2,Normal s)"
| CatchSkipc: "\<Gamma>\<turnstile>\<^sub>c(Catch Skip c\<^sub>2,s) \<rightarrow> (Skip,s)"

| FaultPropc:  "\<lbrakk>c\<noteq>Skip; redex c = c\<rbrakk> \<Longrightarrow> \<Gamma>\<turnstile>\<^sub>c(c,Fault f) \<rightarrow> (Skip,Fault f)"
| StuckPropc:  "\<lbrakk>c\<noteq>Skip; redex c = c\<rbrakk> \<Longrightarrow> \<Gamma>\<turnstile>\<^sub>c(c,Stuck) \<rightarrow> (Skip,Stuck)"
| AbruptPropc: "\<lbrakk>c\<noteq>Skip; redex c = c\<rbrakk> \<Longrightarrow> \<Gamma>\<turnstile>\<^sub>c(c,Abrupt f) \<rightarrow> (Skip,Abrupt f)"
                                                              
lemmas stepc_induct = stepc.induct [of _ "(c,s)" "(c',s')", split_format (complete), case_names
Basicc Specc SpecStuckc Guardc GuardFaultc Seqc SeqSkipc SeqThrowc CondTruec CondFalsec
WhileTruec WhileFalsec Awaitc AwaitAbruptc Callc CallUndefinedc DynComc Catchc CatchThrowc CatchSkipc
FaultPropc StuckPropc AbruptPropc, induct set]

inductive_cases stepc_call_skip_normal:
 "\<Gamma>\<turnstile>\<^sub>c(Call p,Normal s) \<rightarrow> (Skip,s')"

inductive_cases stepc_elim_cases [cases set]:
 "\<Gamma>\<turnstile>\<^sub>c(Skip,s) \<rightarrow> u"
 "\<Gamma>\<turnstile>\<^sub>c(Guard f g c,s) \<rightarrow> u"
 "\<Gamma>\<turnstile>\<^sub>c(Basic f e,s) \<rightarrow> u"
 "\<Gamma>\<turnstile>\<^sub>c(Spec r e,s) \<rightarrow> u"
 "\<Gamma>\<turnstile>\<^sub>c(Seq c1 c2,s) \<rightarrow> u"
 "\<Gamma>\<turnstile>\<^sub>c(Cond b c1 c2,s) \<rightarrow> u"
 "\<Gamma>\<turnstile>\<^sub>c(While b c,s) \<rightarrow> u"
 "\<Gamma>\<turnstile>\<^sub>c(Await b c2 e,s) \<rightarrow> u"
 "\<Gamma>\<turnstile>\<^sub>c(Call p,s) \<rightarrow> u"
 "\<Gamma>\<turnstile>\<^sub>c(DynCom c,s) \<rightarrow> u"
 "\<Gamma>\<turnstile>\<^sub>c(Throw,s) \<rightarrow> u"
 "\<Gamma>\<turnstile>\<^sub>c(Catch c1 c2,s) \<rightarrow> u"

inductive_cases stepc_not_normal_elim_cases:
 "\<Gamma>\<turnstile>\<^sub>c(Call p,Abrupt s) \<rightarrow> (p',s')"
 "\<Gamma>\<turnstile>\<^sub>c(Call p, Fault f) \<rightarrow> (p',s')"
 "\<Gamma>\<turnstile>\<^sub>c(Call p, Stuck) \<rightarrow> (p',s')"
 

lemma Guardc_not_c:"Guard f g c \<noteq> c"
proof (induct c)
qed auto

lemma Catch_not_c1:"Catch c1 c2 \<noteq> c1"
proof (induct c1)
qed auto

lemma Catch_not_c:"Catch c1 c2 \<noteq> c2"
proof (induct c2)
qed auto

lemma seq_not_eq1: "Seq c1 c2\<noteq>c1"
  by (induct c1) auto

lemma seq_not_eq2: "Seq c1 c2\<noteq>c2"
  by (induct c2) auto

lemma if_not_eq1: "Cond b c1 c2 \<noteq>c1"
  by (induct c1) auto

lemma if_not_eq2: "Cond b c1 c2\<noteq>c2"
  by (induct c2) auto


lemmas seq_and_if_not_eq [simp] = seq_not_eq1 seq_not_eq2 
seq_not_eq1 [THEN not_sym] seq_not_eq2 [THEN not_sym] 
if_not_eq1 if_not_eq2 if_not_eq1 [THEN not_sym] if_not_eq2 [THEN not_sym]
Catch_not_c1 Catch_not_c Catch_not_c1 [THEN not_sym] Catch_not_c[THEN not_sym] 
Guardc_not_c Guardc_not_c[THEN not_sym]

inductive_cases stepc_elim_cases_Seq_Seq:
"\<Gamma>\<turnstile>\<^sub>c(Seq c1 c2,s) \<rightarrow> (Seq c1' c2,s')" 

inductive_cases stepc_elim_cases_Seq_Seq1:
"\<Gamma>\<turnstile>\<^sub>c(Seq c1 c2,Fault f) \<rightarrow> (q,s')" 

inductive_cases stepc_elim_cases_Catch_Catch:
"\<Gamma>\<turnstile>\<^sub>c(Catch c1 c2,s) \<rightarrow> (Catch c1' c2,s')" 

inductive_cases stepc_elim_cases_Catch_Catch1:
"\<Gamma>\<turnstile>\<^sub>c(Seq c1 c2,Fault f) \<rightarrow> (q,s')" 

inductive_cases stepc_elim_cases_Seq_skip:
"\<Gamma>\<turnstile>\<^sub>c(Seq Skip c2,s) \<rightarrow> u" 
"\<Gamma>\<turnstile>\<^sub>c(Seq (Guard f g c1) c2,s) \<rightarrow> u"


inductive_cases stepc_elim_cases_Catch_skip:
"\<Gamma>\<turnstile>\<^sub>c(Catch Skip c2,s) \<rightarrow> u"

inductive_cases stepc_elim_cases_Await_skip:
"\<Gamma>\<turnstile>\<^sub>c (Await b c e, Normal s) \<rightarrow> (Skip,t)"

inductive_cases stepc_elim_cases_Await_throw:
"\<Gamma>\<turnstile>\<^sub>c (Await b c e, Normal s) \<rightarrow> (Throw,t)"

inductive_cases stepc_elim_cases_Catch_throw:
"\<Gamma>\<turnstile>\<^sub>c(Catch c1 c2,s) \<rightarrow> (Throw, Normal s1)" 

inductive_cases stepc_elim_cases_Catch_skip_c2:
"\<Gamma>\<turnstile>\<^sub>c(Catch c1 c2,s) \<rightarrow> (c2,s)"

inductive_cases stepc_Normal_elim_cases [cases set]:
 "\<Gamma>\<turnstile>\<^sub>c(Skip,Normal s) \<rightarrow> u"
 "\<Gamma>\<turnstile>\<^sub>c(Guard f g c,Normal s) \<rightarrow> u"
 "\<Gamma>\<turnstile>\<^sub>c(Basic f e,Normal s) \<rightarrow> u"
 "\<Gamma>\<turnstile>\<^sub>c(Spec r e,Normal s) \<rightarrow> u"
 "\<Gamma>\<turnstile>\<^sub>c(Seq c1 c2,Normal s) \<rightarrow> u"
 "\<Gamma>\<turnstile>\<^sub>c(Cond b c1 c2,Normal s) \<rightarrow> u"
 "\<Gamma>\<turnstile>\<^sub>c(While b c,Normal s) \<rightarrow> u"
 "\<Gamma>\<turnstile>\<^sub>c(Await b c e,Normal s) \<rightarrow> u"
 "\<Gamma>\<turnstile>\<^sub>c(Call p,Normal s) \<rightarrow> u"
 "\<Gamma>\<turnstile>\<^sub>c(DynCom c,Normal s) \<rightarrow> u"
 "\<Gamma>\<turnstile>\<^sub>c(Throw,Normal s) \<rightarrow> u"
 "\<Gamma>\<turnstile>\<^sub>c(Catch c1 c2,Normal s) \<rightarrow> u"


text \<open> The final configuration is either of the form @{text "(Skip,_)"} for normal
termination, or @{term "(Throw,Normal s)"} in case the program was started in 
a @{term "Normal"} state and terminated abruptly. The @{const "Abrupt"} state is not used to
model abrupt termination, in contrast to the big-step semantics. Only if the
program starts in an @{const "Abrupt"} states it ends in the same @{term "Abrupt"}
state.\<close>

definition final:: "('s,'p,'f,'e) config \<Rightarrow> bool" where
"final cfg \<equiv> (fst cfg=Skip \<or> ((fst cfg=Throw) \<and> (\<exists>s. snd cfg=Normal s)))"

definition final_valid::"('s,'p,'f,'e) config \<Rightarrow> bool" where
"final_valid cfg = ((fst cfg=Skip \<or> fst cfg=Throw) \<and> (\<exists>s. snd cfg=Normal s))"

abbreviation 
 "stepc_rtrancl" :: "[('s,'p,'f,'e) body,('s,'p,'f,'e) config,('s,'p,'f,'e) config] \<Rightarrow> bool"
                                ("_\<turnstile>\<^sub>c (_ \<rightarrow>\<^sup>*/ _)" [81,81,81] 100)
 where                                
  "\<Gamma>\<turnstile>\<^sub>c cf0 \<rightarrow>\<^sup>* cf1 \<equiv> ((CONST stepc \<Gamma>))\<^sup>*\<^sup>* cf0 cf1" 
  (* "\<Gamma>\<turnstile>\<^sub>c cf0 \<rightarrow>\<^sup>* cf1 \<equiv> (CONST ((stepc \<Gamma>) \<union> (step_e \<Gamma>)))\<^sup>*\<^sup>* cf0 cf1" *)

abbreviation 
 "stepc_trancl" :: "[('s,'p,'f,'e) body,('s,'p,'f,'e) config,('s,'p,'f,'e) config] \<Rightarrow> bool"
                                ("_\<turnstile>\<^sub>c (_ \<rightarrow>\<^sup>+/ _)" [81,81,81] 100)
 where
  "\<Gamma>\<turnstile>\<^sub>c cf0 \<rightarrow>\<^sup>+ cf1 \<equiv> (CONST stepc \<Gamma>)\<^sup>+\<^sup>+ cf0 cf1"

lemma 
   assumes step_a: "\<Gamma>\<turnstile>\<^sub>c(Await b c e, Normal s) \<rightarrow> (t,u)"
   shows step_await_step_c:"(\<Gamma>\<^sub>\<not>\<^sub>a)\<turnstile>(c, Normal s) \<rightarrow>\<^sup>* (sequential t,u)" 
using step_a
proof cases
  fix t1
  assume
      "(t, u) = (Skip, t1)" "s \<in> b" "(\<Gamma>\<^sub>\<not>\<^sub>a)\<turnstile> \<langle>c,Normal s\<rangle> \<Rightarrow> t1" "\<forall>t'. t1 \<noteq> Abrupt t'"
  thus ?thesis 
   by (cases u) 
   (auto intro: exec_impl_steps_Fault exec_impl_steps_Normal exec_impl_steps_Stuck)
next
  fix t1
  assume "(t, u) = (Throw, Normal t1)" "s \<in> b" "(\<Gamma>\<^sub>\<not>\<^sub>a)\<turnstile> \<langle>c,Normal s\<rangle> \<Rightarrow> Abrupt t1"
  thus ?thesis by (simp add: exec_impl_steps_Normal_Abrupt)
qed

lemma 
   assumes (* exec: "\<Gamma>\<turnstile>\<langle>c,Normal s\<rangle> \<Rightarrow> t" and
           b: "s \<in> b" and *)
           step_a: "\<Gamma>\<turnstile>\<^sub>c(Await b c e, Normal s) \<rightarrow> u"
   shows step_await_final1:"final u"
using step_a 
proof cases
  case  (1 t) thus "final u"  by (simp add: final_def)
next
  case (2 t)
  thus "final u" by (simp add: exec_impl_steps_Normal_Abrupt final_def)
qed

lemma step_Abrupt_end: 
  assumes step: "\<Gamma>\<turnstile>\<^sub>c (c\<^sub>1, s) \<rightarrow> (c\<^sub>1', s')"
  shows "s'=Abrupt x \<Longrightarrow> s=Abrupt x"
using step      
  by induct auto

lemma step_not_abrupt_end:
  assumes step: "\<Gamma>\<turnstile>\<^sub>c (c\<^sub>1, s) \<rightarrow> (c\<^sub>1', s')" and 
         not_abr:"\<forall>s'. s\<noteq>Abrupt s'" and 
         abr:"\<exists>s. s' = Abrupt s"
  shows "P"
using step not_abr abr
by induct auto

lemma step_Stuck_end: 
  assumes step: "\<Gamma>\<turnstile>\<^sub>c (c\<^sub>1, s) \<rightarrow> (c\<^sub>1', s')"
  shows "s'=Stuck \<Longrightarrow> 
          s=Stuck \<or> 
          (\<exists>r x e. redex c\<^sub>1 = Spec r e \<and> s=Normal x \<and> (\<forall>t. (x,t)\<notin>r)) \<or> 
          (\<exists>p x. redex c\<^sub>1=  Call p \<and> s=Normal x \<and> \<Gamma> p = None) \<or>
          (\<exists>b c x e.  redex c\<^sub>1 = Await b c e \<and> s=Normal x \<and> x \<in> b \<and> (\<Gamma>\<^sub>\<not>\<^sub>a)\<turnstile>\<langle>c,s\<rangle>\<Rightarrow>s')"
using step
by induct auto

lemma step_Fault_end: 
  assumes step: "\<Gamma>\<turnstile>\<^sub>c (c\<^sub>1, s) \<rightarrow> (c\<^sub>1', s')"
  shows "s'=Fault f \<Longrightarrow> 
          s=Fault f \<or> 
          (\<exists>g c x.  redex c\<^sub>1 = Guard f g c \<and> s=Normal x \<and> x \<notin> g) \<or>
          (\<exists>b c1 x e.  redex c\<^sub>1 = Await b c1 e \<and> s=Normal x \<and> x \<in> b \<and> (\<Gamma>\<^sub>\<not>\<^sub>a)\<turnstile>\<langle>c1,s\<rangle>\<Rightarrow>s')"
using step 
by induct auto

lemma step_not_Fault_f_end:
  assumes step: "\<Gamma>\<turnstile>\<^sub>c (c\<^sub>1, s) \<rightarrow> (c\<^sub>1', s')"
  shows "s'\<notin> Fault ` f \<Longrightarrow> s \<notin> Fault ` f"
using step 
  by induct auto

(* ************************************************************************ *)
subsection {* Structural Properties of Small Step Computations *}
(* ************************************************************************ *)
lemma redex_not_Seq: "redex c = Seq c1 c2 \<Longrightarrow> P"
  apply (induct c)
  apply auto
  done
lemma redex_not_Catch: "redex c = Catch c1 c2 \<Longrightarrow> P"
  apply (induct c)
  apply auto
  done

lemma no_step_final: 
  assumes step: "\<Gamma>\<turnstile>\<^sub>c(c,s) \<rightarrow> (c',s')"
  shows "final (c,s) \<Longrightarrow> P"
using step
by induct (auto simp add: final_def)


lemma no_step_final':
  assumes step: "\<Gamma>\<turnstile>\<^sub>c cfg \<rightarrow> cfg'"
  shows "final cfg \<Longrightarrow> P"
using step
  by (cases cfg, cases cfg') (auto intro: no_step_final)


lemma step_Abrupt:
  assumes step: "\<Gamma>\<turnstile>\<^sub>c (c, s) \<rightarrow> (c', s')"
  shows "\<And>x. s=Abrupt x \<Longrightarrow> s'=Abrupt x"
using step
by (induct) auto

lemma step_Fault: 
  assumes step: "\<Gamma>\<turnstile>\<^sub>c (c, s) \<rightarrow> (c', s')"
  shows "\<And>f. s=Fault f \<Longrightarrow> s'=Fault f"
using step
by (induct) auto

lemma step_Stuck: 
  assumes step: "\<Gamma>\<turnstile>\<^sub>c (c, s) \<rightarrow> (c', s')"
  shows "\<And>f. s=Stuck \<Longrightarrow> s'=Stuck"
using step
by (induct) auto

lemma step_not_normal_not_normal:
  assumes step:"\<Gamma>\<turnstile>\<^sub>c (c, s) \<rightarrow> (c', s')"
  shows "\<forall>s1. s\<noteq>Normal s1 \<Longrightarrow> \<forall>s1. s' \<noteq> Normal s1"
using step step_Abrupt step_Stuck step_Fault
by (induct) auto

lemma step_not_normal_s_eq_t:
  assumes step:"\<Gamma>\<turnstile>\<^sub>c (c, s) \<rightarrow> (c', t)"
  shows "\<forall>s1. s\<noteq>Normal s1 \<Longrightarrow> s=t"
using step step_Abrupt step_Stuck step_Fault
by (induct) auto

lemma SeqSteps: 
  assumes steps: "\<Gamma>\<turnstile>\<^sub>c cfg\<^sub>1\<rightarrow>\<^sup>* cfg\<^sub>2"
  shows "\<And> c\<^sub>1 s c\<^sub>1' s'. \<lbrakk>cfg\<^sub>1 = (c\<^sub>1,s);cfg\<^sub>2=(c\<^sub>1',s')\<rbrakk>
          \<Longrightarrow> \<Gamma>\<turnstile>\<^sub>c(Seq c\<^sub>1 c\<^sub>2,s) \<rightarrow>\<^sup>* (Seq c\<^sub>1' c\<^sub>2, s')"
using steps
proof (induct rule: converse_rtranclp_induct [case_names Refl Trans]) 
  case Refl
  thus ?case
    by simp
next
  case (Trans cfg\<^sub>1 cfg'')      
  have step: "\<Gamma>\<turnstile>\<^sub>c cfg\<^sub>1 \<rightarrow> cfg''" using Trans.hyps(1) by blast
  have steps: "\<Gamma>\<turnstile>\<^sub>c cfg'' \<rightarrow>\<^sup>* cfg\<^sub>2" by fact
  have cfg\<^sub>1: "cfg\<^sub>1 = (c\<^sub>1, s)" and cfg\<^sub>2: "cfg\<^sub>2 = (c\<^sub>1', s')"  by fact+
  obtain c\<^sub>1'' s'' where cfg'': "cfg''=(c\<^sub>1'',s'')"
    by (cases cfg'') auto
  from step cfg\<^sub>1 cfg'' 
  have "\<Gamma>\<turnstile>\<^sub>c (c\<^sub>1,s) \<rightarrow> (c\<^sub>1'',s'')"
    by simp  
  hence "\<Gamma>\<turnstile>\<^sub>c (Seq c\<^sub>1 c\<^sub>2,s) \<rightarrow> (Seq c\<^sub>1'' c\<^sub>2,s'')" by (simp add: Seqc)    
  also from Trans.hyps (3) [OF cfg'' cfg\<^sub>2]
  have "\<Gamma>\<turnstile>\<^sub>c (Seq c\<^sub>1'' c\<^sub>2, s'') \<rightarrow>\<^sup>* (Seq c\<^sub>1' c\<^sub>2, s')" .
  finally show ?case .
qed

lemma CatchSteps: 
  assumes steps: "\<Gamma>\<turnstile>\<^sub>ccfg\<^sub>1\<rightarrow>\<^sup>* cfg\<^sub>2"
  shows "\<And> c\<^sub>1 s c\<^sub>1' s'. \<lbrakk>cfg\<^sub>1 = (c\<^sub>1,s); cfg\<^sub>2=(c\<^sub>1',s')\<rbrakk>
          \<Longrightarrow> \<Gamma>\<turnstile>\<^sub>c(Catch c\<^sub>1 c\<^sub>2,s) \<rightarrow>\<^sup>* (Catch c\<^sub>1' c\<^sub>2, s')"
using steps
proof (induct rule: converse_rtranclp_induct [case_names Refl Trans])
  case Refl
  thus ?case
    by simp
next
  case (Trans cfg\<^sub>1 cfg'')
  have step: "\<Gamma>\<turnstile>\<^sub>c cfg\<^sub>1 \<rightarrow> cfg''" by fact
  have steps: "\<Gamma>\<turnstile>\<^sub>c cfg'' \<rightarrow>\<^sup>* cfg\<^sub>2" by fact
  have cfg\<^sub>1: "cfg\<^sub>1 = (c\<^sub>1, s)" and cfg\<^sub>2: "cfg\<^sub>2 = (c\<^sub>1', s')"  by fact+
  obtain c\<^sub>1'' s'' where cfg'': "cfg''=(c\<^sub>1'',s'')"
    by (cases cfg'') auto
  from step cfg\<^sub>1 cfg'' 
  have s: "\<Gamma>\<turnstile>\<^sub>c (c\<^sub>1,s) \<rightarrow> (c\<^sub>1'',s'')"
    by simp
  hence "\<Gamma>\<turnstile>\<^sub>c (Catch c\<^sub>1 c\<^sub>2,s) \<rightarrow> (Catch c\<^sub>1'' c\<^sub>2,s'')"
    by (rule stepc.Catchc)
  also from Trans.hyps (3) [OF cfg'' cfg\<^sub>2]
  have "\<Gamma>\<turnstile>\<^sub>c (Catch c\<^sub>1'' c\<^sub>2, s'') \<rightarrow>\<^sup>* (Catch c\<^sub>1' c\<^sub>2, s')" .
  finally show ?case .      
qed

lemma steps_Fault: "\<Gamma>\<turnstile>\<^sub>c (c, Fault f) \<rightarrow>\<^sup>* (Skip, Fault f)"
proof (induct c)
  case (Seq c\<^sub>1 c\<^sub>2)
  have steps_c\<^sub>1: "\<Gamma>\<turnstile>\<^sub>c (c\<^sub>1, Fault f) \<rightarrow>\<^sup>* (Skip, Fault f)" by fact
  have steps_c\<^sub>2: "\<Gamma>\<turnstile>\<^sub>c (c\<^sub>2, Fault f) \<rightarrow>\<^sup>* (Skip, Fault f)" by fact
  from SeqSteps [OF steps_c\<^sub>1 refl refl]
  have "\<Gamma>\<turnstile>\<^sub>c (Seq c\<^sub>1 c\<^sub>2, Fault f) \<rightarrow>\<^sup>* (Seq Skip c\<^sub>2, Fault f)".
  also
  have "\<Gamma>\<turnstile>\<^sub>c (Seq Skip c\<^sub>2, Fault f) \<rightarrow> (c\<^sub>2, Fault f)" by (rule SeqSkipc)
  also note steps_c\<^sub>2
  finally show ?case by simp
next
  case (Catch c\<^sub>1 c\<^sub>2)
  have steps_c\<^sub>1: "\<Gamma>\<turnstile>\<^sub>c (c\<^sub>1, Fault f) \<rightarrow>\<^sup>* (Skip, Fault f)" by fact
  from CatchSteps [OF steps_c\<^sub>1 refl refl]
  have "\<Gamma>\<turnstile>\<^sub>c (Catch c\<^sub>1 c\<^sub>2, Fault f) \<rightarrow>\<^sup>* (Catch Skip c\<^sub>2, Fault f)".
  also
  have "\<Gamma>\<turnstile>\<^sub>c (Catch Skip c\<^sub>2, Fault f) \<rightarrow> (Skip, Fault f)" by (rule CatchSkipc) 
  finally show ?case by simp
qed (fastforce intro: stepc.intros)+


lemma steps_Stuck: "\<Gamma>\<turnstile>\<^sub>c (c, Stuck) \<rightarrow>\<^sup>* (Skip, Stuck)"
proof (induct c)
  case (Seq c\<^sub>1 c\<^sub>2)
  have steps_c\<^sub>1: "\<Gamma>\<turnstile>\<^sub>c (c\<^sub>1, Stuck) \<rightarrow>\<^sup>* (Skip, Stuck)" by fact
  have steps_c\<^sub>2: "\<Gamma>\<turnstile>\<^sub>c (c\<^sub>2, Stuck) \<rightarrow>\<^sup>* (Skip, Stuck)" by fact
  from SeqSteps [OF steps_c\<^sub>1 refl refl]
  have "\<Gamma>\<turnstile>\<^sub>c (Seq c\<^sub>1 c\<^sub>2, Stuck) \<rightarrow>\<^sup>* (Seq Skip c\<^sub>2, Stuck)".
  also
  have "\<Gamma>\<turnstile>\<^sub>c (Seq Skip c\<^sub>2, Stuck) \<rightarrow> (c\<^sub>2, Stuck)" by (rule SeqSkipc)
  also note steps_c\<^sub>2
  finally show ?case by simp
next
  case (Catch c\<^sub>1 c\<^sub>2)
  have steps_c\<^sub>1: "\<Gamma>\<turnstile>\<^sub>c (c\<^sub>1, Stuck) \<rightarrow>\<^sup>* (Skip, Stuck)" by fact
  from CatchSteps [OF steps_c\<^sub>1 refl refl]
  have "\<Gamma>\<turnstile>\<^sub>c (Catch c\<^sub>1 c\<^sub>2, Stuck) \<rightarrow>\<^sup>* (Catch Skip c\<^sub>2, Stuck)" .
  also
  have "\<Gamma>\<turnstile>\<^sub>c (Catch Skip c\<^sub>2, Stuck) \<rightarrow> (Skip, Stuck)" by (rule CatchSkipc) 
  finally show ?case by simp
qed (fastforce intro: stepc.intros)+

lemma steps_Abrupt: "\<Gamma>\<turnstile>\<^sub>c (c, Abrupt s) \<rightarrow>\<^sup>* (Skip, Abrupt s)"
proof (induct c)
  case (Seq c\<^sub>1 c\<^sub>2)
  have steps_c\<^sub>1: "\<Gamma>\<turnstile>\<^sub>c (c\<^sub>1, Abrupt s) \<rightarrow>\<^sup>* (Skip, Abrupt s)" by fact
  have steps_c\<^sub>2: "\<Gamma>\<turnstile>\<^sub>c (c\<^sub>2, Abrupt s) \<rightarrow>\<^sup>* (Skip, Abrupt s)" by fact
  from SeqSteps [OF steps_c\<^sub>1 refl refl]
  have "\<Gamma>\<turnstile>\<^sub>c (Seq c\<^sub>1 c\<^sub>2, Abrupt s) \<rightarrow>\<^sup>* (Seq Skip c\<^sub>2, Abrupt s)".
  also
  have "\<Gamma>\<turnstile>\<^sub>c (Seq Skip c\<^sub>2, Abrupt s) \<rightarrow> (c\<^sub>2, Abrupt s)" by (rule SeqSkipc)
  also note steps_c\<^sub>2
  finally show ?case by simp
next
  case (Catch c\<^sub>1 c\<^sub>2)
  have steps_c\<^sub>1: "\<Gamma>\<turnstile>\<^sub>c (c\<^sub>1, Abrupt s) \<rightarrow>\<^sup>* (Skip, Abrupt s)" by fact
  from CatchSteps [OF steps_c\<^sub>1 refl refl]
  have "\<Gamma>\<turnstile>\<^sub>c (Catch c\<^sub>1 c\<^sub>2, Abrupt s) \<rightarrow>\<^sup>* (Catch Skip c\<^sub>2, Abrupt s)".
  also
  have "\<Gamma>\<turnstile>\<^sub>c (Catch Skip c\<^sub>2, Abrupt s) \<rightarrow> (Skip, Abrupt s)" by (rule CatchSkipc) 
  finally show ?case by simp
qed (fastforce intro: stepc.intros)+

lemma step_Fault_prop: 
  assumes step: "\<Gamma>\<turnstile>\<^sub>c (c, s) \<rightarrow> (c', s')"
  shows "\<And>f. s=Fault f \<Longrightarrow> s'=Fault f"
using step
by (induct) auto

lemma step_Abrupt_prop: 
  assumes step: "\<Gamma>\<turnstile>\<^sub>c (c, s) \<rightarrow> (c', s')"
  shows "\<And>x. s=Abrupt x \<Longrightarrow> s'=Abrupt x"
using step
by (induct) auto

lemma step_Stuck_prop: 
  assumes step: "\<Gamma>\<turnstile>\<^sub>c (c, s) \<rightarrow> (c', s')"
  shows "s=Stuck \<Longrightarrow> s'=Stuck"
using step
by (induct) auto

lemma steps_Fault_prop: 
  assumes step: "\<Gamma>\<turnstile>\<^sub>c (c, s) \<rightarrow>\<^sup>* (c', s')"
  shows "s=Fault f \<Longrightarrow> s'=Fault f"
using step
proof (induct rule: converse_rtranclp_induct2 [case_names Refl Trans])
  case Refl thus ?case by simp
next
  case (Trans c s c'' s'')
  thus ?case by (simp add: step_Fault_prop)    
qed

lemma steps_Abrupt_prop: 
  assumes step: "\<Gamma>\<turnstile>\<^sub>c (c, s) \<rightarrow>\<^sup>* (c', s')"
  shows "s=Abrupt t \<Longrightarrow> s'=Abrupt t"
using step
proof (induct rule: converse_rtranclp_induct2 [case_names Refl Trans])
  case Refl thus ?case by simp
next
  case (Trans c s c'' s'')
  thus ?case
    by (auto intro: step_Abrupt_prop)
qed

lemma steps_Stuck_prop: 
  assumes step: "\<Gamma>\<turnstile>\<^sub>c (c, s) \<rightarrow>\<^sup>* (c', s')"
  shows "s=Stuck \<Longrightarrow> s'=Stuck"
using step
proof (induct rule: converse_rtranclp_induct2 [case_names Refl Trans])
  case Refl thus ?case by simp   
next
  case (Trans c s c'' s'')
  thus ?case
    by (auto intro: step_Stuck_prop)
qed

lemma step_seq_throw_normal:
assumes step: "\<Gamma>\<turnstile>\<^sub>c (c, s) \<rightarrow> (c', s')" and
        c_val: "c=Seq Throw Q \<and> c'=Throw"
shows "\<exists>sa. s=Normal sa"
using step c_val
proof (cases s)
  case Normal 
  thus "\<exists>sa. s=Normal sa" by auto
next
  case Abrupt
  thus "\<exists>sa. s=Normal sa" using step c_val stepc_elim_cases(5)[of \<Gamma> Throw Q s "(Throw,s')"] by auto 
next 
  case Stuck
  thus "\<exists>sa. s=Normal sa" using step c_val stepc_elim_cases(5)[of \<Gamma> Throw Q s "(Throw,s')"] by auto
next
  case Fault
    thus "\<exists>sa. s=Normal sa" using step c_val stepc_elim_cases(5)[of \<Gamma> Throw Q s "(Throw,s')"] by auto
qed


lemma step_catch_throw_normal:
assumes step: "\<Gamma>\<turnstile>\<^sub>c (c, s) \<rightarrow> (c', s')" and
        c_val: "c=Catch Throw Q \<and> c'=Throw"
shows "\<exists>sa. s=Normal sa"
using step c_val
proof (cases s)
  case Normal 
  thus "\<exists>sa. s=Normal sa" by auto
next
  case Abrupt
  thus "\<exists>sa. s=Normal sa" using step c_val stepc_elim_cases(12)[of \<Gamma> Throw Q s "(Throw,s')"] by auto 
next 
  case Stuck
  thus "\<exists>sa. s=Normal sa" using step c_val stepc_elim_cases(12)[of \<Gamma> Throw Q s "(Throw,s')"] by auto
next
  case Fault
    thus "\<exists>sa. s=Normal sa" using step c_val stepc_elim_cases(12)[of \<Gamma> Throw Q s "(Throw,s')"] by auto
qed

lemma step_normal_to_normal[rule_format]:
assumes step:"\<Gamma>\<turnstile>\<^sub>c (c, s) \<rightarrow>\<^sup>* (c', s')" and
        sn: "s = Normal sa" and
        finalc':"(\<Gamma>\<turnstile>\<^sub>c (c', s') \<rightarrow>\<^sup>*(c1, s1) \<and>  (\<exists>sb. s1 = Normal sb))"
shows " (\<exists>sc. s'=Normal sc)"
using step sn finalc'                                  
 proof (induct arbitrary: sa rule: converse_rtranclp_induct2 [case_names Refl Trans])
   case Refl show ?case by (simp add: Refl.prems)              
 next     
   case (Trans c s c'' s'') thm converse_rtranclpE2 
     thus ?case
     proof (cases s'')  
      case (Abrupt a1) thus ?thesis using finalc' by (metis steps_Abrupt_prop Trans.hyps(2))                
     next
      case Stuck thus ?thesis using finalc' by (metis steps_Stuck_prop Trans.hyps(2))          
     next
      case Fault thus ?thesis using finalc' by (metis steps_Fault_prop Trans.hyps(2))        
     next 
      case Normal thus ?thesis using Trans.hyps(3) finalc' by blast 
    qed 
qed

lemma step_spec_skip_normal_normal:
  assumes a0:"\<Gamma>\<turnstile>\<^sub>c (c,s)  \<rightarrow> (c',s')" and
          a1:"c=Spec r e" and
          a2: "s=Normal s1" and
          a3: "c'=Skip" and
          a4: "(\<exists>t. (s1,t) \<in> r)"
  shows "\<exists>s1'. s'=Normal s1'"
proof (cases s')  
  case (Normal u) thus ?thesis by auto
next
  case Stuck 
    have "\<forall>f r b p e. \<not> f\<turnstile>\<^sub>c (LanguageCon.com.Spec r e, Normal b) \<rightarrow> p \<or> 
            (\<exists>ba. p = (Skip::('b, 'a, 'c,'d) com, Normal ba) \<and> (b, ba) \<in> r) \<or> 
            p = (Skip, Stuck) \<and> (\<forall>ba. (b, ba) \<notin> r)"
      by (meson stepc_Normal_elim_cases(4))
      thus ?thesis using a0 a1 a2 a4 by blast
next
  case (Fault f) 
  have "\<forall>f r b p e. \<not> f\<turnstile>\<^sub>c (LanguageCon.com.Spec r e, Normal b) \<rightarrow> p \<or> 
            (\<exists>ba. p = (Skip::('b, 'a, 'c,'d) com, Normal ba) \<and> (b, ba) \<in> r) \<or> 
            p = (Skip, Stuck) \<and> (\<forall>ba. (b, ba) \<notin> r)"
    by (meson stepc_Normal_elim_cases(4))
    thus ?thesis using a0 a1 a2 a4 by blast                       
next
  have "\<forall>f r b p e. \<not> f\<turnstile>\<^sub>c (LanguageCon.com.Spec r e, Normal b) \<rightarrow> p \<or> 
        (\<exists>ba. p = (Skip::('b, 'a, 'c,'d) com, Normal ba) \<and> (b, ba) \<in> r) \<or> 
        p = (Skip, Stuck) \<and> (\<forall>ba. (b, ba) \<notin> r)"
    by (meson stepc_Normal_elim_cases(4))
    thus ?thesis using a0 a1 a2 a4 by blast
qed


text{* if not Normal not environmental *}

(* 

NOTE
Call always change the program now 

lemma no_advance_call_inf:
assumes a0: "redex p1 = Call f" and
        a1: "(\<Gamma> f) = Some (Call f)" 
shows "\<Gamma>\<turnstile>\<^sub>c (p1,Normal s) \<rightarrow> (p1, Normal s)"
using a0 a1
proof (induct p1)
  case (Catch) thus ?case by (simp add: Catchc)
next
  case (Seq) thus ?case by (simp add: Seqc)
next
  case (Call) thus ?case
    by (simp add: Callc) 
qed(auto) *)

lemma no_advance_seq:
assumes a0: "P = Seq p1 p2" and
        a1: "\<Gamma>\<turnstile>\<^sub>c (p1,Normal s) \<rightarrow> (p1, Normal s)"
shows "\<Gamma>\<turnstile>\<^sub>c (P,Normal s) \<rightarrow> (P, Normal s)"
by (simp add: Seqc a0 a1)

lemma no_advance_catch:
assumes a0: "P = Catch p1 p2" and
        a1: "\<Gamma>\<turnstile>\<^sub>c (p1,Normal s) \<rightarrow> (p1, Normal s)"
shows "\<Gamma>\<turnstile>\<^sub>c (P,Normal s) \<rightarrow> (P, Normal s)"
by (simp add: Catchc a0 a1)

lemma call_not_normal_skip_always:
  assumes a0:"\<Gamma>\<turnstile>\<^sub>c(Call p,s) \<rightarrow> (p1,s1)" and
          a1:"\<forall>sn. s \<noteq> Normal sn" and
          a2:"p1\<noteq>Skip"
  shows "P" 
proof(cases s)
  case Normal thus ?thesis using a1 by fastforce
next
  case Stuck 
  then have a0:"\<Gamma>\<turnstile>\<^sub>c(Call p,Stuck) \<rightarrow> (p1,s1)" using a0 by auto
  show ?thesis using  a1 a2 stepc_not_normal_elim_cases(3)[OF a0] by fastforce
next
  case (Fault f) 
  then have a0:"\<Gamma>\<turnstile>\<^sub>c(Call p,Fault f) \<rightarrow> (p1,s1)" using a0 by auto
  show ?thesis using  a1 a2 stepc_not_normal_elim_cases(2)[OF a0] by fastforce
next
  case (Abrupt a)
  then have a0:"\<Gamma>\<turnstile>\<^sub>c(Call p,Abrupt a) \<rightarrow> (p1,s1)" using a0 by auto
  show ?thesis using  a1 a2 stepc_not_normal_elim_cases(1)[OF a0] by fastforce
qed

lemma call_f_step_not_s_eq_t_false:
  assumes 
     a0:"\<Gamma>\<turnstile>\<^sub>c(P,s) \<rightarrow> (Q,t)" and
     a1:"(redex P = Call fn \<and> \<Gamma> fn = Some bdy \<and> s=Normal s' \<and> ~(s=t)) \<or>
         (redex P = Call fn \<and> \<Gamma> fn = Some bdy \<and> s=Normal s' \<and> s=t \<and> P=Q \<and> \<Gamma> fn \<noteq> Some (Call fn))"
  shows "False"
using a0 a1
proof (induct rule:stepc_induct)
qed(fastforce+,auto)

lemma step_change_p_or_eq_Ns: 
    assumes step: "\<Gamma>\<turnstile>\<^sub>c (P,Normal s) \<rightarrow> (Q,s')"
    shows  "\<not>(P=Q)"
using step
proof (induct P arbitrary: Q s s')
qed(fastforce elim: stepc_Normal_elim_cases)+

 
lemma step_change_p_or_eq_s: 
    assumes step: "\<Gamma>\<turnstile>\<^sub>c (P,s) \<rightarrow> (Q,s')"
    shows  "\<not>(P=Q)"
using step
proof (induct P arbitrary: Q s s')
qed (fastforce elim: stepc_elim_cases)+

subsection \<open>Lemmas on normalization\<close>

(* lemma step_sequence_flatten:
  assumes exec: "\<Gamma>\<turnstile>\<^sub>c(P,s) \<rightarrow> (Q,t)" 
  shows "\<Gamma>\<turnstile>\<^sub>c(sequence Seq (flatten P),s) \<rightarrow> (sequence Seq (flatten Q),t)"
using exec
proof (induct rule: stepc_induct)
  case (Guardc s g f c) thus ?case using stepc.Guardc
  case (Seqc c1 s c2 s' c2')
  then have " \<Gamma>\<turnstile>\<^sub>c (Seq (LanguageCon.sequence LanguageCon.com.Seq (LanguageCon.flatten c1)) c2', s) \<rightarrow>
                   (Seq (LanguageCon.sequence LanguageCon.com.Seq (LanguageCon.flatten c2)) c2', s') " 
    using stepc.Seqc by fastforce    
  thus ?case sorry
qed(auto intro:stepc.intros)+

lemma normalice_step:
  assumes exec:"\<Gamma>\<turnstile>\<^sub>c(P,s) \<rightarrow> (Q,t)" 
  shows  "\<Gamma>\<turnstile>\<^sub>c( normalizec P,s) \<rightarrow> (normalizec Q,t)"
using exec
proof(induct rule:stepc_induct)
  case (Catchc P s Q t c2)
    thus ?case
   *) 
(* qed(auto intro: stepc.intros) *)


lemma mod_env_not_component:
shows    "\<not> \<Gamma>\<turnstile>\<^sub>c (P, s) \<rightarrow> (P, t)"
proof 
  assume a3:"\<Gamma>\<turnstile>\<^sub>c (P, s) \<rightarrow> (P, t)"           
  thus  False using step_change_p_or_eq_s a3 by fastforce
qed

lemma redex_not_call_seq_catch:
 assumes a0:"redex P = Call f \<and> P\<noteq>Call f"          
 shows "\<exists>p1 p2. P = Seq p1 p2 \<or> P = Catch p1 p2"
using a0 
proof(induct P)
qed(fastforce+)


lemma three_elems_list:
  assumes a1:"length l > 2"
  shows "\<exists>a0 a1 a2 l1. l=a0#a1#a2#l1"
using a1 by (metis Cons_nth_drop_Suc One_nat_def Suc_1 Suc_leI add_lessD1 drop_0 length_greater_0_conv list.size(3) not_numeral_le_zero one_add_one)  


lemma last_length: "((a#xs)!(length xs))=last (a#xs)"
  by (induct xs) auto

lemma list_eq_if [rule_format]: 
  "\<forall>ys. xs=ys \<longrightarrow> (length xs = length ys) \<longrightarrow> (\<forall>i<length xs. xs!i=ys!i)"
  by (induct xs) auto



lemma list_eq: "(length xs = length ys \<and> (\<forall>i<length xs. xs!i=ys!i)) = (xs=ys)"
apply(rule iffI)
 apply clarify
 apply(erule nth_equalityI)
 apply simp+
done

lemma nth_tl: "\<lbrakk> ys!0=a; ys\<noteq>[] \<rbrakk> \<Longrightarrow> ys=(a#(tl ys))"
  by (cases ys) simp_all

lemma nth_tl_if [rule_format]: "ys\<noteq>[] \<longrightarrow> ys!0=a \<longrightarrow> P ys \<longrightarrow> P (a#(tl ys))"
  by (induct ys) simp_all

lemma nth_tl_onlyif [rule_format]: "ys\<noteq>[] \<longrightarrow> ys!0=a \<longrightarrow> P (a#(tl ys)) \<longrightarrow> P ys"
  by (induct ys) simp_all

lemma nth_tl_eq [rule_format]: "ys\<noteq>[] \<longrightarrow> ys!0=a \<longrightarrow> P (a#(tl ys)) = P ys"
  by (induct ys) simp_all

lemma nth_tl_pair: "\<lbrakk>p=(u,ys); ys!0=a; ys\<noteq>[] \<rbrakk> \<Longrightarrow> p=(u,(a#(tl ys)))"
by (simp add: SmallStepCon.nth_tl)

lemma nth_tl_eq_Pair [rule_format]: "p=(u,ys) \<longrightarrow> ys\<noteq>[] \<longrightarrow> ys!0=a \<longrightarrow> P ((u,a#(tl ys))) = P (u,ys)"
  by (induct ys) simp_all

lemma tl_zero[rule_format]: 
  " Suc j<length ys \<longrightarrow> P (ys!Suc j) \<longrightarrow> P (tl(ys)!j)"
  by (simp add: List.nth_tl)

lemma tl_zero1[rule_format]:
  "Suc j<length ys \<longrightarrow>P (tl(ys)!j) \<longrightarrow>P (ys!Suc j)"
 by (simp add: List.nth_tl)

lemma tl_zero_eq [rule_format]:
  "Suc j<length ys \<longrightarrow> (P (tl(ys)!j) = P (ys!Suc j))"
by (simp add: List.nth_tl)

lemma tl_zero_eq' :
   "\<forall>j. Suc j<length ys \<longrightarrow> (P (tl(ys)!j) = P (ys!Suc j))"
using tl_zero_eq by blast

lemma tl_zero_pair:"i < length ys \<Longrightarrow> length ys = length zs \<Longrightarrow>
       Suc j < length (snd (ys!i)) \<Longrightarrow>
       snd (zs!i) = tl (snd (ys!i)) \<Longrightarrow>        
       P ((snd (ys!i))!(Suc j)) =
       P ((snd (zs!i))!j)"  
  by (simp add: tl_zero_eq)


lemma tl_zero_pair':"\<forall>i < length ys. length ys = length zs \<longrightarrow>
       Suc j < length (snd (ys!i)) \<longrightarrow>
       snd (zs!i) = tl (snd (ys!i)) \<longrightarrow>        
       (P ((snd (ys!i))!(Suc j)) =
       P ((snd (zs!i))!j))"  
using tl_zero_pair by blast

lemma tl_zero_pair2:"i < length ys \<Longrightarrow> length ys = length zs \<Longrightarrow>
       Suc (Suc j) < length (snd (ys!i)) \<Longrightarrow>
       snd (zs!i) = tl (snd (ys!i)) \<Longrightarrow>        
       P ((snd (ys!i))!(Suc (Suc j))) ((snd (ys!i))!(Suc j))  =
       P ((snd (zs!i))!(Suc j)) ((snd (zs!i))!j)"  
  by (simp add: tl_zero_eq)

lemma tl_zero_pair2':"\<forall>i < length ys. length ys = length zs \<longrightarrow>
       Suc (Suc j) < length (snd (ys!i)) \<longrightarrow>
       snd (zs!i) = tl (snd (ys!i)) \<longrightarrow>        
       P ((snd (ys!i))!(Suc (Suc j))) ((snd (ys!i))!(Suc j))  =
       P ((snd (zs!i))!(Suc j)) ((snd (zs!i))!j)"  
using tl_zero_pair2  by blast

lemma tl_zero_pair21:"\<forall>i < length ys. length ys = length zs \<longrightarrow>
       Suc (Suc j) < length (snd (ys!i)) \<longrightarrow>
       snd (zs!i) = tl (snd (ys!i)) \<longrightarrow>        
       P  ((snd (ys!i))!(Suc j))  ((snd (ys!i))!(Suc (Suc j)))=
       P ((snd (zs!i))!j) ((snd (zs!i))!(Suc j)) "
by (metis SmallStepCon.nth_tl list.size(3) not_less0 nth_Cons_Suc)  

lemma tl_pair:"Suc (Suc j) < length l \<Longrightarrow>     
       l1 = tl l \<Longrightarrow>
       P (l!(Suc (Suc j))) (l!(Suc j)) =
       P (l1!(Suc j)) (l1!j)"
by (simp add: tl_zero_eq)

lemma list_as_map: 
  assumes 
     a1:"length clist > 0" and 
     a2: "xs = (map (\<lambda>x. fst (hd x)) clist)" and
     a3: "ys = (map (\<lambda>x. tl x) clist)" and
     a4: "\<forall>i< length clist. length (clist!i) > 0" and     
     a5: "\<forall>i < length clist. \<forall>j< length clist. \<forall>k<length  (clist!i).
           snd ((clist!i)!k) = snd ((clist!j)!k)" and
     a6: "\<forall>i < length clist. \<forall>j< length clist. 
            length (clist!i) = length (clist!j)" 
     shows "clist = map (\<lambda>i. (fst i,snd ((clist!0)!0))#snd i) (zip xs ys)"
proof-
  let ?clist'= "map (\<lambda>i. (fst i,snd ((clist!0)!0))#snd i) (zip xs ys)"
  have lens:"length clist = length ?clist'"  using a2 a3 by auto   
  have "(\<forall>i<length clist. clist ! i = ?clist' ! i)" 
  proof -
    {
      fix i    
      assume a11:"i<length clist"
      have xs_clist:"xs!i = fst (hd (clist!i))" using a2 a11 by auto
      have ys_clist:"ys!i = tl (clist ! i)" using a3 a11 by auto
      have snd_zero:"snd (hd (clist!i)) = snd ((clist!0)!0)" using a5 a4 
        by (metis (no_types, lifting) a1 a11 hd_conv_nth less_numeral_extra(3) list.size(3))
      then have "(\<lambda>i. (fst i,snd ((clist!0)!0))#snd i) ((zip xs ys)!i) = clist !i"               
        proof -
          have f1: "length xs = length clist"
            using a2 length_map by blast
          have "\<not> (0::nat) < 0"
            by (meson less_not_refl)
          thus ?thesis
            using f1 by (metis (lifting) a11 a3 a4 
                         fst_conv length_map list.exhaust_sel 
                         list.size(3) nth_zip prod.collapse 
                         snd_conv snd_zero xs_clist ys_clist)
        qed      
      then have "clist ! i = ?clist' ! i" using lens a11 by force
    } 
    thus ?thesis by auto    
  qed
  thus ?thesis using lens list_eq by blast
qed

lemma list_as_map': 
  assumes 
     a1:"length clist > 0" and 
     a2: "xs = (map (\<lambda>x. hd x) clist)" and
     a3: "ys = (map (\<lambda>x. tl x) clist)" and
     a4: "\<forall>i< length clist. length (clist!i) > 0"
     shows "clist = map (\<lambda>i. (fst i)#snd i) (zip xs ys)"
proof-
  let ?clist'= "map (\<lambda>i.(fst i)#snd i) (zip xs ys)"
  have lens:"length clist = length ?clist'" using a2 a3 by auto  
  have "(\<forall>i<length clist. clist ! i = ?clist' ! i)" 
  proof -
    {
      fix i    
      assume a11:"i<length clist"
      have xs_clist:"xs!i = hd (clist!i)" using a2 a11 by auto
      have ys_clist:"ys!i = tl (clist ! i)" using a3 a11 by auto 
      then have "(\<lambda>i. fst i#snd i) ((zip xs ys)!i) = clist !i"  
        using xs_clist ys_clist a11 a2 a3 a4 by fastforce  
      then have "clist ! i = ?clist' ! i" using lens a11 by force
    } 
    thus ?thesis by auto    
  qed
  thus ?thesis using lens list_eq by blast
qed


lemma clist_tail: 
  assumes 
    a1:"length xs = length clist" and
    a2: "ys = (map (\<lambda>i. (\<Gamma>,(fst i,s)#snd i)) (zip xs clist))"
 shows "\<forall>i < length ys. tl (snd (ys!i)) = clist!i "
using a1 a2
proof -   
   show ?thesis using a2
   by (simp add: a1)           
qed   


lemma clist_map: 
   assumes 
    a1:"length xs = length clist" 
   shows "clist = map ((\<lambda>p. tl (snd p)) \<circ> (\<lambda>i. (\<Gamma>, (fst i, s) # snd i))) (zip xs clist)"
proof -
  have f1: "map snd (zip xs clist) = clist"
    using a1 map_snd_zip by blast
  have "map snd (zip xs clist) = map ((\<lambda>p. tl (snd p)) \<circ> (\<lambda>p. (\<Gamma>, (fst p, s) # snd p))) (zip xs clist)"
    by simp
  thus ?thesis
    using f1 by presburger
qed


lemma clist_map1: 
   assumes 
    a1:"length xs = length clist"     
   shows "clist = map (\<lambda>p. tl (snd p)) (map (\<lambda>i. (\<Gamma>,(fst i,s)#snd i)) (zip xs clist))"
proof -
   have "clist = map ((\<lambda>p. tl (snd p)) \<circ> (\<lambda>i. (\<Gamma>, (fst i, s) # snd i))) (zip xs clist)" 
   using a1  clist_map by fastforce
   thus ?thesis by auto
qed

lemma clist_map2:
     "(clist = map (\<lambda>p. tl (snd p)) (l::('a \<times>'b list) list) ) \<Longrightarrow>
       clist = map (\<lambda>p. (snd p)) (map (\<lambda>p. (fst p, tl (snd p))) (l::('a \<times>'b list) list)) "
by auto

lemma map_snd:
   assumes a1: "y = map  (\<lambda>x. f x) l"
   shows   "y=(map snd (map (\<lambda>x. (g x, f x)) l)) "
by (simp add: assms)
 
lemmas map_snd_sym = map_snd[THEN sym]

lemma map_snd':
   shows   " map  (\<lambda>x. f x) l=(map snd (map (\<lambda>x. (g x, f x)) l)) "
by simp


lemma hd_nth:
   assumes a1:"i< length l \<and> ( length( (l!i)) > 0)"
   shows "f (hd (l!i)) = f (nth (l!i) 0)"
using assms hd_conv_nth by fastforce

lemma map_hd_nth:
   assumes a1:"(\<forall>i <length l. length( (l!i)) > 0)"
   shows "map (\<lambda>x. f (hd x)) l = map (\<lambda>x. f (nth (x) 0)) l"
proof -  
   have "\<forall>i < length l. (map (\<lambda>x. f (hd x)) l)!i = f (nth (l!i) 0)"
    using hd_nth a1 by auto
  moreover have "\<forall>i < length l. (map (\<lambda>x. f (nth x 0)) l)!i = f (nth (l!i) 0)"
    using hd_nth a1 by auto
  ultimately have f1:"\<forall>i < length l. (map (\<lambda>x. f (hd x)) l)!i =(map (\<lambda>x. f (nth x 0)) l)!i "
    by auto
  moreover have f2:"length (map (\<lambda>x. f (hd x)) l) = length l"
    by auto   
  moreover have "length (map (\<lambda>x. f (nth x 0)) l) = length l" by auto
  ultimately show ?thesis using nth_equalityI by metis
qed

lemma "i<length clist \<Longrightarrow> clist!i = (x1,ys) \<Longrightarrow> ys = (map (\<lambda>x. (fst (hd (snd x)),s)#tl (snd x)) clist)!i \<Longrightarrow>
         ys = (map (\<lambda>x. (fst x, s)#snd x) 
               (zip (map (\<lambda>x. fst (hd (snd x))) clist) 
                    (map (\<lambda>x. tl (snd x)) clist)))!i"
proof (induct ys)
  case Nil thus ?case by auto
next
  case (Cons y ys) 
  have "\<forall>n ps f. \<not> n < length ps \<or> map f ps ! n = (f (ps ! n::'a \<times> ('b \<times> 'c) list)::('b \<times> 'c) list)"
    by force
  hence "y # ys = (fst (hd (snd (clist ! i))), s) # tl (snd (clist ! i))"
    using Cons.prems(1) Cons.prems(3) by presburger
  thus ?case
    using Cons.prems(1) by auto
qed


lemma mapzip_upd:" length as = length clist  \<Longrightarrow>
       (map (\<lambda>j. (as ! j, sa) # clist ! j) [0..<length as]) =  
       map (\<lambda>j. ((fst j, sa)#snd j)) (zip as clist)"
proof -    
    assume a2: "length as = length clist"   
    have "\<forall>i < length  (map (\<lambda>j. (as ! j, sa) # clist ! j) [0..<length as]). (map (\<lambda>j. (as ! j, sa) # clist ! j) [0..<length as])!i = map (\<lambda>j. ((fst j, sa)#snd j)) (zip as clist)!i"  
     using a2
      by auto
  moreover have "length (map (\<lambda>j. (as ! j, sa) # clist ! j) [0..<length as]) =
         length (map (\<lambda>j. ((fst j, sa)#snd j)) (zip as clist))"
     using a2 by auto   
  ultimately have "(map (\<lambda>j. (as ! j, sa) # clist ! j) [0..<length as]) = map (\<lambda>j. ((fst j, sa)#snd j)) (zip as clist)"
     using nth_equalityI by blast
  thus "map (\<lambda>j. (as ! j, sa) # clist ! j) [0..<length as] = 
        map (\<lambda>j. (fst j, sa) # snd j) (zip as clist) "
      by auto
qed


(************************************************************************ *)
(* subsection {* Equivalence between Small-Step and Big-Step Semantics *} *)
(* ************************************************************************ *)
 
(* 

?\<Gamma>\<turnstile>\<^sub>c (LanguageCon.com.Seq ?c1.0 ?c2.0, ?s) \<rightarrow>
       (LanguageCon.com.Seq ?c1' ?c2.0,
        ?s') \<Longrightarrow>
(?\<Gamma>\<turnstile>\<^sub>c (?c1.0, ?s) \<rightarrow> (?c1', ?s') \<Longrightarrow> ?P) \<Longrightarrow>
?P

lemma 
   assumes 
           step_a: "\<Gamma>\<turnstile>\<^sub>c(Await b c, Normal s) \<rightarrow> (t,u)"
   shows step_await_step_c:"(\<Gamma>\<^sub>\<not>\<^sub>a)\<turnstile>(c, Normal s) \<rightarrow>\<^sup>* (sequential t,u)" 
using step_a
proof cases
  fix t1
  assume
      "(t, u) = (Skip, t1)" "s \<in> b" "\<Gamma>\<turnstile> \<langle>c,Normal s\<rangle> \<Rightarrow> t1" "\<forall>t'. t1 \<noteq> Abrupt t'"
  thus ?thesis 
   by (cases u) 
   (auto intro: exec_impl_steps_Fault exec_impl_steps_Normal exec_impl_steps_Stuck)
next
  fix t1
  assume "(t, u) = (Throw, Normal t1)" "s \<in> b" "\<Gamma>\<turnstile> \<langle>c,Normal s\<rangle> \<Rightarrow> Abrupt t1"
  thus ?thesis by (simp add: exec_impl_steps_Normal_Abrupt)
qed

lemma 
   assumes (* exec: "\<Gamma>\<turnstile>\<langle>c,Normal s\<rangle> \<Rightarrow> t" and
           b: "s \<in> b" and *)
           step_a: "\<Gamma>\<turnstile>\<^sub>c(Await b c, Normal s) \<rightarrow> u"
   shows step_await_final1:"final u"
using step_a 
proof cases
  case  (1 t) thus "final u"  by (simp add: final_def)
next
  case (2 t)
  thus "final u" by (simp add: exec_impl_steps_Normal_Abrupt final_def)
qed

lemma step_Abrupt_end: 
  assumes step: "\<Gamma>\<turnstile>\<^sub>c (c\<^sub>1, s) \<rightarrow> (c\<^sub>1', s')"
  shows "s'=Abrupt x \<Longrightarrow> s=Abrupt x"
using step
by induct auto


lemma step_Stuck_end: 
  assumes step: "\<Gamma>\<turnstile>\<^sub>c (c\<^sub>1, s) \<rightarrow> (c\<^sub>1', s')"
  shows "s'=Stuck \<Longrightarrow> 
          s=Stuck \<or> 
          (\<exists>r x. redex c\<^sub>1 = Spec r \<and> s=Normal x \<and> (\<forall>t. (x,t)\<notin>r)) \<or> 
          (\<exists>p x. redex c\<^sub>1=  Call p \<and> s=Normal x \<and> \<Gamma> p = None) \<or>
          (\<exists>b c x.  redex c\<^sub>1 = Await b c \<and> s=Normal x \<and> x \<in> b \<and> \<Gamma>\<turnstile>\<langle>c,s\<rangle>\<Rightarrow>s')"
using step
by induct auto

lemma step_Fault_end: 
  assumes step: "\<Gamma>\<turnstile>\<^sub>c (c\<^sub>1, s) \<rightarrow> (c\<^sub>1', s')"
  shows "s'=Fault f \<Longrightarrow> 
          s=Fault f \<or> 
          (\<exists>g c x.  redex c\<^sub>1 = Guard f g c \<and> s=Normal x \<and> x \<notin> g) \<or>
          (\<exists>b c1 x.  redex c\<^sub>1 = Await b c1 \<and> s=Normal x \<and> x \<in> b \<and> \<Gamma>\<turnstile>\<langle>c1,s\<rangle>\<Rightarrow>s')"
using step 
by induct auto



(* ************************************************************************ *)
subsection {* Infinite Computations: @{text "\<Gamma>\<turnstile>(c, s) \<rightarrow> \<dots>(\<infinity>)"}*}
(* ************************************************************************ *)

definition inf_c:: "('s,'p,'f,'e) body \<Rightarrow> ('s,'p,'f,'e) config \<Rightarrow> bool"
 ("_\<turnstile>\<^sub>c _ \<rightarrow> \<dots>'(\<infinity>')" [60,80] 100) where
"\<Gamma>\<turnstile>\<^sub>c cfg \<rightarrow> \<dots>(\<infinity>) \<equiv> (\<exists>f. f (0::nat) = cfg \<and> (\<forall>i. \<Gamma>\<turnstile>\<^sub>cf i \<rightarrow> f (i+1)))" 

lemma not_infI: "\<lbrakk>\<And>f. \<lbrakk>f 0 = cfg; \<And>i. \<Gamma>\<turnstile>\<^sub>cf i \<rightarrow> f (Suc i)\<rbrakk> \<Longrightarrow> False\<rbrakk>  
                \<Longrightarrow> \<not>\<Gamma>\<turnstile>\<^sub>c cfg \<rightarrow> \<dots>(\<infinity>)"
  by (auto simp add: inf_c_def)

(* ************************************************************************ *)
subsection {* Equivalence between Termination and the Absence of Infinite Computations*}
(* ************************************************************************ *)


lemma step_preserves_termination: 
  assumes step: "\<Gamma>\<turnstile>(c,s) \<rightarrow> (c',s')"
  shows "\<Gamma>\<turnstile>c\<down>s \<Longrightarrow> \<Gamma>\<turnstile>c'\<down>s'"  
using step
proof (induct)
  case Basic thus ?case by (fastforce intro: terminates.intros)
next
  case Spec thus ?case by (fastforce intro: terminates.intros)
next
  case SpecStuck thus ?case by (fastforce intro: terminates.intros)
next
  case Guard thus ?case 
    by (fastforce intro: terminates.intros elim: terminates_Normal_elim_cases)
next
  case GuardFault thus ?case by (fastforce intro: terminates.intros)
next
  case (Seq c\<^sub>1 s c\<^sub>1' s' c\<^sub>2) thus ?case
    apply (cases s)
    apply     (cases s')
    apply         (fastforce intro: terminates.intros step_extend 
                    elim: terminates_Normal_elim_cases)
    apply (fastforce intro: terminates.intros dest: step_Abrupt_prop 
      step_Fault_prop step_Stuck_prop)+
    done
next
  case (SeqSkip c\<^sub>2 s) 
  thus ?case 
    apply (cases s)
    apply (fastforce intro: terminates.intros exec.intros
            elim: terminates_Normal_elim_cases )+
    done
next
  case (SeqThrow c\<^sub>2 s) 
  thus ?case 
    by (fastforce intro: terminates.intros exec.intros
            elim: terminates_Normal_elim_cases )
next
  case CondTrue 
  thus ?case 
    by (fastforce intro: terminates.intros exec.intros
            elim: terminates_Normal_elim_cases )
next
  case CondFalse 
  thus ?case 
    by (fastforce intro: terminates.intros 
            elim: terminates_Normal_elim_cases )
next
  case WhileTrue
  thus ?case 
    by (fastforce intro: terminates.intros 
            elim: terminates_Normal_elim_cases )
next
  case WhileFalse 
  thus ?case 
    by (fastforce intro: terminates.intros 
            elim: terminates_Normal_elim_cases )
next
  case Call 
  thus ?case 
    by (fastforce intro: terminates.intros 
            elim: terminates_Normal_elim_cases )
next
  case CallUndefined
  thus ?case 
    by (fastforce intro: terminates.intros 
            elim: terminates_Normal_elim_cases )
next
  case DynCom
  thus ?case 
    by (fastforce intro: terminates.intros 
            elim: terminates_Normal_elim_cases )
next
  case (Catch c\<^sub>1 s c\<^sub>1' s' c\<^sub>2) thus ?case
    apply (cases s)
    apply     (cases s')
    apply         (fastforce intro: terminates.intros step_extend 
                    elim: terminates_Normal_elim_cases)
    apply (fastforce intro: terminates.intros dest: step_Abrupt_prop 
      step_Fault_prop step_Stuck_prop)+
    done
next
  case CatchThrow
  thus ?case 
   by (fastforce intro: terminates.intros exec.intros
            elim: terminates_Normal_elim_cases )
next
  case (CatchSkip c\<^sub>2 s) 
  thus ?case 
    by (cases s) (fastforce intro: terminates.intros)+
next
  case FaultProp thus ?case by (fastforce intro: terminates.intros)
next
  case StuckProp thus ?case by (fastforce intro: terminates.intros)
next
  case AbruptProp thus ?case by (fastforce intro: terminates.intros)
next 
  case Await thus ?case using terminates_Skip' by blast 
next 
  case AwaitAbrupt thus ?case by (fastforce intro: terminates.intros)
qed

lemma steps_preserves_termination: 
  assumes steps: "\<Gamma>\<turnstile>(c,s) \<rightarrow>\<^sup>* (c',s')"
  shows "\<Gamma>\<turnstile>c\<down>s \<Longrightarrow> \<Gamma>\<turnstile>c'\<down>s'"
using steps
proof (induct rule: rtranclp_induct2 [consumes 1, case_names Refl Trans])
  case Refl thus ?case  .
next
  case Trans
  thus ?case
    by (blast dest: step_preserves_termination)
qed

ML {*
  ML_Thms.bind_thm ("tranclp_induct2", Split_Rule.split_rule @{context}
    (Rule_Insts.read_instantiate @{context}
      [((("a", 0), Position.none), "(aa,ab)"), ((("b", 0), Position.none), "(ba,bb)")] []
      @{thm tranclp_induct}));
*}

thm tranclp_induct2 tranclp_induct

lemma steps_preserves_termination': 
  assumes steps: "\<Gamma>\<turnstile>(c,s) \<rightarrow>\<^sup>+ (c',s')"
  shows "\<Gamma>\<turnstile>c\<down>s \<Longrightarrow> \<Gamma>\<turnstile>c'\<down>s'"
using steps
proof (induct rule: tranclp_induct2 [consumes 1, case_names Step Trans])
  case Step thus ?case by (blast intro: step_preserves_termination)
next
  case Trans
  thus ?case
    by (blast dest: step_preserves_termination)
qed



definition head_com:: "('s,'p,'f,'e) com \<Rightarrow> ('s,'p,'f,'e) com"
where
"head_com c =
  (case c of
     Seq c\<^sub>1 c\<^sub>2 \<Rightarrow> c\<^sub>1
   | Catch c\<^sub>1 c\<^sub>2 \<Rightarrow> c\<^sub>1
   | _ \<Rightarrow> c)"

  
definition head:: "('s,'p,'f,'e) config \<Rightarrow> ('s,'p,'f,'e) config"
  where "head cfg = (head_com (fst cfg), snd cfg)"

lemma le_Suc_cases: "\<lbrakk>\<And>i. \<lbrakk>i < k\<rbrakk> \<Longrightarrow> P i; P k\<rbrakk> \<Longrightarrow> \<forall>i<(Suc k). P i"
  apply clarify
  apply (case_tac "i=k")
  apply auto
  done

lemma redex_Seq_False: "\<And>c' c''. (redex c = Seq c'' c') = False"
  by (induct c) auto

lemma redex_Catch_False: "\<And>c' c''. (redex c = Catch c'' c') = False"
  by (induct c) auto


lemma infinite_computation_extract_head_Seq:
  assumes inf_comp: "\<forall>i::nat. \<Gamma>\<turnstile>f i \<rightarrow> f (i+1)"
  assumes f_0: "f 0 = (Seq c\<^sub>1 c\<^sub>2,s)"
  assumes not_fin: "\<forall>i<k. \<not> final (head (f i))"
  shows "\<forall>i<k. (\<exists>c' s'. f (i + 1) = (Seq c' c\<^sub>2, s')) \<and>  
               \<Gamma>\<turnstile>head (f i) \<rightarrow> head (f (i+1))"
        (is "\<forall>i<k. ?P i")
using not_fin
proof (induct k)
  case 0
  show ?case by simp
next
  case (Suc k)
  have not_fin_Suc: 
    "\<forall>i<Suc k. \<not> final (head (f i))" by fact
  from this[rule_format] have not_fin_k: 
    "\<forall>i<k. \<not> final (head (f i))" 
    apply clarify
    apply (subgoal_tac "i < Suc k")
    apply blast
    apply simp
    done

  from Suc.hyps [OF this]
  have hyp: "\<forall>i<k. (\<exists>c' s'. f (i + 1) = (Seq c' c\<^sub>2, s')) \<and> 
                   \<Gamma>\<turnstile> head (f i) \<rightarrow> head (f (i + 1))".
  show ?case
  proof (rule le_Suc_cases)
    fix i 
    assume "i < k"
    then show "?P i"
      by (rule hyp [rule_format])
  next
    show "?P k"
    proof -
      from hyp [rule_format, of "k - 1"] f_0
      obtain c' fs' L' s' where  f_k: "f k = (Seq c' c\<^sub>2, s')"
        by (cases k) auto
      from inf_comp [rule_format, of k] f_k
      have "\<Gamma>\<turnstile>(Seq c' c\<^sub>2, s') \<rightarrow> f (k + 1)"
        by simp
      moreover
      from not_fin_Suc [rule_format, of k] f_k
      have "\<not> final (c',s')"
        by (simp add: final_def head_def head_com_def)
      ultimately
      obtain c'' s'' where
         "\<Gamma>\<turnstile>(c', s') \<rightarrow> (c'', s'')" and
         "f (k + 1) = (Seq c'' c\<^sub>2, s'')"
        by cases (auto simp add: redex_Seq_False final_def)
      with f_k
      show ?thesis
        by (simp add: head_def head_com_def)
    qed
  qed
qed

lemma infinite_computation_extract_head_Catch:
  assumes inf_comp: "\<forall>i::nat. \<Gamma>\<turnstile>f i \<rightarrow> f (i+1)"
  assumes f_0: "f 0 = (Catch c\<^sub>1 c\<^sub>2,s)"
  assumes not_fin: "\<forall>i<k. \<not> final (head (f i))"
  shows "\<forall>i<k. (\<exists>c' s'. f (i + 1) = (Catch c' c\<^sub>2, s')) \<and>  
               \<Gamma>\<turnstile>head (f i) \<rightarrow> head (f (i+1))"
        (is "\<forall>i<k. ?P i")
using not_fin
proof (induct k)
  case 0
  show ?case by simp
next
  case (Suc k)
  have not_fin_Suc: 
    "\<forall>i<Suc k. \<not> final (head (f i))" by fact
  from this[rule_format] have not_fin_k: 
    "\<forall>i<k. \<not> final (head (f i))" 
    apply clarify
    apply (subgoal_tac "i < Suc k")
    apply blast
    apply simp
    done

  from Suc.hyps [OF this]
  have hyp: "\<forall>i<k. (\<exists>c' s'. f (i + 1) = (Catch c' c\<^sub>2, s')) \<and> 
                   \<Gamma>\<turnstile> head (f i) \<rightarrow> head (f (i + 1))".
  show ?case
  proof (rule le_Suc_cases)
    fix i 
    assume "i < k"
    then show "?P i"
      by (rule hyp [rule_format])
  next
    show "?P k"
    proof -
      from hyp [rule_format, of "k - 1"] f_0
      obtain c' fs' L' s' where  f_k: "f k = (Catch c' c\<^sub>2, s')"
        by (cases k) auto
      from inf_comp [rule_format, of k] f_k
      have "\<Gamma>\<turnstile>(Catch c' c\<^sub>2, s') \<rightarrow> f (k + 1)"
        by simp
      moreover
      from not_fin_Suc [rule_format, of k] f_k
      have "\<not> final (c',s')"
        by (simp add: final_def head_def head_com_def)
      ultimately
      obtain c'' s'' where
         "\<Gamma>\<turnstile>(c', s') \<rightarrow> (c'', s'')" and
         "f (k + 1) = (Catch c'' c\<^sub>2, s'')"
        by cases (auto simp add: redex_Catch_False final_def)+
      with f_k
      show ?thesis
        by (simp add: head_def head_com_def)
    qed
  qed
qed

lemma no_inf_Throw: "\<not> \<Gamma>\<turnstile>(Throw,s) \<rightarrow> \<dots>(\<infinity>)"
proof 
  assume "\<Gamma>\<turnstile> (Throw, s) \<rightarrow> \<dots>(\<infinity>)"
  then obtain f where
    step [rule_format]: "\<forall>i::nat. \<Gamma>\<turnstile>f i \<rightarrow> f (i+1)" and
    f_0: "f 0 = (Throw, s)"
    by (auto simp add: inf_def)
  from step [of 0, simplified f_0] step [of 1]
  show False
    by cases (auto elim: step_elim_cases)
qed

lemma split_inf_Seq: 
  assumes inf_comp: "\<Gamma>\<turnstile>(Seq c\<^sub>1 c\<^sub>2,s) \<rightarrow> \<dots>(\<infinity>)"
  shows "\<Gamma>\<turnstile>(c\<^sub>1,s) \<rightarrow> \<dots>(\<infinity>) \<or> 
         (\<exists>s'. \<Gamma>\<turnstile>(c\<^sub>1,s) \<rightarrow>\<^sup>* (Skip,s') \<and> \<Gamma>\<turnstile>(c\<^sub>2,s') \<rightarrow> \<dots>(\<infinity>))"
proof -
  from inf_comp obtain f where
    step: "\<forall>i::nat. \<Gamma>\<turnstile>f i \<rightarrow> f (i+1)" and
    f_0: "f 0 = (Seq c\<^sub>1 c\<^sub>2, s)"
    by (auto simp add: inf_def)
  from f_0 have head_f_0: "head (f 0) = (c\<^sub>1,s)" 
    by (simp add: head_def head_com_def)
  show ?thesis
  proof (cases "\<exists>i. final (head (f i))")
    case True
    def k\<equiv>"(LEAST i. final (head (f i)))"
    have less_k: "\<forall>i<k. \<not> final (head (f i))"
      apply (intro allI impI)
      apply (unfold k_def)
      apply (drule not_less_Least)
      apply auto
      done
    from infinite_computation_extract_head_Seq [OF step f_0 this]
    obtain step_head: "\<forall>i<k. \<Gamma>\<turnstile> head (f i) \<rightarrow> head (f (i + 1))" and
           conf: "\<forall>i<k. (\<exists>c' s'. f (i + 1) = (Seq c' c\<^sub>2, s'))"
      by blast 
    from True
    have final_f_k: "final (head (f k))"
      apply -
      apply (erule exE)
      apply (drule LeastI)
      apply (simp add: k_def)
      done
    moreover
    from f_0 conf [rule_format, of "k - 1"]
    obtain c' s' where f_k: "f k = (Seq c' c\<^sub>2,s')"
      by (cases k) auto
    moreover
    from step_head have steps_head: "\<Gamma>\<turnstile>head (f 0) \<rightarrow>\<^sup>* head (f k)"
    proof (induct k)
      case 0 thus ?case by simp
    next
      case (Suc m)
      have step: "\<forall>i<Suc m. \<Gamma>\<turnstile> head (f i) \<rightarrow> head (f (i + 1))" by fact
      hence "\<forall>i<m. \<Gamma>\<turnstile> head (f i) \<rightarrow> head (f (i + 1))"
        by auto
      hence "\<Gamma>\<turnstile> head (f 0) \<rightarrow>\<^sup>*  head (f m)"
        by (rule Suc.hyps)
      also from step [rule_format, of m]
      have "\<Gamma>\<turnstile> head (f m) \<rightarrow> head (f (m + 1))" by simp
      finally show ?case by simp
    qed
    {
      assume f_k: "f k = (Seq Skip c\<^sub>2, s')"
      with steps_head
      have "\<Gamma>\<turnstile>(c\<^sub>1,s) \<rightarrow>\<^sup>* (Skip,s')"
        using head_f_0
        by (simp add: head_def head_com_def)
      moreover
      from step [rule_format, of k] f_k
      obtain "\<Gamma>\<turnstile>(Seq Skip c\<^sub>2,s') \<rightarrow> (c\<^sub>2,s')" and
        f_Suc_k: "f (k + 1) = (c\<^sub>2,s')"
        by (fastforce elim: step.cases intro: step.intros)
      def g\<equiv>"\<lambda>i. f (i + (k + 1))"
      from f_Suc_k
      have g_0: "g 0 = (c\<^sub>2,s')"
        by (simp add: g_def)
      from step
      have "\<forall>i. \<Gamma>\<turnstile>g i \<rightarrow> g (i + 1)"
        by (simp add: g_def)
      with g_0 have "\<Gamma>\<turnstile>(c\<^sub>2,s') \<rightarrow> \<dots>(\<infinity>)"
        by (auto simp add: inf_def)
      ultimately
      have ?thesis
        by auto
    }
    moreover
    {
      fix x
      assume s': "s'=Normal x" and f_k: "f k = (Seq Throw c\<^sub>2, s')"
      from step [rule_format, of k] f_k s'
      obtain "\<Gamma>\<turnstile>(Seq Throw c\<^sub>2,s') \<rightarrow> (Throw,s')" and
        f_Suc_k: "f (k + 1) = (Throw,s')"
        by (fastforce elim: step_elim_cases intro: step.intros)
      def g\<equiv>"\<lambda>i. f (i + (k + 1))"
      from f_Suc_k
      have g_0: "g 0 = (Throw,s')"
        by (simp add: g_def)
      from step
      have "\<forall>i. \<Gamma>\<turnstile>g i \<rightarrow> g (i + 1)"
        by (simp add: g_def)
      with g_0 have "\<Gamma>\<turnstile>(Throw,s') \<rightarrow> \<dots>(\<infinity>)"
        by (auto simp add: inf_def)
      with no_inf_Throw
      have ?thesis
        by auto
    }
    ultimately 
    show ?thesis
      by (auto simp add: final_def head_def head_com_def)
  next
    case False
    then have not_fin: "\<forall>i. \<not> final (head (f i))"
      by blast
    have "\<forall>i. \<Gamma>\<turnstile>head (f i) \<rightarrow> head (f (i + 1))"
    proof 
      fix k
      from not_fin 
      have "\<forall>i<(Suc k). \<not> final (head (f i))"
        by simp
      
      from infinite_computation_extract_head_Seq [OF step f_0 this ]
      show "\<Gamma>\<turnstile> head (f k) \<rightarrow> head (f (k + 1))" by simp
    qed
    with head_f_0 have "\<Gamma>\<turnstile>(c\<^sub>1,s) \<rightarrow> \<dots>(\<infinity>)"
      by (auto simp add: inf_def)
    thus ?thesis
      by simp
  qed
qed

lemma split_inf_Catch: 
  assumes inf_comp: "\<Gamma>\<turnstile>(Catch c\<^sub>1 c\<^sub>2,s) \<rightarrow> \<dots>(\<infinity>)"
  shows "\<Gamma>\<turnstile>(c\<^sub>1,s) \<rightarrow> \<dots>(\<infinity>) \<or> 
         (\<exists>s'. \<Gamma>\<turnstile>(c\<^sub>1,s) \<rightarrow>\<^sup>* (Throw,Normal s') \<and> \<Gamma>\<turnstile>(c\<^sub>2,Normal s') \<rightarrow> \<dots>(\<infinity>))"
proof -
  from inf_comp obtain f where
    step: "\<forall>i::nat. \<Gamma>\<turnstile>f i \<rightarrow> f (i+1)" and
    f_0: "f 0 = (Catch c\<^sub>1 c\<^sub>2, s)"
    by (auto simp add: inf_def)
  from f_0 have head_f_0: "head (f 0) = (c\<^sub>1,s)" 
    by (simp add: head_def head_com_def)
  show ?thesis
  proof (cases "\<exists>i. final (head (f i))")
    case True
    def k\<equiv>"(LEAST i. final (head (f i)))"
    have less_k: "\<forall>i<k. \<not> final (head (f i))"
      apply (intro allI impI)
      apply (unfold k_def)
      apply (drule not_less_Least)
      apply auto
      done
    from infinite_computation_extract_head_Catch [OF step f_0 this]
    obtain step_head: "\<forall>i<k. \<Gamma>\<turnstile> head (f i) \<rightarrow> head (f (i + 1))" and
           conf: "\<forall>i<k. (\<exists>c' s'. f (i + 1) = (Catch c' c\<^sub>2, s'))"
      by blast 
    from True
    have final_f_k: "final (head (f k))"
      apply -
      apply (erule exE)
      apply (drule LeastI)
      apply (simp add: k_def)
      done
    moreover
    from f_0 conf [rule_format, of "k - 1"]
    obtain c' s' where f_k: "f k = (Catch c' c\<^sub>2,s')"
      by (cases k) auto
    moreover
    from step_head have steps_head: "\<Gamma>\<turnstile>head (f 0) \<rightarrow>\<^sup>* head (f k)"
    proof (induct k)
      case 0 thus ?case by simp
    next
      case (Suc m)
      have step: "\<forall>i<Suc m. \<Gamma>\<turnstile> head (f i) \<rightarrow> head (f (i + 1))" by fact
      hence "\<forall>i<m. \<Gamma>\<turnstile> head (f i) \<rightarrow> head (f (i + 1))"
        by auto
      hence "\<Gamma>\<turnstile> head (f 0) \<rightarrow>\<^sup>*  head (f m)"
        by (rule Suc.hyps)
      also from step [rule_format, of m]
      have "\<Gamma>\<turnstile> head (f m) \<rightarrow> head (f (m + 1))" by simp
      finally show ?case by simp
    qed
    {
      assume f_k: "f k = (Catch Skip c\<^sub>2, s')"
      with steps_head
      have "\<Gamma>\<turnstile>(c\<^sub>1,s) \<rightarrow>\<^sup>* (Skip,s')"
        using head_f_0
        by (simp add: head_def head_com_def)
      moreover
      from step [rule_format, of k] f_k
      obtain "\<Gamma>\<turnstile>(Catch Skip c\<^sub>2,s') \<rightarrow> (Skip,s')" and
        f_Suc_k: "f (k + 1) = (Skip,s')"
        by (fastforce elim: step.cases intro: step.intros)
      from step [rule_format, of "k+1", simplified f_Suc_k]
      have ?thesis
        by (rule no_step_final') (auto simp add: final_def)
    }
    moreover
    {
      fix x
      assume s': "s'=Normal x" and f_k: "f k = (Catch Throw c\<^sub>2, s')"
      with steps_head
      have "\<Gamma>\<turnstile>(c\<^sub>1,s) \<rightarrow>\<^sup>* (Throw,s')"
        using head_f_0
        by (simp add: head_def head_com_def)
      moreover
      from step [rule_format, of k] f_k s'
      obtain "\<Gamma>\<turnstile>(Catch Throw c\<^sub>2,s') \<rightarrow> (c\<^sub>2,s')" and
        f_Suc_k: "f (k + 1) = (c\<^sub>2,s')"
        by (fastforce elim: step_elim_cases intro: step.intros)
      def g\<equiv>"\<lambda>i. f (i + (k + 1))"
      from f_Suc_k
      have g_0: "g 0 = (c\<^sub>2,s')"
        by (simp add: g_def)
      from step
      have "\<forall>i. \<Gamma>\<turnstile>g i \<rightarrow> g (i + 1)"
        by (simp add: g_def)
      with g_0 have "\<Gamma>\<turnstile>(c\<^sub>2,s') \<rightarrow> \<dots>(\<infinity>)"
        by (auto simp add: inf_def)
      ultimately
      have ?thesis
        using s'
        by auto
    }
    ultimately 
    show ?thesis
      by (auto simp add: final_def head_def head_com_def)
  next
    case False
    then have not_fin: "\<forall>i. \<not> final (head (f i))"
      by blast
    have "\<forall>i. \<Gamma>\<turnstile>head (f i) \<rightarrow> head (f (i + 1))"
    proof 
      fix k
      from not_fin 
      have "\<forall>i<(Suc k). \<not> final (head (f i))"
        by simp
      
      from infinite_computation_extract_head_Catch [OF step f_0 this ]
      show "\<Gamma>\<turnstile> head (f k) \<rightarrow> head (f (k + 1))" by simp
    qed
    with head_f_0 have "\<Gamma>\<turnstile>(c\<^sub>1,s) \<rightarrow> \<dots>(\<infinity>)"
      by (auto simp add: inf_def)
    thus ?thesis
      by simp
  qed
qed

lemma Skip_no_step: "\<Gamma>\<turnstile>(Skip,s) \<rightarrow> cfg \<Longrightarrow> P"
  apply (erule no_step_final')
  apply (simp add: final_def)
  done

lemma not_inf_Stuck: "\<not> \<Gamma>\<turnstile>(c,Stuck) \<rightarrow> \<dots>(\<infinity>)"
proof (induct c)
  case Skip
  show ?case
  proof (rule not_infI)
    fix f
    assume f_step: "\<And>i. \<Gamma>\<turnstile>f i \<rightarrow> f (Suc i)"
    assume f_0: "f 0 = (Skip, Stuck)" 
    from f_step [of 0] f_0
    show False
      by (auto elim: Skip_no_step)
  qed
next
  case (Basic g) 
  thus ?case 
  proof (rule not_infI)
    fix f
    assume f_step: "\<And>i. \<Gamma>\<turnstile>f i \<rightarrow> f (Suc i)"
    assume f_0: "f 0 = (Basic g, Stuck)" 
    from f_step [of 0] f_0 f_step [of 1]
    show False
      by (fastforce elim: Skip_no_step step_elim_cases)
  qed
next
  case (Spec r) 
  thus ?case 
  proof (rule not_infI)
    fix f
    assume f_step: "\<And>i. \<Gamma>\<turnstile>f i \<rightarrow> f (Suc i)"
    assume f_0: "f 0 = (Spec r, Stuck)" 
    from f_step [of 0] f_0 f_step [of 1]
    show False
      by (fastforce elim: Skip_no_step step_elim_cases)
  qed
next
  case (Seq c\<^sub>1 c\<^sub>2)
  show ?case
  proof 
    assume "\<Gamma>\<turnstile> (Seq c\<^sub>1 c\<^sub>2, Stuck) \<rightarrow> \<dots>(\<infinity>)"
    from split_inf_Seq [OF this] Seq.hyps
    show False
      by (auto dest: steps_Stuck_prop)
  qed
next
  case (Cond b c\<^sub>1 c\<^sub>2) 
  show ?case 
  proof (rule not_infI)
    fix f
    assume f_step: "\<And>i. \<Gamma>\<turnstile>f i \<rightarrow> f (Suc i)"
    assume f_0: "f 0 = (Cond b c\<^sub>1 c\<^sub>2, Stuck)" 
    from f_step [of 0] f_0 f_step [of 1]
    show False
      by (fastforce elim: Skip_no_step step_elim_cases)
  qed
next
  case (While b c) 
  show ?case 
  proof (rule not_infI)
    fix f
    assume f_step: "\<And>i. \<Gamma>\<turnstile>f i \<rightarrow> f (Suc i)"
    assume f_0: "f 0 = (While b c, Stuck)" 
    from f_step [of 0] f_0 f_step [of 1]
    show False
      by (fastforce elim: Skip_no_step step_elim_cases)
  qed
next
  case (Call p) 
  show ?case 
  proof (rule not_infI)
    fix f
    assume f_step: "\<And>i. \<Gamma>\<turnstile>f i \<rightarrow> f (Suc i)"
    assume f_0: "f 0 = (Call p, Stuck)" 
    from f_step [of 0] f_0 f_step [of 1]
    show False
      by (fastforce elim: Skip_no_step step_elim_cases)
  qed
next
  case (DynCom d) 
  show ?case 
  proof (rule not_infI)
    fix f
    assume f_step: "\<And>i. \<Gamma>\<turnstile>f i \<rightarrow> f (Suc i)"
    assume f_0: "f 0 = (DynCom d, Stuck)" 
    from f_step [of 0] f_0 f_step [of 1]
    show False
      by (fastforce elim: Skip_no_step step_elim_cases)
  qed
next
  case (Guard m g c)
  show ?case 
  proof (rule not_infI)
    fix f
    assume f_step: "\<And>i. \<Gamma>\<turnstile>f i \<rightarrow> f (Suc i)"
    assume f_0: "f 0 = (Guard m g c, Stuck)" 
    from f_step [of 0] f_0 f_step [of 1]
    show False
      by (fastforce elim: Skip_no_step step_elim_cases)
  qed
next
  case Throw
  show ?case 
  proof (rule not_infI)
    fix f
    assume f_step: "\<And>i. \<Gamma>\<turnstile>f i \<rightarrow> f (Suc i)"
    assume f_0: "f 0 = (Throw, Stuck)" 
    from f_step [of 0] f_0 f_step [of 1]
    show False
      by (fastforce elim: Skip_no_step step_elim_cases)
  qed
next
  case (Catch c\<^sub>1 c\<^sub>2)
  show ?case
  proof 
    assume "\<Gamma>\<turnstile> (Catch c\<^sub>1 c\<^sub>2, Stuck) \<rightarrow> \<dots>(\<infinity>)"
    from split_inf_Catch [OF this] Catch.hyps
    show False
      by (auto dest: steps_Stuck_prop)
  qed  
next 
  case (Await b c)
  show ?case 
   proof (rule not_infI)
    fix f
    assume f_step: "\<And>i. \<Gamma>\<turnstile>f i \<rightarrow> f (Suc i)"
    assume f_0: "f 0 = (Await b c, Stuck)" 
    from f_step [of 0] f_0 f_step [of 1]
    show False
      by (fastforce elim: Skip_no_step step_elim_cases)
  qed
qed

lemma not_inf_Fault: "\<not> \<Gamma>\<turnstile>(c,Fault x) \<rightarrow> \<dots>(\<infinity>)"
proof (induct c)
  case Skip
  show ?case
  proof (rule not_infI)
    fix f
    assume f_step: "\<And>i. \<Gamma>\<turnstile>f i \<rightarrow> f (Suc i)"
    assume f_0: "f 0 = (Skip, Fault x)" 
    from f_step [of 0] f_0
    show False
      by (auto elim: Skip_no_step)
  qed
next
  case (Basic g) 
  thus ?case 
  proof (rule not_infI)
    fix f
    assume f_step: "\<And>i. \<Gamma>\<turnstile>f i \<rightarrow> f (Suc i)"
    assume f_0: "f 0 = (Basic g, Fault x)" 
    from f_step [of 0] f_0 f_step [of 1]
    show False
      by (fastforce elim: Skip_no_step step_elim_cases)
  qed
next
  case (Spec r) 
  thus ?case 
  proof (rule not_infI)
    fix f
    assume f_step: "\<And>i. \<Gamma>\<turnstile>f i \<rightarrow> f (Suc i)"
    assume f_0: "f 0 = (Spec r, Fault x)" 
    from f_step [of 0] f_0 f_step [of 1]
    show False
      by (fastforce elim: Skip_no_step step_elim_cases)
  qed
next
  case (Seq c\<^sub>1 c\<^sub>2)
  show ?case
  proof 
    assume "\<Gamma>\<turnstile> (Seq c\<^sub>1 c\<^sub>2, Fault x) \<rightarrow> \<dots>(\<infinity>)"
    from split_inf_Seq [OF this] Seq.hyps
    show False
      by (auto dest: steps_Fault_prop)
  qed
next
  case (Cond b c\<^sub>1 c\<^sub>2) 
  show ?case 
  proof (rule not_infI)
    fix f
    assume f_step: "\<And>i. \<Gamma>\<turnstile>f i \<rightarrow> f (Suc i)"
    assume f_0: "f 0 = (Cond b c\<^sub>1 c\<^sub>2, Fault x)" 
    from f_step [of 0] f_0 f_step [of 1]
    show False
      by (fastforce elim: Skip_no_step step_elim_cases)
  qed
next
  case (While b c) 
  show ?case 
  proof (rule not_infI)
    fix f
    assume f_step: "\<And>i. \<Gamma>\<turnstile>f i \<rightarrow> f (Suc i)"
    assume f_0: "f 0 = (While b c, Fault x)" 
    from f_step [of 0] f_0 f_step [of 1]
    show False
      by (fastforce elim: Skip_no_step step_elim_cases)
  qed
next
  case (Call p) 
  show ?case 
  proof (rule not_infI)
    fix f
    assume f_step: "\<And>i. \<Gamma>\<turnstile>f i \<rightarrow> f (Suc i)"
    assume f_0: "f 0 = (Call p, Fault x)" 
    from f_step [of 0] f_0 f_step [of 1]
    show False
      by (fastforce elim: Skip_no_step step_elim_cases)
  qed
next
  case (DynCom d) 
  show ?case 
  proof (rule not_infI)
    fix f
    assume f_step: "\<And>i. \<Gamma>\<turnstile>f i \<rightarrow> f (Suc i)"
    assume f_0: "f 0 = (DynCom d, Fault x)" 
    from f_step [of 0] f_0 f_step [of 1]
    show False
      by (fastforce elim: Skip_no_step step_elim_cases)
  qed
next
  case (Guard m g c)
  show ?case 
  proof (rule not_infI)
    fix f
    assume f_step: "\<And>i. \<Gamma>\<turnstile>f i \<rightarrow> f (Suc i)"
    assume f_0: "f 0 = (Guard m g c, Fault x)" 
    from f_step [of 0] f_0 f_step [of 1]
    show False
      by (fastforce elim: Skip_no_step step_elim_cases)
  qed
next
  case Throw
  show ?case 
  proof (rule not_infI)
    fix f
    assume f_step: "\<And>i. \<Gamma>\<turnstile>f i \<rightarrow> f (Suc i)"
    assume f_0: "f 0 = (Throw, Fault x)" 
    from f_step [of 0] f_0 f_step [of 1]
    show False
      by (fastforce elim: Skip_no_step step_elim_cases)
  qed
next
  case (Catch c\<^sub>1 c\<^sub>2)
  show ?case
  proof 
    assume "\<Gamma>\<turnstile> (Catch c\<^sub>1 c\<^sub>2, Fault x) \<rightarrow> \<dots>(\<infinity>)"
    from split_inf_Catch [OF this] Catch.hyps
    show False
      by (auto dest: steps_Fault_prop)
  qed  
next
  case (Await b c) 
  show ?case 
  proof (rule not_infI)
    fix f
    assume f_step: "\<And>i. \<Gamma>\<turnstile>f i \<rightarrow> f (Suc i)"
    assume f_0: "f 0 = (Await b c, Fault x)" 
    from f_step [of 0] f_0 f_step [of 1]
    show False
      by (fastforce elim: Skip_no_step step_elim_cases)
  qed
qed

lemma not_inf_Abrupt: "\<not> \<Gamma>\<turnstile>(c,Abrupt s) \<rightarrow> \<dots>(\<infinity>)"
proof (induct c)
  case Skip
  show ?case
  proof (rule not_infI)
    fix f
    assume f_step: "\<And>i. \<Gamma>\<turnstile>f i \<rightarrow> f (Suc i)"
    assume f_0: "f 0 = (Skip, Abrupt s)" 
    from f_step [of 0] f_0
    show False
      by (auto elim: Skip_no_step)
  qed
next
  case (Basic g) 
  thus ?case 
  proof (rule not_infI)
    fix f
    assume f_step: "\<And>i. \<Gamma>\<turnstile>f i \<rightarrow> f (Suc i)"
    assume f_0: "f 0 = (Basic g, Abrupt s)" 
    from f_step [of 0] f_0 f_step [of 1]
    show False
      by (fastforce elim: Skip_no_step step_elim_cases)
  qed
next
  case (Spec r) 
  thus ?case 
  proof (rule not_infI)
    fix f
    assume f_step: "\<And>i. \<Gamma>\<turnstile>f i \<rightarrow> f (Suc i)"
    assume f_0: "f 0 = (Spec r, Abrupt s)" 
    from f_step [of 0] f_0 f_step [of 1]
    show False
      by (fastforce elim: Skip_no_step step_elim_cases)
  qed
next
  case (Seq c\<^sub>1 c\<^sub>2)
  show ?case
  proof 
    assume "\<Gamma>\<turnstile> (Seq c\<^sub>1 c\<^sub>2, Abrupt s) \<rightarrow> \<dots>(\<infinity>)"
    from split_inf_Seq [OF this] Seq.hyps
    show False
      by (auto dest: steps_Abrupt_prop)
  qed
next
  case (Cond b c\<^sub>1 c\<^sub>2) 
  show ?case 
  proof (rule not_infI)
    fix f
    assume f_step: "\<And>i. \<Gamma>\<turnstile>f i \<rightarrow> f (Suc i)"
    assume f_0: "f 0 = (Cond b c\<^sub>1 c\<^sub>2, Abrupt s)" 
    from f_step [of 0] f_0 f_step [of 1]
    show False
      by (fastforce elim: Skip_no_step step_elim_cases)
  qed
next
  case (While b c) 
  show ?case 
  proof (rule not_infI)
    fix f
    assume f_step: "\<And>i. \<Gamma>\<turnstile>f i \<rightarrow> f (Suc i)"
    assume f_0: "f 0 = (While b c, Abrupt s)" 
    from f_step [of 0] f_0 f_step [of 1]
    show False
      by (fastforce elim: Skip_no_step step_elim_cases)
  qed
next
  case (Call p) 
  show ?case 
  proof (rule not_infI)
    fix f
    assume f_step: "\<And>i. \<Gamma>\<turnstile>f i \<rightarrow> f (Suc i)"
    assume f_0: "f 0 = (Call p, Abrupt s)" 
    from f_step [of 0] f_0 f_step [of 1]
    show False
      by (fastforce elim: Skip_no_step step_elim_cases)
  qed
next
  case (DynCom d) 
  show ?case 
  proof (rule not_infI)
    fix f
    assume f_step: "\<And>i. \<Gamma>\<turnstile>f i \<rightarrow> f (Suc i)"
    assume f_0: "f 0 = (DynCom d, Abrupt s)" 
    from f_step [of 0] f_0 f_step [of 1]
    show False
      by (fastforce elim: Skip_no_step step_elim_cases)
  qed
next
  case (Guard m g c)
  show ?case 
  proof (rule not_infI)
    fix f
    assume f_step: "\<And>i. \<Gamma>\<turnstile>f i \<rightarrow> f (Suc i)"
    assume f_0: "f 0 = (Guard m g c, Abrupt s)" 
    from f_step [of 0] f_0 f_step [of 1]
    show False
      by (fastforce elim: Skip_no_step step_elim_cases)
  qed
next
  case Throw
  show ?case 
  proof (rule not_infI)
    fix f
    assume f_step: "\<And>i. \<Gamma>\<turnstile>f i \<rightarrow> f (Suc i)"
    assume f_0: "f 0 = (Throw, Abrupt s)" 
    from f_step [of 0] f_0 f_step [of 1]
    show False
      by (fastforce elim: Skip_no_step step_elim_cases)
  qed
next
  case (Catch c\<^sub>1 c\<^sub>2)
  show ?case
  proof 
    assume "\<Gamma>\<turnstile> (Catch c\<^sub>1 c\<^sub>2, Abrupt s) \<rightarrow> \<dots>(\<infinity>)"
    from split_inf_Catch [OF this] Catch.hyps
    show False
      by (auto dest: steps_Abrupt_prop)
  qed  
case (Await b c) 
  show ?case 
  proof (rule not_infI)
    fix f
    assume f_step: "\<And>i. \<Gamma>\<turnstile>f i \<rightarrow> f (Suc i)"
    assume f_0: "f 0 = (Await b c, Abrupt s)" 
    from f_step [of 0] f_0 f_step [of 1]
    show False
      by (fastforce elim: Skip_no_step step_elim_cases)
  qed
qed


theorem terminates_impl_no_infinite_computation:
  assumes termi: "\<Gamma>\<turnstile>c \<down> s"
  shows "\<not> \<Gamma>\<turnstile>(c,s) \<rightarrow> \<dots>(\<infinity>)"
using termi
proof (induct)
  case (Skip s) thus ?case
  proof (rule not_infI)
    fix f
    assume f_step: "\<And>i. \<Gamma>\<turnstile>f i \<rightarrow> f (Suc i)"
    assume f_0: "f 0 = (Skip, Normal s)" 
    from f_step [of 0] f_0
    show False
      by (auto elim: Skip_no_step)
  qed
next
  case (Basic g s) 
  thus ?case 
  proof (rule not_infI)
    fix f
    assume f_step: "\<And>i. \<Gamma>\<turnstile>f i \<rightarrow> f (Suc i)"
    assume f_0: "f 0 = (Basic g, Normal s)" 
    from f_step [of 0] f_0 f_step [of 1]
    show False
      by (fastforce elim: Skip_no_step step_elim_cases)
  qed
next
  case (Spec r s) 
  thus ?case 
  proof (rule not_infI)
    fix f
    assume f_step: "\<And>i. \<Gamma>\<turnstile>f i \<rightarrow> f (Suc i)"
    assume f_0: "f 0 = (Spec r, Normal s)" 
    from f_step [of 0] f_0 f_step [of 1]
    show False
      by (fastforce elim: Skip_no_step step_elim_cases)
  qed
next
  case (Guard s g c m)
  have g: "s \<in> g" by fact
  have hyp: "\<not> \<Gamma>\<turnstile> (c, Normal s) \<rightarrow> \<dots>(\<infinity>)" by fact
  show ?case
  proof (rule not_infI)
    fix f
    assume f_step: "\<And>i. \<Gamma>\<turnstile>f i \<rightarrow> f (Suc i)"
    assume f_0: "f 0 = (Guard m g c, Normal s)" 
    from f_step [of 0] f_0  g
    have "f 1 = (c,Normal s)"
      by (fastforce elim: step_elim_cases)
    with f_step
    have "\<Gamma>\<turnstile> (c, Normal s) \<rightarrow> \<dots>(\<infinity>)"
      apply (simp add: inf_def)
      apply (rule_tac x="\<lambda>i. f (Suc i)" in exI)
      by simp
    with hyp show False ..
  qed
next
  case (GuardFault s g m c)
  have g: "s \<notin> g" by fact
  show ?case
  proof (rule not_infI)
    fix f
    assume f_step: "\<And>i. \<Gamma>\<turnstile>f i \<rightarrow> f (Suc i)"
    assume f_0: "f 0 = (Guard m g c, Normal s)" 
    from g f_step [of 0] f_0 f_step [of 1]
    show False
      by (fastforce elim: Skip_no_step step_elim_cases)
  qed
next
  case (Fault c m) 
  thus ?case
    by (rule not_inf_Fault)
next
  case (Seq c\<^sub>1 s c\<^sub>2)
  show ?case
  proof 
    assume "\<Gamma>\<turnstile> (Seq c\<^sub>1 c\<^sub>2, Normal s) \<rightarrow> \<dots>(\<infinity>)"
    from split_inf_Seq [OF this] Seq.hyps
    show False
      by (auto intro: steps_Skip_impl_exec)
  qed
next
  case (CondTrue s b c1 c2)
  have b: "s \<in> b" by fact
  have hyp_c1: "\<not> \<Gamma>\<turnstile> (c1, Normal s) \<rightarrow> \<dots>(\<infinity>)" by fact
  show ?case
  proof (rule not_infI)
    fix f
    assume f_step: "\<And>i. \<Gamma>\<turnstile>f i \<rightarrow> f (Suc i)"
    assume f_0: "f 0 = (Cond b c1 c2, Normal s)" 
    from b f_step [of 0] f_0
    have "f 1 = (c1,Normal s)"
      by (auto elim: step_Normal_elim_cases)
    with f_step
    have "\<Gamma>\<turnstile> (c1, Normal s) \<rightarrow> \<dots>(\<infinity>)"
      apply (simp add: inf_def)
      apply (rule_tac x="\<lambda>i. f (Suc i)" in exI)
      by simp
    with hyp_c1 show False by simp
  qed    
next
  case (CondFalse s b c2 c1)
  have b: "s \<notin> b" by fact
  have hyp_c2: "\<not> \<Gamma>\<turnstile> (c2, Normal s) \<rightarrow> \<dots>(\<infinity>)" by fact
  show ?case
  proof (rule not_infI)
    fix f
    assume f_step: "\<And>i. \<Gamma>\<turnstile>f i \<rightarrow> f (Suc i)"
    assume f_0: "f 0 = (Cond b c1 c2, Normal s)" 
    from b f_step [of 0] f_0
    have "f 1 = (c2,Normal s)"
      by (auto elim: step_Normal_elim_cases)
    with f_step
    have "\<Gamma>\<turnstile> (c2, Normal s) \<rightarrow> \<dots>(\<infinity>)"
      apply (simp add: inf_def)
      apply (rule_tac x="\<lambda>i. f (Suc i)" in exI)
      by simp
    with hyp_c2 show False by simp
  qed
next    
  case (WhileTrue s b c)
  have b: "s \<in> b" by fact
  have hyp_c: "\<not> \<Gamma>\<turnstile> (c, Normal s) \<rightarrow> \<dots>(\<infinity>)" by fact
  have hyp_w: "\<forall>s'. \<Gamma>\<turnstile> \<langle>c,Normal s\<rangle> \<Rightarrow> s' \<longrightarrow> 
                     \<Gamma>\<turnstile>While b c \<down> s' \<and> \<not> \<Gamma>\<turnstile> (While b c, s') \<rightarrow> \<dots>(\<infinity>)" by fact
  have not_inf_Seq: "\<not> \<Gamma>\<turnstile> (Seq c (While b c), Normal s) \<rightarrow> \<dots>(\<infinity>)"
  proof 
    assume "\<Gamma>\<turnstile> (Seq c (While b c), Normal s) \<rightarrow> \<dots>(\<infinity>)"
    from split_inf_Seq [OF this] hyp_c hyp_w show False
      by (auto intro: steps_Skip_impl_exec)
  qed
  show ?case
  proof 
    assume "\<Gamma>\<turnstile> (While b c, Normal s) \<rightarrow> \<dots>(\<infinity>)"
    then obtain f where
      f_step: "\<And>i. \<Gamma>\<turnstile>f i \<rightarrow> f (Suc i)" and
      f_0: "f 0 = (While b c, Normal s)" 
      by (auto simp add: inf_def)
    from f_step [of 0] f_0 b
    have "f 1 = (Seq c (While b c),Normal s)"
      by (auto elim: step_Normal_elim_cases)
    with f_step
    have "\<Gamma>\<turnstile> (Seq c (While b c), Normal s) \<rightarrow> \<dots>(\<infinity>)"
      apply (simp add: inf_def)
      apply (rule_tac x="\<lambda>i. f (Suc i)" in exI)
      by simp
    with not_inf_Seq show False by simp
  qed
next
  case (WhileFalse s b c)
  have b: "s \<notin> b" by fact
  show ?case
  proof (rule not_infI)
    fix f
    assume f_step: "\<And>i. \<Gamma>\<turnstile>f i \<rightarrow> f (Suc i)"
    assume f_0: "f 0 = (While b c, Normal s)" 
    from b f_step [of 0] f_0 f_step [of 1]
    show False
      by (fastforce elim: Skip_no_step step_elim_cases)
  qed
next
  case (Call p bdy s)
  have bdy: "\<Gamma> p = Some bdy" by fact
  have hyp: "\<not> \<Gamma>\<turnstile> (bdy, Normal s) \<rightarrow> \<dots>(\<infinity>)" by fact
  show ?case
  proof (rule not_infI)
    fix f
    assume f_step: "\<And>i. \<Gamma>\<turnstile>f i \<rightarrow> f (Suc i)"
    assume f_0: "f 0 = (Call p, Normal s)" 
    from bdy f_step [of 0] f_0
    have "f 1 = (bdy,Normal s)"
      by (auto elim: step_Normal_elim_cases)
    with f_step
    have "\<Gamma>\<turnstile> (bdy, Normal s) \<rightarrow> \<dots>(\<infinity>)"
      apply (simp add: inf_def)
      apply (rule_tac x="\<lambda>i. f (Suc i)" in exI)
      by simp
    with hyp show False by simp
  qed    
next
  case (CallUndefined p s)
  have no_bdy: "\<Gamma> p = None" by fact
  show ?case
  proof (rule not_infI)
    fix f
    assume f_step: "\<And>i. \<Gamma>\<turnstile>f i \<rightarrow> f (Suc i)"
    assume f_0: "f 0 = (Call p, Normal s)" 
    from no_bdy f_step [of 0] f_0 f_step [of 1]
    show False
      by (fastforce elim: Skip_no_step step_elim_cases)
  qed
next
  case (Stuck c)
  show ?case
    by (rule not_inf_Stuck)
next
  case (DynCom c s)
  have hyp: "\<not> \<Gamma>\<turnstile> (c s, Normal s) \<rightarrow> \<dots>(\<infinity>)" by fact
  show ?case
  proof (rule not_infI)
    fix f
    assume f_step: "\<And>i. \<Gamma>\<turnstile>f i \<rightarrow> f (Suc i)"
    assume f_0: "f 0 = (DynCom c, Normal s)" 
    from f_step [of 0] f_0
    have "f (Suc 0) = (c s, Normal s)"
      by (auto elim: step_elim_cases)
    with f_step have "\<Gamma>\<turnstile> (c s, Normal s) \<rightarrow> \<dots>(\<infinity>)"
      apply (simp add: inf_def)
      apply (rule_tac x="\<lambda>i. f (Suc i)" in exI)
      by simp
    with hyp
    show False by simp
  qed
next (\<Gamma>,c) \<propto> clist
  case (Throw s) thus ?case
  proof (rule not_infI)
    fix f
    assume f_step: "\<And>i. \<Gamma>\<turnstile>f i \<rightarrow> f (Suc i)"
    assume f_0: "f 0 = (Throw, Normal s)" 
    from f_step [of 0] f_0
    show False
      by (auto elim: step_elim_cases)
  qed  
next
  case (Abrupt c)
  show ?case
    by (rule not_inf_Abrupt)
next
  case (Catch c\<^sub>1 s c\<^sub>2)
  show ?case
  proof 
    assume "\<Gamma>\<turnstile> (Catch c\<^sub>1 c\<^sub>2, Normal s) \<rightarrow> \<dots>(\<infinity>)"
    from split_inf_Catch [OF this] Catch.hyps
    show False
      by (auto intro: steps_Throw_impl_exec)
  qed
next
  case (AwaitTrue s b c)
  have b: "s \<in> b" by fact
  show ?case
  proof (rule not_infI)
    fix f
    assume f_step: "\<And>i. \<Gamma>\<turnstile>f i \<rightarrow> f (Suc i)"
    assume f_0: "f 0 = (Await b c, Normal s)" 
    from b f_step [of 0] f_0 f_step [of 1]
    show False
      by (fastforce elim: Skip_no_step step_elim_cases)
  qed
qed


definition
 termi_call_steps :: "('s,'p,'f,'e) body \<Rightarrow> (('s \<times> 'p) \<times> ('s \<times> 'p))set"
where
"termi_call_steps \<Gamma> =
 {((t,q),(s,p)). \<Gamma>\<turnstile>Call p\<down>Normal s \<and> 
       (\<exists>c. \<Gamma>\<turnstile>(Call p,Normal s) \<rightarrow>\<^sup>+ (c,Normal t) \<and> redex c = Call q)}"


primrec subst_redex:: "('s,'p,'f,'e)com \<Rightarrow> ('s,'p,'f,'e)com \<Rightarrow> ('s,'p,'f,'e)com"
where
"subst_redex Skip c = c" |
"subst_redex (Basic f) c = c" |
"subst_redex (Spec r) c = c" |
"subst_redex (Seq c\<^sub>1 c\<^sub>2) c  = Seq (subst_redex c\<^sub>1 c) c\<^sub>2" |
"subst_redex (Cond b c\<^sub>1 c\<^sub>2) c = c" |
"subst_redex (While b c') c = c" |
"subst_redex (Await b c') c = c" |
"subst_redex (Call p) c = c" |
"subst_redex (DynCom d) c = c" |
"subst_redex (Guard f b c') c = c" |
"subst_redex (Throw) c = c" |
"subst_redex (Catch c\<^sub>1 c\<^sub>2) c = Catch (subst_redex c\<^sub>1 c) c\<^sub>2"

lemma subst_redex_redex:
  "subst_redex c (redex c) = c"
  by (induct c) auto

lemma redex_subst_redex: "redex (subst_redex c r) = redex r"
  by (induct c) auto
  
lemma step_redex':
  shows "\<Gamma>\<turnstile>(redex c,s) \<rightarrow> (r',s') \<Longrightarrow> \<Gamma>\<turnstile>(c,s) \<rightarrow> (subst_redex c r',s')"
by (induct c) (auto intro: step.Seq step.Catch)


lemma step_redex:
  shows "\<Gamma>\<turnstile>(r,s) \<rightarrow> (r',s') \<Longrightarrow> \<Gamma>\<turnstile>(subst_redex c r,s) \<rightarrow> (subst_redex c r',s')"
by (induct c) (auto intro: step.Seq step.Catch)

lemma steps_redex:
  assumes steps: "\<Gamma>\<turnstile> (r, s) \<rightarrow>\<^sup>* (r', s')"
  shows "\<And>c. \<Gamma>\<turnstile>(subst_redex c r,s) \<rightarrow>\<^sup>* (subst_redex c r',s')"
using steps
proof (induct rule: converse_rtranclp_induct2 [case_names Refl Trans])
  case Refl 
  show "\<Gamma>\<turnstile> (subst_redex c r', s') \<rightarrow>\<^sup>* (subst_redex c r', s')"
    by simp
next
  case (Trans r s r'' s'')
  have "\<Gamma>\<turnstile> (r, s) \<rightarrow> (r'', s'')" by fact
  from step_redex [OF this]
  have "\<Gamma>\<turnstile> (subst_redex c r, s) \<rightarrow> (subst_redex c r'', s'')".
  also  
  have "\<Gamma>\<turnstile> (subst_redex c r'', s'') \<rightarrow>\<^sup>* (subst_redex c r', s')" by fact
  finally show ?case .
qed

ML {*
  ML_Thms.bind_thm ("trancl_induct2", Split_Rule.split_rule @{context}
    (Rule_Insts.read_instantiate @{context}
      [((("a", 0), Position.none), "(aa, ab)"), ((("b", 0), Position.none), "(ba, bb)")] []
      @{thm trancl_induct}));
*}

lemma steps_redex':
  assumes steps: "\<Gamma>\<turnstile> (r, s) \<rightarrow>\<^sup>+ (r', s')"
  shows "\<And>c. \<Gamma>\<turnstile>(subst_redex c r,s) \<rightarrow>\<^sup>+ (subst_redex c r',s')"
using steps
proof (induct rule: tranclp_induct2 [consumes 1,case_names Step Trans])
  case (Step r' s')
  have "\<Gamma>\<turnstile> (r, s) \<rightarrow> (r', s')" by fact
  then have "\<Gamma>\<turnstile> (subst_redex c r, s) \<rightarrow> (subst_redex c r', s')"
    by (rule step_redex)
  then show "\<Gamma>\<turnstile> (subst_redex c r, s) \<rightarrow>\<^sup>+ (subst_redex c r', s')"..
next
  case (Trans r' s' r'' s'')
  have "\<Gamma>\<turnstile> (subst_redex c r, s) \<rightarrow>\<^sup>+ (subst_redex c r', s')" by fact
  also
  have "\<Gamma>\<turnstile> (r', s') \<rightarrow> (r'', s'')" by fact
  hence "\<Gamma>\<turnstile> (subst_redex c r', s') \<rightarrow> (subst_redex c r'', s'')"
    by (rule step_redex)
  finally show "\<Gamma>\<turnstile> (subst_redex c r, s) \<rightarrow>\<^sup>+ (subst_redex c r'', s'')" .
qed

primrec seq:: "(nat \<Rightarrow> ('s,'p,'f,'e)com) \<Rightarrow> 'p \<Rightarrow> nat \<Rightarrow> ('s,'p,'f,'e)com"
where
"seq c p 0 = Call p" |
"seq c p (Suc i) = subst_redex (seq c p i) (c i)"


lemma renumber':
  assumes f: "\<forall>i. (a,f i) \<in> r\<^sup>* \<and> (f i,f(Suc i)) \<in> r" 
  assumes a_b: "(a,b) \<in> r\<^sup>*" 
  shows "b = f 0 \<Longrightarrow> (\<exists>f. f 0 = a \<and> (\<forall>i. (f i, f(Suc i)) \<in> r))"
using a_b
proof (induct rule: converse_rtrancl_induct [consumes 1])
  assume "b = f 0"
  with f show "\<exists>f. f 0 = b \<and> (\<forall>i. (f i, f (Suc i)) \<in> r)"
    by blast
next
  fix a z
  assume a_z: "(a, z) \<in> r" and "(z, b) \<in> r\<^sup>*" 
  assume "b = f 0 \<Longrightarrow> \<exists>f. f 0 = z \<and> (\<forall>i. (f i, f (Suc i)) \<in> r)"
         "b = f 0"
  then obtain f where f0: "f 0 = z" and seq: "\<forall>i. (f i, f (Suc i)) \<in> r"
    by iprover
  {
    fix i have "((\<lambda>i. case i of 0 \<Rightarrow> a | Suc i \<Rightarrow> f i) i, f i) \<in> r"
      using seq a_z f0
      by (cases i) auto
  }
  then
  show "\<exists>f. f 0 = a \<and> (\<forall>i. (f i, f (Suc i)) \<in> r)"
    by - (rule exI [where x="\<lambda>i. case i of 0 \<Rightarrow> a | Suc i \<Rightarrow> f i"],simp)
qed

lemma renumber:
 "\<forall>i. (a,f i) \<in> r\<^sup>* \<and> (f i,f(Suc i)) \<in> r 
 \<Longrightarrow> \<exists>f. f 0 = a \<and> (\<forall>i. (f i, f(Suc i)) \<in> r)"
  by (blast dest:renumber')

lemma lem:
  "\<forall>y. r\<^sup>+\<^sup>+ a y \<longrightarrow> P a \<longrightarrow> P y 
   \<Longrightarrow> ((b,a) \<in> {(y,x). P x \<and> r x y}\<^sup>+) = ((b,a) \<in> {(y,x). P x \<and> r\<^sup>+\<^sup>+ x y})"
apply(rule iffI)
 apply clarify
 apply(erule trancl_induct)
  apply blast
 apply(blast intro:tranclp_trans)
apply clarify
apply(erule tranclp_induct)
 apply blast
apply(blast intro:trancl_trans)
done

corollary terminates_impl_no_infinite_trans_computation:
 assumes terminates: "\<Gamma>\<turnstile>c\<down>s"
 shows "\<not>(\<exists>f. f 0 = (c,s) \<and> (\<forall>i. \<Gamma>\<turnstile>f i \<rightarrow>\<^sup>+ f(Suc i)))"
proof -
  have "wf({(y,x). \<Gamma>\<turnstile>(c,s) \<rightarrow>\<^sup>* x \<and> \<Gamma>\<turnstile>x \<rightarrow> y}\<^sup>+)"
  proof (rule wf_trancl)
    show "wf {(y, x). \<Gamma>\<turnstile>(c,s) \<rightarrow>\<^sup>* x \<and> \<Gamma>\<turnstile>x \<rightarrow> y}"
    proof (simp only: wf_iff_no_infinite_down_chain,clarify,simp)
      fix f
      assume "\<forall>i. \<Gamma>\<turnstile>(c,s) \<rightarrow>\<^sup>* f i \<and> \<Gamma>\<turnstile>f i \<rightarrow> f (Suc i)"
      hence "\<exists>f. f (0::nat) = (c,s) \<and> (\<forall>i. \<Gamma>\<turnstile>f i \<rightarrow> f (Suc i))"
        by (rule renumber [to_pred])
      moreover from terminates_impl_no_infinite_computation [OF terminates]
      have "\<not> (\<exists>f. f (0::nat) = (c, s) \<and> (\<forall>i. \<Gamma>\<turnstile>f i \<rightarrow> f (Suc i)))"
        by (simp add: inf_def)
      ultimately show False
        by simp
    qed
  qed
  hence "\<not> (\<exists>f. \<forall>i. (f (Suc i), f i)
                 \<in> {(y, x). \<Gamma>\<turnstile>(c, s) \<rightarrow>\<^sup>* x \<and> \<Gamma>\<turnstile>x \<rightarrow> y}\<^sup>+)"
    by (simp add: wf_iff_no_infinite_down_chain)
  thus ?thesis
  proof (rule contrapos_nn)
    assume "\<exists>f. f (0::nat) = (c, s) \<and> (\<forall>i. \<Gamma>\<turnstile>f i \<rightarrow>\<^sup>+ f (Suc i))"
    then obtain f where
      f0: "f 0 = (c, s)" and
      seq: "\<forall>i. \<Gamma>\<turnstile>f i \<rightarrow>\<^sup>+ f (Suc i)"
      by iprover
    show 
      "\<exists>f. \<forall>i. (f (Suc i), f i) \<in> {(y, x). \<Gamma>\<turnstile>(c, s) \<rightarrow>\<^sup>* x \<and> \<Gamma>\<turnstile>x \<rightarrow> y}\<^sup>+"
    proof (rule exI [where x=f],rule allI)
      fix i
      show "(f (Suc i), f i) \<in> {(y, x). \<Gamma>\<turnstile>(c, s) \<rightarrow>\<^sup>* x \<and> \<Gamma>\<turnstile>x \<rightarrow> y}\<^sup>+"
      proof -   
        {
          fix i have "\<Gamma>\<turnstile>(c,s) \<rightarrow>\<^sup>* f i"
          proof (induct i)
            case 0 show "\<Gamma>\<turnstile>(c, s) \<rightarrow>\<^sup>* f 0"
              by (simp add: f0)
          next
            case (Suc n)
            have "\<Gamma>\<turnstile>(c, s) \<rightarrow>\<^sup>* f n"  by fact
            with seq show "\<Gamma>\<turnstile>(c, s) \<rightarrow>\<^sup>* f (Suc n)"
              by (blast intro: tranclp_into_rtranclp rtranclp_trans)
          qed
        }
        hence "\<Gamma>\<turnstile>(c,s) \<rightarrow>\<^sup>* f i"
          by iprover
        with seq have
          "(f (Suc i), f i) \<in> {(y, x). \<Gamma>\<turnstile>(c, s) \<rightarrow>\<^sup>* x \<and> \<Gamma>\<turnstile>x \<rightarrow>\<^sup>+ y}"
          by clarsimp
        moreover 
        have "\<forall>y. \<Gamma>\<turnstile>f i \<rightarrow>\<^sup>+ y\<longrightarrow>\<Gamma>\<turnstile>(c, s) \<rightarrow>\<^sup>* f i\<longrightarrow>\<Gamma>\<turnstile>(c, s) \<rightarrow>\<^sup>* y"
          by (blast intro: tranclp_into_rtranclp rtranclp_trans)
        ultimately 
        show ?thesis 
          by (subst lem )
      qed
    qed
  qed
qed

theorem wf_termi_call_steps: "wf (termi_call_steps \<Gamma>)"
proof (simp only: termi_call_steps_def wf_iff_no_infinite_down_chain,
       clarify,simp)
  fix f
  assume inf: "\<forall>i. (\<lambda>(t, q) (s, p).
                \<Gamma>\<turnstile>Call p \<down> Normal s \<and>
                (\<exists>c. \<Gamma>\<turnstile> (Call p, Normal s) \<rightarrow>\<^sup>+ (c, Normal t) \<and> redex c = Call q))
             (f (Suc i)) (f i)"
  def s\<equiv>"\<lambda>i::nat. fst (f i)" 
  def p\<equiv>"\<lambda>i::nat. snd (f i)::'b"
  from inf
  have inf': "\<forall>i. \<Gamma>\<turnstile>Call (p i) \<down> Normal (s i) \<and>
               (\<exists>c. \<Gamma>\<turnstile> (Call (p i), Normal (s i)) \<rightarrow>\<^sup>+ (c, Normal (s (i+1))) \<and> 
                    redex c = Call (p (i+1)))"
    apply -
    apply (rule allI)
    apply (erule_tac x=i in allE)
    apply (auto simp add: s_def p_def)
    done
  show False
  proof -
    from inf'
    have "\<exists>c. \<forall>i. \<Gamma>\<turnstile>Call (p i) \<down> Normal (s i) \<and>
               \<Gamma>\<turnstile> (Call (p i), Normal (s i)) \<rightarrow>\<^sup>+ (c i, Normal (s (i+1))) \<and> 
                    redex (c i) = Call (p (i+1))"
      apply -
      apply (rule choice)
      by blast
    then obtain c where
      termi_c: "\<forall>i. \<Gamma>\<turnstile>Call (p i) \<down> Normal (s i)" and
      steps_c: "\<forall>i. \<Gamma>\<turnstile> (Call (p i), Normal (s i)) \<rightarrow>\<^sup>+ (c i, Normal (s (i+1)))" and
      red_c:   "\<forall>i. redex (c i) = Call (p (i+1))"
      by auto
    def g\<equiv>"\<lambda>i. (seq c (p 0) i,Normal (s i)::('a,'c) xstate)"
    from red_c [rule_format, of 0]
    have "g 0 = (Call (p 0), Normal (s 0))"
      by (simp add: g_def)
    moreover
    {
      fix i
      have "redex (seq c (p 0) i) = Call (p i)"
        by (induct i) (auto simp add: redex_subst_redex red_c)
      from this [symmetric]
      have "subst_redex (seq c (p 0) i) (Call (p i)) = (seq c (p 0) i)"
        by (simp add: subst_redex_redex)
    } note subst_redex_seq = this
    have "\<forall>i. \<Gamma>\<turnstile> (g i) \<rightarrow>\<^sup>+ (g (i+1))"
    proof 
      fix i
      from steps_c [rule_format, of i]
      have "\<Gamma>\<turnstile> (Call (p i), Normal (s i)) \<rightarrow>\<^sup>+ (c i, Normal (s (i + 1)))".
      from steps_redex' [OF this, of "(seq c (p 0) i)"]
      have "\<Gamma>\<turnstile> (subst_redex (seq c (p 0) i) (Call (p i)), Normal (s i)) \<rightarrow>\<^sup>+
                (subst_redex (seq c (p 0) i) (c i), Normal (s (i + 1)))" .
      hence "\<Gamma>\<turnstile> (seq c (p 0) i, Normal (s i)) \<rightarrow>\<^sup>+ 
                 (seq c (p 0) (i+1), Normal (s (i + 1)))"
        by (simp add: subst_redex_seq)
      thus "\<Gamma>\<turnstile> (g i) \<rightarrow>\<^sup>+ (g (i+1))"
        by (simp add: g_def)
    qed
    moreover
    from terminates_impl_no_infinite_trans_computation [OF termi_c [rule_format, of 0]]
    have "\<not> (\<exists>f. f 0 = (Call (p 0), Normal (s 0)) \<and> (\<forall>i. \<Gamma>\<turnstile> f i \<rightarrow>\<^sup>+ f (Suc i)))" .
    ultimately show False
      by auto
  qed
qed


lemma no_infinite_computation_implies_wf: 
  assumes not_inf: "\<not> \<Gamma>\<turnstile> (c, s) \<rightarrow> \<dots>(\<infinity>)"
  shows "wf {(c2,c1). \<Gamma> \<turnstile> (c,s) \<rightarrow>\<^sup>* c1 \<and> \<Gamma> \<turnstile> c1 \<rightarrow> c2}"
proof (simp only: wf_iff_no_infinite_down_chain,clarify, simp)
  fix f
  assume "\<forall>i. \<Gamma>\<turnstile>(c, s) \<rightarrow>\<^sup>* f i \<and> \<Gamma>\<turnstile>f i \<rightarrow> f (Suc i)"
  hence "\<exists>f. f 0 = (c, s) \<and> (\<forall>i. \<Gamma>\<turnstile>f i \<rightarrow> f (Suc i))"
    by (rule renumber [to_pred])
  moreover from not_inf
  have "\<not> (\<exists>f. f 0 = (c, s) \<and> (\<forall>i. \<Gamma>\<turnstile>f i \<rightarrow> f (Suc i)))"
    by (simp add: inf_def)
  ultimately show False
    by simp
qed

lemma not_final_Stuck_step: "\<not> final (c,Stuck) \<Longrightarrow> \<exists>c' s'. \<Gamma>\<turnstile> (c, Stuck) \<rightarrow> (c',s')"
by (induct c) (fastforce intro: step.intros simp add: final_def)+

lemma not_final_Abrupt_step: 
  "\<not> final (c,Abrupt s) \<Longrightarrow> \<exists>c' s'. \<Gamma>\<turnstile> (c, Abrupt s) \<rightarrow> (c',s')"
by (induct c) (fastforce intro: step.intros simp add: final_def)+

lemma not_final_Fault_step: 
  "\<not> final (c,Fault f) \<Longrightarrow> \<exists>c' s'. \<Gamma>\<turnstile> (c, Fault f) \<rightarrow> (c',s')"
by (induct c) (fastforce intro: step.intros simp add: final_def)+

lemma not_final_Normal_step: 
  "\<not> final (c,Normal s) \<and> ((\<exists>b c1. redex c = Await b c1) \<longrightarrow> \<Gamma>\<turnstile>c \<down> Normal s) \<Longrightarrow> \<exists>c' s'. \<Gamma>\<turnstile> (c, Normal s) \<rightarrow> (c',s')"
proof (induct c) 
  case Skip thus ?case by (simp add: final_def)
next
  case Basic thus ?case by (meson step.Basic)
next
  case (Spec r)
  thus ?case by (meson step.Spec step.SpecStuck)    
next
  case (Seq c\<^sub>1 c\<^sub>2)
  thus ?case by (metis SeqSkip SeqThrow final_def fst_conv redex.simps(4) step.Seq terminates_Normal_elim_cases(5))
next
  case (Cond b c1 c2)
  show ?case
    by (cases "s \<in> b") (fastforce intro: step.intros)+
next
  case (While b c)
  show ?case
    by (cases "s \<in> b") (fastforce intro: step.intros)+
next
  case (Call p)
  show ?case
  by (cases "\<Gamma> p") (fastforce intro: step.intros)+
next
  case DynCom thus ?case by (fastforce intro: step.intros)
next
  case (Guard f g c)
  show ?case
    by (cases "s \<in> g") (fastforce intro: step.intros)+
next
  case Throw
  thus ?case by (fastforce intro: step.intros simp add: final_def)
next
  case (Catch c\<^sub>1 c\<^sub>2)
  thus ?case
    by (cases "final (c\<^sub>1,Normal s)") (fastforce intro: step.intros elim: terminates_Normal_elim_cases simp add: final_def)+
next
  case (Await b c) 
  then obtain ba c1 where x:"(\<exists>ba c1. redex (Await b c) = Await ba c1)" by simp
  then have "\<Gamma>\<turnstile>Await b c \<down> Normal s" using x Await.prems by blast 
  also have "s \<in> b" by (meson `\<Gamma>\<turnstile>Await b c \<down> Normal s` terminates_Normal_elim_cases(12))
  moreover have "\<exists>t. \<Gamma>\<turnstile>\<langle>c, Normal s\<rangle> \<Rightarrow> t" by (meson calculation terminates_Normal_elim_cases(12) terminates_implies_exec) 
  ultimately show ?case using AwaitAbrupt  step.Await by fastforce
qed

lemma final_termi:
"final (c,s) \<Longrightarrow> \<Gamma>\<turnstile>c\<down>s"
  by (cases s) (auto simp add: final_def terminates.intros)

lemma split_computation: 
assumes steps: "\<Gamma>\<turnstile> (c, s) \<rightarrow>\<^sup>* (c\<^sub>f, s\<^sub>f)"
assumes not_final: "\<not> final (c,s)"
assumes final: "final (c\<^sub>f,s\<^sub>f)"
shows "\<exists>c' s'. \<Gamma>\<turnstile> (c, s) \<rightarrow> (c',s') \<and> \<Gamma>\<turnstile> (c', s') \<rightarrow>\<^sup>* (c\<^sub>f, s\<^sub>f)"
using steps not_final final
proof (induct rule: converse_rtranclp_induct2 [case_names Refl Trans])
  case Refl thus ?case by simp
next
  case (Trans c s c' s')
  thus ?case by auto
qed


lemma wf_implies_termi_reach_step_case:
assumes hyp: "\<And>c' s'. \<Gamma>\<turnstile> (c, Normal s) \<rightarrow> (c', s')\<Longrightarrow> \<Gamma>\<turnstile>c' \<down> s'" and
        hyp1:"(\<And>b c1. (redex c = Await b c1) \<Longrightarrow> \<Gamma>\<turnstile>c1 \<down> Normal s \<and> s\<in>b)"
shows "\<Gamma>\<turnstile>c \<down> Normal s"
using hyp hyp1
proof (induct c)
  case Skip show ?case by (fastforce intro: terminates.intros)
next
  case Basic show ?case by (fastforce intro: terminates.intros)
next
  case (Spec r)
  show ?case
    by (cases "\<exists>t. (s,t)\<in>r") (fastforce intro: terminates.intros)+
next
  case (Seq c\<^sub>1 c\<^sub>2)
  have hyp: "\<And>c' s'. \<Gamma>\<turnstile> (Seq c\<^sub>1 c\<^sub>2, Normal s) \<rightarrow> (c', s') \<Longrightarrow> \<Gamma>\<turnstile>c' \<down> s'"
using Seq.prems by blast 
   have hyp': "(\<And>b c1. (redex (Seq c\<^sub>1 c\<^sub>2)  = Await b c1) \<Longrightarrow> \<Gamma>\<turnstile>c1 \<down> Normal s \<and> s\<in>b)" by fact 
  show ?case 
  proof (rule terminates.Seq)
    {
      fix c' s'
      assume step_c\<^sub>1: "\<Gamma>\<turnstile> (c\<^sub>1, Normal s) \<rightarrow> (c', s')"      
      assume red: "(\<And>b c1. (redex c\<^sub>1  = Await b c1) \<Longrightarrow> \<Gamma>\<turnstile>c1 \<down> Normal s \<and> s\<in>b)"
      have "\<Gamma>\<turnstile>c' \<down> s'"
      proof -
        from step_c\<^sub>1
        have "\<Gamma>\<turnstile> (Seq c\<^sub>1 c\<^sub>2, Normal s) \<rightarrow> (Seq c' c\<^sub>2, s')"
          by (simp add: step.Seq)          
        from hyp [OF this]
        have "\<Gamma>\<turnstile>Seq c' c\<^sub>2 \<down> s'".
        thus "\<Gamma>\<turnstile>c'\<down> s'"
          by cases auto
      qed
    } 
    from Seq.hyps (1) [OF this]
    show "\<Gamma>\<turnstile>c\<^sub>1 \<down> Normal s" using terminates_Skip' by (simp add: hyp') 
  next
    show "\<forall>s'. \<Gamma>\<turnstile> \<langle>c\<^sub>1,Normal s\<rangle> \<Rightarrow> s' \<longrightarrow> \<Gamma>\<turnstile>c\<^sub>2 \<down> s'"
    proof (intro allI impI)
      fix s'
      assume exec_c\<^sub>1: "\<Gamma>\<turnstile> \<langle>c\<^sub>1,Normal s\<rangle> \<Rightarrow> s'"
      show "\<Gamma>\<turnstile>c\<^sub>2 \<down> s'"
      proof (cases "final (c\<^sub>1,Normal s)")
        case True
        hence "c\<^sub>1=Skip \<or> c\<^sub>1=Throw"
          by (simp add: final_def)
        thus ?thesis
        proof
          assume Skip: "c\<^sub>1=Skip"
          have s1:"\<Gamma>\<turnstile>(Seq Skip c\<^sub>2,Normal s) \<rightarrow> (c\<^sub>2,Normal s) \<and>\<not> (\<exists>b c1. Seq c\<^sub>1 c\<^sub>2 = Await b c1)"
            by (simp add: step.SeqSkip)          
          from hyp 
          have "\<Gamma>\<turnstile>c\<^sub>2 \<down> Normal s" using local.Skip s1 by blast 
          moreover from exec_c\<^sub>1 Skip
          have "s'=Normal s"
            by (auto elim: exec_Normal_elim_cases)
          ultimately show ?thesis by simp
        next
          assume Throw: "c\<^sub>1=Throw"
          with exec_c\<^sub>1 have "s'=Abrupt s"
            by (auto elim: exec_Normal_elim_cases)
          thus ?thesis
            by auto
        qed
      next
        case False        
        from exec_impl_steps [OF exec_c\<^sub>1]
        obtain c\<^sub>f t where 
          steps_c\<^sub>1: "\<Gamma>\<turnstile> (c\<^sub>1, Normal s) \<rightarrow>\<^sup>* (c\<^sub>f, t)" and
          fin:"(case s' of
                 Abrupt x \<Rightarrow> c\<^sub>f = Throw \<and> t = Normal x
                | _ \<Rightarrow> c\<^sub>f = Skip \<and> t = s')"
          by (fastforce split: xstate.splits)
        with fin have final: "final (c\<^sub>f,t)"
          by (cases s') (auto simp add: final_def)
        from split_computation [OF steps_c\<^sub>1 False this]
        obtain c'' s'' where
          first: "\<Gamma>\<turnstile> (c\<^sub>1, Normal s) \<rightarrow> (c'', s'')" and
          rest: "\<Gamma>\<turnstile> (c'', s'') \<rightarrow>\<^sup>* (c\<^sub>f, t)" 
          by blast
        from step.Seq [OF first]
        have "\<Gamma>\<turnstile> (Seq c\<^sub>1 c\<^sub>2, Normal s) \<rightarrow> (Seq c'' c\<^sub>2, s'')" by auto
        from hyp [OF this]
        have termi_s'': "\<Gamma>\<turnstile>Seq c'' c\<^sub>2 \<down> s''".
        show ?thesis
        proof (cases s'')
          case (Normal x)
          from termi_s'' [simplified Normal]
          have termi_c\<^sub>2: "\<forall>t. \<Gamma>\<turnstile> \<langle>c'',Normal x\<rangle> \<Rightarrow> t \<longrightarrow> \<Gamma>\<turnstile>c\<^sub>2 \<down> t"
            by cases
          show ?thesis
          proof (cases "\<exists>x'. s'=Abrupt x'")
            case False
            with fin obtain "c\<^sub>f=Skip" "t=s'"
              by (cases s') auto
            from steps_Skip_impl_exec [OF rest [simplified this]] Normal
            have "\<Gamma>\<turnstile> \<langle>c'',Normal x\<rangle> \<Rightarrow> s'"
              by simp
            from termi_c\<^sub>2 [rule_format, OF this]
            show "\<Gamma>\<turnstile>c\<^sub>2 \<down> s'" .
          next
            case True
            with fin obtain x' where s': "s'=Abrupt x'" and "c\<^sub>f=Throw" "t=Normal x'"
              by auto
            from steps_Throw_impl_exec [OF rest [simplified this]] Normal 
            have "\<Gamma>\<turnstile> \<langle>c'',Normal x\<rangle> \<Rightarrow> Abrupt x'"
              by simp
            from termi_c\<^sub>2 [rule_format, OF this] s'
            show "\<Gamma>\<turnstile>c\<^sub>2 \<down> s'" by simp
           qed
        next
          case (Abrupt x)
          from steps_Abrupt_prop [OF rest this]
          have "t=Abrupt x" by simp
          with fin have "s'=Abrupt x"
            by (cases s') auto
          thus "\<Gamma>\<turnstile>c\<^sub>2 \<down> s'" 
            by auto
        next
          case (Fault f)
          from steps_Fault_prop [OF rest this]
          have "t=Fault f" by simp
          with fin have "s'=Fault f"
            by (cases s') auto
          thus "\<Gamma>\<turnstile>c\<^sub>2 \<down> s'" 
            by auto
        next
          case Stuck
          from steps_Stuck_prop [OF rest this]
          have "t=Stuck" by simp
          with fin have "s'=Stuck"
            by (cases s') auto
          thus "\<Gamma>\<turnstile>c\<^sub>2 \<down> s'" 
            by auto
        qed
      qed
    qed
  qed
next
  case (Cond b c\<^sub>1 c\<^sub>2)
  have hyp: "\<And>c' s'. \<Gamma>\<turnstile> (Cond b c\<^sub>1 c\<^sub>2, Normal s) \<rightarrow> (c', s') \<Longrightarrow> \<Gamma>\<turnstile>c' \<down> s'"
by (simp add: Cond.prems(1)) 
  show ?case
  proof (cases "s\<in>b") 
    case True
    then have "\<Gamma>\<turnstile> (Cond b c\<^sub>1 c\<^sub>2, Normal s) \<rightarrow> (c\<^sub>1, Normal s) "
     by (simp add: step.CondTrue)     
    from hyp [OF this] have "\<Gamma>\<turnstile>c\<^sub>1 \<down> Normal s".
    with True show ?thesis
      by (auto intro: terminates.intros)
  next
    case False
    then have "\<Gamma>\<turnstile> (Cond b c\<^sub>1 c\<^sub>2, Normal s) \<rightarrow> (c\<^sub>2, Normal s)"
      by (simp add: step.CondFalse)
    from hyp [OF this] have "\<Gamma>\<turnstile>c\<^sub>2 \<down> Normal s".
    with False show ?thesis
      by (auto intro: terminates.intros)
  qed
next
  case (While b c)
  have hyp: "\<And>c' s'. \<Gamma>\<turnstile> (While b c, Normal s) \<rightarrow> (c', s')   \<Longrightarrow> \<Gamma>\<turnstile>c' \<down> s'" by fact
  show ?case
  proof (cases "s\<in>b") 
    case True
    then have "\<Gamma>\<turnstile> (While b c, Normal s) \<rightarrow> (Seq c (While b c), Normal s)"
      by (simp add: step.WhileTrue)
    from hyp [OF this] have "\<Gamma>\<turnstile>(Seq c (While b c)) \<down> Normal s".
    with True show ?thesis
      by (auto elim: terminates_Normal_elim_cases intro: terminates.intros)
  next
    case False
    thus ?thesis
      by (auto intro: terminates.intros)
  qed
next
  case (Call p)
  have hyp: "\<And>c' s'. \<Gamma>\<turnstile> (Call p, Normal s) \<rightarrow> (c', s')  \<Longrightarrow> \<Gamma>\<turnstile>c' \<down> s'" by (simp add: Call.prems)
  show ?case
  proof (cases "\<Gamma> p")
    case None
    thus ?thesis
      by (auto intro: terminates.intros)
  next
    case (Some bdy)
    then have "\<Gamma>\<turnstile> (Call p, Normal s) \<rightarrow> (bdy, Normal s)"
      by (simp add: step.Call)
    from hyp [OF this] have "\<Gamma>\<turnstile>bdy \<down> Normal s".
    with Some show ?thesis
      by (auto intro: terminates.intros)
  qed
next
  case (DynCom c)
  have hyp: "\<And>c' s'. \<Gamma>\<turnstile> (DynCom c, Normal s) \<rightarrow> (c', s')  \<Longrightarrow> \<Gamma>\<turnstile>c' \<down> s'" by fact
  have "\<Gamma>\<turnstile> (DynCom c, Normal s) \<rightarrow> (c s, Normal s)"
    by (simp add: step.DynCom)
  from hyp [OF this] have "\<Gamma>\<turnstile>c s \<down> Normal s".
  then show ?case
    by (auto intro: terminates.intros)
next
  case (Guard f g c)
  have hyp: "\<And>c' s'. \<Gamma>\<turnstile> (Guard f g c, Normal s) \<rightarrow> (c', s')   \<Longrightarrow> \<Gamma>\<turnstile>c' \<down> s'" by fact
  show ?case
  proof (cases "s\<in>g")
    case True
    then have "\<Gamma>\<turnstile> (Guard f g c, Normal s) \<rightarrow> (c, Normal s) "
      by (simp add: step.Guard) thm step.Guard
    from hyp [OF this] have "\<Gamma>\<turnstile>c\<down> Normal s".
    with True show ?thesis
      by (auto intro: terminates.intros)
  next
    case False
    thus ?thesis
      by (auto intro: terminates.intros)
  qed
next 
  case Throw show ?case by (auto intro: terminates.intros)
next
  case (Catch c\<^sub>1 c\<^sub>2)
  have hyp: "\<And>c' s'. \<Gamma>\<turnstile> (Catch c\<^sub>1 c\<^sub>2, Normal s) \<rightarrow> (c', s')   \<Longrightarrow> \<Gamma>\<turnstile>c' \<down> s'" by fact
  have hyp': "(\<And>b c1. (redex (Catch c\<^sub>1 c\<^sub>2) = Await b c1) \<Longrightarrow> \<Gamma>\<turnstile>c1 \<down> Normal s \<and> s\<in>b)" by fact
  show ?case
  proof (rule terminates.Catch)
    {
      fix c' s'
      assume step_c\<^sub>1: "\<Gamma>\<turnstile> (c\<^sub>1, Normal s) \<rightarrow> (c', s')"
      assume red: "(\<And>b c1. (redex c\<^sub>1  = Await b c1) \<Longrightarrow> \<Gamma>\<turnstile>c1 \<down> Normal s \<and> s\<in>b)"
      have "\<Gamma>\<turnstile>c' \<down> s'"
      proof -
        from step_c\<^sub>1
        have "\<Gamma>\<turnstile> (Catch c\<^sub>1 c\<^sub>2, Normal s) \<rightarrow> (Catch c' c\<^sub>2, s') "
          by (simp add: step.Catch)
        from hyp [OF this]
        have "\<Gamma>\<turnstile>Catch c' c\<^sub>2 \<down> s'".
        thus "\<Gamma>\<turnstile>c'\<down> s'"
          by cases auto
      qed
    } 
    from Catch.hyps (1) [OF this]
    show "\<Gamma>\<turnstile>c\<^sub>1 \<down> Normal s" using terminates_Skip' by (simp add: hyp')
  next  
    show "\<forall>s'. \<Gamma>\<turnstile> \<langle>c\<^sub>1,Normal s\<rangle> \<Rightarrow> Abrupt s' \<longrightarrow> \<Gamma>\<turnstile>c\<^sub>2 \<down> Normal s'"
    proof (intro allI impI)
      fix s'
      assume exec_c\<^sub>1: "\<Gamma>\<turnstile> \<langle>c\<^sub>1,Normal s\<rangle> \<Rightarrow> Abrupt s'"
      show "\<Gamma>\<turnstile>c\<^sub>2 \<down> Normal s'"
      proof (cases "final (c\<^sub>1,Normal s)")
        case True
        with exec_c\<^sub>1
        have Throw: "c\<^sub>1=Throw"
          by (auto simp add: final_def elim: exec_Normal_elim_cases)
        have s1: "\<Gamma>\<turnstile>(Catch Throw c\<^sub>2,Normal s) \<rightarrow> (c\<^sub>2,Normal s)"
          by (simp add: step.CatchThrow)
        from hyp 
        have "\<Gamma>\<turnstile>c\<^sub>2 \<down> Normal s" using local.Throw s1 by blast 
        moreover from exec_c\<^sub>1 Throw
        have "s'=s"
          by (auto elim: exec_Normal_elim_cases)
        ultimately show ?thesis by simp
      next
        case False
        from exec_impl_steps [OF exec_c\<^sub>1]
        obtain c\<^sub>f t where 
          steps_c\<^sub>1: "\<Gamma>\<turnstile> (c\<^sub>1, Normal s) \<rightarrow>\<^sup>* (Throw, Normal s')" 
          by (fastforce split: xstate.splits)
        from split_computation [OF steps_c\<^sub>1 False]
        obtain c'' s'' where
          first: "\<Gamma>\<turnstile> (c\<^sub>1, Normal s) \<rightarrow> (c'', s'')" and
          rest: "\<Gamma>\<turnstile> (c'', s'') \<rightarrow>\<^sup>* (Throw, Normal s')" 
          by (auto simp add: final_def)
        from step.Catch [OF first]
        have "\<Gamma>\<turnstile> (Catch c\<^sub>1 c\<^sub>2, Normal s) \<rightarrow> (Catch c'' c\<^sub>2, s'')" by auto
        from hyp [OF this] 
        have "\<Gamma>\<turnstile>Catch c'' c\<^sub>2 \<down> s''".
        moreover
        from steps_Throw_impl_exec [OF rest]
        have "\<Gamma>\<turnstile> \<langle>c'',s''\<rangle> \<Rightarrow> Abrupt s'".
        moreover
        from rest obtain x where "s''=Normal x"
          by (cases s'')
             (auto dest: steps_Fault_prop steps_Abrupt_prop steps_Stuck_prop)
        ultimately show ?thesis
          by (fastforce elim: terminates_elim_cases)
      qed
    qed
  qed
next
  case (Await b c) 
  have hyp':"\<And>ba c1. redex (Await b c) = Await ba c1 \<Longrightarrow> \<Gamma>\<turnstile>c1 \<down> Normal s \<and> s \<in> ba" by fact 
  have hyp: "\<And>c' s'. \<Gamma>\<turnstile> (Await b c, Normal s) \<rightarrow> (c', s') \<Longrightarrow> \<Gamma>\<turnstile>c' \<down> s'" by (simp add: final_termi step_await_final1)
  have red:"redex (Await b c)  = Await b c" by auto  
  then have "\<And>b1 c1. (redex (Await b c)  = Await b1 c1) \<Longrightarrow> b1=b \<and> c1 = c" by simp
  then have " \<Gamma>\<turnstile>c \<down> Normal s \<and> s \<in> b" by (simp add: Await.prems(2))
  show ?case
  by (simp add: `\<Gamma>\<turnstile>c \<down> Normal s \<and> s \<in> b` terminates.AwaitTrue)      
qed


lemma wf_implies_termi_reach_step_case':
assumes hyp: "\<And>c' s'. \<Gamma>\<turnstile> (c, Normal s) \<rightarrow> (c', s')\<Longrightarrow> \<Gamma>\<turnstile>c' \<down> s'" and
        hyp1:"~(\<exists>b c1. redex c = Await b c1)"
shows "\<Gamma>\<turnstile>c \<down> Normal s"
using hyp hyp1
proof (induct c)
  case Skip show ?case by (fastforce intro: terminates.intros)
next
  case Basic show ?case by (fastforce intro: terminates.intros)
next
  case (Spec r)
  show ?case
    by (cases "\<exists>t. (s,t)\<in>r") (fastforce intro: terminates.intros)+
next
  case (Seq c\<^sub>1 c\<^sub>2)
  have hyp: "\<And>c' s'. \<Gamma>\<turnstile> (Seq c\<^sub>1 c\<^sub>2, Normal s) \<rightarrow> (c', s') \<Longrightarrow> \<Gamma>\<turnstile>c' \<down> s'"
using Seq.prems by blast
  have hyp': "~(\<exists>b c1. redex (Seq c\<^sub>1 c\<^sub>2) = Await b c1)" by fact
  show ?case 
  proof (rule terminates.Seq)
    {
      fix c' s'
      assume step_c\<^sub>1: "\<Gamma>\<turnstile> (c\<^sub>1, Normal s) \<rightarrow> (c', s')"
      assume red:  "~(\<exists>b c1. redex c\<^sub>1 = Await b c1)"      
      have "\<Gamma>\<turnstile>c' \<down> s'"
      proof -
        from step_c\<^sub>1
        have "\<Gamma>\<turnstile> (Seq c\<^sub>1 c\<^sub>2, Normal s) \<rightarrow> (Seq c' c\<^sub>2, s')"
          by (simp add: step.Seq)          
        from hyp [OF this]
        have "\<Gamma>\<turnstile>Seq c' c\<^sub>2 \<down> s'".
        thus "\<Gamma>\<turnstile>c'\<down> s'"
          by cases auto
      qed
    } 
    from Seq.hyps (1) [OF this]
    show "\<Gamma>\<turnstile>c\<^sub>1 \<down> Normal s"using hyp' by force 
  next
    show "\<forall>s'. \<Gamma>\<turnstile> \<langle>c\<^sub>1,Normal s\<rangle> \<Rightarrow> s' \<longrightarrow> \<Gamma>\<turnstile>c\<^sub>2 \<down> s'"
    proof (intro allI impI)
      fix s'
      assume exec_c\<^sub>1: "\<Gamma>\<turnstile> \<langle>c\<^sub>1,Normal s\<rangle> \<Rightarrow> s'"
      show "\<Gamma>\<turnstile>c\<^sub>2 \<down> s'"
      proof (cases "final (c\<^sub>1,Normal s)")
        case True
        hence "c\<^sub>1=Skip \<or> c\<^sub>1=Throw"
          by (simp add: final_def)
        thus ?thesis
        proof
          assume Skip: "c\<^sub>1=Skip"
          have s1:"\<Gamma>\<turnstile>(Seq Skip c\<^sub>2,Normal s) \<rightarrow> (c\<^sub>2,Normal s) \<and>\<not> (\<exists>b c1. Seq c\<^sub>1 c\<^sub>2 = Await b c1)"
            by (simp add: step.SeqSkip)          
          from hyp 
          have "\<Gamma>\<turnstile>c\<^sub>2 \<down> Normal s" using local.Skip s1 by blast 
          moreover from exec_c\<^sub>1 Skip
          have "s'=Normal s"
            by (auto elim: exec_Normal_elim_cases)
          ultimately show ?thesis by simp
        next
          assume Throw: "c\<^sub>1=Throw"
          with exec_c\<^sub>1 have "s'=Abrupt s"
            by (auto elim: exec_Normal_elim_cases)
          thus ?thesis
            by auto
        qed
      next
        case False        
        from exec_impl_steps [OF exec_c\<^sub>1]
        obtain c\<^sub>f t where 
          steps_c\<^sub>1: "\<Gamma>\<turnstile> (c\<^sub>1, Normal s) \<rightarrow>\<^sup>* (c\<^sub>f, t)" and
          fin:"(case s' of
                 Abrupt x \<Rightarrow> c\<^sub>f = Throw \<and> t = Normal x
                | _ \<Rightarrow> c\<^sub>f = Skip \<and> t = s')"
          by (fastforce split: xstate.splits)
        with fin have final: "final (c\<^sub>f,t)"
          by (cases s') (auto simp add: final_def)
        from split_computation [OF steps_c\<^sub>1 False this]
        obtain c'' s'' where
          first: "\<Gamma>\<turnstile> (c\<^sub>1, Normal s) \<rightarrow> (c'', s'')" and
          rest: "\<Gamma>\<turnstile> (c'', s'') \<rightarrow>\<^sup>* (c\<^sub>f, t)" 
          by blast
        from step.Seq [OF first]
        have "\<Gamma>\<turnstile> (Seq c\<^sub>1 c\<^sub>2, Normal s) \<rightarrow> (Seq c'' c\<^sub>2, s'')" by auto
        from hyp [OF this]
        have termi_s'': "\<Gamma>\<turnstile>Seq c'' c\<^sub>2 \<down> s''".
        show ?thesis
        proof (cases s'')
          case (Normal x)
          from termi_s'' [simplified Normal]
          have termi_c\<^sub>2: "\<forall>t. \<Gamma>\<turnstile> \<langle>c'',Normal x\<rangle> \<Rightarrow> t \<longrightarrow> \<Gamma>\<turnstile>c\<^sub>2 \<down> t"
            by cases
          show ?thesis
          proof (cases "\<exists>x'. s'=Abrupt x'")
            case False
            with fin obtain "c\<^sub>f=Skip" "t=s'"
              by (cases s') auto
            from steps_Skip_impl_exec [OF rest [simplified this]] Normal
            have "\<Gamma>\<turnstile> \<langle>c'',Normal x\<rangle> \<Rightarrow> s'"
              by simp
            from termi_c\<^sub>2 [rule_format, OF this]
            show "\<Gamma>\<turnstile>c\<^sub>2 \<down> s'" .
          next
            case True
            with fin obtain x' where s': "s'=Abrupt x'" and "c\<^sub>f=Throw" "t=Normal x'"
              by auto
            from steps_Throw_impl_exec [OF rest [simplified this]] Normal 
            have "\<Gamma>\<turnstile> \<langle>c'',Normal x\<rangle> \<Rightarrow> Abrupt x'"
              by simp
            from termi_c\<^sub>2 [rule_format, OF this] s'
            show "\<Gamma>\<turnstile>c\<^sub>2 \<down> s'" by simp
           qed
        next
          case (Abrupt x)
          from steps_Abrupt_prop [OF rest this]
          have "t=Abrupt x" by simp
          with fin have "s'=Abrupt x"
            by (cases s') auto
          thus "\<Gamma>\<turnstile>c\<^sub>2 \<down> s'" 
            by auto
        next
          case (Fault f)
          from steps_Fault_prop [OF rest this]
          have "t=Fault f" by simp
          with fin have "s'=Fault f"
            by (cases s') auto
          thus "\<Gamma>\<turnstile>c\<^sub>2 \<down> s'" 
            by auto
        next
          case Stuck
          from steps_Stuck_prop [OF rest this]
          have "t=Stuck" by simp
          with fin have "s'=Stuck"
            by (cases s') auto
          thus "\<Gamma>\<turnstile>c\<^sub>2 \<down> s'" 
            by auto
        qed
      qed
    qed
  qed
next
  case (Cond b c\<^sub>1 c\<^sub>2)
  have hyp: "\<And>c' s'. \<Gamma>\<turnstile> (Cond b c\<^sub>1 c\<^sub>2, Normal s) \<rightarrow> (c', s') \<Longrightarrow> \<Gamma>\<turnstile>c' \<down> s'"
by (simp add: Cond.prems(1)) 
  show ?case
  proof (cases "s\<in>b") 
    case True
    then have "\<Gamma>\<turnstile> (Cond b c\<^sub>1 c\<^sub>2, Normal s) \<rightarrow> (c\<^sub>1, Normal s) "
     by (simp add: step.CondTrue)     
    from hyp [OF this] have "\<Gamma>\<turnstile>c\<^sub>1 \<down> Normal s".
    with True show ?thesis
      by (auto intro: terminates.intros)
  next
    case False
    then have "\<Gamma>\<turnstile> (Cond b c\<^sub>1 c\<^sub>2, Normal s) \<rightarrow> (c\<^sub>2, Normal s)"
      by (simp add: step.CondFalse)
    from hyp [OF this] have "\<Gamma>\<turnstile>c\<^sub>2 \<down> Normal s".
    with False show ?thesis
      by (auto intro: terminates.intros)
  qed
next
  case (While b c)
  have hyp: "\<And>c' s'. \<Gamma>\<turnstile> (While b c, Normal s) \<rightarrow> (c', s')   \<Longrightarrow> \<Gamma>\<turnstile>c' \<down> s'" by fact
  show ?case
  proof (cases "s\<in>b") 
    case True
    then have "\<Gamma>\<turnstile> (While b c, Normal s) \<rightarrow> (Seq c (While b c), Normal s)"
      by (simp add: step.WhileTrue)
    from hyp [OF this] have "\<Gamma>\<turnstile>(Seq c (While b c)) \<down> Normal s".
    with True show ?thesis
      by (auto elim: terminates_Normal_elim_cases intro: terminates.intros)
  next
    case False
    thus ?thesis
      by (auto intro: terminates.intros)
  qed
next
  case (Call p)
  have hyp: "\<And>c' s'. \<Gamma>\<turnstile> (Call p, Normal s) \<rightarrow> (c', s')  \<Longrightarrow> \<Gamma>\<turnstile>c' \<down> s'" by (simp add: Call.prems)
  show ?case
  proof (cases "\<Gamma> p")
    case None
    thus ?thesis
      by (auto intro: terminates.intros)
  next
    case (Some bdy)
    then have "\<Gamma>\<turnstile> (Call p, Normal s) \<rightarrow> (bdy, Normal s)"
      by (simp add: step.Call)
    from hyp [OF this] have "\<Gamma>\<turnstile>bdy \<down> Normal s".
    with Some show ?thesis
      by (auto intro: terminates.intros)
  qed
next
  case (DynCom c)
  have hyp: "\<And>c' s'. \<Gamma>\<turnstile> (DynCom c, Normal s) \<rightarrow> (c', s')  \<Longrightarrow> \<Gamma>\<turnstile>c' \<down> s'" by fact
  have "\<Gamma>\<turnstile> (DynCom c, Normal s) \<rightarrow> (c s, Normal s)"
    by (simp add: step.DynCom)
  from hyp [OF this] have "\<Gamma>\<turnstile>c s \<down> Normal s".
  then show ?case
    by (auto intro: terminates.intros)
next
  case (Guard f g c)
  have hyp: "\<And>c' s'. \<Gamma>\<turnstile> (Guard f g c, Normal s) \<rightarrow> (c', s')   \<Longrightarrow> \<Gamma>\<turnstile>c' \<down> s'" by fact
  show ?case
  proof (cases "s\<in>g")
    case True
    then have "\<Gamma>\<turnstile> (Guard f g c, Normal s) \<rightarrow> (c, Normal s) "
      by (simp add: step.Guard) thm step.Guard
    from hyp [OF this] have "\<Gamma>\<turnstile>c\<down> Normal s".
    with True show ?thesis
      by (auto intro: terminates.intros)
  next
    case False
    thus ?thesis
      by (auto intro: terminates.intros)
  qed
next 
  case Throw show ?case by (auto intro: terminates.intros)
next
  case (Catch c\<^sub>1 c\<^sub>2)
  have hyp: "\<And>c' s'. \<Gamma>\<turnstile> (Catch c\<^sub>1 c\<^sub>2, Normal s) \<rightarrow> (c', s')   \<Longrightarrow> \<Gamma>\<turnstile>c' \<down> s'" by fact
  have hyp': "~(\<exists>b c1. redex (Catch c\<^sub>1 c\<^sub>2) = Await b c1)" by fact
  show ?case
  proof (rule terminates.Catch)
    {
      fix c' s'
      assume step_c\<^sub>1: "\<Gamma>\<turnstile> (c\<^sub>1, Normal s) \<rightarrow> (c', s')"
      assume red: "~(\<exists>b c1. redex c\<^sub>1  = Await b c1)"
      have "\<Gamma>\<turnstile>c' \<down> s'"
      proof -
        from step_c\<^sub>1
        have "\<Gamma>\<turnstile> (Catch c\<^sub>1 c\<^sub>2, Normal s) \<rightarrow> (Catch c' c\<^sub>2, s') "
          by (simp add: step.Catch)
        from hyp [OF this]
        have "\<Gamma>\<turnstile>Catch c' c\<^sub>2 \<down> s'".
        thus "\<Gamma>\<turnstile>c'\<down> s'"
          by cases auto
      qed
    } 
    from Catch.hyps (1) [OF this]
    show "\<Gamma>\<turnstile>c\<^sub>1 \<down> Normal s" using hyp' by force
  next  
    show "\<forall>s'. \<Gamma>\<turnstile> \<langle>c\<^sub>1,Normal s\<rangle> \<Rightarrow> Abrupt s' \<longrightarrow> \<Gamma>\<turnstile>c\<^sub>2 \<down> Normal s'"
    proof (intro allI impI)
      fix s'
      assume exec_c\<^sub>1: "\<Gamma>\<turnstile> \<langle>c\<^sub>1,Normal s\<rangle> \<Rightarrow> Abrupt s'"
      show "\<Gamma>\<turnstile>c\<^sub>2 \<down> Normal s'"
      proof (cases "final (c\<^sub>1,Normal s)")
        case True
        with exec_c\<^sub>1
        have Throw: "c\<^sub>1=Throw"
          by (auto simp add: final_def elim: exec_Normal_elim_cases)
        have s1: "\<Gamma>\<turnstile>(Catch Throw c\<^sub>2,Normal s) \<rightarrow> (c\<^sub>2,Normal s)"
          by (simp add: step.CatchThrow)
        from hyp 
        have "\<Gamma>\<turnstile>c\<^sub>2 \<down> Normal s" using local.Throw s1 by blast 
        moreover from exec_c\<^sub>1 Throw
        have "s'=s"
          by (auto elim: exec_Normal_elim_cases)
        ultimately show ?thesis by simp
      next
        case False
        from exec_impl_steps [OF exec_c\<^sub>1]
        obtain c\<^sub>f t where 
          steps_c\<^sub>1: "\<Gamma>\<turnstile> (c\<^sub>1, Normal s) \<rightarrow>\<^sup>* (Throw, Normal s')" 
          by (fastforce split: xstate.splits)
        from split_computation [OF steps_c\<^sub>1 False]
        obtain c'' s'' where
          first: "\<Gamma>\<turnstile> (c\<^sub>1, Normal s) \<rightarrow> (c'', s'')" and
          rest: "\<Gamma>\<turnstile> (c'', s'') \<rightarrow>\<^sup>* (Throw, Normal s')" 
          by (auto simp add: final_def)
        from step.Catch [OF first]
        have "\<Gamma>\<turnstile> (Catch c\<^sub>1 c\<^sub>2, Normal s) \<rightarrow> (Catch c'' c\<^sub>2, s'')" by auto
        from hyp [OF this] 
        have "\<Gamma>\<turnstile>Catch c'' c\<^sub>2 \<down> s''".
        moreover
        from steps_Throw_impl_exec [OF rest]
        have "\<Gamma>\<turnstile> \<langle>c'',s''\<rangle> \<Rightarrow> Abrupt s'".
        moreover
        from rest obtain x where "s''=Normal x"
          by (cases s'')
             (auto dest: steps_Fault_prop steps_Abrupt_prop steps_Stuck_prop)
        ultimately show ?thesis
          by (fastforce elim: terminates_elim_cases)
      qed
    qed
  qed
next
  case (Await b c)       
  show ?case
  using Await.prems(2) by auto   
qed


lemma Await_finish:"\<And>c2 s2 b c. \<Gamma>\<turnstile> (Await b c, s1) \<rightarrow> (c2, s2) \<Longrightarrow> \<Gamma>\<turnstile>c2 \<down> s2"
by (metis Abrupt Fault Stuck final_termi step_await_final1 step_preserves_termination xstate.exhaust)

                                                            
lemma wf_implies_termi_reach:
assumes wf: "wf {(cfg2,cfg1). \<Gamma> \<turnstile> (c,s) \<rightarrow>\<^sup>* cfg1 \<and> \<Gamma> \<turnstile> cfg1 \<rightarrow> cfg2}"
shows "\<And>c1 s1. \<lbrakk>\<Gamma> \<turnstile> (c,s) \<rightarrow>\<^sup>* cfg1;  cfg1=(c1,s1)\<rbrakk>\<Longrightarrow> \<Gamma>\<turnstile>c1\<down>s1"
using wf 
proof (induct cfg1,simp)
  fix c1 s1
  assume reach: "\<Gamma>\<turnstile> (c, s) \<rightarrow>\<^sup>* (c1, s1)"
  assume hyp_raw: "\<And>y c2 s2.
           \<lbrakk>\<Gamma>\<turnstile> (c1, s1) \<rightarrow> (c2, s2); \<Gamma>\<turnstile> (c, s) \<rightarrow>\<^sup>* (c2, s2); y = (c2, s2)\<rbrakk>
           \<Longrightarrow> \<Gamma>\<turnstile>c2 \<down> s2"
  have hyp: "\<And>c2 s2. \<Gamma>\<turnstile> (c1, s1) \<rightarrow> (c2, s2) \<Longrightarrow> \<Gamma>\<turnstile>c2 \<down> s2"
    apply -
    apply (rule hyp_raw)
    apply   assumption
    using reach 
    apply  simp
    apply (rule refl)
    done
  
  show "\<Gamma>\<turnstile>c1 \<down> s1"
  proof (cases s1)  
    case (Normal s1')             
    with  wf_implies_termi_reach_step_case' [OF hyp [simplified Normal]] 
    show ?thesis
      by auto
  qed (auto intro: terminates.intros)
qed

theorem no_infinite_computation_impl_terminates:
  assumes not_inf: "\<not> \<Gamma>\<turnstile> (c, s) \<rightarrow> \<dots>(\<infinity>)"
  shows "\<Gamma>\<turnstile>c\<down>s"
proof -
  from no_infinite_computation_implies_wf [OF not_inf]
  have wf: "wf {(c2, c1). \<Gamma>\<turnstile>(c, s) \<rightarrow>\<^sup>* c1 \<and> \<Gamma>\<turnstile>c1 \<rightarrow> c2}".
  show ?thesis
    by (rule wf_implies_termi_reach [OF wf]) auto
qed

corollary terminates_iff_no_infinite_computation: 
  "\<Gamma>\<turnstile>c\<down>s = (\<not> \<Gamma>\<turnstile> (c, s) \<rightarrow> \<dots>(\<infinity>))"
  apply (rule)
  apply  (erule terminates_impl_no_infinite_computation)
  apply (erule no_infinite_computation_impl_terminates)
  done

(* ************************************************************************* *)
subsection {* Generalised Redexes *} 
(* ************************************************************************* *)

text {*
For an important lemma for the completeness proof of the Hoare-logic for
total correctness we need a generalisation of @{const "redex"} that not only
yield the redex itself but all the enclosing statements as well.
*}

primrec redexes:: "('s,'p,'f,'e)com \<Rightarrow> ('s,'p,'f,'e)com set"
where
"redexes Skip = {Skip}" |
"redexes (Basic f) = {Basic f}" |
"redexes (Spec r) = {Spec r}" |
"redexes (Seq c\<^sub>1 c\<^sub>2) = {Seq c\<^sub>1 c\<^sub>2} \<union> redexes c\<^sub>1" |
"redexes (Cond b c\<^sub>1 c\<^sub>2) = {Cond b c\<^sub>1 c\<^sub>2}" |
"redexes (While b c) = {While b c}" |
"redexes (Call p) = {Call p}" |
"redexes (DynCom d) = {DynCom d}" |
"redexes (Guard f b c) = {Guard f b c}" |
"redexes (Throw) = {Throw}" |
"redexes (Catch c\<^sub>1 c\<^sub>2) = {Catch c\<^sub>1 c\<^sub>2} \<union> redexes c\<^sub>1" |
"redexes (Await b c) = {Await b c}"

lemma root_in_redexes: "c \<in> redexes c"
  apply (induct c)
  apply auto
  done

lemma redex_in_redexes: "redex c \<in> redexes c"
  apply (induct c)
  apply auto
  done

lemma redex_redexes: "\<And>c'. \<lbrakk>c' \<in> redexes c; redex c' = c'\<rbrakk> \<Longrightarrow> redex c = c'" 
  apply (induct c)
  apply auto
  done

lemma step_redexes:
  shows "\<And>r r'. \<lbrakk>\<Gamma>\<turnstile>(r,s) \<rightarrow> (r',s'); r \<in> redexes c\<rbrakk> 
  \<Longrightarrow> \<exists>c'. \<Gamma>\<turnstile>(c,s) \<rightarrow> (c',s') \<and> r' \<in> redexes c'"
proof (induct c)
  case Skip thus ?case by (fastforce intro: step.intros elim: step_elim_cases)
next
  case Basic thus ?case by (fastforce intro: step.intros elim: step_elim_cases)
next
  case Spec thus ?case by (fastforce intro: step.intros elim: step_elim_cases)
next
  case (Seq c\<^sub>1 c\<^sub>2)
  have "r \<in> redexes (Seq c\<^sub>1 c\<^sub>2)" by fact
  hence r: "r = Seq c\<^sub>1 c\<^sub>2 \<or> r \<in> redexes c\<^sub>1"
    by simp
  have step_r: "\<Gamma>\<turnstile> (r, s) \<rightarrow> (r', s')" by fact
  from r show ?case
  proof 
    assume "r = Seq c\<^sub>1 c\<^sub>2"
    with step_r
    show ?case
      by (auto simp add: root_in_redexes)
  next
    assume r: "r \<in> redexes c\<^sub>1"
    from Seq.hyps (1) [OF step_r this] 
    obtain c' where 
      step_c\<^sub>1: "\<Gamma>\<turnstile> (c\<^sub>1, s) \<rightarrow> (c', s')" and
      r': "r' \<in> redexes c'"
      by blast
    from step.Seq [OF step_c\<^sub>1]
    have "\<Gamma>\<turnstile> (Seq c\<^sub>1 c\<^sub>2, s) \<rightarrow> (Seq c' c\<^sub>2, s')".
    with r'
    show ?case
      by auto
  qed
next
  case Cond 
  thus ?case 
    by (fastforce intro: step.intros elim: step_elim_cases simp add: root_in_redexes)
next
  case While 
  thus ?case 
    by (fastforce intro: step.intros elim: step_elim_cases simp add: root_in_redexes)
next
  case Call thus ?case 
    by (fastforce intro: step.intros elim: step_elim_cases simp add: root_in_redexes)
next
  case DynCom thus ?case 
    by (fastforce intro: step.intros elim: step_elim_cases simp add: root_in_redexes)
next
  case Guard thus ?case 
    by (fastforce intro: step.intros elim: step_elim_cases simp add: root_in_redexes)
next
  case Throw thus ?case 
    by (fastforce intro: step.intros elim: step_elim_cases simp add: root_in_redexes)
next
  case (Catch c\<^sub>1 c\<^sub>2)
  have "r \<in> redexes (Catch c\<^sub>1 c\<^sub>2)" by fact
  hence r: "r = Catch c\<^sub>1 c\<^sub>2 \<or> r \<in> redexes c\<^sub>1"
    by simp
  have step_r: "\<Gamma>\<turnstile> (r, s) \<rightarrow> (r', s')" by fact
  from r show ?case
  proof 
    assume "r = Catch c\<^sub>1 c\<^sub>2"
    with step_r
    show ?case
      by (auto simp add: root_in_redexes)
  next
    assume r: "r \<in> redexes c\<^sub>1"
    from Catch.hyps (1) [OF step_r this] 
    obtain c' where 
      step_c\<^sub>1: "\<Gamma>\<turnstile> (c\<^sub>1, s) \<rightarrow> (c', s')" and
      r': "r' \<in> redexes c'"
      by blast
    from step.Catch [OF step_c\<^sub>1]
    have "\<Gamma>\<turnstile> (Catch c\<^sub>1 c\<^sub>2, s) \<rightarrow> (Catch c' c\<^sub>2, s')".
    with r'
    show ?case
      by auto
  qed
next case (Await b c)  
     thus ?case 
     by (fastforce intro: step.intros elim: step_elim_cases simp add: root_in_redexes)
qed 

lemma steps_redexes:
  assumes steps: "\<Gamma>\<turnstile> (r, s) \<rightarrow>\<^sup>* (r', s')"
  shows "\<And>c. r \<in> redexes c \<Longrightarrow> \<exists>c'. \<Gamma>\<turnstile>(c,s) \<rightarrow>\<^sup>* (c',s') \<and> r' \<in> redexes c'"
using steps 
proof (induct rule: converse_rtranclp_induct2 [case_names Refl Trans])
  case Refl
  then
  show "\<exists>c'. \<Gamma>\<turnstile> (c, s') \<rightarrow>\<^sup>* (c', s') \<and> r' \<in> redexes c'"
    by auto
next
  case (Trans r s r'' s'')
  have "\<Gamma>\<turnstile> (r, s) \<rightarrow> (r'', s'')" "r \<in> redexes c" by fact+
  from step_redexes [OF this]
  obtain c' where
    step: "\<Gamma>\<turnstile> (c, s) \<rightarrow> (c', s'')" and
    r'': "r'' \<in> redexes c'"
    by blast
  note step
  also
  from Trans.hyps (3) [OF r'']
  obtain c'' where
    steps: "\<Gamma>\<turnstile> (c', s'') \<rightarrow>\<^sup>* (c'', s')" and
    r': "r' \<in> redexes c''"
    by blast
  note steps
  finally
  show ?case
    using r'
    by blast
qed



lemma steps_redexes':
  assumes steps: "\<Gamma>\<turnstile> (r, s) \<rightarrow>\<^sup>+ (r', s')"
  shows "\<And>c. r \<in> redexes c \<Longrightarrow> \<exists>c'. \<Gamma>\<turnstile>(c,s) \<rightarrow>\<^sup>+ (c',s') \<and> r' \<in> redexes c'"
using steps 
proof (induct rule: tranclp_induct2 [consumes 1, case_names Step Trans])
  case (Step r' s' c') 
  have "\<Gamma>\<turnstile> (r, s) \<rightarrow> (r', s')" "r \<in> redexes c'" by fact+
  from step_redexes [OF this]
  show ?case
    by (blast intro: r_into_trancl)
next
  case (Trans r' s' r'' s'')
  from Trans obtain c' where
    steps: "\<Gamma>\<turnstile> (c, s) \<rightarrow>\<^sup>+ (c', s')" and
    r': "r' \<in> redexes c'"
    by blast
  note steps
  moreover
  have "\<Gamma>\<turnstile> (r', s') \<rightarrow> (r'', s'')" by fact
  from step_redexes [OF this r'] obtain c'' where
    step: "\<Gamma>\<turnstile> (c', s') \<rightarrow> (c'', s'')" and
    r'': "r'' \<in> redexes c''"
    by blast
  note step
  finally show ?case
    using r'' by blast
qed

lemma step_redexes_Seq:
  assumes step: "\<Gamma>\<turnstile>(r,s) \<rightarrow> (r',s')"
  assumes Seq: "Seq r c\<^sub>2 \<in> redexes c"
  shows "\<exists>c'. \<Gamma>\<turnstile>(c,s) \<rightarrow> (c',s') \<and> Seq r' c\<^sub>2 \<in> redexes c'"
proof -
  from step.Seq [OF step]
  have "\<Gamma>\<turnstile> (Seq r c\<^sub>2, s) \<rightarrow> (Seq r' c\<^sub>2, s')".
  from step_redexes [OF this Seq] 
  show ?thesis .
qed

lemma steps_redexes_Seq:
  assumes steps: "\<Gamma>\<turnstile> (r, s) \<rightarrow>\<^sup>* (r', s')"
  shows "\<And>c. Seq r c\<^sub>2 \<in> redexes c \<Longrightarrow> 
              \<exists>c'. \<Gamma>\<turnstile>(c,s) \<rightarrow>\<^sup>* (c',s') \<and> Seq r' c\<^sub>2 \<in> redexes c'"
using steps 
proof (induct rule: converse_rtranclp_induct2 [case_names Refl Trans])
  case Refl
  then show ?case
    by (auto)

next
  case (Trans r s r'' s'')
  have "\<Gamma>\<turnstile> (r, s) \<rightarrow> (r'', s'')" "Seq r c\<^sub>2 \<in> redexes c" by fact+
  from step_redexes_Seq [OF this]
  obtain c' where
    step: "\<Gamma>\<turnstile> (c, s) \<rightarrow> (c', s'')" and
    r'': "Seq r'' c\<^sub>2 \<in> redexes c'"
    by blast
  note step
  also
  from Trans.hyps (3) [OF r'']
  obtain c'' where
    steps: "\<Gamma>\<turnstile> (c', s'') \<rightarrow>\<^sup>* (c'', s')" and
    r': "Seq r' c\<^sub>2 \<in> redexes c''"
    by blast
  note steps
  finally
  show ?case
    using r'
    by blast
qed

lemma steps_redexes_Seq':
  assumes steps: "\<Gamma>\<turnstile> (r, s) \<rightarrow>\<^sup>+ (r', s')"
  shows "\<And>c. Seq r c\<^sub>2 \<in> redexes c 
             \<Longrightarrow> \<exists>c'. \<Gamma>\<turnstile>(c,s) \<rightarrow>\<^sup>+ (c',s') \<and> Seq r' c\<^sub>2 \<in> redexes c'"
using steps 
proof (induct rule: tranclp_induct2 [consumes 1, case_names Step Trans])
  case (Step r' s' c') 
  have "\<Gamma>\<turnstile> (r, s) \<rightarrow> (r', s')" "Seq r c\<^sub>2 \<in> redexes c'" by fact+
  from step_redexes_Seq [OF this]
  show ?case
    by (blast intro: r_into_trancl)
next
  case (Trans r' s' r'' s'')
  from Trans obtain c' where
    steps: "\<Gamma>\<turnstile> (c, s) \<rightarrow>\<^sup>+ (c', s')" and
    r': "Seq r' c\<^sub>2 \<in> redexes c'"
    by blast
  note steps
  moreover
  have "\<Gamma>\<turnstile> (r', s') \<rightarrow> (r'', s'')" by fact
  from step_redexes_Seq [OF this r'] obtain c'' where
    step: "\<Gamma>\<turnstile> (c', s') \<rightarrow> (c'', s'')" and
    r'': "Seq r'' c\<^sub>2 \<in> redexes c''"
    by blast
  note step
  finally show ?case
    using r'' by blast
qed

lemma step_redexes_Catch:
  assumes step: "\<Gamma>\<turnstile>(r,s) \<rightarrow> (r',s')"
  assumes Catch: "Catch r c\<^sub>2 \<in> redexes c"
  shows "\<exists>c'. \<Gamma>\<turnstile>(c,s) \<rightarrow> (c',s') \<and> Catch r' c\<^sub>2 \<in> redexes c'"
proof -
  from step.Catch [OF step]
  have "\<Gamma>\<turnstile> (Catch r c\<^sub>2, s) \<rightarrow> (Catch r' c\<^sub>2, s')".
  from step_redexes [OF this Catch] 
  show ?thesis .
qed

lemma steps_redexes_Catch:
  assumes steps: "\<Gamma>\<turnstile> (r, s) \<rightarrow>\<^sup>* (r', s')"
  shows "\<And>c. Catch r c\<^sub>2 \<in> redexes c \<Longrightarrow> 
              \<exists>c'. \<Gamma>\<turnstile>(c,s) \<rightarrow>\<^sup>* (c',s') \<and> Catch r' c\<^sub>2 \<in> redexes c'"
using steps 
proof (induct rule: converse_rtranclp_induct2 [case_names Refl Trans])
  case Refl
  then show ?case
    by (auto)

next
  case (Trans r s r'' s'')
  have "\<Gamma>\<turnstile> (r, s) \<rightarrow> (r'', s'')" "Catch r c\<^sub>2 \<in> redexes c" by fact+
  from step_redexes_Catch [OF this]
  obtain c' where
    step: "\<Gamma>\<turnstile> (c, s) \<rightarrow> (c', s'')" and
    r'': "Catch r'' c\<^sub>2 \<in> redexes c'"
    by blast
  note step
  also
  from Trans.hyps (3) [OF r'']
  obtain c'' where
    steps: "\<Gamma>\<turnstile> (c', s'') \<rightarrow>\<^sup>* (c'', s')" and
    r': "Catch r' c\<^sub>2 \<in> redexes c''"
    by blast
  note steps
  finally
  show ?case
    using r'
    by blast
qed

lemma steps_redexes_Catch':
  assumes steps: "\<Gamma>\<turnstile> (r, s) \<rightarrow>\<^sup>+ (r', s')"
  shows "\<And>c. Catch r c\<^sub>2 \<in> redexes c 
             \<Longrightarrow> \<exists>c'. \<Gamma>\<turnstile>(c,s) \<rightarrow>\<^sup>+ (c',s') \<and> Catch r' c\<^sub>2 \<in> redexes c'"
using steps 
proof (induct rule: tranclp_induct2 [consumes 1, case_names Step Trans])
  case (Step r' s' c') 
  have "\<Gamma>\<turnstile> (r, s) \<rightarrow> (r', s')" "Catch r c\<^sub>2 \<in> redexes c'" by fact+
  from step_redexes_Catch [OF this]
  show ?case
    by (blast intro: r_into_trancl)
next
  case (Trans r' s' r'' s'')
  from Trans obtain c' where
    steps: "\<Gamma>\<turnstile> (c, s) \<rightarrow>\<^sup>+ (c', s')" and
    r': "Catch r' c\<^sub>2 \<in> redexes c'"
    by blast
  note steps
  moreover
  have "\<Gamma>\<turnstile> (r', s') \<rightarrow> (r'', s'')" by fact
  from step_redexes_Catch [OF this r'] obtain c'' where
    step: "\<Gamma>\<turnstile> (c', s') \<rightarrow> (c'', s'')" and
    r'': "Catch r'' c\<^sub>2 \<in> redexes c''"
    by blast
  note step
  finally show ?case
    using r'' by blast
qed

lemma redexes_subset:"\<And>c'. c' \<in> redexes c \<Longrightarrow> redexes c' \<subseteq> redexes c"
  by (induct c) auto

lemma redexes_preserves_termination:
  assumes termi: "\<Gamma>\<turnstile>c\<down>s"
  shows "\<And>c'. c' \<in> redexes c \<Longrightarrow> \<Gamma>\<turnstile>c'\<down>s"  
using termi
by induct (auto intro: terminates.intros)

*)
end