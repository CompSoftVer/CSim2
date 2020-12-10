theory CRef
imports Main "CSimpl.LocalRG_HoareDef"  "EmbSimpl.HoareTotalProps" 
begin

abbreviation \<tau>  where "\<tau> \<equiv> None"
  
definition Id where "Id \<equiv> {(x,y). x = y}"  

fun wfs_i::"nat \<Rightarrow> ('g,'l) par_state \<Rightarrow> bool"
  where "wfs_i i (g,l) = (i < length l)"

fun wf_conf::"('g,'l,'p,'f,'e) par_com \<Rightarrow> ('g,'l)par_state  \<Rightarrow> bool"  
  where "wf_conf c (g,l) = (length c \<le> length l)"  

fun state_add_local::"'l \<Rightarrow>  ('g,'l)par_state \<Rightarrow> ('g,'l)par_state"
 ("_#s_" [81,81] 100)
  where 
  "state_add_local l (g,ls) = (g, l#ls)"

fun drop_local::"('g,'l)par_state \<Rightarrow> ('g,'l)par_state"
where 
  "drop_local (g,ls) = (g, drop 1 ls)"


fun local_list_par::"('g,'l)par_state \<Rightarrow> 'l list"
where 
  "local_list_par (g, ls) = ls"

fun local_list::"('g\<times>'l)\<times>('l list) \<Rightarrow> 'l list"
  where
 "local_list ((g,l),ls) = ls"

lemma str1:
  assumes a0:"si\<^sub>s < length l\<^sub>s \<and> l\<^sub>s ! si\<^sub>s = (csuci'\<^sub>s, ssuci'\<^sub>s)" 
  shows "\<exists>sis'. sis' < length (l'\<^sub>s@ l\<^sub>s) \<and> (l'\<^sub>s@ l\<^sub>s) ! sis' = (csuci'\<^sub>s, ssuci'\<^sub>s)"          
  using a0 by (induct l'\<^sub>s, auto)
    
lemma str2:
  "j>0 \<Longrightarrow> j< length l \<Longrightarrow>
   \<forall>i<j. ((take j l)@ l')!i = l!i" 
by (simp add: nth_append)

lemma str3:    
  "j\<ge>length l1 \<Longrightarrow>
   j<length (l1@l') \<Longrightarrow>
   (l1 @ l') ! j = l'!(j-length l1)"
  by (simp add: nth_append)

lemma list_conc:"i< length l \<Longrightarrow> 
                 P1 (l!i) \<Longrightarrow> 
                 P \<longrightarrow> j< length l \<and> P2 (l!j) \<and> j\<ge>i \<Longrightarrow>
                 \<exists>i'. i'< length (l1@l) \<and> P1 ((l1@l)!i') \<and>
                 (P \<longrightarrow> (\<exists>j'. j'<length (l1@l) \<and> P2 ((l1@l)!j') \<and>  j'\<ge>i'))"
proof (induct l1)
  case Nil thus ?case by auto
next
  case (Cons el1 l1) 
  then obtain i' j' where step:"i'<length (l1 @ l) \<and> P1 ((l1 @ l) ! i') \<and> 
    (P \<longrightarrow> (j'<length (l1 @ l) \<and> P2 ((l1 @ l) ! j') \<and> i' \<le> j'))" 
    by auto
  {
    assume p:"P"
    then have "Suc i' < length ((el1#l1)@l) \<and> Suc j' < length ((el1#l1)@l) \<and> P1 (((el1#l1)@l)! Suc i') \<and>
               P2 (((el1#l1)@l)!Suc j') \<and> Suc i' \<le> Suc j'"   
      using step p by fastforce
    then have ?case using step p by fastforce
  }    
  also {
    assume "\<not>P"
    then have ?case using step
      by auto    
  }    
  ultimately show ?case by auto
qed
  
definition Sta\<^sub>s :: "('s,'s1) rel \<Rightarrow> 
                   ('s tran, 's1 tran) rel \<Rightarrow> bool" where
  "Sta\<^sub>s f R \<equiv>  (\<forall>x x1 y y1. (x,y) \<in> f \<and>  ((x, x1),y, y1)\<in> R \<longrightarrow> 
                (x1,y1)\<in> f)"


inductive       
      "stepce"::"[('s,'p,'f,'e) body,'e option,('s,'p,'f,'e) config,('s,'p,'f,'e) config] \<Rightarrow> bool"
                                ("_\<turnstile>\<^sub>c\<^sub>_ (_ \<rightarrow>/ _)" [81,81,81,81] 100)  
  for \<Gamma>::"('s,'p,'f,'e) body"
where

  Basicc: "\<Gamma>\<turnstile>\<^sub>c\<^sub>e(Basic f e, s) \<rightarrow> (Skip, (f s))"

| Specc: "(s,t) \<in> r \<Longrightarrow> \<Gamma>\<turnstile>\<^sub>c\<^sub>e(Spec r e, s) \<rightarrow> (Skip, t)"
| SpecStuckc: "\<forall>t. (s,t) \<notin> r \<Longrightarrow> \<Gamma>\<turnstile>\<^sub>c\<^sub>e(Spec r e, s) \<rightarrow> (Stuck,s)"

| Guardc: "s\<in>g \<Longrightarrow> \<Gamma>\<turnstile>\<^sub>c\<^sub>\<tau>(Guard f g c, s) \<rightarrow> (c, s)"
  
| GuardFaultc: "s\<notin>g \<Longrightarrow> \<Gamma>\<turnstile>\<^sub>c\<^sub>\<tau>(Guard f g c, s) \<rightarrow> (Fault f,s)"


| Seqc: "\<Gamma>\<turnstile>\<^sub>c\<^sub>e(c\<^sub>1,s) \<rightarrow> (c\<^sub>1',s')
        \<Longrightarrow> 
        \<Gamma>\<turnstile>\<^sub>c\<^sub>e(Seq c\<^sub>1 c\<^sub>2,s) \<rightarrow> (Seq c\<^sub>1' c\<^sub>2, s')"
| SeqSkipc: "\<Gamma>\<turnstile>\<^sub>c\<^sub>\<tau>(Seq Skip c\<^sub>2,s) \<rightarrow> (c\<^sub>2, s)"
| SeqThrowc: "\<Gamma>\<turnstile>\<^sub>c\<^sub>\<tau>(Seq Throw c\<^sub>2, s) \<rightarrow> (Throw,  s)"
| SeqFaultc: "\<Gamma>\<turnstile>\<^sub>c\<^sub>\<tau>(Seq (Fault f) c\<^sub>2, s) \<rightarrow> (Fault f, s)"
| SeqStuckc: "\<Gamma>\<turnstile>\<^sub>c\<^sub>\<tau>(Seq Stuck c\<^sub>2, s) \<rightarrow> (Stuck, s)"
| CondTruec:  "s\<in>b \<Longrightarrow> \<Gamma>\<turnstile>\<^sub>c\<^sub>\<tau>(Cond b c\<^sub>1 c\<^sub>2, s) \<rightarrow> (c\<^sub>1, s)"
| CondFalsec: "s\<notin>b \<Longrightarrow> \<Gamma>\<turnstile>\<^sub>c\<^sub>\<tau>(Cond b c\<^sub>1 c\<^sub>2, s) \<rightarrow> (c\<^sub>2, s)"

| WhileTruec: "\<lbrakk>s\<in>b\<rbrakk> 
              \<Longrightarrow> 
              \<Gamma>\<turnstile>\<^sub>c\<^sub>\<tau>(While b c, s) \<rightarrow> (Seq c (While b c), s)"

| WhileFalsec: "\<lbrakk>s\<notin>b\<rbrakk> 
               \<Longrightarrow> 
               \<Gamma>\<turnstile>\<^sub>c\<^sub>\<tau>(While b c, s) \<rightarrow> (Skip, s)"


| Awaitc:  "\<lbrakk>s\<in>b; \<Gamma>1=\<Gamma>\<^sub>\<not>\<^sub>a ; \<Gamma>1\<turnstile>\<langle>ca1,Normal s\<rangle> \<Rightarrow> Normal t\<rbrakk> \<Longrightarrow> 
            \<Gamma>\<turnstile>\<^sub>c\<^sub>e(Await b ca1 e, s) \<rightarrow> (Skip,t)"

| AwaitFaultc: "\<lbrakk>s\<in>b; \<Gamma>1=\<Gamma>\<^sub>\<not>\<^sub>a ; \<Gamma>1\<turnstile>\<langle>ca1,Normal s\<rangle> \<Rightarrow> xstate.Fault f\<rbrakk> \<Longrightarrow> 
                 \<Gamma>\<turnstile>\<^sub>c\<^sub>e(Await b ca1 e, s) \<rightarrow> (Fault f,s)"

| AwaitStuckc: "\<lbrakk>s\<in>b; \<Gamma>1=\<Gamma>\<^sub>\<not>\<^sub>a ; \<Gamma>1\<turnstile>\<langle>ca1,Normal s\<rangle> \<Rightarrow>  Semantic.Stuck\<rbrakk> \<Longrightarrow> 
                 \<Gamma>\<turnstile>\<^sub>c\<^sub>e(Await b ca1 e, s) \<rightarrow> (Stuck,s)"

| AwaitAbruptc: "\<lbrakk>s\<in>b; \<Gamma>1=\<Gamma>\<^sub>\<not>\<^sub>a ; \<Gamma>1\<turnstile>\<langle>ca1,Normal s\<rangle> \<Rightarrow> Abrupt t\<rbrakk> \<Longrightarrow> 
                 \<Gamma>\<turnstile>\<^sub>c\<^sub>e(Await b ca1 e, s) \<rightarrow> (Throw,t)"

| Callc: "\<Gamma> p = Some bdy \<Longrightarrow>  bdy\<noteq>Call p \<Longrightarrow>
         \<Gamma>\<turnstile>\<^sub>c\<^sub>\<tau>(Call p, s) \<rightarrow> (bdy, s)"

| CallUndefinedc: "\<Gamma> p=None \<Longrightarrow>
         \<Gamma>\<turnstile>\<^sub>c\<^sub>\<tau>(Call p, s) \<rightarrow> (Stuck,s)"

| DynComc: "\<Gamma>\<turnstile>\<^sub>c\<^sub>\<tau>(DynCom c, s) \<rightarrow> (c s, s)"

| Catchc: "\<lbrakk>\<Gamma>\<turnstile>\<^sub>c\<^sub>e(c\<^sub>1,s) \<rightarrow> (c\<^sub>1',s')\<rbrakk>
          \<Longrightarrow>
          \<Gamma>\<turnstile>\<^sub>c\<^sub>e(Catch c\<^sub>1 c\<^sub>2,s) \<rightarrow> (Catch c\<^sub>1' c\<^sub>2,s')"

| CatchThrowc: "\<Gamma>\<turnstile>\<^sub>c\<^sub>\<tau>(Catch Throw c\<^sub>2, s) \<rightarrow> (c\<^sub>2, s)"
| CatchSkipc: "\<Gamma>\<turnstile>\<^sub>c\<^sub>\<tau>(Catch Skip c\<^sub>2,s) \<rightarrow> (Skip,s)"
| CatchFaultc:"\<Gamma>\<turnstile>\<^sub>c\<^sub>\<tau>(Catch (Fault f) c\<^sub>2,s) \<rightarrow> (Fault f,s)"
| CatchStuckc:"\<Gamma>\<turnstile>\<^sub>c\<^sub>\<tau>(Catch Stuck c\<^sub>2,s) \<rightarrow> (Stuck,s)"
  
          
  
lemmas stepce_induct = stepce.induct [of _ _ "(c,s)" "(c',s')", split_format (complete), case_names
Basicc Specc SpecStuckc Guardc GuardFaultc Seqc SeqSkipc SeqThrowc SeqFaultc SeqStuckc CondTruec CondFalsec
WhileTruec WhileFalsec Awaitc AwaitFaultc AwaitStuckc AwaitAbruptc Callc CallUndefinedc DynComc 
Catchc CatchThrowc CatchSkipc CatchFaultc CatchStuckc, induct set]  

inductive_cases stepc_elim_casese:
 "\<Gamma>\<turnstile>\<^sub>c\<^sub>a(Await b c2 e,s) \<rightarrow> (nc,Normal s')"


inductive_cases stepc_elim_cases1:
 "\<Gamma>\<turnstile>\<^sub>c\<^sub>a(Skip,s) \<rightarrow> u"
 "\<Gamma>\<turnstile>\<^sub>c\<^sub>a(Fault f,s) \<rightarrow> u"
 "\<Gamma>\<turnstile>\<^sub>c\<^sub>a(Stuck,s) \<rightarrow> u"
 "\<Gamma>\<turnstile>\<^sub>c\<^sub>a(Guard f g c,s) \<rightarrow> u"
 "\<Gamma>\<turnstile>\<^sub>c\<^sub>a(Basic f e,s) \<rightarrow> u"
 "\<Gamma>\<turnstile>\<^sub>c\<^sub>a(Spec r e,s) \<rightarrow> u"
 "\<Gamma>\<turnstile>\<^sub>c\<^sub>a(Seq c1 c2,s) \<rightarrow> u"
 "\<Gamma>\<turnstile>\<^sub>c\<^sub>a(Cond b c1 c2,s) \<rightarrow> u"
 "\<Gamma>\<turnstile>\<^sub>c\<^sub>a(While b c,s) \<rightarrow> u"
 "\<Gamma>\<turnstile>\<^sub>c\<^sub>a(Await b c2 e,s) \<rightarrow> u"
 "\<Gamma>\<turnstile>\<^sub>c\<^sub>a(Call p,s) \<rightarrow> u"
 "\<Gamma>\<turnstile>\<^sub>c\<^sub>a(DynCom c,s) \<rightarrow> u"
 "\<Gamma>\<turnstile>\<^sub>c\<^sub>a(Throw,s) \<rightarrow> u"
 "\<Gamma>\<turnstile>\<^sub>c\<^sub>a(Catch c1 c2,s) \<rightarrow> u"

inductive_cases stepc_elim_cases:
"\<Gamma>\<turnstile>\<^sub>c\<^sub>a(Basic f e, s) \<rightarrow> (Skip, f s)"
"\<Gamma>\<turnstile>\<^sub>c\<^sub>a(Spec r e, s) \<rightarrow> (Skip, t)"
"\<Gamma>\<turnstile>\<^sub>c\<^sub>a(Spec r e, s) \<rightarrow> (Stuck, s)"
"\<Gamma>\<turnstile>\<^sub>c\<^sub>e(Guard f g c, s) \<rightarrow> (c, s)"
"\<Gamma>\<turnstile>\<^sub>c\<^sub>e(Guard f g c, s) \<rightarrow> (Fault f, s)"
"\<Gamma>\<turnstile>\<^sub>c\<^sub>a(Seq c\<^sub>1 c\<^sub>2,s) \<rightarrow> (Seq c\<^sub>1' c\<^sub>2, s')"
"\<Gamma>\<turnstile>\<^sub>c\<^sub>e(Seq Skip c\<^sub>2,s) \<rightarrow> (c\<^sub>2, s)"
"\<Gamma>\<turnstile>\<^sub>c\<^sub>e(Seq Throw c\<^sub>2, s) \<rightarrow> (Throw,  s)"
"\<Gamma>\<turnstile>\<^sub>c\<^sub>e(Seq (Fault f) c\<^sub>2, s) \<rightarrow> (Fault f,  s)"
"\<Gamma>\<turnstile>\<^sub>c\<^sub>e(Seq Stuck c\<^sub>2, s) \<rightarrow> (Stuck,  s)"
"\<Gamma>\<turnstile>\<^sub>c\<^sub>e(Cond b c\<^sub>1 c\<^sub>2, s) \<rightarrow> (c\<^sub>1, s)"
"\<Gamma>\<turnstile>\<^sub>c\<^sub>e(Cond b c\<^sub>1 c\<^sub>2, s) \<rightarrow> (c\<^sub>2, s)"
"\<Gamma>\<turnstile>\<^sub>c\<^sub>e(While b c, s) \<rightarrow> (Seq c (While b c), s)"
"\<Gamma>\<turnstile>\<^sub>c\<^sub>e(While b c, s) \<rightarrow> (Skip, s)"
"\<Gamma>\<turnstile>\<^sub>c\<^sub>a(Await b ca1 e, s) \<rightarrow> (Skip,t)"
"\<Gamma>\<turnstile>\<^sub>c\<^sub>a(Await b ca1 e, s) \<rightarrow> (Throw, t)"
"\<Gamma>\<turnstile>\<^sub>c\<^sub>a(Await b ca1 e, s) \<rightarrow> (Fault f, t)"
"\<Gamma>\<turnstile>\<^sub>c\<^sub>a(Await b ca1 e, s) \<rightarrow> (Stuck, t)"
"\<Gamma>\<turnstile>\<^sub>c\<^sub>e(Call p, s) \<rightarrow> (bdy, s)"
"\<Gamma>\<turnstile>\<^sub>c\<^sub>e(Call p, s) \<rightarrow> (Stuck,s)"
"\<Gamma>\<turnstile>\<^sub>c\<^sub>e(DynCom c, s) \<rightarrow> (c s, s)"
"\<Gamma>\<turnstile>\<^sub>c\<^sub>a(Catch c\<^sub>1 c\<^sub>2,s) \<rightarrow> (Catch c\<^sub>1' c\<^sub>2,s')"
"\<Gamma>\<turnstile>\<^sub>c\<^sub>e(Catch Throw c\<^sub>2, s) \<rightarrow> (c\<^sub>2, s)"
"\<Gamma>\<turnstile>\<^sub>c\<^sub>e(Catch Skip c\<^sub>2,s) \<rightarrow> (Skip,s)"
"\<Gamma>\<turnstile>\<^sub>c\<^sub>e(Catch (Fault f) c\<^sub>2,s) \<rightarrow> (Fault f,s)"
"\<Gamma>\<turnstile>\<^sub>c\<^sub>e(Catch Stuck c\<^sub>2,s) \<rightarrow> (Stuck,s)"
"\<Gamma>\<turnstile>\<^sub>c\<^sub>e(c, s) \<rightarrow> (Stuck,s')"
"\<Gamma>\<turnstile>\<^sub>c\<^sub>e(c, s) \<rightarrow> (Throw,s')"
"\<Gamma>\<turnstile>\<^sub>c\<^sub>e(c, s) \<rightarrow> (Fault f,s')"
 
inductive_cases ev_stepc_elim_cases:
  "\<Gamma>\<turnstile>\<^sub>c\<^sub>Some v(c,s) \<rightarrow> u"
  
inductive_cases ev_stepc_normal_elim_cases:
  "\<Gamma>\<turnstile>\<^sub>c\<^sub>Some v(c,Normal s) \<rightarrow> u"

inductive_cases stepc_elim_casestau:
 "\<Gamma>\<turnstile>\<^sub>c\<^sub>\<tau>(Skip,s) \<rightarrow> u"
 "\<Gamma>\<turnstile>\<^sub>c\<^sub>\<tau>(Guard f g c,s) \<rightarrow> u"
 "\<Gamma>\<turnstile>\<^sub>c\<^sub>\<tau>(Basic f e,s) \<rightarrow> u"
 "\<Gamma>\<turnstile>\<^sub>c\<^sub>\<tau>(Spec r e,s) \<rightarrow> u"
 "\<Gamma>\<turnstile>\<^sub>c\<^sub>\<tau>(Seq c1 c2,s) \<rightarrow> u"
 "\<Gamma>\<turnstile>\<^sub>c\<^sub>\<tau>(Cond b c1 c2,s) \<rightarrow> u"
 "\<Gamma>\<turnstile>\<^sub>c\<^sub>\<tau>(While b c,s) \<rightarrow> u"
 "\<Gamma>\<turnstile>\<^sub>c\<^sub>\<tau>(Await b c2 e,s) \<rightarrow> u"
 "\<Gamma>\<turnstile>\<^sub>c\<^sub>\<tau>(Call p,s) \<rightarrow> u"
 "\<Gamma>\<turnstile>\<^sub>c\<^sub>\<tau>(DynCom c,s) \<rightarrow> u"
 "\<Gamma>\<turnstile>\<^sub>c\<^sub>\<tau>(Throw,s) \<rightarrow> u"
 "\<Gamma>\<turnstile>\<^sub>c\<^sub>\<tau>(Catch c1 c2,s) \<rightarrow> u"


lemma stepce_stepc:
  "\<Gamma>\<turnstile>\<^sub>c\<^sub>e (c,s) \<rightarrow> (c',s') \<Longrightarrow> \<Gamma>\<turnstile>\<^sub>c (c,s) \<rightarrow> (c',s')"
proof (induct rule: stepce_induct)
qed (fastforce intro:stepc.intros)+

lemma stepc_stepce:
  "\<Gamma>\<turnstile>\<^sub>c (c,s) \<rightarrow> (c',s') \<Longrightarrow>  \<exists>e. \<Gamma>\<turnstile>\<^sub>c\<^sub>e (c,s) \<rightarrow> (c',s')"
proof (induct rule: stepc_induct)  
qed(fastforce intro:stepce.intros)+
  
lemma stepc_stepce_unique:
  "\<Gamma>\<turnstile>\<^sub>c (c,s) \<rightarrow> (c',s') \<Longrightarrow>  \<exists>!e. \<Gamma>\<turnstile>\<^sub>c\<^sub>e (c,s) \<rightarrow> (c',s')"
proof (induct rule: stepc_induct)
qed (fastforce intro: stepce.intros elim: stepc_elim_cases)+
 
inductive_cases stepc_elim_cases_Seq_skip_ev:
  "\<Gamma>\<^sub>c\<turnstile>\<^sub>c\<^sub>(Some e) (Seq Skip c1, \<sigma>) \<rightarrow> u"
  "\<Gamma>\<^sub>c\<turnstile>\<^sub>c\<^sub>(Some e) (Seq Throw c1, \<sigma>) \<rightarrow> u"
  "\<Gamma>\<^sub>c\<turnstile>\<^sub>c\<^sub>(Some e) (Seq Stuck c1, \<sigma>) \<rightarrow> u"
  "\<Gamma>\<^sub>c\<turnstile>\<^sub>c\<^sub>(Some e) (Seq (Fault f) c1, \<sigma>) \<rightarrow> u"
  "\<Gamma>\<^sub>c\<turnstile>\<^sub>c\<^sub>(Some e) (Catch Skip c1, \<sigma>) \<rightarrow> u"
  "\<Gamma>\<^sub>c\<turnstile>\<^sub>c\<^sub>(Some e) (Catch Throw c1, \<sigma>) \<rightarrow> u"  
  "\<Gamma>\<^sub>c\<turnstile>\<^sub>c\<^sub>(Some e) (Catch Stuck c1, \<sigma>) \<rightarrow> u"
  "\<Gamma>\<^sub>c\<turnstile>\<^sub>c\<^sub>(Some e) (Catch (Fault f) c1, \<sigma>) \<rightarrow> u"

inductive_cases stepc_elim_seq_skip:
 "\<Gamma>\<turnstile>\<^sub>c\<^sub>a(Seq Skip c2,s) \<rightarrow> u"
 "\<Gamma>\<turnstile>\<^sub>c\<^sub>a(Seq Throw c2,s) \<rightarrow> u"
 "\<Gamma>\<turnstile>\<^sub>c\<^sub>a(Seq Stuck c2,s) \<rightarrow> u"
 "\<Gamma>\<turnstile>\<^sub>c\<^sub>a(Seq (Fault f) c2,s) \<rightarrow> u"
 "\<Gamma>\<turnstile>\<^sub>c\<^sub>a(Catch Skip c2,s) \<rightarrow> u"
 "\<Gamma>\<turnstile>\<^sub>c\<^sub>a(Catch Throw c2,s) \<rightarrow> u"
 "\<Gamma>\<turnstile>\<^sub>c\<^sub>a(Catch Stuck c2,s) \<rightarrow> u"
 "\<Gamma>\<turnstile>\<^sub>c\<^sub>a(Catch (Fault f) c2,s) \<rightarrow> u"
 
inductive_cases evstepc_elim_seq:
 "\<Gamma>\<turnstile>\<^sub>c\<^sub>a(Seq c1 c2,s) \<rightarrow> (Seq c1' c2,s')"  
 "\<Gamma>\<turnstile>\<^sub>c\<^sub>a(Catch c1 c2,s) \<rightarrow> (Catch c1' c2,s')"
 "\<Gamma>\<turnstile>\<^sub>c\<^sub>a(Seq c\<^sub>1 c\<^sub>2,s) \<rightarrow> (c, s')"
 "\<Gamma>\<turnstile>\<^sub>c\<^sub>a(Catch c\<^sub>1 c\<^sub>2,s) \<rightarrow> (c, s')"
  
inductive_cases stepc_elim_cases2:
 "\<Gamma>\<turnstile>\<^sub>c\<^sub>a(Cond b c1 c2, s) \<rightarrow> u"
 "\<Gamma>\<turnstile>\<^sub>c\<^sub>a(Guard f b c, s) \<rightarrow> u"
  

lemma dest_while: 
  "\<Gamma>\<turnstile>\<^sub>c\<^sub>a(While b c, s) \<rightarrow> (c1,s') \<Longrightarrow> 
    s' =  s \<and> 
    ((s\<in>-b \<and> c1=Skip) \<or> 
    (s\<in>b \<and> c1 = Seq c (LanguageCon.com.While b c)))
    "
  by (fastforce elim:stepc_elim_cases1(9)) 
  
(* lemmas on skip and throw *) 
  
lemma skip1:
  assumes a4:"\<Gamma>\<^sub>c\<turnstile>\<^sub>c\<^sub>e (LanguageCon.com.Skip, \<sigma>) \<rightarrow> (c1, s1)"
  shows "P" 
  using a4 CRef.stepc_elim_cases1(1) by auto

lemma throw1:
  assumes a4:"\<Gamma>\<^sub>c\<turnstile>\<^sub>c\<^sub>e (LanguageCon.com.Throw,  s) \<rightarrow> (c1, s1)"
  shows "P"
  using CRef.stepc_elim_cases1(13) a4 by auto

lemma Fault_ev:
  assumes a4:"\<Gamma>\<^sub>c\<turnstile>\<^sub>c\<^sub>e (Fault f,  s) \<rightarrow> (c1, s1)"
  shows "P"
  using CRef.stepc_elim_cases1(2) a4 by metis

lemma Stuck_ev:
  assumes a4:"\<Gamma>\<^sub>c\<turnstile>\<^sub>c\<^sub>e (Stuck,  s) \<rightarrow> (c1, s1)"
  shows "P"
  using CRef.stepc_elim_cases1(3) a4 by metis
  

lemma no_step_skip:"\<not> \<Gamma>\<^sub>c\<turnstile>\<^sub>c\<^sub>e (Skip,\<sigma>) \<rightarrow> (c\<^sub>c',\<sigma>')"  
  by (metis stepc_elim_cases1(1))

lemma no_step_Throw:"\<not> \<Gamma>\<^sub>c\<turnstile>\<^sub>c\<^sub>e (Throw,\<sigma>) \<rightarrow> (c\<^sub>c',\<sigma>')"
  by (metis stepc_elim_cases1(13))

lemma no_step_Fault:"\<not> \<Gamma>\<^sub>c\<turnstile>\<^sub>c\<^sub>e (Fault f,\<sigma>) \<rightarrow> (c\<^sub>c',\<sigma>')"
  by (metis stepc_elim_cases1(2))

lemma no_step_Stuck:"\<not> \<Gamma>\<^sub>c\<turnstile>\<^sub>c\<^sub>e (Stuck,\<sigma>) \<rightarrow> (c\<^sub>c',\<sigma>')"
  by (metis stepc_elim_cases1(3))
    
lemma not_catch_skip_throw_ev:
  assumes a4:"\<Gamma>\<^sub>c\<turnstile>\<^sub>c\<^sub>(Some e) (Catch Skip c1, \<sigma>) \<rightarrow> (c1', s1) \<or> 
              \<Gamma>\<^sub>c\<turnstile>\<^sub>c\<^sub>(Some e) (Catch Throw c1, \<sigma>) \<rightarrow> (c1', s1) \<or>
              \<Gamma>\<^sub>c\<turnstile>\<^sub>c\<^sub>(Some e) (Catch Stuck c1, \<sigma>) \<rightarrow> (c1', s1) \<or>
              \<Gamma>\<^sub>c\<turnstile>\<^sub>c\<^sub>(Some e) (Catch (Fault f) c1, \<sigma>) \<rightarrow> (c1', s1)"
     shows "P"
proof -
  have "\<not>\<Gamma>\<^sub>c\<turnstile>\<^sub>c\<^sub>(Some e) (Catch Skip c1, \<sigma>) \<rightarrow> (c1', s1)"    
    by (meson stepc_elim_cases1(1) stepc_elim_cases_Seq_skip_ev(5))
  moreover have "\<not>\<Gamma>\<^sub>c\<turnstile>\<^sub>c\<^sub>(Some e) (Catch Throw c1, \<sigma>) \<rightarrow> (c1', s1)"
    using stepc_elim_cases1(13) stepc_elim_cases_Seq_skip_ev(6)
    by metis
  moreover have "\<not>\<Gamma>\<^sub>c\<turnstile>\<^sub>c\<^sub>(Some e) (Catch Stuck c1, \<sigma>) \<rightarrow> (c1', s1)"
    using stepc_elim_cases1(3) stepc_elim_cases_Seq_skip_ev(7)
    by metis
  moreover have "\<not>\<Gamma>\<^sub>c\<turnstile>\<^sub>c\<^sub>(Some e) (Catch (Fault f) c1, \<sigma>) \<rightarrow> (c1', s1)"
    using stepc_elim_cases1(2) stepc_elim_cases_Seq_skip_ev(8)
    by metis
  ultimately show ?thesis using a4 by auto
qed
  
lemma not_seq_skip_throw_ev:
  assumes a4:"\<Gamma>\<^sub>c\<turnstile>\<^sub>c\<^sub>(Some e) (Seq Skip c1, \<sigma>) \<rightarrow> (c1', s1) \<or> 
              \<Gamma>\<^sub>c\<turnstile>\<^sub>c\<^sub>(Some e) (Seq Throw c1, \<sigma>) \<rightarrow> (c1', s1) \<or> 
              \<Gamma>\<^sub>c\<turnstile>\<^sub>c\<^sub>(Some e) (Seq Stuck c1, \<sigma>) \<rightarrow> (c1', s1) \<or> 
              \<Gamma>\<^sub>c\<turnstile>\<^sub>c\<^sub>(Some e) (Seq (Fault f) c1, \<sigma>) \<rightarrow> (c1', s1)"
     shows "P"
proof -
  have "\<not>\<Gamma>\<^sub>c\<turnstile>\<^sub>c\<^sub>(Some e) (Seq Skip c1, \<sigma>) \<rightarrow> (c1', s1)"    
    by (meson stepc_elim_cases1(1) stepc_elim_cases_Seq_skip_ev(1))
  moreover have "\<not>\<Gamma>\<^sub>c\<turnstile>\<^sub>c\<^sub>(Some e) (Seq Throw c1, \<sigma>) \<rightarrow> (c1', s1)"
    using stepc_elim_cases1(13) stepc_elim_cases_Seq_skip_ev(2)
    by metis
  moreover have "\<not> \<Gamma>\<^sub>c\<turnstile>\<^sub>c\<^sub>(Some e) (Seq Stuck c1, \<sigma>) \<rightarrow> (c1', s1)"
    using stepc_elim_cases1(3) stepc_elim_cases_Seq_skip_ev(3)
    by metis
  moreover have "\<not> \<Gamma>\<^sub>c\<turnstile>\<^sub>c\<^sub>(Some e) (Seq (Fault f) c1, \<sigma>) \<rightarrow> (c1', s1)"
    using stepc_elim_cases1(2) stepc_elim_cases_Seq_skip_ev(4)
    by metis
  ultimately show ?thesis using a4 by auto
qed
   
abbreviation 
 "stepce_rtrancl" :: "[('s,'p,'f,'e) body,'e option,('s,'p,'f,'e) config,('s,'p,'f,'e) config] \<Rightarrow> bool"
                                ("_\<turnstile>\<^sub>c\<^sub>_ (_ \<rightarrow>\<^sup>*/ _)" [81,81,81,81] 100)
 where                                
  "\<Gamma>\<turnstile>\<^sub>c\<^sub>e cf0 \<rightarrow>\<^sup>* cf1 \<equiv> ((CONST stepce \<Gamma> e))\<^sup>*\<^sup>*  cf0 cf1" 
  
abbreviation 
 "stepce_tau_rtrancl" :: "[('s,'p,'f,'e) body,('s,'p,'f,'e) config,('s,'p,'f,'e) config] \<Rightarrow> bool"
                                ("_\<turnstile>\<^sub>c (_ \<rightarrow>\<^sub>\<tau>\<^sup>*/ _)" [81,81,81] 100)
where                                
  "\<Gamma>\<turnstile>\<^sub>c cf0 \<rightarrow>\<^sub>\<tau>\<^sup>* cf1 \<equiv> ((CONST stepce \<Gamma> None))\<^sup>*\<^sup>*  cf0 cf1"
  
  abbreviation 
 "stepce_ev_rtrancl" :: "[('s,'p,'f,'e) body,'e, ('s,'p,'f,'e) config,('s,'p,'f,'e) config] \<Rightarrow> bool"
                                ("_\<turnstile>\<^sub>c\<^sub>_ (_ \<rightarrow>\<^sup>+/ _)" [81,81,81,81] 100)
where                                
  "\<Gamma>\<turnstile>\<^sub>c\<^sub>e cf0 \<rightarrow>\<^sup>+ cf1 \<equiv> \<exists>cf' cf''. \<Gamma>\<turnstile>\<^sub>c cf0 \<rightarrow>\<^sub>\<tau>\<^sup>* cf' \<and>  
                               (\<exists>a. a = Some e \<and> \<Gamma>\<turnstile>\<^sub>c\<^sub>a cf' \<rightarrow> cf'') \<and> 
                                \<Gamma>\<turnstile>\<^sub>c cf'' \<rightarrow>\<^sub>\<tau>\<^sup>* cf1"

abbreviation 
 "step_e_rtrancl" :: "[('g\<times>'l,'p,'f,'e) body,('g, 'l,  'p,'f,'e) config_gs,('g, 'l,  'p,'f,'e) config_gs] \<Rightarrow> bool"
                                ("_\<turnstile>\<^sub>c (_ \<rightarrow>\<^sub>e\<^sup>*/ _)" [81,81,81] 100)
where                                     
  "\<Gamma>\<turnstile>\<^sub>c cf0 \<rightarrow>\<^sub>e\<^sup>* cf1 \<equiv> ((CONST step_e \<Gamma>))\<^sup>*\<^sup>*  cf0 cf1"


 lemma catch_ev_s:
  "\<Gamma>\<turnstile>\<^sub>c\<^sub>e (c,s) \<rightarrow>\<^sup>* (c',s') \<Longrightarrow>
  \<Gamma>\<turnstile>\<^sub>c\<^sub>e (Catch c c2,s) \<rightarrow>\<^sup>* (Catch c' c2,s')"
   apply (induct rule: rtranclp_induct2[case_names Refl Step])   
   by ( auto, meson rtranclp.simps stepce.Catchc)  
  
 lemma catch_ev_plus:
  "\<Gamma>\<turnstile>\<^sub>c\<^sub>v (c1, s) \<rightarrow>\<^sup>+ (c1', s') \<Longrightarrow>
  \<Gamma>\<turnstile>\<^sub>c\<^sub>v (LanguageCon.com.Catch c1 c2, s) \<rightarrow>\<^sup>+ (LanguageCon.com.Catch c1' c2 ,s')
"
  using catch_ev_s[of \<Gamma> \<tau> c1 s _ _ c2 ] catch_ev_s[of \<Gamma> \<tau> _ _ c1' s']  
         stepce.Catchc  
  by fastforce    
     
 lemma seq_ev_s:
  "\<Gamma>\<turnstile>\<^sub>c\<^sub>e (c,s) \<rightarrow>\<^sup>* (c',s') \<Longrightarrow>
  \<Gamma>\<turnstile>\<^sub>c\<^sub>e (Seq c c2,s) \<rightarrow>\<^sup>* (Seq c' c2,s')"
   apply (induct rule: rtranclp_induct2[case_names Refl Step])   
   by ( auto, meson rtranclp.simps stepce.Seqc)

lemma seq_ev_plus:
  "\<Gamma>\<turnstile>\<^sub>c\<^sub>v (c1, s) \<rightarrow>\<^sup>+ (c1', s') \<Longrightarrow>
  \<Gamma>\<turnstile>\<^sub>c\<^sub>v (LanguageCon.com.Seq c1 c2, s) \<rightarrow>\<^sup>+ (LanguageCon.com.Seq c1' c2 ,s')
"
  using seq_ev_s[of \<Gamma> \<tau> c1 s _ _ c2 ] seq_ev_s[of \<Gamma> \<tau> _ _ c1' s']  
         stepce.Seqc  
  by fastforce
lemma tran_tau_closure:"\<Gamma>\<turnstile>\<^sub>c (C, \<sigma>) \<rightarrow>\<^sub>\<tau>\<^sup>* (C', \<sigma>') \<Longrightarrow>
       \<Gamma>\<turnstile>\<^sub>c (C', \<sigma>') \<rightarrow>\<^sub>\<tau>\<^sup>* (C'', \<sigma>'') \<Longrightarrow>
      \<Gamma>\<turnstile>\<^sub>c (C, \<sigma>) \<rightarrow>\<^sub>\<tau>\<^sup>* (C'', \<sigma>'')"
  by auto

lemma event_tran_closure_tau_closure:"\<Gamma>\<turnstile>\<^sub>c (C'', \<sigma>'') \<rightarrow>\<^sub>\<tau>\<^sup>* (C, \<sigma>) \<Longrightarrow>
       \<Gamma>\<turnstile>\<^sub>c\<^sub>v (C, \<sigma>) \<rightarrow>\<^sup>+  (C', \<sigma>') \<Longrightarrow>
       \<Gamma>\<turnstile>\<^sub>c\<^sub>v (C'', \<sigma>'') \<rightarrow>\<^sup>+  (C', \<sigma>')"
  using tran_tau_closure by fastforce

lemma event_tran_closure_tau_tran:"
      \<Gamma>\<turnstile>\<^sub>c\<^sub>\<tau> (C'', \<sigma>'') \<rightarrow> (C, \<sigma>) \<Longrightarrow>
       \<Gamma>\<turnstile>\<^sub>c\<^sub>v (C, \<sigma>) \<rightarrow>\<^sup>+  (C', \<sigma>') \<Longrightarrow>
       \<Gamma>\<turnstile>\<^sub>c\<^sub>v (C'', \<sigma>'') \<rightarrow>\<^sup>+  (C', \<sigma>')"
  using event_tran_closure_tau_closure
  by (meson converse_rtranclp_into_rtranclp)  

inductive       
"step_pev"::"[('g\<times>'l,'p,'f,'e) body, 'e option, ('g,'l,'p,'f,'e) par_config, 
            ('g,'l,'p,'f,'e) par_config] \<Rightarrow> bool"
("_\<turnstile>\<^sub>p\<^sub>_ (_ \<rightarrow>/ _)" [81,81,81] 100)  
where
 ParCompe: "\<lbrakk>i<length Ps;  \<Gamma>\<turnstile>\<^sub>c\<^sub>e(Ps!i,toSeqPar i s) \<rightarrow> (r,s')\<rbrakk> \<Longrightarrow>  
           \<Gamma>\<turnstile>\<^sub>p\<^sub>e(Ps, s) \<rightarrow> (Ps[i:=r], toPar i s' s)"


 lemmas steppev_induct = step_pev.induct [of _ _ "(c,s)" "(c',s')", split_format (complete), case_names
ParComp, induct set]

inductive_cases step_pev_elim_cases [cases set]:
 "\<Gamma>\<turnstile>\<^sub>p\<^sub>e(Ps, s) \<rightarrow> u"

inductive_cases step_pev_pair_elim_cases [cases set]:
 "\<Gamma>\<turnstile>\<^sub>p\<^sub>e(Ps, s) \<rightarrow> (Qs, t)"


 lemma steppe_stepp:
   "\<Gamma>\<turnstile>\<^sub>p\<^sub>e (c,s) \<rightarrow> (c',s') \<Longrightarrow> \<Gamma>\<turnstile>\<^sub>p (c,s) \<rightarrow> (c',s')"  
   using  stepce_stepc   ParCompNormalI by (fastforce elim: step_pev_elim_cases)   
  
lemma stepp_steppe:
  assumes a0:"\<Gamma>\<turnstile>\<^sub>p (c,s) \<rightarrow> (c',s')" shows " \<exists>e. \<Gamma>\<turnstile>\<^sub>p\<^sub>e (c,s) \<rightarrow> (c',s')"
  using step_p_elim_cases[OF a0]
  using stepc_stepce[of \<Gamma>] step_pev.intros[of _ c \<Gamma> _ s] apply auto
  by metis

lemma eq_par:
" wfs_i i s \<Longrightarrow>   
  toPar i s' s = toPar i sa s \<Longrightarrow> s' = sa"
   apply (cases s; cases s'; auto)
  by (metis nth_list_update_eq prod.collapse)

lemma not_set_step_not_par_step_f: 
  assumes a0:"wfs_i i s" and
          a2:"\<not> \<Gamma>\<turnstile>\<^sub>c\<^sub>f (Ps ! i, toSeqPar i s) \<rightarrow> (r, s')" 
  shows "\<not> \<Gamma>\<turnstile>\<^sub>p\<^sub>f (Ps, s) \<rightarrow> (Ps[i := r], toPar i s' s)"
proof (rule contrapos_pp[OF a2])
  assume "\<not> \<not> \<Gamma>\<turnstile>\<^sub>p\<^sub>f (Ps, s) \<rightarrow> (Ps[i := r], toPar i s' s)"
  then have p:"\<Gamma>\<turnstile>\<^sub>p\<^sub>f (Ps, s) \<rightarrow> (Ps[i := r], toPar i s' s)" by auto
  then obtain ia  ra sa where "i < length Ps" and 
                              "\<Gamma>\<turnstile>\<^sub>c\<^sub>f (Ps ! i, toSeqPar i s) \<rightarrow> (r, sa)" and  
                              "Ps[i := r] = Ps[ia := ra]" and 
                              n:"toPar i s' s = toPar i sa s" 
    using step_pev_pair_elim_cases[OF p] step_change_p_or_eq_s stepce_stepc mod_env_not_component 
    apply auto
    by (smt getList.elims mod_env_not_component nth_list_update_eq nth_list_update_neq stepce_stepc)
  thus "\<not> \<not> \<Gamma>\<turnstile>\<^sub>c\<^sub>f (Ps ! i, toSeqPar i s) \<rightarrow> (r, s')" using n eq_par[OF a0 ]
    by blast
qed

lemma stepp_steppe_unique:
  assumes a1:"wf_conf c s" and
          a2:"\<Gamma>\<turnstile>\<^sub>p (c, s) \<rightarrow> (c',s')"
        shows "\<exists>!e. \<Gamma>\<turnstile>\<^sub>p\<^sub>e (c, s) \<rightarrow> (c',s')"
proof-
 obtain i r s1' where i:"i < length c" and
                   "\<Gamma>\<turnstile>\<^sub>c (c ! i, toSeqPar i s) \<rightarrow> (r, s1')" and 
                   c':"c' = c[i := r]" and s':"s' = toPar i s1' s"
    using step_p_pair_elim_cases[OF a2] getList.simps unfolding toPar.simps toSeqPar.simps 
    by metis
    
  moreover obtain e where e:"\<Gamma>\<turnstile>\<^sub>c\<^sub>e (c ! i, toSeqPar i s) \<rightarrow> (r, s1') \<and> 
                       (\<forall>f. e\<noteq>f \<longrightarrow> \<not> \<Gamma>\<turnstile>\<^sub>c\<^sub>f (c ! i, toSeqPar i s) \<rightarrow> (r, s1'))"
    using calculation stepc_stepce_unique by fast
  ultimately have p_tran:"\<Gamma>\<turnstile>\<^sub>p\<^sub>e (c, s) \<rightarrow> (c[i := r], toPar i s1' s)"     
    by (meson ParCompe e i)   
  moreover have "length c \<le> length (snd s)" using a1 prod.exhaust_sel
    by (metis wf_conf.simps)
  then have "i<length (snd s)" using i by auto
  then have "wfs_i i s" using i a1  
    by (metis prod.exhaust_sel wfs_i.simps)    
  ultimately have "(\<forall>f. e\<noteq>f \<longrightarrow> \<not> \<Gamma>\<turnstile>\<^sub>p\<^sub>f (c, s) \<rightarrow> (c[i := r], toPar i s1' s))" 
    using  e not_set_step_not_par_step_f
    by blast
  then show ?thesis 
    using c' s' p_tran by metis    
qed


abbreviation 
 "steppev_rtrancl" :: "[('g\<times>'l,'p,'f,'e) body,'e option,('g,'l, 'p,'f,'e) par_config,('g,'l,'p,'f,'e) par_config] \<Rightarrow> bool"
                                ("_\<turnstile>\<^sub>p\<^sub>_ (_ \<rightarrow>\<^sup>*/ _)" [81,81,81,81] 100)
 where                                
  "\<Gamma>\<turnstile>\<^sub>p\<^sub>e cf0 \<rightarrow>\<^sup>* cf1 \<equiv> ((CONST step_pev \<Gamma> e))\<^sup>*\<^sup>*  cf0 cf1" 

abbreviation 
 "steppev_rtrancl1" :: "[('g\<times>'l,'p,'f,'e) body,('g,'l, 'p,'f,'e) par_config,('g,'l,'p,'f,'e) par_config] \<Rightarrow> bool"
                                ("_\<turnstile>\<^sub>p (_ \<rightarrow>\<^sup>+/ _)" [81,81,81] 100)
 where                                
  "\<Gamma>\<turnstile>\<^sub>p cf0 \<rightarrow>\<^sup>+ cf1 \<equiv> ((CONST step_pev \<Gamma> \<tau>))\<^sup>+\<^sup>+  cf0 cf1" 

abbreviation 
 "steppev_tau_rtrancl" :: "[('g\<times>'l,'p,'f,'e) body,('g,'l,'p,'f,'e) par_config,('g, 'l ,'p,'f,'e) par_config] \<Rightarrow> bool"
                                ("_\<turnstile>\<^sub>p (_ \<rightarrow>\<^sub>\<tau>\<^sup>*/ _)" [81,81,81] 100)
where                                
  "\<Gamma>\<turnstile>\<^sub>p cf0 \<rightarrow>\<^sub>\<tau>\<^sup>* cf1 \<equiv> ((CONST step_pev \<Gamma> None))\<^sup>*\<^sup>*  cf0 cf1"
                                 
  abbreviation 
 "steppeev_ev_rtrancl" :: "[('g\<times>'l,'p,'f,'e) body,'e,('g,'l, 'p,'f,'e) par_config,('g,'l,'p,'f,'e) par_config] \<Rightarrow> bool"
                                ("_\<turnstile>\<^sub>p\<^sub>_ (_ \<rightarrow>\<^sup>+/ _)" [81,81,81,81] 100)
where                                
  "\<Gamma>\<turnstile>\<^sub>p\<^sub>e cf0 \<rightarrow>\<^sup>+ cf1 \<equiv> \<exists>cf' cf''. \<Gamma>\<turnstile>\<^sub>p cf0 \<rightarrow>\<^sub>\<tau>\<^sup>* cf' \<and>  
                               (\<exists>a. a = Some e \<and> \<Gamma>\<turnstile>\<^sub>p\<^sub>a cf' \<rightarrow> cf'') \<and> 
                                \<Gamma>\<turnstile>\<^sub>p cf'' \<rightarrow>\<^sub>\<tau>\<^sup>* cf1"
  

abbreviation 
 "step_pe_rtrancl" ::"[('g\<times>'l,'p,'f,'e) body,('g,'l,'p,'f,'e) par_config,('g, 'l ,'p,'f,'e) par_config] \<Rightarrow> bool"
                                ("_\<turnstile>\<^sub>p (_ \<rightarrow>\<^sub>e\<^sup>*/ _)" [81,81,81] 100)
where                                
  "\<Gamma>\<turnstile>\<^sub>p cf0 \<rightarrow>\<^sub>e\<^sup>* cf1 \<equiv> ((CONST step_pe \<Gamma>))\<^sup>*\<^sup>*  cf0 cf1"

abbreviation 
 "step_pe_trancl" :: "[('g\<times>'l,'p,'f,'e) body,('g,'l,'p,'f,'e) par_config,('g, 'l ,'p,'f,'e) par_config] \<Rightarrow> bool"
                                ("_\<turnstile>\<^sub>p (_ \<rightarrow>\<^sub>e\<^sup>+/ _)" [81,81,81] 100)
where                                
  "\<Gamma>\<turnstile>\<^sub>p cf0 \<rightarrow>\<^sub>e\<^sup>+ cf1 \<equiv> ((CONST step_pe \<Gamma>))\<^sup>+\<^sup>+  cf0 cf1"


lemma rtran_eq_tran: " \<Gamma>\<turnstile>\<^sub>p cf0 \<rightarrow>\<^sub>e\<^sup>* cf1 = \<Gamma>\<turnstile>\<^sub>p cf0 \<rightarrow>\<^sub>e\<^sup>+ cf1"
  using ParEnv apply auto
proof -  
  assume a2: "\<Gamma>\<turnstile>\<^sub>p cf0 \<rightarrow>\<^sub>e\<^sup>* cf1"
  have "(fst cf0, snd cf0) = cf0"
   by (metis (full_types) prod.exhaust_sel)
  then show "\<Gamma>\<turnstile>\<^sub>p cf0 \<rightarrow>\<^sub>e\<^sup>+ cf1"
    using a2  step_pe.intros tranclp.r_into_trancl  by (metis rtranclpD surjective_pairing)
qed

lemma to_par_normal_inc_list:" (g', ls') = toPar i s1' ( (g, ls)) \<Longrightarrow>
       i < length ls \<Longrightarrow> 
       (g', l # ls') = toPar (i + 1) s1' ( (g, l # ls))"
  by (cases s1', auto)


lemma extend_state_mono:
  assumes a0:"wf_conf as s" and 
       a1:"\<Gamma>\<turnstile>\<^sub>p\<^sub>e (as, s) \<rightarrow> (as', s')" and 
       a2:"i<length as" and a3:"s' = toPar i s1' s"      
     shows "l #s s' = toPar (i + 1) s1' (l #s s)"
  using a0 a3 a2  a1  
  by (cases s; cases s'; auto)
    
lemma par_tran_comp:
       "wf_conf as s \<Longrightarrow> 
       \<Gamma>\<turnstile>\<^sub>p\<^sub>e (as, s) \<rightarrow> (as', s') \<Longrightarrow> 
       \<Gamma>\<turnstile>\<^sub>p\<^sub>e (a#as, l #s s) \<rightarrow> (a#as', l #s s')"
proof-
  assume a0:"wf_conf as s" and 
         a1:"\<Gamma>\<turnstile>\<^sub>p\<^sub>e (as, s) \<rightarrow> (as', s')"
  then obtain i r s1' where 
    cond:"i<length as" and "\<Gamma>\<turnstile>\<^sub>c\<^sub>e(as!i,toSeqPar i s) \<rightarrow> (r,s1' )" and as':"as' = as[i:=r]" and
        s':"s' = toPar i s1' s"
    using step_pev_pair_elim_cases[OF a1] 
    unfolding getList.simps toPar.simps toSeqPar.simps by metis
  then have "\<Gamma>\<turnstile>\<^sub>c\<^sub>e((a#as)!(i+1),toSeqPar (i+1) (l #s s)) \<rightarrow> (r,s1' )" by (cases s; fastforce) 
  then have "\<Gamma>\<turnstile>\<^sub>p\<^sub>e (a # as, (l #s s)) \<rightarrow> ((a # as')[i + 1 := r], toPar (i + 1) s1' (l #s s))"
    using ParCompe[of "i+1" "a#as" \<Gamma> e "l #s s" r s1'] cond as' by auto
  moreover have "l #s s' = toPar (i + 1) s1' (l #s s)" 
    using extend_state_mono[OF a0 a1 cond s'] by auto
  ultimately show ?thesis using a1 cond as' by fastforce
qed

lemma final_no_par_step:"All_End (as,  (g,ls)) \<Longrightarrow> \<Gamma>\<turnstile>\<^sub>p\<^sub>e (as,  (g,ls)) \<rightarrow> (as', s) \<Longrightarrow> P" 
  unfolding All_End_def final1_def
  by (metis final1_def final_c_def final_c_step_false steppe_stepp)

lemma  wf_conf_par_step:
  assumes 
    a0:"wf_conf c s" and
    a1:"\<Gamma>\<turnstile>\<^sub>p\<^sub>e (c, s) \<rightarrow> (c', s')"
   shows "wf_conf c' s'" 
proof-
obtain i r s1' where 
    cond:"i<length c" and "\<Gamma>\<turnstile>\<^sub>c\<^sub>e(c!i,toSeqPar i s) \<rightarrow> (r,s1' )" and as':"c' = c[i:=r]" and
        s':"s' = toPar i s1' s"
  using step_pev_pair_elim_cases[OF a1] 
  unfolding getList.simps toPar.simps toSeqPar.simps by blast
  then show ?thesis 
    using a0
    by (cases s; cases s'; auto )    
    
qed

lemma wf_conf_env_step: 
assumes a0:"wf_conf c s" and
        a1:"\<Gamma>\<turnstile>\<^sub>p (c, s) \<rightarrow>\<^sub>e (c', s')"
      shows "wf_conf c' s'" 
  using step_pe_elim_cases[OF a1] a0 
  by (metis a0 snd_conv wf_conf.simps(1))

lemma wf_conf_step:
      "\<Gamma>\<^sub>s\<turnstile>\<^sub>p (as, s) \<rightarrow>\<^sub>\<tau>\<^sup>* (as', s')  \<Longrightarrow>
      wf_conf as s \<Longrightarrow>
      wf_conf as' s'"
proof (induct rule: rtranclp_induct2[case_names Refl Step] )
  case Refl
  then show ?case by auto
next
  case (Step a1 b1 a2 b2)
  then show ?case using wf_conf_par_step by blast
qed

lemma par_tran_comp_rtran:
      "\<Gamma>\<^sub>s\<turnstile>\<^sub>p (as, s) \<rightarrow>\<^sub>\<tau>\<^sup>* (as', s') \<Longrightarrow>
       wf_conf as s \<Longrightarrow>
       \<Gamma>\<^sub>s\<turnstile>\<^sub>p (a#as, l #s s) \<rightarrow>\<^sub>\<tau>\<^sup>* (a#as', l #s s')"
proof (induct arbitrary: l a rule: rtranclp_induct2[case_names Refl Step] )
  case Refl
  then show ?case by auto
next
  case (Step as1 s' as1' s'')
  moreover have "wf_conf as1 s'" using wf_conf_step
    using calculation by blast
  moreover have "\<Gamma>\<^sub>s\<turnstile>\<^sub>p\<^sub>\<tau> (a#as1, l #s s') \<rightarrow> (a#as1', l #s s'')"
    using calculation
    by (simp add: par_tran_comp)
  ultimately show ?case 
    by (metis (no_types, lifting) rtranclp.simps)
qed   

lemma wfs_toPar_seq_eq:"wfs_i i s \<Longrightarrow> toPar i (toSeqPar i s) s = s"
  by (cases s, auto)

lemma wfs_tran_toSeqPar_toPar:
  "wfs_i i s \<Longrightarrow>  ss' = toSeqPar i (toPar i ss' s)"
  by (cases s; cases ss'; auto)

lemma step_getList_tran:"\<forall>j\<noteq>i.  
                           (getList s')!j =  (getList s)!j \<Longrightarrow> 
                        \<forall>j\<noteq>i. (getList s'') ! j = (getList s') ! j \<Longrightarrow>
                       \<forall>j\<noteq>i. (getList s'') ! j = (getList s) ! j"
  by auto

lemma mult_step_in_par0:
  " \<Gamma>\<turnstile>\<^sub>c (c1, ss) \<rightarrow>\<^sub>\<tau>\<^sup>* (c, ss'') \<Longrightarrow> 
    c1 = Coms ! i \<Longrightarrow> 
    ss = toSeqPar i s \<Longrightarrow>  
    wf_conf Coms s \<Longrightarrow>  i< length Coms \<Longrightarrow>
    \<exists>s'. \<Gamma>\<turnstile>\<^sub>p (Coms, s) \<rightarrow>\<^sub>\<tau>\<^sup>* (Coms[i:=c], toPar i ss'' s') \<and> length (snd s') = length (snd s) \<and> 
        (\<forall>j\<noteq>i. (getList s') ! j = (getList s)!j)"                    
proof (induct arbitrary: s  Coms rule: converse_rtranclp_induct2[case_names Refl Step]) 
  case (Refl) 
   have "wfs_i i s" using Refl(3) Refl(4)  by (cases s, auto)
   then show ?case using Refl wfs_toPar_seq_eq
     by (metis list_update_id rtranclp.rtrancl_refl)  
next 
  case (Step c1 ss c' ss')
  then have "i < length (Coms[i := c1])" 
    by (metis length_list_update)
  then have step:"\<Gamma>\<turnstile>\<^sub>p\<^sub>\<tau> (Coms, s) \<rightarrow> (Coms[i := c'], toPar i ss' s)"
    using Step
    using ParCompe by blast
  moreover have f1:"\<forall>j\<noteq>i.  (getList s)!j =  (getList (toPar i ss' s))!j"
    by (cases s; cases ss'; auto) 
  moreover have "\<exists>s'. \<Gamma>\<turnstile>\<^sub>p (Coms[i := c'], toPar i ss' s) \<rightarrow>\<^sub>\<tau>\<^sup>* (Coms[i := c],toPar i ss'' s')  \<and>
                      length (snd s') = length (snd s) \<and>
                    (\<forall>j\<noteq>i. (getList s') ! j = (getList ( toPar i ss' s)) ! j)"
  proof-
    have f1:"c' = Coms[i := c'] ! i"
      by (simp add: Step.prems(4))       
    have f2:"ss' = toSeqPar i (toPar i ss' s)"
    proof-                  
      have "wfs_i i s" using Step(6,7) by (cases s, auto)
      then show ?thesis using wfs_tran_toSeqPar_toPar by fast
    qed           
    have f3:"wf_conf (Coms[i := c']) (toPar i ss' s)"
      using Step.prems(3) step wf_conf_par_step by blast 
    have f4:"i < length Coms"
      by (simp add: Step.prems(4)) 
    then show ?thesis using Step(3)[OF f1 f2 f3] by auto      
  qed
  then obtain s' where 
     f2:"\<Gamma>\<turnstile>\<^sub>p (Coms[i := c'], toPar i ss' s) \<rightarrow>\<^sub>\<tau>\<^sup>* (Coms[i := c],toPar i ss'' s')  \<and>
          length (snd s') = length (snd s) \<and>
         (\<forall>j\<noteq>i. (getList s') ! j = (getList ( toPar i ss' s)) ! j)"
    by fastforce
  ultimately have "\<Gamma>\<turnstile>\<^sub>p (Coms, s) \<rightarrow>\<^sub>\<tau>\<^sup>* (Coms[i:=c], toPar i ss'' s') \<and> 
                   length (snd s') = length (snd s) " 
    by (meson converse_rtranclp_into_rtranclp)  
  moreover have "\<forall>j\<noteq>i. (getList s') ! j = (getList s) ! j"      
    using f1 f2
    by auto      
  ultimately show ?case by auto
qed


lemma length_list: assumes a0: "length l1 = length l2" and
              a1: "i<length l1" and
              a2: "\<forall>j\<noteq>i. l1!j = l2!j " 
            shows "l1[i:=l2!i] = l2"
  using a0 a1 a2
  by (simp add: nth_equalityI nth_list_update) 

lemma mult_step_in_par:
  "wf_conf Coms s \<Longrightarrow>  i< length Coms \<Longrightarrow> 
   \<Gamma>\<turnstile>\<^sub>c (Coms ! i, toSeqPar i s) \<rightarrow>\<^sub>\<tau>\<^sup>* (c, ss'') \<Longrightarrow>         
   \<exists>s'. \<Gamma>\<turnstile>\<^sub>p (Coms, s) \<rightarrow>\<^sub>\<tau>\<^sup>* (Coms[i:=c], toPar i ss'' s') \<and> length (snd s') = length (snd s) \<and>
        (\<forall>j\<noteq>i.  (getList (toPar i ss'' s')) ! j = (getList s)!j)"      
  using mult_step_in_par0 unfolding getList.simps 
  by (metis  toPar_eq_globs)      

lemma eq_toPar:"length (snd s') = length \<Sigma>ls \<Longrightarrow> 
        (\<forall>j. j \<noteq> i \<longrightarrow> getList (toPar i (\<Sigma>'g, \<Sigma>'ls) s') ! j = getList (\<Sigma>g, \<Sigma>ls) ! j) \<Longrightarrow>
       (toPar i (\<Sigma>'g, \<Sigma>'ls) s') = (toPar i (\<Sigma>'g, \<Sigma>'ls) (\<Sigma>g, \<Sigma>ls))"
  apply auto
  by (metis length_list list_update_overwrite nth_equalityI)

lemma mult_step_in_par1:
  assumes a0:"wf_conf Coms s" and a1:"i< length Coms" and
   a2:"\<Gamma>\<turnstile>\<^sub>c (Coms ! i, toSeqPar i s) \<rightarrow>\<^sub>\<tau>\<^sup>* (c, ss'')"
 shows "\<Gamma>\<turnstile>\<^sub>p (Coms, s) \<rightarrow>\<^sub>\<tau>\<^sup>* (Coms[i:=c], toPar i ss'' s)"    
proof-
  obtain s' where "\<Gamma>\<turnstile>\<^sub>p (Coms, s) \<rightarrow>\<^sub>\<tau>\<^sup>* (Coms[i:=c], toPar i ss'' s') \<and> length (snd s') = length (snd s) \<and>
        (\<forall>j\<noteq>i.  (getList (toPar i ss'' s')) ! j = (getList s)!j)"
    using mult_step_in_par[OF a0 a1 a2] by auto
  moreover have "toPar i ss'' s' = toPar i ss'' s"
    using eq_toPar calculation by auto
  ultimately show ?thesis by auto
qed
  

lemma p_step_local_length:"\<Gamma>\<turnstile>\<^sub>p (c, s) \<rightarrow>\<^sub>\<tau>\<^sup>* (c', s') \<Longrightarrow> 
      length( getList s') =length ( getList  s)"
proof (induct rule: rtranclp_induct2[case_names Refl Step] )
  case Refl
  then show ?case by auto
next
  case (Step c' s' c'' s'')  
  then show ?case
    by (metis eq_length_p_step' getList.simps steppe_stepp)
qed


lemma mult_step_in_par':
  "wf_conf Coms s \<Longrightarrow>  i< length Coms \<Longrightarrow> 
   \<Gamma>\<turnstile>\<^sub>c (Coms ! i, toSeqPar i s) \<rightarrow>\<^sub>\<tau>\<^sup>* (c, ss'') \<Longrightarrow>         
   \<exists>s'. \<Gamma>\<turnstile>\<^sub>p (Coms, s) \<rightarrow>\<^sub>\<tau>\<^sup>* (Coms[i:=c], toPar i ss'' s') \<and> (\<forall>j\<noteq>i. (getList s') ! j = (getList s)!j)"    
  using mult_step_in_par0 by blast
  
lemma mult_step_in_par_ev:
  "wf_conf Coms s \<Longrightarrow>  i< length Coms \<Longrightarrow>    
   \<Gamma>\<turnstile>\<^sub>c\<^sub>v (Coms ! i, toSeqPar i s) \<rightarrow>\<^sup>+ (c, ss') \<Longrightarrow> 
   \<exists>s'. \<Gamma>\<turnstile>\<^sub>p\<^sub>v (Coms, s) \<rightarrow>\<^sup>+ (Coms[i:=c], toPar i ss' s') \<and>  length (snd s') = length (snd s) \<and> 
        (\<forall>j\<noteq>i.   (getList (toPar i ss' s')) ! j = (getList s) ! j)" 
proof(clarify)
  fix c' ss1' c'' ss2'
  assume a0:"wf_conf Coms s" and 
            a1:"i < length Coms" and
            a2:"\<Gamma>\<turnstile>\<^sub>c (Coms ! i, toSeqPar i s) \<rightarrow>\<^sub>\<tau>\<^sup>* (c', ss1')" and
        a3:"\<Gamma>\<turnstile>\<^sub>c\<^sub>(Some v) (c', ss1') \<rightarrow> (c'', ss2')" and 
        a4:"\<Gamma>\<turnstile>\<^sub>c (c'', ss2') \<rightarrow>\<^sub>\<tau>\<^sup>* (c, ss')"
  then obtain s' where 
  step1:"\<Gamma>\<turnstile>\<^sub>p (Coms, s) \<rightarrow>\<^sub>\<tau>\<^sup>* (Coms[i:=c'], toPar i ss1' s') \<and> length (snd s') = length (snd s) \<and>                           
          (\<forall>j\<noteq>i.  (getList (toPar i ss1' s')) ! j = (getList s)!j)"
    using mult_step_in_par[OF a0 a1 a2] by auto
  moreover have step2:"\<Gamma>\<turnstile>\<^sub>p\<^sub>(Some v) (Coms[i:=c'], toPar i ss1' s') \<rightarrow> (Coms[i:=c''], toPar i ss2' (toPar i ss1' s')) \<and>                         
                        (\<forall>j\<noteq>i. (getList (toPar i ss2' (toPar i ss1' s'))) ! j = (getList s)!j)"
  proof-
    have "i< length (Coms[i:=c'])" using a1 by auto    
    moreover have "ss1' = toSeqPar i (toPar i ss1' s')" 
      using  a0 a1  local.step1 
      by (metis dec_induct less_Suc_eq prod.collapse snd_eqD wf_conf.elims(2) 
          wfs_i.simps wfs_tran_toSeqPar_toPar)
    ultimately show ?thesis
      using a3 step_pev.simps step1
      by (smt getList.simps list_update_overwrite nth_list_update_eq toPar_eq_globs) 
  qed
  moreover have
      "\<exists>s''. \<Gamma>\<turnstile>\<^sub>p (Coms[i:=c''], toPar i ss2' (toPar i ss1' s')) \<rightarrow>\<^sub>\<tau>\<^sup>* (Coms[i:=c], toPar i ss' s'') \<and> 
            length (snd s'') = length (snd s) \<and>
            (\<forall>j\<noteq>i. (getList ( toPar i ss' s'')) ! j = (getList s)!j)"
  proof-
    have a01:"wf_conf (Coms[i:=c'']) (toPar i ss2' (toPar i ss1' s'))"
      using step2 a0 local.step1 wf_conf_par_step wf_conf_step by blast
    have a02:"i<length (Coms[i:=c''])"
      by (simp add: a1)    
    then have "wfs_i i (toPar i ss2' (toPar i ss1' s')) "  
      using  a0 a1  local.step1
      by (smt Suc_less_SucD getList.simps le_imp_less_Suc length_list_update less_trans_Suc 
         p_step_local_length sndI step2 step_pev_pair_elim_cases wf_conf.elims(2) wfs_i.elims(3))
    then have "ss2' = toSeqPar i (toPar i ss2' (toPar i ss1' s'))" 
      using  a0 a1  local.step1  wfs_tran_toSeqPar_toPar by simp
    then have a03:"\<Gamma>\<turnstile>\<^sub>c (Coms[i := c''] ! i, toSeqPar i (toPar i ss2' (toPar i ss1' s'))) \<rightarrow>\<^sub>\<tau>\<^sup>*
           (c, ss')"
      using a4 a02 by auto
    then obtain s'' where "\<Gamma>\<turnstile>\<^sub>p (Coms[i := c''], toPar i ss2' (toPar i ss1' s')) \<rightarrow>\<^sub>\<tau>\<^sup>* (Coms[i := c'', i := c], toPar i ss' s'') \<and>
          (\<forall>j. j \<noteq> i \<longrightarrow> getList (toPar i ss' s'') ! j = getList (toPar i ss2' (toPar i ss1' s')) ! j)"
      using mult_step_in_par[OF a01 a02 a03] by auto
    moreover have "\<forall>j. j \<noteq> i \<longrightarrow> getList (toPar i ss' s'') ! j = getList s ! j "
      using calculation a3 a4 step2 by simp
    ultimately show ?thesis apply auto
      by (metis getList.simps length_list_update p_step_local_length snd_conv step1)
  qed
  then obtain s'' where "\<Gamma>\<turnstile>\<^sub>p (Coms[i:=c''], toPar i ss2' (toPar i ss1' s')) \<rightarrow>\<^sub>\<tau>\<^sup>* (Coms[i:=c], toPar i ss' s'') \<and> 
                         length (snd s'') = length (snd s) \<and>
                          (\<forall>j\<noteq>i. (getList ( toPar i ss' s'')) ! j = (getList s)!j)"
    by auto  
  ultimately show ?thesis by blast  
qed

lemma mult_step_in_par_ev1:
  assumes a0:"wf_conf Coms s" and  a1:"i< length Coms" and
   a2:"\<Gamma>\<turnstile>\<^sub>c\<^sub>v (Coms ! i, toSeqPar i s) \<rightarrow>\<^sup>+ (c, ss')" 
 shows "\<Gamma>\<turnstile>\<^sub>p\<^sub>v (Coms, s) \<rightarrow>\<^sup>+ (Coms[i:=c], toPar i ss' s)"
  using mult_step_in_par_ev
proof-
  obtain s' where "\<Gamma>\<turnstile>\<^sub>p\<^sub>v (Coms, s) \<rightarrow>\<^sup>+ (Coms[i := c], toPar i ss' s') \<and>
       length (snd s') = length (snd s) \<and> (\<forall>j. j \<noteq> i \<longrightarrow> getList (toPar i ss' s') ! j = getList s ! j)"
    using mult_step_in_par_ev[OF a0 a1 a2] by fast
  moreover have "toPar i ss' s' = toPar i ss' s"
    using eq_toPar calculation by auto
  ultimately show ?thesis by auto
qed
  
lemma get_list_drop_local:"getList s = a#as \<Longrightarrow> a#as = getList(a #s  (drop_local s))"  
  by (cases s, auto)


  
lemma step_s:"\<Gamma>\<turnstile>\<^sub>c ((a # c'') ! 0, toSeqPar 0 s) \<rightarrow>\<^sub>\<tau>\<^sup>* (LanguageCon.com.Skip, toSeqPar 0 s) \<Longrightarrow>
        wf_conf (a # c'') s \<Longrightarrow>  0< length (a # c'') \<Longrightarrow>        
       \<Gamma>\<turnstile>\<^sub>p (a # c'', s) \<rightarrow>\<^sub>\<tau>\<^sup>* (Skip#c'', s)"  
  apply (frule mult_step_in_par[where \<Gamma> = \<Gamma> and i = 0],auto)
  subgoal for s'
    apply (cases s; cases s'; auto;  frule  p_step_local_length; auto )
    by (metis (no_types) Cons_nth_drop_Suc One_nat_def diff_Suc_1 drop0 
         length_Cons nth_Cons_Suc nth_equalityI zero_less_Suc)    
   
  done
    
lemma par_all_skip_rtran:
    "\<forall>i<length C. \<Gamma>\<turnstile>\<^sub>c (C!i, toSeqPar i s) \<rightarrow>\<^sub>\<tau>\<^sup>* (Skip, toSeqPar i s) \<Longrightarrow> length C > 0 \<Longrightarrow>
       wf_conf C s \<Longrightarrow>
       \<exists>C'. \<Gamma>\<turnstile>\<^sub>p (C,s) \<rightarrow>\<^sub>\<tau>\<^sup>* (C', s) \<and> (\<forall>i<length C'. C' ! i = Skip) \<and> C' \<noteq> []"
proof (induction C arbitrary: s)
  case (Nil) thus ?case by auto
next
  case (Cons a as)   
  { assume a0:"as=Nil"    
    then have "\<Gamma>\<turnstile>\<^sub>p (a#as, s) \<rightarrow>\<^sub>\<tau>\<^sup>* ((a#as)[0:=Skip],s)" 
    proof-      
      have a1:"\<Gamma>\<turnstile>\<^sub>c ([a]!0, toSeqPar 0 s) \<rightarrow>\<^sub>\<tau>\<^sup>* (Skip, toSeqPar 0 s)" using Cons(2)
        by auto   
      have a2:"wf_conf [a] s" using Cons(4) a0 by auto                
      thus ?thesis using  a0 mult_step_in_par[OF a2 _ a1] Cons(2,3)
        by (simp add: step_s)
    qed
    then have ?case using a0 by auto
  }
  moreover { fix a1 as1
    let ?s' = "drop_local s"
    assume a0:"as=a1#as1"    
    then have "\<forall>i<length (as). \<Gamma>\<turnstile>\<^sub>c (as ! i, toSeqPar i ?s') \<rightarrow>\<^sub>\<tau>\<^sup>* (LanguageCon.com.Skip, toSeqPar i ?s')" 
      using   Cons.prems(3) Cons(2) by (cases s; auto)                 
    moreover have len:"0 < length as" using a0 by auto
    moreover have wf:"wf_conf as ?s'" using Cons(4) by (cases s, auto)
    ultimately obtain c'' where 
     step1:"\<Gamma>\<turnstile>\<^sub>p (as, ?s') \<rightarrow>\<^sub>\<tau>\<^sup>* (c'',?s') \<and> (\<forall>i<length c''. c'' ! i = LanguageCon.com.Skip) \<and> c'' \<noteq> []"
      using Cons(1) by presburger
    have "\<Gamma>\<turnstile>\<^sub>p (a#as, s) \<rightarrow>\<^sub>\<tau>\<^sup>* (a#c'', s)"  
      using par_tran_comp_rtran[OF conjunct1[OF step1] wf] Cons(4)  apply (cases s, auto)
      by (metis Suc_le_length_iff drop0 drop_Suc list.sel(3))      
    then have step:"\<Gamma>\<turnstile>\<^sub>p (a#as, s) \<rightarrow>\<^sub>\<tau>\<^sup>* (a#c'', s) \<and> (\<forall>i<length c''. c'' ! i = LanguageCon.com.Skip) \<and> c'' \<noteq> []"
      using step1 by auto
    moreover have step_c:"\<Gamma>\<turnstile>\<^sub>c ((a # c'') ! 0, toSeqPar 0 s) \<rightarrow>\<^sub>\<tau>\<^sup>* (LanguageCon.com.Skip, toSeqPar 0 s)" 
      using Cons by auto
    ultimately have "\<Gamma>\<turnstile>\<^sub>p (a # c'', s) \<rightarrow>\<^sub>\<tau>\<^sup>* (Skip#c'', s)" 
      using step_s[OF step_c] Cons.prems(3) wf_conf_step  by blast                      
    then have ?case using step
      by (metis (no_types, hide_lams) length_Cons less_Suc_eq_0_disj list.distinct(1) nth_Cons_0 nth_Cons_Suc rtranclp_trans)       
  }      
  ultimately show ?case
    using list.exhaust by blast
      
qed  
    
lemma par_not_normal_not_event:
  assumes a0:"All_End (c, \<sigma>)" and
              a1:"\<Gamma>\<turnstile>\<^sub>p\<^sub>(Some v) (c, \<sigma>) \<rightarrow> (c', s1)"
  shows "P"
  by (metis a0 a1 eq_fst_iff final_no_par_step)


 
type_synonym ('s) rel1 = "('s \<times> 's) set"

definition R_eq_locals::"('g\<times>('l list)) rel1"
  where "R_eq_locals \<equiv> {(x,y). local_list_par x = local_list_par y}"
  
definition related_transitions::"('s) rel1 \<Rightarrow> ('s1) rel1 \<Rightarrow> 
                                 (('s,'s1) rel) \<Rightarrow> ('s tran, 's1 tran) rel"
 ("'(_, _')\<^sub>_")
where
"related_transitions R R' \<alpha> \<equiv> {((\<sigma>,\<sigma>'),(\<Sigma>,\<Sigma>')). (\<sigma>,\<sigma>')\<in>R \<and> (\<Sigma>,\<Sigma>')\<in>R'  \<and> (\<sigma>,\<Sigma>)\<in>\<alpha> \<and> (\<sigma>',\<Sigma>')\<in>\<alpha>}"



lemma related_transition_intro:"(\<sigma>,\<Sigma>) \<in> \<alpha> \<Longrightarrow>
       (\<sigma>', \<Sigma>') \<in> \<alpha> \<Longrightarrow>
       (\<sigma>, \<sigma>') \<in> G\<^sub>c \<Longrightarrow>
       (\<Sigma>, \<Sigma>') \<in> G\<^sub>s \<Longrightarrow> ((\<sigma>,\<sigma>'), \<Sigma>, \<Sigma>') \<in> (G\<^sub>c, G\<^sub>s\<^sup>*)\<^sub>\<alpha> "
  unfolding related_transitions_def by auto

lemma related_transition_tran: 
 " (\<sigma>,\<Sigma>)\<in>\<alpha> \<Longrightarrow>
  (\<Sigma>,\<Sigma>') \<in> G\<^sub>s \<Longrightarrow>
  ((\<sigma>,\<sigma>'), \<Sigma>', \<Sigma>'') \<in> (G\<^sub>c, G\<^sub>s\<^sup>*)\<^sub>\<alpha> \<Longrightarrow>
  ((\<sigma>, \<sigma>'), \<Sigma>,  \<Sigma>'') \<in> (G\<^sub>c, G\<^sub>s\<^sup>*)\<^sub>\<alpha>"
  unfolding related_transitions_def by auto
       


lemma not_tau_event:"\<Gamma>\<^sub>c\<turnstile>\<^sub>c\<^sub>\<tau> (c,s) \<rightarrow> (c1,s1) \<Longrightarrow> \<not> (e=Some v \<and> (\<Gamma>\<^sub>c\<turnstile>\<^sub>c\<^sub>e (c, s) \<rightarrow> (c1,s1)))"
  using stepc_stepce_unique stepce_stepc by fastforce
    
lemma not_event_tau:"(e=Some v \<and> (\<Gamma>\<^sub>c\<turnstile>\<^sub>c\<^sub>e (c, s) \<rightarrow> (c1,s1))) \<Longrightarrow> \<not> \<Gamma>\<^sub>c\<turnstile>\<^sub>c\<^sub>\<tau> (c,s) \<rightarrow> (c1,s1) "
  using stepc_stepce_unique stepce_stepc by fastforce
thm stepce_stepc

lemma not_env_comp:"\<Gamma>\<^sub>c\<turnstile>\<^sub>c\<^sub>e (c,  ss) \<rightarrow> (c1,ss1) \<Longrightarrow>  \<not> \<Gamma>\<^sub>c\<turnstile>\<^sub>c(c,s) \<rightarrow>\<^sub>e (c1, s1)"
  using env_c_c' step_change_p_or_eq_s stepce_stepc by fast
    
lemma not_local_comp:"\<Gamma>\<^sub>c\<turnstile>\<^sub>c(c,ss) \<rightarrow>\<^sub>e (c1,ss1) \<Longrightarrow> \<not> \<Gamma>\<^sub>c\<turnstile>\<^sub>c\<^sub>e (c, s) \<rightarrow> (c1,s1)"
  using env_c_c' step_change_p_or_eq_s stepce_stepc by fast
    
(* method solve =
(
match premises in P[thin]:"\<And>a. ?P a"  \<Rightarrow>
  \<open>insert P\<close>
) *)

definition toSeq ::"(('g\<times>'l)\<times>('l list)) \<Rightarrow> (('g\<times>'l)) "
  where
"toSeq ns \<equiv> (fst ns)"

type_synonym ('g,'l,'p,'f,'e) config_p = "('g \<times> 'l,'p,'f,'e)com \<times> ('g,'l) c_state"


coinductive "RGSim"::"[('g\<times>'l,'p,'f,'e) body,('g,'l,'p,'f,'e) config_p, (('g,'l) c_state) rel1, 
                           (('g,'l) c_state) rel1,
                     (('g,'l) c_state,('g1,'l1) c_state) rel,
                     (('g,'l) c_state,('g1,'l1) c_state) rel,
                     (('g,'l) c_state,('g1,'l1) c_state)  rel,
                     ('g1\<times>'l1,'p,'f,'e) body,('g1,'l1,'p,'f,'e) config_p, (('g1,'l1) c_state) rel1, 
                            (('g1,'l1) c_state) rel1
                    ] \<Rightarrow> bool" 
("'(_,_,_,_')/ \<succeq>\<^sub>'(\<^sub>_\<^sub>;\<^sub>_\<^sub>;\<^sub>_\<^sub>')/ '(_,_,_,_')" [81,81,81,81,81,81,81,81,81,81,81] 100)
where
  rgsim: "\<lbrakk>(\<sigma>,\<Sigma>)\<in>\<alpha>;                    
           \<forall>c\<^sub>c' \<sigma>'. \<Gamma>\<^sub>c\<turnstile>\<^sub>c\<^sub>\<tau> (c\<^sub>c,toSeq \<sigma>) \<rightarrow> (c\<^sub>c', toSeq \<sigma>') \<and> snd \<sigma> = snd \<sigma>' \<longrightarrow> 
             (\<exists>c\<^sub>s' \<Sigma>'.  \<Gamma>\<^sub>s\<turnstile>\<^sub>c (c\<^sub>s, toSeq \<Sigma>) \<rightarrow>\<^sub>\<tau>\<^sup>* (c\<^sub>s', toSeq \<Sigma>') \<and> snd \<Sigma> = snd \<Sigma>' \<and>
              (\<sigma>', \<Sigma>')\<in>\<alpha> \<and> (((\<sigma>,\<sigma>'),(\<Sigma>,\<Sigma>')) \<in> (G\<^sub>c,G\<^sub>s\<^sup>*)\<^sub>\<alpha>) \<and>
             (\<Gamma>\<^sub>c,(c\<^sub>c', \<sigma>'),R\<^sub>c,G\<^sub>c) \<succeq>\<^sub>(\<^sub>\<alpha>\<^sub>;\<^sub>\<gamma>\<^sub>q\<^sub>;\<^sub>\<gamma>\<^sub>a\<^sub>) (\<Gamma>\<^sub>s,(c\<^sub>s', \<Sigma>'),R\<^sub>s,G\<^sub>s));           
           \<forall>v c\<^sub>c' \<sigma>' e. e=Some v \<and> \<Gamma>\<^sub>c\<turnstile>\<^sub>c\<^sub>e (c\<^sub>c, toSeq \<sigma>) \<rightarrow> (c\<^sub>c', toSeq \<sigma>') \<and> snd \<sigma> = snd \<sigma>' \<longrightarrow> 
             (\<exists> c\<^sub>s' \<Sigma>'. \<Gamma>\<^sub>s\<turnstile>\<^sub>c\<^sub>v (c\<^sub>s,toSeq \<Sigma>) \<rightarrow>\<^sup>+  (c\<^sub>s', toSeq \<Sigma>') \<and> snd \<Sigma> = snd \<Sigma>' \<and>
              (\<sigma>', \<Sigma>')\<in>\<alpha> \<and> (((\<sigma>,\<sigma>'),(\<Sigma>, \<Sigma>')) \<in> (G\<^sub>c,G\<^sub>s\<^sup>*)\<^sub>\<alpha>) \<and>  
                (\<Gamma>\<^sub>c,(c\<^sub>c',(\<sigma>')),R\<^sub>c,G\<^sub>c) \<succeq>\<^sub>(\<^sub>\<alpha>\<^sub>;\<^sub>\<gamma>\<^sub>q\<^sub>;\<^sub>\<gamma>\<^sub>a\<^sub>) (\<Gamma>\<^sub>s,(c\<^sub>s',\<Sigma>'),R\<^sub>s,G\<^sub>s));           
           (\<forall>\<sigma>' \<Sigma>'. (((\<sigma>,\<sigma>'),(\<Sigma>,\<Sigma>')) \<in> (R\<^sub>c,R\<^sub>s\<^sup>*)\<^sub>\<alpha>)  \<longrightarrow> 
               (\<Gamma>\<^sub>c,(c\<^sub>c, \<sigma>'),R\<^sub>c,G\<^sub>c) \<succeq>\<^sub>(\<^sub>\<alpha>\<^sub>;\<^sub>\<gamma>\<^sub>q\<^sub>;\<^sub>\<gamma>\<^sub>a\<^sub>) (\<Gamma>\<^sub>s,(c\<^sub>s, \<Sigma>'),R\<^sub>s,G\<^sub>s));           
            c\<^sub>c = Skip \<longrightarrow> (\<exists>\<Sigma>'. (((\<sigma>, \<sigma>),(\<Sigma>, \<Sigma>')) \<in> (G\<^sub>c,G\<^sub>s\<^sup>*)\<^sub>\<alpha>) \<and> snd \<Sigma> = snd \<Sigma>' \<and>
              (\<sigma>, \<Sigma>')\<in>\<gamma>\<^sub>q \<and> \<gamma>\<^sub>q\<subseteq>\<alpha> \<and> \<Gamma>\<^sub>s\<turnstile>\<^sub>c (c\<^sub>s,toSeq \<Sigma>) \<rightarrow>\<^sub>\<tau>\<^sup>* (Skip, toSeq \<Sigma>'));           
            c\<^sub>c = Throw  \<longrightarrow> (\<exists>\<Sigma>'. (((\<sigma>, \<sigma>),(\<Sigma>, \<Sigma>')) \<in> (G\<^sub>c,G\<^sub>s\<^sup>*)\<^sub>\<alpha>) \<and> snd \<Sigma> = snd \<Sigma>' \<and>
              (\<sigma>, \<Sigma>')\<in>\<gamma>\<^sub>a \<and> \<gamma>\<^sub>a\<subseteq>\<alpha> \<and> \<Gamma>\<^sub>s\<turnstile>\<^sub>c (c\<^sub>s,toSeq \<Sigma>) \<rightarrow>\<^sub>\<tau>\<^sup>* (Throw, toSeq  \<Sigma>'));
            \<forall>f. c\<^sub>c = Fault f  \<longrightarrow> 
              (\<exists>\<Sigma>'. (((\<sigma>, \<sigma>),(\<Sigma>, \<Sigma>')) \<in> (G\<^sub>c,G\<^sub>s\<^sup>*)\<^sub>\<alpha>) \<and> 
                     \<Gamma>\<^sub>s\<turnstile>\<^sub>c (c\<^sub>s,toSeq \<Sigma>) \<rightarrow>\<^sub>\<tau>\<^sup>* (Fault f, toSeq \<Sigma>') \<and>  snd \<Sigma> = snd \<Sigma>' \<and> (\<sigma>,\<Sigma>')\<in>\<alpha>);
            c\<^sub>c = Stuck  \<longrightarrow> 
              (\<exists>\<Sigma>'. (((\<sigma>, \<sigma>),(\<Sigma>, \<Sigma>')) \<in> (G\<^sub>c,G\<^sub>s\<^sup>*)\<^sub>\<alpha>) \<and> 
                    \<Gamma>\<^sub>s\<turnstile>\<^sub>c (c\<^sub>s,toSeq \<Sigma>) \<rightarrow>\<^sub>\<tau>\<^sup>* (Stuck, toSeq \<Sigma>') \<and>  snd \<Sigma> = snd \<Sigma>' \<and> (\<sigma>,\<Sigma>')\<in>\<alpha>)
          \<rbrakk> \<Longrightarrow> (\<Gamma>\<^sub>c,(c\<^sub>c, \<sigma>),R\<^sub>c,G\<^sub>c) \<succeq>\<^sub>(\<^sub>\<alpha>\<^sub>;\<^sub>\<gamma>\<^sub>q\<^sub>;\<^sub>\<gamma>\<^sub>a\<^sub>) (\<Gamma>\<^sub>s,(c\<^sub>s, \<Sigma>),R\<^sub>s,G\<^sub>s)"
    
inductive_cases sim_elim_cases:
  "(\<Gamma>\<^sub>c,(c,s),R\<^sub>c,G\<^sub>c) \<succeq>\<^sub>(\<^sub>\<alpha>\<^sub>;\<^sub>\<gamma>\<^sub>n\<^sub>;\<^sub>\<gamma>\<^sub>a\<^sub>) (\<Gamma>\<^sub>s,(c',s'),R\<^sub>s,G\<^sub>s)" 
 
thm sim_elim_cases 
inductive_cases sim_elim_cases_c[split_format (complete)]:
  "(\<Gamma>\<^sub>c,(Skip,s),R\<^sub>c,G\<^sub>c) \<succeq>\<^sub>(\<^sub>\<alpha>\<^sub>;\<^sub>\<gamma>\<^sub>n\<^sub>;\<^sub>\<gamma>\<^sub>a\<^sub>) (\<Gamma>\<^sub>s,(c',s'),R\<^sub>s,G\<^sub>s)"  
  "(\<Gamma>\<^sub>c,(Throw, s),R\<^sub>c,G\<^sub>c) \<succeq>\<^sub>(\<^sub>\<alpha>\<^sub>;\<^sub>\<gamma>\<^sub>n\<^sub>;\<^sub>\<gamma>\<^sub>a\<^sub>) (\<Gamma>\<^sub>s,(c',s'),R\<^sub>s,G\<^sub>s)"        
  "(\<Gamma>\<^sub>c,(Fault f, s),R\<^sub>c,G\<^sub>c) \<succeq>\<^sub>(\<^sub>\<alpha>\<^sub>;\<^sub>\<gamma>\<^sub>n\<^sub>;\<^sub>\<gamma>\<^sub>a\<^sub>) (\<Gamma>\<^sub>s,(c',s'),R\<^sub>s,G\<^sub>s)"        
  "(\<Gamma>\<^sub>c,(Stuck, s),R\<^sub>c,G\<^sub>c) \<succeq>\<^sub>(\<^sub>\<alpha>\<^sub>;\<^sub>\<gamma>\<^sub>n\<^sub>;\<^sub>\<gamma>\<^sub>a\<^sub>) (\<Gamma>\<^sub>s,(c',s'),R\<^sub>s,G\<^sub>s)"



lemma dest_sim_ev_step:
  "(\<Gamma>\<^sub>c,(c\<^sub>c,\<sigma>),R\<^sub>c,G\<^sub>c) \<succeq>\<^sub>(\<^sub>\<alpha>\<^sub>;\<^sub>\<gamma>\<^sub>n\<^sub>;\<^sub>\<gamma>\<^sub>a\<^sub>) (\<Gamma>\<^sub>s,(c\<^sub>s,\<Sigma>),R\<^sub>s,G\<^sub>s) \<Longrightarrow>
    \<Gamma>\<^sub>c\<turnstile>\<^sub>c\<^sub>(Some v) (c\<^sub>c, toSeq \<sigma>) \<rightarrow> (c\<^sub>c', toSeq \<sigma>') \<Longrightarrow> snd \<sigma> = snd \<sigma>' \<Longrightarrow>
    \<exists> c\<^sub>s' \<Sigma>'. \<Gamma>\<^sub>s\<turnstile>\<^sub>c\<^sub>v (c\<^sub>s, toSeq \<Sigma>) \<rightarrow>\<^sup>+  (c\<^sub>s', toSeq \<Sigma>') \<and> snd \<Sigma> = snd \<Sigma>' \<and>
              (\<sigma>', \<Sigma>')\<in>\<alpha> \<and> (((\<sigma>, \<sigma>'),(\<Sigma>, \<Sigma>')) \<in> (G\<^sub>c,G\<^sub>s\<^sup>*)\<^sub>\<alpha>) \<and>  
                (\<Gamma>\<^sub>c,(c\<^sub>c',\<sigma>'),R\<^sub>c,G\<^sub>c) \<succeq>\<^sub>(\<^sub>\<alpha>\<^sub>;\<^sub>\<gamma>\<^sub>n\<^sub>;\<^sub>\<gamma>\<^sub>a\<^sub>) (\<Gamma>\<^sub>s,(c\<^sub>s',\<Sigma>'),R\<^sub>s,G\<^sub>s)"  
  by (erule sim_elim_cases; cases \<sigma>', force)
 
lemma dest_sim_ev_step1:
  "(\<Gamma>\<^sub>c,(c\<^sub>c,\<sigma>),R\<^sub>c,G\<^sub>c) \<succeq>\<^sub>(\<^sub>\<alpha>\<^sub>;\<^sub>\<gamma>\<^sub>n\<^sub>;\<^sub>\<gamma>\<^sub>a\<^sub>) (\<Gamma>\<^sub>s,(c\<^sub>s,\<Sigma>),R\<^sub>s,G\<^sub>s) \<Longrightarrow>
    (\<forall>c\<^sub>c' \<sigma>' v. \<Gamma>\<^sub>c\<turnstile>\<^sub>c\<^sub>(Some v) (c\<^sub>c, toSeq \<sigma>) \<rightarrow> (c\<^sub>c', toSeq \<sigma>') \<longrightarrow> snd \<sigma> = snd \<sigma>' \<longrightarrow>
    (\<exists> c\<^sub>s' \<Sigma>'. \<Gamma>\<^sub>s\<turnstile>\<^sub>c\<^sub>v (c\<^sub>s, toSeq \<Sigma>) \<rightarrow>\<^sup>+  (c\<^sub>s', toSeq \<Sigma>') \<and> 
              (\<sigma>', \<Sigma>')\<in>\<alpha> \<and> (((\<sigma>, \<sigma>'),(\<Sigma>, \<Sigma>')) \<in> (G\<^sub>c,G\<^sub>s\<^sup>*)\<^sub>\<alpha>) \<and> snd \<Sigma> = snd \<Sigma>' \<and>  
                (\<Gamma>\<^sub>c,(c\<^sub>c', \<sigma>'),R\<^sub>c,G\<^sub>c) \<succeq>\<^sub>(\<^sub>\<alpha>\<^sub>;\<^sub>\<gamma>\<^sub>n\<^sub>;\<^sub>\<gamma>\<^sub>a\<^sub>) (\<Gamma>\<^sub>s,(c\<^sub>s', \<Sigma>'),R\<^sub>s,G\<^sub>s)))"  
  by (erule sim_elim_cases, auto)

   
lemma dest_sim_tau_step:
  "(\<Gamma>\<^sub>c,(c\<^sub>c,\<sigma>),R\<^sub>c,G\<^sub>c) \<succeq>\<^sub>(\<^sub>\<alpha>\<^sub>;\<^sub>\<gamma>\<^sub>n\<^sub>;\<^sub>\<gamma>\<^sub>a\<^sub>) (\<Gamma>\<^sub>s,(c\<^sub>s,\<Sigma>),R\<^sub>s,G\<^sub>s) \<Longrightarrow>
    \<Gamma>\<^sub>c\<turnstile>\<^sub>c\<^sub>\<tau> (c\<^sub>c, toSeq \<sigma>) \<rightarrow> (c\<^sub>c', toSeq \<sigma>') \<Longrightarrow> snd \<sigma> = snd \<sigma>' \<Longrightarrow>
    \<exists>c\<^sub>s' \<Sigma>'.  \<Gamma>\<^sub>s\<turnstile>\<^sub>c (c\<^sub>s, toSeq \<Sigma>) \<rightarrow>\<^sub>\<tau>\<^sup>* (c\<^sub>s', toSeq \<Sigma>') \<and> snd \<Sigma> = snd \<Sigma>' \<and>
              (\<sigma>', \<Sigma>')\<in>\<alpha> \<and> 
              (((\<sigma>, \<sigma>'),(\<Sigma>,  \<Sigma>')) \<in> (G\<^sub>c,G\<^sub>s\<^sup>*)\<^sub>\<alpha>) \<and>
             (\<Gamma>\<^sub>c,(c\<^sub>c', \<sigma>'),R\<^sub>c,G\<^sub>c) \<succeq>\<^sub>(\<^sub>\<alpha>\<^sub>;\<^sub>\<gamma>\<^sub>n\<^sub>;\<^sub>\<gamma>\<^sub>a\<^sub>) (\<Gamma>\<^sub>s,(c\<^sub>s', \<Sigma>'),R\<^sub>s,G\<^sub>s)"
    by (erule sim_elim_cases,cases \<sigma>', force)

lemma dest_sim_env_step:  
  "(\<Gamma>\<^sub>c,(c\<^sub>c,\<sigma>),R\<^sub>c,G\<^sub>c) \<succeq>\<^sub>(\<^sub>\<alpha>\<^sub>;\<^sub>\<gamma>\<^sub>n\<^sub>;\<^sub>\<gamma>\<^sub>a\<^sub>) (\<Gamma>\<^sub>s,(c\<^sub>s,\<Sigma>),R\<^sub>s,G\<^sub>s) \<Longrightarrow>
   (((\<sigma>, \<sigma>'),(\<Sigma>,\<Sigma>')) \<in> (R\<^sub>c,R\<^sub>s\<^sup>*)\<^sub>\<alpha>) \<Longrightarrow>
   (\<Gamma>\<^sub>c,(c\<^sub>c,\<sigma>'),R\<^sub>c,G\<^sub>c) \<succeq>\<^sub>(\<^sub>\<alpha>\<^sub>;\<^sub>\<gamma>\<^sub>n\<^sub>;\<^sub>\<gamma>\<^sub>a\<^sub>) (\<Gamma>\<^sub>s,(c\<^sub>s,\<Sigma>'),R\<^sub>s,G\<^sub>s)"  
  by (erule sim_elim_cases,  cases \<sigma>', cases \<Sigma>', force)
  
 lemma dest_sim_alpha:  
 "(\<Gamma>\<^sub>c,(c\<^sub>c,\<sigma>),R\<^sub>c,G\<^sub>c) \<succeq>\<^sub>(\<^sub>\<alpha>\<^sub>;\<^sub>\<gamma>\<^sub>n\<^sub>;\<^sub>\<gamma>\<^sub>a\<^sub>) (\<Gamma>\<^sub>s,(c\<^sub>s,\<Sigma>),R\<^sub>s,G\<^sub>s) \<Longrightarrow>
   (\<sigma>,\<Sigma>)  \<in> \<alpha>" 
   by (erule sim_elim_cases,auto)

lemma dest_final_skip:
"(\<Gamma>\<^sub>c,(Skip, \<sigma>),R\<^sub>c,G\<^sub>c) \<succeq>\<^sub>(\<^sub>\<alpha>\<^sub>;\<^sub>\<gamma>\<^sub>q\<^sub>;\<^sub>\<gamma>\<^sub>a\<^sub>) (\<Gamma>\<^sub>s,(c\<^sub>s, \<Sigma>),R\<^sub>s,G\<^sub>s) \<Longrightarrow>
  \<exists>\<Sigma>'. (((\<sigma>, \<sigma>),(\<Sigma>, \<Sigma>')) \<in> (G\<^sub>c,G\<^sub>s\<^sup>*)\<^sub>\<alpha>) \<and> snd \<Sigma> = snd \<Sigma>' \<and>
        (\<sigma>, \<Sigma>')\<in>\<gamma>\<^sub>q \<and> \<gamma>\<^sub>q\<subseteq>\<alpha> \<and> \<Gamma>\<^sub>s\<turnstile>\<^sub>c (c\<^sub>s,toSeq \<Sigma>) \<rightarrow>\<^sub>\<tau>\<^sup>* (Skip, toSeq \<Sigma>')"
  by (erule sim_elim_cases,auto)

lemma dest_final_Throw:
"(\<Gamma>\<^sub>c,(Throw, \<sigma>),R\<^sub>c,G\<^sub>c) \<succeq>\<^sub>(\<^sub>\<alpha>\<^sub>;\<^sub>\<gamma>\<^sub>q\<^sub>;\<^sub>\<gamma>\<^sub>a\<^sub>) (\<Gamma>\<^sub>s,(c\<^sub>s, \<Sigma>),R\<^sub>s,G\<^sub>s) \<Longrightarrow>
  \<exists>\<Sigma>'. (((\<sigma>, \<sigma>),(\<Sigma>, \<Sigma>')) \<in> (G\<^sub>c,G\<^sub>s\<^sup>*)\<^sub>\<alpha>) \<and> snd \<Sigma> = snd \<Sigma>' \<and>
        (\<sigma>, \<Sigma>')\<in>\<gamma>\<^sub>a \<and> \<gamma>\<^sub>a\<subseteq>\<alpha> \<and> \<Gamma>\<^sub>s\<turnstile>\<^sub>c (c\<^sub>s,toSeq \<Sigma>) \<rightarrow>\<^sub>\<tau>\<^sup>* (Throw, toSeq \<Sigma>')"
 by (erule sim_elim_cases,auto)

lemma dest_final_Fault:
"(\<Gamma>\<^sub>c,(Fault f, \<sigma>),R\<^sub>c,G\<^sub>c) \<succeq>\<^sub>(\<^sub>\<alpha>\<^sub>;\<^sub>\<gamma>\<^sub>q\<^sub>;\<^sub>\<gamma>\<^sub>a\<^sub>) (\<Gamma>\<^sub>s,(c\<^sub>s, \<Sigma>),R\<^sub>s,G\<^sub>s) \<Longrightarrow>
  \<exists>\<Sigma>'.  (((\<sigma>, \<sigma>),(\<Sigma>, \<Sigma>')) \<in> (G\<^sub>c,G\<^sub>s\<^sup>*)\<^sub>\<alpha>) \<and> snd \<Sigma> = snd \<Sigma>' \<and> snd \<Sigma> = snd \<Sigma>' \<and>
        \<Gamma>\<^sub>s\<turnstile>\<^sub>c (c\<^sub>s,toSeq \<Sigma>) \<rightarrow>\<^sub>\<tau>\<^sup>* (Fault f, toSeq \<Sigma>') \<and> (\<sigma>,\<Sigma>')\<in>\<alpha>"
  by (erule sim_elim_cases, auto)

lemma dest_final_Stuck:
"(\<Gamma>\<^sub>c,(Stuck, \<sigma>),R\<^sub>c,G\<^sub>c) \<succeq>\<^sub>(\<^sub>\<alpha>\<^sub>;\<^sub>\<gamma>\<^sub>q\<^sub>;\<^sub>\<gamma>\<^sub>a\<^sub>) (\<Gamma>\<^sub>s,(c\<^sub>s, \<Sigma>),R\<^sub>s,G\<^sub>s) \<Longrightarrow>
  \<exists>\<Sigma>'.  (((\<sigma>, \<sigma>),(\<Sigma>, \<Sigma>')) \<in> (G\<^sub>c,G\<^sub>s\<^sup>*)\<^sub>\<alpha>) \<and> snd \<Sigma> = snd \<Sigma>' \<and> snd \<Sigma> = snd \<Sigma>' \<and>
        \<Gamma>\<^sub>s\<turnstile>\<^sub>c (c\<^sub>s,toSeq \<Sigma>) \<rightarrow>\<^sub>\<tau>\<^sup>* (Stuck, toSeq \<Sigma>') \<and> (\<sigma>,\<Sigma>')\<in>\<alpha>"
  by (erule sim_elim_cases, auto)


definition "RGSim_pre"::  
  "[('g\<times>'l,'p,'f,'e) body,('g \<times> 'l,'p,'f,'e)com, 
    (('g,'l) c_state) rel1, (('g,'l) c_state) rel1,
     (('g,'l) c_state,('g1,'l1) c_state) rel, (('g,'l) c_state,('g1,'l1) c_state) rel,
      (('g,'l) c_state,('g1,'l1) c_state) rel,  (('g,'l) c_state,('g1,'l1) c_state) rel,
    ('g1\<times>'l1,'p,'f,'e) body,('g1 \<times> 'l1,'p,'f,'e) com, 
     (('g1,'l1) c_state) rel1, (('g1,'l1) c_state) rel1] \<Rightarrow> bool " 
  ("'(_,_,_,_')/ \<succeq>\<^sub>'(\<^sub>_\<^sub>;\<^sub>_\<^sub>\<rhd>\<^sub>_\<^sub>;\<^sub>_\<^sub>')/ '(_,_,_,_')" [81,81,81,81,81,81,81,81,81,81,81,81] 100)
  where
" (\<Gamma>\<^sub>c,c,R\<^sub>c,G\<^sub>c) \<succeq>\<^sub>(\<^sub>\<alpha>\<^sub>;\<^sub>\<xi>\<^sub>\<rhd>\<^sub>\<gamma>\<^sub>n\<^sub>;\<^sub>\<gamma>\<^sub>a\<^sub>) (\<Gamma>\<^sub>s,c',R\<^sub>s,G\<^sub>s) \<equiv> 
  \<forall>\<sigma> \<Sigma>. (\<sigma>,\<Sigma>)\<in>\<xi> \<longrightarrow> (\<Gamma>\<^sub>c,(c, \<sigma>),R\<^sub>c,G\<^sub>c) \<succeq>\<^sub>(\<^sub>\<alpha>\<^sub>;\<^sub>\<gamma>\<^sub>n\<^sub>;\<^sub>\<gamma>\<^sub>a\<^sub>) (\<Gamma>\<^sub>s,(c', \<Sigma>),R\<^sub>s,G\<^sub>s)
"
    
 definition ToInv :: "('s,'s1)  rel \<Rightarrow> ('s1,'s)rel"
  ("\<Down>\<^sub>i_" [81] 100)
  where "ToInv r \<equiv> {(s2,s1). (s1, s2) \<in> r}"




inductive_set cptn\<^sub>e :: "(('g,'l,'p,'f,'e) confs) set"
where
  CptnOne: " (\<Gamma>, [(P,s)]) \<in> cptn\<^sub>e"
| CptnEnv: "\<lbrakk>\<Gamma>\<turnstile>\<^sub>c(P,s) \<rightarrow>\<^sub>e (P,t); (\<Gamma>,(P, t)#xs) \<in> cptn\<^sub>e \<rbrakk> \<Longrightarrow>
             (\<Gamma>,(P,s)#(P,t)#xs) \<in> cptn\<^sub>e"
| CptnComp: "\<lbrakk>\<Gamma>\<turnstile>\<^sub>c\<^sub>e(P,toSeq s) \<rightarrow> (Q,toSeq t); snd s = snd t; (\<Gamma>,(Q, t)#xs) \<in> cptn\<^sub>e \<rbrakk> \<Longrightarrow> 
              (\<Gamma>,(P,s)#(Q,t)#xs) \<in> cptn\<^sub>e"         
  
    
definition cp\<^sub>e :: "('g\<times>'l,'p,'f,'e) body \<Rightarrow> ('g\<times>'l,'p,'f,'e) com \<Rightarrow> 
                  ('g,'l) c_state \<Rightarrow> (('g, 'l,'p,'f,'e) confs) set" where
  "cp\<^sub>e \<Gamma> P s \<equiv> {(\<Gamma>1,l). l!0=(P,s) \<and> (\<Gamma>,l) \<in> cptn\<^sub>e \<and> \<Gamma>1=\<Gamma>}"     
  

        
definition comm\<^sub>e :: 
  "(('g,'l) c_state) rel1 \<times> 
   (('g,'l) c_state set \<times> ('g,'l) c_state set) \<Rightarrow>
   'f set \<Rightarrow> 
     (('g,'l,'p,'f,'e) confs) set" where
  "comm\<^sub>e \<equiv> \<lambda>(guar, (q,a)) F. 
            {c. (\<forall>i e. Suc i<length (snd c) \<longrightarrow> 
                 (fst c)\<turnstile>\<^sub>c\<^sub>e(fst ((snd c)!i),toSeq (snd ((snd c)!i)))  \<rightarrow> 
                           (fst ((snd c)!Suc i),toSeq (snd ((snd c)!Suc i))) \<longrightarrow> 
                   ((snd ((snd c)!i)), (snd ((snd c)!Suc i))) \<in> guar) \<and> 
                 (final_glob (last (snd c))  \<longrightarrow> fst (last (snd c)) \<notin> Fault ` F  \<longrightarrow>               
                    ((fst (last (snd c)) = Skip \<and> snd (last (snd c)) \<in> q)) \<or>
                    (fst (last (snd c)) = Throw \<and> snd (last (snd c)) \<in>  a))}"

definition com_validity :: 
  "('g\<times>'l,'p,'f,'e) body \<Rightarrow>  'f set \<Rightarrow> ('g\<times>'l,'p,'f,'e) com \<Rightarrow> 
    (('g,'l) c_state) set \<Rightarrow> (('g,'l) c_state) rel1 \<Rightarrow>  (('g,'l) c_state) rel1  \<Rightarrow>  
    (('g,'l) c_state) set \<Rightarrow>  (('g,'l) c_state) set \<Rightarrow>  bool" 
    ("_ \<Turnstile>\<^sub>e\<^bsub>'/_\<^esub>/ _ sat [_,_, _, _,_]" [61,60,0,0,0,0,0,0] 45) where
  "\<Gamma> \<Turnstile>\<^sub>e\<^bsub>/F\<^esub> Pr sat [p, R, G, q,a] \<equiv> 
   \<forall>s. cp\<^sub>e \<Gamma> Pr s \<inter> assum(p, R) \<subseteq> comm\<^sub>e(G, (q,a)) F"
  

lemma RG_sim_cp\<^sub>e:      
 shows "\<exists>l. (\<Gamma>\<^sub>s,l) \<in> (cp\<^sub>e \<Gamma>\<^sub>s c\<^sub>s s') \<and> (\<forall>i. Suc i<length l \<longrightarrow>
           \<Gamma>\<^sub>s\<turnstile>\<^sub>c(l!i)  \<rightarrow>\<^sub>e (l!(Suc i)) \<longrightarrow>
           (snd(l!i), snd(l!(Suc i))) \<in>  R\<^sub>s)"
proof - 
  let ?l1 = "[(c\<^sub>s,s')]"
  have "(\<Gamma>\<^sub>s,[(c\<^sub>s,s')])\<in> (cp\<^sub>e \<Gamma>\<^sub>s c\<^sub>s s')" unfolding cp\<^sub>e_def by (simp add: cptn\<^sub>e.CptnOne)
  also have "(\<forall>i. Suc i<length ?l1 \<longrightarrow>
           \<Gamma>\<^sub>s\<turnstile>\<^sub>c(?l1!i)  \<rightarrow>\<^sub>e (?l1!(Suc i)) \<longrightarrow>
           (snd(?l1!i), snd(?l1!(Suc i))) \<in>  R\<^sub>s)" by auto
  ultimately show ?thesis by auto
qed
    
lemma RG_sim_fst_env_assum1: 
  assumes    
   a0:"s\<^sub>s \<in> p\<^sub>s"
 shows "\<exists>l. (\<Gamma>\<^sub>s,l)\<in>cp\<^sub>e \<Gamma>\<^sub>s c\<^sub>s s\<^sub>s \<and> (\<Gamma>\<^sub>s,l) \<in> assum(p\<^sub>s,R\<^sub>s)"
  proof-
  obtain l1 where 
  l1:"(\<Gamma>\<^sub>s,l1)\<in>(cp\<^sub>e \<Gamma>\<^sub>s c\<^sub>s s\<^sub>s)" and
  l2:"(\<forall>i. Suc i<length l1 \<longrightarrow>
        \<Gamma>\<^sub>s\<turnstile>\<^sub>c(l1!i)  \<rightarrow>\<^sub>e (l1!(Suc i)) \<longrightarrow>
     (snd(l1!i), snd(l1!(Suc i))) \<in>  R\<^sub>s)" 
    using RG_sim_cp\<^sub>e[of \<Gamma>\<^sub>s c\<^sub>s s\<^sub>s] by auto
  then have snd_normal: "snd (l1!0) \<in> p\<^sub>s" using l1 a0 unfolding cp\<^sub>e_def by auto  
  then show ?thesis using l1 l2 unfolding assum_def by fastforce
qed  


lemma step_guarantee:  
  assumes a0:"\<Gamma>\<^sub>c\<turnstile>\<^sub>c\<^sub>e (c\<^sub>c,toSeq \<sigma>)  \<rightarrow> (c\<^sub>c',toSeq \<sigma>') \<and> snd \<sigma> = snd \<sigma>'" and
  a1: " \<forall>c\<^sub>c' \<sigma>'. \<Gamma>\<^sub>c\<turnstile>\<^sub>c\<^sub>\<tau> (c\<^sub>c,toSeq \<sigma>) \<rightarrow> (c\<^sub>c', toSeq \<sigma>') \<and> snd \<sigma> = snd \<sigma>' \<longrightarrow> 
             (\<exists>c\<^sub>s' \<Sigma>'.  \<Gamma>\<^sub>s\<turnstile>\<^sub>c (c\<^sub>s, toSeq \<Sigma>) \<rightarrow>\<^sub>\<tau>\<^sup>* (c\<^sub>s', toSeq \<Sigma>') \<and> snd \<Sigma> = snd \<Sigma>' \<and>
              (\<sigma>', \<Sigma>')\<in>\<alpha> \<and> 
              (((\<sigma>,\<sigma>'),(\<Sigma>,  \<Sigma>')) \<in> (G\<^sub>c,G\<^sub>s\<^sup>*)\<^sub>\<alpha>) \<and>
             (\<Gamma>\<^sub>c,(c\<^sub>c', \<sigma>'),R\<^sub>c,G\<^sub>c) \<succeq>\<^sub>(\<^sub>\<alpha>\<^sub>;\<^sub>\<gamma>\<^sub>q\<^sub>;\<^sub>\<gamma>\<^sub>a\<^sub>) (\<Gamma>\<^sub>s,(c\<^sub>s', \<Sigma>'),R\<^sub>s,G\<^sub>s))" and
  a2:" \<forall>v c\<^sub>c' \<sigma>'. \<Gamma>\<^sub>c\<turnstile>\<^sub>c\<^sub>(Some v) (c\<^sub>c, toSeq \<sigma>) \<rightarrow> (c\<^sub>c', toSeq \<sigma>') \<and> snd \<sigma> = snd \<sigma>' \<longrightarrow> 
             (\<exists> c\<^sub>s' \<Sigma>'. \<Gamma>\<^sub>s\<turnstile>\<^sub>c\<^sub>v (c\<^sub>s, toSeq \<Sigma>) \<rightarrow>\<^sup>+  (c\<^sub>s', toSeq \<Sigma>') \<and> snd \<Sigma> = snd \<Sigma>' \<and>
              (\<sigma>', \<Sigma>')\<in>\<alpha> \<and> (((\<sigma>, \<sigma>'),(\<Sigma>, \<Sigma>')) \<in> (G\<^sub>c,G\<^sub>s\<^sup>*)\<^sub>\<alpha>) \<and>  
                (\<Gamma>\<^sub>c,(c\<^sub>c', \<sigma>'),R\<^sub>c,G\<^sub>c) \<succeq>\<^sub>(\<^sub>\<alpha>\<^sub>;\<^sub>\<gamma>\<^sub>q\<^sub>;\<^sub>\<gamma>\<^sub>a\<^sub>) (\<Gamma>\<^sub>s,(c\<^sub>s',\<Sigma>'),R\<^sub>s,G\<^sub>s))"
shows "\<exists>\<Sigma>' c\<^sub>s'. (\<Gamma>\<^sub>s\<turnstile>\<^sub>c (c\<^sub>s, toSeq \<Sigma>) \<rightarrow>\<^sub>\<tau>\<^sup>* (c\<^sub>s', toSeq \<Sigma>')  \<or> 
                   (\<exists>v. e= Some v \<and> \<Gamma>\<^sub>s\<turnstile>\<^sub>c\<^sub>v (c\<^sub>s, toSeq \<Sigma>) \<rightarrow>\<^sup>+ (c\<^sub>s',toSeq \<Sigma>'))) \<and>  snd \<Sigma> = snd \<Sigma>' \<and> 
                  (\<sigma>',\<Sigma>')\<in>\<alpha> \<and> (\<sigma>,\<sigma>')\<in>G\<^sub>c"
proof -  
  have "\<Gamma>\<^sub>c\<turnstile>\<^sub>c\<^sub>\<tau> (c\<^sub>c,toSeq \<sigma>)  \<rightarrow> (c\<^sub>c',toSeq \<sigma>') \<or>  
        (\<exists>v. e = Some v \<and> \<Gamma>\<^sub>c\<turnstile>\<^sub>c\<^sub>e (c\<^sub>c,toSeq \<sigma>)  \<rightarrow> (c\<^sub>c',toSeq  \<sigma>'))" 
    using a0 by auto
  thus ?thesis
  proof
     assume "\<Gamma>\<^sub>c\<turnstile>\<^sub>c\<^sub>\<tau> (c\<^sub>c,toSeq \<sigma>)  \<rightarrow> (c\<^sub>c',toSeq  \<sigma>')"
     thus ?thesis using a1 a0 unfolding related_transitions_def by blast    
   next
     assume "(\<exists>v. e = Some v \<and> \<Gamma>\<^sub>c\<turnstile>\<^sub>c\<^sub>e (c\<^sub>c,toSeq \<sigma>)  \<rightarrow> (c\<^sub>c',toSeq \<sigma>'))"
     then obtain v where a0: "e=Some v \<and> \<Gamma>\<^sub>c\<turnstile>\<^sub>c\<^sub>(Some v) (c\<^sub>c,toSeq \<sigma>)  \<rightarrow> (c\<^sub>c',toSeq  \<sigma>') \<and> 
                              snd \<sigma> = snd \<sigma>'" using a0 by auto
     then have"(\<exists> c\<^sub>s' \<Sigma>'. \<Gamma>\<^sub>s\<turnstile>\<^sub>c\<^sub>v (c\<^sub>s, toSeq \<Sigma>) \<rightarrow>\<^sup>+  (c\<^sub>s', toSeq  \<Sigma>') \<and> 
              (\<sigma>', \<Sigma>')\<in>\<alpha> \<and> (((\<sigma>,  \<sigma>'),(\<Sigma>, \<Sigma>')) \<in> (G\<^sub>c,G\<^sub>s\<^sup>*)\<^sub>\<alpha>) \<and>   snd \<Sigma> = snd \<Sigma>' \<and>
                (\<Gamma>\<^sub>c,(c\<^sub>c', \<sigma>'),R\<^sub>c,G\<^sub>c) \<succeq>\<^sub>(\<^sub>\<alpha>\<^sub>;\<^sub>\<gamma>\<^sub>q\<^sub>;\<^sub>\<gamma>\<^sub>a\<^sub>) (\<Gamma>\<^sub>s,(c\<^sub>s', \<Sigma>'),R\<^sub>s,G\<^sub>s))"
       using a2 by fast 
     thus ?thesis using a0 unfolding related_transitions_def by blast
  qed    
qed
  

  
lemma step_sim:
  assumes a0:"\<Gamma>\<^sub>c\<turnstile>\<^sub>c\<^sub>e (c\<^sub>c,toSeq \<sigma>)  \<rightarrow> (c\<^sub>c',toSeq \<sigma>') \<and> snd \<sigma> = snd \<sigma>'" and
  a1: " \<forall>c\<^sub>c' \<sigma>'. \<Gamma>\<^sub>c\<turnstile>\<^sub>c\<^sub>\<tau> (c\<^sub>c,toSeq \<sigma>) \<rightarrow> (c\<^sub>c', toSeq \<sigma>') \<and> snd \<sigma> = snd \<sigma>' \<longrightarrow> 
             (\<exists>c\<^sub>s' \<Sigma>'.  \<Gamma>\<^sub>s\<turnstile>\<^sub>c (c\<^sub>s, toSeq \<Sigma>) \<rightarrow>\<^sub>\<tau>\<^sup>* (c\<^sub>s', toSeq \<Sigma>') \<and> snd \<Sigma> = snd \<Sigma>' \<and> 
              (\<sigma>', \<Sigma>')\<in>\<alpha> \<and> 
              (((\<sigma>, \<sigma>'),(\<Sigma>, \<Sigma>')) \<in> (G\<^sub>c,G\<^sub>s\<^sup>*)\<^sub>\<alpha>) \<and>
             (\<Gamma>\<^sub>c,(c\<^sub>c', \<sigma>'),R\<^sub>c,G\<^sub>c) \<succeq>\<^sub>(\<^sub>\<alpha>\<^sub>;\<^sub>\<gamma>\<^sub>q\<^sub>;\<^sub>\<gamma>\<^sub>a\<^sub>) (\<Gamma>\<^sub>s,(c\<^sub>s', \<Sigma>'),R\<^sub>s,G\<^sub>s))" and
  a2:" \<forall>v c\<^sub>c' \<sigma>'. \<Gamma>\<^sub>c\<turnstile>\<^sub>c\<^sub>(Some v) (c\<^sub>c, toSeq \<sigma>) \<rightarrow> (c\<^sub>c', toSeq \<sigma>')  \<and> snd \<sigma> = snd \<sigma>' \<longrightarrow> 
             (\<exists> c\<^sub>s' \<Sigma>'. \<Gamma>\<^sub>s\<turnstile>\<^sub>c\<^sub>v (c\<^sub>s, toSeq \<Sigma>) \<rightarrow>\<^sup>+  (c\<^sub>s', toSeq \<Sigma>') \<and> snd \<Sigma> = snd \<Sigma>' \<and>
              (\<sigma>', \<Sigma>')\<in>\<alpha> \<and> (((\<sigma>, \<sigma>'),(\<Sigma>,  \<Sigma>')) \<in> (G\<^sub>c,G\<^sub>s\<^sup>*)\<^sub>\<alpha>) \<and>  
                (\<Gamma>\<^sub>c,(c\<^sub>c', \<sigma>'),R\<^sub>c,G\<^sub>c) \<succeq>\<^sub>(\<^sub>\<alpha>\<^sub>;\<^sub>\<gamma>\<^sub>q\<^sub>;\<^sub>\<gamma>\<^sub>a\<^sub>) (\<Gamma>\<^sub>s,(c\<^sub>s',\<Sigma>'),R\<^sub>s,G\<^sub>s))"
  shows "\<exists>c\<^sub>s' \<Sigma>'. (\<Gamma>\<^sub>c,(c\<^sub>c', \<sigma>'),R\<^sub>c,G\<^sub>c) \<succeq>\<^sub>(\<^sub>\<alpha>\<^sub>;\<^sub>\<gamma>\<^sub>q\<^sub>;\<^sub>\<gamma>\<^sub>a\<^sub>) (\<Gamma>\<^sub>s,(c\<^sub>s', \<Sigma>'),R\<^sub>s,G\<^sub>s) "
proof -  
  have "\<Gamma>\<^sub>c\<turnstile>\<^sub>c\<^sub>\<tau> (c\<^sub>c,toSeq \<sigma>)  \<rightarrow> (c\<^sub>c',toSeq \<sigma>') \<or>  
       (\<exists>v. e = Some v \<and> \<Gamma>\<^sub>c\<turnstile>\<^sub>c\<^sub>e (c\<^sub>c,toSeq \<sigma>)  \<rightarrow> (c\<^sub>c',toSeq \<sigma>'))" 
    using a0 by auto
  thus ?thesis
  proof
    assume "\<Gamma>\<^sub>c\<turnstile>\<^sub>c\<^sub>\<tau> (c\<^sub>c,toSeq \<sigma>)  \<rightarrow> (c\<^sub>c',toSeq \<sigma>')"    
    then show ?thesis using a1 a0  by fast   
   next
     assume "(\<exists>v. e = Some v \<and> \<Gamma>\<^sub>c\<turnstile>\<^sub>c\<^sub>e (c\<^sub>c,toSeq \<sigma>)  \<rightarrow> (c\<^sub>c',toSeq \<sigma>'))"     
     thus ?thesis using a2 a0 by fast
  qed    
qed

        
lemma sim_next_state:
  "(\<Gamma>\<^sub>c,(c\<^sub>c, \<sigma>),R\<^sub>c,G\<^sub>c) \<succeq>\<^sub>(\<^sub>\<alpha>\<^sub>;\<^sub>\<gamma>\<^sub>q\<^sub>;\<^sub>\<gamma>\<^sub>a\<^sub>) (\<Gamma>\<^sub>s,(c\<^sub>s, \<Sigma>),R\<^sub>s,G\<^sub>s) \<Longrightarrow>
   \<Gamma>\<^sub>c\<turnstile>\<^sub>c\<^sub>e (c\<^sub>c,toSeq \<sigma>)  \<rightarrow> (c\<^sub>c',toSeq  \<sigma>') \<and> snd \<sigma> = snd \<sigma>' \<Longrightarrow>
  \<exists>\<Sigma>' c\<^sub>s' .  \<Gamma>\<^sub>s\<turnstile>\<^sub>c (c\<^sub>s, toSeq \<Sigma>) \<rightarrow>\<^sub>\<tau>\<^sup>* (c\<^sub>s', toSeq \<Sigma>') \<or> 
     (\<exists>v. e= Some v \<and> \<Gamma>\<^sub>s\<turnstile>\<^sub>c\<^sub>v (c\<^sub>s, toSeq \<Sigma>) \<rightarrow>\<^sup>+  (c\<^sub>s', toSeq  \<Sigma>')) \<and> snd \<Sigma> = snd \<Sigma>' \<and>
     (\<sigma>',\<Sigma>')\<in>\<alpha> \<and> ((\<sigma>, \<sigma>')\<in>G\<^sub>c)"
  apply (erule sim_elim_cases,  drule step_guarantee)
  apply fastforce apply auto[1]
  by blast
    
  
  lemma sim_guarantee_normal:
"(\<Gamma>\<^sub>c,(c\<^sub>c,\<sigma>),R\<^sub>c,G\<^sub>c) \<succeq>\<^sub>(\<^sub>\<alpha>\<^sub>;\<^sub>\<gamma>\<^sub>q\<^sub>;\<^sub>\<gamma>\<^sub>a\<^sub>) (\<Gamma>\<^sub>s,(c\<^sub>s,\<Sigma>),R\<^sub>s,G\<^sub>s) \<Longrightarrow>
 \<Gamma>\<^sub>c\<turnstile>\<^sub>c\<^sub>e (c\<^sub>c,toSeq \<sigma>)  \<rightarrow> (c\<^sub>c',toSeq \<sigma>') \<and> snd \<sigma> = snd \<sigma>' \<Longrightarrow>
\<exists>c\<^sub>s' \<Sigma>'. (\<Gamma>\<^sub>c,(c\<^sub>c', \<sigma>'),R\<^sub>c,G\<^sub>c) \<succeq>\<^sub>(\<^sub>\<alpha>\<^sub>;\<^sub>\<gamma>\<^sub>q\<^sub>;\<^sub>\<gamma>\<^sub>a\<^sub>) (\<Gamma>\<^sub>s,(c\<^sub>s',\<Sigma>'),R\<^sub>s,G\<^sub>s)"
    apply (erule sim_elim_cases, drule step_sim)   
      apply fastforce         
    apply auto[1] by blast


thm steppev_induct[simplified split_beta]

lemma dest_par_step:
   "\<Gamma>\<turnstile>\<^sub>p\<^sub>e (c\<^sub>c,\<sigma>) \<rightarrow> (c\<^sub>c', \<sigma>') \<Longrightarrow> 
      \<exists>i s' r.  i<length c\<^sub>c \<and>  \<Gamma>\<turnstile>\<^sub>c\<^sub>e(c\<^sub>c!i,toSeqPar i \<sigma>) \<rightarrow> (r,s') \<and> c\<^sub>c' = c\<^sub>c[i:=r] \<and> \<sigma>' = toPar i s' \<sigma>" 
  by (fastforce elim: step_pev_elim_cases)

lemma dest_par_step_toSeqState: 
  assumes a0:"\<Gamma>\<turnstile>\<^sub>p\<^sub>e (c\<^sub>c,\<sigma>) \<rightarrow> (c\<^sub>c', \<sigma>')" and a1:"length c\<^sub>c =  length (snd \<sigma>)"
  shows"\<exists>i. \<Gamma>\<turnstile>\<^sub>c\<^sub>e (c\<^sub>c!i, fst (toSeqState i \<sigma>) ) \<rightarrow> (c\<^sub>c'!i, fst (toSeqState i \<sigma>') ) \<and> 
           snd (toSeqState i \<sigma>) = snd (toSeqState i \<sigma>')"
proof-
  obtain i s' r where "i<length c\<^sub>c \<and>  \<Gamma>\<turnstile>\<^sub>c\<^sub>e(c\<^sub>c!i,toSeqPar i \<sigma>) \<rightarrow> (r,s') \<and> c\<^sub>c' = c\<^sub>c[i:=r] \<and> \<sigma>' = toPar i s' \<sigma>"
    using dest_par_step[OF a0] by auto
  moreover have "\<Gamma>\<turnstile>\<^sub>c\<^sub>e (c\<^sub>c!i, fst (toSeqState i \<sigma>) ) \<rightarrow> (c\<^sub>c'!i, fst (toSeqState i \<sigma>') )" 
    using a1 calculation unfolding toSeqState_def
    by (simp add: prod.case_eq_if)
  ultimately show ?thesis unfolding toSeqState_def Let_def split_beta  
    using nth_list_update by fastforce
qed

definition finalp:: "('s,'p,'f,'e)com \<Rightarrow>  bool" where
"finalp c  \<equiv> c = Skip \<or> c = Throw \<or> (\<exists>f. c= Fault f) \<or> c = Stuck"

definition final_error:: "('s,'p,'f,'e)com list \<Rightarrow> bool" where
"final_error P \<equiv> (\<forall>i<length P. finalp (P!i)) \<and> (\<exists>j<length P. P!j = Stuck \<or> (\<exists>f. P!j = Fault f))"

definition final_error_r:: "('s,'p,'f,'e)com list \<Rightarrow> ('S,'p,'f,'e)com list \<Rightarrow> bool" where
"final_error_r P P' \<equiv> final_error P \<and> final_error P' \<and> 
                      (\<forall>i<length P. \<forall>f. P!i = Fault f \<longrightarrow> (\<exists>j<length P'. P'!j = Fault f)) \<and> 
                      (\<forall>i<length P. P!i=Stuck \<longrightarrow> (\<exists>j<length P'. P'!j =Stuck)) \<and>
                      (\<forall>i<length P'. \<forall>f. P'!i = Fault f \<longrightarrow> (\<exists>j<length P. P!j = Fault f)) \<and> 
                      (\<forall>i<length P'. P'!i=Stuck \<longrightarrow> (\<exists>j<length P. P!j =Stuck))"

lemma final_error_r_sim_spec:
  "final_error P \<Longrightarrow> final_error_r P P' \<Longrightarrow> final_error P'"
  unfolding final_error_def final_error_r_def finalp_def 
  by auto

lemma throw_program_final_c:"throw_program P \<Longrightarrow> final_c (P,s)"
  unfolding throw_program_def final_c_def final1_def by fastforce

lemma skip_program_final_c:"skip_program P \<Longrightarrow> final_c (P,s)"
  unfolding skip_program_def final_c_def final1_def by fastforce

lemma error_program_final_c:"final_error P \<Longrightarrow> final_c (P,s)"
  unfolding final_error_def finalp_def final_c_def final1_def by fastforce

lemma error_program_P_not_empty:"final_error P \<Longrightarrow> 0 < length P"
  unfolding final_error_def finalp_def by auto
 
coinductive "RGSIM"::"[('g\<times>'l,'p,'f,'e) body,('g,'l, 'p,'f,'e) par_config, 
                      (('g,'l)par_state)  rel1, (('g,'l)par_state)  rel1,
                      (('g,'l)par_state,('g1,'l1)par_state) rel, 
                      (('g,'l)par_state,('g1,'l1)par_state) rel,
                       (('g,'l)par_state,('g1,'l1)par_state) rel,
                     ('g1\<times>'l1,'p,'f,'e) body,('g1,'l1, 'p,'f,'e) par_config, 
                      (('g1,'l1)par_state)  rel1, (('g1,'l1)par_state)  rel1
                    ] \<Rightarrow> bool " 
("'(_,_,_,_')/ \<succeq>\<^sub>p\<^sub>'(\<^sub>_\<^sub>;\<^sub>_\<^sub>;\<^sub>_\<^sub>')/ '(_,_,_,_')" [81,81,81,81,81,81,81,81,81,81,81] 100)
where
  RGSIM: "\<lbrakk>(\<sigma>,\<Sigma>)\<in>\<alpha>;
           \<forall>c\<^sub>c' \<sigma>'. (\<Gamma>\<^sub>c\<turnstile>\<^sub>p\<^sub>\<tau> (c\<^sub>c,\<sigma>) \<rightarrow> (c\<^sub>c',  \<sigma>')) \<longrightarrow> 
             (\<exists>c\<^sub>s' \<Sigma>'.  \<Gamma>\<^sub>s\<turnstile>\<^sub>p (c\<^sub>s, \<Sigma>) \<rightarrow>\<^sub>\<tau>\<^sup>* (c\<^sub>s',  \<Sigma>') \<and> (\<sigma>', \<Sigma>')\<in>\<alpha> \<and> 
              (((\<sigma>, \<sigma>'),(\<Sigma>,  \<Sigma>')) \<in> (G\<^sub>c,G\<^sub>s\<^sup>*)\<^sub>\<alpha>) \<and> (\<Gamma>\<^sub>c,(c\<^sub>c', \<sigma>'),R\<^sub>c,G\<^sub>c) \<succeq>\<^sub>p\<^sub>(\<^sub>\<alpha>\<^sub>;\<^sub>\<gamma>\<^sub>q\<^sub>;\<^sub>\<gamma>\<^sub>a\<^sub>) (\<Gamma>\<^sub>s,(c\<^sub>s', \<Sigma>'),R\<^sub>s,G\<^sub>s));           
           \<forall>v c\<^sub>c' \<sigma>' e. e=Some v \<and> (\<Gamma>\<^sub>c\<turnstile>\<^sub>p\<^sub>e (c\<^sub>c, \<sigma>) \<rightarrow> (c\<^sub>c',  \<sigma>')) \<longrightarrow> 
             (\<exists> c\<^sub>s' \<Sigma>'. \<Gamma>\<^sub>s\<turnstile>\<^sub>p\<^sub>v (c\<^sub>s, \<Sigma>) \<rightarrow>\<^sup>+  (c\<^sub>s',  \<Sigma>') \<and> 
             (\<sigma>', \<Sigma>')\<in>\<alpha> \<and> (((\<sigma>, \<sigma>'),(\<Sigma>,  \<Sigma>')) \<in> (G\<^sub>c,G\<^sub>s\<^sup>*)\<^sub>\<alpha>) \<and>  
             (\<Gamma>\<^sub>c,(c\<^sub>c', \<sigma>'),R\<^sub>c,G\<^sub>c) \<succeq>\<^sub>p\<^sub>(\<^sub>\<alpha>\<^sub>;\<^sub>\<gamma>\<^sub>q\<^sub>;\<^sub>\<gamma>\<^sub>a\<^sub>) (\<Gamma>\<^sub>s,(c\<^sub>s', \<Sigma>'),R\<^sub>s,G\<^sub>s));                      
           \<forall>\<sigma>' \<Sigma>'. (((\<sigma>,\<sigma>'),(\<Sigma>,\<Sigma>')) \<in> (R\<^sub>c,R\<^sub>s\<^sup>*)\<^sub>\<alpha>) \<longrightarrow> 
              (\<Gamma>\<^sub>c,(c\<^sub>c,\<sigma>'),R\<^sub>c,G\<^sub>c) \<succeq>\<^sub>p\<^sub>(\<^sub>\<alpha>\<^sub>;\<^sub>\<gamma>\<^sub>q\<^sub>;\<^sub>\<gamma>\<^sub>a\<^sub>) (\<Gamma>\<^sub>s,(c\<^sub>s,\<Sigma>'),R\<^sub>s,G\<^sub>s);           
           (\<forall>i<length c\<^sub>c. c\<^sub>c!i = Skip) \<and> 0 < length c\<^sub>c \<longrightarrow> 
              (\<exists>\<Sigma>' c\<^sub>s'. (((\<sigma>, \<sigma>),(\<Sigma>,  \<Sigma>')) \<in> (G\<^sub>c,G\<^sub>s\<^sup>*)\<^sub>\<alpha>) \<and> 
              (\<sigma>, \<Sigma>')\<in>\<gamma>\<^sub>q \<and> \<gamma>\<^sub>q\<subseteq>\<alpha> \<and> \<Gamma>\<^sub>s\<turnstile>\<^sub>p (c\<^sub>s,\<Sigma>) \<rightarrow>\<^sub>\<tau>\<^sup>* (c\<^sub>s',  \<Sigma>') \<and> 
              (\<forall>i<length c\<^sub>s'. c\<^sub>s'!i = Skip) \<and> 0 < length c\<^sub>s');                   
           throw_program c\<^sub>c \<longrightarrow> 
              (\<exists>\<Sigma>' c\<^sub>s'. (((\<sigma>, \<sigma>),(\<Sigma>,  \<Sigma>')) \<in> (G\<^sub>c,G\<^sub>s\<^sup>*)\<^sub>\<alpha>) \<and>
              (\<sigma>, \<Sigma>')\<in>\<gamma>\<^sub>a \<and> \<gamma>\<^sub>a\<subseteq>\<alpha> \<and> \<Gamma>\<^sub>s\<turnstile>\<^sub>p (c\<^sub>s,\<Sigma>) \<rightarrow>\<^sub>\<tau>\<^sup>* (c\<^sub>s',  \<Sigma>') \<and> 
              throw_program c\<^sub>s');                                           
           final_error c\<^sub>c  \<longrightarrow> 
              (\<exists>\<Sigma>' c\<^sub>s'. (((\<sigma>, \<sigma>),(\<Sigma>,  \<Sigma>')) \<in> (G\<^sub>c,G\<^sub>s\<^sup>*)\<^sub>\<alpha>) \<and> \<Gamma>\<^sub>s\<turnstile>\<^sub>p (c\<^sub>s,\<Sigma>) \<rightarrow>\<^sub>\<tau>\<^sup>* (c\<^sub>s', \<Sigma>') \<and> 
                       final_error_r c\<^sub>c c\<^sub>s')       
          \<rbrakk> \<Longrightarrow> (\<Gamma>\<^sub>c,(c\<^sub>c,\<sigma>),R\<^sub>c,G\<^sub>c) \<succeq>\<^sub>p\<^sub>(\<^sub>\<alpha>\<^sub>;\<^sub>\<gamma>\<^sub>q\<^sub>;\<^sub>\<gamma>\<^sub>a\<^sub>) (\<Gamma>\<^sub>s,(c\<^sub>s,\<Sigma>),R\<^sub>s,G\<^sub>s)"

inductive_cases par_sim_elim_cases:
  "(\<Gamma>\<^sub>c,(c,s),R\<^sub>c,G\<^sub>c) \<succeq>\<^sub>p\<^sub>(\<^sub>\<alpha>\<^sub>;\<^sub>\<gamma>\<^sub>q\<^sub>;\<^sub>\<gamma>\<^sub>a\<^sub>) (\<Gamma>\<^sub>s,(c',s'),R\<^sub>s,G\<^sub>s)" 
 
lemma dest_SIM_alpha:  
 "(\<Gamma>\<^sub>c,(c\<^sub>c,\<sigma>),R\<^sub>c,G\<^sub>c) \<succeq>\<^sub>p\<^sub>(\<^sub>\<alpha>\<^sub>;\<^sub>\<gamma>\<^sub>q\<^sub>;\<^sub>\<gamma>\<^sub>a\<^sub>) (\<Gamma>\<^sub>s,(c\<^sub>s,\<Sigma>),R\<^sub>s,G\<^sub>s) \<Longrightarrow>
   (\<sigma>,\<Sigma>) \<in> \<alpha>"
  by (erule par_sim_elim_cases,auto)  

lemma dest_SIM_ev_step:
  "(\<Gamma>\<^sub>c,(c\<^sub>c,\<sigma>),R\<^sub>c,G\<^sub>c) \<succeq>\<^sub>p\<^sub>(\<^sub>\<alpha>\<^sub>;\<^sub>\<gamma>\<^sub>q\<^sub>;\<^sub>\<gamma>\<^sub>a\<^sub>) (\<Gamma>\<^sub>s,(c\<^sub>s,\<Sigma>),R\<^sub>s,G\<^sub>s) \<Longrightarrow>
     \<Gamma>\<^sub>c\<turnstile>\<^sub>p\<^sub>(Some v) (c\<^sub>c, \<sigma>) \<rightarrow> (c\<^sub>c', \<sigma>') \<Longrightarrow>
    \<exists> c\<^sub>s' \<Sigma>'. \<Gamma>\<^sub>s\<turnstile>\<^sub>p\<^sub>v (c\<^sub>s, \<Sigma>) \<rightarrow>\<^sup>+  (c\<^sub>s', \<Sigma>') \<and> 
              (\<sigma>', \<Sigma>')\<in>\<alpha> \<and> (((\<sigma>, \<sigma>'),(\<Sigma>, \<Sigma>')) \<in> (G\<^sub>c,G\<^sub>s\<^sup>*)\<^sub>\<alpha>) \<and>  
                (\<Gamma>\<^sub>c,(c\<^sub>c', \<sigma>'),R\<^sub>c,G\<^sub>c) \<succeq>\<^sub>p\<^sub>(\<^sub>\<alpha>\<^sub>;\<^sub>\<gamma>\<^sub>q\<^sub>;\<^sub>\<gamma>\<^sub>a\<^sub>) (\<Gamma>\<^sub>s,(c\<^sub>s', \<Sigma>'),R\<^sub>s,G\<^sub>s)"  
  by (erule par_sim_elim_cases, cases \<sigma>', auto)
    
lemma dest_SIM_tau_step:
  "(\<Gamma>\<^sub>c,(c\<^sub>c,\<sigma>),R\<^sub>c,G\<^sub>c) \<succeq>\<^sub>p\<^sub>(\<^sub>\<alpha>\<^sub>;\<^sub>\<gamma>\<^sub>q\<^sub>;\<^sub>\<gamma>\<^sub>a\<^sub>) (\<Gamma>\<^sub>s,(c\<^sub>s,\<Sigma>),R\<^sub>s,G\<^sub>s) \<Longrightarrow>
    \<Gamma>\<^sub>c\<turnstile>\<^sub>p\<^sub>\<tau> (c\<^sub>c, \<sigma>) \<rightarrow> (c\<^sub>c',  \<sigma>') \<Longrightarrow>
   \<exists>c\<^sub>s' \<Sigma>'.  \<Gamma>\<^sub>s\<turnstile>\<^sub>p (c\<^sub>s, \<Sigma>) \<rightarrow>\<^sub>\<tau>\<^sup>* (c\<^sub>s',  \<Sigma>') \<and>
              (\<sigma>', \<Sigma>')\<in>\<alpha> \<and> 
              (((\<sigma>, \<sigma>'),(\<Sigma>,  \<Sigma>')) \<in> (G\<^sub>c,G\<^sub>s\<^sup>*)\<^sub>\<alpha>) \<and>
             (\<Gamma>\<^sub>c,(c\<^sub>c', \<sigma>'),R\<^sub>c,G\<^sub>c) \<succeq>\<^sub>p\<^sub>(\<^sub>\<alpha>\<^sub>;\<^sub>\<gamma>\<^sub>q\<^sub>;\<^sub>\<gamma>\<^sub>a\<^sub>) (\<Gamma>\<^sub>s,(c\<^sub>s', \<Sigma>'),R\<^sub>s,G\<^sub>s)"
  by (erule par_sim_elim_cases, cases \<sigma>', auto)
        
lemma dest_SIM_env_step:  
  "(\<Gamma>\<^sub>c,(c\<^sub>c,\<sigma>),R\<^sub>c,G\<^sub>c) \<succeq>\<^sub>p\<^sub>(\<^sub>\<alpha>\<^sub>;\<^sub>\<gamma>\<^sub>q\<^sub>;\<^sub>\<gamma>\<^sub>a\<^sub>) (\<Gamma>\<^sub>s,(c\<^sub>s,\<Sigma>),R\<^sub>s,G\<^sub>s) \<Longrightarrow>
   (((\<sigma>,\<sigma>'),(\<Sigma>,\<Sigma>')) \<in> (R\<^sub>c,R\<^sub>s\<^sup>*)\<^sub>\<alpha>)  \<Longrightarrow>
   (\<Gamma>\<^sub>c,(c\<^sub>c,\<sigma>'),R\<^sub>c,G\<^sub>c) \<succeq>\<^sub>p\<^sub>(\<^sub>\<alpha>\<^sub>;\<^sub>\<gamma>\<^sub>q\<^sub>;\<^sub>\<gamma>\<^sub>a\<^sub>) (\<Gamma>\<^sub>s,(c\<^sub>s,\<Sigma>'),R\<^sub>s,G\<^sub>s)"  
  by (erule par_sim_elim_cases, cases \<sigma>', cases \<Sigma>', force)
    
 lemma dest_SIM_skip_term:
  "(\<Gamma>\<^sub>c,(c\<^sub>c,\<sigma>),R\<^sub>c,G\<^sub>c) \<succeq>\<^sub>p\<^sub>(\<^sub>\<alpha>\<^sub>;\<^sub>\<gamma>\<^sub>q\<^sub>;\<^sub>\<gamma>\<^sub>a\<^sub>) (\<Gamma>\<^sub>s,(c\<^sub>s,\<Sigma>),R\<^sub>s,G\<^sub>s) \<Longrightarrow>
   (\<forall>i<length c\<^sub>c. c\<^sub>c!i = Skip) \<and> 0 < length c\<^sub>c \<Longrightarrow>
   \<exists>\<Sigma>' c\<^sub>s'. (((\<sigma>, \<sigma>),(\<Sigma>, \<Sigma>')) \<in> (G\<^sub>c,G\<^sub>s\<^sup>*)\<^sub>\<alpha>) \<and>
            (\<sigma>, \<Sigma>')\<in>\<gamma>\<^sub>q \<and> \<gamma>\<^sub>q\<subseteq>\<alpha> \<and> 
           \<Gamma>\<^sub>s\<turnstile>\<^sub>p (c\<^sub>s,\<Sigma>) \<rightarrow>\<^sub>\<tau>\<^sup>* (c\<^sub>s',  \<Sigma>') \<and> 
            (\<forall>i<length c\<^sub>s'. c\<^sub>s'!i = Skip) \<and> 0 < length c\<^sub>s'"
   by (erule par_sim_elim_cases, auto)
   
    
 lemma dest_SIM_throw_term:
  "(\<Gamma>\<^sub>c,(c\<^sub>c,\<sigma>),R\<^sub>c,G\<^sub>c) \<succeq>\<^sub>p\<^sub>(\<^sub>\<alpha>\<^sub>;\<^sub>\<gamma>\<^sub>q\<^sub>;\<^sub>\<gamma>\<^sub>a\<^sub>) (\<Gamma>\<^sub>s,(c\<^sub>s,\<Sigma>),R\<^sub>s,G\<^sub>s) \<Longrightarrow>
    throw_program c\<^sub>c \<Longrightarrow>
   \<exists>\<Sigma>' c\<^sub>s'. (((\<sigma>, \<sigma>),(\<Sigma>,  \<Sigma>')) \<in> (G\<^sub>c,G\<^sub>s\<^sup>*)\<^sub>\<alpha>) \<and>
                (\<sigma>, \<Sigma>')\<in>\<gamma>\<^sub>a \<and> \<gamma>\<^sub>a\<subseteq>\<alpha> \<and> \<Gamma>\<^sub>s\<turnstile>\<^sub>p (c\<^sub>s,\<Sigma>) \<rightarrow>\<^sub>\<tau>\<^sup>* (c\<^sub>s',  \<Sigma>') \<and> throw_program c\<^sub>s'"
   by (erule par_sim_elim_cases, cases \<sigma>,auto)


 lemma dest_SIM_error:
  "(\<Gamma>\<^sub>c,(c\<^sub>c,\<sigma>),R\<^sub>c,G\<^sub>c) \<succeq>\<^sub>p\<^sub>(\<^sub>\<alpha>\<^sub>;\<^sub>\<gamma>\<^sub>q\<^sub>;\<^sub>\<gamma>\<^sub>a\<^sub>) (\<Gamma>\<^sub>s,(c\<^sub>s,\<Sigma>),R\<^sub>s,G\<^sub>s) \<Longrightarrow>
    final_error c\<^sub>c \<and> 0 < length c\<^sub>c \<Longrightarrow>
   \<exists>\<Sigma>' c\<^sub>s'. \<Gamma>\<^sub>s\<turnstile>\<^sub>p (c\<^sub>s,\<Sigma>) \<rightarrow>\<^sub>\<tau>\<^sup>* (c\<^sub>s', \<Sigma>') \<and> final_error_r c\<^sub>c c\<^sub>s'"
   by (erule par_sim_elim_cases, cases \<sigma>,auto)
  
     
 (* lemma dest_SIM_not_Normal_transition:
  "(\<Gamma>\<^sub>c,(c\<^sub>c,\<sigma>),R\<^sub>c,G\<^sub>c) \<succeq>\<^sub>p\<^sub>(\<^sub>\<alpha>\<^sub>;\<^sub>\<gamma>\<^sub>q\<^sub>;\<^sub>\<gamma>\<^sub>a\<^sub>) (\<Gamma>\<^sub>s,(c\<^sub>s,\<Sigma>),R\<^sub>s,G\<^sub>s) \<Longrightarrow>
   (\<Gamma>\<^sub>c\<turnstile>\<^sub>p\<^sub>e (c\<^sub>c,\<sigma>) \<rightarrow> (c\<^sub>c',\<sigma>')) \<and> (\<forall>\<sigma>n. \<sigma>'\<noteq>Normal \<sigma>n) \<Longrightarrow>
   \<exists>\<Sigma>' c\<^sub>s'. (\<sigma>',\<Sigma>')\<in>\<alpha>\<^sub>x \<and> (\<Gamma>\<^sub>s\<turnstile>\<^sub>p (c\<^sub>s,\<Sigma>) \<rightarrow>\<^sub>\<tau>\<^sup>* (c\<^sub>s', \<Sigma>')  \<or> \<Gamma>\<^sub>s\<turnstile>\<^sub>p\<^sub>v (c', \<Sigma>) \<rightarrow>\<^sup>+ (c\<^sub>s',\<Sigma>') ) \<and>
            (((\<sigma>, \<sigma>'),(\<Sigma>, \<Sigma>')) \<in> (G\<^sub>c,G\<^sub>s\<^sup>*) (*  \<^sub>\<alpha>) \<and>
            (\<Gamma>\<^sub>c,(c\<^sub>c',Normal \<sigma>n'),R\<^sub>c,G\<^sub>c) \<succeq>\<^sub>p\<^sub>(\<^sub>\<alpha>\<^sub>;\<^sub>\<gamma>\<^sub>q\<^sub>;\<^sub>\<gamma>\<^sub>a\<^sub>) (\<Gamma>\<^sub>s,(c\<^sub>s',Normal \<Sigma>n'),R\<^sub>s,G\<^sub>s)"
   by (erule par_sim_elim_cases,auto) *)
    
definition "RGSIM_p_pre"::  
  "[('g\<times>'l,'p,'f,'e) body,('g,'l,'p,'f,'e)par_com,
    (('g,'l)par_state)  rel1, (('g,'l)par_state)  rel1,
     (('g,'l)par_state,('g1,'l1)par_state) rel, 
     (('g,'l)par_state,('g1,'l1)par_state) rel,
     (('g,'l)par_state,('g1,'l1)par_state) rel, 
     (('g,'l)par_state,('g1,'l1)par_state) rel,
    ('g1\<times>'l1,'p,'f,'e) body,('g1,'l1, 'p,'f,'e) par_com, 
    (('g1,'l1)par_state)  rel1, (('g1,'l1)par_state)  rel1] \<Rightarrow> bool " 
  ("'(_,_,_,_')/ \<succeq>\<^sub>p\<^sub>'(\<^sub>_\<^sub>;\<^sub>_\<^sub>\<rhd>\<^sub>_\<^sub>;\<^sub>_\<^sub>')/ '(_,_,_,_')" [81,81,81,81,81,81,81,81,81,81,81,81] 100)
  where
" (\<Gamma>\<^sub>c,c\<^sub>c,R\<^sub>c,G\<^sub>c) \<succeq>\<^sub>p\<^sub>(\<^sub>\<alpha>\<^sub>;\<^sub>\<xi>\<^sub>\<rhd>\<^sub>\<gamma>\<^sub>n\<^sub>;\<^sub>\<gamma>\<^sub>a\<^sub>) (\<Gamma>\<^sub>s,c\<^sub>s,R\<^sub>s,G\<^sub>s) \<equiv> 
  \<forall>\<sigma> \<Sigma>. (\<sigma>,\<Sigma>)\<in>\<xi> \<longrightarrow> (\<Gamma>\<^sub>c,(c\<^sub>c, \<sigma>),R\<^sub>c,G\<^sub>c) \<succeq>\<^sub>p\<^sub>(\<^sub>\<alpha>\<^sub>;\<^sub>\<gamma>\<^sub>n\<^sub>;\<^sub>\<gamma>\<^sub>a\<^sub>) (\<Gamma>\<^sub>s,(c\<^sub>s, \<Sigma>),R\<^sub>s,G\<^sub>s)
"

inductive_set par_cptn\<^sub>e :: "(('g,'l,'p,'f,'e) par_confs) set"
  where    
  ParCptnOne: "(\<Gamma>, [(P,s)]) \<in> par_cptn\<^sub>e"
| ParCptnEnv: "\<lbrakk>\<Gamma>\<turnstile>\<^sub>p(P,s) \<rightarrow>\<^sub>e (P,t);(\<Gamma>,(P, t)#xs) \<in> par_cptn\<^sub>e \<rbrakk> \<Longrightarrow>(\<Gamma>,(P,s)#(P,t)#xs) \<in> par_cptn\<^sub>e"
| ParCptnComp: "\<lbrakk> \<Gamma> \<turnstile>\<^sub>p\<^sub>e(P,s) \<rightarrow> (Q,t); (\<Gamma>,(Q,t)#xs) \<in> par_cptn\<^sub>e \<rbrakk> \<Longrightarrow> (\<Gamma>,(P,s)#(Q,t)#xs) \<in> par_cptn\<^sub>e"
  
lemma par_cptn\<^sub>e_cptn:"(\<Gamma>,xs) \<in> par_cptn\<^sub>e \<Longrightarrow> (\<Gamma>,xs) \<in> par_cptn"
proof(induct rule: par_cptn\<^sub>e.induct)
  case (ParCptnOne \<Gamma> P s)
  then show ?case
    by (blast intro: par_cptn.ParCptnOne) 
next
  case (ParCptnEnv \<Gamma> P s t xs)
  then show ?case
    by (blast intro: par_cptn.ParCptnEnv) 
next
  case (ParCptnComp \<Gamma> e P s Q t xs)
  then show ?case
    using  steppe_stepp by (blast intro:par_cptn.ParCptnComp)
qed 
 
lemma par_cptn_cptn\<^sub>e:"(\<Gamma>,xs) \<in> par_cptn \<Longrightarrow> (\<Gamma>,xs) \<in> par_cptn\<^sub>e"
proof(induct rule: par_cptn.induct)
  case (ParCptnOne \<Gamma> P s)
  then show ?case
    by (blast intro: par_cptn\<^sub>e.ParCptnOne) 
next
  case (ParCptnEnv \<Gamma> P s t xs)
  then show ?case
    by (blast intro: par_cptn\<^sub>e.ParCptnEnv) 
next
  case (ParCptnComp \<Gamma> P s Q t xs)
  then show ?case
    using  stepp_steppe by (blast intro:par_cptn\<^sub>e.ParCptnComp)
qed 
    

lemma par_cptn_eq:"par_cptn\<^sub>e = par_cptn"  
  using par_cptn_cptn\<^sub>e par_cptn\<^sub>e_cptn by fastforce
  
 inductive_cases par_cptn_e_elim_cases [cases set]:
"(\<Gamma>, [(P,s)]) \<in> par_cptn\<^sub>e"
"(\<Gamma>,(P,s)#(Q,t)#xs) \<in> par_cptn\<^sub>e"

lemma par_cptn_step:"(\<Gamma>,(P,s)#(Q,t)#xs) \<in> par_cptn\<^sub>e \<Longrightarrow> \<exists>e. (\<Gamma>\<turnstile>\<^sub>p\<^sub>e (P, s) \<rightarrow> (Q, t)) \<or> \<Gamma>\<turnstile>\<^sub>p (P, s) \<rightarrow>\<^sub>e (Q, t)"
  by (erule par_cptn_e_elim_cases(2), auto)

lemma cptne_append_is_cptne [rule_format]: 
 "\<forall>b a. (\<Gamma>,b#c1)\<in>par_cptn\<^sub>e \<longrightarrow>  (\<Gamma>,a#c2)\<in>par_cptn\<^sub>e \<longrightarrow> (b#c1)!length c1=a \<longrightarrow> (\<Gamma>,b#c1@c2)\<in>par_cptn\<^sub>e"
apply(induct c1)
 apply simp
apply clarify
apply(erule par_cptn\<^sub>e.cases,simp_all)
  apply (meson par_cptn\<^sub>e.ParCptnEnv)
  by (meson par_cptn\<^sub>e.ParCptnComp)  

lemma par_cptn_e_dest:"(\<Gamma>,(P,s)#(Q,t)#xs) \<in> par_cptn\<^sub>e \<Longrightarrow> (\<Gamma>,(Q,t)#xs)\<in> par_cptn\<^sub>e"
by (auto dest: par_cptn_e_elim_cases)

lemma par_cptn_e_dest_pair:"(\<Gamma>,x#x1#xs) \<in> par_cptn\<^sub>e \<Longrightarrow> (\<Gamma>,x1#xs)\<in> par_cptn\<^sub>e"
proof -
  assume "(\<Gamma>,x#x1#xs) \<in> par_cptn\<^sub>e"
  thus ?thesis using par_cptn_e_dest prod.collapse by metis
qed

lemma par_cptn_e_dest1:"(\<Gamma>,(P,s)#(Q,t)#xs) \<in> par_cptn\<^sub>e \<Longrightarrow> (\<Gamma>,(P,s)#[(Q,t)])\<in> par_cptn\<^sub>e"
proof -
  assume a1: "(\<Gamma>, (P, s) # (Q, t) # xs) \<in> par_cptn\<^sub>e"
  have "(\<Gamma>, [(Q, t)]) \<in> par_cptn\<^sub>e"
    by (meson ParCptnOne)
  thus ?thesis
    by (metis a1 par_cptn\<^sub>e.ParCptnComp par_cptn\<^sub>e.ParCptnEnv par_cptn_e_elim_cases(2))       
qed


lemma par_cptn_dest1_pair:"(\<Gamma>,x#x1#xs) \<in> par_cptn\<^sub>e \<Longrightarrow> (\<Gamma>,x#[x1])\<in> par_cptn\<^sub>e"
proof -
  assume "(\<Gamma>,x#x1#xs) \<in> par_cptn\<^sub>e"
  thus ?thesis using par_cptn_e_dest1 prod.collapse by metis
qed


lemma par_cptn_dest_2:
  "(\<Gamma>,a#xs@ys) \<in> par_cptn\<^sub>e  \<Longrightarrow> (\<Gamma>,a#xs)\<in> par_cptn\<^sub>e"
proof (induct "xs" arbitrary: a)
  case Nil thus ?case using par_cptn\<^sub>e.simps by (cases a, fastforce)    
next
  case (Cons x xs') 
  then have "(\<Gamma>,a#[x])\<in>par_cptn\<^sub>e" by (simp add: par_cptn_dest1_pair)
  also have "(\<Gamma>, x # xs') \<in> par_cptn\<^sub>e"
    using Cons.hyps Cons.prems 
    by (metis append_Cons par_cptn_e_dest_pair)    
  ultimately show ?case using cptne_append_is_cptne [of \<Gamma> a "[x]" x xs']
    by force    
qed   
    
lemma droppar_cptne_is_par_cptne [rule_format]:
  "\<forall>j<length c. (\<Gamma>,c) \<in> par_cptn\<^sub>e \<longrightarrow> (\<Gamma>,drop j c) \<in> par_cptn\<^sub>e"
apply(induct "c")
 apply(force elim: par_cptn\<^sub>e.cases)
apply clarify
apply(case_tac j,simp+)
apply(erule par_cptn\<^sub>e.cases)
  apply simp
 apply force
apply force
  done  
    
lemma par_assum_tail:
  assumes a0:"c =  (\<Gamma>,(p,l)#xs)" and 
          a1:"\<forall>i. Suc i<length (snd c) \<longrightarrow> 
              (fst c)\<turnstile>\<^sub>p((snd c)!i)  \<rightarrow>\<^sub>e ((snd c)!(Suc i)) \<longrightarrow>        
              (snd((snd c)!i), snd((snd c)!(Suc i))) \<in> rely" and
          a2:"c1 = (\<Gamma>,xs)"
    shows "\<forall>i. Suc i<length (snd c1) \<longrightarrow> 
              (fst c1)\<turnstile>\<^sub>p((snd c1)!i)  \<rightarrow>\<^sub>e ((snd c1)!(Suc i)) \<longrightarrow>        
              (snd((snd c1)!i), snd((snd c1)!(Suc i))) \<in> rely"
  using a0 a1 a2 by fastforce
          
definition par_cp\<^sub>e :: "('g\<times>'l,'p,'f,'e) body \<Rightarrow> ('g,'l,'p,'f,'e) par_com \<Rightarrow> 
                       ('g,'l)par_state  \<Rightarrow> ('g,'l,'p,'f,'e) par_confs set" where
  "par_cp\<^sub>e \<Gamma> P s \<equiv> {(\<Gamma>1,l). l!0=(P,s) \<and> (\<Gamma>,l) \<in> par_cptn\<^sub>e \<and> \<Gamma>1=\<Gamma> \<and> wf_conf P s}"

 lemma wf_conf_par_cp: 
  assumes a0:"(\<Gamma>, l) \<in> par_cp\<^sub>e \<Gamma> c s" 
  shows "\<forall>i< length l. wf_conf (fst (l!i)) (snd (l!i))"

proof-
  { 
    have l:"l!0=(c,s)" and cpt:"(\<Gamma>,l) \<in> par_cptn\<^sub>e" and wf:"length c \<le> length (snd s)" 
      using a0 unfolding par_cp\<^sub>e_def
      apply blast unfolding par_cp\<^sub>e_def
      apply (metis (no_types, lifting) Product_Type.Collect_case_prodD assms par_cp\<^sub>e_def snd_conv)
      by (metis (no_types, lifting) Product_Type.Collect_case_prodD 
            assms par_cp\<^sub>e_def prod.collapse wf_conf.simps)
    have ?thesis using l cpt wf 
    proof(induct l arbitrary: c s)
      case Nil
      then show ?case
        by simp 
    next
      case (Cons a l)
      moreover { assume "l=[]"
        then have ?case using Cons
          by (metis fst_conv length_Cons less_Suc0 list.size(3) snd_conv wf_conf.elims(3))
      }
      moreover {
        fix s' c' l1 
        assume a00:"l = (c', s')#l1"
        then obtain e  where step:"\<Gamma>\<turnstile>\<^sub>p\<^sub>e (c, s) \<rightarrow> (c', s') \<or> \<Gamma>\<turnstile>\<^sub>p (c, s) \<rightarrow>\<^sub>e (c', s')" 
          using l Cons par_cptn_step[of \<Gamma> c s c' s' l1] by fastforce 
        then have  "length c' \<le> length (snd s')"
          using calculation(4) 
          by (metis all_same_length_state_program_par_step fst_conv snd_conv steppe_stepp)        
        then have ?case using Cons apply auto
          by (metis (no_types, lifting) a00 diff_Suc_1 fst_conv less_Suc_eq_0_disj nth_Cons' 
           par_cptn_e_dest_pair prod.collapse snd_conv wf_conf.simps)        
      } ultimately show ?case
        by (metis list.exhaust surj_pair) 
    qed    
  } thus ?thesis by auto
qed

lemma wf_conf_par_cp_last: 
  assumes a0:"(\<Gamma>, l) \<in> par_cp\<^sub>e \<Gamma> c s" 
  shows "wf_conf (fst (last l)) (snd (last l))"
proof-
  have "length l > 0" using a0 unfolding par_cp\<^sub>e_def
    using par_cptn\<^sub>e.simps by fastforce
  moreover have "wf_conf (fst (l!((length l)-1)))  (snd (l!((length l)-1)))"
    using calculation wf_conf_par_cp[OF a0] by simp
  ultimately show ?thesis
    using \<open>0 < length l\<close>
    by (simp add: last_conv_nth)
qed
  

lemma eq_wf_state_conf:"length P > 0 \<Longrightarrow> wf_state ((length P)-1) s = wf_conf P s"
  unfolding wf_state_def apply (cases s, auto)
  by (metis diff_Suc_less length_greater_0_conv less_imp_diff_less order.not_eq_order_implies_strict)

lemma eq_par_cp\<^sub>e_par_cp:"par_cp\<^sub>e \<Gamma> P s = par_cp \<Gamma> P s" 
  using par_cptn_eq eq_wf_state_conf unfolding par_cp\<^sub>e_def par_cp_def apply auto
  apply (smt prod.collapse wf_conf.simps)
  by (smt prod.collapse wf_conf.simps) 
                                                              
lemma par_cp_l_dest:"(\<Gamma>, l) \<in> par_cp\<^sub>e \<Gamma> c s \<Longrightarrow>  
       \<exists>l'. l = (c,s)#l'" 
unfolding par_cp\<^sub>e_def 
proof-
  assume "(\<Gamma>, l) \<in> {(\<Gamma>1, ls). ls ! 0 = (c, s) \<and> (\<Gamma>, ls) \<in> par_cptn\<^sub>e \<and> \<Gamma>1 = \<Gamma> \<and> 
          wf_conf c s}"
  then have l:"l!0 = (c,s) \<and> (\<Gamma>, l) \<in> par_cptn\<^sub>e" by auto
  thus ?thesis proof (cases l)
    case Nil thus ?thesis using l par_cptn\<^sub>e.simps by blast
  next 
    case (Cons la lh) thus ?thesis using l par_cptn\<^sub>e.simps by auto
  qed
qed
      
lemma par_cptn\<^sub>e_take_suc_i:
  "(\<Gamma>, l)\<in> par_cptn\<^sub>e \<Longrightarrow>
   i < length l \<Longrightarrow>
   k = length l - i -1 \<Longrightarrow>
  (\<Gamma>, (take (i+1) l)) \<in> par_cptn\<^sub>e"
proof(induct k arbitrary:l i)
  case 0 thus ?case by auto    
next
  case (Suc k)
  then obtain a l1 where l:"l = a #l1"
    by (metis gr_implies_not_zero list.exhaust_sel list.size(3)) 
  {
   assume "i=0" then have ?case
   proof -
     have "(\<Gamma>, take 1 l) \<in> par_cptn\<^sub>e"
       by (metis (no_types) One_nat_def Suc.prems(1) neq_Nil_conv 
           par_cptn\<^sub>e.ParCptnOne surj_pair take_Suc_Cons take_eq_Nil)
     then show ?thesis
       by (simp add: \<open>i = 0\<close>)
   qed 
  } note l1 = this
  { assume "i>0"    
    then obtain i' where "i = i'+1"
      by (metis Suc_diff_1 Suc_eq_plus1) 
    then have ?case using Suc l
      by (metis Suc_eq_plus1 append_take_drop_id par_cptn_dest_2 take_Suc_Cons)
  } thus ?case using l1 by auto
qed   
  
lemma par_cptn\<^sub>e_take_i:
  "(\<Gamma>, l)\<in> par_cptn\<^sub>e \<Longrightarrow>
   i < length l \<Longrightarrow>   
  (\<Gamma>, (take (i+1) l)) \<in> par_cptn\<^sub>e"
using par_cptn\<^sub>e_take_suc_i by auto
    
lemma par_cp\<^sub>e_app:
  assumes a0:"(\<Gamma>, (c',s')#l') \<in> par_cp\<^sub>e \<Gamma> c' s'" and
          a1:"(\<Gamma>, l) \<in> par_cp\<^sub>e \<Gamma> c s \<and> l!i = (c', s') \<and> i<length l"
  shows "(\<Gamma>, (take (i+1) l) @ l') \<in> par_cp\<^sub>e \<Gamma> c s"
proof-
  have "l!0 = (c,s) \<and> (\<Gamma>, l)\<in> par_cptn\<^sub>e" using a1 unfolding par_cp\<^sub>e_def by auto
  then have "(\<Gamma>, (take (i+1) l) ) \<in> par_cptn\<^sub>e" using a1 par_cptn\<^sub>e_take_suc_i by auto
  then obtain a b where take_ab:"(take (i+1) l) = a#b" using par_cptn\<^sub>e.simps by blast 
  also then have  "(a#b)!length b = (c',s')" using a1    
  proof -
    have f1: "Suc i = i + Suc 0"
      by presburger
    have f2: "\<forall>n ps. \<not> n < length ps \<or> (ps ! n) # drop (Suc n) ps = drop n ps"
      using Cons_nth_drop_Suc by blast
    then have "length (take i l) + (length (drop (i + 1) l) + Suc 0) = 
               length ((a # b) @ drop (i + 1) l)" using f1 
      by (metis (no_types) One_nat_def a1 
                append_take_drop_id take_ab length_append list.size(4))
    then have "length (take i l) = length b" by force
    then show ?thesis
      by (metis One_nat_def a1 f1 nth_append_length take_Suc_conv_app_nth take_ab)       
  qed
  ultimately show ?thesis using a0 cptne_append_is_cptne unfolding par_cp\<^sub>e_def
  proof -
    assume a1: "(\<Gamma>, (c', s') # l') \<in> {(\<Gamma>1, l). l ! 0 = (c', s') \<and> 
                (\<Gamma>, l) \<in> par_cptn\<^sub>e \<and> \<Gamma>1 = \<Gamma> \<and> wf_conf c' s'}"
    have "l \<noteq> []"
      using a1 gr_implies_not_zero
      using assms(2) by auto
    then have f2: "wf_conf c s"
      by (metis \<open>l ! 0 = (c, s) \<and> (\<Gamma>, l) \<in> par_cptn\<^sub>e\<close> assms(2) fst_conv 
           length_greater_0_conv snd_conv wf_conf.elims(3) wf_conf_par_cp)
    have f3: "(take (i + 1) l @ l') ! 0 = l ! 0"
      by (metis (no_types) append_Cons append_take_drop_id nth_Cons_0 take_ab)
    have "((c', s') # l') ! 0 = (c', s') \<and> (\<Gamma>, (c', s') # l') \<in> par_cptn\<^sub>e \<and> wf_conf c' s'"
      using a1 by force
    then have "(\<Gamma>, a # b @ l') \<in> par_cptn\<^sub>e"
      by (metis (no_types) \<open>(\<Gamma>, take (i + 1) l) \<in> par_cptn\<^sub>e\<close> 
            \<open>(a # b) ! length b = (c', s')\<close> cptne_append_is_cptne take_ab)
    then show "(\<Gamma>, take (i + 1) l @ l') \<in> {(f, ps). ps ! 0 = (c, s) \<and> 
                  (\<Gamma>, ps) \<in> par_cptn\<^sub>e \<and> f = \<Gamma> \<and> wf_conf c s }"
      using f3 f2 \<open>l ! 0 = (c, s) \<and> (\<Gamma>, l) \<in> par_cptn\<^sub>e\<close> take_ab case_prodI 
      unfolding par_cp\<^sub>e_def by auto
   qed
qed
  
lemma par_cp\<^sub>e_app1:
  assumes a0:"(\<Gamma>, l') \<in> par_cp\<^sub>e \<Gamma> c' s'" and
          a1:"(\<Gamma>, l) \<in> par_cp\<^sub>e \<Gamma> c s \<and> l!i = (c', s') \<and> i<length l"
  shows "(\<Gamma>, (take i l) @ l') \<in> par_cp\<^sub>e \<Gamma> c s"
proof-
  obtain l'' where l:"l'= (c',s')#l''"  unfolding par_cp\<^sub>e_def
    using a0 par_cp_l_dest by blast 
  then have "(\<Gamma>, (take (i+1) l) @ l'') \<in> par_cp\<^sub>e \<Gamma> c s"
    using par_cp\<^sub>e_app a1 a0 by blast
  thus ?thesis using a1 l
  proof -
    have f1: "drop i l = (c', s') # drop (Suc i) l"
      by (metis (no_types) Cons_nth_drop_Suc a1)
    have "take (i + 1) l = take i l @ take (Suc 0) (drop i l)"
      by (metis One_nat_def take_add)
    then show ?thesis
      using f1 \<open>(\<Gamma>, take (i + 1) l @ l'') \<in> par_cp\<^sub>e \<Gamma> c s\<close> l by force
  qed 
qed
  
                                         
lemma tau_tran_closure_cptn: 
  assumes a0:"\<Gamma>\<turnstile>\<^sub>p (c,s) \<rightarrow>\<^sub>\<tau>\<^sup>* (c',s')" and a1:"wf_conf c s"
  shows "\<exists>l. (\<Gamma>,l) \<in>par_cp\<^sub>e \<Gamma> c s \<and> last l = (c',s')"
  using a0
proof  (induct rule: rtranclp_induct[case_names Refl Step] )
  case Refl       
   then show ?case unfolding par_cp\<^sub>e_def using par_cptn\<^sub>e.intros(1)[of _ c s] a1 by force
 next
   case (Step a1 a2) 
   then obtain c1 s1 c2 s2 where a1:"a1=(c1,s1) \<and> a2=(c2,s2)"
     by (meson wf_conf.cases)    
   with Step have c1_cptn:"(\<Gamma>,(c1,s1)#[(c2,s2)])\<in>par_cptn\<^sub>e" using par_cptn\<^sub>e.intros
     by (simp add: par_cptn\<^sub>e.ParCptnComp par_cptn\<^sub>e.ParCptnOne)
   from Step obtain l1 where cs_cptn:"(\<Gamma>,(c,s)#l1) \<in> par_cptn\<^sub>e" and 
                             last:"last ((c,s)#l1) = (c1,s1)" 
     unfolding par_cp\<^sub>e_def using a1
     by (metis (mono_tags, lifting) Product_Type.Collect_case_prodD Step.hyps(3) par_cp\<^sub>e_def par_cp_l_dest snd_conv) 
   have "(\<Gamma>, (c, s) # l1 @ [(c2, s2)]) \<in> par_cptn\<^sub>e" using a1 cptne_append_is_cptne[OF cs_cptn c1_cptn] last
     unfolding par_cp\<^sub>e_def by (simp add: last_length) 
   thus ?case using a1 unfolding par_cp\<^sub>e_def
     using Step.hyps(3) par_cp\<^sub>e_def snoc_eq_iff_butlast
     using assms(2) by fastforce 
 qed


lemma append_assume_R: assumes     
  a0:  "(\<Gamma>, l\<^sub>s) \<in> par_cp\<^sub>e \<Gamma> c  \<sigma> \<and>
        last l\<^sub>s = (c, \<sigma>') \<and>
        (\<forall>i. Suc i < length l\<^sub>s \<longrightarrow> \<Gamma>\<^sub>s\<turnstile>\<^sub>p (l\<^sub>s ! i) \<rightarrow>\<^sub>e (l\<^sub>s ! Suc i) \<longrightarrow> (snd (l\<^sub>s ! i), snd (l\<^sub>s ! Suc i)) \<in> R)" and
  a1: "l' =  l\<^sub>s@[(c, \<sigma>'')]" and
  a2:"(\<sigma>', \<sigma>'')\<in> R"            
shows "(\<forall>i. Suc i < length l' \<longrightarrow> \<Gamma>\<^sub>s\<turnstile>\<^sub>p (l' ! i) \<rightarrow>\<^sub>e (l' ! Suc i) \<longrightarrow> (snd (l' ! i), snd (l' ! Suc i)) \<in> R)"
proof -
  {fix i
    assume a00:"Suc i < length l'" and
     a01:"\<Gamma>\<^sub>s\<turnstile>\<^sub>p (l' ! i) \<rightarrow>\<^sub>e (l' ! Suc i)" 
    then have "(snd (l' ! i), snd (l' ! Suc i)) \<in> R" 
    proof-
    {assume "i<length l\<^sub>s" 
      then have ?thesis using a0 a1 a00 a01
        by (metis (no_types, lifting) Suc_lessI a2 diff_Suc_1 last_conv_nth length_0_conv nat.simps(3) 
               nth_append nth_append_length snd_conv)
    } 
    moreover {assume "i\<ge>length l\<^sub>s"     
     then have ?thesis using a1 a2 a0 a00 by auto 
    } ultimately show ?thesis by fastforce
    qed
  } thus ?thesis by auto
qed

 
lemma tau_tran_env_closure_cptn: 
  assumes a0: "\<Gamma>\<turnstile>\<^sub>p (c,  \<sigma>) \<rightarrow>\<^sub>e\<^sup>* (c,  \<sigma>')" and a1:"wf_conf c \<sigma>"
  shows "\<exists>l\<^sub>s. (\<Gamma>,l\<^sub>s) \<in>par_cp\<^sub>e \<Gamma> c \<sigma> \<and> last l\<^sub>s = (c, \<sigma>') "
  using a0
proof  (induct rule: rtranclp_induct[case_names Refl Step] )
  case Refl       
   show ?case 
     using  tau_tran_closure_cptn a1 unfolding par_cp\<^sub>e_def apply auto
     by (metis a1 eq_snd_iff last.simps nth_Cons_0 par_cptn\<^sub>e.ParCptnOne wf_conf.simps)
 next
   case (Step a1 a2) 
   then obtain c1 s1 c2 s2 where a2:"a1=(c1,s1) \<and> a2=(c2,s2)"
     using prod.exhaust_sel by blast      
   have "(\<Gamma>,[(c1, s2)])\<in>par_cptn\<^sub>e" using par_cptn\<^sub>e.intros  by blast
   then  
   have c1_cptn:"(\<Gamma>,(c1,s1)#[(c1, s2)])\<in>par_cptn\<^sub>e" 
     using  Step(1)   Step(3) par_cptn\<^sub>e.intros(2) Step(2)
     by (metis a2 env_pe_c_c'_false)    
   from Step obtain l1 where cs_cptn:"(\<Gamma>,(c, \<sigma>)#l1) \<in> par_cptn\<^sub>e" and 
                             last:"last ((c, \<sigma>)#l1) = (c1, s1)" 
     unfolding par_cp\<^sub>e_def using a2 
     by (metis (mono_tags, lifting) Product_Type.Collect_case_prodD 
          par_cp\<^sub>e_def Step.hyps(3)  par_cp_l_dest snd_conv) 
   have "(\<Gamma>, (c,  \<sigma>) # l1 @ [(c1, s2)]) \<in> par_cptn\<^sub>e" using a1 cptne_append_is_cptne[OF cs_cptn c1_cptn] last
     unfolding par_cp\<^sub>e_def by (simp add: last_length)   
   then show ?case using a1 a2 unfolding par_cp\<^sub>e_def apply auto
     by (metis Step.hyps(2) append_is_Nil_conv env_pe_c_c'_false last_ConsR 
             last_snoc list.distinct(1) nth_Cons_0 )
 qed
 
lemma id_R_rtrancl_trancl:"\<forall>a. (a,a)\<in>R \<Longrightarrow> R\<^sup>*=R\<^sup>+"
  by (metis equalityI prod.exhaust r_into_rtrancl r_into_trancl' subsetI 
       trancl_rtrancl_absorb transitive_closure_trans(8))

lemma wf_conf_R: 
  assumes 
       a0:"\<forall>\<sigma>. (\<sigma>,\<sigma>)\<in>R" and a5:"wf_conf c \<sigma>" and
       a2:"(\<sigma>, \<sigma>') \<in> R\<^sup>*" and a3:"\<sigma>' = \<sigma>n'" and a4:"R \<subseteq> R_eq_locals" 
   shows "wf_conf c  \<sigma>'"
proof-
  have a2:"(\<sigma>,  \<sigma>') \<in> R\<^sup>+" using a2 a0 id_R_rtrancl_trancl by blast    
  show ?thesis using a2 a3
  proof  (induct arbitrary: \<sigma>n' rule: Transitive_Closure.trancl_induct[case_names Refl Step] )
    case (Refl \<sigma>' ) 
    then show ?case using a4 a5 unfolding R_eq_locals_def  by fastforce
  next
    case (Step \<sigma>' \<sigma>'') 
    then show ?case using a4 unfolding R_eq_locals_def by fastforce
  qed
qed


lemma R_cptn:
  assumes a0:"\<forall>\<sigma>. (\<sigma>,\<sigma>)\<in>R" and a5:"wf_conf c \<sigma>" and
          a2:"(\<sigma>, \<sigma>') \<in> R\<^sup>*" and  a4:"R \<subseteq> R_eq_locals"
        shows "\<exists>l\<^sub>s. (\<Gamma>,l\<^sub>s) \<in>par_cp\<^sub>e \<Gamma> c \<sigma> \<and> last l\<^sub>s = (c, \<sigma>') \<and> 
               (\<forall>i. Suc i<length l\<^sub>s \<longrightarrow> 
                 \<Gamma>\<^sub>s\<turnstile>\<^sub>p(l\<^sub>s!i)  \<rightarrow>\<^sub>e (l\<^sub>s!(Suc i)) \<longrightarrow>        
                 (snd(l\<^sub>s!i), snd(l\<^sub>s!(Suc i))) \<in> R)"
proof-   
  have a2:"(\<sigma>,  \<sigma>') \<in> R\<^sup>+" using a2 a0 id_R_rtrancl_trancl
    by blast    
  show ?thesis using a2 
proof  (induct rule: Transitive_Closure.trancl_induct[case_names Refl Step] )
  case (Refl \<sigma>' )
  then have "(\<Gamma>, [(c, \<sigma>')])\<in> par_cptn\<^sub>e"  using par_cptn\<^sub>e.intros(1)[of _ c \<sigma>'] by force  
  moreover have  "snd \<sigma> = snd \<sigma>'" using Refl a4 unfolding R_eq_locals_def by fastforce  
  moreover have "\<Gamma>\<turnstile>\<^sub>p (c,  \<sigma>) \<rightarrow>\<^sub>e (c,  \<sigma>')" 
    using ParEnv calculation by (metis prod.exhaust_sel)
  then have "(\<Gamma>, (c, \<sigma>) # [(c,  \<sigma>')]) \<in> par_cptn\<^sub>e"
    by (simp add: calculation(1) par_cptn\<^sub>e.ParCptnEnv)        
  ultimately show ?case unfolding par_cp\<^sub>e_def using a5 par_cptn\<^sub>e.intros(2)  Refl apply auto 
    by (smt One_nat_def diff_Suc_1 last.simps last_length length_Cons less_antisym list.simps(3) list.size(3)
            not_add_less1 nth_Cons_0 plus_1_eq_Suc prod.collapse snd_conv wf_conf.simps)
        
next
  case (Step \<sigma>' \<sigma>'')  
  then obtain l\<^sub>s where l:" (\<Gamma>, l\<^sub>s) \<in> par_cp\<^sub>e \<Gamma> c \<sigma> \<and>
          last l\<^sub>s = (c,  \<sigma>') \<and>
          (\<forall>i. Suc i < length l\<^sub>s \<longrightarrow> \<Gamma>\<^sub>s\<turnstile>\<^sub>p (l\<^sub>s ! i) \<rightarrow>\<^sub>e (l\<^sub>s ! Suc i) \<longrightarrow> (snd (l\<^sub>s ! i), snd (l\<^sub>s ! Suc i)) \<in> R)"
    using Step(3)
    using a4 a5 by blast     
  then have "(\<Gamma>, (c, \<sigma>')#[(c, \<sigma>'')])\<in> par_cptn\<^sub>e" 
    using Step a4  ParEnv par_cptn\<^sub>e.intros(2) par_cptn\<^sub>e.intros(1)
  proof-
    have "snd \<sigma>' = snd \<sigma>''" using Step a4  unfolding R_eq_locals_def by fastforce
    moreover have "\<Gamma>\<turnstile>\<^sub>p (c,  \<sigma>') \<rightarrow>\<^sub>e (c,  \<sigma>'')" 
      using ParEnv calculation by (metis prod.exhaust_sel)
    then show ?thesis
       using par_cptn\<^sub>e.intros(2) par_cptn\<^sub>e.intros(1) ParEnv
       by blast
  qed      
  then have l':"(\<Gamma>, l\<^sub>s@[(c, \<sigma>'')])\<in> par_cptn\<^sub>e" using l
    by (metis (no_types, lifting) append_Cons case_prodD cptne_append_is_cptne last_length mem_Collect_eq par_cp\<^sub>e_def par_cp_l_dest) 
  moreover have "last (l\<^sub>s@[(c, \<sigma>'')]) = (c, \<sigma>'')" by auto
  moreover have "(l\<^sub>s@[(c,\<sigma>'')]) ! 0 = (c,  \<sigma>)" using l unfolding par_cp\<^sub>e_def
    using l par_cp_l_dest by fastforce
  ultimately show ?case using l append_assume_R[OF l _ Step(2)[simplified  Step(3)], of "l\<^sub>s @ [(c,\<sigma>'')]"] 
    using l unfolding par_cp\<^sub>e_def by auto
  qed
qed

lemma l_append:
  assumes 
      a0:"i<length l" 
    shows "l!i = (l@l1)!i "
  by (simp add:  a0 nth_append)
  
lemma add_l: assumes 
  a0:"Suc i = length l" and
  a1:"last l = (c1, s1)" 
 shows "(l @ [(c2, s2)]) ! i = (c1, s1) \<and>
       (l @ [(c2, s2)]) ! Suc i = (c2, s2)"
proof -
 
  have "\<forall>ps n. \<exists>psa p. (Suc n \<noteq> length ps \<or> length psa = n) \<and> 
               (Suc n \<noteq> length ps \<or> (p::'a \<times> 'b) # psa = ps)"
    by (metis Suc_length_conv)
  then show ?thesis
    using a0 a1  by (metis (no_types) last_length lessI 
                     nth_append nth_append_length)
qed

lemma assum_union:
  assumes a0:"\<forall>i. Suc i < length l \<longrightarrow> 
                  \<Gamma>\<^sub>s\<turnstile>\<^sub>p l ! i \<rightarrow>\<^sub>e (l ! Suc i) \<longrightarrow> 
                 (snd (l ! i), snd (l ! Suc i)) \<in> R"  and
          a1:"\<forall>i. Suc i < length l' \<longrightarrow> 
                   \<Gamma>\<^sub>s\<turnstile>\<^sub>p l' ! i \<rightarrow>\<^sub>e (l' ! Suc i) \<longrightarrow> 
                  (snd (l' ! i), snd (l' ! Suc i)) \<in> R" and
          a2:"j<length l \<and> l!j = l'!0"
   shows "\<forall>i. Suc i<length ((take j l)@ l') \<longrightarrow> 
               \<Gamma>\<^sub>s\<turnstile>\<^sub>p(((take j l)@ l')!i)  \<rightarrow>\<^sub>e (((take j l)@ l')!(Suc i)) \<longrightarrow>        
               (snd(((take j l)@ l')!i), snd(((take j l)@ l')!(Suc i))) \<in> R"
proof-   
       
  { assume "j=0"
    then have ?thesis using a1 by auto
  } note l = this
  {
    assume j:"j>0"
    then have eq:"\<forall>i<j. ((take j l)@ l')!i = l!i" using a2 by (simp add: nth_append)         
    {fix i
     assume a00: "Suc i<length ((take j l)@ l')" and
            a01: "\<Gamma>\<^sub>s\<turnstile>\<^sub>p(((take j l)@ l')!i)  \<rightarrow>\<^sub>e (((take j l)@ l')!(Suc i))"      
     {assume "Suc i<j"
       then have "(snd ((take j l @ l') ! i), snd ((take j l @ l') ! Suc i)) \<in> R" 
         using a0 a2 a01 by (simp add: nth_append)
     } note l1 = this
     {assume suc:"Suc i = j"       
       then have "(take j l @ l') ! i = l!i" using eq by simp          
       also have " (take j l @ l') ! j = l'!0" 
         using a2 a00 suc str3[of "take j l" _ l'] by auto       
       ultimately have "(snd ((take j l @ l') ! i), snd ((take j l @ l') ! Suc i)) \<in> R" 
         using a2 a0 suc  a01 by auto          
     } note l2 =this
     {
       assume suc:"Suc i > j"  
       have l:"length (take j l) = j" using a2 by auto
       then have "(take j l @ l') ! i = l'!(i-j)" using a00 str3[of "take j l" _ l'] suc  by auto
       moreover have "(take j l @ l') ! Suc i = l'!((Suc i)-j)" using str3[of "take j l" _ l'] a00 suc l by auto
       ultimately have "(snd ((take j l @ l') ! i), snd ((take j l @ l') ! Suc i)) \<in> R" 
         using a1 suc l a00 a01
         by (simp add: a2 Suc_diff_le less_Suc_eq_le)    
     }
     then have "(snd(((take j l)@ l')!i), snd(((take j l)@ l')!(Suc i))) \<in> R" 
       using l1 l2 by fastforce   
   } then have ?thesis by auto 
   then have ?thesis by auto
  } thus ?thesis using l by fastforce
qed
  
lemma assum_union_comp_tran:
  assumes a0:"\<forall>i. Suc i < length l \<longrightarrow> 
                  \<Gamma>\<turnstile>\<^sub>p l ! i \<rightarrow>\<^sub>e (l ! Suc i) \<longrightarrow> 
                 (snd (l ! i), snd (l ! Suc i)) \<in> R"  and
          a1:"\<forall>i. Suc i < length l' \<longrightarrow> 
                   \<Gamma>\<turnstile>\<^sub>p l' ! i \<rightarrow>\<^sub>e (l' ! Suc i) \<longrightarrow> 
                  (snd (l' ! i), snd (l' ! Suc i)) \<in> R" and
          a2:"last l = (c',s') \<and> l'!0 = (c'',s'') \<and> \<Gamma>\<turnstile>\<^sub>p\<^sub>a (c',s') \<rightarrow> (c'',s'')"
   shows "\<forall>i. Suc i<length (l@ l') \<longrightarrow> 
               \<Gamma>\<turnstile>\<^sub>p((l@ l')!i)  \<rightarrow>\<^sub>e ((l@ l')!(Suc i)) \<longrightarrow>        
               (snd((l@ l')!i), snd((l@ l')!(Suc i))) \<in> R"
proof - 
    {      
      fix i
      assume a01:"Suc i<length (l@l')" and
             a02: "\<Gamma>\<turnstile>\<^sub>p((l@l')!i)  \<rightarrow>\<^sub>e ((l@l')!(Suc i))"
      have not_env:"\<not> \<Gamma>\<turnstile>\<^sub>p (c',s')  \<rightarrow>\<^sub>e (c'',s'')" using a2
        by (metis  env_pe_c_c'_false nth_list_update_eq 
               step_change_p_or_eq_s step_pev_pair_elim_cases stepce_stepc)
      {
        assume a001: "Suc i< length l" 
        then have "l!i = (l@l')!i \<and>
              l!(Suc i) = (l@l')!(Suc i)"
          using l_append[of _ l l'] by fastforce      
        then have "(snd((l@l')!i), snd((l@l')!(Suc i))) \<in> R"
          using  a0 a02 a001 by auto
      } note l1 = this
      {
        assume a001: "Suc i = length l"         
        then have "l = [] \<longrightarrow> (l @ l') ! i = (c', s')"
            by auto
        then have "(l@l')!i = (c',s') \<and>
                   (l@l')!(Suc i) = (c'',s'')"
          using a2 a001
          by (metis cancel_comm_monoid_add_class.diff_cancel diff_Suc_1 
                    last_conv_nth lessI nth_append order_less_irrefl)
        then have "(snd((l@l')!i), snd((l@l')!(Suc i))) \<in> R" 
          using not_env a2 a02 a001 by auto
      } note l2= this
      { assume a001: "Suc i > length l"
        then obtain k where k:"i = length l + k"          
          using less_imp_Suc_add by auto          
        also have "\<forall>i. (l@l') ! (length l + i) =
                        l'!i" by auto
        ultimately have "(l@l')!i = l'!k \<and>
                         (l@l')!Suc i = l'!Suc k"
          by (metis add_Suc_right)        
        then have "(snd((l@l')!i), snd((l@l')!(Suc i))) \<in> R" 
         using a1 a01 a02  k by auto
      }
      then have "(snd((l@l')!i), snd((l@l')!(Suc i))) \<in> R"
        using l1 l2 a02 not_env by fastforce
    } thus ?thesis by auto
qed

lemma tau_tran_closure_cptn1: 
  assumes a0:"\<Gamma>\<turnstile>\<^sub>p (c,s) \<rightarrow>\<^sub>\<tau>\<^sup>* (c',s')" and a1:"wf_conf c s"
  shows "\<exists>l. (\<Gamma>,l) \<in>par_cp\<^sub>e \<Gamma> c s \<and> 
             (\<forall>i. Suc i<length l \<longrightarrow> 
                       \<Gamma>\<turnstile>\<^sub>p(l!i)  \<rightarrow>\<^sub>e (l!(Suc i)) \<longrightarrow>        
                       (snd(l!i), snd(l!(Suc i))) \<in> R) \<and> 
             last l = (c',s')"
  using a0
proof  (induct rule: rtranclp_induct[case_names Refl Step] )
  case Refl       
   show ?case unfolding par_cp\<^sub>e_def wf_conf.simps using par_cptn\<^sub>e.intros(1)[of _ c s] a1 apply auto
     by (metis One_nat_def last.simps length_Cons list.size(3) 
    not_add_less1 nth_Cons_0 plus_1_eq_Suc snd_conv wf_conf.elims(2)) 
 next
   case (Step a1 a2) 
   then obtain c1 s1 c2 s2 where a1:"a1=(c1,s1) \<and> a2=(c2,s2)"
     using prod.exhaust_sel by blast   
   with Step have c1_cptn:"(\<Gamma>,(c1,s1)#[(c2,s2)])\<in>par_cptn\<^sub>e" 
     using par_cptn\<^sub>e.intros
     by (simp add: par_cptn\<^sub>e.ParCptnComp par_cptn\<^sub>e.ParCptnOne)
   from Step obtain l1 where cs_cptn:"(\<Gamma>,(c,s)#l1) \<in> par_cptn\<^sub>e" and 
                             all_r: "(\<forall>i. Suc i<length ((c,s)#l1) \<longrightarrow> 
                                          \<Gamma>\<turnstile>\<^sub>p(((c,s)#l1)!i)  \<rightarrow>\<^sub>e (((c,s)#l1)!(Suc i)) \<longrightarrow>        
                                          (snd(((c,s)#l1)!i), snd(((c,s)#l1)!(Suc i))) \<in> R)" and
                             last:"last ((c,s)#l1) = (c1,s1)" 
     unfolding par_cp\<^sub>e_def using a1
     by (metis (mono_tags, lifting) Product_Type.Collect_case_prodD  par_cp\<^sub>e_def par_cp_l_dest snd_conv) 
   have "(\<Gamma>, (c, s) # l1 @ [(c2, s2)]) \<in> par_cptn\<^sub>e" using a1 cptne_append_is_cptne[OF cs_cptn c1_cptn] last
     unfolding par_cp\<^sub>e_def by (simp add: last_length)
   also have tran:"(\<forall>i. Suc i<length ((c, s) # l1 @ [(c2, s2)]) \<longrightarrow> 
                      \<Gamma>\<turnstile>\<^sub>p(((c, s) # l1 @ [(c2, s2)])!i)  \<rightarrow>\<^sub>e (((c, s) # l1 @ [(c2, s2)])!(Suc i)) \<longrightarrow>        
                      (snd(((c, s) # l1 @ [(c2, s2)])!i), snd(((c, s) # l1 @ [(c2, s2)])!(Suc i))) \<in> R)"
     using assum_union_comp_tran[OF all_r, of "[(c2,s2)]" c1 s1 c2 s2]  last Step(2) a1 by fastforce   
   ultimately show ?case
     using a1  unfolding par_cp\<^sub>e_def  apply auto
     by (metis (no_types, lifting) tran append_is_Nil_conv assms(2) 
              last.simps last_snoc list.simps(3) nth_Cons_0 prod.collapse wf_conf.simps)
qed  
  
  
  
lemma evnt_tran_closure_cptn: 
  assumes a0:"\<Gamma>\<turnstile>\<^sub>p\<^sub>e (c,s) \<rightarrow>\<^sup>+ (cf,sf)" and a1:"wf_conf c s"
  shows "\<exists>l. (\<Gamma>,l) \<in>par_cp\<^sub>e \<Gamma> c s \<and>
             last l = (cf,sf)"
proof-
  obtain c' s' c'' s'' 
  where a0:"\<Gamma>\<turnstile>\<^sub>p (c,s) \<rightarrow>\<^sub>\<tau>\<^sup>* (c',s') \<and>  
           (\<exists>a. a = Some e \<and> \<Gamma>\<turnstile>\<^sub>p\<^sub>a (c',s') \<rightarrow> (c'',s'')) \<and> 
            \<Gamma>\<turnstile>\<^sub>p (c'',s'') \<rightarrow>\<^sub>\<tau>\<^sup>* (cf,sf)" using a0 by auto
  then obtain l1 l2 where "(\<Gamma>,(c,s)#l1) \<in>par_cp\<^sub>e \<Gamma> c s " and lastl1:"last ((c,s)#l1) = (c',s')" and
                          "(\<Gamma>,(c'',s'')#l2) \<in>par_cp\<^sub>e \<Gamma> c'' s''" and lastl2:"last ((c'',s'')#l2) = (cf,sf)" 
    using tau_tran_closure_cptn
    by (metis a1 par_cp_l_dest wf_conf_par_step wf_conf_step)                     
  then have l1:"(\<Gamma>,(c,s)#l1)\<in>par_cptn\<^sub>e" and
            l2:"(\<Gamma>,(c'',s'')#l2) \<in>par_cptn\<^sub>e" 
    unfolding par_cp\<^sub>e_def by auto   
  have c:"(\<Gamma>,(c',s')#[(c'',s'')])\<in>par_cptn\<^sub>e" using a0
    by (simp add: a0 par_cptn\<^sub>e.ParCptnComp par_cptn\<^sub>e.ParCptnOne)
 then have cl2:"(\<Gamma>,(c',s')#(c'',s'')#l2) \<in>par_cptn\<^sub>e" and 
           "last ((c',s')#(c'',s'')#l2) = (cf,sf)" 
   using cptne_append_is_cptne[OF c l2] lastl2 by auto
  then have "(\<Gamma>,(c,s)#l1@((c'',s'')#l2)) \<in>par_cptn\<^sub>e" and 
            "last ((c,s)#l1@((c'',s'')#l2)) = (cf,sf)" 
   using cptne_append_is_cptne[OF l1 cl2] lastl1 
   by (auto simp add: last_length lastl2)   
  thus  ?thesis  unfolding par_cp\<^sub>e_def using a1  by force
qed
  
lemma evnt_tran_closure_cptn1: 
  assumes a0:"\<Gamma>\<turnstile>\<^sub>p\<^sub>e (c,s) \<rightarrow>\<^sup>+ (cf,sf)" and a1:"wf_conf c s"
  shows "\<exists>l. (\<Gamma>,l) \<in>par_cp\<^sub>e \<Gamma> c s \<and>
             (\<forall>i. Suc i<length l \<longrightarrow> 
                       \<Gamma>\<turnstile>\<^sub>p(l!i)  \<rightarrow>\<^sub>e (l!(Suc i)) \<longrightarrow>        
                       (snd(l!i), snd(l!(Suc i))) \<in> R) \<and>
             last l = (cf,sf)"
proof-
  obtain c' s' c'' s'' where a0:"\<Gamma>\<turnstile>\<^sub>p (c,s) \<rightarrow>\<^sub>\<tau>\<^sup>* (c',s')" and  
                             a0':"(\<exists>a. a = Some e \<and> \<Gamma>\<turnstile>\<^sub>p\<^sub>a (c',s') \<rightarrow> (c'',s''))" and 
                             a0'':"\<Gamma>\<turnstile>\<^sub>p (c'',s'') \<rightarrow>\<^sub>\<tau>\<^sup>* (cf,sf)" using a0 by auto
  then have a1':"wf_conf c'' s''" using a1  wf_conf_par_step wf_conf_step by blast 
  obtain l1 l2 where "(\<Gamma>,(c,s)#l1) \<in>par_cp\<^sub>e \<Gamma> c s " and
                    envl1:    "(\<forall>i. Suc i<length ((c,s)#l1) \<longrightarrow> 
                                \<Gamma>\<turnstile>\<^sub>p(((c,s)#l1)!i)  \<rightarrow>\<^sub>e (((c,s)#l1)!(Suc i)) \<longrightarrow>        
                                (snd(((c,s)#l1)!i), snd(((c,s)#l1)!(Suc i))) \<in> R)" and
                     lastl1:"last ((c,s)#l1) = (c',s')" and
                          "(\<Gamma>,(c'',s'')#l2) \<in>par_cp\<^sub>e \<Gamma> c'' s''" and 
                      envl2:    "(\<forall>i. Suc i<length ((c'',s'')#l2) \<longrightarrow> 
                                \<Gamma>\<turnstile>\<^sub>p(((c'',s'')#l2)!i)  \<rightarrow>\<^sub>e (((c'',s'')#l2)!(Suc i)) \<longrightarrow>        
                                (snd(((c'',s'')#l2)!i), snd(((c'',s'')#l2)!(Suc i))) \<in> R)" and
                     lastl2:"last ((c'',s'')#l2) = (cf,sf)" 
    using tau_tran_closure_cptn1[OF a0 a1, of R] 
          tau_tran_closure_cptn1[OF a0'' a1', of R] by (blast dest: par_cp_l_dest)                      
  then have l1:"(\<Gamma>,(c,s)#l1)\<in>par_cptn\<^sub>e" and
            l2:"(\<Gamma>,(c'',s'')#l2) \<in>par_cptn\<^sub>e" 
    unfolding par_cp\<^sub>e_def by auto   
  have env:"(\<forall>i. Suc i<length ((c,s)#l1@((c'',s'')#l2)) \<longrightarrow> 
            \<Gamma>\<turnstile>\<^sub>p(((c,s)#l1@((c'',s'')#l2))!i)  \<rightarrow>\<^sub>e (((c,s)#l1@((c'',s'')#l2))!(Suc i)) \<longrightarrow>        
           (snd(((c,s)#l1@((c'',s'')#l2))!i), snd(((c,s)#l1@((c'',s'')#l2))!(Suc i))) \<in> R)"  
  using assum_union_comp_tran[OF envl1 envl2, of c' s' c'' s''] lastl1 a0 a0' a0'' by fastforce  
  have c:"(\<Gamma>,(c',s')#[(c'',s'')])\<in>par_cptn\<^sub>e" using a0' 
    by (simp add: a0 par_cptn\<^sub>e.ParCptnComp par_cptn\<^sub>e.ParCptnOne)
 then have cl2:"(\<Gamma>,(c',s')#(c'',s'')#l2) \<in>par_cptn\<^sub>e" and 
           "last ((c',s')#(c'',s'')#l2) = (cf,sf)" 
   using cptne_append_is_cptne[OF c l2] lastl2 by auto
  then have "(\<Gamma>,(c,s)#l1@((c'',s'')#l2)) \<in>par_cptn\<^sub>e" and 
            "last ((c,s)#l1@((c'',s'')#l2)) = (cf,sf)" 
   using cptne_append_is_cptne[OF l1 cl2] lastl1 
   by (auto simp add: last_length lastl2)   
  thus  ?thesis using env a1 unfolding par_cp\<^sub>e_def
    by (metis (mono_tags, lifting) case_prodI mem_Collect_eq nth_Cons_0)
qed

definition sim_final_state :: "('g\<times>'l, 'p, 'f, 'e) LanguageCon.com list \<Rightarrow>
                               ('g,'l)par_state \<Rightarrow>
                               ('g1\<times>'l1, 'p, 'f, 'e) LanguageCon.com list \<Rightarrow>                                
                               ('g1,'l1)par_state \<Rightarrow>                                 
                               (('g,'l)par_state,('g1,'l1)par_state) rel \<Rightarrow> 
                               (('g,'l)par_state,('g1,'l1)par_state) rel \<Rightarrow> bool"
where
"sim_final_state c\<^sub>c s\<^sub>c c\<^sub>s s\<^sub>s \<gamma>n \<gamma>a \<equiv> 
  (final_error_r c\<^sub>c c\<^sub>s) \<or> 
  (skip_program c\<^sub>s \<and> skip_program c\<^sub>c \<and> (s\<^sub>c,s\<^sub>s)\<in>\<gamma>n) \<or> 
  (throw_program c\<^sub>s \<and> throw_program c\<^sub>c \<and>(s\<^sub>c,s\<^sub>s)\<in>\<gamma>a)"  
    

lemma last_skip_ref1:
  assumes 
   a0: "(\<Gamma>\<^sub>c,(c\<^sub>c,\<sigma>),R\<^sub>c,G\<^sub>c) \<succeq>\<^sub>p\<^sub>(\<^sub>\<alpha>\<^sub>;\<^sub>\<gamma>\<^sub>q\<^sub>;\<^sub>\<gamma>\<^sub>a\<^sub>) (\<Gamma>\<^sub>s,(c\<^sub>s,\<Sigma>),R\<^sub>s,G\<^sub>s)" and a2:"wf_conf c\<^sub>s \<Sigma>" and
   a1:"(\<forall>i<length c\<^sub>c. c\<^sub>c!i = Skip) \<and> 0 < length c\<^sub>c"
  shows 
   "\<exists>l\<^sub>s.   (\<Gamma>\<^sub>s,l\<^sub>s) \<in>par_cp\<^sub>e \<Gamma>\<^sub>s c\<^sub>s \<Sigma> \<and>
           (\<forall>i. Suc i<length l\<^sub>s \<longrightarrow> 
                     \<Gamma>\<^sub>s\<turnstile>\<^sub>p(l\<^sub>s!i)  \<rightarrow>\<^sub>e (l\<^sub>s!(Suc i)) \<longrightarrow>        
                     (snd(l\<^sub>s!i), snd(l\<^sub>s!(Suc i))) \<in> R\<^sub>s) \<and> 
           (\<forall>i<length (fst (last l\<^sub>s)). fst (last l\<^sub>s)!i = Skip) \<and> 
            (\<sigma>,snd(last l\<^sub>s)) \<in>\<gamma>\<^sub>q \<and> 0 < length (fst (last l\<^sub>s))"
proof-
 obtain \<Sigma>' c\<^sub>s' where "((((\<sigma>, \<sigma>),(\<Sigma>,  \<Sigma>')) \<in> (G\<^sub>c,G\<^sub>s\<^sup>*)\<^sub>\<alpha>) \<and>
        (\<sigma>, \<Sigma>')\<in>\<gamma>\<^sub>q \<and> \<gamma>\<^sub>q\<subseteq>\<alpha> \<and>
        \<Gamma>\<^sub>s\<turnstile>\<^sub>p (c\<^sub>s,\<Sigma>) \<rightarrow>\<^sub>\<tau>\<^sup>* (c\<^sub>s', \<Sigma>') \<and> (\<forall>i<length c\<^sub>s'. c\<^sub>s'!i = Skip) \<and> 0 < length c\<^sub>s')"
   using a1 par_sim_elim_cases[OF a0] by force
 thus ?thesis using tau_tran_closure_cptn1 a2 
   by (metis  (mono_tags, lifting) fst_conv snd_conv)     
qed  
  
  
lemma last_skip_ref:  
  assumes 
   a0: "(\<Gamma>\<^sub>c,(c\<^sub>c,\<sigma>),R\<^sub>c,G\<^sub>c) \<succeq>\<^sub>p\<^sub>(\<^sub>\<alpha>\<^sub>;\<^sub>\<gamma>\<^sub>q\<^sub>;\<^sub>\<gamma>\<^sub>a\<^sub>) (\<Gamma>\<^sub>s,(c\<^sub>s,\<Sigma>),R\<^sub>s,G\<^sub>s)" and a2:"wf_conf c\<^sub>s \<Sigma>" and
   a1:"(\<forall>i<length c\<^sub>c. c\<^sub>c!i = Skip) \<and> 0 < length c\<^sub>c"
  shows 
   "\<exists>l\<^sub>s.   (\<Gamma>\<^sub>s,l\<^sub>s) \<in>par_cp\<^sub>e \<Gamma>\<^sub>s c\<^sub>s \<Sigma> \<and>
           (\<forall>i. Suc i<length l\<^sub>s \<longrightarrow> 
                     \<Gamma>\<^sub>s\<turnstile>\<^sub>p(l\<^sub>s!i)  \<rightarrow>\<^sub>e (l\<^sub>s!(Suc i)) \<longrightarrow>        
                     (snd(l\<^sub>s!i), snd(l\<^sub>s!(Suc i))) \<in> R\<^sub>s) \<and>
           final_c (fst (last l\<^sub>s),snd(last l\<^sub>s)) \<and> 0 < length (fst (last l\<^sub>s)) \<and> 
               sim_final_state c\<^sub>c \<sigma> (fst (last l\<^sub>s)) (snd (last l\<^sub>s)) \<gamma>\<^sub>q \<gamma>\<^sub>a"
  using last_skip_ref1[OF a0 a2 a1] a1  
  unfolding sim_final_state_def final_c_def  final1_def final_error_def
  skip_program_def throw_program_def by auto

lemma last_Throw_ref1:
  assumes 
   a0: "(\<Gamma>\<^sub>c,(c\<^sub>c,\<sigma>),R\<^sub>c,G\<^sub>c) \<succeq>\<^sub>p\<^sub>(\<^sub>\<alpha>\<^sub>;\<^sub>\<gamma>\<^sub>q\<^sub>;\<^sub>\<gamma>\<^sub>a\<^sub>) (\<Gamma>\<^sub>s,(c\<^sub>s,\<Sigma>),R\<^sub>s,G\<^sub>s)" and a0':"wf_conf c\<^sub>s \<Sigma>" and
   a1:"throw_program c\<^sub>c"
  shows 
   "\<exists>l\<^sub>s. (\<Gamma>\<^sub>s,l\<^sub>s) \<in>par_cp\<^sub>e \<Gamma>\<^sub>s c\<^sub>s \<Sigma> \<and>
           (\<forall>i. Suc i<length l\<^sub>s \<longrightarrow> 
                     \<Gamma>\<^sub>s\<turnstile>\<^sub>p(l\<^sub>s!i)  \<rightarrow>\<^sub>e (l\<^sub>s!(Suc i)) \<longrightarrow>        
                     (snd(l\<^sub>s!i), snd(l\<^sub>s!(Suc i))) \<in> R\<^sub>s) \<and> 
           final_c (fst (last l\<^sub>s),snd(last l\<^sub>s)) \<and>  0 < length (fst (last l\<^sub>s)) \<and> 
          throw_program (fst (last l\<^sub>s)) \<and> (\<sigma> ,snd(last l\<^sub>s)) \<in>\<gamma>\<^sub>a"
proof-
 have "\<exists>\<Sigma>' c\<^sub>s'. ((\<sigma>, \<sigma>), \<Sigma>, \<Sigma>') \<in> ((G\<^sub>c, G\<^sub>s\<^sup>*)\<^sub>\<alpha>) \<and>
                (\<sigma>, \<Sigma>') \<in> \<gamma>\<^sub>a \<and>
                \<gamma>\<^sub>a \<subseteq> \<alpha> \<and>
                \<Gamma>\<^sub>s\<turnstile>\<^sub>p (c\<^sub>s, \<Sigma>) \<rightarrow>\<^sub>\<tau>\<^sup>* (c\<^sub>s', \<Sigma>') \<and>  throw_program (c\<^sub>s')"
   using a1 par_sim_elim_cases[OF a0]
   by (cases \<sigma>, auto)
 then obtain \<Sigma>' c\<^sub>s' where "((\<sigma>, \<sigma>), \<Sigma>,  \<Sigma>') \<in> ((G\<^sub>c, G\<^sub>s\<^sup>*)\<^sub>\<alpha>) \<and>
                (\<sigma>, \<Sigma>') \<in> \<gamma>\<^sub>a \<and>
                \<gamma>\<^sub>a \<subseteq> \<alpha> \<and>
                \<Gamma>\<^sub>s\<turnstile>\<^sub>p (c\<^sub>s, \<Sigma>) \<rightarrow>\<^sub>\<tau>\<^sup>* (c\<^sub>s',  \<Sigma>') \<and>  throw_program (c\<^sub>s')"
   by auto
 then obtain l\<^sub>s where "(\<Gamma>\<^sub>s, l\<^sub>s) \<in> par_cp\<^sub>e \<Gamma>\<^sub>s c\<^sub>s \<Sigma> \<and>
          (\<forall>i. Suc i < length l\<^sub>s \<longrightarrow> \<Gamma>\<^sub>s\<turnstile>\<^sub>p (l\<^sub>s ! i) \<rightarrow>\<^sub>e (l\<^sub>s ! Suc i) \<longrightarrow> (snd (l\<^sub>s ! i), snd (l\<^sub>s ! Suc i)) \<in> R\<^sub>s) \<and>
           snd(last l\<^sub>s) =  \<Sigma>' \<and> final_c (fst (last l\<^sub>s),snd(last l\<^sub>s)) \<and>
          throw_program (fst (last l\<^sub>s)) \<and> (\<sigma>, \<Sigma>') \<in> \<gamma>\<^sub>a "
   using tau_tran_closure_cptn1 a0' throw_program_final_c 
   by (metis (mono_tags, lifting) fst_conv snd_conv) 
  also then have "0 < length (fst (last l\<^sub>s))" unfolding throw_program_def by force
 ultimately show ?thesis by blast           
qed  

  
lemma last_Throw_ref:
assumes 
 a0: "(\<Gamma>\<^sub>c,(c\<^sub>c,\<sigma>),R\<^sub>c,G\<^sub>c) \<succeq>\<^sub>p\<^sub>(\<^sub>\<alpha>\<^sub>;\<^sub>\<gamma>\<^sub>q\<^sub>;\<^sub>\<gamma>\<^sub>a\<^sub>) (\<Gamma>\<^sub>s,(c\<^sub>s,\<Sigma>),R\<^sub>s,G\<^sub>s)" and a0':"wf_conf c\<^sub>s \<Sigma>" and
 a1:"throw_program c\<^sub>c"
shows 
 "\<exists>l\<^sub>s.   (\<Gamma>\<^sub>s,l\<^sub>s) \<in>par_cp\<^sub>e \<Gamma>\<^sub>s c\<^sub>s \<Sigma> \<and>
         (\<forall>i. Suc i<length l\<^sub>s \<longrightarrow> 
                   \<Gamma>\<^sub>s\<turnstile>\<^sub>p(l\<^sub>s!i)  \<rightarrow>\<^sub>e (l\<^sub>s!(Suc i)) \<longrightarrow>        
                   (snd(l\<^sub>s!i), snd(l\<^sub>s!(Suc i))) \<in> R\<^sub>s) \<and> 
         final_c (fst (last l\<^sub>s),snd(last l\<^sub>s)) \<and>  0 < length (fst (last l\<^sub>s)) \<and>
            sim_final_state c\<^sub>c \<sigma> (fst (last l\<^sub>s)) (snd (last l\<^sub>s)) \<gamma>\<^sub>q \<gamma>\<^sub>a"
 using last_Throw_ref1[OF a0 a0' a1] a1 unfolding sim_final_state_def by auto 
      
lemma last_not_normal_ref1:
  assumes 
   a0: "(\<Gamma>\<^sub>c,(c\<^sub>c,\<sigma>),R\<^sub>c,G\<^sub>c) \<succeq>\<^sub>p\<^sub>(\<^sub>\<alpha>\<^sub>;\<^sub>\<gamma>\<^sub>n\<^sub>;\<^sub>\<gamma>\<^sub>a\<^sub>) (\<Gamma>\<^sub>s,(c\<^sub>s,\<Sigma>),R\<^sub>s,G\<^sub>s)" and a0':"wf_conf c\<^sub>s \<Sigma>" and
   a1:"final_error c\<^sub>c"
  shows 
   "\<exists>l\<^sub>s.   (\<Gamma>\<^sub>s,l\<^sub>s) \<in>par_cp\<^sub>e \<Gamma>\<^sub>s c\<^sub>s \<Sigma> \<and>
           (\<forall>i. Suc i<length l\<^sub>s \<longrightarrow> 
                     \<Gamma>\<^sub>s\<turnstile>\<^sub>p(l\<^sub>s!i)  \<rightarrow>\<^sub>e (l\<^sub>s!(Suc i)) \<longrightarrow>        
                     (snd(l\<^sub>s!i), snd(l\<^sub>s!(Suc i))) \<in> R\<^sub>s) \<and> 
           final_error (fst (last l\<^sub>s))"
proof-  
   have "\<exists>\<Sigma>' c\<^sub>s'.  (((\<sigma>, \<sigma>),(\<Sigma>,  \<Sigma>')) \<in> (G\<^sub>c,G\<^sub>s\<^sup>*)\<^sub>\<alpha>) \<and> \<Gamma>\<^sub>s\<turnstile>\<^sub>p (c\<^sub>s, \<Sigma>) \<rightarrow>\<^sub>\<tau>\<^sup>* (c\<^sub>s', \<Sigma>') \<and> final_error_r c\<^sub>c c\<^sub>s'"
    using a1 par_sim_elim_cases[OF a0] 
    by force
  then obtain \<Sigma>' c\<^sub>s' where "  \<Gamma>\<^sub>s\<turnstile>\<^sub>p (c\<^sub>s, \<Sigma>) \<rightarrow>\<^sub>\<tau>\<^sup>* (c\<^sub>s', \<Sigma>') \<and>  final_error_r c\<^sub>c c\<^sub>s'"
    by auto 
 thus ?thesis using tau_tran_closure_cptn1 using a1 a0' unfolding final_error_r_def
   by (metis (mono_tags, lifting) fst_conv)  
qed  


lemma last_not_normal_ref1':
  assumes 
   a0: "(\<Gamma>\<^sub>c,(c\<^sub>c,\<sigma>),R\<^sub>c,G\<^sub>c) \<succeq>\<^sub>p\<^sub>(\<^sub>\<alpha>\<^sub>;\<^sub>\<gamma>\<^sub>n\<^sub>;\<^sub>\<gamma>\<^sub>a\<^sub>) (\<Gamma>\<^sub>s,(c\<^sub>s,\<Sigma>),R\<^sub>s,G\<^sub>s)" and a0':"wf_conf c\<^sub>s \<Sigma>" and
   a1:"final_error c\<^sub>c"
  shows 
   "\<exists>l\<^sub>s.   (\<Gamma>\<^sub>s,l\<^sub>s) \<in>par_cp\<^sub>e \<Gamma>\<^sub>s c\<^sub>s \<Sigma> \<and>
           (\<forall>i. Suc i<length l\<^sub>s \<longrightarrow> 
                     \<Gamma>\<^sub>s\<turnstile>\<^sub>p(l\<^sub>s!i)  \<rightarrow>\<^sub>e (l\<^sub>s!(Suc i)) \<longrightarrow>        
                     (snd(l\<^sub>s!i), snd(l\<^sub>s!(Suc i))) \<in> R\<^sub>s) \<and> 
           final_error_r c\<^sub>c (fst (last l\<^sub>s))"
proof-  
   have "\<exists>\<Sigma>' c\<^sub>s'.  (((\<sigma>, \<sigma>),(\<Sigma>,  \<Sigma>')) \<in> (G\<^sub>c,G\<^sub>s\<^sup>*)\<^sub>\<alpha>) \<and> \<Gamma>\<^sub>s\<turnstile>\<^sub>p (c\<^sub>s, \<Sigma>) \<rightarrow>\<^sub>\<tau>\<^sup>* (c\<^sub>s', \<Sigma>') \<and> final_error_r c\<^sub>c c\<^sub>s'"
    using a1 par_sim_elim_cases[OF a0] 
    by force
  then obtain \<Sigma>' c\<^sub>s' where "  \<Gamma>\<^sub>s\<turnstile>\<^sub>p (c\<^sub>s, \<Sigma>) \<rightarrow>\<^sub>\<tau>\<^sup>* (c\<^sub>s', \<Sigma>') \<and>  final_error_r c\<^sub>c c\<^sub>s'"
    by auto 
 thus ?thesis using tau_tran_closure_cptn1 using a1 a0'
   by (metis (mono_tags, lifting) fst_conv)  
qed  

lemma last_not_normal_ref:
assumes 
 a0: "(\<Gamma>\<^sub>c,(c\<^sub>c,\<sigma>),R\<^sub>c,G\<^sub>c) \<succeq>\<^sub>p\<^sub>(\<^sub>\<alpha>\<^sub>;\<^sub>\<gamma>\<^sub>q\<^sub>;\<^sub>\<gamma>\<^sub>a\<^sub>) (\<Gamma>\<^sub>s,(c\<^sub>s,\<Sigma>),R\<^sub>s,G\<^sub>s)" and a0':"wf_conf c\<^sub>s \<Sigma>" and
 a1:"final_error c\<^sub>c"
shows 
 "\<exists>l\<^sub>s.   (\<Gamma>\<^sub>s,l\<^sub>s) \<in>par_cp\<^sub>e \<Gamma>\<^sub>s c\<^sub>s \<Sigma> \<and>
         (\<forall>i. Suc i<length l\<^sub>s \<longrightarrow> 
                   \<Gamma>\<^sub>s\<turnstile>\<^sub>p(l\<^sub>s!i)  \<rightarrow>\<^sub>e (l\<^sub>s!(Suc i)) \<longrightarrow>        
                   (snd(l\<^sub>s!i), snd(l\<^sub>s!(Suc i))) \<in> R\<^sub>s) \<and>
         final_c (fst (last l\<^sub>s),snd(last l\<^sub>s)) \<and> 0 < length (fst (last l\<^sub>s)) \<and>
         sim_final_state c\<^sub>c \<sigma> (fst (last l\<^sub>s)) (snd (last l\<^sub>s)) \<gamma>\<^sub>q \<gamma>\<^sub>a"
  using last_not_normal_ref1'[OF a0 a0' a1]  a1 
   error_program_P_not_empty  error_program_final_c final_error_r_sim_spec
  unfolding sim_final_state_def 
  by (cases \<sigma>, blast)
  
  
lemma All_End_simulation:
  assumes 
   a0: "(\<Gamma>\<^sub>c,(c\<^sub>c,\<sigma>),R\<^sub>c,G\<^sub>c) \<succeq>\<^sub>p\<^sub>(\<^sub>\<alpha>\<^sub>;\<^sub>\<gamma>\<^sub>q\<^sub>;\<^sub>\<gamma>\<^sub>a\<^sub>) (\<Gamma>\<^sub>s,(c\<^sub>s,\<Sigma>),R\<^sub>s,G\<^sub>s)" and  a0':"wf_conf c\<^sub>s \<Sigma>" and
   a1:"All_End (c\<^sub>c,\<sigma>)"
  shows 
   "\<exists>l\<^sub>s.   (\<Gamma>\<^sub>s,l\<^sub>s) \<in>par_cp\<^sub>e \<Gamma>\<^sub>s c\<^sub>s \<Sigma> \<and>
           (\<forall>i. Suc i<length l\<^sub>s \<longrightarrow> 
                     \<Gamma>\<^sub>s\<turnstile>\<^sub>p(l\<^sub>s!i)  \<rightarrow>\<^sub>e (l\<^sub>s!(Suc i)) \<longrightarrow>        
                     (snd(l\<^sub>s!i), snd(l\<^sub>s!(Suc i))) \<in> R\<^sub>s) \<and> 
           All_End (last l\<^sub>s) \<and>  sim_final_state c\<^sub>c \<sigma> (fst (last l\<^sub>s)) (snd (last l\<^sub>s)) \<gamma>\<^sub>q \<gamma>\<^sub>a"
proof-  
  have c_not_empty: "c\<^sub>c \<noteq>[] \<and> (\<forall>i<length c\<^sub>c. final1 (c\<^sub>c!i) \<sigma> )" 
    using a1 unfolding All_End_def by auto
  { 
    assume "\<forall>i<length c\<^sub>c. c\<^sub>c!i = Skip" 
    then have ?thesis 
      using c_not_empty last_skip_ref[OF a0 a0']   last_not_normal_ref[OF a0 a0']            
      unfolding All_End_def final_def final_c_def
      by auto
  } note l =this
  {
    assume "\<not> (\<forall>i<length c\<^sub>c. c\<^sub>c!i = Skip)"     
    then have f:"final_c (c\<^sub>c,\<sigma>)  \<and> (\<exists>i<length c\<^sub>c. c\<^sub>c!i = Throw \<or> c\<^sub>c!i = Stuck \<or> (\<exists>f. c\<^sub>c!i = Fault f))"
      using c_not_empty
      unfolding final_c_def final1_def by fastforce
    {assume "\<exists>i<length c\<^sub>c. c\<^sub>c!i = Stuck \<or> (\<exists>f. c\<^sub>c!i = Fault f)"
      then have "final_error c\<^sub>c" using a1 
        unfolding All_End_def final_error_def finalp_def final1_def by auto
      then have ?thesis 
        using   last_not_normal_ref[OF a0 a0'] a1 
        unfolding final_c_def  All_End_def  by auto
    }
    moreover {assume "\<not>(\<exists>i<length c\<^sub>c. c\<^sub>c!i = Stuck \<or> (\<exists>f. c\<^sub>c!i = Fault f))"
      moreover have "\<exists>i<length c\<^sub>c. c\<^sub>c!i = Throw" using calculation f by auto
      ultimately have "throw_program c\<^sub>c" 
        using a1 unfolding throw_program_def All_End_def final1_def by auto
      then have ?thesis 
        using   last_Throw_ref[OF a0 a0'] a1 
        unfolding final_c_def  All_End_def  by auto
    } ultimately have ?thesis by auto
  }
  thus ?thesis using l by auto
qed  
  

  
  
definition par_comm\<^sub>e :: 
  "(('g,'l)par_state)  rel1 \<times> 
   (('g,'l)par_state set \<times>('g,'l)par_state set) \<Rightarrow>
   'f set \<Rightarrow> 
     (('g,'l,'p,'f,'e) par_confs) set" where
  "par_comm\<^sub>e \<equiv> \<lambda>(guar, (q,a)) F. 
     {c. (\<forall>i e. 
            Suc i<length (snd c) \<longrightarrow> 
            ((fst c)\<turnstile>\<^sub>p\<^sub>e((snd c)!i)  \<rightarrow> ((snd c)!(Suc i))) \<longrightarrow>                        
              (snd((snd c)!i), snd((snd c)!(Suc i))) \<in> guar) \<and> 
                (All_End (last (snd c)) \<longrightarrow>  not_fault (fst (last (snd c)))  F \<longrightarrow> 
                   throw_program (fst (last (snd c))) \<and> snd (last (snd c)) \<in> a \<or>
                   skip_program (fst (last (snd c))) \<and> snd (last (snd c)) \<in> q)}"

lemma par_comm\<^sub>e_par_comm: 
 "(\<Gamma>,xs)\<in> par_comm\<^sub>e (G,q,a) F \<Longrightarrow> (\<Gamma>,xs)\<in> par_comm (G,q,a) F" 
  unfolding par_comm\<^sub>e_def par_comm_def  
  apply auto
  by (metis prod.collapse stepp_steppe)+
  

lemma par_comm_par_comm\<^sub>e: 
 "(\<Gamma>,xs)\<in> par_comm (G,q,a) F \<Longrightarrow> (\<Gamma>,xs)\<in> par_comm\<^sub>e (G,q,a) F" 
  unfolding par_comm\<^sub>e_def par_comm_def  
  apply auto
  by (metis prod.collapse steppe_stepp)+
    
lemma par_comm_eq_par_comm\<^sub>e:
  "par_comm (G,q,a) F = par_comm\<^sub>e (G,q,a) F"
  using par_comm\<^sub>e_par_comm par_comm_par_comm\<^sub>e by auto
  
lemma par_comm_tail: 
  assumes a0:"(\<Gamma>, (p1, t) # (p2,s) # xs) \<in> par_comm\<^sub>e (G\<^sub>s, q\<^sub>s, a\<^sub>s) F" 
  shows "(\<Gamma>, (p2,s) # xs) \<in> par_comm\<^sub>e (G\<^sub>s, q\<^sub>s, a\<^sub>s) F"
  using a0 unfolding par_comm\<^sub>e_def  All_End_def final_def by auto
            

        

definition par_com_validity :: 
  "('g\<times>'l,'p,'f,'e) body \<Rightarrow>  'f set \<Rightarrow>  ('g,'l,'p,'f,'e) par_com \<Rightarrow> 
    ('g,'l)par_state set \<Rightarrow> (('g,'l)par_state) rel1 \<Rightarrow>  (('g,'l)par_state) rel1 \<Rightarrow>  
    ('g,'l)par_state set \<Rightarrow>  ('g,'l)par_state set \<Rightarrow>  bool" 
    ("_ \<Turnstile>\<^sub>e\<^bsub>'/_\<^esub>/ _ SAT [_,_, _, _,_]" [61,60,0,0,0,0,0,0] 45) where
  "\<Gamma> \<Turnstile>\<^sub>e\<^bsub>/F\<^esub> Pr SAT [p, R, G, q,a] \<equiv> 
   \<forall>s. par_cp\<^sub>e \<Gamma> Pr s \<inter> par_assum(p, R) \<subseteq> par_comm\<^sub>e(G, (q,a)) F"
              

lemma SIM_alpha:
assumes   
  a0:"(\<Gamma>,(c\<^sub>c,\<sigma>),R,G) \<succeq>\<^sub>p\<^sub>(\<^sub>\<alpha>\<^sub>;\<^sub>\<gamma>\<^sub>q\<^sub>;\<^sub>\<gamma>\<^sub>a\<^sub>) (\<Gamma>',(c\<^sub>s, \<Sigma>),R',G')"
shows "(\<sigma>,\<Sigma>) \<in> \<alpha>" 
proof -
  show ?thesis using a0 par_sim_elim_cases(1) by blast
qed
 
  
lemma par_comp_step_SIM:
  assumes a0:"\<Gamma>\<^sub>c\<turnstile>\<^sub>p\<^sub>e (c\<^sub>c,\<sigma>)  \<rightarrow> (c\<^sub>c', \<sigma>')" and
  a1: "\<forall>c\<^sub>c' \<sigma>'. (\<Gamma>\<^sub>c\<turnstile>\<^sub>p\<^sub>\<tau> (c\<^sub>c,\<sigma>) \<rightarrow> (c\<^sub>c', \<sigma>')) \<longrightarrow> 
             (\<exists>c\<^sub>s' \<Sigma>'.  \<Gamma>\<^sub>s\<turnstile>\<^sub>p (c\<^sub>s, \<Sigma>) \<rightarrow>\<^sub>\<tau>\<^sup>* (c\<^sub>s', \<Sigma>') \<and>
              (\<sigma>', \<Sigma>')\<in>\<alpha> \<and> 
              (((\<sigma>, \<sigma>'),(\<Sigma>, \<Sigma>')) \<in> (G\<^sub>c,G\<^sub>s\<^sup>*)\<^sub>\<alpha>) \<and>
             (\<Gamma>\<^sub>c,(c\<^sub>c', \<sigma>'),R\<^sub>c,G\<^sub>c) \<succeq>\<^sub>p\<^sub>(\<^sub>\<alpha>\<^sub>;\<^sub>\<gamma>\<^sub>q\<^sub>;\<^sub>\<gamma>\<^sub>a\<^sub>) (\<Gamma>\<^sub>s,(c\<^sub>s', \<Sigma>'),R\<^sub>s,G\<^sub>s))" and
  a2:"\<forall>v c\<^sub>c' \<sigma>'. (\<Gamma>\<^sub>c\<turnstile>\<^sub>p\<^sub>(Some v) (c\<^sub>c, \<sigma>) \<rightarrow> (c\<^sub>c', \<sigma>')) \<longrightarrow> 
             (\<exists> c\<^sub>s' \<Sigma>'. \<Gamma>\<^sub>s\<turnstile>\<^sub>p\<^sub>v (c\<^sub>s, \<Sigma>) \<rightarrow>\<^sup>+  (c\<^sub>s', \<Sigma>') \<and> 
              (\<sigma>', \<Sigma>')\<in>\<alpha> \<and> (((\<sigma>, \<sigma>'),(\<Sigma>, \<Sigma>')) \<in> (G\<^sub>c,G\<^sub>s\<^sup>*)\<^sub>\<alpha>) \<and>  
                (\<Gamma>\<^sub>c,(c\<^sub>c', \<sigma>'),R\<^sub>c,G\<^sub>c) \<succeq>\<^sub>p\<^sub>(\<^sub>\<alpha>\<^sub>;\<^sub>\<gamma>\<^sub>q\<^sub>;\<^sub>\<gamma>\<^sub>a\<^sub>) (\<Gamma>\<^sub>s,(c\<^sub>s', \<Sigma>'),R\<^sub>s,G\<^sub>s))"
shows "\<exists>c\<^sub>s' \<Sigma>'. (\<Gamma>\<^sub>c,(c\<^sub>c', \<sigma>'),R\<^sub>c,G\<^sub>c) \<succeq>\<^sub>p\<^sub>(\<^sub>\<alpha>\<^sub>;\<^sub>\<gamma>\<^sub>q\<^sub>;\<^sub>\<gamma>\<^sub>a\<^sub>) (\<Gamma>\<^sub>s,(c\<^sub>s',\<Sigma>'),R\<^sub>s,G\<^sub>s) \<and> 
                 (\<Gamma>\<^sub>s\<turnstile>\<^sub>p (c\<^sub>s, \<Sigma>) \<rightarrow>\<^sub>\<tau>\<^sup>* (c\<^sub>s', \<Sigma>') \<or> (\<exists>v. e=Some v \<and> \<Gamma>\<^sub>s\<turnstile>\<^sub>p\<^sub>v (c\<^sub>s, \<Sigma>) \<rightarrow>\<^sup>+ (c\<^sub>s', \<Sigma>')))"
proof -  
  have "(\<Gamma>\<^sub>c\<turnstile>\<^sub>p\<^sub>\<tau> (c\<^sub>c,\<sigma>)  \<rightarrow> (c\<^sub>c', \<sigma>')) \<or>  (\<exists>v. e = Some v \<and> \<Gamma>\<^sub>c\<turnstile>\<^sub>p\<^sub>e (c\<^sub>c,\<sigma>)  \<rightarrow> (c\<^sub>c', \<sigma>'))"
    using a0 by auto
  thus ?thesis
  proof    
    assume "\<Gamma>\<^sub>c\<turnstile>\<^sub>p\<^sub>\<tau> (c\<^sub>c, \<sigma>) \<rightarrow> (c\<^sub>c', \<sigma>')"
    thus ?thesis using  a1 by fastforce  
   next
     assume "(\<exists>v. e = Some v \<and> \<Gamma>\<^sub>c\<turnstile>\<^sub>p\<^sub>e (c\<^sub>c, \<sigma>) \<rightarrow> (c\<^sub>c', \<sigma>'))"     
     thus ?thesis using a2 
       by fast
  qed    
qed
 

lemma par_step_guarantee:  
assumes a0:"\<Gamma>\<^sub>c\<turnstile>\<^sub>p\<^sub>e (c\<^sub>c,\<sigma>)  \<rightarrow> (c\<^sub>c', \<sigma>')" and
  a1: "\<forall>c\<^sub>c' \<sigma>'. (\<Gamma>\<^sub>c\<turnstile>\<^sub>p\<^sub>\<tau> (c\<^sub>c,\<sigma>) \<rightarrow> (c\<^sub>c', \<sigma>')) \<longrightarrow> 
             (\<exists>c\<^sub>s' \<Sigma>'.  \<Gamma>\<^sub>s\<turnstile>\<^sub>p (c\<^sub>s, \<Sigma>) \<rightarrow>\<^sub>\<tau>\<^sup>* (c\<^sub>s', \<Sigma>') \<and>
              (\<sigma>', \<Sigma>')\<in>\<alpha> \<and> 
              (((\<sigma>, \<sigma>'),(\<Sigma>, \<Sigma>')) \<in> (G\<^sub>c,G\<^sub>s\<^sup>*)\<^sub>\<alpha>) \<and>
             (\<Gamma>\<^sub>c,(c\<^sub>c', \<sigma>'),R\<^sub>c,G\<^sub>c) \<succeq>\<^sub>p\<^sub>(\<^sub>\<alpha>\<^sub>;\<^sub>\<gamma>\<^sub>q\<^sub>;\<^sub>\<gamma>\<^sub>a\<^sub>) (\<Gamma>\<^sub>s,(c\<^sub>s', \<Sigma>'),R\<^sub>s,G\<^sub>s))" and
  a2:"\<forall>v c\<^sub>c' \<sigma>'. (\<Gamma>\<^sub>c\<turnstile>\<^sub>p\<^sub>(Some v) (c\<^sub>c, \<sigma>) \<rightarrow> (c\<^sub>c', \<sigma>')) \<longrightarrow> 
             (\<exists> c\<^sub>s' \<Sigma>'. \<Gamma>\<^sub>s\<turnstile>\<^sub>p\<^sub>v (c\<^sub>s, \<Sigma>) \<rightarrow>\<^sup>+  (c\<^sub>s', \<Sigma>') \<and> 
              (\<sigma>', \<Sigma>')\<in>\<alpha> \<and> (((\<sigma>, \<sigma>'),(\<Sigma>, \<Sigma>')) \<in> (G\<^sub>c,G\<^sub>s\<^sup>*)\<^sub>\<alpha>) \<and>  
                (\<Gamma>\<^sub>c,(c\<^sub>c', \<sigma>'),R\<^sub>c,G\<^sub>c) \<succeq>\<^sub>p\<^sub>(\<^sub>\<alpha>\<^sub>;\<^sub>\<gamma>\<^sub>q\<^sub>;\<^sub>\<gamma>\<^sub>a\<^sub>) (\<Gamma>\<^sub>s,(c\<^sub>s', \<Sigma>'),R\<^sub>s,G\<^sub>s))"
shows "\<exists>c\<^sub>s' \<Sigma>'. (\<Gamma>\<^sub>s\<turnstile>\<^sub>p (c\<^sub>s, \<Sigma>) \<rightarrow>\<^sub>\<tau>\<^sup>* (c\<^sub>s',\<Sigma>') \<or> (\<exists>v. e=Some v \<and> \<Gamma>\<^sub>s\<turnstile>\<^sub>p\<^sub>v (c\<^sub>s, \<Sigma>) \<rightarrow>\<^sup>+ (c\<^sub>s', \<Sigma>'))) \<and> 
                (\<sigma>',\<Sigma>')\<in>\<alpha> \<and> ((\<sigma>, \<sigma>')\<in>G\<^sub>c)"
proof- 
  have "(\<Gamma>\<^sub>c\<turnstile>\<^sub>p\<^sub>\<tau> (c\<^sub>c,\<sigma>)  \<rightarrow> (c\<^sub>c',\<sigma>')) \<or>  (\<exists>v. e = Some v \<and> \<Gamma>\<^sub>c\<turnstile>\<^sub>p\<^sub>e (c\<^sub>c,\<sigma>)  \<rightarrow> (c\<^sub>c', \<sigma>'))"
    using a0 by auto
  thus ?thesis 
  proof
    assume "\<Gamma>\<^sub>c\<turnstile>\<^sub>p\<^sub>\<tau> (c\<^sub>c, \<sigma>) \<rightarrow> (c\<^sub>c',  \<sigma>')"      
    then show ?thesis using a1 unfolding related_transitions_def by fast
  next
    assume "\<exists>v. e = Some v \<and> \<Gamma>\<^sub>c\<turnstile>\<^sub>p\<^sub>e (c\<^sub>c, \<sigma>) \<rightarrow> (c\<^sub>c', \<sigma>')"    
    then obtain v where a0: "e = Some v \<and> \<Gamma>\<^sub>c\<turnstile>\<^sub>p\<^sub>e (c\<^sub>c, \<sigma>) \<rightarrow> (c\<^sub>c', \<sigma>')" by auto
    then have "\<exists>c\<^sub>s' \<Sigma>'.
               (\<Gamma>\<^sub>s\<turnstile>\<^sub>p\<^sub>v (c\<^sub>s, \<Sigma>) \<rightarrow>\<^sup>+ (c\<^sub>s', \<Sigma>')) \<and>
               (\<sigma>',\<Sigma>')\<in>\<alpha> \<and> 
                (((\<sigma>, \<sigma>'),(\<Sigma>, \<Sigma>')) \<in> (G\<^sub>c,G\<^sub>s\<^sup>*)\<^sub>\<alpha>)" using a2 by fast
    thus ?thesis using a0 unfolding related_transitions_def by blast  
  qed    
qed  

lemma SIM_next_state_normal:
"(\<Gamma>\<^sub>c,(c\<^sub>c,\<sigma>),R\<^sub>c,G\<^sub>c) \<succeq>\<^sub>p\<^sub>(\<^sub>\<alpha>\<^sub>;\<^sub>\<gamma>\<^sub>q\<^sub>;\<^sub>\<gamma>\<^sub>a\<^sub>) (\<Gamma>\<^sub>s,(c\<^sub>s,\<Sigma>),R\<^sub>s,G\<^sub>s) \<Longrightarrow> 
 \<Gamma>\<^sub>c\<turnstile>\<^sub>p\<^sub>e (c\<^sub>c,\<sigma>)  \<rightarrow> (c\<^sub>c', \<sigma>') \<Longrightarrow>
 \<exists>c\<^sub>s' \<Sigma>'. (\<Gamma>\<^sub>s\<turnstile>\<^sub>p (c\<^sub>s, \<Sigma>) \<rightarrow>\<^sub>\<tau>\<^sup>* (c\<^sub>s', \<Sigma>') \<or> (\<exists>v. e=Some v \<and> \<Gamma>\<^sub>s\<turnstile>\<^sub>p\<^sub>v (c\<^sub>s, \<Sigma>) \<rightarrow>\<^sup>+ (c\<^sub>s', \<Sigma>'))) \<and> 
                (\<sigma>',\<Sigma>')\<in>\<alpha> \<and> ((\<sigma>, \<sigma>')\<in>G\<^sub>c)"
  apply (erule par_sim_elim_cases, frule par_step_guarantee)
  by (cases \<sigma>', auto)


lemma SIM_guarantee_normal1:  
 "(\<Gamma>\<^sub>c,(c\<^sub>c,\<sigma>),R\<^sub>c,G\<^sub>c) \<succeq>\<^sub>p\<^sub>(\<^sub>\<alpha>\<^sub>;\<^sub>\<gamma>\<^sub>q\<^sub>;\<^sub>\<gamma>\<^sub>a\<^sub>) (\<Gamma>\<^sub>s,(c\<^sub>s,\<Sigma>),R\<^sub>s,G\<^sub>s) \<Longrightarrow> 
 \<Gamma>\<^sub>c\<turnstile>\<^sub>p\<^sub>e (c\<^sub>c,\<sigma>)  \<rightarrow> (c\<^sub>c', \<sigma>') \<Longrightarrow>
 \<exists>c\<^sub>s' \<Sigma>'. (\<Gamma>\<^sub>c,(c\<^sub>c', \<sigma>'),R\<^sub>c,G\<^sub>c) \<succeq>\<^sub>p\<^sub>(\<^sub>\<alpha>\<^sub>;\<^sub>\<gamma>\<^sub>q\<^sub>;\<^sub>\<gamma>\<^sub>a\<^sub>) (\<Gamma>\<^sub>s,(c\<^sub>s', \<Sigma>'),R\<^sub>s,G\<^sub>s) \<and>
     (\<Gamma>\<^sub>s\<turnstile>\<^sub>p (c\<^sub>s, \<Sigma>) \<rightarrow>\<^sub>\<tau>\<^sup>* (c\<^sub>s', \<Sigma>') \<or> (\<exists>v. e=Some v \<and> \<Gamma>\<^sub>s\<turnstile>\<^sub>p\<^sub>v (c\<^sub>s, \<Sigma>) \<rightarrow>\<^sup>+ (c\<^sub>s', \<Sigma>')))"    
  by (erule par_sim_elim_cases, drule par_comp_step_SIM, auto)
    
lemma SIM_guarantee_normal:
assumes  
 a0:"(\<Gamma>\<^sub>c,(c\<^sub>c,\<sigma>),R\<^sub>c,G\<^sub>c) \<succeq>\<^sub>p\<^sub>(\<^sub>\<alpha>\<^sub>;\<^sub>\<gamma>\<^sub>q\<^sub>;\<^sub>\<gamma>\<^sub>a\<^sub>) (\<Gamma>\<^sub>s,(c\<^sub>s,\<Sigma>),R\<^sub>s,G\<^sub>s)" and a0':"wf_conf c\<^sub>s \<Sigma>" and
 a1:"\<Gamma>\<^sub>c\<turnstile>\<^sub>p\<^sub>e (c\<^sub>c,\<sigma>)  \<rightarrow> (c\<^sub>c', \<sigma>')"
shows "\<exists>c\<^sub>s' \<Sigma>' l. (\<Gamma>\<^sub>c,(c\<^sub>c', \<sigma>'),R\<^sub>c,G\<^sub>c) \<succeq>\<^sub>p\<^sub>(\<^sub>\<alpha>\<^sub>;\<^sub>\<gamma>\<^sub>q\<^sub>;\<^sub>\<gamma>\<^sub>a\<^sub>) (\<Gamma>\<^sub>s,(c\<^sub>s', \<Sigma>'),R\<^sub>s,G\<^sub>s) \<and>
                  (\<forall>i. Suc i<length l \<longrightarrow> 
                       \<Gamma>\<^sub>s\<turnstile>\<^sub>p(l!i)  \<rightarrow>\<^sub>e (l!(Suc i)) \<longrightarrow>        
                       (snd(l!i), snd(l!(Suc i))) \<in> R\<^sub>s) \<and>
                  (\<Gamma>\<^sub>s,l) \<in>par_cp\<^sub>e \<Gamma>\<^sub>s c\<^sub>s \<Sigma> \<and> last l = (c\<^sub>s',  \<Sigma>')"
proof-         
  obtain c\<^sub>s' \<Sigma>' where c1:"(\<Gamma>\<^sub>c,(c\<^sub>c', \<sigma>'),R\<^sub>c,G\<^sub>c) \<succeq>\<^sub>p\<^sub>(\<^sub>\<alpha>\<^sub>;\<^sub>\<gamma>\<^sub>q\<^sub>;\<^sub>\<gamma>\<^sub>a\<^sub>) (\<Gamma>\<^sub>s,(c\<^sub>s', \<Sigma>'),R\<^sub>s,G\<^sub>s)" and 
                 "(\<Gamma>\<^sub>s\<turnstile>\<^sub>p (c\<^sub>s, \<Sigma>) \<rightarrow>\<^sub>\<tau>\<^sup>* (c\<^sub>s',  \<Sigma>') \<or> (\<exists>v. e=Some v \<and> \<Gamma>\<^sub>s\<turnstile>\<^sub>p\<^sub>v (c\<^sub>s, \<Sigma>) \<rightarrow>\<^sup>+ (c\<^sub>s', \<Sigma>')))"   
    using  SIM_guarantee_normal1[OF a0 a1] by blast 
  thus ?thesis using  
    tau_tran_closure_cptn1[of \<Gamma>\<^sub>s c\<^sub>s \<Sigma> c\<^sub>s' "\<Sigma>'", OF _ a0']
    evnt_tran_closure_cptn1[of \<Gamma>\<^sub>s c\<^sub>s \<Sigma> _ c\<^sub>s' "\<Sigma>'", OF _ a0'] by blast
qed 

lemma SIM_guarantee:
assumes  
 a0:"(\<Gamma>\<^sub>c,(c\<^sub>c,\<sigma>),R\<^sub>c,G\<^sub>c) \<succeq>\<^sub>p\<^sub>(\<^sub>\<alpha>\<^sub>;\<^sub>\<gamma>\<^sub>q\<^sub>;\<^sub>\<gamma>\<^sub>a\<^sub>) (\<Gamma>\<^sub>s,(c\<^sub>s,\<Sigma>),R\<^sub>s,G\<^sub>s)" and a0':"wf_conf c\<^sub>s \<Sigma>" and
 a1:"\<Gamma>\<^sub>c\<turnstile>\<^sub>p\<^sub>e (c\<^sub>c,\<sigma>)  \<rightarrow> (c\<^sub>c', \<sigma>')"
shows "\<exists>c\<^sub>s' \<Sigma>' l. (\<Gamma>\<^sub>c,(c\<^sub>c', \<sigma>'),R\<^sub>c,G\<^sub>c) \<succeq>\<^sub>p\<^sub>(\<^sub>\<alpha>\<^sub>;\<^sub>\<gamma>\<^sub>q\<^sub>;\<^sub>\<gamma>\<^sub>a\<^sub>) (\<Gamma>\<^sub>s,(c\<^sub>s', \<Sigma>'),R\<^sub>s,G\<^sub>s) \<and>
                  (\<forall>i. Suc i<length l \<longrightarrow> 
                       \<Gamma>\<^sub>s\<turnstile>\<^sub>p(l!i)  \<rightarrow>\<^sub>e (l!(Suc i)) \<longrightarrow>        
                       (snd(l!i), snd(l!(Suc i))) \<in> R\<^sub>s) \<and>
                  (\<Gamma>\<^sub>s,l) \<in>par_cp\<^sub>e \<Gamma>\<^sub>s c\<^sub>s \<Sigma> \<and> last l = (c\<^sub>s', \<Sigma>')"
  using a1 SIM_guarantee_normal[OF a0 a0']
  by (cases \<sigma>', fastforce)


lemma SIM_next_state:
  assumes 
a0:"(\<Gamma>\<^sub>c,(c\<^sub>c,\<sigma>),R\<^sub>c,G\<^sub>c) \<succeq>\<^sub>p\<^sub>(\<^sub>\<alpha>\<^sub>;\<^sub>\<gamma>\<^sub>q\<^sub>;\<^sub>\<gamma>\<^sub>a\<^sub>) (\<Gamma>\<^sub>s,(c\<^sub>s,\<Sigma>),R\<^sub>s,G\<^sub>s)" and
a1:"\<Gamma>\<^sub>c\<turnstile>\<^sub>p\<^sub>e (c\<^sub>c,\<sigma>)  \<rightarrow> (c\<^sub>c', \<sigma>')" 
shows  "\<exists>c\<^sub>s' \<Sigma>'. (\<Gamma>\<^sub>s\<turnstile>\<^sub>p (c\<^sub>s, \<Sigma>) \<rightarrow>\<^sub>\<tau>\<^sup>* (c\<^sub>s', \<Sigma>') \<or> (\<exists>v. e=Some v \<and> \<Gamma>\<^sub>s\<turnstile>\<^sub>p\<^sub>v (c\<^sub>s, \<Sigma>) \<rightarrow>\<^sup>+ (c\<^sub>s',\<Sigma>')))
                 \<and> (\<sigma>',\<Sigma>')\<in>\<alpha> \<and> ((\<sigma>,\<sigma>')\<in>G\<^sub>c)"
 using SIM_next_state_normal[OF a0]   a1  by blast              


definition in_rel :: "'b rel1 \<Rightarrow> ('a, 'b) rel \<Rightarrow> 'a rel1"
  where "in_rel r \<alpha> = {(\<sigma>, \<sigma>'). (\<forall>\<Sigma>. (\<sigma>, \<Sigma>)\<in>\<alpha> \<longrightarrow> (\<exists>\<Sigma>'.  (\<sigma>',\<Sigma>')\<in>\<alpha> \<and> (\<Sigma>, \<Sigma>')\<in>r))}"


lemma R_eq_locals_tran:assumes a0:"R\<^sub>s \<subseteq> R_eq_locals" shows "R\<^sub>s\<^sup>* \<subseteq> R_eq_locals"  
  apply auto 
  subgoal for a b a' b'
    apply(induct rule: converse_rtrancl_induct, auto)    
    using a0 unfolding R_eq_locals_def by auto
  done 

lemma SIM_env:  
  assumes 
  a0:"(\<Gamma>\<^sub>c,(c\<^sub>c,\<sigma>),R\<^sub>c,G\<^sub>c) \<succeq>\<^sub>p\<^sub>(\<^sub>\<alpha>\<^sub>;\<^sub>\<gamma>\<^sub>q\<^sub>;\<^sub>\<gamma>\<^sub>a\<^sub>) (\<Gamma>\<^sub>s,(c\<^sub>s,\<Sigma>),R\<^sub>s,G\<^sub>s)" and 
  a0':"wf_conf c\<^sub>s \<Sigma>" and a0'':"R\<^sub>s \<subseteq> R_eq_locals" and
  a1:"(\<sigma>,\<sigma>') \<in> R\<^sub>c" and a1':"R\<^sub>c \<subseteq>  in_rel (R\<^sub>s\<^sup>*) \<alpha>" and
  a2:"\<Gamma>\<turnstile>\<^sub>p (c\<^sub>c, \<sigma>) \<rightarrow>\<^sub>e (c'\<^sub>c, \<sigma>')"
shows "\<exists>\<Sigma>' l\<^sub>s. (\<Gamma>\<^sub>c,(c\<^sub>c,\<sigma>'),R\<^sub>c,G\<^sub>c) \<succeq>\<^sub>p\<^sub>(\<^sub>\<alpha>\<^sub>;\<^sub>\<gamma>\<^sub>q\<^sub>;\<^sub>\<gamma>\<^sub>a\<^sub>) (\<Gamma>\<^sub>s,(c\<^sub>s,\<Sigma>'),R\<^sub>s,G\<^sub>s) \<and> 
           (\<Gamma>\<^sub>s,l\<^sub>s) \<in>par_cp\<^sub>e \<Gamma>\<^sub>s c\<^sub>s \<Sigma> \<and> last l\<^sub>s = (c\<^sub>s,\<Sigma>') "
proof- 
  have "(\<Gamma>\<^sub>s,[(c\<^sub>s,\<Sigma>)]) \<in>par_cp\<^sub>e \<Gamma>\<^sub>s c\<^sub>s \<Sigma>"     
    unfolding par_cp\<^sub>e_def  using a0' par_cptn\<^sub>e.intros
    by (simp add: par_cptn\<^sub>e.ParCptnOne)
  then have eq_pr:"c\<^sub>c = c'\<^sub>c"
    using a2 env_pe_c_c' by blast
  moreover have  \<sigma>n:"snd \<sigma>= snd \<sigma>'" 
    using step_pe_elim_cases[OF a2]
    by (metis snd_conv)
  then have \<Sigma>n:"(\<sigma>,\<Sigma>)\<in>\<alpha>" using a0
    using dest_SIM_alpha by blast 
  moreover obtain \<Sigma>' where step_R:"(\<sigma>', \<Sigma>') \<in> \<alpha> \<and> (\<Sigma>, \<Sigma>') \<in> R\<^sub>s\<^sup>* "
    using \<sigma>n a1' a1 \<Sigma>n a0'' unfolding in_rel_def R_eq_locals_def  by blast  
  then have "(\<Gamma>\<^sub>c,(c\<^sub>c,\<sigma>'),R\<^sub>c,G\<^sub>c) \<succeq>\<^sub>p\<^sub>(\<^sub>\<alpha>\<^sub>;\<^sub>\<gamma>\<^sub>q\<^sub>;\<^sub>\<gamma>\<^sub>a\<^sub>) (\<Gamma>\<^sub>s,(c\<^sub>s,\<Sigma>'),R\<^sub>s,G\<^sub>s)" 
    using \<sigma>n \<Sigma>n a1 a0 dest_SIM_env_step[OF a0] unfolding related_transitions_def  
    by blast
  moreover have "\<exists>l\<^sub>s. (\<Gamma>\<^sub>s,l\<^sub>s) \<in>par_cp\<^sub>e \<Gamma>\<^sub>s c\<^sub>s \<Sigma> \<and> last l\<^sub>s = (c\<^sub>s, \<Sigma>')"    
  proof-
    have "snd \<Sigma> = snd \<Sigma>'"using  step_R R_eq_locals_tran[OF a0'']
      unfolding R_eq_locals_def by fastforce  
    then have x: "\<Gamma>\<^sub>s\<turnstile>\<^sub>p (c\<^sub>s,  \<Sigma>) \<rightarrow>\<^sub>e\<^sup>* (c\<^sub>s,  \<Sigma>')"
      using ParEnv
      by (metis prod.exhaust_sel r_into_rtranclp)
    then show ?thesis using tau_tran_env_closure_cptn[OF x] \<Sigma>n a0' by auto
  qed
  ultimately show ?thesis using a1 a0 
    unfolding related_transitions_def Id_def par_cp\<^sub>e_def by fastforce
qed

lemma SIM_env1:  
  assumes 
  a0:"(\<Gamma>\<^sub>c,(c\<^sub>c,\<sigma>),R\<^sub>c,G\<^sub>c) \<succeq>\<^sub>p\<^sub>(\<^sub>\<alpha>\<^sub>;\<^sub>\<gamma>\<^sub>q\<^sub>;\<^sub>\<gamma>\<^sub>a\<^sub>) (\<Gamma>\<^sub>s,(c\<^sub>s,\<Sigma>),R\<^sub>s,G\<^sub>s)" and 
  a0':"wf_conf c\<^sub>s \<Sigma>" and a0'':"R\<^sub>s \<subseteq> R_eq_locals" and
  a1:"(\<sigma>,\<sigma>') \<in> R\<^sub>c" and a1':"R\<^sub>c \<subseteq>  in_rel (R\<^sub>s\<^sup>*) \<alpha>" and
  a2:"\<Gamma>\<turnstile>\<^sub>p (c\<^sub>c, \<sigma>) \<rightarrow>\<^sub>e (c'\<^sub>c, \<sigma>')" and a3:"\<forall>\<Sigma>. (\<Sigma>,\<Sigma>)\<in>R\<^sub>s"
shows "\<exists>\<Sigma>' l\<^sub>s. (\<Gamma>\<^sub>c,(c\<^sub>c,\<sigma>'),R\<^sub>c,G\<^sub>c) \<succeq>\<^sub>p\<^sub>(\<^sub>\<alpha>\<^sub>;\<^sub>\<gamma>\<^sub>q\<^sub>;\<^sub>\<gamma>\<^sub>a\<^sub>) (\<Gamma>\<^sub>s,(c\<^sub>s,\<Sigma>'),R\<^sub>s,G\<^sub>s) \<and>
               (\<forall>i. Suc i<length l\<^sub>s \<longrightarrow> 
                 \<Gamma>\<^sub>s\<turnstile>\<^sub>p(l\<^sub>s!i)  \<rightarrow>\<^sub>e (l\<^sub>s!(Suc i)) \<longrightarrow>        
                 (snd(l\<^sub>s!i), snd(l\<^sub>s!(Suc i))) \<in> R\<^sub>s) \<and> 
               (\<Gamma>\<^sub>s,l\<^sub>s) \<in>par_cp\<^sub>e \<Gamma>\<^sub>s c\<^sub>s \<Sigma> \<and> last l\<^sub>s = (c\<^sub>s,\<Sigma>') "
proof- 
 
  have "(\<Gamma>\<^sub>s,[(c\<^sub>s,\<Sigma>)]) \<in>par_cp\<^sub>e \<Gamma>\<^sub>s c\<^sub>s \<Sigma>" 
    unfolding par_cp\<^sub>e_def  using a0' par_cptn\<^sub>e.intros  
    by (simp add: par_cptn\<^sub>e.ParCptnOne)
  then have eq_pr:"c\<^sub>c = c'\<^sub>c"
    using a2 env_pe_c_c' by blast  
  then have \<Sigma>n:"(\<sigma>, \<Sigma>)\<in>\<alpha>" using a0
    using dest_SIM_alpha by blast 
  moreover obtain \<Sigma>' where "(\<sigma>', \<Sigma>') \<in> \<alpha>" and \<Sigma>:"(\<Sigma>, \<Sigma>') \<in> R\<^sub>s\<^sup>*"
  using a1' a1 \<Sigma>n unfolding in_rel_def by fast
  then have "(\<Gamma>\<^sub>c,(c\<^sub>c,\<sigma>'),R\<^sub>c,G\<^sub>c) \<succeq>\<^sub>p\<^sub>(\<^sub>\<alpha>\<^sub>;\<^sub>\<gamma>\<^sub>q\<^sub>;\<^sub>\<gamma>\<^sub>a\<^sub>) (\<Gamma>\<^sub>s,(c\<^sub>s, \<Sigma>'),R\<^sub>s,G\<^sub>s)" 
    using  \<Sigma>n a1 a0 dest_SIM_env_step[OF a0] 
    unfolding related_transitions_def  by fast
  moreover have "\<exists>l\<^sub>s. (\<Gamma>\<^sub>s,l\<^sub>s) \<in>par_cp\<^sub>e \<Gamma>\<^sub>s c\<^sub>s \<Sigma> \<and> last l\<^sub>s = (c\<^sub>s, \<Sigma>')"    
  proof-
    have "snd \<Sigma> = snd \<Sigma>'" 
      using  \<Sigma> R_eq_locals_tran[OF a0''] unfolding R_eq_locals_def
      by fastforce
    then have x: "\<Gamma>\<^sub>s\<turnstile>\<^sub>p (c\<^sub>s,  \<Sigma>) \<rightarrow>\<^sub>e\<^sup>* (c\<^sub>s,  \<Sigma>')"
      using ParEnv
      by (metis prod.exhaust_sel r_into_rtranclp)
    then show ?thesis using tau_tran_env_closure_cptn[OF x] \<Sigma>n a0' by blast
  qed
  ultimately  show ?thesis using a1 a0 a0' a0'' R_cptn[OF a3  _ \<Sigma>] 
    unfolding related_transitions_def Id_def par_cp\<^sub>e_def by blast
qed    
  

  
lemma cptn_e:
  assumes a0:"(\<Gamma>, l') \<in> par_cp\<^sub>e \<Gamma> c' s'" and
          a1:"(\<Gamma>, l) \<in> par_cp\<^sub>e \<Gamma> c s \<and> last l = (c', s')"
        shows "(\<Gamma>, (take ((length l) -1) l) @ l') \<in> par_cp\<^sub>e \<Gamma> c s"
  using a0 a1 par_cp\<^sub>e_app1
  by (metis (no_types, lifting) diff_less last_conv_nth 
    length_Cons length_greater_0_conv less_Suc_eq_0_disj less_numeral_extra(1) par_cp_l_dest) 
  
lemma RG_SIM_cp_all_sim:
  assumes            
   a0:"(\<Gamma>\<^sub>c,l\<^sub>c)\<in> par_cp\<^sub>e \<Gamma> c\<^sub>c s\<^sub>c \<and> 
       (\<forall>i. Suc i<length l\<^sub>c \<longrightarrow> 
            \<Gamma>\<^sub>c\<turnstile>\<^sub>p(l\<^sub>c!i)  \<rightarrow>\<^sub>e (l\<^sub>c!(Suc i)) \<longrightarrow>        
            (snd(l\<^sub>c!i), snd(l\<^sub>c!(Suc i))) \<in> R\<^sub>c)" and  a0'':"R\<^sub>s \<subseteq> R_eq_locals" and
   a0':"wf_conf c\<^sub>s s\<^sub>s" and a1':"R\<^sub>c \<subseteq>  in_rel (R\<^sub>s\<^sup>*) \<alpha>" and
   a1:"(\<Gamma>\<^sub>c,(c\<^sub>c,s\<^sub>c),R\<^sub>c,G\<^sub>c) \<succeq>\<^sub>p\<^sub>(\<^sub>\<alpha>\<^sub>;\<^sub>\<gamma>\<^sub>q\<^sub>;\<^sub>\<gamma>\<^sub>a\<^sub>) (\<Gamma>\<^sub>s,(c\<^sub>s,s\<^sub>s),R\<^sub>s,G\<^sub>s)" 
 shows "\<forall>i. i<length l\<^sub>c \<longrightarrow> (\<exists>c'\<^sub>s s'\<^sub>s. (\<Gamma>\<^sub>c,l\<^sub>c !i ,R\<^sub>c,G\<^sub>c) \<succeq>\<^sub>p\<^sub>(\<^sub>\<alpha>\<^sub>;\<^sub>\<gamma>\<^sub>q\<^sub>;\<^sub>\<gamma>\<^sub>a\<^sub>) (\<Gamma>\<^sub>s,(c'\<^sub>s,s'\<^sub>s),R\<^sub>s,G\<^sub>s))"   
proof -  
   {fix i
    assume a00:"i < length l\<^sub>c" 
    have "(\<Gamma>\<^sub>c,l\<^sub>c)\<in> par_cp\<^sub>e \<Gamma> c\<^sub>c s\<^sub>c \<and>(\<forall>i. Suc i<length l\<^sub>c \<longrightarrow> 
         \<Gamma>\<^sub>c\<turnstile>\<^sub>p(l\<^sub>c!i)  \<rightarrow>\<^sub>e (l\<^sub>c!(Suc i)) \<longrightarrow>        
         (snd(l\<^sub>c!i), snd(l\<^sub>c!(Suc i))) \<in> R\<^sub>c)" using a0 unfolding par_assum_def by auto
    then have "(\<exists>c'\<^sub>s s'\<^sub>s. (\<Gamma>\<^sub>c,l\<^sub>c !i ,R\<^sub>c,G\<^sub>c) \<succeq>\<^sub>p\<^sub>(\<^sub>\<alpha>\<^sub>;\<^sub>\<gamma>\<^sub>q\<^sub>;\<^sub>\<gamma>\<^sub>a\<^sub>) (\<Gamma>\<^sub>s,(c'\<^sub>s,s'\<^sub>s),R\<^sub>s,G\<^sub>s))" using a00 a1 a0'
    proof (induct i arbitrary: l\<^sub>c c\<^sub>c s\<^sub>c c\<^sub>s s\<^sub>s)
      case 0 thus ?case unfolding par_cp\<^sub>e_def by fastforce
    next
      case (Suc i)
      then have l_gt1:"length l\<^sub>c\<ge>1" by auto
      {assume "length l\<^sub>c = 1"
       then have ?case using l_gt1 Suc Suc par_cp\<^sub>e_def by force
      } note l1= this
      { 
      assume l_g1:"length l\<^sub>c>1"
      then have lcptn:"l\<^sub>c!0 = (c\<^sub>c,s\<^sub>c) \<and> (\<Gamma>\<^sub>c,l\<^sub>c) \<in> par_cptn\<^sub>e" and wconf:" wf_conf c\<^sub>c s\<^sub>c" 
        using Suc unfolding par_cp\<^sub>e_def by auto
      have "\<exists> c'\<^sub>c s'\<^sub>c lh\<^sub>c. l\<^sub>c = (c\<^sub>c,s\<^sub>c)#(c'\<^sub>c,s'\<^sub>c)#lh\<^sub>c"
      proof -
        obtain a1 a2 lh\<^sub>c where "l\<^sub>c = a1#a2#lh\<^sub>c"using Suc l_g1
          by (metis One_nat_def length_0_conv length_Cons less_not_refl not_less0 remdups_adj.cases)        
        also then have "a1 = (c\<^sub>c,s\<^sub>c)" using Suc(2) unfolding par_cp\<^sub>e_def by auto
        ultimately show ?thesis using prod.exhaust_sel by blast
      qed 
      then obtain c'\<^sub>c s'\<^sub>c lh\<^sub>c where l:"l\<^sub>c = (c\<^sub>c,s\<^sub>c)#(c'\<^sub>c,s'\<^sub>c)#lh\<^sub>c" by auto
      let ?l'="(c'\<^sub>c,s'\<^sub>c)#lh\<^sub>c"
      obtain e where step:"\<Gamma>\<^sub>c\<turnstile>\<^sub>p\<^sub>e (c\<^sub>c, s\<^sub>c) \<rightarrow> (c'\<^sub>c, s'\<^sub>c) \<or> \<Gamma>\<^sub>c\<turnstile>\<^sub>p (c\<^sub>c, s\<^sub>c) \<rightarrow>\<^sub>e (c'\<^sub>c, s'\<^sub>c)" 
        using l lcptn par_cptn_step[of \<Gamma>\<^sub>c c\<^sub>c s\<^sub>c c'\<^sub>c s'\<^sub>c lh\<^sub>c] by fastforce  
      then have "wf_conf c'\<^sub>c s'\<^sub>c" using lcptn wf_conf_par_step  l wconf
        using wf_conf_env_step by blast 
      then have "(\<Gamma>\<^sub>c,?l')\<in> par_cp\<^sub>e \<Gamma> c'\<^sub>c s'\<^sub>c" using Suc(2) l unfolding par_cp\<^sub>e_def
        using par_cptn_e_elim_cases(2)[of \<Gamma>\<^sub>c c\<^sub>c s\<^sub>c c'\<^sub>c s'\<^sub>c lh\<^sub>c]  by auto 
      moreover have "(\<forall>i. Suc i<length ?l' \<longrightarrow>
                          \<Gamma>\<^sub>c\<turnstile>\<^sub>p(?l'!i)  \<rightarrow>\<^sub>e (?l'!(Suc i)) \<longrightarrow>        
                          (snd(?l'!i), snd(?l'!(Suc i))) \<in> R\<^sub>c)" 
        using Suc(2) l by fastforce      
      moreover have "i < length ((c'\<^sub>c,s'\<^sub>c)#lh\<^sub>c)" using Suc l by auto
      moreover obtain c'\<^sub>s s'\<^sub>s ls where "(\<Gamma>\<^sub>c,(c'\<^sub>c, s'\<^sub>c),R\<^sub>c,G\<^sub>c) \<succeq>\<^sub>p\<^sub>(\<^sub>\<alpha>\<^sub>;\<^sub>\<gamma>\<^sub>q\<^sub>;\<^sub>\<gamma>\<^sub>a\<^sub>) (\<Gamma>\<^sub>s,(c'\<^sub>s,s'\<^sub>s),R\<^sub>s,G\<^sub>s)" and
           par_cps:"(\<Gamma>\<^sub>s, ls) \<in> par_cp\<^sub>e \<Gamma>\<^sub>s c\<^sub>s s\<^sub>s" and last:"last ls = (c'\<^sub>s, s'\<^sub>s)"
        using step SIM_env[OF Suc(4) Suc(5)]  SIM_guarantee[OF Suc(4) Suc(5)] a1' l lcptn  a0''
        by (metis One_nat_def Suc.prems(1) l_g1 nth_Cons_0 nth_Cons_Suc snd_conv step_pe_elim_cases)           
      moreover have "wf_conf c'\<^sub>s s'\<^sub>s" using wf_conf_par_cp_last[OF par_cps] using last
        by (metis fst_conv snd_conv wf_conf.elims(3))      
      ultimately have ?case using Suc.hyps l by auto        
    } thus ?case using l1 l_gt1 by fastforce
    qed 
  } thus ?thesis by auto
qed    
  
  
lemma RG_SIM_cp_all_sim_l\<^sub>s:    
assumes    
 a0:"(\<Gamma>\<^sub>c,l\<^sub>c)\<in> par_cp\<^sub>e \<Gamma>\<^sub>c c\<^sub>c s\<^sub>c \<and> 
     (\<forall>i. Suc i<length l\<^sub>c \<longrightarrow> 
          \<Gamma>\<^sub>c\<turnstile>\<^sub>p(l\<^sub>c!i)  \<rightarrow>\<^sub>e (l\<^sub>c!(Suc i)) \<longrightarrow>        
          (snd(l\<^sub>c!i), snd(l\<^sub>c!(Suc i))) \<in> R\<^sub>c)" and  a0'':"R\<^sub>s \<subseteq> R_eq_locals" and
   a0':"wf_conf c\<^sub>s s\<^sub>s" and
 a2:"R\<^sub>c \<subseteq>  in_rel (R\<^sub>s\<^sup>*) \<alpha>" and a3:"\<forall>\<Sigma>. (\<Sigma>,\<Sigma>)\<in>R\<^sub>s" and
 a4:"(\<Gamma>\<^sub>c,(c\<^sub>c,s\<^sub>c),R\<^sub>c,G\<^sub>c) \<succeq>\<^sub>p\<^sub>(\<^sub>\<alpha>\<^sub>;\<^sub>\<gamma>\<^sub>q\<^sub>;\<^sub>\<gamma>\<^sub>a\<^sub>) (\<Gamma>\<^sub>s,(c\<^sub>s,s\<^sub>s),R\<^sub>s,G\<^sub>s)" 
shows "\<exists>l\<^sub>s. (\<Gamma>\<^sub>s,l\<^sub>s)\<in> par_cp\<^sub>e \<Gamma>\<^sub>s c\<^sub>s s\<^sub>s \<and>
            (\<forall>i. Suc i<length l\<^sub>s \<longrightarrow> 
                 \<Gamma>\<^sub>s\<turnstile>\<^sub>p(l\<^sub>s!i)  \<rightarrow>\<^sub>e (l\<^sub>s!(Suc i)) \<longrightarrow>        
                 (snd(l\<^sub>s!i), snd(l\<^sub>s!(Suc i))) \<in> R\<^sub>s) \<and> 
             (\<forall>i<length l\<^sub>c. (\<exists>i\<^sub>s<length l\<^sub>s. 
               (\<Gamma>\<^sub>c,l\<^sub>c !i ,R\<^sub>c,G\<^sub>c) \<succeq>\<^sub>p\<^sub>(\<^sub>\<alpha>\<^sub>;\<^sub>\<gamma>\<^sub>q\<^sub>;\<^sub>\<gamma>\<^sub>a\<^sub>) (\<Gamma>\<^sub>s,l\<^sub>s!i\<^sub>s,R\<^sub>s,G\<^sub>s) ))"   
 using a0 a4 a0'
 proof (induct l\<^sub>c arbitrary: c\<^sub>c s\<^sub>c c\<^sub>s s\<^sub>s)  
   case Nil thus ?case unfolding par_cp\<^sub>e_def using par_cptn\<^sub>e.simps
     by fastforce       
 next         
   case (Cons l l\<^sub>c)
   then have lc:"l = (c\<^sub>c,s\<^sub>c)" unfolding par_cp\<^sub>e_def using par_cptn\<^sub>e.simps by auto
   {
     assume l:"l\<^sub>c = Nil" 
      then have "(\<Gamma>\<^sub>c,l ,R\<^sub>c,G\<^sub>c) \<succeq>\<^sub>p\<^sub>(\<^sub>\<alpha>\<^sub>;\<^sub>\<gamma>\<^sub>q\<^sub>;\<^sub>\<gamma>\<^sub>a\<^sub>) (\<Gamma>\<^sub>s,(c\<^sub>s,s\<^sub>s), R\<^sub>s,G\<^sub>s)" 
        using Cons(2,3)  unfolding par_cp\<^sub>e_def by auto
      also have "(\<Gamma>\<^sub>s,[(c\<^sub>s,s\<^sub>s)])\<in> par_cp\<^sub>e \<Gamma>\<^sub>s c\<^sub>s s\<^sub>s"  using Cons.prems(3)  unfolding par_cp\<^sub>e_def
        by (simp add: par_cptn\<^sub>e.ParCptnOne) 
      ultimately have ?case using l by auto      
    }note l1 = this
    { fix c'\<^sub>c s'\<^sub>c lh\<^sub>c
      assume l:"l\<^sub>c = (c'\<^sub>c,s'\<^sub>c)#lh\<^sub>c"
      then have lcptn:"((c\<^sub>c,s\<^sub>c)#(c'\<^sub>c,s'\<^sub>c)#lh\<^sub>c)!0 = (c\<^sub>c,s\<^sub>c) \<and> (\<Gamma>\<^sub>c,(c\<^sub>c,s\<^sub>c)#(c'\<^sub>c,s'\<^sub>c)#lh\<^sub>c)\<in>par_cptn\<^sub>e" 
        using Cons l unfolding par_cp\<^sub>e_def by auto
      then obtain e where tran_c:"(\<Gamma>\<^sub>c\<turnstile>\<^sub>p\<^sub>e (c\<^sub>c,s\<^sub>c)  \<rightarrow> (c'\<^sub>c,s'\<^sub>c)) \<or> 
                                   \<Gamma>\<^sub>c\<turnstile>\<^sub>p (c\<^sub>c,s\<^sub>c) \<rightarrow>\<^sub>e (c'\<^sub>c,s'\<^sub>c)"
        using par_cptn_e_elim_cases(2) by blast   
      moreover have  "wf_conf c'\<^sub>c s'\<^sub>c" 
        using Cons.prems(1) l
        by (metis (no_types, lifting) Product_Type.Collect_case_prodD par_cp\<^sub>e_def 
             tran_c wf_conf_env_step wf_conf_par_step) 
      ultimately have "(\<Gamma>\<^sub>c,(c'\<^sub>c,s'\<^sub>c)#lh\<^sub>c)\<in> par_cp\<^sub>e \<Gamma>\<^sub>c c'\<^sub>c s'\<^sub>c" 
        using Cons(2) par_cptn_e_elim_cases(2)[of \<Gamma>\<^sub>c c\<^sub>c s\<^sub>c c'\<^sub>c s'\<^sub>c lh\<^sub>c]              
              case_prodI lcptn   
        unfolding par_cp\<^sub>e_def by auto
      moreover have "(\<forall>i. Suc i<length l\<^sub>c \<longrightarrow> 
                      \<Gamma>\<^sub>c\<turnstile>\<^sub>p(l\<^sub>c!i)  \<rightarrow>\<^sub>e (l\<^sub>c!(Suc i)) \<longrightarrow>        
                      (snd(l\<^sub>c!i), snd(l\<^sub>c!(Suc i))) \<in> R\<^sub>c)"
        using Cons(2) by auto        
      moreover have "\<exists> c'\<^sub>s s'\<^sub>s l\<^sub>s. (\<Gamma>\<^sub>c,(c'\<^sub>c, s'\<^sub>c),R\<^sub>c,G\<^sub>c) \<succeq>\<^sub>p\<^sub>(\<^sub>\<alpha>\<^sub>;\<^sub>\<gamma>\<^sub>q\<^sub>;\<^sub>\<gamma>\<^sub>a\<^sub>) (\<Gamma>\<^sub>s,(c'\<^sub>s,s'\<^sub>s),R\<^sub>s,G\<^sub>s) 
                     \<and> (\<Gamma>\<^sub>s, l\<^sub>s) \<in> par_cp\<^sub>e \<Gamma>\<^sub>s c\<^sub>s s\<^sub>s \<and> 
                       (\<forall>i. Suc i<length l\<^sub>s \<longrightarrow> 
                            \<Gamma>\<^sub>s\<turnstile>\<^sub>p(l\<^sub>s!i)  \<rightarrow>\<^sub>e (l\<^sub>s!(Suc i)) \<longrightarrow>        
                            (snd(l\<^sub>s!i), snd(l\<^sub>s!(Suc i))) \<in> R\<^sub>s) \<and>
                            last l\<^sub>s = (c'\<^sub>s, s'\<^sub>s)"
         using  tran_c    
         apply auto 
         using SIM_guarantee[OF Cons(3) Cons(4)] apply fast 
         using par_cp_l_dest l  SIM_env1[OF Cons(3) Cons(4) a0'' _ a2 _ a3 ] calculation  Cons(2)
              lc
         apply auto
         by (smt  nth_Cons_0 snd_conv step_pe_elim_cases zero_less_Suc)         
       moreover then  obtain c'\<^sub>s s'\<^sub>s l\<^sub>s where 
         sim:"(\<Gamma>\<^sub>c,(c'\<^sub>c, s'\<^sub>c),R\<^sub>c,G\<^sub>c) \<succeq>\<^sub>p\<^sub>(\<^sub>\<alpha>\<^sub>;\<^sub>\<gamma>\<^sub>q\<^sub>;\<^sub>\<gamma>\<^sub>a\<^sub>) (\<Gamma>\<^sub>s,(c'\<^sub>s,s'\<^sub>s),R\<^sub>s,G\<^sub>s) \<and> 
              (\<forall>i. Suc i<length l\<^sub>s \<longrightarrow> 
                            \<Gamma>\<^sub>s\<turnstile>\<^sub>p(l\<^sub>s!i)  \<rightarrow>\<^sub>e (l\<^sub>s!(Suc i)) \<longrightarrow>        
                            (snd(l\<^sub>s!i), snd(l\<^sub>s!(Suc i))) \<in>R\<^sub>s) \<and>
              (\<Gamma>\<^sub>s, l\<^sub>s) \<in> par_cp\<^sub>e \<Gamma>\<^sub>s c\<^sub>s s\<^sub>s \<and> last l\<^sub>s = (c'\<^sub>s, s'\<^sub>s)" by auto  
       ultimately have "\<exists>l\<^sub>s. (\<Gamma>\<^sub>s, l\<^sub>s) \<in> par_cp\<^sub>e \<Gamma>\<^sub>s c'\<^sub>s s'\<^sub>s \<and>
                        (\<forall>i. Suc i < length l\<^sub>s \<longrightarrow>
                             \<Gamma>\<^sub>s\<turnstile>\<^sub>p (l\<^sub>s ! i) \<rightarrow>\<^sub>e (l\<^sub>s ! Suc i) \<longrightarrow>
                            (snd (l\<^sub>s ! i), snd (l\<^sub>s ! Suc i)) \<in> R\<^sub>s) \<and>
                      (\<forall>i<length l\<^sub>c.
                        \<exists>i\<^sub>s<length l\<^sub>s. (\<Gamma>\<^sub>c,l\<^sub>c ! i,R\<^sub>c,G\<^sub>c) \<succeq>\<^sub>p\<^sub>(\<^sub>\<alpha>\<^sub>;\<^sub>\<gamma>\<^sub>q\<^sub>;\<^sub>\<gamma>\<^sub>a\<^sub>)
                      (\<Gamma>\<^sub>s,l\<^sub>s ! i\<^sub>s,R\<^sub>s,G\<^sub>s))"    
        using Cons(1) l
        by (metis (no_types, lifting) fst_conv snd_conv wf_conf_par_cp_last)
      then obtain l1s where induc:"(\<Gamma>\<^sub>s, l1s) \<in> par_cp\<^sub>e \<Gamma>\<^sub>s c'\<^sub>s s'\<^sub>s \<and>
                      (\<forall>i. Suc i < length l1s \<longrightarrow>
                             \<Gamma>\<^sub>s\<turnstile>\<^sub>p (l1s ! i) \<rightarrow>\<^sub>e (l1s ! Suc i) \<longrightarrow>
                            (snd (l1s ! i), snd (l1s ! Suc i)) \<in> R\<^sub>s) \<and>
                      (\<forall>i<length l\<^sub>c.
                        \<exists>i\<^sub>s<length l1s. (\<Gamma>\<^sub>c,l\<^sub>c ! i,R\<^sub>c,G\<^sub>c) \<succeq>\<^sub>p\<^sub>(\<^sub>\<alpha>\<^sub>;\<^sub>\<gamma>\<^sub>q\<^sub>;\<^sub>\<gamma>\<^sub>a\<^sub>)
                      (\<Gamma>\<^sub>s,l1s ! i\<^sub>s,R\<^sub>s,G\<^sub>s))" by auto
      then have comp:"(\<Gamma>\<^sub>s,(take ((length l\<^sub>s)-1) l\<^sub>s)@l1s) \<in> par_cp\<^sub>e \<Gamma>\<^sub>s c\<^sub>s s\<^sub>s" 
        using sim cptn_e by fast
      moreover have "\<forall>i. Suc i < length ((take ((length l\<^sub>s)-1) l\<^sub>s)@l1s) \<longrightarrow>
                         \<Gamma>\<^sub>s\<turnstile>\<^sub>p (((take ((length l\<^sub>s)-1) l\<^sub>s)@l1s) ! i) \<rightarrow>\<^sub>e (((take ((length l\<^sub>s)-1) l\<^sub>s)@l1s) ! Suc i) \<longrightarrow>
                         (snd (((take ((length l\<^sub>s)-1) l\<^sub>s)@l1s) ! i), snd (((take ((length l\<^sub>s)-1) l\<^sub>s)@l1s) ! Suc i)) \<in> R\<^sub>s"
      proof-
        have "l1s ! 0 = (c'\<^sub>s,s'\<^sub>s)" using induc par_cp_l_dest by fastforce
        then have "l\<^sub>s ! (length l\<^sub>s - 1) = l1s ! 0" using sim
          by (metis last_conv_nth neq_Nil_conv par_cp_l_dest) 
        then also have "length l\<^sub>s - 1 < length l\<^sub>s"
          using par_cp_l_dest sim by fastforce
        ultimately show ?thesis  
          using assum_union[ of l\<^sub>s \<Gamma>\<^sub>s R\<^sub>s l1s "length l\<^sub>s - 1"] sim induc by fast
      qed                         
      moreover have "(\<forall>i<length (l # l\<^sub>c).
                  \<exists>i\<^sub>s<length ((take ((length l\<^sub>s)-1) l\<^sub>s)@l1s). (\<Gamma>\<^sub>c,(l # l\<^sub>c) ! i,R\<^sub>c,G\<^sub>c) \<succeq>\<^sub>p\<^sub>(\<^sub>\<alpha>\<^sub>;\<^sub>\<gamma>\<^sub>q\<^sub>;\<^sub>\<gamma>\<^sub>a\<^sub>)
                                (\<Gamma>\<^sub>s,((take ((length l\<^sub>s)-1) l\<^sub>s)@l1s) ! i\<^sub>s,R\<^sub>s,G\<^sub>s))"
      proof-
      {fix i            
       assume "i<length (l#l\<^sub>c)"
       {
         assume "i=0"
         then have "(\<Gamma>\<^sub>c,(l # l\<^sub>c) ! i,R\<^sub>c,G\<^sub>c) \<succeq>\<^sub>p\<^sub>(\<^sub>\<alpha>\<^sub>;\<^sub>\<gamma>\<^sub>q\<^sub>;\<^sub>\<gamma>\<^sub>a\<^sub>)
               (\<Gamma>\<^sub>s,(take (length l\<^sub>s - 1) l\<^sub>s @ l1s) !0,R\<^sub>s,G\<^sub>s)" 
           using sim Cons(3) lc                           
           by (metis (no_types) Cons.prems(2) comp lc nth_Cons_0 par_cp_l_dest)                                    
         then have "\<exists>i\<^sub>s<length (take (length l\<^sub>s - 1) l\<^sub>s @ l1s).
                 (\<Gamma>\<^sub>c,(l # l\<^sub>c) ! i,R\<^sub>c,G\<^sub>c) \<succeq>\<^sub>p\<^sub>(\<^sub>\<alpha>\<^sub>;\<^sub>\<gamma>\<^sub>q\<^sub>;\<^sub>\<gamma>\<^sub>a\<^sub>)
                 (\<Gamma>\<^sub>s,(take (length l\<^sub>s - 1) l\<^sub>s @ l1s) !
                   i\<^sub>s,R\<^sub>s,G\<^sub>s)" using induc l by force          
       }  note lef =this         
       { assume "i>0"           
         have "i < Suc (length l\<^sub>c)"                       
           using \<open>i < length (l # l\<^sub>c)\<close> by auto             
         then have "\<not> length l\<^sub>c < i"                   
           by (meson not_less_eq)                      
         then have "\<exists>i\<^sub>s<length (take (length l\<^sub>s - 1) l\<^sub>s @ l1s).
              (\<Gamma>\<^sub>c, (l#l\<^sub>c) ! i,R\<^sub>c,G\<^sub>c) \<succeq>\<^sub>p\<^sub>(\<^sub>\<alpha>\<^sub>;\<^sub>\<gamma>\<^sub>q\<^sub>;\<^sub>\<gamma>\<^sub>a\<^sub>)
              (\<Gamma>\<^sub>s,(take (length l\<^sub>s - 1) l\<^sub>s @ l1s) ! i\<^sub>s,R\<^sub>s,G\<^sub>s)"                        
           by (metis (no_types) Suc_diff_1 \<open>0 < i\<close> induc not_less_eq nth_Cons_pos prod.collapse str1)
       }         
       then have "\<exists>i\<^sub>s<length (take (length l\<^sub>s - 1) l\<^sub>s @ l1s).
                 (\<Gamma>\<^sub>c,(l # l\<^sub>c) ! i,R\<^sub>c,G\<^sub>c) \<succeq>\<^sub>p\<^sub>(\<^sub>\<alpha>\<^sub>;\<^sub>\<gamma>\<^sub>q\<^sub>;\<^sub>\<gamma>\<^sub>a\<^sub>)
                 (\<Gamma>\<^sub>s,(take (length l\<^sub>s - 1) l\<^sub>s @ l1s) !
                   i\<^sub>s,R\<^sub>s,G\<^sub>s)" using lef by fastforce        
     }thus ?thesis by auto                
   qed                
    ultimately have ?case by fast
  }    
  thus ?case using l1      
    by (metis list.exhaust_sel surjective_pairing)          
qed  
  
  
lemma RG_SIM_cp_all_sim_l\<^sub>s_All_End:    
assumes    
 a0:"(\<Gamma>\<^sub>c,l\<^sub>c)\<in> par_cp\<^sub>e \<Gamma>\<^sub>c c\<^sub>c s\<^sub>c \<and> 
     (\<forall>i. Suc i<length l\<^sub>c \<longrightarrow> 
          \<Gamma>\<^sub>c\<turnstile>\<^sub>p(l\<^sub>c!i)  \<rightarrow>\<^sub>e (l\<^sub>c!(Suc i)) \<longrightarrow>        
          (snd(l\<^sub>c!i), snd(l\<^sub>c!(Suc i))) \<in> R\<^sub>c)" and    a0'':"R\<^sub>s \<subseteq> R_eq_locals" and
   a0':"wf_conf c\<^sub>s s\<^sub>s" and  
 a1:"(\<Gamma>\<^sub>c,(c\<^sub>c,s\<^sub>c),R\<^sub>c,G\<^sub>c) \<succeq>\<^sub>p\<^sub>(\<^sub>\<alpha>\<^sub>;\<^sub>\<gamma>\<^sub>q\<^sub>;\<^sub>\<gamma>\<^sub>a\<^sub>) (\<Gamma>\<^sub>s,(c\<^sub>s,s\<^sub>s),R\<^sub>s,G\<^sub>s)"  and
 a2:"All_End (last l\<^sub>c)" and a4:"R\<^sub>c \<subseteq>  in_rel (R\<^sub>s\<^sup>*) \<alpha>" and a5:"\<forall>\<Sigma>. (\<Sigma>,\<Sigma>)\<in>R\<^sub>s"
shows "\<exists>l\<^sub>s. (\<Gamma>\<^sub>s,l\<^sub>s)\<in> par_cp\<^sub>e \<Gamma>\<^sub>s c\<^sub>s s\<^sub>s \<and>
            (\<forall>i. Suc i<length l\<^sub>s \<longrightarrow> 
                 \<Gamma>\<^sub>s\<turnstile>\<^sub>p(l\<^sub>s!i)  \<rightarrow>\<^sub>e (l\<^sub>s!(Suc i)) \<longrightarrow>        
                 (snd(l\<^sub>s!i), snd(l\<^sub>s!(Suc i))) \<in> R\<^sub>s) \<and> 
             All_End (last l\<^sub>s) \<and> sim_final_state (fst (last l\<^sub>c)) (snd (last l\<^sub>c)) (fst (last l\<^sub>s)) (snd (last l\<^sub>s)) \<gamma>\<^sub>q \<gamma>\<^sub>a"  
proof -
  obtain l\<^sub>s where l1:"(\<Gamma>\<^sub>s,l\<^sub>s)\<in> par_cp\<^sub>e \<Gamma>\<^sub>s c\<^sub>s s\<^sub>s \<and>
            (\<forall>i. Suc i<length l\<^sub>s \<longrightarrow> 
                 \<Gamma>\<^sub>s\<turnstile>\<^sub>p(l\<^sub>s!i)  \<rightarrow>\<^sub>e (l\<^sub>s!(Suc i)) \<longrightarrow>        
                 (snd(l\<^sub>s!i), snd(l\<^sub>s!(Suc i))) \<in> R\<^sub>s) \<and>              
             (\<forall>i<length l\<^sub>c. (\<exists>i\<^sub>s<length l\<^sub>s. 
               (\<Gamma>\<^sub>c,l\<^sub>c !i ,R\<^sub>c,G\<^sub>c) \<succeq>\<^sub>p\<^sub>(\<^sub>\<alpha>\<^sub>;\<^sub>\<gamma>\<^sub>q\<^sub>;\<^sub>\<gamma>\<^sub>a\<^sub>) (\<Gamma>\<^sub>s,l\<^sub>s!i\<^sub>s,R\<^sub>s,G\<^sub>s) ))"  
    using RG_SIM_cp_all_sim_l\<^sub>s[OF a0 a0'' a0'  a4 a5 a1] by auto
  then obtain i\<^sub>s where iss: "i\<^sub>s<length l\<^sub>s \<and> (\<Gamma>\<^sub>c,(last l\<^sub>c) ,R\<^sub>c,G\<^sub>c) \<succeq>\<^sub>p\<^sub>(\<^sub>\<alpha>\<^sub>;\<^sub>\<gamma>\<^sub>q\<^sub>;\<^sub>\<gamma>\<^sub>a\<^sub>) (\<Gamma>\<^sub>s,l\<^sub>s!i\<^sub>s,R\<^sub>s,G\<^sub>s)"
    by (metis a0 last_length length_Cons lessI par_cp_l_dest)
    
  then obtain l\<^sub>s1 where ls1:"(\<Gamma>\<^sub>s,l\<^sub>s1) \<in>par_cp\<^sub>e \<Gamma>\<^sub>s (fst (l\<^sub>s!i\<^sub>s)) (snd (l\<^sub>s!i\<^sub>s)) \<and>
           (\<forall>i. Suc i<length l\<^sub>s1 \<longrightarrow> 
                     \<Gamma>\<^sub>s\<turnstile>\<^sub>p(l\<^sub>s1!i)  \<rightarrow>\<^sub>e (l\<^sub>s1!(Suc i)) \<longrightarrow>        
                     (snd(l\<^sub>s1!i), snd(l\<^sub>s1!(Suc i))) \<in> R\<^sub>s) \<and> 
           All_End (last l\<^sub>s1) \<and> sim_final_state (fst (last l\<^sub>c)) (snd (last l\<^sub>c)) (fst (last l\<^sub>s1)) (snd (last l\<^sub>s1)) \<gamma>\<^sub>q \<gamma>\<^sub>a" 
    using All_End_simulation a2 a0' wf_conf_par_cp
    by (metis local.l1 prod.exhaust_sel wf_conf_par_cp)    
  then have "(\<Gamma>\<^sub>s,(take i\<^sub>s l\<^sub>s)@ l\<^sub>s1) \<in> par_cp\<^sub>e \<Gamma>\<^sub>s c\<^sub>s s\<^sub>s" using l1 par_cp\<^sub>e_app1
    by (metis iss prod.collapse) 
  moreover have "All_End (last ((take i\<^sub>s l\<^sub>s)@ l\<^sub>s1)) \<and> 
                 sim_final_state (fst (last l\<^sub>c)) (snd (last l\<^sub>c)) (fst (last ((take i\<^sub>s l\<^sub>s)@ l\<^sub>s1))) (snd (last ((take i\<^sub>s l\<^sub>s)@ l\<^sub>s1))) \<gamma>\<^sub>q \<gamma>\<^sub>a"
    using ls1 par_cp_l_dest by fastforce
  moreover have "(\<forall>i. Suc i<length ((take i\<^sub>s l\<^sub>s)@ l\<^sub>s1) \<longrightarrow> 
                 \<Gamma>\<^sub>s\<turnstile>\<^sub>p(((take i\<^sub>s l\<^sub>s)@ l\<^sub>s1)!i)  \<rightarrow>\<^sub>e (((take i\<^sub>s l\<^sub>s)@ l\<^sub>s1)!(Suc i)) \<longrightarrow>        
                 (snd(((take i\<^sub>s l\<^sub>s)@ l\<^sub>s1)!i), snd(((take i\<^sub>s l\<^sub>s)@ l\<^sub>s1)!(Suc i))) \<in> R\<^sub>s)"
    using ls1 l1 assum_union
    by (metis (no_types, lifting) iss nth_Cons_0 par_cp_l_dest prod.collapse)  
  ultimately show ?thesis by auto
qed

lemma skip_program_not_fault:"skip_program c \<Longrightarrow> not_fault c F"
  unfolding skip_program_def not_fault_def by auto

lemma throw_program_not_fault:"throw_program c \<Longrightarrow> not_fault c F"
  unfolding throw_program_def not_fault_def by auto

lemma final_error_not_fault:
  "not_fault c\<^sub>c F \<Longrightarrow> final_error c\<^sub>c \<Longrightarrow> final_error_r c\<^sub>c c\<^sub>s \<Longrightarrow> not_fault c\<^sub>s F"
  unfolding not_fault_def final_error_r_def     
  by force

lemma final_error_not_fault1:
  assumes a0:"not_fault c\<^sub>c F" and a1:"final_error_r c\<^sub>c c\<^sub>s" and a2:"All_End (c\<^sub>c,s)"
  shows "not_fault c\<^sub>s F"
proof-
  { assume "final_error c\<^sub>c"
    then have ?thesis using final_error_not_fault a0 a1 by auto
  }
  moreover {
    assume "\<not> final_error c\<^sub>c" 
    then have "\<not> final_error c\<^sub>s"
      using a1 unfolding final_error_r_def by auto
    then have ?thesis using a1 unfolding final_error_r_def by auto
  } ultimately show ?thesis by auto
qed 

lemma final_state:"sim_final_state c \<sigma> s \<Sigma> \<gamma>\<^sub>q \<gamma>\<^sub>a \<Longrightarrow> All_End (c,\<sigma>) \<Longrightarrow>
      not_fault c F \<Longrightarrow> not_fault s F"  
  unfolding sim_final_state_def 
  using skip_program_not_fault throw_program_not_fault final_error_not_fault1    
  by blast
  

lemma RG_SIM_fst_env_comm_ref1: 
  assumes      
 a0:"(\<forall>i<length l\<^sub>c. \<exists>i\<^sub>s<length l\<^sub>s.(\<Gamma>\<^sub>c,l\<^sub>c !i ,R\<^sub>c,G\<^sub>c) \<succeq>\<^sub>p\<^sub>(\<^sub>\<alpha>\<^sub>;\<^sub>\<gamma>\<^sub>q\<^sub>;\<^sub>\<gamma>\<^sub>a\<^sub>) (\<Gamma>\<^sub>s,l\<^sub>s!i\<^sub>s,R\<^sub>s,G\<^sub>s) )" and   
 a2:" Suc i<length l\<^sub>c" and
 a3:"\<Gamma>\<^sub>c\<turnstile>\<^sub>p\<^sub>e(l\<^sub>c!i)  \<rightarrow> (l\<^sub>c!(Suc i))" and
 a4:"(\<Gamma>\<^sub>s,l\<^sub>s) \<in> par_comm\<^sub>e(G\<^sub>s, (q\<^sub>s,a\<^sub>s)) F" and  
 a8:"l\<^sub>s!0=(p,s)" and a9:"(\<Gamma>\<^sub>s,l\<^sub>s)\<in> par_cptn\<^sub>e " and
  a10:"(\<Gamma>\<^sub>s,l\<^sub>s)\<in>par_assum(UNIV,R\<^sub>s)"    
shows "(snd(l\<^sub>c!i), snd(l\<^sub>c!(Suc i))) \<in> G\<^sub>c"
proof-
  obtain c\<^sub>c \<sigma> c\<^sub>c' \<sigma>' where l: "l\<^sub>c!i = (c\<^sub>c,\<sigma>) \<and> l\<^sub>c!(Suc i) = (c\<^sub>c',\<sigma>')"
    using prod.exhaust_sel by blast
  then have step:"\<Gamma>\<^sub>c\<turnstile>\<^sub>p\<^sub>e (c\<^sub>c,\<sigma>)  \<rightarrow> (c\<^sub>c',\<sigma>')" using a3 by auto
  then obtain i\<^sub>s i\<^sub>s\<^sub>' where sims:"i\<^sub>s<length l\<^sub>s \<and> (\<Gamma>\<^sub>c,(c\<^sub>c,\<sigma>) ,R\<^sub>c,G\<^sub>c) \<succeq>\<^sub>p\<^sub>(\<^sub>\<alpha>\<^sub>;\<^sub>\<gamma>\<^sub>q\<^sub>;\<^sub>\<gamma>\<^sub>a\<^sub>) (\<Gamma>\<^sub>s,l\<^sub>s!i\<^sub>s,R\<^sub>s,G\<^sub>s)" and
                      islen:"i\<^sub>s\<^sub>'<length l\<^sub>s" and sim1:"(\<Gamma>\<^sub>c,(c\<^sub>c',\<sigma>') ,R\<^sub>c,G\<^sub>c) \<succeq>\<^sub>p\<^sub>(\<^sub>\<alpha>\<^sub>;\<^sub>\<gamma>\<^sub>q\<^sub>;\<^sub>\<gamma>\<^sub>a\<^sub>) (\<Gamma>\<^sub>s,l\<^sub>s!i\<^sub>s\<^sub>',R\<^sub>s,G\<^sub>s) " 
    using a0 a2 l by (metis Suc_lessD)  
  then  obtain c\<^sub>s \<Sigma> where ls:"l\<^sub>s!i\<^sub>s=(c\<^sub>s,\<Sigma>)" using prod.exhaust_sel by blast
  then have sim:"(\<Gamma>\<^sub>c,(c\<^sub>c,\<sigma>) ,R\<^sub>c,G\<^sub>c) \<succeq>\<^sub>p\<^sub>(\<^sub>\<alpha>\<^sub>;\<^sub>\<gamma>\<^sub>q\<^sub>;\<^sub>\<gamma>\<^sub>a\<^sub>) (\<Gamma>\<^sub>s,(c\<^sub>s,\<Sigma>),R\<^sub>s,G\<^sub>s)"
    using sims by auto
  obtain c\<^sub>s' \<Sigma>' where guar:"
     (\<Gamma>\<^sub>s\<turnstile>\<^sub>p (c\<^sub>s,\<Sigma>) \<rightarrow>\<^sub>\<tau>\<^sup>* (c\<^sub>s', \<Sigma>') \<or> (\<exists>v. e = Some v \<and> \<Gamma>\<^sub>s\<turnstile>\<^sub>p\<^sub>v (c\<^sub>s,\<Sigma>) \<rightarrow>\<^sup>+ (c\<^sub>s', \<Sigma>'))) \<and>     
     (\<sigma>', \<Sigma>') \<in> \<alpha> \<and> 
     (\<sigma>, \<sigma>') \<in> G\<^sub>c"    
    using SIM_next_state[OF sim step] by force
  thus ?thesis using l by auto      
qed


lemma final_c_lambda1:
  assumes a0:"(\<Gamma>\<^sub>s,l\<^sub>s) \<in> par_comm\<^sub>e(G\<^sub>s, (q\<^sub>s,a\<^sub>s)) F " and
          a1:"not_fault (fst (last l\<^sub>c)) F" and                    
          a2:"All_End (last l\<^sub>c)" and a2':"All_End (last l\<^sub>s)" and
          a3: "sim_final_state (fst (last l\<^sub>c)) (snd (last l\<^sub>c)) (fst (last l\<^sub>s)) (snd (last l\<^sub>s)) \<gamma>\<^sub>q \<gamma>\<^sub>a"
  shows " skip_program (fst (last l\<^sub>s)) \<and> snd (last l\<^sub>s) \<in> q\<^sub>s \<or> 
          throw_program (fst (last l\<^sub>s)) \<and> snd (last l\<^sub>s) \<in>  a\<^sub>s"
proof-
  have "not_fault (fst (last l\<^sub>s)) F" 
    using a1 a2 a3 final_state[OF a3 ] by auto  
  thus ?thesis using a0 a2' unfolding  par_comm\<^sub>e_def split_beta 
    unfolding skip_program_def throw_program_def by auto
qed

lemma skip_not_throw:"skip_program c \<Longrightarrow> \<not> throw_program c "
  unfolding skip_program_def throw_program_def by auto

lemma throw_not_skip:"throw_program c \<Longrightarrow> \<not> skip_program c"
  unfolding skip_program_def throw_program_def by auto

lemma skip_not_final_error:"skip_program c \<Longrightarrow> \<not> final_error c"
  unfolding skip_program_def final_error_def by auto

lemma final_error_not_skip:" final_error c \<Longrightarrow> \<not> skip_program c"
  unfolding skip_program_def final_error_def by auto

lemma throw_not_final_error:"throw_program c \<Longrightarrow> \<not> final_error c"
  unfolding throw_program_def final_error_def by auto

lemma final_error_not_throw:" final_error c \<Longrightarrow> \<not> throw_program c"
  unfolding throw_program_def final_error_def by auto

lemma sim_final_state_dest_skip1:
  "sim_final_state c \<sigma> s \<Sigma> r1 r2 \<Longrightarrow>
   skip_program c \<Longrightarrow>
   skip_program s \<and> (\<sigma>,\<Sigma>)\<in>r1"
    unfolding sim_final_state_def
    using final_error_not_skip final_error_r_def skip_not_throw by blast

lemma sim_final_state_dest_skip2:
  "sim_final_state c \<sigma> s \<Sigma> r1 r2 \<Longrightarrow>
   skip_program s \<Longrightarrow>
   skip_program c \<and> (\<sigma>,\<Sigma>)\<in>r1"
    unfolding sim_final_state_def
    using final_error_not_skip final_error_r_def skip_not_throw by blast


lemma sim_final_state_dest_throw1:
  "sim_final_state c \<sigma> s \<Sigma> r1 r2 \<Longrightarrow>
   throw_program s \<Longrightarrow>
   throw_program c \<and> (\<sigma>,\<Sigma>)\<in>r2"
    unfolding sim_final_state_def
    using final_error_not_throw final_error_r_def skip_not_throw by blast
    
lemma sim_final_state_dest_throw2:
  "sim_final_state c \<sigma> s \<Sigma> r1 r2 \<Longrightarrow>
   throw_program c \<Longrightarrow>
   throw_program s \<and> (\<sigma>,\<Sigma>)\<in>r2"
    unfolding sim_final_state_def
    using final_error_not_throw final_error_r_def skip_not_throw by blast

lemma sim_final_state_dest_final_error:
  "sim_final_state c \<sigma> s \<Sigma> r1 r2 \<Longrightarrow>
   final_error c \<Longrightarrow>
   final_error c"
    unfolding sim_final_state_def
    using final_error_not_throw final_error_r_def skip_not_throw by blast


lemma final_c_lambda2:
  assumes a0:"(\<Gamma>\<^sub>s,l\<^sub>s) \<in> par_comm\<^sub>e(G\<^sub>s, (q\<^sub>s,a\<^sub>s)) F " and
          a1:"not_fault (fst (last l\<^sub>c)) F" and
          a2: "All_End (last l\<^sub>c)" and a2': "All_End (last l\<^sub>s)" and         
          a4: "sim_final_state (fst (last l\<^sub>c)) (snd (last l\<^sub>c)) (fst (last l\<^sub>s)) (snd (last l\<^sub>s)) \<gamma>\<^sub>q \<gamma>\<^sub>a"
  shows "(skip_program (fst (last l\<^sub>s)) \<and> (snd (last l\<^sub>c),snd (last l\<^sub>s))\<in> \<gamma>\<^sub>q) \<or> 
         (throw_program (fst (last l\<^sub>s)) \<and> (snd (last l\<^sub>c),snd (last l\<^sub>s))\<in> \<gamma>\<^sub>a)"
  using a4 final_c_lambda1[OF a0 a1 a2 a2' a4]
  using sim_final_state_dest_skip2 sim_final_state_dest_throw1 by blast


lemma final_c_lambda3:
  assumes a0:"(\<Gamma>\<^sub>s,l\<^sub>s) \<in> par_comm\<^sub>e(G\<^sub>s, (q\<^sub>s,a\<^sub>s)) F " and
          a1:"not_fault (fst (last l\<^sub>c)) F" and
          a2: "All_End (last l\<^sub>c)" and a2':"All_End (last l\<^sub>s)" and
          a3: "\<gamma>qn = \<Down>\<^sub>i\<gamma>\<^sub>q \<and> q\<^sub>s \<subseteq> Domain \<gamma>qn \<and> ((\<gamma>qn `` q\<^sub>s) \<subseteq> q\<^sub>c) \<and>
               \<gamma>an = \<Down>\<^sub>i\<gamma>\<^sub>a \<and> a\<^sub>s \<subseteq> Domain \<gamma>an \<and> ((\<gamma>an `` a\<^sub>s) \<subseteq> a\<^sub>c)" and
          a4: "sim_final_state (fst (last l\<^sub>c)) (snd (last l\<^sub>c)) (fst (last l\<^sub>s)) (snd (last l\<^sub>s)) \<gamma>\<^sub>q \<gamma>\<^sub>a"
  shows " (skip_program (fst (last l\<^sub>c)) \<and> snd (last l\<^sub>c) \<in>  q\<^sub>c) \<or> 
          (throw_program (fst (last l\<^sub>c)) \<and> snd (last l\<^sub>c) \<in>  a\<^sub>c )" 
proof -
  have comm_ls:" (skip_program (fst (last l\<^sub>s)) \<and> snd (last l\<^sub>s) \<in> q\<^sub>s) \<or> 
          (throw_program (fst (last l\<^sub>s)) \<and> snd (last l\<^sub>s) \<in> a\<^sub>s )"
    using final_c_lambda1[OF a0 a1 a2  a2' a4] by auto
 { assume a00:"skip_program (fst (last l\<^sub>c))"            
   then have nssq:"snd (last l\<^sub>s) \<in> q\<^sub>s" 
      using a00 a4 comm_ls
      using sim_final_state_dest_throw1 skip_not_throw by blast
    then have "snd (last l\<^sub>c) \<in>  q\<^sub>c" using  a00 a4 a3 unfolding sim_final_state_def ToInv_def      
    proof -
      have f1: "skip_program (fst (last l\<^sub>s)) \<and> (snd (last l\<^sub>c), snd (last l\<^sub>s)) \<in> \<gamma>\<^sub>q"
        using a00 a4 sim_final_state_dest_skip1 by blast
      have "\<gamma>qn = {(pa, p). (p, pa) \<in> \<gamma>\<^sub>q}"
        by (simp add: ToInv_def a3)
      then show ?thesis
        using f1 a3 nssq by blast
    qed         
  }  
  also {
    assume a00:"throw_program (fst (last l\<^sub>c))"       
    moreover have "snd (last l\<^sub>s) \<in> a\<^sub>s"  
      using a4 comm_ls a00
      using sim_final_state_dest_skip2 skip_not_throw by blast     
    ultimately have "snd (last l\<^sub>c) \<in>  a\<^sub>c" using a00 a4 a3
    proof -
      have f1: "throw_program (fst (last l\<^sub>s)) \<and> (snd (last l\<^sub>c), snd (last l\<^sub>s)) \<in> \<gamma>\<^sub>a"
        using a00 a4 sim_final_state_dest_throw2 by blast
      have "\<gamma>an = {(pa, p). (p, pa) \<in> \<gamma>\<^sub>a}"
        by (simp add: ToInv_def a3)
      then show ?thesis
        using f1 \<open>snd (last l\<^sub>s) \<in> a\<^sub>s\<close> a3 by blast
      qed
  }
  ultimately show ?thesis
    using a4 comm_ls sim_final_state_dest_skip2 sim_final_state_dest_throw1 by blast
qed
 
  
lemma RG_SIM_fst_env_comm_ref2: 
assumes  
 a0:"(\<Gamma>\<^sub>c,(c\<^sub>c,s\<^sub>c),R\<^sub>c,G\<^sub>c) \<succeq>\<^sub>p\<^sub>(\<^sub>\<alpha>\<^sub>;\<^sub>\<gamma>\<^sub>q\<^sub>;\<^sub>\<gamma>\<^sub>a\<^sub>) (\<Gamma>\<^sub>s,(c\<^sub>s,s\<^sub>s),R\<^sub>s,G\<^sub>s)" and
 a1:"\<gamma>qn = \<Down>\<^sub>i\<gamma>\<^sub>q \<and> q\<^sub>s \<subseteq> Domain \<gamma>qn \<and> ((\<gamma>qn `` q\<^sub>s) \<subseteq> q\<^sub>c) \<and>
     \<gamma>an = \<Down>\<^sub>i\<gamma>\<^sub>a \<and> a\<^sub>s \<subseteq> Domain \<gamma>an \<and> ((\<gamma>an `` a\<^sub>s)\<subseteq> a\<^sub>c)" and                  
 a2:"(\<Gamma>\<^sub>s,l\<^sub>s) \<in> par_comm\<^sub>e(G\<^sub>s, (q\<^sub>s,a\<^sub>s)) F \<and>
     (\<Gamma>\<^sub>s,l\<^sub>s)\<in>par_cp\<^sub>e \<Gamma>\<^sub>s c\<^sub>s s\<^sub>s \<and> 
     (\<Gamma>\<^sub>s,l\<^sub>s) \<in> par_assum(p\<^sub>s,R\<^sub>s) \<and> All_End (last l\<^sub>s) \<and> 
     sim_final_state (fst (last l\<^sub>c)) (snd (last l\<^sub>c)) (fst (last l\<^sub>s)) (snd (last l\<^sub>s)) \<gamma>\<^sub>q \<gamma>\<^sub>a" and
 a3:"(\<Gamma>\<^sub>c,l\<^sub>c)\<in>par_cp\<^sub>e \<Gamma>\<^sub>c c\<^sub>c s\<^sub>c \<and> (\<Gamma>\<^sub>c,l\<^sub>c) \<in> par_assum(p\<^sub>c,R\<^sub>c)"
shows "All_End (last l\<^sub>c)  \<longrightarrow> not_fault (fst (last l\<^sub>c)) F \<longrightarrow>
          (skip_program (fst (last l\<^sub>c)) \<and> snd (last l\<^sub>c) \<in>  q\<^sub>c) \<or> 
          (throw_program (fst (last l\<^sub>c)) \<and> snd (last l\<^sub>c) \<in>  a\<^sub>c )"
proof -
  {
    assume "All_End (last l\<^sub>c)" and a01:"not_fault (fst (last l\<^sub>c)) F"            
    then have "(skip_program (fst (last l\<^sub>c)) \<and> snd (last l\<^sub>c) \<in>  q\<^sub>c) \<or> 
              (throw_program (fst (last l\<^sub>c)) \<and> snd (last l\<^sub>c) \<in>  a\<^sub>c )" 
      using  a1 a2  final_c_lambda3[OF _, of \<Gamma>\<^sub>s l\<^sub>s G\<^sub>s q\<^sub>s a\<^sub>s F l\<^sub>c \<gamma>qn \<gamma>\<^sub>q q\<^sub>c \<gamma>an \<gamma>\<^sub>a a\<^sub>c] by blast  
  } thus ?thesis by auto
qed

lemma RG_SIM_fst_env_par_comm_ref: 
  assumes  
   a0:"(\<Gamma>\<^sub>c,(c\<^sub>c,s\<^sub>c),R\<^sub>c,G\<^sub>c) \<succeq>\<^sub>p\<^sub>(\<^sub>\<alpha>\<^sub>;\<^sub>\<gamma>\<^sub>q\<^sub>;\<^sub>\<gamma>\<^sub>a\<^sub>) (\<Gamma>\<^sub>s,(c\<^sub>s,s\<^sub>s),R\<^sub>s,G\<^sub>s)" and     
   a1:"\<gamma>qn = \<Down>\<^sub>i\<gamma>\<^sub>q \<and> q\<^sub>s \<subseteq> Domain \<gamma>qn \<and> ((\<gamma>qn `` q\<^sub>s) \<subseteq> q\<^sub>c) \<and>
       \<gamma>an = \<Down>\<^sub>i\<gamma>\<^sub>a \<and> a\<^sub>s \<subseteq> Domain \<gamma>an \<and> ((\<gamma>an `` a\<^sub>s) \<subseteq> a\<^sub>c)" and                     
   a2:"(\<Gamma>\<^sub>c,l\<^sub>c)\<in>par_cp\<^sub>e \<Gamma>\<^sub>c c\<^sub>c s\<^sub>c \<and> (\<Gamma>\<^sub>c,l\<^sub>c) \<in> par_assum(p\<^sub>c,R\<^sub>c)" and
   a3:"s\<^sub>s \<in>  p\<^sub>s"  and
   a4:"\<Gamma>\<^sub>s \<Turnstile>\<^sub>e\<^bsub>/F\<^esub> c\<^sub>s SAT [p\<^sub>s, R\<^sub>s, G\<^sub>s, q\<^sub>s,a\<^sub>s]" and 
   a7:"R\<^sub>c \<subseteq>  in_rel (R\<^sub>s\<^sup>*) \<alpha>" and a8:"\<forall>\<Sigma>. (\<Sigma>,\<Sigma>)\<in>R\<^sub>s"  and 
   a9:"R\<^sub>s \<subseteq> R_eq_locals" and a10:"wf_conf c\<^sub>s s\<^sub>s"
 shows "(\<Gamma>\<^sub>c,l\<^sub>c) \<in> par_comm\<^sub>e (G\<^sub>c, (q\<^sub>c,a\<^sub>c)) F"
proof-      
  {       
   {fix i e
     assume b00:"Suc i<length l\<^sub>c" and
            b01:"\<Gamma>\<^sub>c\<turnstile>\<^sub>p\<^sub>e(l\<^sub>c!i)  \<rightarrow> (l\<^sub>c!(Suc i))"
     obtain l\<^sub>s where ls:"(\<Gamma>\<^sub>s,l\<^sub>s)\<in> par_cp\<^sub>e \<Gamma>\<^sub>s c\<^sub>s s\<^sub>s \<and>
                      (\<forall>i. Suc i<length l\<^sub>s \<longrightarrow> 
                          \<Gamma>\<^sub>s\<turnstile>\<^sub>p(l\<^sub>s!i)  \<rightarrow>\<^sub>e (l\<^sub>s!(Suc i)) \<longrightarrow>        
                        (snd(l\<^sub>s!i), snd(l\<^sub>s!(Suc i))) \<in> R\<^sub>s) \<and> 
                       (\<forall>i<length l\<^sub>c. (\<exists>i\<^sub>s<length l\<^sub>s. 
                          (\<Gamma>\<^sub>c,l\<^sub>c !i ,R\<^sub>c,G\<^sub>c) \<succeq>\<^sub>p\<^sub>(\<^sub>\<alpha>\<^sub>;\<^sub>\<gamma>\<^sub>q\<^sub>;\<^sub>\<gamma>\<^sub>a\<^sub>) (\<Gamma>\<^sub>s,l\<^sub>s!i\<^sub>s,R\<^sub>s,G\<^sub>s) ))" 
       using RG_SIM_cp_all_sim_l\<^sub>s[OF _ a9 a10 a7 a8 a0] a2 a3 
       unfolding par_assum_def par_cp\<^sub>e_def split_beta by fastforce      
    moreover have ass:"(\<Gamma>\<^sub>s,l\<^sub>s)\<in>par_assum(p\<^sub>s,R\<^sub>s)" 
      using calculation a3 unfolding par_assum_def par_cp\<^sub>e_def by auto   
    ultimately have comm:"(\<Gamma>\<^sub>s,l\<^sub>s) \<in> par_comm\<^sub>e(G\<^sub>s, (q\<^sub>s,a\<^sub>s)) F"
      using a4 unfolding par_com_validity_def by fast            
    have ass:"(\<Gamma>\<^sub>s,l\<^sub>s)\<in>par_assum(UNIV,R\<^sub>s)" using ass 
      unfolding par_assum_def  by fast     
    then have "(snd(l\<^sub>c!i), snd(l\<^sub>c!(Suc i))) \<in> G\<^sub>c" 
      using RG_SIM_fst_env_comm_ref1[OF _ b00 b01 comm   _ _  ass] 
       ls  a0  a2  unfolding par_cp\<^sub>e_def by blast
   } 
   then have f1:"\<forall>i e. Suc i< length l\<^sub>c \<longrightarrow> 
                    (\<Gamma>\<^sub>c\<turnstile>\<^sub>p\<^sub>e(l\<^sub>c!i)  \<rightarrow> (l\<^sub>c!(Suc i))) \<longrightarrow>
                   (snd(l\<^sub>c!i), snd(l\<^sub>c!(Suc i))) \<in> G\<^sub>c" by auto   
   {
     assume a00:"All_End (last l\<^sub>c)" and a01:"not_fault (fst (last l\<^sub>c)) F"
     obtain l\<^sub>s where 
       "(\<Gamma>\<^sub>s,l\<^sub>s)\<in> par_cp\<^sub>e \<Gamma>\<^sub>s c\<^sub>s s\<^sub>s \<and>
        (\<forall>i. Suc i<length l\<^sub>s \<longrightarrow> 
             \<Gamma>\<^sub>s\<turnstile>\<^sub>p(l\<^sub>s!i)  \<rightarrow>\<^sub>e (l\<^sub>s!(Suc i)) \<longrightarrow>        
             (snd(l\<^sub>s!i), snd(l\<^sub>s!(Suc i))) \<in> R\<^sub>s) \<and> 
         All_End (last l\<^sub>s) \<and> sim_final_state (fst (last l\<^sub>c)) (snd (last l\<^sub>c)) (fst (last l\<^sub>s)) (snd (last l\<^sub>s)) \<gamma>\<^sub>q \<gamma>\<^sub>a"
       using a2 a3 RG_SIM_cp_all_sim_l\<^sub>s_All_End[OF _ a9 a10 a0 a00  a7 a8]
       unfolding par_assum_def par_cp\<^sub>e_def by auto
     moreover then have "(\<Gamma>\<^sub>s,l\<^sub>s)\<in>par_assum(p\<^sub>s,R\<^sub>s)" using a3 unfolding par_assum_def par_cp\<^sub>e_def by auto  
     ultimately moreover have "(\<Gamma>\<^sub>s,l\<^sub>s) \<in> par_comm\<^sub>e(G\<^sub>s, (q\<^sub>s,a\<^sub>s)) F"
       using a4 unfolding par_com_validity_def by fast      
     ultimately have a4:"(\<Gamma>\<^sub>s,l\<^sub>s) \<in> par_comm\<^sub>e(G\<^sub>s, (q\<^sub>s,a\<^sub>s)) F \<and>
       (\<Gamma>\<^sub>s,l\<^sub>s)\<in>par_cp\<^sub>e \<Gamma>\<^sub>s c\<^sub>s s\<^sub>s \<and> 
       (\<Gamma>\<^sub>s,l\<^sub>s) \<in> par_assum(p\<^sub>s,R\<^sub>s) \<and> All_End (last l\<^sub>s) \<and> 
       sim_final_state (fst (last l\<^sub>c)) (snd (last l\<^sub>c)) (fst (last l\<^sub>s)) (snd (last l\<^sub>s)) \<gamma>\<^sub>q \<gamma>\<^sub>a"
      by auto 
     then have "All_End (last l\<^sub>c)  \<longrightarrow> not_fault (fst (last l\<^sub>c)) F \<longrightarrow>                   
          (throw_program (fst (last l\<^sub>c)) \<and> snd (last l\<^sub>c) \<in> a\<^sub>c) \<or>
          (skip_program (fst (last l\<^sub>c)) \<and> snd (last l\<^sub>c) \<in> q\<^sub>c)" 
      using RG_SIM_fst_env_comm_ref2[OF a0 a1 _ a2] by fastforce
   }
   then have "All_End (last l\<^sub>c) \<longrightarrow> not_fault (fst (last l\<^sub>c)) F \<longrightarrow>
             (throw_program (fst (last l\<^sub>c)) \<and> snd (last l\<^sub>c) \<in> a\<^sub>c) \<or>
             (skip_program (fst (last l\<^sub>c)) \<and> snd (last l\<^sub>c) \<in> q\<^sub>c)" by auto
   note res = conjI [OF this f1]   
  }
   thus?thesis unfolding par_comm\<^sub>e_def by auto  
 qed

definition set_to_list::"'a set \<Rightarrow> ('a list) set \<Rightarrow> ('a list) set"
  where"set_to_list s s1\<equiv>{l. \<exists>a l1. l=a#l1 \<and> a\<in>s \<and> l1\<in>s1}"


definition image_set_list_list::"('a set) list \<Rightarrow> ('a list) set"
  where
"image_set_list_list sl \<equiv> foldr (\<lambda>a l. set_to_list a l) sl {}"

definition image_list::"('s, 'ss) rel \<Rightarrow> 's list \<Rightarrow> ('ss set) list"
  where "image_list \<alpha> l  \<equiv> map (\<lambda>a. \<alpha>``{a}) l"

definition state_list_map::"('s list)set \<Rightarrow> ('s,'ss) rel \<Rightarrow> (('ss set) list) set"
  where "state_list_map s \<alpha> \<equiv> {l. \<exists>l'. l'\<in>s \<and> l = image_list \<alpha> l'}"





(* definition Refinement ::"('ss,'p,'f,'e) body \<Rightarrow> ('ss,'p,'f,'e) com list  \<Rightarrow>  ('sc,'ss)  invs \<Rightarrow>
                         ('sc,'p,'f,'e) body \<Rightarrow> ('sc,'p,'f,'e) com list  \<Rightarrow> bool" ("'(_,_') \<sqsubseteq>\<^sub>_ '(_,_')" [45, 45, 45,45, 45] 60)
  where "(\<Gamma>\<^sub>s,S) \<sqsubseteq>\<^sub>\<alpha> (\<Gamma>\<^sub>c,C) \<equiv> \<forall>\<Sigma>. (par_cp \<Gamma>\<^sub>c C (\<alpha>``\<Sigma>)) \<subseteq> (par_cp \<Gamma>\<^sub>s S \<Sigma>)" *)

   
lemma SAT_e_eq:"(\<Gamma> \<Turnstile>\<^sub>e\<^bsub>/F\<^esub> c SAT [p, R, G, q,a]) = (\<Gamma> \<Turnstile>\<^bsub>/F\<^esub> c SAT [p, R, G, q,a])" 
  unfolding par_com_validity_def LocalRG_HoareDef.par_com_validity_def   
  using eq_par_cp\<^sub>e_par_cp par_comm_eq_par_comm\<^sub>e by fast   



lemma RG_SIM_RG_pre: "(\<Gamma>\<^sub>c,c\<^sub>c,R\<^sub>c,G\<^sub>c) \<succeq>\<^sub>p\<^sub>(\<^sub>\<alpha>\<^sub>;\<^sub>\<xi>\<^sub>\<rhd>\<^sub>\<gamma>\<^sub>q\<^sub>;\<^sub>\<gamma>\<^sub>a\<^sub>) (\<Gamma>\<^sub>s,c\<^sub>s,R\<^sub>s,G\<^sub>s) \<Longrightarrow>  
                p\<^sub>c \<subseteq> Domain \<xi> \<and>  ( \<xi> `` p\<^sub>c \<subseteq> p\<^sub>s) \<Longrightarrow>
               \<gamma>qn = \<Down>\<^sub>i\<gamma>\<^sub>q \<and> q\<^sub>s \<subseteq> Domain \<gamma>qn \<and> ((\<gamma>qn `` q\<^sub>s) \<subseteq> q\<^sub>c) \<and>
                \<gamma>an = \<Down>\<^sub>i\<gamma>\<^sub>a \<and> a\<^sub>s \<subseteq> Domain \<gamma>an \<and> ((\<gamma>an `` a\<^sub>s) \<subseteq> a\<^sub>c)  \<Longrightarrow> 
                R\<^sub>c \<subseteq>  in_rel (R\<^sub>s\<^sup>*) \<alpha> \<Longrightarrow> \<forall>\<Sigma>. (\<Sigma>,\<Sigma>)\<in>R\<^sub>s \<Longrightarrow>  
                R\<^sub>s \<subseteq> R_eq_locals \<Longrightarrow> p\<^sub>s \<subseteq> {s\<^sub>s. wf_conf c\<^sub>s  s\<^sub>s} \<Longrightarrow>
               (\<Gamma>\<^sub>s \<Turnstile>\<^bsub>/F\<^esub> c\<^sub>s SAT [p\<^sub>s, R\<^sub>s, G\<^sub>s, q\<^sub>s,a\<^sub>s]) \<longrightarrow> (\<Gamma>\<^sub>c \<Turnstile>\<^bsub>/F\<^esub> c\<^sub>c SAT [p\<^sub>c, R\<^sub>c, G\<^sub>c, q\<^sub>c,a\<^sub>c])"  
proof -
  assume a0: "(\<Gamma>\<^sub>c,c\<^sub>c,R\<^sub>c,G\<^sub>c) \<succeq>\<^sub>p\<^sub>(\<^sub>\<alpha>\<^sub>;\<^sub>\<xi>\<^sub>\<rhd>\<^sub>\<gamma>\<^sub>q\<^sub>;\<^sub>\<gamma>\<^sub>a\<^sub>) (\<Gamma>\<^sub>s,c\<^sub>s,R\<^sub>s,G\<^sub>s)" and         
         a1: " p\<^sub>c \<subseteq> Domain \<xi> \<and>  ( \<xi> `` p\<^sub>c \<subseteq> p\<^sub>s)" and 
         a1':"\<gamma>qn = \<Down>\<^sub>i\<gamma>\<^sub>q \<and> q\<^sub>s \<subseteq> Domain \<gamma>qn \<and> ((\<gamma>qn `` q\<^sub>s) \<subseteq> q\<^sub>c) \<and>
               \<gamma>an = \<Down>\<^sub>i\<gamma>\<^sub>a \<and> a\<^sub>s \<subseteq> Domain \<gamma>an \<and> ((\<gamma>an `` a\<^sub>s) \<subseteq> a\<^sub>c) " and
 a5:"R\<^sub>c \<subseteq>  in_rel (R\<^sub>s\<^sup>*) \<alpha>" and a6:"\<forall>\<Sigma>. (\<Sigma>,\<Sigma>)\<in>R\<^sub>s" and a7:"R\<^sub>s \<subseteq> R_eq_locals" and 
 a8:"p\<^sub>s \<subseteq> {s\<^sub>s. wf_conf c\<^sub>s  s\<^sub>s}"
  {
    assume b0:"\<Gamma>\<^sub>s \<Turnstile>\<^bsub>/F\<^esub> c\<^sub>s SAT [p\<^sub>s, R\<^sub>s, G\<^sub>s, q\<^sub>s,a\<^sub>s]" 
    then have "\<Gamma>\<^sub>c \<Turnstile>\<^bsub>/F\<^esub> c\<^sub>c SAT [p\<^sub>c, R\<^sub>c, G\<^sub>c, q\<^sub>c,a\<^sub>c]"
    proof-
      {fix s\<^sub>c l
        assume c0:"l\<in> par_cp \<Gamma>\<^sub>c c\<^sub>c s\<^sub>c \<inter> par_assum(p\<^sub>c, R\<^sub>c)"
        then have"s\<^sub>c \<in> p\<^sub>c" 
          unfolding par_assum_def par_cp_def by auto   
        then obtain s\<^sub>s where 
           sa_sa'_xi:"(s\<^sub>c,s\<^sub>s)\<in>\<xi>" and
           sa'_normal:"s\<^sub>s \<in> p\<^sub>s" using a1 by force        
        have sim:"(\<Gamma>\<^sub>c,(c\<^sub>c,s\<^sub>c),R\<^sub>c,G\<^sub>c) \<succeq>\<^sub>p\<^sub>(\<^sub>\<alpha>\<^sub>;\<^sub>\<gamma>\<^sub>q\<^sub>;\<^sub>\<gamma>\<^sub>a\<^sub>) (\<Gamma>\<^sub>s,(c\<^sub>s, s\<^sub>s),R\<^sub>s,G\<^sub>s)" 
          using a0 sa_sa'_xi  unfolding RGSIM_p_pre_def by blast
        have wf:"wf_conf c\<^sub>s  s\<^sub>s" using a8 sa'_normal by auto
        have "l\<in>par_comm(G\<^sub>c, (q\<^sub>c,a\<^sub>c)) F" 
          using RG_SIM_fst_env_par_comm_ref[OF sim _  _ _ _  a5 a6 a7 wf, of \<gamma>qn q\<^sub>s q\<^sub>c \<gamma>an a\<^sub>s a\<^sub>c]  c0 a1 a1' 
            b0 SAT_e_eq par_comm_eq_par_comm\<^sub>e eq_par_cp\<^sub>e_par_cp sa'_normal 
          unfolding par_cp_def  by fast
      } thus ?thesis unfolding LocalRG_HoareDef.par_com_validity_def by auto
    qed      
  } thus ?thesis by auto
qed  
  
end
