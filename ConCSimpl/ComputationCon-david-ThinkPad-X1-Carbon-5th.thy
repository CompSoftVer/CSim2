theory ComputationCon imports "SmallStepCon"
begin
type_synonym ('g,'l) c_state = "('g\<times>'l)\<times>('l list)"
type_synonym ('g, 'l, 'p,'f,'e) config_gs = "('g\<times>'l,'p,'f,'e)com  \<times> (('g,'l) c_state,'f) xstate"

(* inductive 
      "step_e"::"[('g\<times>'l,'p,'f,'e) body,('g, 'l,  'p,'f,'e) config_gs,('g, 'l,  'p,'f,'e) config_gs] \<Rightarrow> bool"
                                ("_\<turnstile>\<^sub>c (_ \<rightarrow>\<^sub>e/ _)" [81,81,81] 100)  
  for \<Gamma>::"('g\<times>'l,'p,'f,'e) body"
where
Env:"(\<forall>ns'. t'\<noteq>Normal ns' \<or> (snd (fst ns) =snd (fst ns') \<and> 
            length (snd ns) = length (snd ns'))) \<Longrightarrow> 
      \<Gamma>\<turnstile>\<^sub>c (Ps, Normal ns) \<rightarrow>\<^sub>e (Ps, t')"
|Env_n: "(\<forall>ns. t\<noteq>Normal ns) \<Longrightarrow> \<Gamma>\<turnstile>\<^sub>c (Ps, t) \<rightarrow>\<^sub>e (Ps, t)"

 inductive 
      "step_e1"::"[('g\<times>'l,'p,'f,'e) body,('g, 'l,  'p,'f,'e) config_gs,('g, 'l,  'p,'f,'e) config_gs] \<Rightarrow> bool"
                                ("_\<turnstile>\<^sub>c (_ \<rightarrow>\<^sub>e\<^sub>1/ _)" [81,81,81] 100)  
  for \<Gamma>::"('g\<times>'l,'p,'f,'e) body"
where
Env1:"(\<forall>ns'. t'\<noteq>Normal ns') \<or> (\<exists>ns'. t'=Normal ns' \<and> (snd (fst ns) =snd (fst ns') \<and> 
            length (snd ns) = length (snd ns'))) \<Longrightarrow> 
      \<Gamma>\<turnstile>\<^sub>c (Ps, Normal ns) \<rightarrow>\<^sub>e\<^sub>1 (Ps, t')"
|Env_n1: "(\<forall>ns. t\<noteq>Normal ns) \<Longrightarrow> \<Gamma>\<turnstile>\<^sub>c (Ps, t) \<rightarrow>\<^sub>e\<^sub>1 (Ps, t)"

inductive 
      "step_e2"::"[('g\<times>'l,'p,'f,'e) body,('g, 'l,  'p,'f,'e) config_gs,('g, 'l,  'p,'f,'e) config_gs] \<Rightarrow> bool"
                                ("_\<turnstile>\<^sub>c (_ \<rightarrow>\<^sub>e\<^sub>2/ _)" [81,81,81] 100)  
  for \<Gamma>::"('g\<times>'l,'p,'f,'e) body"
where
Env:"(\<forall>ns'. t'\<noteq>Normal ns' \<or> t'\<noteq>Abrupt ns') \<or> 
            (\<exists>ns'. t'=Normal ns' \<and> snd (fst ns) =snd (fst ns') \<and> 
                               length (snd ns) = length (snd ns')) \<or> 
           (\<exists>ns'. t'=Abrupt ns' \<and> length (snd ns) = length (snd ns')) \<Longrightarrow> 
      \<Gamma>\<turnstile>\<^sub>c (Ps, Normal ns) \<rightarrow>\<^sub>e\<^sub>2 (Ps, t')"
|Env_n: "(\<forall>ns. t\<noteq>Normal ns) \<Longrightarrow> \<Gamma>\<turnstile>\<^sub>c (Ps, t) \<rightarrow>\<^sub>e\<^sub>2 (Ps, t)"

inductive 
      "step_e3"::"[('g\<times>'l,'p,'f,'e) body,('g, 'l,  'p,'f,'e) config_gs,('g, 'l,  'p,'f,'e) config_gs] \<Rightarrow> bool"
                                ("_\<turnstile>\<^sub>c (_ \<rightarrow>\<^sub>e\<^sub>3/ _)" [81,81,81] 100)  
  for \<Gamma>::"('g\<times>'l,'p,'f,'e) body"
where
Env:"(\<forall>ns'. (t'\<noteq>Normal ns' \<and> t'\<noteq>Abrupt ns') \<or> (t'=Normal ns' \<and> snd (fst ns) =snd (fst ns') \<and> 
            length (snd ns) = length (snd ns')) \<or> 
           (t'=Abrupt ns' \<and> length (snd ns) = length (snd ns'))) \<Longrightarrow> 
      \<Gamma>\<turnstile>\<^sub>c (Ps, Normal ns) \<rightarrow>\<^sub>e\<^sub>3 (Ps, t')"
|Env_n: "(\<forall>ns. t\<noteq>Normal ns) \<Longrightarrow> \<Gamma>\<turnstile>\<^sub>c (Ps, t) \<rightarrow>\<^sub>e\<^sub>3 (Ps, t)" *)

inductive 
      "step_e"::"[('g\<times>'l,'p,'f,'e) body,('g, 'l,  'p,'f,'e) config_gs,('g, 'l,  'p,'f,'e) config_gs] \<Rightarrow> bool"
                                ("_\<turnstile>\<^sub>c (_ \<rightarrow>\<^sub>e/ _)" [81,81,81] 100)  
  for \<Gamma>::"('g\<times>'l,'p,'f,'e) body"
where
Env:"(\<forall>ns'. (t'\<noteq>Normal ns' \<and> t'\<noteq>Abrupt ns') \<or> (t'=Normal ns' \<and> snd (fst ns) =snd (fst ns') \<and> 
            length (snd ns) = length (snd ns')) \<or> 
           (t'=Abrupt ns' \<and> length (snd ns) = length (snd ns'))) \<Longrightarrow> 
      \<Gamma>\<turnstile>\<^sub>c (Ps, Normal ns) \<rightarrow>\<^sub>e (Ps, t')"
|Env_n: "(\<forall>ns. t\<noteq>Normal ns) \<Longrightarrow> \<Gamma>\<turnstile>\<^sub>c (Ps, t) \<rightarrow>\<^sub>e (Ps, t)"

lemma "(\<forall>ns'. (t'\<noteq>Normal ns' \<and> t'\<noteq>Abrupt ns') \<or> (t'=Normal ns' \<longrightarrow> snd (fst ns) =snd (fst ns') \<and> 
            length (snd ns) = length (snd ns')) \<or> 
           (t'=Abrupt ns' \<longrightarrow> length (snd ns) = length (snd ns'))) = True"
  by auto

(* lemma "(\<forall>ns'. (t'\<noteq>Normal ns' \<and> t'\<noteq>Abrupt ns') \<or> (t'=Normal ns' \<and> snd (fst ns) =snd (fst ns') \<and> 
            length (snd ns) = length (snd ns')) \<or> 
           (t'=Abrupt ns' \<and> length (snd ns) = length (snd ns'))) = True"
  sorry  *)


lemma "(\<forall>ns'. t'\<noteq>Normal ns' \<or> t'\<noteq>Abrupt ns') \<or> 
            (\<exists>ns'. t'=Normal ns' \<and> snd (fst ns) =snd (fst ns') \<and> 
                               length (snd ns) = length (snd ns')) \<or> 
           (\<exists>ns'. t'=Abrupt ns' \<and> length (snd ns) = length (snd ns')) =
        (\<forall>ns'. t'\<noteq>Normal ns' \<or> t'\<noteq>Abrupt ns' \<or> (t'=Normal ns' \<longrightarrow> snd (fst ns) =snd (fst ns') \<and> 
            length (snd ns) = length (snd ns')) \<or> 
           (t'=Abrupt ns' \<longrightarrow> length (snd ns) = length (snd ns')))"
  by auto


lemma "(\<forall>ns'. t'\<noteq>Normal ns' \<or> (snd (fst ns) =snd (fst ns') \<and> 
            length (snd ns) = length (snd ns'))) = 
      (\<forall>ns'. t'\<noteq>Normal ns') \<or> (\<exists>ns'. t'=Normal ns' \<and> (snd (fst ns) =snd (fst ns') \<and> 
            length (snd ns) = length (snd ns')))"
  by auto

lemma etranE: "\<Gamma>\<turnstile>\<^sub>c c \<rightarrow>\<^sub>e c' \<Longrightarrow> (\<And>P s t. c = (P, s) \<Longrightarrow> c' = (P, t) \<Longrightarrow> Q) \<Longrightarrow> Q"
  by (induct c, induct c', erule  step_e.cases, blast)

inductive_cases stepe_Normal_elim_cases [cases set]:
 "\<Gamma>\<turnstile>\<^sub>c(Ps,Normal s) \<rightarrow>\<^sub>e (Ps,t)"

(* inductive_cases stepe1_Normal_elim_cases [cases set]:
 "\<Gamma>\<turnstile>\<^sub>c(Ps,Normal s) \<rightarrow>\<^sub>e\<^sub>1 (Ps,t)"

inductive_cases stepe2_Normal_elim_cases [cases set]:
 "\<Gamma>\<turnstile>\<^sub>c(Ps,Normal s) \<rightarrow>\<^sub>e\<^sub>2 (Ps,t)"

inductive_cases stepe3_Normal_elim_cases [cases set]:
 "\<Gamma>\<turnstile>\<^sub>c(Ps,Normal s) \<rightarrow>\<^sub>e\<^sub>3 (Ps,t)" *)

inductive_cases stepe_elim_cases [cases set]:
 "\<Gamma>\<turnstile>\<^sub>c(Ps,s) \<rightarrow>\<^sub>e (Ps,t)"

inductive_cases stepe_elim_cases_normal_abrupt [cases set]:
 "\<Gamma>\<turnstile>\<^sub>c(Ps,Normal s) \<rightarrow>\<^sub>e (Ps,Abrupt t)"

inductive_cases stepe_not_norm_elim_cases:
 "\<Gamma>\<turnstile>\<^sub>c(Ps,s) \<rightarrow>\<^sub>e (Ps,Abrupt t)"
 "\<Gamma>\<turnstile>\<^sub>c(Ps,s) \<rightarrow>\<^sub>e (Ps,Stuck)"
 "\<Gamma>\<turnstile>\<^sub>c(Ps,s) \<rightarrow>\<^sub>e (Ps,Fault t)"
 "\<Gamma>\<turnstile>\<^sub>c(Ps,s) \<rightarrow>\<^sub>e (Ps,Normal t)"

thm stepe_Normal_elim_cases

lemma env_c_c'_false:
   assumes step_m: "\<Gamma>\<turnstile>\<^sub>c (c, s) \<rightarrow>\<^sub>e (c', s')" 
   shows "~(c=c')  \<Longrightarrow> P"
using step_m etranE by blast

lemma eenv_normal_s'_normal_s:
   assumes step_m: "\<Gamma>\<turnstile>\<^sub>c (c, s) \<rightarrow>\<^sub>e (c', Normal s')" 
   shows "(\<And>s1. s\<noteq>Normal s1)  \<Longrightarrow> P"
  using step_m
  using env_c_c'_false stepe_not_norm_elim_cases(4) by blast

lemma eenv_eq_length:
  assumes step_m: "\<Gamma>\<turnstile>\<^sub>c (c, Normal s) \<rightarrow>\<^sub>e (c', Normal s')" and
          normal_s:"s= ((g,l),ls)" and normal_s':"s'= ((g',l'),ls')"
   shows "(length ls \<noteq> length ls')  \<Longrightarrow> P"
  using step_m normal_s normal_s'
  using env_c_c'_false stepe_Normal_elim_cases by fastforce

lemma env_normal_s'_normal_s:
   assumes step_m: "\<Gamma>\<turnstile>\<^sub>c (c, s) \<rightarrow>\<^sub>e (c', Normal s') " 
   shows "\<exists>s1. s= Normal s1"
  using step_m 
  using env_c_c'_false stepe_not_norm_elim_cases(4) by blast
  

lemma env_c_c':
   assumes step_m: "\<Gamma>\<turnstile>\<^sub>c (c, s) \<rightarrow>\<^sub>e (c', s')" 
   shows "(c=c')"
using env_c_c'_false step_m by fastforce 

lemma env_normal_s:
   assumes step_m: "\<Gamma>\<turnstile>\<^sub>c (c, s) \<rightarrow>\<^sub>e (c', s')" and s: "s\<noteq>s'" 
   shows "\<exists>sa. s = Normal sa"
using  stepe_elim_cases[OF step_m[simplified env_c_c'[OF step_m]]] s 
  by metis

lemma env_not_normal_s:
   assumes a1:"\<Gamma>\<turnstile>\<^sub>c (c, s) \<rightarrow>\<^sub>e (c', s')" and  a2:"(\<forall>t. s\<noteq>Normal t)" 
   shows "s=s'"
using a1 a2
  by (cases rule:step_e.cases,auto) 

lemma env_normal_same_local_length:
   assumes a1:"\<Gamma>\<turnstile>\<^sub>c (c, Normal ((g,l),ls)) \<rightarrow>\<^sub>e (c', Normal ((g',l'),ls'))" 
   shows "l=l' \<and> length ls = length ls'"
  using a1 
  by (cases rule:step_e.cases,auto)

lemma env_normal_same_local:
   assumes a1:"\<Gamma>\<turnstile>\<^sub>c (c, Normal ((g,l),ls)) \<rightarrow>\<^sub>e (c', Normal ((g',l'),ls'))" 
   shows "l=l'"
  using a1 env_normal_same_local_length
  by fast

lemma env_normal_same_length:
   assumes a1:"\<Gamma>\<turnstile>\<^sub>c (c, Normal ((g,l),ls)) \<rightarrow>\<^sub>e (c', Normal ((g',l'),ls'))" 
   shows "length ls = length ls'"
   using a1 env_normal_same_local_length
  by fast


lemma env_not_normal_s_not_norma_t:
   assumes a1:"\<Gamma>\<turnstile>\<^sub>c (c, s) \<rightarrow>\<^sub>e (c', s')" and  a2:"(\<forall>t. s\<noteq>Normal t)" 
   shows "(\<forall>t. s'\<noteq>Normal t)"
using a1 a2 env_not_normal_s
  by blast

lemma env_normal_intro:
  assumes a1:"length ls = length ls'"
  shows "\<Gamma>\<turnstile>\<^sub>c (c, Normal ((g,l),ls)) \<rightarrow>\<^sub>e (c, Normal ((g',l),ls'))"      
  using a1 by (auto intro: step_e.intros)

lemma env_abrupt_intro:
  assumes a1:"length ls = length ls'"
  shows "\<Gamma>\<turnstile>\<^sub>c (c, Normal ((g,l),ls)) \<rightarrow>\<^sub>e (c, Abrupt ((g',l),ls'))"      
  using a1 by (auto intro: step_e.intros)
thm  stepe_elim_cases_normal_abrupt
lemma env_len_ls:
  assumes a0: "\<Gamma>\<turnstile>\<^sub>c (c, s) \<rightarrow>\<^sub>e (c, Abrupt ((g',l),ls'))"
  shows "\<exists>sn. (s = Normal sn \<or> s =Abrupt sn) \<and> length (snd sn) = length ls'"
  using a0 
  by (auto elim: stepe_not_norm_elim_cases(1))

lemma env_intro:"\<Gamma>\<turnstile>\<^sub>c (P, s) \<rightarrow>\<^sub>e (P, t) \<Longrightarrow>
      \<Gamma>\<turnstile>\<^sub>c (Q, s) \<rightarrow>\<^sub>e (Q, t)"
  by (auto elim: stepe_elim_cases simp add: Env Env_n)
  
lemma stepe_not_Fault_f_end:
  assumes step_e: "\<Gamma>\<turnstile>\<^sub>c (c\<^sub>1, s) \<rightarrow>\<^sub>e (c\<^sub>1', s')"
  shows "s'\<notin> Fault ` f \<Longrightarrow> s \<notin> Fault ` f"
proof (cases s) 
  case (Fault f')
    assume s'_f:"s' \<notin> Fault ` f" and
           "s = Fault f'" 
    then have "s=s'" using step_e env_normal_s by blast  
  thus ?thesis using s'_f Fault by blast
qed (auto)


lemma snormal_enviroment:
   "(\<exists>nsa. s = Normal nsa \<and> (\<forall>nsa'. sa = Normal nsa' \<longrightarrow> snd (fst nsa) =snd (fst nsa') \<and> 
                                                  length (snd nsa) = length (snd nsa')) \<and>
                     (\<forall>nsa'. sa = Abrupt nsa' \<longrightarrow> length (snd nsa) = length (snd nsa'))) \<or> 
    (s = sa \<and> (\<forall>sa. s \<noteq> Normal sa)) \<Longrightarrow>
        \<Gamma>\<turnstile>\<^sub>c (x, s) \<rightarrow>\<^sub>e (x, sa)" 
  apply (cases s)
  apply (auto simp add: Env Env_n) apply (cases sa, auto)
  apply (simp add: env_normal_intro)
  by (cases s, auto simp add: Env Env_n) 

lemma not_step_c_env: 
"\<Gamma>\<turnstile>\<^sub>c (c, s) \<rightarrow>\<^sub>e (c, s') \<Longrightarrow> 
 (\<And>sa. \<not>(s=Normal sa)) \<Longrightarrow> 
  (\<And>sa. \<not>(s'=Normal sa))"  
  by (rule stepe_elim_cases, auto)


lemma step_c_env_not_normal_eq_state: 
"\<Gamma>\<turnstile>\<^sub>c (c, s) \<rightarrow>\<^sub>e (c, s') \<Longrightarrow> 
 (\<And>sa. \<not>(s=Normal sa)) \<Longrightarrow> 
  s=s'"
by (fastforce elim:stepe_elim_cases)

 
definition final_glob:: "('g,'l,'p,'f,'e) config_gs \<Rightarrow> bool" where
  "final_glob cfg \<equiv>   (fst cfg=Skip \<or> ((fst cfg=Throw) \<and> (\<exists>s. snd cfg=Normal s)))"
                                           
lemma final_eq:"snd cfg = Normal s \<Longrightarrow> final_glob cfg = SmallStepCon.final (fst cfg, Normal (fst s))"
  unfolding final_def final_glob_def SmallStepCon.final_def
  by auto


section \<open> computation with enviroment \<close>

primrec toSeq ::"(('g\<times>'l)\<times>('l list),'f) xstate \<Rightarrow> (('g\<times>'l),'f) xstate"
  where
"toSeq (Normal ns) = Normal (fst ns)"
|"toSeq (Abrupt ns) = Abrupt (fst ns)"
|"toSeq (Fault f) = Fault f"
|"toSeq Stuck = Stuck"

lemma 
  assumes 
    a0:"\<forall>ns ns'. (s = Normal ns \<or> s = Abrupt ns) \<and> (s' = Normal ns' \<or> s' = Abrupt ns') \<longrightarrow> 
       snd ns = snd ns'" and 
    a1:"toSeq s = toSeq s'"
  shows eq_toSeq:"s = s'" using a0 a1
  apply (cases s)
  by (cases s', auto)+

lemma toSeq_not_in_fault: "s \<notin> Fault ` f = (toSeq s \<notin> Fault ` f)"
  by (cases s, auto)

lemma toSeq_not_stuck: "s \<noteq> Stuck = (toSeq s \<noteq> Stuck)"
  by (cases s, auto)

lemma toSeq_not_fault: "(\<forall>f. s\<noteq> Fault f) = (\<forall>f. toSeq s \<noteq> Fault f)"
  by (cases s, auto)

lemma toSeq_not_Normal: "(\<forall>na. s\<noteq> Normal na) = (\<forall>na. toSeq s \<noteq> Normal na)"
  by (cases s, auto)

lemma toSeq_not_abrupt: "(\<forall>na. s\<noteq> Abrupt na) = (\<forall>na. toSeq s \<noteq> Abrupt na)"
  by (cases s, auto)



inductive
      "step_ce"::"[('g\<times>'l,'p,'f,'e) body,('g, 'l, 'p,'f,'e) config_gs,('g, 'l, 'p,'f,'e) config_gs] \<Rightarrow> bool"
                                ("_\<turnstile>\<^sub>c (_ \<rightarrow>\<^sub>c\<^sub>e/ _)" [81,81,81] 100)  
  for \<Gamma>::"('g\<times>'l,'p,'f,'e) body"
  where
c_step: "\<lbrakk>\<Gamma>\<turnstile>\<^sub>c (c, (toSeq s)) \<rightarrow> (c', toSeq s'); 
         \<forall>ns ns'. 
              (s = Normal ns \<or> s = Abrupt ns) \<and> 
              (s' = Normal ns' \<or> s' = Abrupt ns') \<longrightarrow> snd ns = snd ns'\<rbrakk> \<Longrightarrow> 
         \<Gamma>\<turnstile>\<^sub>c (c,s) \<rightarrow>\<^sub>c\<^sub>e (c',s')"
|e_step: "\<Gamma>\<turnstile>\<^sub>c (c,s) \<rightarrow>\<^sub>e (c',s') \<Longrightarrow> \<Gamma>\<turnstile>\<^sub>c (c,s) \<rightarrow>\<^sub>c\<^sub>e (c',s') " 


(* inductive
      "step_ce"::"[('g\<times>'l,'p,'f,'e) body,('g, 'l, 'p,'f,'e) config_gs,('g, 'l, 'p,'f,'e) config_gs] \<Rightarrow> bool"
                                ("_\<turnstile>\<^sub>c (_ \<rightarrow>\<^sub>c\<^sub>e/ _)" [81,81,81] 100)  
  for \<Gamma>::"('g\<times>'l,'p,'f,'e) body"
  where
c_stepN: "\<Gamma>\<turnstile>\<^sub>c ((c, (Normal l::(('g\<times>'l),'f) xstate))) \<rightarrow> (c', Normal l') \<Longrightarrow> 
          \<Gamma>\<turnstile>\<^sub>c (c,Normal (l,ls)) \<rightarrow>\<^sub>c\<^sub>e (c',Normal (l',ls))"
|c_stepA: "\<Gamma>\<turnstile>\<^sub>c ((c, (Normal l::(('g\<times>'l),'f) xstate))) \<rightarrow> (c', Abrupt l') \<Longrightarrow> 
          \<Gamma>\<turnstile>\<^sub>c (c,Normal (l,ls)) \<rightarrow>\<^sub>c\<^sub>e (c',Abrupt (l',ls))"
|c_stepF: "\<Gamma>\<turnstile>\<^sub>c ((c, (Normal l::(('g\<times>'l),'f) xstate))) \<rightarrow> (c', Fault F ) \<Longrightarrow> 
          \<Gamma>\<turnstile>\<^sub>c (c,Normal (l,ls)) \<rightarrow>\<^sub>c\<^sub>e (c',Fault F)"
|c_stuck: "\<Gamma>\<turnstile>\<^sub>c ((c, (Normal l::(('g\<times>'l),'f) xstate))) \<rightarrow> (c', Stuck) \<Longrightarrow> 
          \<Gamma>\<turnstile>\<^sub>c (c,Normal (l,ls)) \<rightarrow>\<^sub>c\<^sub>e (c',Stuck)"
|c_stuck': "\<Gamma>\<turnstile>\<^sub>c ((c,Stuck)) \<rightarrow> (c', s') \<Longrightarrow> 
          \<Gamma>\<turnstile>\<^sub>c (c,Stuck) \<rightarrow>\<^sub>c\<^sub>e (c',Stuck)"
|c_F: "\<Gamma>\<turnstile>\<^sub>c ((c,Fault F)) \<rightarrow> (c', Fault F) \<Longrightarrow> 
          \<Gamma>\<turnstile>\<^sub>c (c,Fault F) \<rightarrow>\<^sub>c\<^sub>e (c',Fault F)"
|c_a: "\<Gamma>\<turnstile>\<^sub>c ((c, (Abrupt l::(('g\<times>'l),'f) xstate))) \<rightarrow> (c', Abrupt l) \<Longrightarrow> 
          \<Gamma>\<turnstile>\<^sub>c (c,Abrupt (l,ls)) \<rightarrow>\<^sub>c\<^sub>e (c',Abrupt (l,ls))"
|e_step: "\<Gamma>\<turnstile>\<^sub>c (c,s) \<rightarrow>\<^sub>e (c',s') \<Longrightarrow> \<Gamma>\<turnstile>\<^sub>c (c,s) \<rightarrow>\<^sub>c\<^sub>e (c',s') "
*)

lemmas step_ce_induct = step_ce.induct [of _ "(c,s)" "(c',s')", split_format (complete), case_names
c_step e_step, induct set]

           
inductive_cases step_ce_elim_cases [cases set]:
 "\<Gamma>\<turnstile>\<^sub>c cf0 \<rightarrow>\<^sub>c\<^sub>e cf1"

inductive_cases step_ce_elim_cases1 [cases set]:
 "\<Gamma>\<turnstile>\<^sub>c (c,Normal (g,l)) \<rightarrow>\<^sub>c\<^sub>e (c',Normal (g',l'))"
 "\<Gamma>\<turnstile>\<^sub>c (c,Normal (g,l)) \<rightarrow>\<^sub>c\<^sub>e (c',Abrupt(g',l'))"
 "\<Gamma>\<turnstile>\<^sub>c (c,Normal (g,l)) \<rightarrow>\<^sub>c\<^sub>e (c',Fault f)"
 "\<Gamma>\<turnstile>\<^sub>c (c,Normal (g,l)) \<rightarrow>\<^sub>c\<^sub>e (c',Stuck)"
 "\<Gamma>\<turnstile>\<^sub>c (c,Abrupt (g,l)) \<rightarrow>\<^sub>c\<^sub>e (c',Normal (g',l'))"
 "\<Gamma>\<turnstile>\<^sub>c (c,Abrupt (g,l)) \<rightarrow>\<^sub>c\<^sub>e (c',Stuck)"
 "\<Gamma>\<turnstile>\<^sub>c (c,Abrupt (g,l)) \<rightarrow>\<^sub>c\<^sub>e (c',Abrupt (g',l'))"

thm step_ce_elim_cases1 step_ce_elim_cases

lemma step_ce_elim_casesA1[cases set,elim]:
"\<lbrakk>\<Gamma>\<turnstile>\<^sub>c (c, Normal (g, l)) \<rightarrow>\<^sub>c\<^sub>e (c', Normal (g', l'));
  \<lbrakk>\<Gamma>\<turnstile>\<^sub>c (c, (Normal g)) \<rightarrow> (c', (Normal g')); l=l' \<rbrakk> \<Longrightarrow> P;
 \<Gamma>\<turnstile>\<^sub>c (c, Normal (g, l)) \<rightarrow>\<^sub>e (c', Normal (g', l')) \<Longrightarrow> P\<rbrakk>
\<Longrightarrow> P" 
  by (auto elim: step_ce_elim_cases) 

lemma step_ce_elim_casesA2[cases set,elim]:
"\<lbrakk>\<Gamma>\<turnstile>\<^sub>c (c, Normal (g, l)) \<rightarrow>\<^sub>c\<^sub>e (c', Abrupt (g', l'));
  \<lbrakk>\<Gamma>\<turnstile>\<^sub>c (c, (Normal g)) \<rightarrow> (c', (Abrupt g')); l=l' \<rbrakk> \<Longrightarrow> P;
 \<lbrakk>\<Gamma>\<turnstile>\<^sub>c (c, Normal (g, l)) \<rightarrow>\<^sub>e (c', Abrupt (g', l'))\<rbrakk> \<Longrightarrow> P\<rbrakk>
\<Longrightarrow> P" 
  by (auto elim: step_ce_elim_cases) 

lemma step_ce_elim_casesA3[cases set,elim]:
"\<lbrakk>\<Gamma>\<turnstile>\<^sub>c (c, Normal (g, l)) \<rightarrow>\<^sub>c\<^sub>e (c', Stuck);
  \<lbrakk>\<Gamma>\<turnstile>\<^sub>c (c, (Normal g)) \<rightarrow> (c', Stuck)\<rbrakk> \<Longrightarrow> P;
 \<Gamma>\<turnstile>\<^sub>c (c, Normal (g, l)) \<rightarrow>\<^sub>e (c', Stuck) \<Longrightarrow> P\<rbrakk>
\<Longrightarrow> P" 
  by (auto elim: step_ce_elim_cases) 

lemma step_ce_elim_casesA4[cases set,elim]:
"\<lbrakk>\<Gamma>\<turnstile>\<^sub>c (c, Normal (g, l)) \<rightarrow>\<^sub>c\<^sub>e (c', Fault f);
  \<lbrakk>\<Gamma>\<turnstile>\<^sub>c (c, (Normal g)) \<rightarrow> (c', Fault f)\<rbrakk> \<Longrightarrow> P;
 \<Gamma>\<turnstile>\<^sub>c (c, Normal (g, l)) \<rightarrow>\<^sub>e (c', Fault f) \<Longrightarrow> P\<rbrakk>
\<Longrightarrow> P" 
  by (auto elim: step_ce_elim_cases) 

lemma step_ce_elim_casesA5[cases set,elim]:
"\<lbrakk>\<Gamma>\<turnstile>\<^sub>c (c, Abrupt (g, l)) \<rightarrow>\<^sub>c\<^sub>e (c', Abrupt (g', l'));
  \<lbrakk>\<Gamma>\<turnstile>\<^sub>c (c, (Abrupt g)) \<rightarrow> (c', (Abrupt g')); l=l' \<rbrakk> \<Longrightarrow> P;
 \<Gamma>\<turnstile>\<^sub>c (c, Abrupt (g, l)) \<rightarrow>\<^sub>e (c', Abrupt (g', l')) \<Longrightarrow> P\<rbrakk>
\<Longrightarrow> P" 
  by (auto elim: step_ce_elim_cases) 

lemma step_ce_elim_casesA6[cases set,elim]:
"\<lbrakk>\<Gamma>\<turnstile>\<^sub>c (c, Abrupt (g, l)) \<rightarrow>\<^sub>c\<^sub>e (c', Normal (g', l'));
  \<lbrakk>\<Gamma>\<turnstile>\<^sub>c (c, (Abrupt g)) \<rightarrow> (c', Normal g'); l=l'\<rbrakk> \<Longrightarrow> P;
 \<Gamma>\<turnstile>\<^sub>c (c, Abrupt (g, l)) \<rightarrow>\<^sub>e (c', Normal (g', l')) \<Longrightarrow> P\<rbrakk>
\<Longrightarrow> P" 
  by (auto elim: step_ce_elim_cases) 

lemma step_ce_elim_casesA7[cases set,elim]:
"\<lbrakk>\<Gamma>\<turnstile>\<^sub>c (c, Abrupt (g, l)) \<rightarrow>\<^sub>c\<^sub>e (c', Fault f);
  \<lbrakk>\<Gamma>\<turnstile>\<^sub>c (c, (Abrupt g)) \<rightarrow> (c', Fault f)\<rbrakk> \<Longrightarrow> P;
 \<Gamma>\<turnstile>\<^sub>c (c, Abrupt (g, l)) \<rightarrow>\<^sub>e (c', Fault f) \<Longrightarrow> P\<rbrakk>
\<Longrightarrow> P" 
  by (auto elim: step_ce_elim_cases) 

lemma step_ce_elim_casesA8[cases set,elim]:
"\<lbrakk>\<Gamma>\<turnstile>\<^sub>c (c, Abrupt (g, l)) \<rightarrow>\<^sub>c\<^sub>e (c', Stuck);
  \<lbrakk>\<Gamma>\<turnstile>\<^sub>c (c, (Abrupt g)) \<rightarrow> (c', Stuck)\<rbrakk> \<Longrightarrow> P;
 \<Gamma>\<turnstile>\<^sub>c (c, Abrupt (g, l)) \<rightarrow>\<^sub>e (c', Stuck) \<Longrightarrow> P\<rbrakk>
\<Longrightarrow> P" 
  by (auto elim: step_ce_elim_cases) 

lemma step_ce_elim_casesA9[cases set,elim]:
"\<lbrakk>\<Gamma>\<turnstile>\<^sub>c (c, Fault f) \<rightarrow>\<^sub>c\<^sub>e (c', Fault f);
  \<lbrakk>\<Gamma>\<turnstile>\<^sub>c (c, Fault f) \<rightarrow> (c', Fault f)\<rbrakk> \<Longrightarrow> P;
 \<Gamma>\<turnstile>\<^sub>c (c, Fault f) \<rightarrow>\<^sub>e (c', Fault f) \<Longrightarrow> P\<rbrakk>
\<Longrightarrow> P" 
  by (auto elim: step_ce_elim_cases) 

lemma step_ce_elim_casesA10[cases set,elim]:
"\<lbrakk>\<Gamma>\<turnstile>\<^sub>c (c, Fault f) \<rightarrow>\<^sub>c\<^sub>e (c', Stuck);
  \<lbrakk>\<Gamma>\<turnstile>\<^sub>c (c, Fault f) \<rightarrow> (c', Stuck)\<rbrakk> \<Longrightarrow> P;
 \<Gamma>\<turnstile>\<^sub>c (c, Fault f) \<rightarrow>\<^sub>e (c', Stuck) \<Longrightarrow> P\<rbrakk>
\<Longrightarrow> P" 
  by (auto elim: step_ce_elim_cases) 

lemma step_ce_elim_casesA11[cases set,elim]:
"\<lbrakk>\<Gamma>\<turnstile>\<^sub>c (c, Fault f) \<rightarrow>\<^sub>c\<^sub>e (c', Normal (g,l));
  \<lbrakk>\<Gamma>\<turnstile>\<^sub>c (c, Fault f) \<rightarrow> (c', Normal g)\<rbrakk> \<Longrightarrow> P;
 \<Gamma>\<turnstile>\<^sub>c (c, Fault f) \<rightarrow>\<^sub>e (c', Normal (g,l)) \<Longrightarrow> P\<rbrakk>
\<Longrightarrow> P" 
  by (auto elim: step_ce_elim_cases)

lemma step_ce_elim_casesA12[cases set,elim]:
"\<lbrakk>\<Gamma>\<turnstile>\<^sub>c (c, Fault f) \<rightarrow>\<^sub>c\<^sub>e (c', Abrupt (g,l));
  \<lbrakk>\<Gamma>\<turnstile>\<^sub>c (c, Fault f) \<rightarrow> (c', Abrupt g)\<rbrakk> \<Longrightarrow> P;
 \<Gamma>\<turnstile>\<^sub>c (c, Fault f) \<rightarrow>\<^sub>e (c', Abrupt (g,l)) \<Longrightarrow> P\<rbrakk>
\<Longrightarrow> P" 
  by (auto elim: step_ce_elim_cases)

lemma step_ce_elim_casesA13[cases set,elim]:
"\<lbrakk>\<Gamma>\<turnstile>\<^sub>c (c, Stuck) \<rightarrow>\<^sub>c\<^sub>e (c', Fault f);
  \<lbrakk>\<Gamma>\<turnstile>\<^sub>c (c, Stuck) \<rightarrow> (c', Fault f)\<rbrakk> \<Longrightarrow> P;
 \<Gamma>\<turnstile>\<^sub>c (c, Stuck) \<rightarrow>\<^sub>e (c', Fault f) \<Longrightarrow> P\<rbrakk>
\<Longrightarrow> P" 
  by (auto elim: step_ce_elim_cases) 

lemma step_ce_elim_casesA14[cases set,elim]:
"\<lbrakk>\<Gamma>\<turnstile>\<^sub>c (c, Stuck) \<rightarrow>\<^sub>c\<^sub>e (c', Stuck);
  \<lbrakk>\<Gamma>\<turnstile>\<^sub>c (c, Stuck) \<rightarrow> (c', Stuck)\<rbrakk> \<Longrightarrow> P;
 \<Gamma>\<turnstile>\<^sub>c (c, Stuck) \<rightarrow>\<^sub>e (c', Stuck) \<Longrightarrow> P\<rbrakk>
\<Longrightarrow> P" 
  by (auto elim: step_ce_elim_cases) 

lemma step_ce_elim_casesA15[cases set,elim]:
"\<lbrakk>\<Gamma>\<turnstile>\<^sub>c (c, Stuck) \<rightarrow>\<^sub>c\<^sub>e (c', Normal (g,l));
  \<lbrakk>\<Gamma>\<turnstile>\<^sub>c (c, Stuck) \<rightarrow> (c', Normal g)\<rbrakk> \<Longrightarrow> P;
 \<Gamma>\<turnstile>\<^sub>c (c, Stuck) \<rightarrow>\<^sub>e (c', Normal (g,l)) \<Longrightarrow> P\<rbrakk> 
\<Longrightarrow> P" 
  by (auto elim: step_ce_elim_cases)

lemma step_ce_elim_casesA16:
"\<lbrakk>\<Gamma>\<turnstile>\<^sub>c (c, Stuck) \<rightarrow>\<^sub>c\<^sub>e (c', Abrupt (g,l));
  \<lbrakk>\<Gamma>\<turnstile>\<^sub>c (c, Stuck) \<rightarrow> (c', Abrupt g)\<rbrakk> \<Longrightarrow> P;
 \<Gamma>\<turnstile>\<^sub>c (c, Stuck) \<rightarrow>\<^sub>e (c', Abrupt (g,l)) \<Longrightarrow> P\<rbrakk>
\<Longrightarrow> P" 
  by (auto elim: step_ce_elim_cases)



lemma step_dest:
  assumes a0:"\<Gamma>\<turnstile>\<^sub>c(P,Normal s) \<rightarrow>\<^sub>c\<^sub>e (Q,t)"
  shows "\<Gamma>\<turnstile>\<^sub>c(P,Normal s) \<rightarrow>\<^sub>e (Q,t) \<or> 
        (\<Gamma>\<turnstile>\<^sub>c (P, toSeq (Normal s)) \<rightarrow> (Q, toSeq t) \<and> (\<forall>t'. t= Normal t' \<or> t = Abrupt t' \<longrightarrow>  (snd s) =  (snd t')))"   
  using a0 apply clarsimp
  apply (erule step_ce_elim_cases)   
  apply auto  
  by (metis (no_types) surjective_pairing)+

lemma step_dest1:
  assumes a0:"\<Gamma>\<turnstile>\<^sub>c(P,Normal s) \<rightarrow>\<^sub>c\<^sub>e (Q,t)" and
  a1:"\<Gamma>\<turnstile>\<^sub>c (P, toSeq (Normal s)) \<rightarrow> (Q, toSeq t)"
shows"(\<forall>t'. t= Normal t' \<or> t = Abrupt t' \<longrightarrow>  (snd s) =  (snd t'))"   
  using a0 a1 apply clarsimp
  apply (erule step_ce_elim_cases)   
  apply auto
  apply (metis (no_types) prod.exhaust_sel)+
  using a1 env_c_c' step_change_p_or_eq_s by blast+ 
  

lemma transfer_normal:"
      \<Gamma>\<turnstile>\<^sub>c (c, Normal s) \<rightarrow> (c', Normal s') \<Longrightarrow>
      \<Gamma>\<turnstile>\<^sub>c (c, Normal (s, ls)) \<rightarrow>\<^sub>c\<^sub>e (c', Normal (s', ls))"  
  by (auto intro: c_step)
  
lemma step_c_normal_normal: assumes a1: "\<Gamma>\<turnstile>\<^sub>c cf0 \<rightarrow> cf1"
      shows "\<And> c\<^sub>1 s s'. \<lbrakk>cf0 = (c\<^sub>1,Normal s);cf1=(c\<^sub>1,s');(\<forall>sa. \<not>(s'=Normal sa))\<rbrakk>
          \<Longrightarrow> P"
using a1 
by (induct rule: stepc.induct, induct, auto)


lemma normal_not_normal_eq_p: 
  assumes a1: "\<Gamma>\<turnstile>\<^sub>c (cf0) \<rightarrow>\<^sub>c\<^sub>e cf1"
  shows "\<And> c\<^sub>1 s s'. \<lbrakk>cf0 = (c\<^sub>1,Normal s);cf1=(c\<^sub>1,s');(\<forall>sa. \<not>(s'=Normal sa))\<rbrakk>
          \<Longrightarrow> \<Gamma>\<turnstile>\<^sub>c cf0 \<rightarrow>\<^sub>e cf1 \<and> \<not>( \<Gamma>\<turnstile>\<^sub>c (c\<^sub>1, toSeq (Normal s)) \<rightarrow> (c\<^sub>1, toSeq s'))"  
  apply (meson step_c_normal_normal step_e.intros )
   using Env apply (metis assms step_dest )
   by (simp add: mod_env_not_component step_dest)              

lemma call_f_step_ce_not_s_eq_t_env_step:
  assumes 
     a0:"\<Gamma>\<turnstile>\<^sub>c(P,s) \<rightarrow>\<^sub>c\<^sub>e (Q,t)" and
     a1:"(redex P = Call fn \<and> \<Gamma> fn = Some bdy \<and> s=Normal s' \<and> (s\<noteq>t)) \<or>
         (redex P = Call fn \<and> \<Gamma> fn = Some bdy \<and> s=Normal s' \<and> s=t \<and> P=Q \<and> \<Gamma> fn \<noteq> Some (Call fn)) "
   shows "\<Gamma>\<turnstile>\<^sub>c(P,s) \<rightarrow>\<^sub>e (Q,t)"
proof-  
  obtain s' where "\<Gamma>\<turnstile>\<^sub>c(P,s) \<rightarrow>\<^sub>e (Q,t) \<or> (s=Normal s' \<and> \<Gamma>\<turnstile>\<^sub>c (P, toSeq (Normal s')) \<rightarrow> (Q, toSeq t) \<and> 
       (\<forall>t'. t= Normal t' \<longrightarrow> (snd s') = (snd t')))" 
    using step_dest a0 a1
    by fast
  moreover {assume "\<Gamma>\<turnstile>\<^sub>c(P,s) \<rightarrow>\<^sub>e (Q,t)"
    then have ?thesis by auto
  }
  moreover {
    assume a00:"s=Normal s'" and a01:"\<Gamma>\<turnstile>\<^sub>c (P, toSeq (Normal s')) \<rightarrow> (Q, toSeq t)" and 
       a02:"(\<forall>t'. t= Normal t' \<longrightarrow> (snd s') = (snd t'))"
    then have ?thesis  using  call_f_step_not_s_eq_t_false[OF a01] a1
      apply (cases t)
      apply (metis prod.expand toSeq.simps(1) xstate.inject(1))                  
      by fastforce+      
  }                                        
  ultimately show ?thesis by auto
qed 

abbreviation 
 "stepce_rtrancl" :: "[('g\<times>'l,'p,'f,'e) body,('g, 'l, 'p,'f,'e) config_gs,('g, 'l, 'p,'f,'e) config_gs] \<Rightarrow> bool"
                                ("_\<turnstile>\<^sub>c (_ \<rightarrow>\<^sub>c\<^sub>e\<^sup>*/ _)" [81,81,81] 100)
 where                                
  "\<Gamma>\<turnstile>\<^sub>c cf0 \<rightarrow>\<^sub>c\<^sub>e\<^sup>* cf1 \<equiv> ((CONST step_ce \<Gamma>))\<^sup>*\<^sup>* cf0 cf1" 
  (* "\<Gamma>\<turnstile>\<^sub>c cf0 \<rightarrow>\<^sup>* cf1 \<equiv> (CONST ((stepc \<Gamma>) \<union> (step_e \<Gamma>)))\<^sup>*\<^sup>* cf0 cf1" *)

abbreviation 
 "stepce_trancl" :: "[('g\<times>'l,'p,'f,'e) body,('g, 'l, 'p,'f,'e) config_gs,('g, 'l, 'p,'f,'e) config_gs] \<Rightarrow> bool"
                                ("_\<turnstile>\<^sub>c (_ \<rightarrow>\<^sub>c\<^sub>e\<^sup>+/ _)" [81,81,81] 100)
 where
  "\<Gamma>\<turnstile>\<^sub>c cf0 \<rightarrow>\<^sub>c\<^sub>e\<^sup>+ cf1 \<equiv> (CONST step_ce \<Gamma>)\<^sup>+\<^sup>+ cf0 cf1"

text \<open> lemmas about single step computation \<close> 

lemma ce_not_normal_s:
   assumes a1:"\<Gamma>\<turnstile>\<^sub>c cf0 \<rightarrow>\<^sub>c\<^sub>e cf1"
   shows "\<And> c\<^sub>1 c\<^sub>2 s s'. \<lbrakk>cf0 = (c\<^sub>1,s);cf1=(c\<^sub>2,s');(\<forall>sa. (s\<noteq>Normal sa))\<rbrakk>
                     \<Longrightarrow> s=s'"
using a1
  apply (clarify, cases rule:step_ce.cases)  
  apply (metis eq_toSeq prod.sel(1) prod.sel(2) step_not_normal_s_eq_t toSeq.simps xstate.simps(5))
  using env_not_normal_s by blast

lemma not_eq_not_env:
   assumes step_m: "\<Gamma>\<turnstile>\<^sub>c (c, s) \<rightarrow>\<^sub>c\<^sub>e (c', s')" 
   shows "~(c=c') \<Longrightarrow> \<Gamma>\<turnstile>\<^sub>c (c, s) \<rightarrow>\<^sub>e (c', s') \<Longrightarrow> P"
using step_m etranE by blast


lemma step_ce_not_step_e_step_c:
   assumes step_m: "\<Gamma>\<turnstile>\<^sub>c (c, s) \<rightarrow>\<^sub>c\<^sub>e (c', s')" 
   shows "\<not> (\<Gamma>\<turnstile>\<^sub>c (c, s) \<rightarrow>\<^sub>e (c', s')) \<Longrightarrow>(\<Gamma>\<turnstile>\<^sub>c (c, toSeq s) \<rightarrow> (c', toSeq s'))"
  using step_m  step_ce_elim_cases by blast

lemma step_ce_step_c_eq_c:
assumes step_m: "\<Gamma>\<turnstile>\<^sub>c (c, s) \<rightarrow>\<^sub>c\<^sub>e (c', s')" 
   shows "(\<Gamma>\<turnstile>\<^sub>c (c, toSeq s) \<rightarrow> (c', toSeq s')) \<Longrightarrow> c=c' \<Longrightarrow> P"
  using step_m  step_ce_elim_cases step_ce_not_step_e_step_c
  by (simp add: mod_env_not_component)

lemma step_ce_notNormal:   
   assumes step_m: "\<Gamma>\<turnstile>\<^sub>c (c, s) \<rightarrow>\<^sub>c\<^sub>e (c', s')" 
   shows "(\<forall>sa. \<not>(s=Normal sa)) \<Longrightarrow> s'=s"
using step_m
proof (induct rule:step_ce_induct) 
  case (e_step a b a' b')
  thus ?case
    using env_not_normal_s by blast
next
  case (c_step a b a' b')
  thus ?case
    using ce_not_normal_s step_ce.c_step by blast
qed

lemma steps_ce_not_Normal:  
   assumes step_m: "\<Gamma>\<turnstile>\<^sub>c (c, s) \<rightarrow>\<^sub>c\<^sub>e\<^sup>* (c', s')" 
   shows "\<forall>sa. \<not>(s=Normal sa) \<Longrightarrow> s'=s"
using step_m
proof (induct rule: converse_rtranclp_induct2 [case_names Refl Trans])
  case Refl then show ?case by auto
next
  case (Trans a b a' b') 
  thus ?case using step_ce_notNormal by blast 
qed

lemma step_ce_Normal_eq_l:   
  assumes step_m: "\<Gamma>\<turnstile>\<^sub>c (c, Normal (s,l)) \<rightarrow>\<^sub>c\<^sub>e (c', Normal (s',l'))" and
          step_ce:"\<Gamma>\<turnstile>\<^sub>c (c, Normal s) \<rightarrow> (c', Normal s')"
   shows "l=l'"  
  by (metis  env_c_c' mod_env_not_component snd_conv step_ce step_dest step_m)

lemma step_ce_dest:   
  assumes step_m: "\<Gamma>\<turnstile>\<^sub>c (c, s) \<rightarrow>\<^sub>c\<^sub>e (c', s')" 
  shows "\<Gamma>\<turnstile>\<^sub>c (c, toSeq s) \<rightarrow> (c', toSeq s') \<or> \<Gamma>\<turnstile>\<^sub>c (c, s) \<rightarrow>\<^sub>e (c', s')"
  using step_ce_not_step_e_step_c step_m by blast


lemma steps_not_normal_ce_c: 
  assumes steps: "\<Gamma>\<turnstile>\<^sub>c (c, s) \<rightarrow>\<^sub>c\<^sub>e\<^sup>* (c', s')"
  shows         "( \<forall>sa. \<not>(s=Normal sa)) \<Longrightarrow> \<Gamma>\<turnstile>\<^sub>c (c, toSeq s) \<rightarrow>\<^sup>* (c', toSeq s')"
using steps
proof (induct rule: converse_rtranclp_induct2 [case_names Refl Trans])
  case Refl thus ?case by auto
next
  case (Trans a b a' b') then show ?case 
    by (metis (no_types, hide_lams) converse_rtranclp_into_rtranclp env_c_c' 
           step_ce_notNormal step_ce_not_step_e_step_c)
qed

lemma ce_eq_length: assumes a0:"\<Gamma>\<turnstile>\<^sub>c (P,s) \<rightarrow>\<^sub>c\<^sub>e (Q,t)" and
              a1:"s= Normal ns \<or> s = Abrupt ns" and
              a2:"t = Normal nt \<or> t = Abrupt nt"
            shows "length (snd ns) = length (snd nt)"
proof-
  have "\<Gamma>\<turnstile>\<^sub>c (P,s) \<rightarrow>\<^sub>e (Q,t) \<or> \<Gamma>\<turnstile>\<^sub>c (P, toSeq s) \<rightarrow> (Q, toSeq t)"    
    using a0 step_ce_dest by blast
  moreover{ 
    assume a00:"\<Gamma>\<turnstile>\<^sub>c (P,s) \<rightarrow>\<^sub>e (Q,t)"
    then have eq_p:"P=Q"
      using env_c_c' by blast
    then have ?thesis using a00 stepe_elim_cases[OF a00[simplified eq_p]]
      by (metis a1 a2 prod.exhaust_sel xstate.inject(1) xstate.inject(2) xstate.simps(5))
  }
  moreover{
    assume a00:" \<Gamma>\<turnstile>\<^sub>c (P, toSeq s) \<rightarrow> (Q, toSeq t)"
    then have ?thesis
      by (metis a0 a1 a2 calculation(2) step_ce_notNormal 
           step_dest xstate.inject(2) xstate.simps(5))
  } ultimately show ?thesis by auto
qed

(* lemma steps_c_ce: 
  assumes steps: "\<Gamma>\<turnstile>\<^sub>c (c, s1) \<rightarrow>\<^sup>* (c', s2)" and
          a0:"s1 = toSeq s" and a0':"s2 = toSeq s'" and
          a1: "\<forall>ns ns'. 
              (s = Normal ns \<or> s = Abrupt ns) \<and> 
              (s' = Normal ns' \<or> s' = Abrupt ns') \<longrightarrow> snd ns =snd ns'"
  shows         "\<Gamma>\<turnstile>\<^sub>c (c, s) \<rightarrow>\<^sub>c\<^sub>e\<^sup>* (c', s')"
  using steps a1 a0 a0'
  thm converse_rtranclp_induct2 [case_names Refl Trans]
proof (induct arbitrary: s s' rule: converse_rtranclp_induct2 [case_names Refl Trans])
  case Refl      
  thus ?case using eq_toSeq by blast
next
  case (Trans a b a' b')   
  thus ?case 
  proof(cases a) 
    by (simp add: Trans.hyps(3) converse_rtranclp_into_rtranclp)
qed

lemma steps_not_normal_c_ce: 
  assumes steps: "\<Gamma>\<turnstile>\<^sub>c (c, s) \<rightarrow>\<^sup>* (c', s')"
  shows         "( \<forall>sa. \<not>(s=Normal sa)) \<Longrightarrow> \<Gamma>\<turnstile>\<^sub>c (c, s) \<rightarrow>\<^sub>c\<^sub>e\<^sup>* (c', s')"
by (simp add: steps steps_c_ce)

lemma steps_not_normal_c_eq_ce:
assumes normal: "( \<forall>sa. \<not>(s=Normal sa))"
shows         " \<Gamma>\<turnstile>\<^sub>c (c, s) \<rightarrow>\<^sup>* (c', s') =  \<Gamma>\<turnstile>\<^sub>c (c, s) \<rightarrow>\<^sub>c\<^sub>e\<^sup>* (c', s')"
using normal
using steps_c_ce steps_not_normal_ce_c by auto 

lemma steps_ce_Fault: "\<Gamma>\<turnstile>\<^sub>c (c, Fault f) \<rightarrow>\<^sub>c\<^sub>e\<^sup>* (Skip, Fault f)"
by (simp add: SmallStepCon.steps_Fault steps_c_ce)

lemma steps_ce_Stuck: "\<Gamma>\<turnstile>\<^sub>c (c, Stuck) \<rightarrow>\<^sub>c\<^sub>e\<^sup>* (Skip, Stuck)"
by (simp add: SmallStepCon.steps_Stuck steps_c_ce)

lemma steps_ce_Abrupt: "\<Gamma>\<turnstile>\<^sub>c (c, Abrupt a) \<rightarrow>\<^sub>c\<^sub>e\<^sup>* (Skip, Abrupt a)"
by (simp add: SmallStepCon.steps_Abrupt steps_c_ce)  *)

lemma step_ce_seq_throw_normal:
assumes step: "\<Gamma>\<turnstile>\<^sub>c (c, s) \<rightarrow>\<^sub>c\<^sub>e (c', s')" and
        c_val: "c=Seq Throw Q \<and> c'=Throw"
shows "\<exists>sa. s=Normal sa"
using step c_val not_eq_not_env   
      step_ce_not_step_e_step_c step_seq_throw_normal  
  by (metis SemanticCon.isAbr_def SemanticCon.not_isAbrD seq_and_if_not_eq(3) 
            toSeq.simps(2) toSeq.simps(3) toSeq.simps(4) xstate.distinct(3) 
            xstate.simps(5) xstate.simps(9))    

lemma step_ce_catch_throw_normal:
assumes step: "\<Gamma>\<turnstile>\<^sub>c (c, s) \<rightarrow>\<^sub>c\<^sub>e (c', s')" and
        c_val: "c=Catch Throw Q \<and> c'=Throw"
shows "\<exists>sa. s=Normal sa"
using step c_val not_eq_not_env
      step_ce_not_step_e_step_c step_catch_throw_normal
  by (metis SemanticCon.isAbr_def SemanticCon.not_isAbrD seq_and_if_not_eq(11) 
         toSeq.simps(2) toSeq.simps(3) toSeq.simps(4) 
        xstate.distinct(3) xstate.simps(5) xstate.simps(9)) 


lemma step_ce_normal_to_normal[rule_format]:
assumes step:"\<Gamma>\<turnstile>\<^sub>c (c, s) \<rightarrow>\<^sub>c\<^sub>e\<^sup>* (c', s')" and
        sn: "s = Normal sa" and
        finalc':"(\<Gamma>\<turnstile>\<^sub>c (c', s') \<rightarrow>\<^sub>c\<^sub>e\<^sup>*(c1, s1) \<and>  (\<exists>sb. s1 = Normal sb))"
shows "         
       (\<exists>sc. s'=Normal sc)"
using step sn finalc' steps_ce_not_Normal by blast      


lemma ce_Throw_toSkip: 
  assumes a0:"\<Gamma>\<turnstile>\<^sub>c (LanguageCon.com.Throw, s) \<rightarrow>\<^sub>c\<^sub>e x"
  shows "fst x = Skip \<or> fst x = Throw"
proof-
  have "\<Gamma>\<turnstile>\<^sub>c (Throw, toSeq s) \<rightarrow> (fst x, toSeq (snd x)) 
        \<or> \<Gamma>\<turnstile>\<^sub>c (Throw, s) \<rightarrow>\<^sub>e x" using a0 step_ce_dest
    by (metis prod.collapse)
  thus ?thesis
    by (metis env_c_c' prod.collapse prod.inject stepc_elim_cases(11))
qed
(* lemma SeqSteps_ce: 
  assumes steps: "\<Gamma>\<turnstile>\<^sub>c cfg\<^sub>1\<rightarrow>\<^sub>c\<^sub>e\<^sup>* cfg\<^sub>2"
  shows "\<And> c\<^sub>1 s c\<^sub>1' s'. \<lbrakk>cfg\<^sub>1 = (c\<^sub>1,s);cfg\<^sub>2=(c\<^sub>1',s')\<rbrakk>
          \<Longrightarrow> \<Gamma>\<turnstile>\<^sub>c(Seq c\<^sub>1 c\<^sub>2,s) \<rightarrow>\<^sub>c\<^sub>e\<^sup>* (Seq c\<^sub>1' c\<^sub>2, s')"
using steps
proof (induct rule: converse_rtranclp_induct [case_names Refl Trans]) 
  case Refl
  thus ?case
    by simp
next
  case (Trans cfg\<^sub>1 cfg'') 
  then have "\<Gamma>\<turnstile>\<^sub>c cfg\<^sub>1 \<rightarrow> cfg'' \<or> \<Gamma>\<turnstile>\<^sub>c cfg\<^sub>1 \<rightarrow>\<^sub>e cfg''" 
   using step_ce_elim_cases by blast
  thus ?case 
  proof
    assume a1:"\<Gamma>\<turnstile>\<^sub>c cfg\<^sub>1 \<rightarrow>\<^sub>e cfg''"          
    have "\<forall>f p pa. \<not> f\<turnstile>\<^sub>c p \<rightarrow>\<^sub>e pa \<or> (\<exists>c. 
                   (\<exists>x. p = (c::('a, 'b, 'c,'d) LanguageCon.com, x)) \<and> (\<exists>x. pa = (c, x)))"
      by (meson etranE)
    then obtain cc :: "('b \<Rightarrow> ('a, 'b, 'c,'d) LanguageCon.com option) \<Rightarrow> 
                              ('a, 'b, 'c,'d) LanguageCon.com \<times> ('a, 'c) xstate \<Rightarrow> 
                              ('a, 'b, 'c,'d) LanguageCon.com \<times> ('a, 'c) xstate \<Rightarrow> 
                              ('a, 'b, 'c,'d) LanguageCon.com" and 
                xx :: "('b \<Rightarrow> ('a, 'b, 'c,'d) LanguageCon.com option) \<Rightarrow> 
                       ('a, 'b, 'c,'d) LanguageCon.com \<times> ('a, 'c) xstate \<Rightarrow> 
                       ('a, 'b, 'c,'d) LanguageCon.com \<times> ('a, 'c) xstate \<Rightarrow> ('a, 'c) xstate" and
                xxa :: "('b \<Rightarrow> ('a, 'b, 'c,'d) LanguageCon.com option) \<Rightarrow> 
                        ('a, 'b, 'c,'d) LanguageCon.com \<times> ('a, 'c) xstate \<Rightarrow> 
                       ('a, 'b, 'c,'d) LanguageCon.com \<times> ('a, 'c) xstate \<Rightarrow> ('a, 'c) xstate" where
      f1: "\<forall>f p pa. \<not> f\<turnstile>\<^sub>c p \<rightarrow>\<^sub>e pa \<or> p = (cc f p pa, xx f p pa) \<and> pa = (cc f p pa, xxa f p pa)"
      by (metis (no_types))
    have f2: "\<forall>f c x xa. \<not> f\<turnstile>\<^sub>c (c::('a, 'b, 'c,'d) LanguageCon.com, x) \<rightarrow>\<^sub>e (c, xa) \<or> 
                            (\<exists>a. x = Normal a) \<or> (\<forall>a. xa \<noteq> Normal a) \<and> x = xa"
      by (metis stepe_elim_cases)
    have f3: "(c\<^sub>1, xxa \<Gamma> cfg\<^sub>1 cfg'') = cfg''"
      using f1 by (metis Trans.prems(1) a1 fst_conv)
    hence "\<Gamma>\<turnstile>\<^sub>c (LanguageCon.com.Seq c\<^sub>1 c\<^sub>2, xxa \<Gamma> cfg\<^sub>1 cfg'') \<rightarrow>\<^sub>c\<^sub>e\<^sup>* (LanguageCon.com.Seq c\<^sub>1' c\<^sub>2, s')"
      using Trans.hyps(3) Trans.prems(2) by force
    thus ?thesis
      using f3 f2 by (metis (no_types) Env Trans.prems(1) a1 e_step r_into_rtranclp 
                       rtranclp.rtrancl_into_rtrancl rtranclp_idemp)   
  next
     assume "\<Gamma>\<turnstile>\<^sub>c cfg\<^sub>1 \<rightarrow> cfg''"
     thus ?thesis
      proof -
        have "\<forall>p. \<exists>c x. p = (c::('a, 'b, 'c,'d) LanguageCon.com, x::('a, 'c) xstate)"
          by auto
        thus ?thesis
          by (metis (no_types) Seqc Trans.hyps(3) Trans.prems(1) Trans.prems(2) 
                   `\<Gamma>\<turnstile>\<^sub>c cfg\<^sub>1 \<rightarrow> cfg''` c_step converse_rtranclp_into_rtranclp)
      qed
  qed
qed


lemma CatchSteps_ce: 
  assumes steps: "\<Gamma>\<turnstile>\<^sub>ccfg\<^sub>1\<rightarrow>\<^sub>c\<^sub>e\<^sup>* cfg\<^sub>2"
  shows "\<And> c\<^sub>1 s c\<^sub>1' s'. \<lbrakk>cfg\<^sub>1 = (c\<^sub>1,s); cfg\<^sub>2=(c\<^sub>1',s')\<rbrakk>
          \<Longrightarrow> \<Gamma>\<turnstile>\<^sub>c(Catch c\<^sub>1 c\<^sub>2,s) \<rightarrow>\<^sub>c\<^sub>e\<^sup>* (Catch c\<^sub>1' c\<^sub>2, s')"
using steps
proof (induct rule: converse_rtranclp_induct [case_names Refl Trans])
  case Refl
  thus ?case
    by simp
next
  case (Trans cfg\<^sub>1 cfg'')
then have "\<Gamma>\<turnstile>\<^sub>c cfg\<^sub>1 \<rightarrow> cfg'' \<or> \<Gamma>\<turnstile>\<^sub>c cfg\<^sub>1 \<rightarrow>\<^sub>e cfg''" 
   using step_ce_elim_cases by blast
  thus ?case 
  proof
    assume a1:"\<Gamma>\<turnstile>\<^sub>c cfg\<^sub>1 \<rightarrow>\<^sub>e cfg''"        
    have "\<forall>f p pa. \<not> f\<turnstile>\<^sub>c p \<rightarrow>\<^sub>e pa \<or> (\<exists>c. (\<exists>x. p = (c::('a, 'b, 'c,'d) LanguageCon.com, x)) \<and> (\<exists>x. pa = (c, x)))"
      by (meson etranE)
    then obtain cc :: "('b \<Rightarrow>('a, 'b, 'c, 'd) LanguageCon.com option) \<Rightarrow>
                        ('a, 'b, 'c, 'd) LanguageCon.com \<times> ('a, 'c) xstate \<Rightarrow>
                        ('a, 'b, 'c, 'd) LanguageCon.com \<times> ('a, 'c) xstate \<Rightarrow>
                        ('a, 'b, 'c, 'd) LanguageCon.com" and 
                xx :: "('b \<Rightarrow>('a, 'b, 'c, 'd) LanguageCon.com option) \<Rightarrow>
                       ('a, 'b, 'c, 'd) LanguageCon.com \<times> ('a, 'c) xstate \<Rightarrow>
                       ('a, 'b, 'c, 'd) LanguageCon.com \<times> ('a, 'c) xstate \<Rightarrow> 
                       ('a, 'c) xstate" and 
                xxa :: "('b \<Rightarrow>('a, 'b, 'c, 'd) LanguageCon.com option) \<Rightarrow>
                         ('a, 'b, 'c, 'd) LanguageCon.com \<times> ('a, 'c) xstate \<Rightarrow>
                         ('a, 'b, 'c, 'd) LanguageCon.com \<times> ('a, 'c) xstate \<Rightarrow> ('a, 'c) xstate" where
      f1: "\<forall>f p pa. \<not> f\<turnstile>\<^sub>c p \<rightarrow>\<^sub>e pa \<or> p = (cc f p pa, xx f p pa) \<and> pa = (cc f p pa, xxa f p pa)"
      by (metis (no_types))
    have f2: "\<forall>f c x xa. \<not> f\<turnstile>\<^sub>c (c::('a, 'b, 'c,'d) LanguageCon.com, x) \<rightarrow>\<^sub>e (c, xa) \<or> 
                         (\<exists>a. x = Normal a) \<or> (\<forall>a. xa \<noteq> Normal a) \<and> x = xa"
      by (metis stepe_elim_cases)
    have f3: "(c\<^sub>1, xxa \<Gamma> cfg\<^sub>1 cfg'') = cfg''"
      using f1 by (metis Trans.prems(1) a1 fst_conv)
    hence "\<Gamma>\<turnstile>\<^sub>c (LanguageCon.com.Catch c\<^sub>1 c\<^sub>2, xxa \<Gamma> cfg\<^sub>1 cfg'') \<rightarrow>\<^sub>c\<^sub>e\<^sup>* (LanguageCon.com.Catch c\<^sub>1' c\<^sub>2, s')"
      using Trans.hyps(3) Trans.prems(2) by force
    thus ?thesis
      using f3 f2 by (metis (no_types) Env Trans.prems(1) a1 e_step r_into_rtranclp rtranclp.rtrancl_into_rtrancl rtranclp_idemp)              
  next
    assume "\<Gamma>\<turnstile>\<^sub>c cfg\<^sub>1 \<rightarrow> cfg''"
    thus ?thesis
    proof -
      obtain cc :: "('a, 'b, 'c, 'd) LanguageCon.com \<times> ('a, 'c) xstate \<Rightarrow> ('a, 'b, 'c, 'd) LanguageCon.com" and xx :: "('a, 'b, 'c, 'd) LanguageCon.com \<times> ('a, 'c) xstate \<Rightarrow> ('a, 'c) xstate" where
        f1: "\<forall>p. p = (cc p, xx p)"
        by (meson old.prod.exhaust)
      hence "\<And>c. \<Gamma>\<turnstile>\<^sub>c (LanguageCon.com.Catch c\<^sub>1 c, s) \<rightarrow> (LanguageCon.com.Catch (cc cfg'') c, xx cfg'')"
        by (metis (no_types) Catchc Trans.prems(1) `\<Gamma>\<turnstile>\<^sub>c cfg\<^sub>1 \<rightarrow> cfg''`)
      thus ?thesis
        using f1 by (meson Trans.hyps(3) Trans.prems(2) c_step converse_rtranclp_into_rtranclp)
    qed      
  qed
qed

*)

subsection \<open>Computations\<close>
subsubsection \<open>Sequential computations\<close>

type_synonym ('g,'l,'p,'f,'e) confs = 
  "('g\<times>'l,'p,'f,'e) body \<times> (('g, 'l, 'p,'f,'e) config_gs) list"

(* inductive_set cptn :: "(('g,'l,'p,'f,'e) confs) set"
where
  CptnOne: " (\<Gamma>, [(P,s)]) \<in> cptn"
| CptnEnv: "\<lbrakk>\<Gamma>\<turnstile>\<^sub>c(P,s) \<rightarrow>\<^sub>e (P,t); (\<Gamma>,(P, t)#xs) \<in> cptn \<rbrakk> \<Longrightarrow>
             (\<Gamma>,(P,s)#(P,t)#xs) \<in> cptn"
| CptnComp: "\<lbrakk>\<Gamma>\<turnstile>\<^sub>c(P,toSeq s) \<rightarrow> (Q,toSeq t); 
              \<forall>ns ns'. 
               (s = Normal ns \<or> s = Abrupt ns) \<and> 
               (t = Normal ns' \<or> t = Abrupt ns') \<longrightarrow> snd ns = snd ns'; 
              (\<Gamma>,(Q, t)#xs) \<in> cptn \<rbrakk> \<Longrightarrow> 
              (\<Gamma>,(P,s)#(Q,t)#xs) \<in> cptn" *)

inductive_set cptn :: "(('g,'l,'p,'f,'e) confs) set"
where
  CptnOne: " (\<Gamma>, [(P,s)]) \<in> cptn"
| Cptn: "\<lbrakk>\<Gamma>\<turnstile>\<^sub>c(P,s) \<rightarrow>\<^sub>c\<^sub>e (Q,t); (\<Gamma>,(Q, t)#xs) \<in> cptn \<rbrakk> \<Longrightarrow>
             (\<Gamma>,(P,s)#(Q,t)#xs) \<in> cptn"

(* lemma c1: assumes a0:"(\<Gamma>,c)\<in>cptn1" shows "(\<Gamma>,c)\<in>cptn"
  using a0
proof(induct)
  case (CptnOne1 \<Gamma> P s)
  then show ?case
    by (simp add: cptn.CptnOne) 
next
  case (Cptn1 \<Gamma> P s Q t xs)
  moreover { assume " \<Gamma>\<turnstile>\<^sub>c (P, toSeq s) \<rightarrow> (Q, toSeq t)"
    then have ?case using Cptn1
      using cptn.CptnComp step_ce_notNormal step_dest1 by blast
  }
  moreover { assume " \<Gamma>\<turnstile>\<^sub>c (P,  s) \<rightarrow>\<^sub>e (Q,  t)"
    then have ?case
      using calculation(3) cptn.CptnEnv env_c_c' by blast 
  }ultimately show ?case
    using step_ce_not_step_e_step_c by blast 
qed
  

lemma c2: assumes a0:"(\<Gamma>,c)\<in>cptn" 
  shows"(\<Gamma>,c)\<in>cptn1"
  using a0 
proof(induct)
case (CptnOne \<Gamma> P s)
then show ?case
  by (simp add: cptn1.CptnOne1) 
next
case (CptnEnv \<Gamma> P s t xs)
then show ?case
  by (simp add: cptn1.Cptn1 e_step) 
next
  case (CptnComp \<Gamma> P s Q t xs)
  then show ?case
    by (simp add: c_step cptn1.Cptn1) 
qed

lemma eq_cptn: "cptn = cptn1"
  using c1 c2 by auto *)
  

(* inductive_cases cptn_elim_cases [cases set]:
"(\<Gamma>, [(P,s)]) \<in> cptn"
"(\<Gamma>,(P,s)#(Q,t)#xs) \<in> cptn"
"(\<Gamma>,(P,s)#(P,t)#xs) \<in> cptn" *)

inductive_cases cptn_elim_cases [cases set]:
"(\<Gamma>, [(P,s)]) \<in> cptn"
"(\<Gamma>,(P,s)#(Q,t)#xs) \<in> cptn"

(*
lemma cptn_elim_casesa1[cases set,elim]:
 "\<lbrakk>(\<Gamma>, (P, Normal ((g,l1), l)) # (Q, Normal ((g',l1'), l')) # xs) \<in> cptn;
   \<lbrakk>\<Gamma>\<turnstile>\<^sub>c (P, Normal ((g,l1), l)) \<rightarrow>\<^sub>e (P, Normal ((g',l1'), l')); (\<Gamma>, (P, Normal ((g',l1'), l')) # xs) \<in> cptn; Q = P\<rbrakk> \<Longrightarrow> Pa;
   \<lbrakk>\<Gamma>\<turnstile>\<^sub>c (P, Normal (g,l1)) \<rightarrow> (Q, Normal (g',l1'));
   l=l';
    (\<Gamma>, (Q, Normal ((g',l1'), l')) # xs) \<in> cptn\<rbrakk>
   \<Longrightarrow> Pa\<rbrakk>
  \<Longrightarrow> Pa"
  by (auto elim:cptn_elim_cases)

lemma cptn_elim_casesa2[cases set,elim]:
 "\<lbrakk>(\<Gamma>, (P, Normal (g, l)) # (Q, Abrupt (g', l')) # xs) \<in> cptn;
   \<lbrakk>\<Gamma>\<turnstile>\<^sub>c (P, Normal (g, l)) \<rightarrow>\<^sub>e (P, Abrupt (g', l')); (\<Gamma>, (P, Abrupt (g', l')) # xs) \<in> cptn; Q = P\<rbrakk> \<Longrightarrow> Pa;
   \<lbrakk>\<Gamma>\<turnstile>\<^sub>c (P, Normal g) \<rightarrow> (Q, Abrupt g');
   l=l';
    (\<Gamma>, (Q, Abrupt (g', l')) # xs) \<in> cptn\<rbrakk>
   \<Longrightarrow> Pa\<rbrakk>
  \<Longrightarrow> Pa"
  by (auto elim:cptn_elim_cases)

lemma cptn_elim_casesa3[cases set,elim]:
 "\<lbrakk>(\<Gamma>, (P, Normal (g, l)) # (Q, Fault f) # xs) \<in> cptn;
   \<lbrakk>\<Gamma>\<turnstile>\<^sub>c (P, Normal (g, l)) \<rightarrow>\<^sub>e (P, Fault f); (\<Gamma>, (P, Fault f) # xs) \<in> cptn; Q = P\<rbrakk> \<Longrightarrow> Pa;
   \<lbrakk>\<Gamma>\<turnstile>\<^sub>c (P, Normal g) \<rightarrow> (Q, Fault f);
    (\<Gamma>, (Q, Fault f) # xs) \<in> cptn\<rbrakk>
   \<Longrightarrow> Pa\<rbrakk>
  \<Longrightarrow> Pa"
  by (auto elim:cptn_elim_cases)

lemma cptn_elim_casesa4[cases set,elim]:
 "\<lbrakk>(\<Gamma>, (P, Normal (g, l)) # (Q, Stuck) # xs) \<in> cptn;
   \<lbrakk>\<Gamma>\<turnstile>\<^sub>c (P, Normal (g, l)) \<rightarrow>\<^sub>e (P, Stuck); (\<Gamma>, (P, Stuck) # xs) \<in> cptn; Q = P\<rbrakk> \<Longrightarrow> Pa;
   \<lbrakk>\<Gamma>\<turnstile>\<^sub>c (P, Normal g) \<rightarrow> (Q, Stuck);
    (\<Gamma>, (Q, Stuck) # xs) \<in> cptn\<rbrakk>
   \<Longrightarrow> Pa\<rbrakk>
  \<Longrightarrow> Pa"
  by (auto elim:cptn_elim_cases)

lemma cptn_elim_casesa5[cases set,elim]:
 "\<lbrakk>(\<Gamma>, (P, Abrupt (g, l)) # (Q, Normal (g', l')) # xs) \<in> cptn;
   \<lbrakk>\<Gamma>\<turnstile>\<^sub>c (P, Abrupt (g, l)) \<rightarrow>\<^sub>e (P, Normal (g', l')); (\<Gamma>, (P, Normal (g', l')) # xs) \<in> cptn; Q = P\<rbrakk> \<Longrightarrow> Pa;
   \<lbrakk>\<Gamma>\<turnstile>\<^sub>c (P, Abrupt g) \<rightarrow> (Q, Normal g');
   l=l';
    (\<Gamma>, (Q, Normal (g', l')) # xs) \<in> cptn\<rbrakk>
   \<Longrightarrow> Pa\<rbrakk>
  \<Longrightarrow> Pa"
  by (auto elim:cptn_elim_cases)

lemma cptn_elim_casesa6[cases set,elim]:
 "\<lbrakk>(\<Gamma>, (P, Abrupt (g, l)) # (Q, Abrupt (g', l')) # xs) \<in> cptn;
   \<lbrakk>\<Gamma>\<turnstile>\<^sub>c (P, Abrupt (g, l)) \<rightarrow>\<^sub>e (P, Abrupt (g', l')); (\<Gamma>, (P, Abrupt (g', l')) # xs) \<in> cptn; Q = P\<rbrakk> \<Longrightarrow> Pa;
   \<lbrakk>\<Gamma>\<turnstile>\<^sub>c (P, Abrupt g) \<rightarrow> (Q, Abrupt g');
   l=l';
    (\<Gamma>, (Q, Abrupt (g', l')) # xs) \<in> cptn\<rbrakk>
   \<Longrightarrow> Pa\<rbrakk>
  \<Longrightarrow> Pa"
  by (auto elim:cptn_elim_cases)

lemma cptn_elim_casesa7[cases set,elim]:
 "\<lbrakk>(\<Gamma>, (P, Abrupt (g, l)) # (Q, Fault f) # xs) \<in> cptn;
   \<lbrakk>\<Gamma>\<turnstile>\<^sub>c (P, Abrupt (g, l)) \<rightarrow>\<^sub>e (P, Fault f); (\<Gamma>, (P, Fault f) # xs) \<in> cptn; Q = P\<rbrakk> \<Longrightarrow> Pa;
   \<lbrakk>\<Gamma>\<turnstile>\<^sub>c (P, Abrupt g) \<rightarrow> (Q, Fault f);
    (\<Gamma>, (Q, Fault f) # xs) \<in> cptn\<rbrakk>
   \<Longrightarrow> Pa\<rbrakk>
  \<Longrightarrow> Pa"
  by (auto elim:cptn_elim_cases)

lemma cptn_elim_casesa8[cases set,elim]:
 "\<lbrakk>(\<Gamma>, (P, Abrupt (g, l)) # (Q, Stuck) # xs) \<in> cptn;
   \<lbrakk>\<Gamma>\<turnstile>\<^sub>c (P, Abrupt (g, l)) \<rightarrow>\<^sub>e (P, Stuck); (\<Gamma>, (P, Stuck) # xs) \<in> cptn; Q = P\<rbrakk> \<Longrightarrow> Pa;
   \<lbrakk>\<Gamma>\<turnstile>\<^sub>c (P, Abrupt g) \<rightarrow> (Q, Stuck);
    (\<Gamma>, (Q, Stuck) # xs) \<in> cptn\<rbrakk>
   \<Longrightarrow> Pa\<rbrakk>
  \<Longrightarrow> Pa"
  by (auto elim:cptn_elim_cases)

lemma cptn_elim_casesa9[cases set,elim]:
 "\<lbrakk>(\<Gamma>, (P, Fault f) # (Q, Normal (g', l')) # xs) \<in> cptn;
   \<lbrakk>\<Gamma>\<turnstile>\<^sub>c (P, Fault f) \<rightarrow>\<^sub>e (P, Normal (g', l')); (\<Gamma>, (P, Normal (g', l')) # xs) \<in> cptn; Q = P\<rbrakk> \<Longrightarrow> Pa;
   \<lbrakk>\<Gamma>\<turnstile>\<^sub>c (P, Fault f) \<rightarrow> (Q, Normal g');  
    (\<Gamma>, (Q, Normal (g', l')) # xs) \<in> cptn\<rbrakk>
   \<Longrightarrow> Pa\<rbrakk>
  \<Longrightarrow> Pa"
  by (auto elim:cptn_elim_cases)

lemma cptn_elim_casesa10[cases set,elim]:
 "\<lbrakk>(\<Gamma>, (P, Fault f) # (Q, Abrupt (g', l')) # xs) \<in> cptn;
   \<lbrakk>\<Gamma>\<turnstile>\<^sub>c (P, Fault f) \<rightarrow>\<^sub>e (P, Abrupt (g', l')); (\<Gamma>, (P, Abrupt (g', l')) # xs) \<in> cptn; Q = P\<rbrakk> \<Longrightarrow> Pa;
   \<lbrakk>\<Gamma>\<turnstile>\<^sub>c (P, Fault f) \<rightarrow> (Q, Abrupt g');
    (\<Gamma>, (Q, Abrupt (g', l')) # xs) \<in> cptn\<rbrakk>
   \<Longrightarrow> Pa\<rbrakk>
  \<Longrightarrow> Pa"
  by (auto elim:cptn_elim_cases)

lemma cptn_elim_casesa11[cases set,elim]:
 "\<lbrakk>(\<Gamma>, (P, Fault f) # (Q, Fault f') # xs) \<in> cptn;
   \<lbrakk>\<Gamma>\<turnstile>\<^sub>c (P, Fault f) \<rightarrow>\<^sub>e (P, Fault f'); (\<Gamma>, (P, Fault f') # xs) \<in> cptn; Q = P\<rbrakk> \<Longrightarrow> Pa;
   \<lbrakk>\<Gamma>\<turnstile>\<^sub>c (P, Fault f) \<rightarrow> (Q, Fault f');
    (\<Gamma>, (Q, Fault f') # xs) \<in> cptn\<rbrakk>
   \<Longrightarrow> Pa\<rbrakk>
  \<Longrightarrow> Pa"
  by (auto elim:cptn_elim_cases)

lemma cptn_elim_casesa12[cases set,elim]:
 "\<lbrakk>(\<Gamma>, (P, Fault f) # (Q, Stuck) # xs) \<in> cptn;
   \<lbrakk>\<Gamma>\<turnstile>\<^sub>c (P, Fault f) \<rightarrow>\<^sub>e (P, Stuck); (\<Gamma>, (P, Stuck) # xs) \<in> cptn; Q = P\<rbrakk> \<Longrightarrow> Pa;
   \<lbrakk>\<Gamma>\<turnstile>\<^sub>c (P, Fault f) \<rightarrow> (Q, Stuck);
    (\<Gamma>, (Q, Stuck) # xs) \<in> cptn\<rbrakk>
   \<Longrightarrow> Pa\<rbrakk>
  \<Longrightarrow> Pa"
  by (auto elim:cptn_elim_cases)

lemma cptn_elim_casesa13[cases set,elim]:
 "\<lbrakk>(\<Gamma>, (P, Stuck) # (Q, Normal (g', l')) # xs) \<in> cptn;
   \<lbrakk>\<Gamma>\<turnstile>\<^sub>c (P, Stuck) \<rightarrow>\<^sub>e (P, Normal (g', l')); (\<Gamma>, (P, Normal (g', l')) # xs) \<in> cptn; Q = P\<rbrakk> \<Longrightarrow> Pa;
   \<lbrakk>\<Gamma>\<turnstile>\<^sub>c (P, Stuck) \<rightarrow> (Q, Normal g');  
    (\<Gamma>, (Q, Normal (g', l')) # xs) \<in> cptn\<rbrakk>
   \<Longrightarrow> Pa\<rbrakk>
  \<Longrightarrow> Pa"
  by (auto elim:cptn_elim_cases)

lemma cptn_elim_casesa14[cases set,elim]:
 "\<lbrakk>(\<Gamma>, (P, Stuck) # (Q, Abrupt (g', l')) # xs) \<in> cptn;
   \<lbrakk>\<Gamma>\<turnstile>\<^sub>c (P, Stuck) \<rightarrow>\<^sub>e (P, Abrupt (g', l')); (\<Gamma>, (P, Abrupt (g', l')) # xs) \<in> cptn; Q = P\<rbrakk> \<Longrightarrow> Pa;
   \<lbrakk>\<Gamma>\<turnstile>\<^sub>c (P, Stuck) \<rightarrow> (Q, Abrupt g');
    (\<Gamma>, (Q, Abrupt (g', l')) # xs) \<in> cptn\<rbrakk>
   \<Longrightarrow> Pa\<rbrakk>
  \<Longrightarrow> Pa"
  by (auto elim:cptn_elim_cases)

lemma cptn_elim_casesa15[cases set,elim]:
 "\<lbrakk>(\<Gamma>, (P, Stuck) # (Q, Fault f) # xs) \<in> cptn;
   \<lbrakk>\<Gamma>\<turnstile>\<^sub>c (P, Stuck) \<rightarrow>\<^sub>e (P, Fault f); (\<Gamma>, (P, Fault f) # xs) \<in> cptn; Q = P\<rbrakk> \<Longrightarrow> Pa;
   \<lbrakk>\<Gamma>\<turnstile>\<^sub>c (P, Stuck) \<rightarrow> (Q, Fault f);
    (\<Gamma>, (Q, Fault f) # xs) \<in> cptn\<rbrakk>
   \<Longrightarrow> Pa\<rbrakk>
  \<Longrightarrow> Pa"
  by (auto elim:cptn_elim_cases)

lemma cptn_elim_casesa16[cases set,elim]:
 "\<lbrakk>(\<Gamma>, (P, Stuck) # (Q, Stuck) # xs) \<in> cptn;
   \<lbrakk>\<Gamma>\<turnstile>\<^sub>c (P, Stuck) \<rightarrow>\<^sub>e (P, Stuck); (\<Gamma>, (P, Stuck) # xs) \<in> cptn; Q = P\<rbrakk> \<Longrightarrow> Pa;
   \<lbrakk>\<Gamma>\<turnstile>\<^sub>c (P, Stuck) \<rightarrow> (Q, Stuck);
    (\<Gamma>, (Q, Stuck) # xs) \<in> cptn\<rbrakk>
   \<Longrightarrow> Pa\<rbrakk>
  \<Longrightarrow> Pa"
  by (auto elim:cptn_elim_cases)
  *)

inductive_cases cptn_elim_cases_pair [cases set]:
"(\<Gamma>, [x]) \<in> cptn"
"(\<Gamma>, x#x1#xs) \<in> cptn"

lemma cptn_dest:"(\<Gamma>,(P,s)#(Q,t)#xs) \<in> cptn \<Longrightarrow> (\<Gamma>,(Q,t)#xs)\<in> cptn"
by (auto dest: cptn_elim_cases)

lemma cptn_dest_pair:"(\<Gamma>,x#x1#xs) \<in> cptn \<Longrightarrow> (\<Gamma>,x1#xs)\<in> cptn"
proof -
  assume "(\<Gamma>,x#x1#xs) \<in> cptn"
  thus ?thesis using cptn_dest prod.collapse by metis
qed

lemma cptn_dest1:"(\<Gamma>,(P,s)#(Q,t)#xs) \<in> cptn \<Longrightarrow> (\<Gamma>,(P,s)#[(Q,t)])\<in> cptn"
proof -
  assume a1: "(\<Gamma>, (P, s) # (Q, t) # xs) \<in> cptn"
  have "(\<Gamma>, [(Q, t)]) \<in> cptn"
    by (meson cptn.CptnOne)
  thus ?thesis
    using a1 cptn.Cptn cptn_elim_cases(2) by blast
  (* proof (cases s)
    case (Normal s') 
    then obtain g l1 l where f1: 
          "(\<Gamma>, (P, Normal s') # (Q, t) # xs) \<in> cptn \<and> s' = ((g,l1),l)"
       using Normal a1
       by (metis old.prod.exhaust)
     thus ?thesis
       apply (cases t)     
       by (auto simp add: Normal cptn.CptnEnv cptn.CptnComp cptn.CptnOne)      
  next
    case (Abrupt x) 
     then obtain g l1 l where f1: 
          "(\<Gamma>, (P, Abrupt x) # (Q, t) # xs) \<in> cptn \<and> x = ((g,l1),l)"
       using Abrupt a1
       by (metis old.prod.exhaust)
    thus ?thesis  
      apply (cases t)
      by (auto simp add: Abrupt cptn.CptnEnv cptn.CptnComp cptn.CptnOne)     
  next
    case (Stuck)     
    thus ?thesis using a1
     apply (cases t)      
      by (auto simp add:  cptn.CptnEnv cptn.CptnComp cptn.CptnOne)
  next 
    case (Fault f) thus ?thesis
      using a1   apply (cases t,auto) 
      by (auto simp add: Fault cptn.CptnEnv cptn.CptnComp cptn.CptnOne)       
  qed *)
qed

lemma cptn_dest1_pair:"(\<Gamma>,x#x1#xs) \<in> cptn \<Longrightarrow> (\<Gamma>,x#[x1])\<in> cptn"
proof -
  assume "(\<Gamma>,x#x1#xs) \<in> cptn"
  thus ?thesis using cptn_dest1 prod.collapse by metis
qed

lemma cptn_append_is_cptn [rule_format]: 
 "\<forall>b a. (\<Gamma>,b#c1)\<in>cptn \<longrightarrow>  (\<Gamma>,a#c2)\<in>cptn \<longrightarrow> (b#c1)!length c1=a \<longrightarrow> (\<Gamma>,b#c1@c2)\<in>cptn"
apply(induct c1)
 apply simp
apply clarify
apply(erule cptn.cases,simp_all)
  by (simp add: cptn.Cptn)
(* apply (simp add: cptn.CptnEnv)
by (simp add: cptn.CptnComp) *)

lemma cptn_dest_2:
  "(\<Gamma>,a#xs@ys) \<in> cptn  \<Longrightarrow> (\<Gamma>,a#xs)\<in> cptn"
proof (induct "xs" arbitrary: a)
  case Nil thus ?case using cptn.simps by fastforce 
next
  case (Cons x xs') 
  then have "(\<Gamma>,a#[x])\<in>cptn" by (simp add: cptn_dest1_pair)
  also have "(\<Gamma>, x # xs') \<in> cptn"
    using Cons.hyps Cons.prems cptn_dest_pair by fastforce    
  ultimately show ?case using cptn_append_is_cptn [of \<Gamma> a "[x]" x xs']
    by force    
qed   

lemma tl_in_cptn: "\<lbrakk> (g,a#xs) \<in>cptn; xs\<noteq>[] \<rbrakk> \<Longrightarrow> (g,xs)\<in>cptn"
  by (force elim: cptn.cases)

lemma sublist_in_cptn:"(\<Gamma>, ys@ xs) \<in> cptn \<Longrightarrow> xs\<noteq> [] \<Longrightarrow> (\<Gamma>, xs) \<in> cptn"
proof(induct ys)
  case Nil
  then show ?case by auto
next
  case (Cons a ys)
  then have "(\<Gamma>, a # (ys @ xs)) \<in> cptn " by auto
  then show ?case using cptn_elim_cases
    by (metis Cons.hyps Cons.prems(2) Nil_is_append_conv tl_in_cptn)  
qed

subsection {* Relation between @{term "stepc_rtrancl"} and @{term "cptn"} *}

lemma stepc_rtrancl_cptn:
  assumes step: "\<Gamma>\<turnstile>\<^sub>c (c,s) \<rightarrow>\<^sub>c\<^sub>e\<^sup>* (cf,sf)"           
  shows "\<exists>xs. (\<Gamma>,(c, s)#xs) \<in> cptn \<and>(cf,sf) = (last ((c,s)#xs))"
using step 
proof (induct rule: converse_rtranclp_induct2 [case_names Refl Trans]) 
  case Refl thus ?case using cptn.CptnOne by auto
next
  case (Trans c s c' s')  
  have "\<Gamma>\<turnstile>\<^sub>c (c, s) \<rightarrow>\<^sub>e (c', s') \<or> \<Gamma>\<turnstile>\<^sub>c (c, toSeq s) \<rightarrow> (c', toSeq s')"
    using Trans.hyps(1) step_ce_not_step_e_step_c by blast    
  then show ?case  
    by (metis (no_types) Trans.hyps(1) Trans.hyps(3) cptn.Cptn 
         last_ConsR list.simps(3))
qed
(*
  proof
    assume prem:"\<Gamma>\<turnstile>\<^sub>c (c, s) \<rightarrow>\<^sub>e (c', s')"       
    then have ceqc':"c=c'" using prem env_c_c'
      by auto           
    obtain xs where xs_s:"(\<Gamma>, (c', s') # xs) \<in> cptn \<and> (cf, sf) = last ((c', s') # xs)"
      using Trans(3) by auto 
    then have xs_f: "(\<Gamma>, (c, s)#(c', s') # xs) \<in> cptn" 
(*    using cptn.CptnEnv ceqc'  prem *)
    by (simp add: Trans.hyps(1) cptn.Cptn) (*by fastforce *)
    also have "last ((c', s') # xs) = last ((c,s)#(c', s') # xs)" by auto
    then have "(cf, sf) = last ((c, s) # (c', s') # xs)"
      using   xs_s by auto
    thus ?thesis
      using  xs_f by blast
  next
    assume prem:"\<Gamma>\<turnstile>\<^sub>c (c, toSeq s) \<rightarrow> (c', toSeq s')" 
    obtain xs where xs_s:"(\<Gamma>, (c', s') # xs) \<in> cptn \<and> (cf, sf) = last ((c', s') # xs) "
      using Trans(3) by auto 
    have "(\<Gamma>, (c, s) # (c', s') # xs) \<in> cptn" 
      using  Trans.hyps(1)
      by (simp add: cptn.Cptn xs_s) 
(*      using cptn1.Cptn1 xs_s by fastforce *)
    also have "last ((c', s') # xs) = last ((c,s)#(c', s') # xs)" by auto
    ultimately show ?thesis using xs_s by fastforce
  qed 
qed *)


lemma cptn_stepc_rtrancl:
  assumes cptn_step: "(\<Gamma>,(c, s)#xs) \<in> cptn" and
          cf_last:"(cf,sf) = (last ((c,s)#xs))"
  shows "\<Gamma>\<turnstile>\<^sub>c (c,s) \<rightarrow>\<^sub>c\<^sub>e\<^sup>* (cf,sf)"
using cptn_step cf_last
proof (induct xs arbitrary: c s) 
  case Nil
  thus ?case by simp 
next
  case (Cons a xs c s)   
  then obtain ca sa where eq_pair: "a=(ca,sa)" and "(cf, sf) = last ((ca,sa) # xs) " 
    using Cons by (fastforce)    
  then have "\<Gamma>\<turnstile>\<^sub>c (ca,sa) \<rightarrow>\<^sub>c\<^sub>e\<^sup>* (cf, sf)" using Cons
    using cptn_dest_pair by blast
  moreover have "\<Gamma>\<turnstile>\<^sub>c (c, s) \<rightarrow>\<^sub>c\<^sub>e (ca, sa)" using Cons eq_pair
    using cptn_elim_cases(2) by blast
  ultimately show ?case
    by auto
(*  have f1: "\<forall>f p pa. \<not> (f::'a \<Rightarrow> ('b, _, 'c,'d) LanguageCon.com option)\<turnstile>\<^sub>c p \<rightarrow> pa \<or> f\<turnstile>\<^sub>c p \<rightarrow>\<^sub>c\<^sub>e pa"
    by (simp add: c_step)
  have f2: "(\<Gamma>, (c, s) # (ca, sa) # xs) \<in> cptn"
    using `(\<Gamma>, (c, s) # a # xs) \<in> cptn` eq_pair by blast
  have f3: "\<forall>f p pa. \<not> (f::'a \<Rightarrow> ('b, _, 'c,'d) LanguageCon.com option)\<turnstile>\<^sub>c p \<rightarrow>\<^sub>e pa \<or> f\<turnstile>\<^sub>c p \<rightarrow>\<^sub>c\<^sub>e pa"
    using e_step by blast
  have "\<forall>c x. (\<Gamma>, (c, x) # xs) \<notin> cptn \<or> (cf, sf) \<noteq> last ((c, x) # xs) \<or> \<Gamma>\<turnstile>\<^sub>c (c, x) \<rightarrow>\<^sub>c\<^sub>e\<^sup>* (cf, sf)"
    using Cons.hyps by blast
  thus ?case
    using f3 f2 f1 by (metis (no_types) `(cf, sf) = last ((ca, sa) # xs)` converse_rtranclp_into_rtranclp cptn_elim_cases(2)) *)
qed

lemma cptn_stepc_rtran:
  assumes cptn_step: "(\<Gamma>,x#xs) \<in> cptn" and          
          a1:"Suc i < length (x#xs)"
  shows "\<Gamma>\<turnstile>\<^sub>c ((x#xs)!i) \<rightarrow>\<^sub>c\<^sub>e ((x#xs)!(Suc i))"
using cptn_step a1
proof (induct i arbitrary: x xs)
  case 0
    then obtain x1 xs1 where xs:"xs=x1#xs1"
      by (metis length_Cons less_not_refl list.exhaust list.size(3))    
    then have "\<Gamma>\<turnstile>\<^sub>c x \<rightarrow>\<^sub>c\<^sub>e x1"
        using "0.prems"(1) cptn_elim_cases_pair(2) by blast
    then show ?case
        by (simp add: xs)    
next
  case (Suc i)  
  then have "Suc i < length xs" by auto
  moreover obtain x1 xs1 where xs:"xs=x1#xs1"
    by (metis (full_types) calculation list.exhaust list.size(3) not_less0)  
  moreover have "\<Gamma>\<turnstile>\<^sub>c ((x1 # xs1) ! i) \<rightarrow>\<^sub>c\<^sub>e ((x1 # xs1) ! Suc i)" 
    using Suc
    using calculation(1) cptn_dest_pair xs by blast
  thus ?case using xs by auto
qed 
     
      
lemma cptn_stepconf_rtrancl:
  assumes cptn_step: "(\<Gamma>,cfg1#xs) \<in> cptn" and
          cf_last:"cfg2 = (last (cfg1#xs))"
  shows "\<Gamma>\<turnstile>\<^sub>c cfg1 \<rightarrow>\<^sub>c\<^sub>e\<^sup>* cfg2"
using cptn_step cf_last
by (metis cptn_stepc_rtrancl prod.collapse)

lemma cptn_all_steps_rtrancl:
  assumes cptn_step: "(\<Gamma>,cfg1#xs) \<in> cptn"          
  shows "\<forall>i<length (cfg1#xs). \<Gamma>\<turnstile>\<^sub>c cfg1 \<rightarrow>\<^sub>c\<^sub>e\<^sup>* ((cfg1#xs)!i)"
using cptn_step 
proof (induct xs arbitrary: cfg1)
  case Nil thus ?case by auto
next
  case (Cons x xs1) thus ?case
  proof -
     have hyp:"\<forall>i<length (x # xs1). \<Gamma>\<turnstile>\<^sub>c x \<rightarrow>\<^sub>c\<^sub>e\<^sup>* ((x # xs1) ! i)"
       using Cons.hyps Cons.prems cptn_dest_pair by blast      
     thus ?thesis
     proof
     {
        fix i
        assume a0:"i<length (cfg1 # x # xs1)"
        then have "Suc 0 < length (cfg1 # x # xs1)"
          by simp
        hence "\<Gamma>\<turnstile>\<^sub>c (cfg1 # x # xs1) ! 0 \<rightarrow>\<^sub>c\<^sub>e ((cfg1 # x # xs1) ! Suc 0)"
          using Cons.prems cptn_stepc_rtran by blast
        then have "\<Gamma>\<turnstile>\<^sub>c cfg1 \<rightarrow>\<^sub>c\<^sub>e x" using Cons by simp
        also have  "i < Suc (Suc (length xs1))"
          using a0 by force
        ultimately have "\<Gamma>\<turnstile>\<^sub>c cfg1 \<rightarrow>\<^sub>c\<^sub>e\<^sup>* (cfg1 # x # xs1) ! i" using hyp Cons
         using converse_rtranclp_into_rtranclp hyp less_Suc_eq_0_disj 
         by auto 
     } thus ?thesis by auto qed
  qed
qed


lemma last_not_F:
assumes 
  a0:"(\<Gamma>,xs)\<in>cptn"  
shows "snd (last xs) \<notin> Fault ` F \<Longrightarrow> \<forall>i < length xs. snd (xs!i) \<notin> Fault ` F"
using a0
proof(induct) print_cases
  case (CptnOne \<Gamma> p s) thus ?case by auto
next
  case (Cptn  \<Gamma> P s t xs) 
  thus ?case 
    by (metis (no_types, hide_lams) ce_not_normal_s image_iff last_ConsR length_Cons less_Suc_eq_0_disj list.simps(3) nth_Cons_0 
            nth_Cons_Suc snd_conv xstate.distinct(3)) 
qed

lemma Normal_Normal: 
assumes p1:"(\<Gamma>, (P, Normal s) # a # as) \<in> cptn" and       
        p2:"(\<exists>sb. snd (last ((P, Normal s) # a # as))  = Normal sb)"
shows "\<exists>sa. snd a = Normal sa"
proof -
   obtain la1 la2 where last_prod:"last ((P, Normal s)# a#as) = (la1,la2)" by fastforce
   obtain a1 a2 where a_prod:"a=(a1,a2)" by fastforce
   from p1 have clos_p_a:"\<Gamma>\<turnstile>\<^sub>c (P,Normal s) \<rightarrow>\<^sub>c\<^sub>e\<^sup>* (a1, a2)" 
     using a_prod cptn_elim_cases(2)
     by blast  
   then have "\<Gamma>\<turnstile>\<^sub>c (fst a, snd a) \<rightarrow>\<^sub>c\<^sub>e\<^sup>*  (la1,la2)"
     by (metis cptn_stepconf_rtrancl last_ConsR last_prod list.distinct(1) 
          p1 prod.exhaust_sel tl_in_cptn)  
   moreover obtain bb where "Normal bb = la2" using last_prod p2 by auto
   ultimately show ?thesis by (metis (no_types)  steps_ce_not_Normal)
qed

lemma skip_all_skip:
  assumes a0:"(\<Gamma>,cfg)\<in>cptn" and
          a1:"cfg = (Skip,s)#cfg1"
  shows "\<forall>i<length cfg. fst(cfg!i) = Skip"
using a0 a1
proof(induct cfg1 arbitrary:cfg s)
  case Nil thus ?case by auto
next
  case (Cons x xs)  
  have cptn:"(\<Gamma>,x#xs)\<in>cptn"
    using Cons.prems(1) Cons.prems(2) cptn_dest_pair by blast
  have "\<Gamma>\<turnstile>\<^sub>c(Skip,s) \<rightarrow>\<^sub>e x" using cptn_elim_cases_pair(2)[OF Cons(2)[simplified Cons(3)]]
    by (metis step_ce_dest stepc_elim_cases(1))   
  then obtain s' where x:"x = (Skip,s')"
    by (metis env_c_c' prod.exhaust_sel)    
  moreover have cptn:"(\<Gamma>,x#xs)\<in>cptn"
    using Cons.prems(1) Cons.prems(2) cptn_dest_pair by blast
  moreover have 
    xs:"x # xs = (LanguageCon.com.Skip, s') # xs" using x by auto
  ultimately show ?case using Cons(1)[OF cptn xs] Cons(3)
    using diff_Suc_1 fstI length_Cons less_Suc_eq_0_disj nth_Cons' by auto 
qed

lemma skip_all_skip_throw:
  assumes a0:"(\<Gamma>,cfg)\<in>cptn" and
          a1:"cfg = (Throw,s)#cfg1"
  shows "\<forall>i<length cfg. fst(cfg!i) = Skip \<or> fst(cfg!i) = Throw"
using a0 a1
proof(induct cfg1 arbitrary:cfg s)
  case Nil thus ?case by auto
next
  case (Cons x xs)
  have cptn:"(\<Gamma>,x#xs)\<in>cptn"
    using Cons.prems(1) Cons.prems(2) cptn_dest_pair by blast
  have ce:"\<Gamma>\<turnstile>\<^sub>c(Throw,s) \<rightarrow>\<^sub>c\<^sub>e x" 
    by (auto intro:cptn_elim_cases_pair(2)[OF Cons(2)[simplified Cons(3)]])
  then obtain s' where x:"x = (Skip,s') \<or> x = (Throw, s')"
    using ce_Throw_toSkip 
    by (metis eq_fst_iff)      
  show ?case using x
  proof 
    assume "x=(Skip,s')" thus ?thesis using skip_all_skip Cons(3)
      using cptn fstI length_Cons less_Suc_eq_0_disj nth_Cons' nth_Cons_Suc skip_all_skip 
      by fastforce 
  next
    assume x:"x=(Throw,s')"
    moreover have cptn:"(\<Gamma>,x#xs)\<in>cptn"
      using Cons.prems(1) Cons.prems(2) cptn_dest_pair by blast
    moreover have 
      xs:"x # xs = (LanguageCon.com.Throw, s') # xs" using x by auto
    ultimately show ?case using Cons(1)[OF cptn xs] Cons(3)
    using diff_Suc_1 fstI length_Cons less_Suc_eq_0_disj nth_Cons' by auto 
  qed  
qed


lemma cptn_env_same_prog:
assumes a0: "(\<Gamma>, l) \<in> cptn" and
        a1:  "\<forall>k < j. (\<Gamma>\<turnstile>\<^sub>c(l!k)  \<rightarrow>\<^sub>e (l!(Suc k)))" and
        a2: "Suc j < length l"
shows "fst (l!j) =  fst (l!0)"
using a0 a1 a2
proof (induct j arbitrary: l)
  case 0 thus ?case by auto
next
  case (Suc j) 
    then have "fst (l!j) =  fst (l!0)" by fastforce
    thus ?case using Suc 
      by (metis (no_types) env_c_c' lessI prod.collapse)
  qed



lemma takecptn_is_cptn [rule_format, elim!]:
  "\<forall>j. (\<Gamma>,c) \<in> cptn \<longrightarrow> (\<Gamma>, take (Suc j) c) \<in> cptn"
apply(induct "c")
 apply(force elim: cptn.cases)
apply clarify
apply(case_tac j)
 apply simp
 apply(rule CptnOne)
apply simp
apply(force intro:cptn.intros elim:cptn.cases)
done



lemma dropcptn_is_cptn [rule_format,elim!]:
  "\<forall>j<length c. (\<Gamma>,c) \<in> cptn \<longrightarrow> (\<Gamma>, drop j c) \<in> cptn"
apply(induct "c")
 apply(force elim: cptn.cases)
apply clarify
apply(case_tac j,simp+)
apply(erule cptn.cases)
  apply simp
 apply force
  done

subsection\<open>Modular Definition of Computation\<close>
definition lift :: "('g\<times>'l,'p,'f,'e)com  \<Rightarrow> ('g, 'l, 'p,'f,'e) config_gs \<Rightarrow> ('g, 'l, 'p,'f,'e) config_gs" where
  "lift Q \<equiv> \<lambda>(P, s).  ((Seq P Q), s)" 

definition lift_catch :: "('g\<times>'l,'p,'f,'e)com  \<Rightarrow> ('g, 'l, 'p,'f,'e) config_gs \<Rightarrow> ('g, 'l, 'p,'f,'e) config_gs" where
  "lift_catch Q \<equiv> \<lambda>(P, s).  (Catch P Q, s)"     

lemma map_lift_eq_xs_xs':"map (lift a) xs = map (lift a) xs' \<Longrightarrow> xs=xs'" 
proof (induct xs arbitrary: xs')
  case Nil thus ?case by auto
next
  case (Cons x xsa)
  then have a0:"(lift a) x # map (lift a) xsa = map (lift a) (x # xsa)"
    by fastforce 
  also obtain x' xsa' where xs':"xs' = x'#xsa'" 
    using Cons by auto
  ultimately have a1:"map (lift a) (x # xsa) =map (lift a) (x' # xsa')"
    using Cons by auto
  then have xs:"xsa=xsa'" using a0 a1 Cons by fastforce
  then have "(lift a) x' = (lift a) x" using a0 a1  by auto
  then have "x' = x" unfolding lift_def
    by (metis (no_types, lifting) LanguageCon.com.inject(3) 
               case_prod_beta old.prod.inject prod.collapse)   
  thus ?case using xs xs' by auto
qed

lemma map_lift_catch_eq_xs_xs':"map (lift_catch a) xs = map (lift_catch a) xs' \<Longrightarrow> xs=xs'" 
proof (induct xs arbitrary: xs')
  case Nil thus ?case by auto
next
  case (Cons x xsa)
  then have a0:"(lift_catch a) x # map (lift_catch a) xsa = map (lift_catch a) (x # xsa)"
    by auto 
  also obtain x' xsa' where xs':"xs' = x'#xsa'" 
    using Cons by auto
  ultimately have a1:"map (lift_catch a) (x # xsa) =map (lift_catch a) (x' # xsa')"
    using Cons by auto  
  then have xs:"xsa=xsa'" using a0 a1 Cons by fastforce  
  then have "(lift_catch a) x' = (lift_catch a) x" using a0 a1  by auto
  then have "x' = x" unfolding lift_catch_def
    by (metis (no_types, lifting) LanguageCon.com.inject(9) 
               case_prod_beta old.prod.inject prod.collapse)   
  thus ?case using xs xs' by auto
qed

lemma map_lift_all_seq:
 assumes a0:"zs=map (lift a) xs" and
         a1:"i<length zs"
 shows "\<exists>b. fst (zs!i) = Seq b a"
using a0 a1
proof (induct zs arbitrary: xs i)
  case Nil thus ?case by auto
next
  case (Cons z1 zsa) thus ?case unfolding lift_def
  proof -
    assume a1: "z1 # zsa = map (\<lambda>b. case b of (P, s) \<Rightarrow> (LanguageCon.com.Seq P a, s)) xs"
    have "\<forall>p c. \<exists>x. \<forall>pa ca xa. 
            (pa \<noteq> (ca::('a, 'b, 'c, 'd) LanguageCon.com, xa::('a, 'c) xstate) \<or> ca = fst pa) \<and> 
            ((c::('a, 'b, 'c, 'd) LanguageCon.com) \<noteq> fst p \<or> (c, x::('a, 'c) xstate) = p)"
      by fastforce
    then obtain xx :: "('a, 'b, 'c, 'd) LanguageCon.com \<times> ('a, 'c) xstate \<Rightarrow> ('a, 'b, 'c, 'd) LanguageCon.com \<Rightarrow> ('a, 'c) xstate" where
      "\<And>p c x ca pa. (p \<noteq> (c::('a, 'b, 'c, 'd) LanguageCon.com, x::('a, 'c) xstate) \<or> c = fst p) \<and> (ca \<noteq> fst pa \<or> (ca, xx pa ca) = pa)"
      by (metis (full_types))  
    then show ?thesis
      using a1 \<open>i < length (z1 # zsa)\<close>
      by (simp add: Cons.hyps Cons.prems(1) case_prod_beta')
  qed
qed

lemma map_lift_catch_all_catch:
 assumes a0:"zs=map (lift_catch a) xs" and
         a1:"i<length zs"
 shows "\<exists>b. fst (zs!i) = Catch b a"
using a0 a1
proof (induct zs arbitrary: xs i)
  case Nil thus ?case by auto
next
  case (Cons z1 zsa) thus ?case unfolding lift_catch_def
  proof -
    assume a1: "z1 # zsa = map (\<lambda>b. case b of (P, s) \<Rightarrow> (LanguageCon.com.Catch P a, s)) xs"
    have "\<forall>p c. \<exists>x. \<forall>pa ca xa. 
            (pa \<noteq> (ca::('a, 'b, 'c, 'd) LanguageCon.com, xa::('a, 'c) xstate) \<or> ca = fst pa) \<and> 
            ((c::('a, 'b, 'c, 'd) LanguageCon.com) \<noteq> fst p \<or> (c, x::('a, 'c) xstate) = p)"
      by fastforce
    then obtain xx :: "('a, 'b, 'c, 'd) LanguageCon.com \<times> ('a, 'c) xstate \<Rightarrow> ('a, 'b, 'c, 'd) LanguageCon.com \<Rightarrow> ('a, 'c) xstate" where
      "\<And>p c x ca pa. (p \<noteq> (c::('a, 'b, 'c, 'd) LanguageCon.com, x::('a, 'c) xstate) \<or> c = fst p) \<and> (ca \<noteq> fst pa \<or> (ca, xx pa ca) = pa)"
      by (metis (full_types))  
    then show ?thesis
      using a1 \<open>i < length (z1 # zsa)\<close>
      by (simp add: Cons.hyps Cons.prems(1) case_prod_beta')
  qed
qed

lemma map_lift_some_eq_pos:
 assumes a0:"map (lift P) xs @ (P1, s1)#ys = 
             map (lift P) xs'@ (P2, s2)#ys'" and
         a1:"\<forall>p0. P1\<noteq>Seq p0 P" and
         a2:"\<forall>p0. P2\<noteq>Seq p0 P" 
 shows "length xs = length xs'"
proof -
  {assume ass:"length xs \<noteq> length xs'"
   { assume ass:"length xs < length xs'"
     then have False using a0  map_lift_all_seq a1 a2
     by (metis (no_types, lifting) fst_conv length_map nth_append nth_append_length)
   }note l=this
   { assume ass:"length xs > length xs'"
     then have False using a0  map_lift_all_seq a1 a2
     by (metis (no_types, lifting) fst_conv length_map nth_append nth_append_length)
   }  then have False using l ass by fastforce
  }
  thus ?thesis by auto
qed

lemma map_lift_some_eq:
 assumes a0:"map (lift P) xs @ (P1, s1)#ys = 
             map (lift P) xs'@ (P2, s2)#ys'" and
        a1:"\<forall>p0. P1\<noteq>Seq p0 P" and
        a2:"\<forall>p0. P2\<noteq>Seq p0 P" 
 shows "xs' = xs \<and> ys = ys'"
proof -
  have "length xs = length xs'" using a0 map_lift_some_eq_pos a1 a2 by blast
  also have "xs' = xs" using a0 assms calculation map_lift_eq_xs_xs' by fastforce
  ultimately show ?thesis using a0 by fastforce
qed

lemma map_lift_catch_some_eq_pos:
 assumes a0:"map (lift_catch P) xs @ (P1, s1)#ys = 
             map (lift_catch P) xs'@ (P2, s2)#ys'" and
         a1:"\<forall>p0. P1\<noteq>Catch p0 P" and
         a2:"\<forall>p0. P2\<noteq>Catch p0 P" 
 shows "length xs = length xs'"
proof -
  {assume ass:"length xs \<noteq> length xs'"
   { assume ass:"length xs < length xs'"
     then have False using a0  map_lift_catch_all_catch a1 a2
     by (metis (no_types, lifting) fst_conv length_map nth_append nth_append_length)
   }note l=this
   { assume ass:"length xs > length xs'"
     then have False using a0  map_lift_catch_all_catch a1 a2
     by (metis (no_types, lifting) fst_conv length_map nth_append nth_append_length)
   }  then have False using l ass by fastforce
  }
  thus ?thesis by auto
qed

lemma map_lift_catch_some_eq:
 assumes a0:"map (lift_catch P) xs @ (P1, s1)#ys = 
             map (lift_catch P) xs'@ (P2, s2)#ys'" and
        a1:"\<forall>p0. P1\<noteq>Catch p0 P" and
        a2:"\<forall>p0. P2\<noteq>Catch p0 P" 
 shows "xs' = xs \<and> ys = ys'"
proof -
  have "length xs = length xs'" using a0 map_lift_catch_some_eq_pos a1 a2 by blast
  also have "xs' = xs" using a0 assms calculation map_lift_catch_eq_xs_xs' by fastforce
  ultimately show ?thesis using a0 by fastforce
qed



inductive_set cptn_mod :: "(('g,'l,'p,'f,'e) confs) set"
where
  CptnModOne: "(\<Gamma>,[(P, s)]) \<in> cptn_mod"
| CptnModEnv: "\<lbrakk>\<Gamma>\<turnstile>\<^sub>c(P,s) \<rightarrow>\<^sub>e (P,t);(\<Gamma>,(P, t)#xs) \<in> cptn_mod \<rbrakk> \<Longrightarrow> 
               (\<Gamma>,(P, s)#(P, t)#xs) \<in> cptn_mod"
| CptnModSkip: "\<lbrakk>\<Gamma>\<turnstile>\<^sub>c(P,toSeq s) \<rightarrow> (Skip,toSeq t); redex P = P;
                \<forall>ns ns'. 
                  (s = Normal ns \<or> s = Abrupt ns) \<and> 
                  (t = Normal ns' \<or> t = Abrupt ns') \<longrightarrow> snd ns = snd ns';
                (\<Gamma>,(Skip, t)#xs) \<in> cptn_mod \<rbrakk> \<Longrightarrow> 
                (\<Gamma>,(P,s)#(Skip, t)#xs) \<in>cptn_mod"

| CptnModThrow: "\<lbrakk>\<Gamma>\<turnstile>\<^sub>c(P,toSeq s) \<rightarrow> (Throw,toSeq t); redex P = P;
                \<forall>ns ns'. 
                  (s = Normal ns \<or> s = Abrupt ns) \<and> 
                  (t = Normal ns' \<or> t = Abrupt ns') \<longrightarrow> snd ns = snd ns';
                (\<Gamma>,(Throw, t)#xs) \<in> cptn_mod \<rbrakk> \<Longrightarrow> 
                (\<Gamma>,(P,s)#(Throw, t)#xs) \<in>cptn_mod"

| CptnModCondT: "\<lbrakk>(\<Gamma>,(P0, Normal s)#ys) \<in> cptn_mod; fst s \<in> b \<rbrakk> \<Longrightarrow> 
                (\<Gamma>,((Cond b P0 P1), Normal s)#(P0, Normal s)#ys) \<in> cptn_mod"
| CptnModCondF: "\<lbrakk>(\<Gamma>,(P1, Normal s)#ys) \<in> cptn_mod; fst s \<notin> b \<rbrakk> \<Longrightarrow> 
                (\<Gamma>,((Cond b P0 P1), Normal s)#(P1, Normal s)#ys) \<in> cptn_mod"
| CptnModSeq1: 
  "\<lbrakk>(\<Gamma>,(P0, s)#xs) \<in> cptn_mod; zs=map (lift P1) xs \<rbrakk> \<Longrightarrow> 
   (\<Gamma>,((Seq P0 P1), s)#zs) \<in> cptn_mod"

| CptnModSeq2: 
  "\<lbrakk>(\<Gamma>, (P0, s)#xs) \<in> cptn_mod; fst(last ((P0, s)#xs)) = Skip;
    (\<Gamma>,(P1, snd(last ((P0, s)#xs)))#ys) \<in> cptn_mod;
    zs=(map (lift P1) xs)@((P1, snd(last ((P0, s)#xs)))#ys) \<rbrakk> \<Longrightarrow> 
   (\<Gamma>,((Seq P0 P1), s)#zs) \<in> cptn_mod"
(*| CptnModSeq3:
  "\<lbrakk> (\<Gamma>,(P1, s)#xs) \<in> cptn_mod\<rbrakk> \<Longrightarrow> (\<Gamma>,((Seq Skip P1), s)#(P1, s)#xs) \<in> cptn_mod"*)

| CptnModSeq3: 
  "\<lbrakk>(\<Gamma>, (P0, Normal s)#xs) \<in> cptn_mod; 
    fst(last ((P0, Normal s)#xs)) = Throw;
    snd(last ((P0, Normal s)#xs)) = Normal s'; 
    (\<Gamma>,(Throw,Normal s')#ys) \<in> cptn_mod; 
    zs=(map (lift P1) xs)@((Throw,Normal s')#ys) \<rbrakk> \<Longrightarrow>
   (\<Gamma>,((Seq P0 P1), Normal s)#zs) \<in> cptn_mod"

| CptnModWhile1: 
  "\<lbrakk>(\<Gamma>, (P, Normal s)#xs) \<in> cptn_mod; fst s \<in> b; 
    zs=map (lift (While b P)) xs \<rbrakk> \<Longrightarrow> 
    (\<Gamma>, ((While b P), Normal s)#
      ((Seq P (While b P)),Normal s)#zs) \<in> cptn_mod"

| CptnModWhile2: 
  "\<lbrakk> (\<Gamma>, (P, Normal s)#xs) \<in> cptn_mod; 
     fst(last ((P, Normal s)#xs))=Skip; fst s \<in> b; 
     zs=(map (lift (While b P)) xs)@
      (While b P, snd(last ((P, Normal s)#xs)))#ys; 
      (\<Gamma>,(While b P, snd(last ((P, Normal s)#xs)))#ys) \<in> 
        cptn_mod\<rbrakk> \<Longrightarrow> 
   (\<Gamma>,(While b P, Normal s)#
     (Seq P (While b P), Normal s)#zs) \<in> cptn_mod"

| CptnModWhile3: 
  "\<lbrakk> (\<Gamma>, (P, Normal s)#xs) \<in> cptn_mod; 
     fst(last ((P, Normal s)#xs))=Throw; fst s \<in> b;
     snd(last ((P, Normal s)#xs)) = Normal s'; 
    (\<Gamma>,(Throw,Normal s')#ys) \<in> cptn_mod;  
     zs=(map (lift (While b P)) xs)@((Throw,Normal s')#ys)\<rbrakk> \<Longrightarrow> 
   (\<Gamma>,(While b P, Normal s)#
     (Seq P (While b P), Normal s)#zs) \<in> cptn_mod"

| CptnModCall: "\<lbrakk>(\<Gamma>,(bdy, Normal s)#ys) \<in> cptn_mod;\<Gamma> p = Some bdy; bdy\<noteq>Call p \<rbrakk> \<Longrightarrow> 
                (\<Gamma>,((Call p), Normal s)#(bdy, Normal s)#ys) \<in> cptn_mod" 
| CptnModDynCom: "\<lbrakk>(\<Gamma>,(c (fst s), Normal s)#ys) \<in> cptn_mod \<rbrakk> \<Longrightarrow> 
                  (\<Gamma>,(DynCom c, Normal s)#(c (fst s), Normal s)#ys) \<in> cptn_mod"

| CptnModGuard: "\<lbrakk>(\<Gamma>,(c, Normal s)#ys) \<in> cptn_mod; fst s \<in> g \<rbrakk> \<Longrightarrow> 
                 (\<Gamma>,(Guard f g c, Normal s)#(c, Normal s)#ys) \<in> cptn_mod"

| CptnModCatch1: "\<lbrakk>(\<Gamma>,(P0, s)#xs) \<in> cptn_mod; zs=map (lift_catch P1) xs \<rbrakk>
                 \<Longrightarrow> (\<Gamma>,((Catch P0 P1), s)#zs) \<in> cptn_mod"
| CptnModCatch2: 
  "\<lbrakk>(\<Gamma>, (P0, s)#xs) \<in> cptn_mod; fst(last ((P0, s)#xs)) = Skip; 
    (\<Gamma>,(Skip,snd(last ((P0, s)#xs)))#ys) \<in> cptn_mod;  
    zs=(map (lift_catch P1) xs)@((Skip,snd(last ((P0, s)#xs)))#ys) \<rbrakk> \<Longrightarrow> 
   (\<Gamma>,((Catch P0 P1), s)#zs) \<in> cptn_mod"

| CptnModCatch3: 
  "\<lbrakk>(\<Gamma>, (P0, Normal s)#xs) \<in> cptn_mod; fst(last ((P0, Normal s)#xs)) = Throw; 
  snd(last ((P0, Normal s)#xs)) = Normal s';
  (\<Gamma>,(P1, snd(last ((P0, Normal s)#xs)))#ys) \<in> cptn_mod; 
  zs=(map (lift_catch P1) xs)@((P1, snd(last ((P0, Normal s)#xs)))#ys) \<rbrakk> \<Longrightarrow> 
   (\<Gamma>,((Catch P0 P1), Normal s)#zs) \<in> cptn_mod"


lemmas CptnMod_induct = cptn_mod.induct [of _ "[(c,s)]", split_format (complete), case_names
CptnModOne CptnModEnv CptnModSkip CptnModThrow CptnModCondT CptnModCondF 
CptnModSeq1 CptnModSeq2 CptnModSeq3 CptnModSeq4 CptnModWhile1 CptnModWhile2 CptnModWhile3 CptnModCall CptnModDynCom CptnModGuard 
CptnModCatch1 CptnModCatch2 CptnModCatch3, induct set]

inductive_cases CptnMod_elim_cases [cases set]:
"(\<Gamma>,(Skip, s)#u#xs) \<in> cptn_mod"
"(\<Gamma>,(Guard f g c, s)#u#xs) \<in> cptn_mod"
"(\<Gamma>,(Basic f e, s)#u#xs) \<in> cptn_mod"
"(\<Gamma>,(Spec r e, s)#u#xs) \<in> cptn_mod"
"(\<Gamma>,(Seq c1 c2, s)#u#xs) \<in> cptn_mod"
"(\<Gamma>,(Cond b c1 c2, s)#u#xs) \<in> cptn_mod"
"(\<Gamma>,(Await b c2 e, s)#u#xs) \<in> cptn_mod"
"(\<Gamma>,(Call p, s)#u#xs) \<in> cptn_mod"
"(\<Gamma>,(DynCom c,s)#u#xs) \<in> cptn_mod"
"(\<Gamma>,(Throw,s)#u#xs) \<in> cptn_mod"
"(\<Gamma>,(Catch c1 c2,s)#u#xs) \<in> cptn_mod"


inductive_cases CptnMod_Normal_elim_cases [cases set]:
"(\<Gamma>,(Skip, Normal s)#u#xs) \<in> cptn_mod"
"(\<Gamma>,(Guard f g c, Normal s)#u#xs) \<in> cptn_mod"
"(\<Gamma>,(Basic f e, Normal s)#u#xs) \<in> cptn_mod"
"(\<Gamma>,(Spec r e, Normal s)#u#xs) \<in> cptn_mod"
"(\<Gamma>,(Seq c1 c2, Normal s)#u#xs) \<in> cptn_mod"
"(\<Gamma>,(Cond b c1 c2, Normal s)#u#xs) \<in> cptn_mod"
"(\<Gamma>,(Await b c2 e, Normal s)#u#xs) \<in> cptn_mod"
"(\<Gamma>,(Call p, Normal s)#u#xs) \<in> cptn_mod"
"(\<Gamma>,(DynCom c,Normal s)#u#xs) \<in> cptn_mod"
"(\<Gamma>,(Throw,Normal s)#u#xs) \<in> cptn_mod"
"(\<Gamma>,(Catch c1 c2,Normal s)#u#xs) \<in> cptn_mod"
"(\<Gamma>,(P,Normal s)#(P,s')#xs) \<in> cptn_mod"
"(\<Gamma>,(P,Abrupt s)#(P,Abrupt s')#xs) \<in> cptn_mod"
"(\<Gamma>,(P,Stuck)#(P,Stuck)#xs) \<in> cptn_mod"
"(\<Gamma>,(P,Fault f)#(P,Fault f)#xs) \<in> cptn_mod"

inductive_cases CptnMod_env_elim_cases [cases set]:
"(\<Gamma>,(P,Normal s)#(P,s')#xs) \<in> cptn_mod"
"(\<Gamma>,(P,Abrupt s)#(P,Abrupt s')#xs) \<in> cptn_mod"
"(\<Gamma>,(P,Stuck)#(P,Stuck)#xs) \<in> cptn_mod"
"(\<Gamma>,(P,Fault f)#(P,Fault f)#xs) \<in> cptn_mod"

subsection \<open>Equivalence of small semantics and computational\<close>

definition catch_cond 
where
"catch_cond zs Q xs P s s'' s' \<Gamma> \<equiv> (zs=(map (lift_catch Q) xs) \<or>
             ((fst(((P, s)#xs)!length xs)=Throw \<and>
               snd(last ((P, s)#xs)) = Normal s' \<and> s=Normal s''\<and>
               (\<exists>ys. (\<Gamma>,(Q, snd(((P, s)#xs)!length xs))#ys) \<in> cptn_mod \<and> 
                zs=(map (lift_catch Q) xs)@((Q, snd(((P, s)#xs)!length xs))#ys)))) \<or>
                ((fst(((P, s)#xs)!length xs)=Skip \<and> 
                 (\<exists>ys. (\<Gamma>,(Skip,snd(last ((P, s)#xs)))#ys) \<in> cptn_mod \<and>                   
                 zs=(map (lift_catch Q) xs)@((Skip,snd(last ((P, s)#xs)))#ys)))))
"

lemma div_catch: assumes cptn_m:"(\<Gamma>,list) \<in> cptn_mod"
shows "(\<forall>s P Q zs. list=(Catch P Q, s)#zs \<longrightarrow>
       (\<exists>xs s' s''. 
          (\<Gamma>,(P, s)#xs) \<in> cptn_mod  \<and> 
             catch_cond zs Q xs P s s'' s' \<Gamma>))  
            "
unfolding catch_cond_def
using cptn_m
proof (induct rule: cptn_mod.induct)
case (CptnModOne \<Gamma> P s)
  thus ?case using cptn_mod.CptnModOne by blast 
next
  case (CptnModSkip  \<Gamma> P s t xs) 
  from CptnModSkip.hyps
  have step: "\<Gamma>\<turnstile>\<^sub>c (P, toSeq s) \<rightarrow> (Skip, toSeq t)" by auto
  from CptnModSkip.hyps
  have noskip: "~(P=Skip)" using stepc_elim_cases(1) by blast  
  have no_catch: "\<forall>p1 p2. \<not>(P=Catch p1 p2)" using CptnModSkip.hyps(2) redex_not_Catch by auto
  from CptnModSkip.hyps
  have in_cptn_mod: "(\<Gamma>, (Skip, t) # xs) \<in> cptn_mod" by auto  
  then show ?case using no_catch by simp
next
  case (CptnModThrow  \<Gamma> P s t xs) 
  from CptnModThrow.hyps
  have step: "\<Gamma>\<turnstile>\<^sub>c (P, toSeq s) \<rightarrow> (Throw, toSeq t)" by auto 
  from CptnModThrow.hyps
  have in_cptn_mod: "(\<Gamma>, (Throw, t) # xs) \<in> cptn_mod" by auto 
  have no_catch: "\<forall>p1 p2. \<not>(P=Catch p1 p2)" using CptnModThrow.hyps(2) redex_not_Catch by auto
  then show ?case by auto
next
  case (CptnModCondT \<Gamma> P0 s ys b P1)
  thus ?case using CptnModOne by blast
next
  case (CptnModCondF \<Gamma> P0 s ys b P1)
  thus ?case using CptnModOne by blast
next
  case (CptnModCatch1 sa P Q zs)
  thus ?case by blast
next
  case (CptnModCatch2 \<Gamma> P0 s xs ys zs P1) 
  from CptnModCatch2.hyps(3) 
  have last:"fst (((P0, s) # xs) ! length xs) = Skip" 
       by (simp add: last_length) 
  have P0cptn:"(\<Gamma>, (P0, s) # xs) \<in> cptn_mod" by fact          
  then have "zs = map (lift_catch P1) xs @((Skip,snd(last ((P0, s)#xs)))#ys)" by (simp add:CptnModCatch2.hyps)
  show ?case
  proof -{
    fix sa P Q zsa    
    assume eq:"(Catch P0 P1, s) # zs = (Catch P Q, sa) # zsa"
    then have "P0 =P \<and> P1 = Q \<and> s=sa \<and> zs=zsa" by auto
    then have "(P0, s) = (P, sa)" by auto 
    have "last ((P0, s) # xs) = ((P, sa) # xs) ! length xs"
      by (simp add: `P0 = P \<and> P1 = Q \<and> s = sa \<and> zs = zsa` last_length)
    then have "zs = (map (lift_catch Q) xs)@((Skip,snd(last ((P0, s)#xs)))#ys)"
      using `P0 = P \<and> P1 = Q \<and> s = sa \<and> zs = zsa` `zs = map (lift_catch P1) xs @ ((Skip,snd(last ((P0, s)#xs)))#ys)` 
      by force    
    then have "(\<exists>xs s' s''. ((\<Gamma>,(P, s)#xs) \<in> cptn_mod  \<and> 
             ((zs=(map (lift_catch Q) xs) \<or>
             ((fst(((P, s)#xs)!length xs)=Throw \<and>
               snd(last ((P, s)#xs)) = Normal s' \<and>  s=Normal s''\<and>
               (\<exists>ys. (\<Gamma>,(Q, snd(((P, s)#xs)!length xs))#ys) \<in> cptn_mod \<and> 
                zs=(map (lift_catch Q) xs)@((Q, snd(((P, s)#xs)!length xs))#ys)))) \<or>
                (\<exists>ys. ((fst(((P, s)#xs)!length xs)=Skip \<and> (\<Gamma>,(Skip,snd(last ((P, s)#xs)))#ys) \<in> cptn_mod \<and>                 
                 zs=(map (lift_catch Q) xs)@((Skip,snd(last ((P0, s)#xs)))#ys))))))))"
    using P0cptn  `P0 = P \<and> P1 = Q \<and> s = sa \<and> zs = zsa`  last  CptnModCatch2.hyps(4) by blast 
   } 
   thus ?thesis by auto
  qed
next
  case (CptnModCatch3 \<Gamma> P0 s xs s' P1 ys zs)
  from CptnModCatch3.hyps(3)  
  have last:"fst (((P0, Normal s) # xs) ! length xs) = Throw" 
       by (simp add: last_length) 
  from CptnModCatch3.hyps(4) 
  have lastnormal:"snd (last ((P0, Normal s) # xs)) = Normal s'"
      by (simp add: last_length)
  have P0cptn:"(\<Gamma>, (P0, Normal s) # xs) \<in> cptn_mod" by fact
  from CptnModCatch3.hyps(5) have P1cptn:"(\<Gamma>, (P1, snd (((P0, Normal s) # xs) ! length xs)) # ys) \<in> cptn_mod"
      by (simp add: last_length)          
  then have "zs = map (lift_catch P1) xs @ (P1, snd (last ((P0, Normal s) # xs))) # ys" by (simp add:CptnModCatch3.hyps)
  show ?case
  proof -{
    fix sa P Q zsa    
    assume eq:"(Catch P0 P1, Normal s) # zs = (Catch P Q, Normal sa) # zsa"
    then have "P0 =P \<and> P1 = Q \<and> Normal s= Normal sa \<and> zs=zsa" by auto     
    have "last ((P0, Normal s) # xs) = ((P, Normal sa) # xs) ! length xs"
      by (simp add: `P0 = P \<and> P1 = Q \<and> Normal s = Normal sa \<and> zs = zsa` last_length)
    then have "zsa = map (lift_catch Q) xs @ (Q, snd (((P, Normal sa) # xs) ! length xs)) # ys"
      using `P0 = P \<and> P1 = Q \<and> Normal s = Normal sa \<and> zs = zsa` `zs = map (lift_catch P1) xs @ (P1, snd (last ((P0, Normal s) # xs))) # ys` by force
    then have "(\<Gamma>, (P, Normal s) # xs) \<in> cptn_mod \<and> (fst(((P, Normal s)#xs)!length xs)=Throw \<and>
               snd(last ((P, Normal s)#xs)) = Normal s' \<and> 
              (\<exists>ys. (\<Gamma>,(Q, snd(((P, Normal s)#xs)!length xs))#ys) \<in> cptn_mod \<and> 
              zs=(map (lift_catch Q) xs)@((Q, snd(((P, Normal s)#xs)!length xs))#ys)))" 
      using lastnormal P1cptn P0cptn `P0 = P \<and> P1 = Q \<and> Normal s = Normal sa \<and> zs = zsa` last 
       by auto    
    }note this [of P0 P1 s zs] thus ?thesis by blast qed
next
  case (CptnModEnv \<Gamma> P s t xs)  
  then have step:"(\<Gamma>, (P, t) # xs) \<in> cptn_mod" by auto  
  have step_e: "\<Gamma>\<turnstile>\<^sub>c (P, s) \<rightarrow>\<^sub>e (P, t)" using CptnModEnv by auto
  show ?case     
    proof (cases P)
      case (Catch P1 P2) 
      then have eq_P_Catch:"(P, t) # xs = (LanguageCon.com.Catch P1 P2, t) # xs" by auto      
      then  obtain xsa t' t'' where 
         p1:"(\<Gamma>, (P1, t) # xsa) \<in> cptn_mod" and p2:"
     (xs = map (lift_catch P2) xsa \<or>
      fst (((P1, t) # xsa) ! length xsa) = LanguageCon.com.Throw \<and>
      snd (last ((P1, t) # xsa)) = Normal t' \<and>
      t = Normal t'' \<and>
      (\<exists>ys. (\<Gamma>, (P2, snd (((P1, t) # xsa) ! length xsa)) # ys) \<in> cptn_mod \<and>
            xs =
            map (lift_catch P2) xsa @
            (P2, snd (((P1, t) # xsa) ! length xsa)) # ys) \<or>
            fst (((P1, t) # xsa) ! length xsa) = LanguageCon.com.Skip \<and>
            (\<exists>ys.(\<Gamma>,(Skip,snd(last ((P1, t)#xsa)))#ys) \<in> cptn_mod \<and> 
            xs = map (lift_catch P2) xsa @
            ((LanguageCon.com.Skip, snd (last ((P1, t) # xsa)))#ys)))" 
        using CptnModEnv(3) by auto
      have all_step:"(\<Gamma>, (P1, s)#((P1, t) # xsa)) \<in> cptn_mod"              
          using cptn_mod.CptnModEnv env_intro p1 step_e by blast                           
      show ?thesis using p2 
      proof  
        assume "xs = map (lift_catch P2) xsa"
        have "(P, t) # xs = map (lift_catch P2) ((P1, t) # xsa)"
          by (simp add: `xs = map (lift_catch P2) xsa` lift_catch_def local.Catch)
        thus ?thesis using all_step eq_P_Catch by fastforce
      next 
        assume 
         "fst (((P1, t) # xsa) ! length xsa) = LanguageCon.com.Throw \<and>
          snd (last ((P1, t) # xsa)) = Normal t' \<and>
          t = Normal t'' \<and>
          (\<exists>ys. (\<Gamma>, (P2, snd (((P1, t) # xsa) ! length xsa)) # ys) \<in> cptn_mod \<and>
                xs =
                map (lift_catch P2) xsa @
                (P2, snd (((P1, t) # xsa) ! length xsa)) # ys) \<or>
                fst (((P1, t) # xsa) ! length xsa) = LanguageCon.com.Skip \<and>
           (\<exists>ys. (\<Gamma>,(Skip,snd(last ((P1, t)#xsa)))#ys) \<in> cptn_mod \<and> 
            xs = map (lift_catch P2) xsa @
            ((LanguageCon.com.Skip, snd (last ((P1, t) # xsa)))#ys))"      
         then show ?thesis 
         proof
           assume 
            a1:"fst (((P1, t) # xsa) ! length xsa) = LanguageCon.com.Throw \<and>
             snd (last ((P1, t) # xsa)) = Normal t' \<and>
             t = Normal t'' \<and>
             (\<exists>ys. (\<Gamma>, (P2, snd (((P1, t) # xsa) ! length xsa)) # ys) \<in> cptn_mod \<and>
                xs = map (lift_catch P2) xsa @
                       (P2, snd (((P1, t) # xsa) ! length xsa)) # ys)"
            then obtain ys where p2_exec:"(\<Gamma>, (P2, snd (((P1, t) # xsa) ! length xsa)) # ys) \<in> cptn_mod \<and>
                xs = map (lift_catch P2) xsa @
                       (P2, snd (((P1, t) # xsa) ! length xsa)) # ys" 
            by fastforce
            from a1 obtain t1 where t_normal: "t=Normal t1" 
              using env_normal_s'_normal_s by blast
            have f1:"fst (((P1, s)#(P1, t) # xsa) ! length ((P1, t)#xsa)) = LanguageCon.com.Throw"
              using a1 by fastforce
             from a1 have last_normal: "snd (last ((P1, s)#(P1, t) # xsa)) = Normal t'"
               by fastforce 
             then have p2_long_exec: "(\<Gamma>, (P2, snd (((P1, s)#(P1, t) # xsa) ! length ((P1, s)#xsa))) # ys) \<in> cptn_mod \<and>
                (P, t)#xs = map (lift_catch P2) ((P1, t) # xsa) @
                       (P2, snd (((P1, s)#(P1, t) # xsa) ! length ((P1, s)#xsa))) # ys" using p2_exec 
                by (simp add: lift_catch_def local.Catch)                  
             thus ?thesis using  a1 f1 last_normal all_step eq_P_Catch 
               by (clarify, metis (no_types) list.size(4) not_step_c_env  step_e)            
           next
           assume 
            as1:"fst (((P1, t) # xsa) ! length xsa) = LanguageCon.com.Skip \<and>
           (\<exists>ys. (\<Gamma>,(Skip,snd(last ((P1, t)#xsa)))#ys) \<in> cptn_mod \<and> 
            xs = map (lift_catch P2) xsa @
            ((LanguageCon.com.Skip, snd (last ((P1, t) # xsa)))#ys))"               
            then obtain ys where p1:"(\<Gamma>,(Skip,snd(last ((P1, t)#xsa)))#ys) \<in> cptn_mod \<and> 
                         (P, t)#xs = map (lift_catch P2) ((P1, t) # xsa) @
                          ((LanguageCon.com.Skip, snd (last ((P1, t) # xsa)))#ys)"
            proof -
              assume a1: "\<And>ys. (\<Gamma>, (LanguageCon.com.Skip, snd (last ((P1, t) # xsa))) # ys) \<in> cptn_mod \<and> (P, t) # xs = map (lift_catch P2) ((P1, t) # xsa) @ (LanguageCon.com.Skip, snd (last ((P1, t) # xsa))) # ys \<Longrightarrow> thesis"
              have "(LanguageCon.com.Catch P1 P2, t) # map (lift_catch P2) xsa = map (lift_catch P2) ((P1, t) # xsa)"
                by (simp add: lift_catch_def)
              thus ?thesis
                using a1 as1 eq_P_Catch by moura
            qed            
            from as1 have p2: "fst (((P1, s)#(P1, t) # xsa) ! length ((P1, t) #xsa)) = LanguageCon.com.Skip"
                 by fastforce                              
            thus ?thesis using p1 all_step eq_P_Catch by fastforce
          qed
      qed
    qed (auto)
qed(force+)


definition seq_cond 
where
"seq_cond zs Q xs P s s'' s' \<Gamma> \<equiv> (zs=(map (lift Q) xs) \<or>
             ((fst(((P, s)#xs)!length xs)=Skip \<and> 
               (\<exists>ys. (\<Gamma>,(Q, snd(((P, s)#xs)!length xs))#ys) \<in> cptn_mod \<and> 
                zs=(map (lift (Q)) xs)@((Q, snd(((P, s)#xs)!length xs))#ys)))) \<or>
             ((fst(((P, s)#xs)!length xs)=Throw \<and> 
                 snd(last ((P, s)#xs)) = Normal s' \<and>  s=Normal s''\<and>
                 (\<exists>ys.  (\<Gamma>,(Throw,Normal s')#ys) \<in> cptn_mod \<and>
                      zs=(map (lift Q) xs)@((Throw,Normal s')#ys)))))
"

lemma div_seq: assumes cptn_m:"(\<Gamma>,list) \<in> cptn_mod"
shows "(\<forall>s P Q zs. list=(Seq P Q, s)#zs \<longrightarrow>
       (\<exists>xs s' s''. 
          (\<Gamma>,(P, s)#xs) \<in> cptn_mod  \<and> 
             seq_cond zs Q xs P s s'' s' \<Gamma>))  
            "
unfolding seq_cond_def
using cptn_m
proof (induct rule: cptn_mod.induct)
  case (CptnModOne \<Gamma> P s)
  thus ?case using cptn_mod.CptnModOne by blast 
next
  case (CptnModSkip  \<Gamma> P s t xs) 
  from CptnModSkip.hyps
  have step: "\<Gamma>\<turnstile>\<^sub>c (P, toSeq s) \<rightarrow> (Skip, toSeq t)" by auto
  from CptnModSkip.hyps
  have noskip: "~(P=Skip)" using stepc_elim_cases(1) by blast  
  have x: "\<forall>c c1 c2. redex c = Seq c1 c2 \<Longrightarrow> False"
          using redex_not_Seq by blast
  from CptnModSkip.hyps
  have in_cptn_mod: "(\<Gamma>, (Skip, t) # xs) \<in> cptn_mod" by auto  
  then show ?case using CptnModSkip.hyps(2) SmallStepCon.redex_not_Seq by blast
next
  case (CptnModThrow  \<Gamma> P s t xs)
  from CptnModThrow.hyps
  have step: "\<Gamma>\<turnstile>\<^sub>c (P, toSeq s) \<rightarrow> (Throw, toSeq t)" by auto 
  moreover from CptnModThrow.hyps
  have in_cptn_mod: "(\<Gamma>, (Throw, t) # xs) \<in> cptn_mod" by auto 
  have no_seq: "\<forall>p1 p2. \<not>(P=Seq p1 p2)" using CptnModThrow.hyps(2) redex_not_Seq by auto
  ultimately show ?case by auto   
next 
  case (CptnModCondT \<Gamma> P0 s ys b P1)
  thus ?case by auto
next
  case (CptnModCondF \<Gamma> P0 s ys b P1)
  thus ?case by auto
next
  case (CptnModSeq1 \<Gamma> P0 s xs zs P1)
  thus ?case by blast
next 
  case (CptnModSeq2 \<Gamma> P0 s xs P1 ys zs) 
  from CptnModSeq2.hyps(3) last_length have last:"fst (((P0, s) # xs) ! length xs) = Skip" 
       by (simp add: last_length) 
  have P0cptn:"(\<Gamma>, (P0, s) # xs) \<in> cptn_mod" by fact
  from CptnModSeq2.hyps(4) have P1cptn:"(\<Gamma>, (P1, snd (((P0, s) # xs) ! length xs)) # ys) \<in> cptn_mod"
      by (simp add: last_length)          
  then have "zs = map (lift P1) xs @ (P1, snd (last ((P0, s) # xs))) # ys" by (simp add:CptnModSeq2.hyps)
  show ?case
  proof -{
    fix sa P Q zsa    
    assume eq:"(Seq P0 P1, s) # zs = (Seq P Q, sa) # zsa"
    then have "P0 =P \<and> P1 = Q \<and> s=sa \<and> zs=zsa" by auto 
     have "last ((P0, s) # xs) = ((P, sa) # xs) ! length xs"
            by (simp add: `P0 = P \<and> P1 = Q \<and> s = sa \<and> zs = zsa` last_length)
    then have "zsa = map (lift Q) xs @ (Q, snd (((P, sa) # xs) ! length xs)) # ys"
         using `P0 = P \<and> P1 = Q \<and> s = sa \<and> zs = zsa` `zs = map (lift P1) xs @ (P1, snd (last ((P0, s) # xs))) # ys` 
         by force    
    then have "(\<exists>xs s' s''. (\<Gamma>, (P, sa) # xs) \<in> cptn_mod \<and>
                        (zsa = map (lift Q) xs \<or>              
                         fst (((P, sa) # xs) ! length xs) = Skip \<and>
                             (\<exists>ys. (\<Gamma>, (Q, snd (((P, sa) # xs) ! length xs)) # ys) \<in> cptn_mod \<and>
                             zsa = map (lift Q) xs @ (Q, snd (((P, sa) # xs) ! length xs)) # ys) \<or>
                        ((fst(((P, sa)#xs)!length xs)=Throw \<and> 
                          snd(last ((P, sa)#xs)) = Normal s' \<and>  s=Normal s''\<and>
                         (\<exists>ys. (\<Gamma>,(Throw,Normal s')#ys) \<in> cptn_mod \<and>
                               zsa=(map (lift Q) xs)@((Throw,Normal s')#ys))))))
               " 
        using P0cptn P1cptn  `P0 = P \<and> P1 = Q \<and> s = sa \<and> zs = zsa` last 
        by blast                 
   }  
   thus ?case by auto qed     
next
  case (CptnModSeq3 \<Gamma> P0 s xs s' ys zs P1) 
  from CptnModSeq3.hyps(3) 
  have last:"fst (((P0, Normal s) # xs) ! length xs) = Throw" 
       by (simp add: last_length) 
  have P0cptn:"(\<Gamma>, (P0, Normal s) # xs) \<in> cptn_mod" by fact
  from CptnModSeq3.hyps(4) 
  have lastnormal:"snd (last ((P0, Normal s) # xs)) = Normal s'"
      by (simp add: last_length)          
  then have "zs = map (lift P1) xs @ ((Throw, Normal s')#ys)" by (simp add:CptnModSeq3.hyps)
  show ?case
  proof -{
    fix sa P Q zsa    
    assume eq:"(Seq P0 P1, Normal s) # zs = (Seq P Q, Normal sa) # zsa"
    then have "P0 =P \<and> P1 = Q \<and> Normal s=Normal sa \<and> zs=zsa" by auto
    then have "(P0, Normal s) = (P, Normal sa)" by auto 
    have "last ((P0, Normal s) # xs) = ((P, Normal sa) # xs) ! length xs"
                    by (simp add: `P0 = P \<and> P1 = Q \<and> Normal s = Normal sa \<and> zs = zsa` last_length)
    then have zsa:"zsa = (map (lift Q) xs)@((Throw,Normal s')#ys)"
                    using `P0 = P \<and> P1 = Q \<and> Normal s = Normal sa \<and> zs = zsa` `zs = map (lift P1) xs @ ((Throw, Normal s')#ys)` 
    by force
    then have a1:"(\<Gamma>,(Throw,Normal s')#ys) \<in> cptn_mod" using CptnModSeq3.hyps(5) by blast               
    then have "(\<exists>xs s'. (\<Gamma>, (P, Normal sa) # xs) \<in> cptn_mod \<and>
                        (zsa = map (lift Q) xs \<or>              
                         fst (((P,Normal sa) # xs) ! length xs) = Skip \<and>
                             (\<exists>ys. (\<Gamma>, (Q, snd (((P, Normal sa) # xs) ! length xs)) # ys) \<in> cptn_mod \<and>
                             zsa = map (lift Q) xs @ (Q, snd (((P, Normal sa) # xs) ! length xs)) # ys) \<or>
                        ((fst(((P, Normal sa)#xs)!length xs)=Throw \<and> 
                          snd(last ((P, Normal sa)#xs)) = Normal s' \<and>
                          (\<exists>ys. (\<Gamma>,(Throw,Normal s')#ys) \<in> cptn_mod \<and>
                          zsa=(map (lift Q) xs)@((Throw,Normal s')#ys))))))"
     using P0cptn zsa a1 last lastnormal
     by (metis \<open>(P0, Normal s) = (P, Normal sa)\<close>)
   }  
   thus ?thesis by fast qed  
next 
  case (CptnModEnv \<Gamma> P s t zs) 
  then have step:"(\<Gamma>, (P, t) # zs) \<in> cptn_mod" by auto
  have step_e: "\<Gamma>\<turnstile>\<^sub>c (P, s) \<rightarrow>\<^sub>e (P, t)" using CptnModEnv by auto  
  show ?case     
    proof (cases P)
      case (Seq P1 P2) 
      then have eq_P:"(P, t) # zs = (LanguageCon.com.Seq P1 P2, t) # zs" by auto      
      then  obtain xs t' t'' where 
         p1:"(\<Gamma>, (P1, t) # xs) \<in> cptn_mod" and p2:"
     (zs = map (lift P2) xs \<or>
      fst (((P1, t) # xs) ! length xs) = LanguageCon.com.Skip \<and>      
      (\<exists>ys. (\<Gamma>, (P2, snd (((P1, t) # xs) ! length xs)) # ys) \<in> cptn_mod \<and>
            zs =
            map (lift P2) xs @
            (P2, snd (((P1, t) # xs) ! length xs)) # ys) \<or>
      fst (((P1, t) # xs) ! length xs) = LanguageCon.com.Throw \<and>
      snd (last ((P1, t) # xs)) = Normal t' \<and>
      t = Normal t'' \<and> (\<exists>ys. (\<Gamma>,(Throw,Normal t')#ys) \<in> cptn_mod \<and> 
      zs =
      map (lift P2) xs @
      ((LanguageCon.com.Throw, Normal t')#ys))) " 
        using CptnModEnv(3) by auto
      have all_step:"(\<Gamma>, (P1, s)#((P1, t) # xs)) \<in> cptn_mod"
        using cptn_mod.CptnModEnv env_intro p1 step_e by blast         
      show ?thesis using p2 
      proof  
        assume "zs = map (lift P2) xs"
        have "(P, t) # zs = map (lift P2) ((P1, t) # xs)"
          by (simp add: `zs = map (lift P2) xs` lift_def local.Seq)
        thus ?thesis using all_step eq_P by fastforce
      next 
        assume 
         "fst (((P1, t) # xs) ! length xs) = LanguageCon.com.Skip \<and>      
         (\<exists>ys. (\<Gamma>, (P2, snd (((P1, t) # xs) ! length xs)) # ys) \<in> cptn_mod \<and>
            zs = map (lift P2) xs @ (P2, snd (((P1, t) # xs) ! length xs)) # ys) \<or>
          fst (((P1, t) # xs) ! length xs) = LanguageCon.com.Throw \<and>
           snd (last ((P1, t) # xs)) = Normal t' \<and>
           t = Normal t'' \<and> (\<exists>ys. (\<Gamma>,(Throw,Normal t')#ys) \<in> cptn_mod \<and> 
           zs = map (lift P2) xs @ ((LanguageCon.com.Throw, Normal t')#ys))"
         then show ?thesis 
         proof
           assume 
            a1:"fst (((P1, t) # xs) ! length xs) = LanguageCon.com.Skip \<and>      
               (\<exists>ys. (\<Gamma>, (P2, snd (((P1, t) # xs) ! length xs)) # ys) \<in> cptn_mod \<and>
               zs = map (lift P2) xs @ (P2, snd (((P1, t) # xs) ! length xs)) # ys)"
               from a1 obtain ys where 
                   p2_exec:"(\<Gamma>, (P2, snd (((P1, t) # xs) ! length xs)) # ys) \<in> cptn_mod \<and>
                       zs = map (lift P2) xs @
                       (P2, snd (((P1, t) # xs) ! length xs)) # ys" 
                by auto 
               have f1:"fst (((P1, s)#(P1, t) # xs) ! length ((P1, t)#xs)) = LanguageCon.com.Skip"
                 using a1 by fastforce             
               then have p2_long_exec: 
                 "(\<Gamma>, (P2, snd (((P1, s)#(P1, t) # xs) ! length ((P1, t)#xs))) # ys) \<in> cptn_mod \<and>
                  (P, t)#zs = map (lift P2) ((P1, t) # xs) @
                       (P2, snd (((P1, s)#(P1, t) # xs) ! length ((P1, t)#xs))) # ys" 
             using p2_exec by (simp add: lift_def local.Seq)     
             thus ?thesis using a1 f1 all_step eq_P by blast            
           next
           assume 
            a1:"fst (((P1, t) # xs) ! length xs) = LanguageCon.com.Throw \<and>
            snd (last ((P1, t) # xs)) = Normal t' \<and> t = Normal t'' \<and> 
          (\<exists>ys. (\<Gamma>,(Throw,Normal t')#ys) \<in> cptn_mod \<and> 
           zs = map (lift P2) xs @ ((LanguageCon.com.Throw, Normal t')#ys))"             
             then have last_throw:
               "fst (((P1, s)#(P1, t) # xs) ! length ((P1, t) #xs)) = LanguageCon.com.Throw" 
               by fastforce
             from a1 have last_normal: "snd (last ((P1, s)#(P1, t) # xs)) = Normal t'"
               by fastforce
             have seq_lift:
               "(LanguageCon.com.Seq P1 P2, t) # map (lift P2) xs = map (lift P2) ((P1, t) # xs)"
                by (simp add: a1 lift_def)             
            thus  ?thesis using a1 last_throw last_normal all_step eq_P         
              by (clarify, metis (no_types, lifting) append_Cons env_normal_s'_normal_s  step_e)                 
          qed
      qed
    qed (auto) 
qed (force)+



lemma cptn_onlyif_cptn_mod_aux:
  assumes vars:"v = toSeq s" and vars1:"w = toSeq t" and stepseq:"\<Gamma>\<turnstile>\<^sub>c (P,v) \<rightarrow> (Q,w)" and
          normal_eq_l:"\<forall>ns ns'.                                             
                  (s = Normal ns \<or> s = Abrupt ns) \<and> 
                  (t = Normal ns' \<or> t = Abrupt ns') \<longrightarrow> snd ns = snd ns'" and
        stepmod:"(\<Gamma>,(Q,t)#xs) \<in> cptn_mod"
shows "(\<Gamma>,(P,s)#(Q,t)#xs) \<in> cptn_mod"
using  stepseq normal_eq_l stepmod vars vars1
proof (induct arbitrary: xs)
  case (Basicc f e s1)     
  thus ?case  using stepc.Basicc[of \<Gamma> f e s1]  
    by (simp add: cptn_mod.CptnModSkip)    
next
  case (Specc s1 t1 r)
  thus ?case using stepc.Specc[of s1 t1 r \<Gamma>] by (simp add: cptn_mod.CptnModSkip)
next
  case (SpecStuckc s1 r)
  thus ?case using stepc.SpecStuckc[of s1 _ \<Gamma>] by (simp add: cptn_mod.CptnModSkip)    
next
  case (Guardc s1 g f c)
  thus ?case
    by (metis (mono_tags, lifting) cptn_mod.CptnModGuard prod_eq_iff toSeq.simps(1) toSeq_not_Normal xstate.inject(1))
next
  case (GuardFaultc)
  thus ?case
    by (metis SmallStepCon.redex.simps(9) cptn_mod.CptnModSkip stepc.GuardFaultc) 
next
  case (Seqc c1 s1 c1' t1 c2)
  have step: "\<Gamma>\<turnstile>\<^sub>c (c1, s1) \<rightarrow> (c1', t1)" by (simp add: Seqc.hyps(1))
  then have nsc1: "c1\<noteq>Skip" using stepc_elim_cases(1) by blast 
  have assum: "(\<Gamma>, (Seq c1' c2, t) # xs) \<in> cptn_mod" using Seqc.prems by blast
  have divseq:"(\<forall>s P Q zs. (Seq c1' c2, t) # xs=(Seq P Q, s)#zs \<longrightarrow>
                (\<exists>xs sv' sv''. ((\<Gamma>,(P, s)#xs) \<in> cptn_mod  \<and> 
                           (zs=(map (lift Q) xs) \<or>
                           ((fst(((P, s)#xs)!length xs)=Skip \<and> 
                             (\<exists>ys. (\<Gamma>,(Q, snd(((P, s)#xs)!length xs))#ys) \<in> cptn_mod \<and> 
                              zs=(map (lift (Q)) xs)@((Q, snd(((P, s)#xs)!length xs))#ys)))) \<or>
                           ((fst(((P, s)#xs)!length xs)=Throw \<and> 
                               snd(last ((P, s)#xs)) = Normal sv' \<and>  t=Normal sv''\<and>
                             (\<exists>ys.  (\<Gamma>,(Throw,Normal sv')#ys) \<in> cptn_mod \<and>
                              zs=(map (lift Q) xs)@((Throw,Normal sv')#ys))
                               ))))
                            
                 ))"  using div_seq [OF assum] unfolding seq_cond_def by auto
   {fix sa P Q zsa
       assume ass:"(Seq c1' c2, t) # xs = (Seq P Q, sa) # zsa"
       then have eqs:"c1' = P \<and> c2 = Q \<and> t = sa \<and> xs = zsa" by auto
       then have "(\<exists>xs sv' sv''. (\<Gamma>, (P, sa) # xs) \<in> cptn_mod \<and>
                        (zsa = map (lift Q) xs \<or>              
                         fst (((P, sa) # xs) ! length xs) = Skip \<and>
                             (\<exists>ys. (\<Gamma>, (Q, snd (((P, sa) # xs) ! length xs)) # ys) \<in> cptn_mod \<and>
                             zsa = map (lift Q) xs @ (Q, snd (((P, sa) # xs) ! length xs)) # ys) \<or>
                        ((fst(((P, sa)#xs)!length xs)=Throw \<and> 
                          snd(last ((P, sa)#xs)) = Normal sv' \<and>  t=Normal sv''\<and>
                          (\<exists>ys.  (\<Gamma>,(Throw,Normal sv')#ys) \<in> cptn_mod \<and>
                              zsa=(map (lift Q) xs)@((Throw,Normal sv')#ys))))))" 
             using ass divseq   by blast
    } note conc=this [of c1' c2 t xs]    
     then obtain xs' sa' sa''
       where  split:"(\<Gamma>, (c1', t) # xs') \<in> cptn_mod \<and>
                     (xs = map (lift c2) xs' \<or>                   
                     fst (((c1', t) # xs') ! length xs') = Skip \<and>
                        (\<exists>ys. (\<Gamma>, (c2, snd (((c1', t) # xs') ! length xs')) # ys) \<in> cptn_mod \<and>
                         xs = map (lift c2) xs' @ (c2, snd (((c1', t) # xs') ! length xs')) # ys) \<or>
                     ((fst(((c1', t)#xs')!length xs')=Throw \<and> 
                         snd(last ((c1', t)#xs')) = Normal sa' \<and> t=Normal sa''\<and>
                         (\<exists>ys.  (\<Gamma>,(Throw,Normal sa')#ys) \<in> cptn_mod \<and>
                              xs=(map (lift c2) xs')@((Throw,Normal sa')#ys))
                         )))"  by blast
  then have "(xs = map (lift c2) xs' \<or>                   
                     fst (((c1', t) # xs') ! length xs') = Skip \<and>
                        (\<exists>ys. (\<Gamma>, (c2, snd (((c1', t) # xs') ! length xs')) # ys) \<in> cptn_mod \<and>
                         xs = map (lift c2) xs' @ (c2, snd (((c1', t) # xs') ! length xs')) # ys) \<or>
                     ((fst(((c1', t)#xs')!length xs')=Throw \<and> 
                         snd(last ((c1',t)#xs')) = Normal sa' \<and> t=Normal sa''\<and>
                         (\<exists>ys.  (\<Gamma>,(Throw,Normal sa')#ys) \<in> cptn_mod \<and>
                              xs=(map (lift c2) xs')@((Throw,Normal sa')#ys)))))" by auto
  thus ?case 
  proof{           
       assume c1'nonf:"xs = map (lift c2) xs'"
       then have c1'cptn:"(\<Gamma>, (c1', t) # xs') \<in> cptn_mod" using split by blast
       then have induct_step: "(\<Gamma>, (c1, s) # (c1', t)#xs') \<in> cptn_mod"
         using Seqc.hyps(2)
         using Seqc.prems(3) Seqc.prems(4) normal_eq_l by blast  
       then have "(Seq c1' c2, t)#xs = map (lift c2) ((c1', t)#xs')"
            using c1'nonf
            by (simp add: CptnModSeq1 lift_def)
       thus ?thesis 
            using c1'nonf c1'cptn induct_step by (auto simp add: CptnModSeq1)
    next
      assume "fst (((c1', t) # xs') ! length xs') = Skip \<and>
              (\<exists>ys. (\<Gamma>, (c2, snd (((c1', t) # xs') ! length xs')) # ys) \<in> cptn_mod \<and>
                  xs = map (lift c2) xs' @ (c2, snd (((c1', t) # xs') ! length xs')) # ys) \<or>
             ((fst(((c1', t)#xs')!length xs')=Throw \<and> 
                snd(last ((c1', t)#xs')) = Normal sa' \<and>  t=Normal sa''\<and>
                (\<exists>ys.  (\<Gamma>,(Throw,Normal sa')#ys) \<in> cptn_mod \<and>
                              xs=(map (lift c2) xs')@((Throw,Normal sa')#ys))))"  
      thus ?thesis
      proof
         assume assth:"fst (((c1', t) # xs') ! length xs') = Skip \<and>
              (\<exists>ys. (\<Gamma>, (c2, snd (((c1', t) # xs') ! length xs')) # ys) \<in> cptn_mod \<and>
                  xs = map (lift c2) xs' @ (c2, snd (((c1', t) # xs') ! length xs')) # ys)"
         then obtain ys 
             where split':"(\<Gamma>, (c2, snd (((c1', t) # xs') ! length xs')) # ys) \<in> cptn_mod \<and>
                  xs = map (lift c2) xs' @ (c2, snd (((c1', t) # xs') ! length xs')) # ys"
             by auto    
         then have c1'cptn:"(\<Gamma>, (c1', t) # xs') \<in> cptn_mod" using split by blast
         then have induct_step: "(\<Gamma>, (c1, s) # (c1', t)#xs') \<in> cptn_mod"
         using Seqc.hyps(2)
         using Seqc.prems(3) Seqc.prems(4) normal_eq_l by blast                  
         then have seqmap:"(Seq c1 c2, s)#(Seq c1' c2, t)#xs = map (lift c2) ((c1,s)#(c1', t)#xs') @ (c2, snd (((c1', t) # xs') ! length xs')) # ys"
        using split'   
         by (simp add: CptnModSeq2 lift_def) 
        then have lastc1:"last ((c1, s) # (c1', t) # xs') = ((c1', t) # xs') ! length xs'"
          by (simp add: last_length) 
        then have lastc1skip:"fst (last ((c1, s) # (c1', t) # xs')) = Skip" 
          using assth by fastforce          
        thus ?thesis 
           using seqmap split' last_length cptn_mod.CptnModSeq2 
                 induct_step lastc1 lastc1skip 
           by fastforce
    next
        assume assm:"((fst(((c1', t)#xs')!length xs')=Throw \<and> 
                snd(last ((c1', t)#xs')) = Normal sa' \<and> t=Normal sa''\<and>
                (\<exists>ys.  (\<Gamma>,(Throw,Normal sa')#ys) \<in> cptn_mod \<and>
                 xs=(map (lift c2) xs')@((Throw,Normal sa')#ys))))"
        then have s'eqsa'': "t=Normal sa''" by auto
        then have snormal: "\<exists>ns. s=Normal ns"
          using Seqc.hyps(1) Seqc.prems(3) Seqc.prems(4) c_step normal_eq_l step_ce_notNormal by blast
        then have c1'cptn:"(\<Gamma>, (c1', t) # xs') \<in> cptn_mod" using split by blast        
        then have induct_step: "(\<Gamma>, (c1, s) # (c1', t)#xs') \<in> cptn_mod"
        using Seqc.hyps(2)
        using Seqc.prems(3) Seqc.prems(4) normal_eq_l by blast  
        then obtain ys where seqmap:"(Seq c1' c2, t)#xs = (map (lift c2) ((c1', t)#xs'))@((Throw,Normal sa')#ys)"
        using assm
        proof -
          assume a1: "\<And>ys. (LanguageCon.com.Seq c1' c2, t) # xs = map (lift c2) ((c1', t) # xs') @ (LanguageCon.com.Throw, Normal sa') # ys \<Longrightarrow> thesis"
          have "(LanguageCon.com.Seq c1' c2, Normal sa'') # map (lift c2) xs' = map (lift c2) ((c1', t) # xs')"
            by (simp add: assm lift_def)
          thus ?thesis
            using a1 assm by moura
        qed  
        then have lastc1:"last ((c1, s) # (c1', t) # xs') = ((c1', t) # xs') ! length xs'"
                   by (simp add: last_length) 
        then have lastc1skip:"fst (last ((c1, s) # (c1', t) # xs')) = Throw" 
             using assm by fastforce
        then have "snd (last ((c1, s) # (c1', t) # xs')) = Normal sa'"
             using assm by force        
        thus ?thesis
            using assm c1'cptn induct_step lastc1skip snormal seqmap s'eqsa'' 
            by (auto simp add:cptn_mod.CptnModSeq3)
   qed
  }qed    
          
next
  case (SeqSkipc c2 s1 xs)
  then have c2incptn:"(\<Gamma>, (c2, s) # xs) \<in> cptn_mod"
    using eq_toSeq by blast
  moreover have 1:"(\<Gamma>, [(Skip, s)]) \<in> cptn_mod" by (simp add: cptn_mod.CptnModOne)
  moreover have 2:"fst(last ([(Skip, s)])) = Skip" by fastforce
  moreover have 3:"(\<Gamma>,(c2, snd(last [(Skip, s)]))#xs) \<in> cptn_mod" 
    using c2incptn by auto  
  moreover have "(c2,s)#xs=(map (lift c2) [])@(c2, snd(last [(Skip, s)]))#xs"
    by (auto simp add:lift_def)
  moreover have "s=t" using eq_toSeq SeqSkipc by blast
  ultimately show ?case        
    by (simp add:  CptnModSeq2)
next
  case (SeqThrowc c2 s1 xs)  
  have eq_st:"s=t" using eq_toSeq[OF SeqThrowc(1)] SeqThrowc by auto
  obtain ns where normals:"s=Normal ns" using SeqThrowc
    by (metis toSeq_not_Normal)
  have "(\<Gamma>, [(Throw, Normal ns)]) \<in> cptn_mod" by (simp add: cptn_mod.CptnModOne) 
  then obtain ys where ys_nil:"ys=[]" and last:"(\<Gamma>, (Throw, s)#ys)\<in> cptn_mod" 
   using normals by auto
  moreover have "fst (last ((Throw, Normal ns)#ys)) = Throw" using ys_nil last by auto
  moreover have "snd (last ((Throw, Normal ns)#ys)) = Normal ns" using ys_nil last by auto
  moreover from ys_nil have "(map (lift c2) ys) = []" by auto  
  ultimately show ?case using SeqThrowc.prems cptn_mod.CptnModSeq3 eq_st normals
    by blast
next
  case (CondTruec s1 b c1 c2)
  moreover obtain ns where normals:"s=Normal ns"
    by (metis (no_types) calculation(4) toSeq_not_Normal)
  moreover have "s=t"
    using calculation(4,5) eq_toSeq[OF calculation(2)]  by auto
  ultimately show ?case by (simp add: cptn_mod.CptnModCondT)
next
  case (CondFalsec s1 b c1 c2)
  moreover obtain ns where normals:"s=Normal ns"
    by (metis (no_types) calculation(4) toSeq_not_Normal)
  moreover have "s=t"
    using calculation(4,5) eq_toSeq[OF calculation(2)]  by auto
  ultimately show ?case
     by (simp add: cptn_mod.CptnModCondF)
next
  case (WhileTruec s1 b c)
  have sinb: "s1\<in>b" by fact
  obtain ns where normals:"s=Normal ns"
    by (metis (no_types) WhileTruec(4) toSeq_not_Normal)
  have eq_st:"s=t" using eq_toSeq[OF WhileTruec(2)] WhileTruec by auto
  have SeqcWhile: "(\<Gamma>, (Seq c (While b c), Normal ns) # xs) \<in> cptn_mod" 
    using sinb normals eq_st WhileTruec by blast  
  have divseq:"(\<forall>s P Q zs. (Seq c (While b c), Normal ns) # xs=(Seq P Q, s)#zs \<longrightarrow>
                (\<exists>xs s'. ((\<Gamma>,(P, s)#xs) \<in> cptn_mod  \<and> 
                           (zs=(map (lift Q) xs) \<or>
                           ((fst(((P, s)#xs)!length xs)=Skip \<and> 
                             (\<exists>ys. (\<Gamma>,(Q, snd(((P, s)#xs)!length xs))#ys) \<in> cptn_mod \<and> 
                              zs=(map (lift (Q)) xs)@((Q, snd(((P, s)#xs)!length xs))#ys)))) \<or>
                           ((fst(((P, s)#xs)!length xs)=Throw \<and> 
                               snd(last ((P, s)#xs)) = Normal s' \<and>
                              (\<exists>ys.  (\<Gamma>,(Throw,Normal s')#ys) \<in> cptn_mod \<and>
                      zs=(map (lift Q) xs)@((Throw,Normal s')#ys))))))                            
                 ))" using div_seq [OF SeqcWhile] eq_st normals unfolding seq_cond_def by fast
{fix sa P Q zsa
       assume ass:"(Seq c (While b c), Normal ns) # xs = (Seq P Q, sa) # zsa"
       then have eqs:"c = P \<and> (While b c) = Q \<and> Normal ns = sa \<and> xs = zsa" by auto
       then have "(\<exists>xs s'. (\<Gamma>, (P, sa) # xs) \<in> cptn_mod \<and>
                        (zsa = map (lift Q) xs \<or>              
                         fst (((P, sa) # xs) ! length xs) = Skip \<and>
                             (\<exists>ys. (\<Gamma>, (Q, snd (((P, sa) # xs) ! length xs)) # ys) \<in> cptn_mod \<and>
                             zsa = map (lift Q) xs @ (Q, snd (((P, sa) # xs) ! length xs)) # ys) \<or>
                        ((fst(((P, sa)#xs)!length xs)=Throw \<and> 
                          snd(last ((P, sa)#xs)) = Normal s' \<and>
                          (\<exists>ys.  (\<Gamma>,(Throw,Normal s')#ys) \<in> cptn_mod \<and>
                      zsa=(map (lift Q) xs)@((Throw,Normal s')#ys))
                        ))))" 
             using ass divseq by auto
    } note conc=this [of c "While b c" "Normal ns" xs] 
   then obtain xs' s' 
        where  split:"(\<Gamma>, (c, Normal ns) # xs') \<in> cptn_mod \<and>
     (xs = map (lift (While b c)) xs' \<or>
      fst (((c, Normal ns) # xs') ! length xs') = Skip \<and>
      (\<exists>ys. (\<Gamma>, (While b c, snd (((c, Normal ns) # xs') ! length xs')) # ys)
            \<in> cptn_mod \<and>
            xs =
            map (lift (While b c)) xs' @
            (While b c, snd (((c, Normal ns) # xs') ! length xs')) # ys) \<or>
      fst (((c, Normal ns) # xs') ! length xs') = Throw \<and>
      snd (last ((c, Normal ns) # xs')) = Normal s' \<and> 
      (\<exists>ys.  (\<Gamma>, ((Throw, Normal s')#ys)) \<in> cptn_mod \<and>
      xs = map (lift (While b c)) xs' @ ((Throw, Normal s')#ys)))"  by blast 
   then have "(xs = map (lift (While b c)) xs' \<or>
            fst (((c, Normal ns) # xs') ! length xs') = Skip \<and>
            (\<exists>ys. (\<Gamma>, (While b c, snd (((c, Normal ns) # xs') ! length xs')) # ys)
                  \<in> cptn_mod \<and>
                  xs =
                  map (lift (While b c)) xs' @
                  (While b c, snd (((c, Normal ns) # xs') ! length xs')) # ys) \<or>
            fst (((c, Normal ns) # xs') ! length xs') = Throw \<and>
            snd (last ((c, Normal ns) # xs')) = Normal s' \<and>
            (\<exists>ys.  (\<Gamma>, ((Throw, Normal s')#ys)) \<in> cptn_mod \<and>
          xs = map (lift (While b c)) xs' @ ((Throw, Normal s')#ys)))" ..
 thus ?case
 proof{ 
   assume 1:"xs = map (lift (While b c)) xs'"  
   have 3:"(\<Gamma>, (c, Normal ns) # xs') \<in> cptn_mod" using split by auto   
   then show ?thesis using "1" cptn_mod.CptnModWhile1 sinb normals eq_st
     by (metis WhileTruec.prems(3) toSeq.simps(1) xstate.inject(1)) 
 next
   assume "fst (((c, Normal ns) # xs') ! length xs') = Skip \<and>
          (\<exists>ys. (\<Gamma>, (While b c, snd (((c, Normal ns) # xs') ! length xs')) # ys)
                \<in> cptn_mod \<and>
                xs =
                map (lift (While b c)) xs' @
                (While b c, snd (((c, Normal ns) # xs') ! length xs')) # ys) \<or>
          fst (((c, Normal ns) # xs') ! length xs') = Throw \<and>
          snd (last ((c, Normal ns) # xs')) = Normal s' \<and>
          (\<exists>ys.  (\<Gamma>, ((Throw, Normal s')#ys)) \<in> cptn_mod \<and>
          xs = map (lift (While b c)) xs' @ ((Throw, Normal s')#ys))"
   thus ?case
   proof
     assume asm:"fst (((c, Normal ns) # xs') ! length xs') = Skip \<and>
             (\<exists>ys. (\<Gamma>, (While b c, snd (((c, Normal ns) # xs') ! length xs')) # ys)
             \<in> cptn_mod \<and>
             xs =
             map (lift (While b c)) xs' @
             (While b c, snd (((c, Normal ns) # xs') ! length xs')) # ys)"
     then obtain ys 
       where asm':"(\<Gamma>, (While b c, snd (last ((c, Normal ns) # xs'))) # ys)
                   \<in> cptn_mod 
                   \<and> xs = map (lift (While b c)) xs' @
                       (While b c, snd (last ((c, Normal ns) # xs'))) # ys" 
              by (auto simp add: last_length)
     moreover have 3:"(\<Gamma>, (c, Normal ns) # xs') \<in> cptn_mod" using split by auto
     moreover from asm have "fst (last ((c, Normal ns) # xs'))  = Skip"
       by (simp add: last_length)        
     ultimately show ?case using sinb normals eq_st WhileTruec.prems(3)
       by (auto simp add: CptnModWhile2)
   next
    assume asm:" fst (((c, Normal ns) # xs') ! length xs') = Throw \<and>
          snd (last ((c, Normal ns) # xs')) = Normal s' \<and>
          (\<exists>ys.  (\<Gamma>, ((Throw, Normal s')#ys)) \<in> cptn_mod \<and>
          xs = map (lift (While b c)) xs' @ ((Throw, Normal s')#ys))"   
     moreover have 3:"(\<Gamma>, (c, Normal ns) # xs') \<in> cptn_mod" using split by auto
     moreover from asm have "fst (last ((c, Normal ns) # xs'))  = Throw"
          by (simp add: last_length) 
     ultimately show ?case using sinb normals eq_st WhileTruec.prems(3) 
       by (auto simp add:CptnModWhile3)
   qed
 }qed  
next
  case (WhileFalsec s1 b c)
  thus ?case  using stepc.WhileFalsec[of s1 b \<Gamma> c]  
    by (simp add: cptn_mod.CptnModSkip) 
next
  case (Awaitc s1 b \<Gamma>a c t1)
  thus ?case using stepc.Awaitc[of s1 b \<Gamma>a \<Gamma>]
    by (simp add: cptn_mod.CptnModSkip)
next
  case (AwaitAbruptc s1 b \<Gamma>a c t1 ta)
  thus ?case using stepc.AwaitAbruptc[of s1 b \<Gamma>a \<Gamma> c t1 ta] by (simp add: cptn_mod.CptnModThrow) 
next
  case (Callc p bdy s1)
  moreover have eq_st:"s=t" using eq_toSeq[OF Callc(3)] Callc by auto
  moreover obtain ns where normals:"s=Normal ns"
    by (metis (no_types) Callc(5) toSeq_not_Normal)
  ultimately show ?case using cptn_mod.CptnModCall by fast 
next
  case (CallUndefinedc p s1)  
  thus ?case using stepc.CallUndefinedc[of \<Gamma> p s1,OF CallUndefinedc(1)]
    by (simp add: cptn_mod.CptnModSkip)
next
  case (DynComc c s1)
  moreover obtain ns where "s=Normal ns"
    by (metis (full_types) DynComc.prems(3) toSeq_not_Normal) 
  moreover have "fst ns = s1"
    using calculation(3) calculation(5) by auto
  moreover have "s=t"
    using  calculation(3,4) eq_toSeq[OF DynComc(1)] by force 
  ultimately show ?case using  cptn_mod.CptnModDynCom
    by blast 
next
  case (Catchc c1 s1 c1' t1 c2)
   have step: "\<Gamma>\<turnstile>\<^sub>c (c1, s1) \<rightarrow> (c1', t1)" by (simp add: Catchc.hyps(1))
  then have nsc1: "c1\<noteq>Skip" using stepc_elim_cases(1) by blast 
  have assum: "(\<Gamma>, (Catch c1' c2, t) # xs) \<in> cptn_mod" 
    using Catchc.prems by blast
  have divcatch:"(\<forall>s P Q zs. (Catch c1' c2, t) # xs=(Catch P Q, s)#zs \<longrightarrow>
  (\<exists>xs s' s''. ((\<Gamma>,(P, s)#xs) \<in> cptn_mod  \<and> 
             (zs=(map (lift_catch Q) xs) \<or>
             ((fst(((P, s)#xs)!length xs)=Throw \<and>
               snd(last ((P, s)#xs)) = Normal s' \<and>  s=Normal s''\<and>
               (\<exists>ys. (\<Gamma>,(Q, snd(((P, s)#xs)!length xs))#ys) \<in> cptn_mod \<and> 
                zs=(map (lift_catch Q) xs)@((Q, snd(((P, s)#xs)!length xs))#ys)))) \<or>
                ((fst(((P, s)#xs)!length xs)=Skip \<and>  
                  (\<exists>ys. (\<Gamma>,(Skip,snd(last ((P, s)#xs)))#ys) \<in> cptn_mod \<and>                   
                 zs=(map (lift_catch Q) xs)@((Skip,snd(last ((P, s)#xs)))#ys))                
                 ))))
   ))" using div_catch [OF assum] by (auto simp add: catch_cond_def)
   {fix sa P Q zsa
       assume ass:"(Catch c1' c2, t) # xs = (Catch P Q, sa) # zsa"
       then have eqs:"c1' = P \<and> c2 = Q \<and> t = sa \<and> xs = zsa" by auto
       then have "(\<exists>xs sv' sv''. ((\<Gamma>,(P, sa)#xs) \<in> cptn_mod  \<and> 
             (zsa=(map (lift_catch Q) xs) \<or>
             ((fst(((P, sa)#xs)!length xs)=Throw \<and>
               snd(last ((P, sa)#xs)) = Normal sv' \<and>  t=Normal sv''\<and>
               (\<exists>ys. (\<Gamma>,(Q, snd(((P, sa)#xs)!length xs))#ys) \<in> cptn_mod \<and> 
                zsa=(map (lift_catch Q) xs)@((Q, snd(((P, sa)#xs)!length xs))#ys)))) \<or>
                ((fst(((P, sa)#xs)!length xs)=Skip \<and>                  
                 (\<exists>ys. (\<Gamma>,(Skip,snd(last ((P, sa)#xs)))#ys) \<in> cptn_mod \<and>                   
                 zsa=(map (lift_catch Q) xs)@((Skip,snd(last ((P, sa)#xs)))#ys))))))
   )"   using ass divcatch by blast
    } note conc=this [of c1' c2 t xs]    
     then obtain xs' sa' sa''
       where split:
         "(\<Gamma>, (c1', t) # xs') \<in> cptn_mod \<and> 
          (xs = map (lift_catch c2) xs' \<or>
          fst (((c1', t) # xs') ! length xs') = Throw \<and>
          snd (last ((c1', t) # xs')) = Normal sa' \<and> t = Normal sa'' \<and>
          (\<exists>ys. (\<Gamma>, (c2, snd (((c1', t) # xs') ! length xs')) # ys) \<in> cptn_mod \<and>
                xs = map (lift_catch c2) xs' @
                (c2, snd (((c1', t) # xs') ! length xs')) # ys) \<or>
          fst (((c1', t) # xs') ! length xs') = Skip \<and>
          (\<exists>ys. (\<Gamma>,(Skip,snd(last ((c1', t)#xs')))#ys) \<in> cptn_mod \<and>                   
                 xs=(map (lift_catch c2) xs')@((Skip,snd(last ((c1', t)#xs')))#ys)))"          
        by blast
  then have "(xs = map (lift_catch c2) xs' \<or>
          fst (((c1', t) # xs') ! length xs') = Throw \<and>
          snd (last ((c1', t) # xs')) = Normal sa' \<and> t = Normal sa'' \<and>
          (\<exists>ys. (\<Gamma>, (c2, snd (((c1', t) # xs') ! length xs')) # ys) \<in> cptn_mod \<and>
                xs = map (lift_catch c2) xs' @
                (c2, snd (((c1', t) # xs') ! length xs')) # ys) \<or>
          fst (((c1', t) # xs') ! length xs') = Skip \<and>
          (\<exists>ys. (\<Gamma>,(Skip,snd(last ((c1', t)#xs')))#ys) \<in> cptn_mod \<and>                   
                 xs=(map (lift_catch c2) xs')@((Skip,snd(last ((c1', t)#xs')))#ys)))"          
        by auto
  thus ?case   
  proof{
    assume c1'nonf:"xs = map (lift_catch c2) xs'"       
    then have c1'cptn:"(\<Gamma>, (c1', t) # xs') \<in> cptn_mod" using split by blast
    then have induct_step: "(\<Gamma>, (c1, s) # (c1', t)#xs') \<in> cptn_mod"
      using Catchc.hyps(2)  Catchc.prems(3) Catchc.prems(4) normal_eq_l by blast
    then have "(Catch c1' c2, t)#xs = map (lift_catch c2) ((c1', t)#xs')"
      using c1'nonf
      by (simp add: CptnModCatch1 lift_catch_def)
    thus ?thesis 
      using c1'nonf c1'cptn induct_step by (auto simp add: CptnModCatch1)
  next
    assume "fst (((c1', t) # xs') ! length xs') = Throw \<and>
          snd (last ((c1', t) # xs')) = Normal sa' \<and> t = Normal sa'' \<and>
          (\<exists>ys. (\<Gamma>, (c2, snd (((c1', t) # xs') ! length xs')) # ys) \<in> cptn_mod \<and>
          xs =map (lift_catch c2) xs' @ (c2, snd (((c1', t) # xs') ! length xs')) # ys) \<or>
         fst (((c1', t) # xs') ! length xs') = Skip \<and>
          (\<exists>ys. (\<Gamma>,(Skip,snd(last ((c1', t)#xs')))#ys) \<in> cptn_mod \<and>                   
           xs=(map (lift_catch c2) xs')@((Skip,snd(last ((c1', t)#xs')))#ys))"  
    thus ?thesis
    proof
      assume assth:
       "fst (((c1', t) # xs') ! length xs') = Throw \<and>
        snd (last ((c1', t) # xs')) = Normal sa' \<and> t = Normal sa'' \<and>
        (\<exists>ys. (\<Gamma>, (c2, snd (((c1', t) # xs') ! length xs')) # ys) \<in> cptn_mod \<and>
        xs =map (lift_catch c2) xs' @ (c2, snd (((c1', t) # xs') ! length xs')) # ys)"     
      then have s'eqsa'': "t=Normal sa''" by auto
      then have snormal: "\<exists>ns. s=Normal ns"
        by (metis step_not_normal_s_eq_t stepseq toSeq_not_Normal vars vars1)
      then obtain ys 
        where split':"(\<Gamma>, (c2, snd (((c1', t) # xs') ! length xs')) # ys) \<in> cptn_mod \<and>
                xs =map (lift_catch c2) xs' @ (c2, snd (((c1', t) # xs') ! length xs')) # ys"
        using assth by auto    
      then have c1'cptn:"(\<Gamma>, (c1',t) # xs') \<in> cptn_mod" 
        using split by blast
      then have induct_step: "(\<Gamma>, (c1, s) # (c1', t)#xs') \<in> cptn_mod"
        using Catchc.hyps(2) Catchc.prems(3) Catchc.prems(4) normal_eq_l by blast
      then have seqmap:"(Catch c1 c2, s)#(Catch c1' c2, t)#xs = 
                             map (lift_catch c2) ((c1,s)#(c1', t)#xs') @ 
                                (c2, snd (((c1', t) # xs') ! length xs')) # ys"
        using split' by (simp add: CptnModCatch3 lift_catch_def) 
      then have lastc1:"last ((c1, s) # (c1', t) # xs') = ((c1', t) # xs') ! length xs'"
        by (simp add: last_length) 
      then have lastc1skip:"fst (last ((c1, s) # (c1', t) # xs')) = Throw" 
        using assth by fastforce
      then have "snd (last ((c1, s) # (c1', t) # xs')) = Normal sa'"             
        using assth by force
      thus ?thesis 
        using snormal seqmap s'eqsa'' split' last_length  
         cptn_mod.CptnModCatch3 induct_step lastc1 lastc1skip
        by (smt append_Cons list.inject list.simps(9))
    next        
      assume assm:" fst (((c1', t) # xs') ! length xs') = Skip \<and>
                       (\<exists>ys. (\<Gamma>,(Skip,snd(last ((c1', t)#xs')))#ys) \<in> cptn_mod \<and>                   
                      xs=(map (lift_catch c2) xs')@((Skip,snd(last ((c1', t)#xs')))#ys))"        
      then have c1'cptn:"(\<Gamma>, (c1', t) # xs') \<in> cptn_mod" using split by blast
      then have induct_step: "(\<Gamma>, (c1, s) # (c1', t)#xs') \<in> cptn_mod"
        using Catchc.hyps(2) Catchc.prems(3) Catchc.prems(4) normal_eq_l by blast  
      then have "map (lift_catch c2) ((c1', t) # xs') = 
                  (Catch c1' c2, t) # map (lift_catch c2) xs'" 
        by (auto simp add: lift_catch_def)
      then obtain ys
        where seqmap:"(Catch c1' c2, t)#xs = 
          (map (lift_catch c2) ((c1', t)#xs'))@((Skip,snd(last ((c1', t)#xs')))#ys)"        
        using assm by fastforce
      then have lastc1:"last ((c1, s) # (c1', t) # xs') = ((c1', t) # xs') ! length xs'"
        by (simp add: last_length) 
      then have lastc1skip:"fst (last ((c1, s) # (c1', t) # xs')) = Skip" 
        using assm by fastforce
      then have "snd (last ((c1, s) # (c1', t) # xs')) = snd (last ((c1',t) # xs'))"
        using assm by force
      thus ?thesis             
        using assm c1'cptn induct_step lastc1skip seqmap by (auto simp add:cptn_mod.CptnModCatch2)
    qed
  }qed              
next
  case (CatchThrowc c2 s1)
  then obtain ns where ns:"s = Normal ns"
    by (metis toSeq_not_Normal)
  then have eq_st: "s=t" using  eq_toSeq[OF CatchThrowc(1)] CatchThrowc(3,4) by auto
  then have c2incptn:"(\<Gamma>, (c2, Normal ns) # xs) \<in> cptn_mod" using ns CatchThrowc
    by auto
  then have 1:"(\<Gamma>, [(Throw, Normal ns)]) \<in> cptn_mod" by (simp add: cptn_mod.CptnModOne)
  then have 2:"fst(last ([(Throw, Normal ns)])) = Throw" by fastforce
  then have 3:"(\<Gamma>,(c2, snd(last [(Throw, Normal ns)]))#xs) \<in> cptn_mod" 
      using c2incptn by auto  
  then have "(c2,Normal ns)#xs=(map (lift c2) [])@(c2, snd(last [(Throw, Normal ns)]))#xs" 
       by (auto simp add:lift_def)
  thus ?case using eq_st ns CptnModCatch3 1 2 3
    by fastforce    
next
  case (CatchSkipc c2 s1)
  have "(\<Gamma>, [(Skip, s)]) \<in> cptn_mod" by (simp add: cptn_mod.CptnModOne)
  then obtain ys where ys_nil:"ys=[]" and last:"(\<Gamma>, (Skip,  s)#ys)\<in> cptn_mod"
    by auto
  moreover have "fst (last ((Skip,  s)#ys)) = Skip" using ys_nil last by auto
  moreover have "snd (last ((Skip,  s)#ys)) = s" using ys_nil last by auto
  moreover from ys_nil have "(map (lift_catch c2) ys) = []" by auto 
  moreover have "s=t"
    using CatchSkipc.prems(3) CatchSkipc.prems(4) eq_toSeq normal_eq_l by blast 
  ultimately show ?case using CatchSkipc.prems by (simp add: cptn_mod.CptnModCatch2 ys_nil)
next
  case (FaultPropc c f)
  thus ?case
    by (metis cptn_mod.CptnModSkip stepc.FaultPropc) 
next
  case (AbruptPropc c f)
  thus ?case by (metis cptn_mod.CptnModSkip stepc.AbruptPropc)
next
  case (StuckPropc c)
  thus ?case by (simp add: cptn_mod.CptnModSkip stepc.StuckPropc)
qed

lemma cptn_onlyif_cptn_mod: 
assumes cptn_asm:"(\<Gamma>,c) \<in> cptn"
shows  "(\<Gamma>,c) \<in> cptn_mod"
using cptn_asm
proof (induct) 
 case CptnOne thus ?case by (rule CptnModOne)
next
  case (Cptn \<Gamma> P s Q t xs)
  then have "\<Gamma>\<turnstile>\<^sub>c (P, s) \<rightarrow>\<^sub>e (Q, t) \<or> \<Gamma>\<turnstile>\<^sub>c (P, toSeq s) \<rightarrow> (Q, toSeq t)"
    using step_ce_not_step_e_step_c by blast
  moreover{
    assume "\<Gamma>\<turnstile>\<^sub>c (P, s) \<rightarrow>\<^sub>e (Q, t)"
    then have ?case
      using Cptn.hyps(3) cptn_mod.CptnModEnv env_c_c' by blast
  }
  moreover{
    assume a00:"\<Gamma>\<turnstile>\<^sub>c (P, toSeq s) \<rightarrow> (Q, toSeq t)"   
    moreover have "\<not> \<Gamma>\<turnstile>\<^sub>c (P, s) \<rightarrow>\<^sub>e (Q, t)"
      using env_c_c' mod_env_not_component calculation by blast    
    then have ?case using cptn_onlyif_cptn_mod_aux[OF _ _ a00 _ Cptn(3)] Cptn by fastforce
  }
  ultimately show ?case by auto 
qed

lemma lift_is_cptn: 
assumes cptn_asm:"(\<Gamma>,c)\<in>cptn"
shows "(\<Gamma>,map (lift P) c) \<in> cptn"
using cptn_asm
proof (induct)
 case CptnOne thus ?case using cptn.simps by fastforce
next
  case (Cptn \<Gamma> Pa s Q t xs)
  have "\<Gamma>\<turnstile>\<^sub>c (Pa, s) \<rightarrow>\<^sub>e (Q, t) \<or> \<Gamma>\<turnstile>\<^sub>c (Pa, toSeq s) \<rightarrow> (Q, toSeq t)"
    using Cptn.hyps(1) step_ce_not_step_e_step_c by blast
  moreover{
    assume "\<Gamma>\<turnstile>\<^sub>c (Pa, s) \<rightarrow>\<^sub>e (Q, t)" 
    then have ?case using Cptn unfolding lift_def
      by (cases rule: step_e.cases, (simp add: Env cptn.Cptn e_step), (simp add: Env_n cptn.Cptn e_step)) 
  }
  moreover {
    assume "\<Gamma>\<turnstile>\<^sub>c (Pa, toSeq s) \<rightarrow> (Q, toSeq t)"
    moreover have "\<Gamma>\<turnstile>\<^sub>c (LanguageCon.com.Seq Pa P, toSeq s) \<rightarrow> (LanguageCon.com.Seq Q P, toSeq t)"
      using Seqc calculation by blast
    ultimately have "\<Gamma>\<turnstile>\<^sub>c (LanguageCon.com.Seq Pa P, s) \<rightarrow>\<^sub>c\<^sub>e (LanguageCon.com.Seq Q P, t)"
      using Cptn.hyps(1) c_step[of \<Gamma> "LanguageCon.com.Seq Pa P" s "LanguageCon.com.Seq Q P" t] 
      env_c_c' step_ce_notNormal step_ce_step_c_eq_c step_dest
      by (metis xstate.inject(2) xstate.simps(5)) 
    then have ?case using  Cptn by (simp add:  cptn.Cptn lift_def)
  }
  ultimately show ?case by auto
qed

lemma lift_catch_is_cptn:
assumes cptn_asm:"(\<Gamma>,c)\<in>cptn"
shows "(\<Gamma>,map (lift_catch P) c) \<in> cptn"
using cptn_asm
proof (induct)
  case CptnOne thus ?case using cptn.simps by fastforce
next
  case (Cptn \<Gamma> Pa s Q t xs)
  have "\<Gamma>\<turnstile>\<^sub>c (Pa, s) \<rightarrow>\<^sub>e (Q, t) \<or> \<Gamma>\<turnstile>\<^sub>c (Pa, toSeq s) \<rightarrow> (Q, toSeq t)"
    using Cptn.hyps(1) step_ce_not_step_e_step_c by blast
  moreover{
    assume "\<Gamma>\<turnstile>\<^sub>c (Pa, s) \<rightarrow>\<^sub>e (Q, t)" 
    then have ?case using Cptn unfolding lift_catch_def
      by (cases rule: step_e.cases, (simp add: Env cptn.Cptn e_step), (simp add: Env_n cptn.Cptn e_step)) 
  }
  moreover {
    assume "\<Gamma>\<turnstile>\<^sub>c (Pa, toSeq s) \<rightarrow> (Q, toSeq t)"
    moreover have "\<Gamma>\<turnstile>\<^sub>c (LanguageCon.com.Catch Pa P, toSeq s) \<rightarrow> (LanguageCon.com.Catch Q P, toSeq t)"
      using Catchc calculation by blast
    ultimately have "\<Gamma>\<turnstile>\<^sub>c (LanguageCon.com.Catch Pa P, s) \<rightarrow>\<^sub>c\<^sub>e (LanguageCon.com.Catch Q P, t)"
      using Cptn.hyps(1) c_step[of \<Gamma> "LanguageCon.com.Catch Pa P" s "LanguageCon.com.Catch Q P" t] 
      env_c_c' step_ce_notNormal step_ce_step_c_eq_c step_dest
      by (metis xstate.inject(2) xstate.simps(5)) 
    then have ?case using  Cptn by (simp add:  cptn.Cptn lift_catch_def)
  }
  ultimately show ?case by auto  
qed

lemma last_lift: "\<lbrakk>xs\<noteq>[]; fst(xs!(length xs - (Suc 0)))=Q\<rbrakk> 
 \<Longrightarrow> fst((map (lift P) xs)!(length (map (lift P) xs)- (Suc 0)))=Seq Q P"
  by (cases "(xs ! (length xs - (Suc 0)))") (simp add:lift_def)

lemma last_lift_catch: "\<lbrakk>xs\<noteq>[]; fst(xs!(length xs - (Suc 0)))=Q\<rbrakk> 
 \<Longrightarrow> fst((map (lift_catch P) xs)!(length (map (lift_catch P) xs)- (Suc 0)))=Catch Q P"
  by (cases "(xs ! (length xs - (Suc 0)))") (simp add:lift_catch_def)

lemma last_fst [rule_format]: "P((a#x)!length x) \<longrightarrow> \<not>P a \<longrightarrow> P (x!(length x - (Suc 0)))" 
  by (induct x) simp_all


lemma last_fst_esp: 
 "fst(((P,s)#xs)!(length xs))=Skip \<Longrightarrow> P\<noteq>Skip \<Longrightarrow> fst(xs!(length xs - (Suc 0)))=Skip" 
apply(erule last_fst)
apply simp
done

lemma last_snd: "xs\<noteq>[] \<Longrightarrow> 
  snd(((map (lift P) xs))!(length (map (lift P) xs) - (Suc 0)))=snd(xs!(length xs - (Suc 0)))"
  by (cases "(xs ! (length xs - (Suc 0)))") (simp_all add:lift_def)

lemma last_snd_catch: "xs\<noteq>[] \<Longrightarrow> 
  snd(((map (lift_catch P) xs))!(length (map (lift_catch P) xs) - (Suc 0)))=snd(xs!(length xs - (Suc 0)))"
  by (cases "(xs ! (length xs - (Suc 0)))") (simp_all add:lift_catch_def)

lemma Cons_lift: "((Seq P Q), s) # (map (lift Q) xs) = map (lift Q) ((P, s) # xs)"
  by (simp add:lift_def)
thm last_map eq_snd_iff list.inject list.simps(9) last_length
lemma Cons_lift_catch: "((Catch P Q), s) # (map (lift_catch Q) xs) = map (lift_catch Q) ((P, s) # xs)"
  by (simp add:lift_catch_def)

lemma Cons_lift_append: 
  "((Seq P Q), s) # (map (lift Q) xs) @ ys = map (lift Q) ((P, s) # xs)@ ys "
  by (simp add:lift_def)

lemma Cons_lift_catch_append: 
  "((Catch P Q), s) # (map (lift_catch Q) xs) @ ys = map (lift_catch Q) ((P, s) # xs)@ ys "
  by (simp add:lift_catch_def)

lemma lift_nth: "i<length xs \<Longrightarrow> map (lift Q) xs ! i = lift Q  (xs! i)"
  by (simp add:lift_def)

lemma lift_catch_nth: "i<length xs \<Longrightarrow> map (lift_catch Q) xs ! i = lift_catch Q  (xs! i)"
  by (simp add:lift_catch_def)
thm list.simps(9) last_length lift_catch_def Cons_lift_catch
lemma snd_lift: "i< length xs \<Longrightarrow> snd(lift Q (xs ! i))= snd (xs ! i)"
  by (cases "xs!i") (simp add:lift_def)

lemma snd_lift_catch: "i< length xs \<Longrightarrow> snd(lift_catch Q (xs ! i))= snd (xs ! i)"
  by (cases "xs!i") (simp add:lift_catch_def)


lemma lift_P1: 
 assumes map_cptn:"(\<Gamma>, map (lift Q) ((P, s) # xs)) \<in> cptn" and
         P_ends:"fst (last ((P, s) # xs)) = Skip"
 shows "(\<Gamma>, map (lift Q) ((P, s) # xs) @ [(Q, snd (last ((P, s) # xs)))]) \<in> cptn"
using map_cptn P_ends
proof (induct xs arbitrary: P s) 
  case Nil
  have P0_skips: "P=Skip" using Nil.prems(2) by auto   
  then have "\<Gamma>\<turnstile>\<^sub>c (LanguageCon.com.Seq LanguageCon.com.Skip Q, s) \<rightarrow>\<^sub>c\<^sub>e (Q, s)"
    by (metis SeqSkipc c_step xstate.inject(1) xstate.inject(2) xstate.simps(5))
  then have "(\<Gamma>,[(Seq Skip Q, s), (Q, s)]) \<in> cptn"       
    by (simp add: cptn.Cptn cptn.CptnOne)
  then show ?case using P0_skips by (simp add: lift_def)
next
  case (Cons a xs)
  have "(\<Gamma>, map (lift Q) ((P, s) # a # xs)) \<in> cptn"
    using Cons.prems(1) by blast  
  have "fst (last ( a # xs)) = Skip" using Cons.prems(2) by auto
  also have seq_PQ:"(\<Gamma>,(Seq P Q,s) # (map (lift Q) (a#xs))) \<in> cptn"
    by (metis Cons.prems(1) Cons_lift)
  then have "(\<Gamma>,(map (lift Q) (a#xs))) \<in> cptn"
    proof -
      assume a1:"(\<Gamma>, (Seq P Q, s) # map (lift Q) (a # xs)) \<in> cptn"            
      then obtain a1 a2 xs1 where a2: "map (lift Q) (a#xs) = ((a1,a2)#xs1)" by fastforce 
      thus ?thesis  using cptn_dest using seq_PQ by auto 
    qed 
  then have "(\<Gamma>, map (lift Q) (a#xs) @ [(Q, snd (last ((a#xs))))]) \<in> cptn" 
   by (metis Cons.hyps(1) calculation prod.collapse)   
  then have t1:"(\<Gamma>, (Seq (fst a) Q, (snd a))#map (lift Q) xs @ [(Q, snd (last ((P, s)#(a#xs))))]) \<in> cptn"
   by (simp add: Cons_lift_append)
  then have "(\<Gamma>,(Seq P Q,s) # (Seq (fst a) Q, (snd a))#map (lift Q) xs)\<in> cptn"
   using seq_PQ by (simp add: Cons_lift)  
  then have t2: "(\<Gamma>,(Seq P Q,s) # [(Seq (fst a) Q, (snd a))]) \<in> cptn"
   using cptn_dest1 by blast
  then have"((Seq P Q,s) # [(Seq (fst a) Q, (snd a))])!length [(Seq (fst a) Q, (snd a))] = (Seq (fst a) Q, (snd a))"
   by auto  
  then have "(\<Gamma>,(Seq P Q,s) # [(Seq (fst a) Q, (snd a))]@map (lift Q) xs @ [(Q, snd (last ((P, s)#(a#xs))))])\<in> cptn"
   using cptn_append_is_cptn t1 t2 by blast   
  then have "(\<Gamma>, map (lift Q) ((P,s)#(fst a, snd a)#xs) @[(Q, snd (last ((P, s)#(a#xs))))])\<in>cptn"
   using Cons_lift_append append_Cons append_Nil by metis
  thus ?case by auto    
qed


lemma lift_catch_P1: 
 assumes map_cptn:"(\<Gamma>, map (lift_catch Q) ((P, Normal s) # xs)) \<in> cptn" and
         P_ends:"fst (last ((P, Normal s) # xs)) = Throw" and
         P_ends_normal:"\<exists>p. snd(last ((P, Normal s) # xs)) = Normal p"
 shows "(\<Gamma>, map (lift_catch Q) ((P, Normal s) # xs) @ [(Q, snd (last ((P, Normal s) # xs)))]) \<in> cptn"
using map_cptn P_ends P_ends_normal
proof (induct xs arbitrary: P s) 
  case Nil
  have P0_skips: "P=Throw" using Nil.prems(2) by auto   
  then have "\<Gamma>\<turnstile>\<^sub>c (LanguageCon.com.Catch LanguageCon.com.Throw Q, Normal s) \<rightarrow>\<^sub>c\<^sub>e (Q, Normal s)"
     by (metis CatchThrowc surj_pair transfer_normal)
  then have "(\<Gamma>,[(Catch Throw Q, Normal s), (Q, Normal s)]) \<in> cptn"
    by (simp add: cptn.Cptn CatchThrowc cptn.CptnOne)
  then show ?case using P0_skips by (simp add: lift_catch_def)
next
  case (Cons a xs) 
  have s1:"(\<Gamma>, map (lift_catch Q) ((P, Normal s) # a # xs)) \<in> cptn"
    using Cons.prems(1) by blast 
  have s2:"fst (last ( a # xs)) = Throw" using Cons.prems(2) by auto
  then obtain p where s3:"snd(last (a #xs)) = Normal p" using Cons.prems(3) by auto
  also have seq_PQ:"(\<Gamma>,(Catch P Q,Normal s) # (map (lift_catch Q) (a#xs))) \<in> cptn"
    by (metis Cons.prems(1) Cons_lift_catch) thm Cons.hyps
  then have axs_in_cptn:"(\<Gamma>,(map (lift_catch Q) (a#xs))) \<in> cptn"
    proof -
      assume a1:"(\<Gamma>, (Catch P Q, Normal s) # map (lift_catch Q) (a # xs)) \<in> cptn"            
      then obtain a1 a2 xs1 where a2: "map (lift_catch Q) (a#xs) = ((a1,a2)#xs1)" by fastforce 
      thus ?thesis  using cptn_dest using seq_PQ by auto 
    qed 
  then have "(\<Gamma>, map (lift_catch Q) (a#xs) @ [(Q, snd (last ((a#xs))))]) \<in> cptn" 
    proof (cases "xs=[]")
      case True thus ?thesis using s2 s3 axs_in_cptn by (metis Cons.hyps eq_snd_iff last_ConsL)
    next
      case False            
      from seq_PQ have seq:"(\<Gamma>,(Catch P Q,Normal s) # (Catch (fst a) Q,snd a)#map (lift_catch Q) xs)\<in> cptn"
        by (simp add: Cons_lift_catch)                         
      obtain cf sf where last_map_axs:"(cf,sf)=last (map (lift_catch Q) (a#xs))" using prod.collapse by blast
      have "\<forall>p ps. (ps=[] \<and> last [p] = p) \<or> (ps\<noteq>[] \<and> last (p#ps) = last ps)" by simp              
      then have tranclos:"\<Gamma>\<turnstile>\<^sub>c (Catch P Q,Normal s) \<rightarrow>\<^sub>c\<^sub>e\<^sup>* (Catch (fst a) Q,snd a)" using Cons_lift_catch
            by (metis (no_types) cptn_dest1 cptn_stepc_rtrancl not_Cons_self2 seq)
      have tranclos_a:"\<Gamma>\<turnstile>\<^sub>c (Catch (fst a) Q,snd a) \<rightarrow>\<^sub>c\<^sub>e\<^sup>* (cf,sf)"
           by (metis Cons_lift_catch axs_in_cptn cptn_stepc_rtrancl last_map_axs prod.collapse)      
      have snd_last:"snd (last (map (lift_catch Q) (a#xs))) = snd (last (a #xs))"
      proof - 
         have eqslist:"snd(((map (lift_catch Q) (a#xs)))!(length (map (lift_catch Q) xs)))= snd((a#xs)!(length xs))" 
           using last_snd_catch by fastforce  
         have "(lift_catch Q a)#(map (lift_catch Q) xs) = (map (lift_catch Q) (a#xs))" by auto
         then have "(map (lift_catch Q) (a#xs))!(length (map (lift_catch Q) xs)) = last (map (lift_catch Q) (a#xs))"
           using last_length [of "(lift_catch Q a)" "(map (lift_catch Q) xs)"] by auto
         thus ?thesis using eqslist by (simp add:last_length)
      qed
      then obtain p1 where  "(snd a) = Normal p1"
         by (metis tranclos_a last_map_axs s3 snd_conv step_ce_normal_to_normal tranclos)   
      moreover obtain a1 a2 where aeq:"a = (a1,a2)" by fastforce 
      moreover have "fst (last ((a1,a2) # xs)) = Throw" using s2 False by auto  
      moreover have "(\<Gamma>, map (lift_catch Q) ((a1,a2) # xs)) \<in> cptn" using aeq axs_in_cptn False by auto  
      moreover have "\<exists>p. snd (last ((a1,a2) # xs)) = Normal p" using s3 aeq by auto
      moreover have "a2 = Normal p1" using aeq calculation(1) by auto 
      ultimately have "(\<Gamma>, map (lift_catch Q) ((a1,a2) # xs) @
                           [(Q, snd (last ((a1,a2) # xs)))])\<in> cptn" 
                 using Cons.hyps aeq by blast
      thus ?thesis using aeq by force 
    qed      
  then have t1:"(\<Gamma>, (Catch (fst a) Q, (snd a))#map (lift_catch Q) xs @ [(Q, snd (last ((P, Normal s)#(a#xs))))]) \<in> cptn"
   by (simp add: Cons_lift_catch_append)
  then have "(\<Gamma>,(Catch P Q,Normal s) # (Catch (fst a) Q, (snd a))#map (lift_catch Q) xs)\<in> cptn"
   using seq_PQ by (simp add: Cons_lift_catch)  
  then have t2: "(\<Gamma>,(Catch P Q,Normal s) # [(Catch (fst a) Q, (snd a))]) \<in> cptn"
   using cptn_dest1 by blast
  then have"((Catch P Q,Normal s) # [(Catch (fst a) Q, (snd a))])!length [(Catch (fst a) Q, (snd a))] = (Catch (fst a) Q, (snd a))"
   by auto  
  then have "(\<Gamma>,(Catch P Q,Normal s) # [(Catch (fst a) Q, (snd a))]@map (lift_catch Q) xs @ [(Q, snd (last ((P, Normal s)#(a#xs))))])\<in> cptn"
   using cptn_append_is_cptn t1 t2 by blast
  then have "(\<Gamma>, map (lift_catch Q) ((P,Normal s)#(fst a, snd a)#xs) @[(Q, snd (last ((P,Normal s)#(a#xs))))])\<in>cptn"
   using Cons_lift_catch_append append_Cons append_Nil by metis
  thus ?case by auto    
qed

lemma seq2:
assumes 
    p1:"(\<Gamma>, (P0, s) # xs) \<in> cptn_mod" and
    p2:"(\<Gamma>, (P0, s) # xs) \<in> cptn" and
    p3:"fst (last ((P0, s) # xs)) = Skip" and
    p4:"(\<Gamma>, (P1, snd (last ((P0, s) # xs))) # ys) \<in> cptn_mod" and
    p5:"(\<Gamma>, (P1, snd (last ((P0, s) # xs))) # ys) \<in> cptn" and
    p6:"zs = map (lift P1) xs @ (P1, snd (last ((P0, s) # xs))) # ys"
shows "(\<Gamma>, (Seq P0 P1, s) # zs) \<in> cptn"
using p1 p2 p3 p4 p5 p6
proof -
have last_skip:"fst (last ((P0, s) # xs)) = Skip" using p3 by blast 
  have "(\<Gamma>, (map (lift P1) ((P0, s) # xs))@(P1, snd (last ((P0, s) # xs))) # ys) \<in> cptn"
  proof -
    have "(\<Gamma>,map (lift P1) ((P0, s) #xs)) \<in> cptn"
      using p2 lift_is_cptn by blast 
    then have "(\<Gamma>,map (lift P1) ((P0, s) #xs)@[(P1, snd (last ((P0, s) # xs)))]) \<in> cptn" 
      using last_skip lift_P1 by blast 
    then have "(\<Gamma>,(Seq P0 P1, s) # map (lift P1) xs@[(P1, snd (last ((P0, s) # xs)))]) \<in> cptn"
         by (simp add: Cons_lift_append)
    moreover have "last ((Seq P0 P1, s) # map (lift P1) xs @[(P1, snd (last ((P0, s) # xs)))]) = (P1, snd (last ((P0, s) # xs)))" 
      by auto  
    moreover have "last ((Seq P0 P1, s) # map (lift P1) xs @[(P1, snd (last ((P0, s) # xs)))]) =
                   ((Seq P0 P1, s) # map (lift P1) xs @[(P1, snd (last ((P0, s) # xs)))])!length (map (lift P1) xs @[(P1, snd (last ((P0, s) # xs)))])" 
      by (metis last_length)             
    ultimately have "(\<Gamma>, (Seq P0 P1, s) # map (lift P1) xs @ (P1, snd (last ((P0, s) # xs))) # ys)\<in> cptn" 
      using cptn_append_is_cptn p5 by fastforce
    thus ?thesis by (simp add: Cons_lift_append)
  qed 
  thus ?thesis  
    by (simp add: Cons_lift_append p6)
qed

lemma seq3:
assumes
    p1:"(\<Gamma>, (P0, Normal s) # xs) \<in> cptn_mod" and
    p2:"(\<Gamma>, (P0, Normal s) # xs) \<in> cptn" and
    p3:"fst (last ((P0, Normal s) # xs)) = Throw" and
    p4:"snd (last ((P0, Normal s) # xs)) = Normal s'" and
    p5:"(\<Gamma>,(Throw,Normal s')#ys) \<in> cptn_mod" and
    p6:"(\<Gamma>,(Throw,Normal s')#ys) \<in> cptn" and
    p7:"zs = map (lift P1) xs @((Throw,Normal s')#ys)" 
shows "(\<Gamma>, (Seq P0 P1, Normal s) # zs) \<in> cptn"
using p1 p2 p3 p4 p5 p6 p7
proof (induct xs arbitrary: zs P0 s)   
  case Nil 
  have h:"\<Gamma>\<turnstile>\<^sub>c (LanguageCon.com.Seq LanguageCon.com.Throw P1, Normal s') \<rightarrow>\<^sub>c\<^sub>e (LanguageCon.com.Throw, Normal s')"
    using SeqThrowc
    by (metis old.prod.exhaust transfer_normal)
  show ?case using cptn.Cptn[OF h,of ys] Nil
    by simp
next
  case (Cons a as)
  then obtain sa where "snd a = Normal sa" by (meson Normal_Normal)
  obtain a1 a2 where a_prod:"a=(a1,a2)" by fastforce
  obtain la1 la2 where last_prod:"last (a#as) = (la1,la2)" by fastforce 
  then have lasst_aas_last: "last (a#as) = (last ((P0, Normal s) # a # as))" by auto    
  then have "la1 = Throw" using Cons.prems(3) last_prod by force
  have "la2 = Normal s'" using Cons.prems(4) last_prod lasst_aas_last by force
  have f1: "(\<Gamma>, (a1, a2) # as) \<in> cptn"
    using Cons.prems(2) a_prod cptn_dest by blast
  have f2: "Normal sa = a2"
    using `snd a = Normal sa` a_prod by force
  have "(\<Gamma>, a # as) \<in> cptn_mod"
    using f1 a_prod cptn_onlyif_cptn_mod by blast
  then have hyp:"(\<Gamma>, (Seq a1 P1, Normal sa) # 
            map (lift P1) as @ ((Throw,Normal s')#ys)) \<in> cptn"
        using Cons.hyps Cons.prems(3) Cons.prems(4)  Cons.prems(5) Cons.prems(6) a_prod f1 f2 by fastforce
  thus ?case
  proof -
    have "(Seq a1 P1, a2) # map (lift P1) as @((Throw,Normal s')#ys) = zs"
      by (simp add: Cons.prems(7) Cons_lift_append a_prod)    
    moreover have "\<Gamma>\<turnstile>\<^sub>c (Seq P0 P1, Normal s) \<rightarrow>\<^sub>c\<^sub>e (Seq a1 P1, a2)"
      using Cons.prems(2) a_prod cptn_elim_cases(2)
      by (smt Seqc e_step env_intro eq_fst_iff eq_snd_iff f2 not_eq_not_env step_ce_dest step_dest1 toSeq.simps(1) transfer_normal)
    ultimately show ?thesis using  Cons.prems(2) Seqc a_prod cptn.Cptn  cptn_elim_cases f2 hyp
      by blast      
  qed 
qed

lemma cptn_if_cptn_mod: 
assumes cptn_mod_asm:"(\<Gamma>,c) \<in> cptn_mod"
shows  "(\<Gamma>,c) \<in> cptn"
using cptn_mod_asm
proof (induct)
  case (CptnModOne) thus ?case using cptn.CptnOne by blast
next
  case CptnModSkip thus ?case
    by (simp add: c_step cptn.Cptn) 
next
  case CptnModThrow thus ?case by (simp add: c_step cptn.Cptn) 
next 
  case CptnModCondT thus ?case
    by (metis CondTruec cptn.Cptn prod.exhaust_sel transfer_normal) 
next
  case CptnModCondF thus ?case
    by (metis CondFalsec cptn.Cptn prod.exhaust_sel transfer_normal)
next
  case (CptnModSeq1 \<Gamma> P0 s xs zs P1) 
  have "(\<Gamma>, map (lift P1) ((P0, s) # xs)) \<in> cptn"
    using CptnModSeq1.hyps(2) lift_is_cptn by blast
  thus ?case by (simp add: Cons_lift CptnModSeq1.hyps(3))
next
  case (CptnModSeq2 \<Gamma> P0 s xs P1 ys zs)   
  thus ?case by (simp add:seq2)
next
  case (CptnModSeq3 \<Gamma> P0 s xs s' zs P1) 
  thus ?case by (simp add: seq3)
next
  case (CptnModWhile1  \<Gamma> P s xs b zs) thus ?case
    by (metis Cons_lift WhileTruec cptn.Cptn lift_is_cptn prod.collapse transfer_normal)
next 
  case (CptnModWhile2  \<Gamma> P s xs b zs ys)    
  then have "(\<Gamma>, (Seq P (While b P), Normal s) # zs) \<in> cptn" 
    by (simp add:seq2)  
  moreover have "\<Gamma>\<turnstile>\<^sub>c(While b P,toSeq (Normal s)) \<rightarrow> (Seq P (While b P),toSeq(Normal s))" 
    by (simp add: CptnModWhile2.hyps(4) WhileTruec)
  ultimately show ?case
    by (metis  cptn.Cptn prod.collapse toSeq.simps(1) transfer_normal)
next
  case (CptnModWhile3  \<Gamma> P s xs b s' ys zs) 
  then have "(\<Gamma>,(Seq P (While b P), Normal s) # zs) \<in> cptn"
    by (simp add: seq3)        
  moreover have "\<Gamma>\<turnstile>\<^sub>c(While b P,toSeq (Normal s)) \<rightarrow> (Seq P (While b P),toSeq (Normal s))"
    by (simp add: CptnModWhile3.hyps(4) WhileTruec)
  ultimately show ?case by (metis  cptn.Cptn prod.collapse toSeq.simps(1) transfer_normal)
next 
  case (CptnModCall \<Gamma> bdy s ys p) thus ?case
    by (metis Callc cptn.Cptn prod.exhaust_sel transfer_normal) 
next
  case (CptnModDynCom \<Gamma> c s ys) thus ?case
    by (metis DynComc cptn.Cptn prod.exhaust_sel transfer_normal)
next
  case (CptnModGuard \<Gamma> c s ys g f) thus ?case
    by (metis Guardc cptn.Cptn prod.exhaust_sel transfer_normal)
next
  case (CptnModCatch1 \<Gamma> P0 s xs zs P1)
  have "(\<Gamma>, map (lift_catch P1) ((P0, s) # xs)) \<in> cptn"
    using CptnModCatch1.hyps(2) lift_catch_is_cptn by blast
  thus ?case by (simp add: Cons_lift_catch CptnModCatch1.hyps(3))
next
  case (CptnModCatch2 \<Gamma> P0 s xs ys zs P1)
  thus ?case
  proof (induct xs arbitrary: zs P0 s) 
    case Nil 
    then have "\<Gamma>\<turnstile>\<^sub>c (Catch Skip P1, s) \<rightarrow>\<^sub>c\<^sub>e (LanguageCon.com.Skip, s)"
      by (metis CatchSkipc c_step xstate.inject(2) xstate.simps(1) xstate.simps(5))
    thus ?case using cptn.simps
      using Nil.prems(3) Nil.prems(5) Nil.prems(6) by fastforce
  next
    case (Cons a as)
    then obtain sa where "snd a = sa" by auto
    then obtain a1 a2 where a_prod:"a=(a1,a2)" and sa_a2: "a2 =sa" 
           by fastforce
    obtain la1 la2 where last_prod:"last (a#as) = (la1,la2)" by fastforce 
    then have lasst_aas_last: "last (a#as) = (last ((P0, s) # a # as))" by auto    
    then have "la1 = Skip" using Cons.prems(3) last_prod by force
    have f1: "(\<Gamma>, (a1, a2) # as) \<in> cptn"
      using Cons.prems(2) a_prod cptn_dest by blast
    have "(\<Gamma>, a # as) \<in> cptn_mod"
      using f1 a_prod cptn_onlyif_cptn_mod by blast
    then have hyp:"(\<Gamma>, (Catch a1 P1, a2) # 
              map (lift_catch P1) as @ ((Skip, la2)#ys)) \<in> cptn"
          using Cons.hyps Cons.prems a_prod f1 last_prod by fastforce
    thus ?case
    proof -
      have f1:"(Catch a1 P1, a2) # map (lift_catch P1) as @ ((Skip, la2)#ys) = zs"
        using Cons.prems(4) Cons_lift_catch_append a_prod last_prod by (simp add: Cons.prems(6))         
      have "(\<Gamma>, map (lift_catch P1) ((P0, s) # a # as)) \<in> cptn"
       using Cons.prems(2) lift_catch_is_cptn by blast
      hence "(\<Gamma>, (LanguageCon.com.Catch P0 P1, s) # (LanguageCon.com.Catch a1 P1, a2) # map (lift_catch P1) as) \<in> cptn"
        by (metis (no_types) Cons_lift_catch a_prod)
      hence "(\<Gamma>, (LanguageCon.com.Catch P0 P1, s) # zs) \<in> cptn \<or> (\<Gamma>, (LanguageCon.com.Catch P0 P1, s) # (LanguageCon.com.Catch a1 P1, a2) # map (lift_catch P1) as) \<in> cptn \<and> (\<not> \<Gamma>\<turnstile>\<^sub>c (LanguageCon.com.Catch P0 P1, s) \<rightarrow>\<^sub>e (LanguageCon.com.Catch P0 P1, a2) \<or> (\<Gamma>, (LanguageCon.com.Catch P0 P1, a2) # map (lift_catch P1) as) \<notin> cptn \<or> LanguageCon.com.Catch a1 P1 \<noteq> LanguageCon.com.Catch P0 P1)"
        using f1 cptn.Cptn hyp
        using e_step by blast
      thus ?thesis
       by (metis (no_types) f1 cptn.Cptn cptn_elim_cases(2) hyp)
     qed
   qed
next 
  case (CptnModCatch3  \<Gamma> P0 s xs s' P1 ys zs)
  thus ?case
  proof (induct xs arbitrary: zs P0 s) 
    case Nil 
    then have "\<Gamma>\<turnstile>\<^sub>c (LanguageCon.com.Catch LanguageCon.com.Throw P1, Normal s) \<rightarrow>\<^sub>c\<^sub>e (P1, Normal s)"
      by (metis CatchThrowc prod.exhaust_sel transfer_normal)
    thus ?case using  cptn.simps
      using Nil.prems(3) Nil.prems(6) Nil.prems(7) by fastforce
  next
    case (Cons a as)
    then obtain sa where "snd a = Normal sa" by (meson Normal_Normal)
    obtain a1 a2 where a_prod:"a=(a1,a2)" by fastforce
    obtain la1 la2 where last_prod:"last (a#as) = (la1,la2)" by fastforce 
    then have lasst_aas_last: "last (a#as) = (last ((P0, Normal s) # a # as))" by auto    
    then have "la1 = Throw" using Cons.prems(3) last_prod by force
    have "la2 = Normal s'" using Cons.prems(4) last_prod lasst_aas_last by force
    have f1: "(\<Gamma>, (a1, a2) # as) \<in> cptn"
      using Cons.prems(2) a_prod cptn_dest by blast
    have f2: "Normal sa = a2"
      using `snd a = Normal sa` a_prod by force
    have "(\<Gamma>, a # as) \<in> cptn_mod"
      using f1 a_prod cptn_onlyif_cptn_mod by blast
    then have hyp:"(\<Gamma>, (Catch a1 P1, Normal sa) # 
              map (lift_catch P1) as @ (P1, snd (last ((a1, Normal sa) # as))) # ys) \<in> cptn"
          using Cons.hyps Cons.prems a_prod f1 f2
          by (metis lasst_aas_last)
    thus ?case
    proof -
(*      have "\<Gamma>\<turnstile>\<^sub>c (P0, Normal s) \<rightarrow>\<^sub>e (P0, a2)"
        by (fastforce intro: step_e.intros) 
      then *) 
      have transit:"\<Gamma>\<turnstile>\<^sub>c(P0,Normal s) \<rightarrow>\<^sub>c\<^sub>e (a1,Normal sa)"             
        by (metis (no_types) Cons.prems(2) a_prod  cptn_elim_cases(2)  f2)
      then have transit_catch:"\<Gamma>\<turnstile>\<^sub>c(Catch P0 P1,Normal s) \<rightarrow>\<^sub>c\<^sub>e (Catch a1 P1,Normal sa)"          
      proof -
        have f1: "P0 = a1 \<or> \<not> \<Gamma>\<turnstile>\<^sub>c (P0, Normal s) \<rightarrow>\<^sub>e (a1, Normal sa)"
          using not_eq_not_env transit by blast
        have "\<Gamma>\<turnstile>\<^sub>c (a1, Normal s) \<rightarrow>\<^sub>e (a1, Normal sa) \<longrightarrow> 
               \<Gamma>\<turnstile>\<^sub>c (Catch a1 P1, Normal s) \<rightarrow>\<^sub>e (Catch a1 P1, Normal sa)"
          using env_intro by blast
        then show ?thesis
          using f1 by (metis (no_types) Catchc e_step prod.collapse 
              step_dest toSeq.simps(1) transfer_normal transit)
      qed              
      have "a=(a1, Normal sa)" using a_prod f2 by auto
      then have "snd (last ((a1, Normal sa) # as)) = Normal s'"
        using  Cons lasst_aas_last by fastforce
      hence f1: "snd (last ((a1, Normal sa) # as)) = la2"
        using `la2 = Normal s'` by blast
      have "(Catch a1 P1, a2) # map (lift_catch P1) as @ (P1, la2) # ys = zs"
        using Cons.prems Cons_lift_catch_append a_prod last_prod by auto
      moreover have "\<Gamma>\<turnstile>\<^sub>c (LanguageCon.com.Catch P0 P1, Normal s) \<rightarrow>\<^sub>c\<^sub>e (LanguageCon.com.Catch a1 P1, a2)"
         using f2 transit_catch by blast
       ultimately show ?thesis
        using f1 cptn.Cptn  f2 hyp by metis
    qed
  qed
next 
  case (CptnModEnv) thus ?case
    by (simp add: cptn.Cptn e_step)
qed

lemma cptn_eq_cptn_mod: 
shows  "(x \<in>cptn_mod)  = (x\<in>cptn)"
by (cases x, auto simp add: cptn_if_cptn_mod cptn_onlyif_cptn_mod)

lemma cptn_eq_cptn_mod_set: 
shows  "cptn_mod  = cptn"
by (auto simp add: cptn_if_cptn_mod cptn_onlyif_cptn_mod)

subsection \<open>Computational modular semantic for nested calls\<close>
inductive_set cptn_mod_nest_call :: "(nat\<times>('g,'l,'p,'f,'e) confs) set"
where
  CptnModNestOne: "(n,\<Gamma>,[(P, s)]) \<in> cptn_mod_nest_call"
| CptnModNestEnv: "\<lbrakk>\<Gamma>\<turnstile>\<^sub>c(P,s) \<rightarrow>\<^sub>e (P,t);(n,\<Gamma>,(P, t)#xs) \<in> cptn_mod_nest_call\<rbrakk> \<Longrightarrow> 
                     (n,\<Gamma>,(P, s)#(P, t)#xs) \<in> cptn_mod_nest_call"
| CptnModNestSkip: "\<lbrakk>\<Gamma>\<turnstile>\<^sub>c(P,toSeq s) \<rightarrow> (Skip,toSeq t); redex P = P; 
                    \<forall>ns ns'. 
                     (s = Normal ns \<or> s = Abrupt ns) \<and> 
                     (t = Normal ns' \<or> t = Abrupt ns') \<longrightarrow> snd ns = snd ns';
                     \<forall>f. ((\<exists>sn. s = Normal sn) \<and> (\<Gamma> f) = Some Skip \<longrightarrow> P  \<noteq> Call f  );
                      (n,\<Gamma>,(Skip, t)#xs) \<in> cptn_mod_nest_call \<rbrakk> \<Longrightarrow> 
                      (n,\<Gamma>,(P,s)#(Skip, t)#xs) \<in>cptn_mod_nest_call"

| CptnModNestThrow: "\<lbrakk>\<Gamma>\<turnstile>\<^sub>c(P,toSeq s) \<rightarrow> (Throw,toSeq t); redex P = P; 
                     \<forall>f. ((\<exists>sn. s = Normal sn) \<and> (\<Gamma> f) = Some Throw \<longrightarrow> P  \<noteq> Call f  );
                     \<forall>ns ns'. 
                     (s = Normal ns \<or> s = Abrupt ns) \<and> 
                     (t = Normal ns' \<or> t = Abrupt ns') \<longrightarrow> snd ns = snd ns';
                      (n,\<Gamma>,(Throw, t)#xs) \<in> cptn_mod_nest_call \<rbrakk> \<Longrightarrow> 
                      (n,\<Gamma>,(P,s)#(Throw, t)#xs) \<in>cptn_mod_nest_call"

| CptnModNestCondT: "\<lbrakk>(n,\<Gamma>,(P0, Normal s)#ys) \<in> cptn_mod_nest_call; fst s \<in> b \<rbrakk> \<Longrightarrow> 
                    (n,\<Gamma>,((Cond b P0 P1), Normal s)#(P0, Normal s)#ys) \<in> cptn_mod_nest_call"

| CptnModNestCondF: "\<lbrakk>(n,\<Gamma>,(P1, Normal s)#ys) \<in> cptn_mod_nest_call; fst s \<notin> b \<rbrakk> \<Longrightarrow> 
                     (n,\<Gamma>,((Cond b P0 P1), Normal s)#(P1, Normal s)#ys) \<in> cptn_mod_nest_call"

| CptnModNestSeq1: 
  "\<lbrakk>(n,\<Gamma>,(P0, s)#xs) \<in> cptn_mod_nest_call; zs=map (lift P1) xs \<rbrakk> \<Longrightarrow> 
   (n,\<Gamma>,((Seq P0 P1), s)#zs) \<in> cptn_mod_nest_call"

| CptnModNestSeq2: 
  "\<lbrakk>(n,\<Gamma>, (P0, s)#xs) \<in> cptn_mod_nest_call; fst(last ((P0, s)#xs)) = Skip;
    (n,\<Gamma>,(P1, snd(last ((P0, s)#xs)))#ys) \<in> cptn_mod_nest_call;
    zs=(map (lift P1) xs)@((P1, snd(last ((P0, s)#xs)))#ys) \<rbrakk> \<Longrightarrow> 
   (n,\<Gamma>,((Seq P0 P1), s)#zs) \<in> cptn_mod_nest_call"

| CptnModNestSeq3: 
  "\<lbrakk>(n,\<Gamma>, (P0, Normal s)#xs) \<in> cptn_mod_nest_call; 
    fst(last ((P0, Normal s)#xs)) = Throw;
    snd(last ((P0, Normal s)#xs)) = Normal s'; 
    (n,\<Gamma>,(Throw,Normal s')#ys) \<in> cptn_mod_nest_call; 
    zs=(map (lift P1) xs)@((Throw,Normal s')#ys) \<rbrakk> \<Longrightarrow>
   (n,\<Gamma>,((Seq P0 P1), Normal s)#zs) \<in> cptn_mod_nest_call"

| CptnModNestWhile1: 
  "\<lbrakk>(n,\<Gamma>, (P, Normal s)#xs) \<in> cptn_mod_nest_call; fst s \<in> b; 
    zs=map (lift (While b P)) xs \<rbrakk> \<Longrightarrow> 
    (n,\<Gamma>, ((While b P), Normal s)#
      ((Seq P (While b P)),Normal s)#zs) \<in> cptn_mod_nest_call"

| CptnModNestWhile2: 
  "\<lbrakk> (n,\<Gamma>, (P, Normal s)#xs) \<in> cptn_mod_nest_call; 
     fst(last ((P, Normal s)#xs))=Skip; fst s \<in> b; 
     zs=(map (lift (While b P)) xs)@
      (While b P, snd(last ((P, Normal s)#xs)))#ys; 
      (n,\<Gamma>,(While b P, snd(last ((P, Normal s)#xs)))#ys) \<in> 
        cptn_mod_nest_call\<rbrakk> \<Longrightarrow> 
   (n,\<Gamma>,(While b P, Normal s)#
     (Seq P (While b P), Normal s)#zs) \<in> cptn_mod_nest_call"

| CptnModNestWhile3: 
  "\<lbrakk> (n,\<Gamma>, (P, Normal s)#xs) \<in> cptn_mod_nest_call; 
     fst(last ((P, Normal s)#xs))=Throw; fst s \<in> b;
     snd(last ((P, Normal s)#xs)) = Normal s'; 
    (n,\<Gamma>,(Throw,Normal s')#ys) \<in> cptn_mod_nest_call;  
     zs=(map (lift (While b P)) xs)@((Throw,Normal s')#ys)\<rbrakk> \<Longrightarrow> 
   (n,\<Gamma>,(While b P, Normal s)#
     (Seq P (While b P), Normal s)#zs) \<in> cptn_mod_nest_call"

| CptnModNestCall: "\<lbrakk>(n,\<Gamma>,(bdy, Normal s)#ys) \<in> cptn_mod_nest_call;\<Gamma> p = Some bdy; bdy\<noteq>Call p \<rbrakk> \<Longrightarrow> 
                 (Suc n, \<Gamma>,((Call p), Normal s)#(bdy, Normal s)#ys) \<in> cptn_mod_nest_call" 

| CptnModNestDynCom: "\<lbrakk>(n,\<Gamma>,(c (fst s), Normal s)#ys) \<in> cptn_mod_nest_call \<rbrakk> \<Longrightarrow> 
                 (n,\<Gamma>,(DynCom c, Normal s)#(c (fst s), Normal s)#ys) \<in> cptn_mod_nest_call"

| CptnModNestGuard: "\<lbrakk>(n,\<Gamma>,(c, Normal s)#ys) \<in> cptn_mod_nest_call; fst s \<in> g \<rbrakk> \<Longrightarrow> 
                  (n,\<Gamma>,(Guard f g c, Normal s)#(c, Normal s)#ys) \<in> cptn_mod_nest_call"

| CptnModNestCatch1: "\<lbrakk>(n,\<Gamma>,(P0, s)#xs) \<in> cptn_mod_nest_call; zs=map (lift_catch P1) xs \<rbrakk>
                 \<Longrightarrow> (n,\<Gamma>,((Catch P0 P1), s)#zs) \<in> cptn_mod_nest_call"

| CptnModNestCatch2: 
  "\<lbrakk>(n,\<Gamma>, (P0, s)#xs) \<in> cptn_mod_nest_call; fst(last ((P0, s)#xs)) = Skip; 
    (n,\<Gamma>,(Skip,snd(last ((P0, s)#xs)))#ys) \<in> cptn_mod_nest_call;  
    zs=(map (lift_catch P1) xs)@((Skip,snd(last ((P0, s)#xs)))#ys) \<rbrakk> \<Longrightarrow> 
   (n,\<Gamma>,((Catch P0 P1), s)#zs) \<in> cptn_mod_nest_call"

| CptnModNestCatch3: 
  "\<lbrakk>(n,\<Gamma>, (P0, Normal s)#xs) \<in> cptn_mod_nest_call; fst(last ((P0, Normal s)#xs)) = Throw; 
  snd(last ((P0, Normal s)#xs)) = Normal s';
  (n,\<Gamma>,(P1, snd(last ((P0, Normal s)#xs)))#ys) \<in> cptn_mod_nest_call; 
  zs=(map (lift_catch P1) xs)@((P1, snd(last ((P0, Normal s)#xs)))#ys) \<rbrakk> \<Longrightarrow> 
   (n,\<Gamma>,((Catch P0 P1), Normal s)#zs) \<in> cptn_mod_nest_call"

lemmas CptnMod_nest_call_induct = cptn_mod_nest_call.induct [of _ _ "[(c,s)]", split_format (complete), case_names
CptnModOne CptnModEnv CptnModSkip CptnModThrow CptnModCondT CptnModCondF 
CptnModSeq1 CptnModSeq2 CptnModSeq3 CptnModSeq4 CptnModWhile1 CptnModWhile2 CptnModWhile3 CptnModCall CptnModDynCom CptnModGuard 
CptnModCatch1 CptnModCatch2 CptnModCatch3, induct set]

inductive_cases CptnModNest_elim_cases [cases set]:
"(n,\<Gamma>,(Skip, s)#u#xs) \<in> cptn_mod_nest_call"
"(n,\<Gamma>,(Guard f g c, s)#u#xs) \<in> cptn_mod_nest_call"
"(n,\<Gamma>,(Basic f e, s)#u#xs) \<in> cptn_mod_nest_call"
"(n,\<Gamma>,(Spec r e, s)#u#xs) \<in> cptn_mod_nest_call"
"(n,\<Gamma>,(Seq c1 c2, s)#u#xs) \<in> cptn_mod_nest_call"
"(n,\<Gamma>,(Cond b c1 c2, s)#u#xs) \<in> cptn_mod_nest_call"
"(n,\<Gamma>,(Await b c2 e, s)#u#xs) \<in> cptn_mod_nest_call"
"(n,\<Gamma>,(Call p, s)#u#xs) \<in> cptn_mod_nest_call"
"(n,\<Gamma>,(DynCom c,s)#u#xs) \<in> cptn_mod_nest_call"
"(n,\<Gamma>,(Throw,s)#u#xs) \<in> cptn_mod_nest_call"
"(n,\<Gamma>,(Catch c1 c2,s)#u#xs) \<in> cptn_mod_nest_call"

inductive_cases stepc_elim_cases_Seq_Seq':
"\<Gamma>\<turnstile>\<^sub>c(Seq c1 c2,s) \<rightarrow> (Seq c1' c2',s')" 

inductive_cases stepc_elim_cases_Catch_Catch':
"\<Gamma>\<turnstile>\<^sub>c(Catch c1 c2,s) \<rightarrow> (Catch c1' c2',s')" 

inductive_cases CptnModNest_same_elim_cases [cases set]:
"(n,\<Gamma>,(u, s)#(u,t)#xs) \<in> cptn_mod_nest_call"

inductive_cases CptnModNest_elim_cases_Stuck [cases set]:
"(n,\<Gamma>,(P, Stuck)#(Skip, s)#xs) \<in> cptn_mod_nest_call"

inductive_cases CptnModNest_elim_cases_Fault [cases set]:
"(n,\<Gamma>,(P, Fault f)#(Skip, s)#xs) \<in> cptn_mod_nest_call"

inductive_cases CptnModNest_elim_cases_Abrupt [cases set]:
"(n,\<Gamma>,(P, Abrupt as)#(Skip, s)#xs) \<in> cptn_mod_nest_call"

inductive_cases  CptnModNest_elim_cases_Call_Stuck [cases set]:
"(n,\<Gamma>,(Call p, s)#(Skip, Stuck)#xs) \<in> cptn_mod_nest_call"

inductive_cases  CptnModNest_elim_cases_Call [cases set]:
"(0, \<Gamma>,((Call p), Normal s)#(bdy, Normal s)#ys) \<in> cptn_mod_nest_call"

inductive_cases  CptnEmpty [cases set]:
"(n, \<Gamma>,[]) \<in> cptn_mod_nest_call"

inductive_cases  CptnModNest_elim_cases_Call_normal [cases set]:
"(Suc n, \<Gamma>,((Call p), Normal s)#(bdy, Normal s)#ys) \<in> cptn_mod_nest_call"

lemma cptn_mod_nest_mono1: "(n,\<Gamma>,cfs) \<in>  cptn_mod_nest_call  \<Longrightarrow> (Suc n,\<Gamma>,cfs)\<in> cptn_mod_nest_call"
proof (induct rule:cptn_mod_nest_call.induct)
  case (CptnModNestOne) thus ?case using cptn_mod_nest_call.CptnModNestOne by blast
next
  case (CptnModNestEnv) thus ?case using cptn_mod_nest_call.CptnModNestEnv by blast
next
   case (CptnModNestSkip) thus ?case using cptn_mod_nest_call.CptnModNestSkip by blast
next
   case (CptnModNestThrow) thus ?case using cptn_mod_nest_call.intros(4) by blast
next
   case (CptnModNestCondT n) thus ?case 
     using cptn_mod_nest_call.CptnModNestCondT[of "Suc n"] by blast
next
  case (CptnModNestCondF n) thus ?case 
    using cptn_mod_nest_call.CptnModNestCondF[of "Suc n"] by blast
next
  case (CptnModNestSeq1 n) thus ?case 
    using cptn_mod_nest_call.CptnModNestSeq1[of "Suc n"] by blast
next
  case (CptnModNestSeq2 n) thus ?case 
     using cptn_mod_nest_call.CptnModNestSeq2[of "Suc n"] by blast
next
  case (CptnModNestSeq3 n) thus ?case 
     using cptn_mod_nest_call.CptnModNestSeq3[of "Suc n"] by blast
next
  case (CptnModNestWhile1 n) thus ?case 
     using cptn_mod_nest_call.CptnModNestWhile1[of "Suc n"] by blast
next
  case (CptnModNestWhile2 n) thus ?case 
     using cptn_mod_nest_call.CptnModNestWhile2[of "Suc n"] by blast
next
  case (CptnModNestWhile3 n) thus ?case 
     using cptn_mod_nest_call.CptnModNestWhile3[of "Suc n"] by blast
next
 case (CptnModNestCall) thus ?case 
     using cptn_mod_nest_call.CptnModNestCall by fastforce
next 
 case (CptnModNestDynCom) thus ?case 
     using cptn_mod_nest_call.CptnModNestDynCom by blast
next
 case (CptnModNestGuard n) thus ?case 
     using cptn_mod_nest_call.CptnModNestGuard[of "Suc n"] by fastforce
next
 case (CptnModNestCatch1 n) thus ?case 
     using cptn_mod_nest_call.CptnModNestCatch1[of "Suc n"] by fastforce
next
 case (CptnModNestCatch2 n) thus ?case 
     using cptn_mod_nest_call.CptnModNestCatch2[of "Suc n"] by fastforce
next
 case (CptnModNestCatch3 n) thus ?case 
     using cptn_mod_nest_call.CptnModNestCatch3[of "Suc n"] by fastforce
qed

lemma cptn_mod_nest_mono2: 
  "(n,\<Gamma>,cfs) \<in>  cptn_mod_nest_call  \<Longrightarrow> m>n \<Longrightarrow>
   (m,\<Gamma>,cfs)\<in> cptn_mod_nest_call"
proof (induct "m-n" arbitrary: m n)
  case 0 thus ?case by auto
next
  case (Suc k) 
  have "m - Suc n = k"
    using Suc.hyps(2) Suc.prems(2) Suc_diff_Suc Suc_inject by presburger
  then show ?case
    using Suc.hyps(1) Suc.prems(1) Suc.prems(2) cptn_mod_nest_mono1 less_Suc_eq by blast   
qed

lemma cptn_mod_nest_mono: 
  "(n,\<Gamma>,cfs) \<in>  cptn_mod_nest_call  \<Longrightarrow> m\<ge>n \<Longrightarrow>
   (m,\<Gamma>,cfs)\<in> cptn_mod_nest_call"
proof (cases "n=m")
  assume "(n, \<Gamma>, cfs) \<in> cptn_mod_nest_call" and  
          "n = m"  thus ?thesis by auto
next
  assume "(n, \<Gamma>, cfs) \<in> cptn_mod_nest_call" and  
         "n\<le>m" and
         "n \<noteq> m"  
   thus ?thesis by (auto simp add: cptn_mod_nest_mono2)
 qed





subsection \<open>Equivalence of comp mod semantics and comp mod nested\<close>

definition catch_cond_nest
where
"catch_cond_nest zs Q xs P s s'' s' \<Gamma> n \<equiv> (zs=(map (lift_catch Q) xs) \<or>
             ((fst(((P, s)#xs)!length xs)=Throw \<and>
               snd(last ((P, s)#xs)) = Normal s' \<and> s=Normal s''\<and>
               (\<exists>ys. (n,\<Gamma>,(Q, snd(((P, s)#xs)!length xs))#ys) \<in> cptn_mod_nest_call \<and> 
                zs=(map (lift_catch Q) xs)@((Q, snd(((P, s)#xs)!length xs))#ys)))) \<or>
                ((fst(((P, s)#xs)!length xs)=Skip \<and> 
                 (\<exists>ys. (n,\<Gamma>,(Skip,snd(last ((P, s)#xs)))#ys) \<in> cptn_mod_nest_call \<and>                   
                 zs=(map (lift_catch Q) xs)@((Skip,snd(last ((P, s)#xs)))#ys)))))
"

lemma div_catch_nest: assumes cptn_m:"(n,\<Gamma>,list) \<in> cptn_mod_nest_call"
shows "(\<forall>s P Q zs. list=(Catch P Q, s)#zs \<longrightarrow>
       (\<exists>xs s' s''. 
          (n, \<Gamma>,(P, s)#xs) \<in> cptn_mod_nest_call  \<and> 
             catch_cond_nest zs Q xs P s s'' s' \<Gamma> n))  
            "
unfolding catch_cond_nest_def
using cptn_m
proof (induct rule: cptn_mod_nest_call.induct)
case (CptnModNestOne \<Gamma> P s)
  thus ?case using cptn_mod_nest_call.CptnModNestOne by blast 
next
  case (CptnModNestSkip  \<Gamma> P s t n xs) 
  from CptnModNestSkip.hyps
  have step: "\<Gamma>\<turnstile>\<^sub>c (P, toSeq s) \<rightarrow> (Skip, toSeq t)" by auto
  from CptnModNestSkip.hyps
  have noskip: "~(P=Skip)" using stepc_elim_cases(1) by blast  
  have no_catch: "\<forall>p1 p2. \<not>(P=Catch p1 p2)" using CptnModNestSkip.hyps(2) redex_not_Catch by auto
  from CptnModNestSkip.hyps
  have in_cptn_mod: "(n,\<Gamma>, (Skip, t) # xs) \<in> cptn_mod_nest_call" by auto  
  then show ?case using no_catch by simp
next
  case (CptnModNestThrow  \<Gamma> P s t n xs) 
  from CptnModNestThrow.hyps
  have step: "\<Gamma>\<turnstile>\<^sub>c (P, toSeq s) \<rightarrow> (Throw, toSeq t)" by auto 
  from CptnModNestThrow.hyps
  have in_cptn_mod: "(n,\<Gamma>, (Throw, t) # xs) \<in> cptn_mod_nest_call" by auto 
  have no_catch: "\<forall>p1 p2. \<not>(P=Catch p1 p2)" using CptnModNestThrow.hyps(2) redex_not_Catch by auto
  then show ?case by auto
next
  case (CptnModNestCondT \<Gamma> P0 s ys b P1)
  thus ?case using CptnModOne by blast
next
  case (CptnModNestCondF \<Gamma> P0 s ys b P1)
  thus ?case using CptnModOne by blast
next
  case (CptnModNestCatch1 sa P Q zs)
  thus ?case by blast
next
  case (CptnModNestCatch2 n \<Gamma> P0 s xs ys zs P1) 
  from CptnModNestCatch2.hyps(3) 
  have last:"fst (((P0, s) # xs) ! length xs) = Skip" 
       by (simp add: last_length) 
  have P0cptn:"(n,\<Gamma>, (P0, s) # xs) \<in> cptn_mod_nest_call" by fact          
  then have "zs = map (lift_catch P1) xs @((Skip,snd(last ((P0, s)#xs)))#ys)" by (simp add:CptnModNestCatch2.hyps)
  show ?case
  proof -{
    fix sa P Q zsa    
    assume eq:"(Catch P0 P1, s) # zs = (Catch P Q, sa) # zsa"
    then have "P0 =P \<and> P1 = Q \<and> s=sa \<and> zs=zsa" by auto
    then have "(P0, s) = (P, sa)" by auto 
    have "last ((P0, s) # xs) = ((P, sa) # xs) ! length xs"
      by (simp add: `P0 = P \<and> P1 = Q \<and> s = sa \<and> zs = zsa` last_length)
    then have "zs = (map (lift_catch Q) xs)@((Skip,snd(last ((P0, s)#xs)))#ys)"
      using `P0 = P \<and> P1 = Q \<and> s = sa \<and> zs = zsa` `zs = map (lift_catch P1) xs @ ((Skip,snd(last ((P0, s)#xs)))#ys)` 
      by force    
    then have "(\<exists>xs s' s''. ((n,\<Gamma>,(P, s)#xs) \<in> cptn_mod_nest_call  \<and> 
             ((zs=(map (lift_catch Q) xs) \<or>
             ((fst(((P, s)#xs)!length xs)=Throw \<and>
               snd(last ((P, s)#xs)) = Normal s' \<and>  s=Normal s''\<and>
               (\<exists>ys. (n,\<Gamma>,(Q, snd(((P, s)#xs)!length xs))#ys) \<in> cptn_mod_nest_call \<and> 
                zs=(map (lift_catch Q) xs)@((Q, snd(((P, s)#xs)!length xs))#ys)))) \<or>
                (\<exists>ys. ((fst(((P, s)#xs)!length xs)=Skip \<and> (n,\<Gamma>,(Skip,snd(last ((P, s)#xs)))#ys) \<in> cptn_mod_nest_call \<and>                 
                 zs=(map (lift_catch Q) xs)@((Skip,snd(last ((P0, s)#xs)))#ys))))))))"
    using P0cptn  `P0 = P \<and> P1 = Q \<and> s = sa \<and> zs = zsa`  last  CptnModNestCatch2.hyps(4) by blast 
   } 
   thus ?thesis by auto
  qed
next
  case (CptnModNestCatch3 n \<Gamma> P0 s xs s' P1 ys zs)
  from CptnModNestCatch3.hyps(3)  
  have last:"fst (((P0, Normal s) # xs) ! length xs) = Throw" 
       by (simp add: last_length) 
  from CptnModNestCatch3.hyps(4) 
  have lastnormal:"snd (last ((P0, Normal s) # xs)) = Normal s'"
      by (simp add: last_length)
  have P0cptn:"(n,\<Gamma>, (P0, Normal s) # xs) \<in> cptn_mod_nest_call" by fact
  from CptnModNestCatch3.hyps(5) 
    have P1cptn:"(n,\<Gamma>, (P1, snd (((P0, Normal s) # xs) ! length xs)) # ys) \<in> cptn_mod_nest_call"
      by (simp add: last_length)          
  then have "zs = map (lift_catch P1) xs @ (P1, snd (last ((P0, Normal s) # xs))) # ys" 
    by (simp add:CptnModNestCatch3.hyps)
  show ?case
  proof -{
    fix sa P Q zsa    
    assume eq:"(Catch P0 P1, Normal s) # zs = (Catch P Q, Normal sa) # zsa"
    then have "P0 =P \<and> P1 = Q \<and> Normal s= Normal sa \<and> zs=zsa" by auto     
    have "last ((P0, Normal s) # xs) = ((P, Normal sa) # xs) ! length xs"
      by (simp add: `P0 = P \<and> P1 = Q \<and> Normal s = Normal sa \<and> zs = zsa` last_length)
    then have "zsa = map (lift_catch Q) xs @ (Q, snd (((P, Normal sa) # xs) ! length xs)) # ys"
      using `P0 = P \<and> P1 = Q \<and> Normal s = Normal sa \<and> zs = zsa` `zs = map (lift_catch P1) xs @ (P1, snd (last ((P0, Normal s) # xs))) # ys` by force
    then have "(n,\<Gamma>, (P, Normal s) # xs) \<in> cptn_mod_nest_call \<and> (fst(((P, Normal s)#xs)!length xs)=Throw \<and>
               snd(last ((P, Normal s)#xs)) = Normal s' \<and> 
              (\<exists>ys. (n,\<Gamma>,(Q, snd(((P, Normal s)#xs)!length xs))#ys) \<in> cptn_mod_nest_call \<and> 
              zs=(map (lift_catch Q) xs)@((Q, snd(((P, Normal s)#xs)!length xs))#ys)))" 
      using lastnormal P1cptn P0cptn `P0 = P \<and> P1 = Q \<and> Normal s = Normal sa \<and> zs = zsa` last 
       by auto    
    }note this [of P0 P1 s zs] thus ?thesis by blast qed
next
  case (CptnModNestEnv \<Gamma> P s t n xs)  
  then have step:"(n, \<Gamma>, (P, t) # xs) \<in> cptn_mod_nest_call" by auto  
  have step_e: "\<Gamma>\<turnstile>\<^sub>c (P, s) \<rightarrow>\<^sub>e (P, t)" using CptnModNestEnv by auto
  show ?case     
    proof (cases P)
      case (Catch P1 P2) 
      then have eq_P_Catch:"(P, t) # xs = (LanguageCon.com.Catch P1 P2, t) # xs" by auto      
      then  obtain xsa t' t'' where 
         p1:"(n,\<Gamma>, (P1, t) # xsa) \<in> cptn_mod_nest_call" and 
        p2:" (xs = map (lift_catch P2) xsa \<or>
            fst (((P1, t) # xsa) ! length xsa) = LanguageCon.com.Throw \<and>
            snd (last ((P1, t) # xsa)) = Normal t' \<and>
            t = Normal t'' \<and>
            (\<exists>ys. (n,\<Gamma>, (P2, snd (((P1, t) # xsa) ! length xsa)) # ys) \<in> cptn_mod_nest_call \<and>
              xs = map (lift_catch P2) xsa @ (P2, snd (((P1, t) # xsa) ! length xsa)) # ys) \<or>
                fst (((P1, t) # xsa) ! length xsa) = LanguageCon.com.Skip \<and>
                (\<exists>ys.(n,\<Gamma>,(Skip,snd(last ((P1, t)#xsa)))#ys) \<in> cptn_mod_nest_call \<and> 
                xs = map (lift_catch P2) xsa @
                ((LanguageCon.com.Skip, snd (last ((P1, t) # xsa)))#ys)))" 
        using CptnModNestEnv(3) by auto
      have all_step:"(n,\<Gamma>, (P1, s)#((P1, t) # xsa)) \<in> cptn_mod_nest_call"
        using p1 Env Env_n cptn_mod.CptnModEnv env_normal_s step_e
      proof -
        have "\<Gamma>\<turnstile>\<^sub>c (P1, s) \<rightarrow>\<^sub>e (P1, t)"
          using env_intro step_e by blast
        then show ?thesis
          by (simp add: cptn_mod_nest_call.CptnModNestEnv p1)
      qed
      show ?thesis using p2 
      proof  
        assume "xs = map (lift_catch P2) xsa"
        have "(P, t) # xs = map (lift_catch P2) ((P1, t) # xsa)"
          by (simp add: `xs = map (lift_catch P2) xsa` lift_catch_def local.Catch)
        thus ?thesis using all_step eq_P_Catch by fastforce
      next 
        assume 
         "fst (((P1, t) # xsa) ! length xsa) = LanguageCon.com.Throw \<and>
          snd (last ((P1, t) # xsa)) = Normal t' \<and>
          t = Normal t'' \<and>
          (\<exists>ys. (n,\<Gamma>, (P2, snd (((P1, t) # xsa) ! length xsa)) # ys) \<in> cptn_mod_nest_call \<and>
                xs =
                map (lift_catch P2) xsa @
                (P2, snd (((P1, t) # xsa) ! length xsa)) # ys) \<or>
                fst (((P1, t) # xsa) ! length xsa) = LanguageCon.com.Skip \<and>
           (\<exists>ys. (n,\<Gamma>,(Skip,snd(last ((P1, t)#xsa)))#ys) \<in> cptn_mod_nest_call \<and> 
            xs = map (lift_catch P2) xsa @
            ((LanguageCon.com.Skip, snd (last ((P1, t) # xsa)))#ys))"      
         then show ?thesis 
         proof
           assume 
            a1:"fst (((P1, t) # xsa) ! length xsa) = LanguageCon.com.Throw \<and>
             snd (last ((P1, t) # xsa)) = Normal t' \<and>
             t = Normal t'' \<and>
             (\<exists>ys. (n,\<Gamma>, (P2, snd (((P1, t) # xsa) ! length xsa)) # ys) \<in> cptn_mod_nest_call \<and>
                xs = map (lift_catch P2) xsa @
                       (P2, snd (((P1, t) # xsa) ! length xsa)) # ys)"
            then obtain ys where p2_exec:"(n,\<Gamma>, (P2, snd (((P1, t) # xsa) ! length xsa)) # ys) \<in> cptn_mod_nest_call \<and>
                xs = map (lift_catch P2) xsa @
                       (P2, snd (((P1, t) # xsa) ! length xsa)) # ys" 
            by fastforce
            from a1 obtain t1 where t_normal: "t=Normal t1" 
              using env_normal_s'_normal_s by blast
            have f1:"fst (((P1, s)#(P1, t) # xsa) ! length ((P1, t)#xsa)) = LanguageCon.com.Throw"
              using a1 by fastforce
             from a1 have last_normal: "snd (last ((P1, s)#(P1, t) # xsa)) = Normal t'"
               by fastforce 
             then have p2_long_exec: "(n,\<Gamma>, (P2, snd (((P1, s)#(P1, t) # xsa) ! length ((P1, s)#xsa))) # ys) \<in> cptn_mod_nest_call \<and>
                (P, t)#xs = map (lift_catch P2) ((P1, t) # xsa) @
                       (P2, snd (((P1, s)#(P1, t) # xsa) ! length ((P1, s)#xsa))) # ys" using p2_exec 
                by (simp add: lift_catch_def local.Catch)                  
             thus ?thesis using  a1 f1 last_normal all_step eq_P_Catch 
               by (clarify, metis (no_types) list.size(4) not_step_c_env  step_e)            
           next
           assume 
            as1:"fst (((P1, t) # xsa) ! length xsa) = LanguageCon.com.Skip \<and>
           (\<exists>ys. (n,\<Gamma>,(Skip,snd(last ((P1, t)#xsa)))#ys) \<in> cptn_mod_nest_call \<and> 
            xs = map (lift_catch P2) xsa @
            ((LanguageCon.com.Skip, snd (last ((P1, t) # xsa)))#ys))"               
            then obtain ys where p1:"(n,\<Gamma>,(Skip,snd(last ((P1, t)#xsa)))#ys) \<in> cptn_mod_nest_call \<and> 
                         (P, t)#xs = map (lift_catch P2) ((P1, t) # xsa) @
                          ((LanguageCon.com.Skip, snd (last ((P1, t) # xsa)))#ys)"
            proof -
              assume a1: "\<And>ys. (n,\<Gamma>, (LanguageCon.com.Skip, snd (last ((P1, t) # xsa))) # ys) \<in> cptn_mod_nest_call \<and> 
                         (P, t) # xs = map (lift_catch P2) ((P1, t) # xsa) @ 
                         (LanguageCon.com.Skip, snd (last ((P1, t) # xsa))) # ys \<Longrightarrow> 
                         thesis"
              have "(LanguageCon.com.Catch P1 P2, t) # map (lift_catch P2) xsa = map (lift_catch P2) ((P1, t) # xsa)"
                by (simp add: lift_catch_def)
              thus ?thesis
                using a1 as1 eq_P_Catch by moura
            qed            
            from as1 have p2: "fst (((P1, s)#(P1, t) # xsa) ! length ((P1, t) #xsa)) = LanguageCon.com.Skip"
                 by fastforce                              
            thus ?thesis using p1 all_step eq_P_Catch by fastforce
          qed
      qed
    qed (auto)
qed(force+)


definition seq_cond_nest
where
"seq_cond_nest zs Q xs P s s'' s' \<Gamma> n \<equiv> (zs=(map (lift Q) xs) \<or>
             ((fst(((P, s)#xs)!length xs)=Skip \<and> 
               (\<exists>ys. (n,\<Gamma>,(Q, snd(((P, s)#xs)!length xs))#ys) \<in> cptn_mod_nest_call \<and> 
                zs=(map (lift (Q)) xs)@((Q, snd(((P, s)#xs)!length xs))#ys)))) \<or>
             ((fst(((P, s)#xs)!length xs)=Throw \<and> 
                 snd(last ((P, s)#xs)) = Normal s' \<and>  s=Normal s''\<and>
                 (\<exists>ys.  (n,\<Gamma>,(Throw,Normal s')#ys) \<in> cptn_mod_nest_call \<and>
                      zs=(map (lift Q) xs)@((Throw,Normal s')#ys)))))
"

lemma Seq_P_Not_finish:
 assumes
   a0:"zs = map (lift Q) xs" and
   a1:"(m, \<Gamma>,(LanguageCon.com.Seq P Q, s) # zs) \<in> cptn_mod_nest_call" and
   a2:"seq_cond_nest zs Q xs' P s s'' s' \<Gamma> m" 
shows "xs=xs'"
using a2 unfolding seq_cond_nest_def 
proof
  assume "zs= map (lift Q) xs'"
  then have  "map (lift Q) xs' = 
              map (lift Q) xs" using a0 by auto 
  thus ?thesis using map_lift_eq_xs_xs' by fastforce
next
  assume 
    ass:"fst (((P, s) # xs') ! length xs') = LanguageCon.com.Skip \<and>
         (\<exists>ys. (m, \<Gamma>, (Q, snd (((P, s) # xs') ! length xs')) # ys) \<in> cptn_mod_nest_call \<and>
         zs = map (lift Q) xs' @ (Q, snd (((P, s) # xs') ! length xs')) # ys) \<or>
         fst (((P, s) # xs') ! length xs') = LanguageCon.com.Throw \<and>
         snd (last ((P, s) # xs')) = Normal s' \<and>
         s = Normal s'' \<and>
         (\<exists>ys. (m, \<Gamma>, (LanguageCon.com.Throw, Normal s') # ys) \<in> cptn_mod_nest_call \<and>
         zs = map (lift Q) xs' @ (LanguageCon.com.Throw, Normal s') # ys)"
   {assume 
     ass:"fst (((P, s) # xs') ! length xs') = LanguageCon.com.Skip \<and>
        (\<exists>ys. (m, \<Gamma>, (Q, snd (((P, s) # xs') ! length xs')) # ys) \<in> cptn_mod_nest_call \<and>
         zs = map (lift Q) xs' @ (Q, snd (((P, s) # xs') ! length xs')) # ys)"
      then obtain ys where 
         zs:"zs = map (lift Q) xs' @ (Q, snd (((P, s) # xs') ! length xs')) # ys" 
             by auto 
      then have zs_while:"fst (zs!(length (map (lift Q) xs'))) =
                   Q"  by (metis fstI nth_append_length) 
      have "length zs = length (map (lift Q) xs' @
         (Q, snd (((P, s) # xs') ! length xs')) # ys)" 
          using zs by auto
      then have "(length (map (lift Q) xs')) < 
                  length zs" by auto       
      then have ?thesis using a0 zs_while map_lift_all_seq
         using seq_and_if_not_eq(4) by fastforce     
   }note l = this
   {assume ass:"fst (((P, s) # xs') ! length xs') = LanguageCon.com.Throw \<and>
         snd (last ((P, s) # xs')) = Normal s' \<and>
         s = Normal s'' \<and>
         (\<exists>ys. (m, \<Gamma>, (LanguageCon.com.Throw, Normal s') # ys) \<in> cptn_mod_nest_call \<and>
         zs = map (lift Q) xs' @ (LanguageCon.com.Throw, Normal s') # ys)"
      then obtain ys where 
            zs:"zs = map (lift Q) xs' @ 
                 (LanguageCon.com.Throw, Normal s') # ys" by auto
      then have zs_while:
          "fst (zs!(length (map (lift Q) xs'))) = Throw"  by (metis fstI nth_append_length) 
       have "length zs = length (map (lift Q) xs' @(LanguageCon.com.Throw, Normal s') # ys)" 
           using zs by auto
       then have "(length (map (lift Q) xs')) < 
                  length zs" by auto       
       then have ?thesis using a0 zs_while map_lift_all_seq
         using seq_and_if_not_eq(4) by fastforce
   } thus ?thesis using l ass by auto
qed

lemma Seq_P_Ends_Normal:
 assumes
   a0:"zs = map (lift Q) xs @ (Q, snd (last ((P, s) # xs))) # ys" and
   a0':"fst (last ((P, s) # xs)) = Skip" and
   a1:"(m, \<Gamma>,(LanguageCon.com.Seq P Q, s) # zs) \<in> cptn_mod_nest_call" and
   a2:"seq_cond_nest zs Q xs' P s s'' s' \<Gamma> m" 
shows "xs=xs' \<and> (m,\<Gamma>,(Q, snd(((P, s)#xs)!length xs))#ys) \<in> cptn_mod_nest_call"
using a2 unfolding seq_cond_nest_def 
proof
  assume ass:"zs= map (lift Q) xs'"
  then have  "map (lift Q) xs' = 
              map (lift Q) xs @ (Q, snd (last ((P, s) # xs))) # ys" using a0 by auto 
  then have zs_while:"fst (zs!(length (map (lift Q) xs))) = Q"  
    by (metis a0 fstI nth_append_length) 
  also have "length zs = 
             length (map (lift Q) xs @ (Q, snd (last ((P, s) # xs))) # ys)" 
    using a0 by auto
  then have "(length (map (lift Q) xs)) < length zs" by auto       
  then show ?thesis using ass zs_while map_lift_all_seq
           using seq_and_if_not_eq(4)
  by metis   
next
  assume 
    ass:"fst (((P, s) # xs') ! length xs') = LanguageCon.com.Skip \<and>
         (\<exists>ys. (m, \<Gamma>, (Q, snd (((P, s) # xs') ! length xs')) # ys) \<in> cptn_mod_nest_call \<and>
         zs = map (lift Q) xs' @ (Q, snd (((P, s) # xs') ! length xs')) # ys) \<or>
         fst (((P, s) # xs') ! length xs') = LanguageCon.com.Throw \<and>
         snd (last ((P, s) # xs')) = Normal s' \<and>
         s = Normal s'' \<and>
         (\<exists>ys. (m, \<Gamma>, (LanguageCon.com.Throw, Normal s') # ys) \<in> cptn_mod_nest_call \<and>
         zs = map (lift Q) xs' @ (LanguageCon.com.Throw, Normal s') # ys)"
   {assume 
     ass:"fst (((P, s) # xs') ! length xs') = LanguageCon.com.Skip \<and>
        (\<exists>ys. (m, \<Gamma>, (Q, snd (((P, s) # xs') ! length xs')) # ys) \<in> cptn_mod_nest_call \<and>
         zs = map (lift Q) xs' @ (Q, snd (((P, s) # xs') ! length xs')) # ys)"
      then obtain ys' where 
         zs:"zs = map (lift Q) xs' @ (Q, snd (((P, s) # xs') ! length xs')) # ys' \<and>
             (m, \<Gamma>, (Q, snd (((P, s) # xs') ! length xs')) # ys') \<in> cptn_mod_nest_call" 
             by auto 
      then have ?thesis
        using  map_lift_some_eq[of Q xs Q _ ys xs' Q _ ys'] 
               zs  a0 seq_and_if_not_eq(4)[of Q] 
        by auto               
   }note l = this
   {assume ass:"fst (((P, s) # xs') ! length xs') = LanguageCon.com.Throw \<and>
         snd (last ((P, s) # xs')) = Normal s' \<and>
         s = Normal s'' \<and>
         (\<exists>ys. (m, \<Gamma>, (LanguageCon.com.Throw, Normal s') # ys) \<in> cptn_mod_nest_call \<and>
         zs = map (lift Q) xs' @ (LanguageCon.com.Throw, Normal s') # ys)"
      then obtain ys' where 
         zs:"zs = map (lift Q) xs' @ (LanguageCon.com.Throw, Normal s') # ys' \<and>
             (m, \<Gamma>, (LanguageCon.com.Throw, Normal s') # ys') \<in> cptn_mod_nest_call" 
         by auto
      then have zs_while:
          "fst (zs!(length (map (lift Q) xs'))) = Throw"  by (metis fstI nth_append_length)       
      have False
        by (metis (no_types) LanguageCon.com.distinct(17) 
              LanguageCon.com.distinct(71) 
              a0 a0' ass last_length
              map_lift_some_eq seq_and_if_not_eq(4) zs)
      then have ?thesis
        by metis
   } thus ?thesis using l ass by auto
qed

lemma Seq_P_Ends_Abort:
 assumes
   a0:"zs = map (lift Q) xs @ (Throw, Normal s') # ys" and
   a0':"fst (last ((P, Normal s) # xs)) = Throw" and
   a0'':"snd(last ((P, Normal s) # xs)) = Normal s'" and
   a1:"(m, \<Gamma>,(LanguageCon.com.Seq P Q, Normal s) # zs) \<in> cptn_mod_nest_call" and
   a2:"seq_cond_nest zs Q xs' P (Normal s) ns'' ns' \<Gamma> m" 
shows "xs=xs' \<and> (m,\<Gamma>,(Throw,Normal s')#ys) \<in> cptn_mod_nest_call"
using a2 unfolding seq_cond_nest_def 
proof
  assume ass:"zs= map (lift Q) xs'"
  then have  "map (lift Q) xs' = 
              map (lift Q) xs @ (Throw, Normal s') # ys" using a0 by auto 
  then have zs_while:"fst (zs!(length (map (lift Q) xs))) = Throw"  
    by (metis a0  fstI nth_append_length) 
  also have "length zs = 
             length (map (lift Q) xs @ (Throw, Normal s') # ys)" 
    using a0 by auto
  then have "(length (map (lift Q) xs)) < length zs" by auto       
  then show ?thesis using ass zs_while map_lift_all_seq    
    by (metis (no_types) LanguageCon.com.simps(82))    
next
  assume 
    ass:"fst (((P, Normal s) # xs') ! length xs') = LanguageCon.com.Skip \<and>
         (\<exists>ys. (m, \<Gamma>, (Q, snd (((P, Normal s) # xs') ! length xs')) # ys)
          \<in> cptn_mod_nest_call \<and>
         zs = map (lift Q) xs' @
              (Q, snd (((P, Normal s) # xs') ! length xs')) # ys) \<or>
         fst (((P, Normal s) # xs') ! length xs') = LanguageCon.com.Throw \<and>
         snd (last ((P, Normal s) # xs')) = Normal ns' \<and>
         Normal s = Normal ns'' \<and>
         (\<exists>ys. (m, \<Gamma>, (LanguageCon.com.Throw, Normal ns') # ys) \<in> cptn_mod_nest_call \<and>
            zs = map (lift Q) xs' @ (LanguageCon.com.Throw, Normal ns') # ys)"
   {assume 
     ass:"fst (((P, Normal s) # xs') ! length xs') = LanguageCon.com.Skip \<and>
         (\<exists>ys. (m, \<Gamma>, (Q, snd (((P, Normal s) # xs') ! length xs')) # ys)
          \<in> cptn_mod_nest_call \<and>
         zs = map (lift Q) xs' @
              (Q, snd (((P, Normal s) # xs') ! length xs')) # ys)"
      then obtain ys' where 
         zs:"(m, \<Gamma>, (Q, snd (((P, Normal s) # xs') ! length xs')) # ys')
               \<in> cptn_mod_nest_call \<and>
            zs = map (lift Q) xs' @ 
              (Q, snd (((P, Normal s) # xs') ! length xs')) # ys'" 
             by auto 
      then have ?thesis
        using a0 seq_and_if_not_eq(4)[of Q]
         by (metis LanguageCon.com.distinct(17) LanguageCon.com.distinct(71) 
             a0' ass last_length map_lift_some_eq)                        
   }note l = this
   {assume ass:"fst (((P, Normal s) # xs') ! length xs') = LanguageCon.com.Throw \<and>
         snd (last ((P, Normal s) # xs')) = Normal ns' \<and>
         Normal s = Normal ns'' \<and>
         (\<exists>ys. (m, \<Gamma>, (LanguageCon.com.Throw, Normal ns') # ys) \<in> cptn_mod_nest_call \<and>
            zs = map (lift Q) xs' @ (LanguageCon.com.Throw, Normal ns') # ys)"
      then obtain ys' where 
         zs:"(m, \<Gamma>, (LanguageCon.com.Throw, Normal ns') # ys') \<in> cptn_mod_nest_call \<and>
            zs = map (lift Q) xs' @ (LanguageCon.com.Throw, Normal ns') # ys'" 
         by auto
      then have zs_while:
          "fst (zs!(length (map (lift Q) xs'))) = Throw"  
        by (metis fstI nth_append_length)             
      then have ?thesis using a0 ass map_lift_some_eq by blast        
   } thus ?thesis using l ass by auto
qed

lemma Catch_P_Not_finish:
 assumes
   a0:"zs = map (lift_catch Q) xs" and   
   a1:"catch_cond_nest zs Q xs' P s s'' s' \<Gamma> m" 
shows "xs=xs'"
using a1 unfolding catch_cond_nest_def 
proof
  assume "zs= map (lift_catch Q) xs'"
  then have  "map (lift_catch Q) xs' = 
              map (lift_catch Q) xs" using a0 by auto 
  thus ?thesis using map_lift_catch_eq_xs_xs' by fastforce
next
  assume 
    ass:"
         fst (((P, s) # xs') ! length xs') = LanguageCon.com.Throw \<and>
         snd (last ((P, s) # xs')) = Normal s' \<and>
         s = Normal s'' \<and>
         (\<exists>ys. (m, \<Gamma>, (Q, snd (((P, s) # xs') ! length xs')) # ys) \<in> cptn_mod_nest_call \<and>
         zs = map (lift_catch Q) xs' @ (Q, snd (((P, s) # xs') ! length xs')) # ys) \<or>
         fst (((P, s) # xs') ! length xs') = LanguageCon.com.Skip \<and>
         (\<exists>ys. (m, \<Gamma>, (LanguageCon.com.Skip, snd (last ((P, s) # xs'))) # ys) \<in> cptn_mod_nest_call \<and>
         zs = map (lift_catch Q) xs' @ (LanguageCon.com.Skip, snd (last ((P, s) # xs'))) # ys)"
   {assume 
     ass:"fst (((P, s) # xs') ! length xs') = LanguageCon.com.Skip \<and>
         (\<exists>ys. (m, \<Gamma>, (LanguageCon.com.Skip, snd (last ((P, s) # xs'))) # ys) \<in> cptn_mod_nest_call \<and>
         zs = map (lift_catch Q) xs' @ (LanguageCon.com.Skip, snd (last ((P, s) # xs'))) # ys)"
      then obtain ys where 
         zs:"(m, \<Gamma>, (LanguageCon.com.Skip, snd (last ((P, s) # xs'))) # ys) \<in> cptn_mod_nest_call \<and>
            zs = map (lift_catch Q) xs' @ (LanguageCon.com.Skip, snd (last ((P, s) # xs'))) # ys" 
             by auto 
      then have zs_while:"fst (zs!(length (map (lift_catch Q) xs'))) = Skip "  
        by (metis fstI nth_append_length) 
      have "length zs = length (map (lift Q) xs' @
         (Q, snd (((P, s) # xs') ! length xs')) # ys)" 
          using zs by auto
      then have "(length (map (lift Q) xs')) < 
                  length zs" by auto       
      then have ?thesis using a0 zs_while map_lift_catch_all_catch
         using seq_and_if_not_eq(12) by fastforce     
   }note l = this
   {assume ass:"fst (((P, s) # xs') ! length xs') = LanguageCon.com.Throw \<and>
         snd (last ((P, s) # xs')) = Normal s' \<and>
         s = Normal s'' \<and>
         (\<exists>ys. (m, \<Gamma>, (Q, snd (((P, s) # xs') ! length xs')) # ys) \<in> cptn_mod_nest_call \<and>
         zs = map (lift_catch Q) xs' @ (Q, snd (((P, s) # xs') ! length xs')) # ys)"
      then obtain ys where 
            zs:"zs = map (lift_catch Q) xs' @ (Q, snd (((P, s) # xs') ! length xs')) # ys" by auto
      then have zs_while:
        "fst (zs!(length (map (lift Q) xs'))) = Q"
         by (metis (no_types) eq_fst_iff length_map nth_append_length zs) 
       have "length zs = length (map (lift Q) xs' @(LanguageCon.com.Throw, Normal s') # ys)" 
           using zs by auto
       then have "(length (map (lift Q) xs')) < 
                  length zs" by auto       
       then have ?thesis using a0 zs_while map_lift_catch_all_catch
         by fastforce
   } thus ?thesis using l ass by auto
qed

lemma Catch_P_Ends_Normal:
 assumes
   a0:"zs = map (lift_catch Q) xs @ (Q, snd (last ((P, Normal s) # xs))) # ys" and
   a0':"fst (last ((P, Normal s) # xs)) = Throw" and
   a0'':"snd (last ((P, Normal s) # xs)) = Normal s'" and
   a1:"catch_cond_nest zs Q xs' P (Normal s) ns'' ns' \<Gamma> m" 
shows "xs=xs' \<and> (m,\<Gamma>,(Q, snd(((P, Normal s)#xs)!length xs))#ys) \<in> cptn_mod_nest_call"
using a1 unfolding catch_cond_nest_def 
proof
  assume ass:"zs= map (lift_catch Q) xs'"
  then have  "map (lift_catch Q) xs' = 
              map (lift_catch Q) xs @ (Q, snd (last ((P, Normal s) # xs))) # ys" using a0 by auto 
  then have zs_while:"fst (zs!(length (map (lift_catch Q) xs))) = Q"
    by (metis a0 fstI nth_append_length)      
  also have "length zs = 
             length (map (lift_catch Q) xs @ (Q, snd (last ((P, Normal s) # xs))) # ys)" 
    using a0 by auto
  then have "(length (map (lift_catch Q) xs)) < length zs" by auto       
  then show ?thesis using ass zs_while map_lift_catch_all_catch
           using seq_and_if_not_eq(12)
  by metis
next
  assume 
    ass:"fst (((P, Normal s) # xs') ! length xs') = LanguageCon.com.Throw \<and>
         snd (last ((P, Normal s) # xs')) = Normal ns' \<and>
         Normal s = Normal ns'' \<and>
         (\<exists>ys. (m, \<Gamma>, (Q, snd (((P, Normal s) # xs') ! length xs')) # ys) \<in> cptn_mod_nest_call \<and>
         zs = map (lift_catch Q) xs' @ (Q, snd (((P, Normal s) # xs') ! length xs')) # ys) \<or>
         fst (((P, Normal s) # xs') ! length xs') = LanguageCon.com.Skip \<and>
         (\<exists>ys. (m, \<Gamma>, (LanguageCon.com.Skip, snd (last ((P, Normal s) # xs'))) # ys) \<in> cptn_mod_nest_call \<and>
         zs = map (lift_catch Q) xs' @ (LanguageCon.com.Skip, snd (last ((P, Normal s) # xs'))) # ys)"
   {assume 
     ass:"fst (((P, Normal s) # xs') ! length xs') = LanguageCon.com.Skip \<and>
         (\<exists>ys. (m, \<Gamma>, (LanguageCon.com.Skip, snd (last ((P, Normal s) # xs'))) # ys) \<in> cptn_mod_nest_call \<and>
         zs = map (lift_catch Q) xs' @ (LanguageCon.com.Skip, snd (last ((P, Normal s) # xs'))) # ys)"
      then obtain ys' where 
         zs:"(m, \<Gamma>, (LanguageCon.com.Skip, snd (last ((P, Normal s) # xs'))) # ys') \<in> cptn_mod_nest_call \<and>
             zs = map (lift_catch Q) xs' @ (LanguageCon.com.Skip, snd (last ((P, Normal s) # xs'))) # ys'" 
             by auto 
      then have ?thesis
        using  map_lift_catch_some_eq[of Q xs Q _ ys xs' Skip _ ys'] 
               zs  a0 seq_and_if_not_eq(12)[of Q]
        by (metis LanguageCon.com.distinct(17) LanguageCon.com.distinct(19) a0' ass last_length)                        
   }note l = this
   {assume ass:"fst (((P, Normal s) # xs') ! length xs') = LanguageCon.com.Throw \<and>
                snd (last ((P, Normal s) # xs')) = Normal ns' \<and>
                Normal s = Normal ns'' \<and>
                (\<exists>ys. (m, \<Gamma>, (Q, snd (((P, Normal s) # xs') ! length xs')) # ys) \<in> cptn_mod_nest_call \<and>
                zs = map (lift_catch Q) xs' @ (Q, snd (((P, Normal s) # xs') ! length xs')) # ys)"
      then obtain ys' where 
         zs:"(m, \<Gamma>, (Q, snd (((P, Normal s) # xs') ! length xs')) # ys') \<in> cptn_mod_nest_call \<and>
                zs = map (lift_catch Q) xs' @ (Q, snd (((P, Normal s) # xs') ! length xs')) # ys'" 
         by auto
      then have zs_while:
          "fst (zs!(length (map (lift_catch Q) xs'))) = Q"  by (metis fstI nth_append_length)       

      then have ?thesis 
        using LanguageCon.com.distinct(17) LanguageCon.com.distinct(71) 
            a0 a0' ass last_length map_lift_catch_some_eq[of Q xs Q _ ys xs' Q _ ys']  
            seq_and_if_not_eq(12) zs
        by blast        
   } thus ?thesis using l ass by auto
qed
 
lemma Catch_P_Ends_Skip:
 assumes
   a0:"zs = map (lift_catch Q) xs @ (Skip, snd (last ((P, s) # xs))) # ys" and
   a0':"fst (last ((P,s) # xs)) = Skip" and
   a1:"catch_cond_nest zs Q xs' P s ns'' ns' \<Gamma> m" 
shows "xs=xs' \<and> (m,\<Gamma>,(Skip,snd(last ((P,s) # xs)))#ys) \<in> cptn_mod_nest_call"
using a1 unfolding catch_cond_nest_def 
proof
  assume ass:"zs= map (lift_catch Q) xs'"
  then have  "map (lift_catch Q) xs' = 
              map (lift_catch Q) xs @ (Skip, snd (last ((P, s) # xs))) # ys" using a0 by auto 
  then have zs_while:"fst (zs!(length (map (lift_catch Q) xs))) = Skip"  
    by (metis a0  fstI nth_append_length) 
  also have "length zs = 
             length (map (lift_catch Q) xs @ (Skip, snd (last ((P, s) # xs))) # ys)" 
    using a0 by auto
  then have "(length (map (lift_catch Q) xs)) < length zs" by auto       
  then show ?thesis using ass zs_while map_lift_catch_all_catch
    by (metis LanguageCon.com.distinct(19))    
next
  assume 
    ass:"fst (((P, s) # xs') ! length xs') = LanguageCon.com.Throw \<and>
         snd (last ((P, s) # xs')) = Normal ns' \<and>
         s = Normal ns'' \<and>
         (\<exists>ys. (m, \<Gamma>, (Q, snd (((P, s) # xs') ! length xs')) # ys) \<in> cptn_mod_nest_call \<and>
         zs = map (lift_catch Q) xs' @ (Q, snd (((P, s) # xs') ! length xs')) # ys) \<or>
         fst (((P, s) # xs') ! length xs') = LanguageCon.com.Skip \<and>
         (\<exists>ys. (m, \<Gamma>, (LanguageCon.com.Skip, snd (last ((P, s) # xs'))) # ys) \<in> cptn_mod_nest_call \<and>
         zs = map (lift_catch Q) xs' @ (LanguageCon.com.Skip, snd (last ((P, s) # xs'))) # ys)"
   {assume 
     ass:"fst (((P, s) # xs') ! length xs') = LanguageCon.com.Skip \<and>
         (\<exists>ys. (m, \<Gamma>, (LanguageCon.com.Skip, snd (last ((P, s) # xs'))) # ys) \<in> cptn_mod_nest_call \<and>
         zs = map (lift_catch Q) xs' @ (LanguageCon.com.Skip, snd (last ((P, s) # xs'))) # ys)"
      then obtain ys' where 
         zs:"(m, \<Gamma>, (LanguageCon.com.Skip, snd (last ((P, s) # xs'))) # ys') \<in> cptn_mod_nest_call \<and>
             zs = map (lift_catch Q) xs' @ (LanguageCon.com.Skip, snd (last ((P, s) # xs'))) # ys'" 
             by auto 
      then have ?thesis
        using a0 seq_and_if_not_eq(12)[of Q] a0' ass last_length map_lift_catch_some_eq
        using LanguageCon.com.distinct(19) by blast                
   }note l = this
   {assume ass:"fst (((P, s) # xs') ! length xs') = LanguageCon.com.Throw \<and>
         snd (last ((P, s) # xs')) = Normal ns' \<and>
         s = Normal ns'' \<and>
         (\<exists>ys. (m, \<Gamma>, (Q, snd (((P, s) # xs') ! length xs')) # ys) \<in> cptn_mod_nest_call \<and>
         zs = map (lift_catch Q) xs' @ (Q, snd (((P, s) # xs') ! length xs')) # ys)"
      then obtain ys' where 
         zs:"(m, \<Gamma>, (Q, snd (((P, s) # xs') ! length xs')) # ys') \<in> cptn_mod_nest_call \<and>
         zs = map (lift_catch Q) xs' @ (Q, snd (((P, s) # xs') ! length xs')) # ys'" 
         by auto
      then have zs_while:
          "fst (zs!(length (map (lift_catch Q) xs'))) = Q"  
        by (metis fstI nth_append_length)             
      then have ?thesis 
        using a0 seq_and_if_not_eq(12)[of Q] a0' ass last_length map_lift_catch_some_eq
        by (metis LanguageCon.com.distinct(17) LanguageCon.com.distinct(19))               
   } thus ?thesis using l ass by auto
qed


lemma div_seq_nest: 
  assumes cptn_m:"(n,\<Gamma>,list) \<in> cptn_mod_nest_call"
  shows "(\<forall>s P Q zs. list=(Seq P Q, s)#zs \<longrightarrow>
       (\<exists>xs s' s''. 
          (n,\<Gamma>,(P, s)#xs) \<in> cptn_mod_nest_call  \<and> 
             seq_cond_nest zs Q xs P s s'' s' \<Gamma> n))  
            "
unfolding seq_cond_nest_def
using cptn_m
proof (induct rule: cptn_mod_nest_call.induct)
  case (CptnModNestOne \<Gamma> P s)
  thus ?case using cptn_mod_nest_call.CptnModNestOne 
   by blast
next
  case (CptnModNestSkip  \<Gamma> P s t n xs) 
  from CptnModNestSkip.hyps
  have step: "\<Gamma>\<turnstile>\<^sub>c (P, toSeq s) \<rightarrow> (Skip, toSeq t)" by auto
  from CptnModNestSkip.hyps
  have noskip: "~(P=Skip)" using stepc_elim_cases(1) by blast  
  have x: "\<forall>c c1 c2. redex c = Seq c1 c2 \<Longrightarrow> False"
          using redex_not_Seq by blast
  from CptnModNestSkip.hyps
  have in_cptn_mod: "(n,\<Gamma>, (Skip, t) # xs) \<in> cptn_mod_nest_call" by auto  
  then show ?case using CptnModNestSkip.hyps(2) SmallStepCon.redex_not_Seq by blast
next
  case (CptnModNestThrow  \<Gamma> P s t xs)
  from CptnModNestThrow.hyps
  have step: "\<Gamma>\<turnstile>\<^sub>c (P, toSeq s) \<rightarrow> (Throw, toSeq t)" by auto 
  moreover from CptnModNestThrow.hyps 
  have no_seq: "\<forall>p1 p2. \<not>(P=Seq p1 p2)" using CptnModNestThrow.hyps(2) redex_not_Seq by auto
  ultimately show ?case by auto   
next 
  case (CptnModNestCondT \<Gamma> P0 s ys b P1)
  thus ?case by auto
next
  case (CptnModNestCondF \<Gamma> P0 s ys b P1)
  thus ?case by auto
next
  case (CptnModNestSeq1 n \<Gamma> P0 s xs zs P1) thus ?case 
    by blast   
next 
  case (CptnModNestSeq2 n \<Gamma> P0 s xs P1 ys zs) 
  from CptnModNestSeq2.hyps(3) last_length have last:"fst (((P0, s) # xs) ! length xs) = Skip" 
       by (simp add: last_length) 
  have P0cptn:"(n,\<Gamma>, (P0, s) # xs) \<in> cptn_mod_nest_call" by fact
  from CptnModNestSeq2.hyps(4) have P1cptn:"(n,\<Gamma>, (P1, snd (((P0, s) # xs) ! length xs)) # ys) \<in> cptn_mod_nest_call"
      by (simp add: last_length)          
  then have "zs = map (lift P1) xs @ (P1, snd (last ((P0, s) # xs))) # ys" by (simp add:CptnModNestSeq2.hyps)
  show ?case
    by (metis CptnModNestSeq2.hyps(3) CptnModNestSeq2.hyps(4) CptnModNestSeq2.hyps(6) 
              LanguageCon.com.inject(3) P0cptn fst_conv last_length list.sel(3) 
              nth_Cons_0 snd_conv)    
next
  case (CptnModNestSeq3 n \<Gamma> P0 s xs s' ys zs P1) 
  from CptnModNestSeq3.hyps(3) 
  have last:"fst (((P0, Normal s) # xs) ! length xs) = Throw" 
       by (simp add: last_length) 
  have P0cptn:"(n,\<Gamma>, (P0, Normal s) # xs) \<in> cptn_mod_nest_call" by fact
  from CptnModNestSeq3.hyps(4) 
  have lastnormal:"snd (last ((P0, Normal s) # xs)) = Normal s'"
      by (simp add: last_length)          
  then have "zs = map (lift P1) xs @ ((Throw, Normal s')#ys)" by (simp add:CptnModNestSeq3.hyps)
  show ?case
    by (metis CptnModNestSeq3.hyps(3) CptnModNestSeq3.hyps(5) CptnModNestSeq3.hyps(7)
       LanguageCon.com.inject(3) P0cptn 
      fst_conv last_length lastnormal list.inject snd_conv)         
next 
  case (CptnModNestEnv  \<Gamma> P s t n zs) 
  then have step:"(n,\<Gamma>, (P, t) # zs) \<in> cptn_mod_nest_call" by auto
  have step_e: "\<Gamma>\<turnstile>\<^sub>c (P, s) \<rightarrow>\<^sub>e (P, t)" using CptnModNestEnv by auto  
  show ?case     
    proof (cases P)
      case (Seq P1 P2) 
      then have eq_P:"(P, t) # zs = (LanguageCon.com.Seq P1 P2, t) # zs" by auto      
      then  obtain xs t' t'' where 
         p1:"(n,\<Gamma>, (P1, t) # xs) \<in> cptn_mod_nest_call" and p2:"
     (zs = map (lift P2) xs \<or>
      fst (((P1, t) # xs) ! length xs) = LanguageCon.com.Skip \<and>      
      (\<exists>ys. (n,\<Gamma>, (P2, snd (((P1, t) # xs) ! length xs)) # ys) \<in> cptn_mod_nest_call \<and>
            zs =
            map (lift P2) xs @
            (P2, snd (((P1, t) # xs) ! length xs)) # ys) \<or>
      fst (((P1, t) # xs) ! length xs) = LanguageCon.com.Throw \<and>
      snd (last ((P1, t) # xs)) = Normal t' \<and>
      t = Normal t'' \<and> (\<exists>ys. (n,\<Gamma>,(Throw,Normal t')#ys) \<in> cptn_mod_nest_call \<and> 
      zs =
      map (lift P2) xs @
      ((LanguageCon.com.Throw, Normal t')#ys))) " 
        using CptnModNestEnv(3) by auto
      have all_step:"(n,\<Gamma>, (P1, s)#((P1, t) # xs)) \<in> cptn_mod_nest_call" 
        using p1 cptn_mod_nest_call.CptnModNestEnv step_e
        by (metis (no_types, lifting) env_intro)
      show ?thesis using p2 
      proof  
        assume "zs = map (lift P2) xs"
        have "(P, t) # zs = map (lift P2) ((P1, t) # xs)"
          by (simp add: `zs = map (lift P2) xs` lift_def local.Seq)
        thus ?thesis using all_step eq_P by fastforce
      next 
        assume 
         "fst (((P1, t) # xs) ! length xs) = LanguageCon.com.Skip \<and>      
         (\<exists>ys. (n,\<Gamma>, (P2, snd (((P1, t) # xs) ! length xs)) # ys) \<in> cptn_mod_nest_call \<and>
            zs = map (lift P2) xs @ (P2, snd (((P1, t) # xs) ! length xs)) # ys) \<or>
          fst (((P1, t) # xs) ! length xs) = LanguageCon.com.Throw \<and>
           snd (last ((P1, t) # xs)) = Normal t' \<and>
           t = Normal t'' \<and> (\<exists>ys. (n,\<Gamma>,(Throw,Normal t')#ys) \<in> cptn_mod_nest_call \<and> 
           zs = map (lift P2) xs @ ((LanguageCon.com.Throw, Normal t')#ys))"
         then show ?thesis 
         proof
           assume 
            a1:"fst (((P1, t) # xs) ! length xs) = LanguageCon.com.Skip \<and>      
               (\<exists>ys. (n,\<Gamma>, (P2, snd (((P1, t) # xs) ! length xs)) # ys) \<in> cptn_mod_nest_call \<and>
               zs = map (lift P2) xs @ (P2, snd (((P1, t) # xs) ! length xs)) # ys)"
               from a1 obtain ys where 
                   p2_exec:"(n,\<Gamma>, (P2, snd (((P1, t) # xs) ! length xs)) # ys) \<in> cptn_mod_nest_call \<and>
                       zs = map (lift P2) xs @
                       (P2, snd (((P1, t) # xs) ! length xs)) # ys" 
                by auto 
               have f1:"fst (((P1, s)#(P1, t) # xs) ! length ((P1, t)#xs)) = LanguageCon.com.Skip"
                 using a1 by fastforce             
               then have p2_long_exec: 
                 "(n,\<Gamma>, (P2, snd (((P1, s)#(P1, t) # xs) ! length ((P1, t)#xs))) # ys) \<in> cptn_mod_nest_call \<and>
                  (P, t)#zs = map (lift P2) ((P1, t) # xs) @
                       (P2, snd (((P1, s)#(P1, t) # xs) ! length ((P1, t)#xs))) # ys" 
             using p2_exec by (simp add: lift_def local.Seq)     
             thus ?thesis using a1 f1 all_step eq_P by blast            
           next
           assume 
            a1:"fst (((P1, t) # xs) ! length xs) = LanguageCon.com.Throw \<and>
            snd (last ((P1, t) # xs)) = Normal t' \<and> t = Normal t'' \<and> 
          (\<exists>ys. (n,\<Gamma>,(Throw,Normal t')#ys) \<in> cptn_mod_nest_call \<and> 
           zs = map (lift P2) xs @ ((LanguageCon.com.Throw, Normal t')#ys))"             
             then have last_throw:
               "fst (((P1, s)#(P1, t) # xs) ! length ((P1, t) #xs)) = LanguageCon.com.Throw" 
               by fastforce
             from a1 have last_normal: "snd (last ((P1, s)#(P1, t) # xs)) = Normal t'"
               by fastforce
             have seq_lift:
               "(LanguageCon.com.Seq P1 P2, t) # map (lift P2) xs = map (lift P2) ((P1, t) # xs)"
                by (simp add: a1 lift_def)             
            thus  ?thesis using a1 last_throw last_normal all_step eq_P         
              by (clarify, metis (no_types, lifting) append_Cons env_normal_s'_normal_s  step_e)                 
          qed
      qed
    qed (auto) 
qed (force)+

lemma not_func_redex_cptn_mod_nest_n': 
  assumes  
       vars:"v = toSeq s" and vars1:"w = toSeq t" and 
       a0:"\<Gamma>\<turnstile>\<^sub>c (P, v) \<rightarrow> (Q, w)" and
        a0':"\<forall>ns ns'. (s = Normal ns \<or> s = Abrupt ns) \<and> 
                     (t = Normal ns' \<or> t = Abrupt ns') \<longrightarrow> snd ns = snd ns'" and
        a1:"(n,\<Gamma>,(Q,t)#xs) \<in>  cptn_mod_nest_call" and 
        a2:"(\<forall>fn. redex P \<noteq> Call fn) \<or> 
            (redex P = Call fn \<and> \<Gamma> fn = None) \<or> 
            (redex P = Call fn \<and> (\<forall>sa. s\<noteq>Normal sa))"
shows "(n,\<Gamma>,(P,s)#(Q,t)#xs) \<in>  cptn_mod_nest_call"
using a0 a1 a2 a0' vars vars1
proof (induct arbitrary: xs) 
  case (Basicc f e s1)    
  thus ?case  using stepc.Basicc[of \<Gamma> f e s1]
   by (simp add: Basicc cptn_mod_nest_call.CptnModNestSkip)
next
  case (Specc s1 t1 r)
  thus ?case using stepc.Specc[of s1 t1 r \<Gamma>]  
    by (simp add: Specc cptn_mod_nest_call.CptnModNestSkip)
next
  case (SpecStuckc s1 r)
  thus ?case using stepc.SpecStuckc[of s1 _ \<Gamma>]  
    by (simp add: cptn_mod_nest_call.CptnModNestSkip stepc.SpecStuckc)
next
  case (Guardc s1 g f c) 
    thus ?case
      by (metis (mono_tags, lifting) cptn_mod_nest_call.CptnModNestGuard prod_eqI toSeq.simps(1) toSeq_not_Normal xstate.inject(1)) 
  next
    case (GuardFaultc s1 g f c)        
    thus ?case using  stepc.GuardFaultc[of s1 g \<Gamma> f]
      by (simp add: GuardFaultc cptn_mod_nest_call.CptnModNestSkip)
next
case (Seqc c1 s1 c1' t1 c2)
  have step: "\<Gamma>\<turnstile>\<^sub>c (c1, s1) \<rightarrow> (c1', t1)" by (simp add: Seqc.hyps(1))
  then have nsc1: "c1\<noteq>Skip" using stepc_elim_cases(1) by blast 
  have assum: "(n, \<Gamma>, (Seq c1' c2, t) # xs) \<in> cptn_mod_nest_call" using Seqc.prems by blast
  have divseq:"(\<forall>s P Q zs. (Seq c1' c2, t) # xs=(Seq P Q, s)#zs \<longrightarrow>
                (\<exists>xs sv' sv''. ((n,\<Gamma>,(P, s)#xs) \<in> cptn_mod_nest_call  \<and> 
                           (zs=(map (lift Q) xs) \<or>
                           ((fst(((P, s)#xs)!length xs)=Skip \<and> 
                             (\<exists>ys. (n,\<Gamma>,(Q, snd(((P, s)#xs)!length xs))#ys) \<in> cptn_mod_nest_call \<and> 
                              zs=(map (lift (Q)) xs)@((Q, snd(((P, s)#xs)!length xs))#ys)))) \<or>
                           ((fst(((P, s)#xs)!length xs)=Throw \<and> 
                               snd(last ((P, s)#xs)) = Normal sv' \<and>  t=Normal sv''\<and>
                             (\<exists>ys.  (n,\<Gamma>,(Throw,Normal sv')#ys) \<in> cptn_mod_nest_call \<and>
                              zs=(map (lift Q) xs)@((Throw,Normal sv')#ys))
                               ))))
                            
                 ))"  using div_seq_nest [OF assum] unfolding seq_cond_nest_def by auto
   {fix sa P Q zsa
       assume ass:"(Seq c1' c2, t) # xs = (Seq P Q, sa) # zsa"
       then have eqs:"c1' = P \<and> c2 = Q \<and> t = sa \<and> xs = zsa" by auto
       then have "(\<exists>xs sv' sv''. (n,\<Gamma>, (P, sa) # xs) \<in> cptn_mod_nest_call \<and>
                        (zsa = map (lift Q) xs \<or>              
                         fst (((P, sa) # xs) ! length xs) = Skip \<and>
                             (\<exists>ys. (n,\<Gamma>, (Q, snd (((P, sa) # xs) ! length xs)) # ys) \<in> cptn_mod_nest_call \<and>
                             zsa = map (lift Q) xs @ (Q, snd (((P, sa) # xs) ! length xs)) # ys) \<or>
                        ((fst(((P, sa)#xs)!length xs)=Throw \<and> 
                          snd(last ((P, sa)#xs)) = Normal sv' \<and>  t=Normal sv''\<and>
                          (\<exists>ys.  (n,\<Gamma>,(Throw,Normal sv')#ys) \<in> cptn_mod_nest_call \<and>
                              zsa=(map (lift Q) xs)@((Throw,Normal sv')#ys))))))" 
             using ass divseq by blast
    } note conc=this [of c1' c2 t xs]    
     then obtain xs' sa' sa''
       where  split:"(n,\<Gamma>, (c1',t) # xs') \<in> cptn_mod_nest_call \<and>
                     (xs = map (lift c2) xs' \<or>                   
                     fst (((c1', t) # xs') ! length xs') = Skip \<and>
                        (\<exists>ys. (n,\<Gamma>, (c2, snd (((c1',t) # xs') ! length xs')) # ys) \<in> cptn_mod_nest_call \<and>
                         xs = map (lift c2) xs' @ (c2, snd (((c1', t) # xs') ! length xs')) # ys) \<or>
                     ((fst(((c1', t)#xs')!length xs')=Throw \<and> 
                         snd(last ((c1', t)#xs')) = Normal sa' \<and> t=Normal sa''\<and>
                         (\<exists>ys.  (n,\<Gamma>,(Throw,Normal sa')#ys) \<in> cptn_mod_nest_call \<and>
                              xs=(map (lift c2) xs')@((Throw,Normal sa')#ys))
                         )))"  by blast
  then have "(xs = map (lift c2) xs' \<or>                   
                   fst (((c1', t) # xs') ! length xs') = Skip \<and>
                      (\<exists>ys. (n,\<Gamma>, (c2, snd (((c1', t) # xs') ! length xs')) # ys) \<in> cptn_mod_nest_call \<and>
                       xs = map (lift c2) xs' @ (c2, snd (((c1', t) # xs') ! length xs')) # ys) \<or>
                   ((fst(((c1', t)#xs')!length xs')=Throw \<and> 
                       snd(last ((c1',t)#xs')) = Normal sa' \<and> t=Normal sa''\<and>
                       (\<exists>ys.  (n,\<Gamma>,(Throw,Normal sa')#ys) \<in> cptn_mod_nest_call \<and>
                            xs=(map (lift c2) xs')@((Throw,Normal sa')#ys)))))" 
    by auto
  thus ?case 
  proof{           
       assume c1'nonf:"xs = map (lift c2) xs'"
       then have c1'cptn:"(n,\<Gamma>, (c1', t) # xs') \<in> cptn_mod_nest_call" using split by blast
       then have induct_step: "(n,\<Gamma>, (c1, s) # (c1', t)#xs') \<in> cptn_mod_nest_call"
         using Seqc.hyps(2) Seqc.prems(2) Seqc.prems(4) a0' 
         by (simp add: Seqc.prems(5))
       then have "(Seq c1' c2, t)#xs = map (lift c2) ((c1', t)#xs')"
         using c1'nonf
         by (simp add: lift_def)
       thus ?thesis 
         using c1'nonf c1'cptn induct_step by (auto simp add: CptnModNestSeq1)
    next
      assume "fst (((c1', t) # xs') ! length xs') = Skip \<and>
              (\<exists>ys. (n,\<Gamma>, (c2, snd (((c1', t) # xs') ! length xs')) # ys) \<in> cptn_mod_nest_call \<and>
                  xs = map (lift c2) xs' @ (c2, snd (((c1', t) # xs') ! length xs')) # ys) \<or>
             ((fst(((c1', t)#xs')!length xs')=Throw \<and> 
                snd(last ((c1', t)#xs')) = Normal sa' \<and> t=Normal sa''\<and>
                (\<exists>ys.  (n,\<Gamma>,(Throw,Normal sa')#ys) \<in> cptn_mod_nest_call \<and>
                              xs=(map (lift c2) xs')@((Throw,Normal sa')#ys))))"  
      thus ?thesis
      proof
       assume assth:"fst (((c1', t) # xs') ! length xs') = Skip \<and>
            (\<exists>ys. (n,\<Gamma>, (c2, snd (((c1', t) # xs') ! length xs')) # ys) \<in> cptn_mod_nest_call \<and>
                xs = map (lift c2) xs' @ (c2, snd (((c1', t) # xs') ! length xs')) # ys)"
       then obtain ys 
           where split':"(n,\<Gamma>, (c2, snd (((c1', t) # xs') ! length xs')) # ys) \<in> cptn_mod_nest_call \<and>
                xs = map (lift c2) xs' @ (c2, snd (((c1', t) # xs') ! length xs')) # ys"
           by auto    
       then have c1'cptn:"(n,\<Gamma>, (c1', t) # xs') \<in> cptn_mod_nest_call" using split by blast
       then have induct_step: "(n,\<Gamma>, (c1, s) # (c1', t)#xs') \<in> cptn_mod_nest_call"
       using Seqc.hyps(2) Seqc.prems(2)
       by (simp add: Seqc.prems(4) Seqc.prems(5) a0')                
     then have seqmap:"(Seq c1 c2, s)#(Seq c1' c2, t)#xs = 
            map (lift c2) ((c1,s)#(c1', t)#xs') @ (c2, snd (((c1', t) # xs') ! length xs')) # ys"
      using split' by (simp add:  lift_def) 
      then have lastc1:"last ((c1, s) # (c1', t) # xs') = ((c1', t) # xs') ! length xs'"
        by (simp add: last_length) 
      then have lastc1skip:"fst (last ((c1, s) # (c1', t) # xs')) = Skip" 
           using assth by fastforce          
      thus ?thesis 
        using seqmap split' cptn_mod_nest_call.CptnModNestSeq2
              induct_step lastc1 lastc1skip
        by (metis (no_types) Cons_lift_append )               
    next
        assume assm:"((fst(((c1', t)#xs')!length xs')=Throw \<and> 
                snd(last ((c1', t)#xs')) = Normal sa' \<and>  t=Normal sa''\<and>
                (\<exists>ys.(n,\<Gamma>,(Throw,Normal sa')#ys) \<in> cptn_mod_nest_call \<and>
                 xs=(map (lift c2) xs')@((Throw,Normal sa')#ys))))"
        then have s'eqsa'': "t=Normal sa''" by auto
        then have snormal: "\<exists>ns. s=Normal ns"
          by (metis Seqc.prems(4) Seqc.prems(5) local.step step_not_normal_s_eq_t toSeq_not_Normal)
        then have c1'cptn:"(n,\<Gamma>, (c1', t) # xs') \<in> cptn_mod_nest_call" using split by blast        
        then have induct_step: "(n,\<Gamma>, (c1, s) # (c1', t)#xs') \<in> cptn_mod_nest_call"
          using Seqc.hyps(2) Seqc.prems(2) 
          by (simp add: Seqc.prems(4) Seqc.prems(5) a0')       
        then obtain ys where
          seqmap:"(Seq c1' c2, t)#xs = 
                    (map (lift c2) ((c1', t)#xs'))@((Throw,Normal sa')#ys)"
        using assm
        using Cons_lift_append by blast          
        then have lastc1:"last ((c1, s) # (c1',t) # xs') = ((c1', t) # xs') ! length xs'"
                   by (simp add: last_length) 
        then have lastc1skip:"fst (last ((c1, s) # (c1', t) # xs')) = Throw" 
             using assm by fastforce
        then have "snd (last ((c1, s) # (c1', t) # xs')) = Normal sa'"
             using assm by force        
        thus ?thesis
            using assm c1'cptn induct_step lastc1skip snormal seqmap s'eqsa'' 
            by (auto simp add:cptn_mod_nest_call.CptnModNestSeq3)
        qed
      }qed   
  next
    case (SeqSkipc c2 s1 xs)
  have c2incptn:"(n,\<Gamma>, (c2, s) # xs) \<in> cptn_mod_nest_call"
    using SeqSkipc.prems(1) SeqSkipc.prems(4) SeqSkipc.prems(5) a0' eq_toSeq by blast
  moreover have 1:"(n,\<Gamma>, [(Skip, s)]) \<in> cptn_mod_nest_call"
    by (simp add: cptn_mod_nest_call.CptnModNestOne)
  moreover have 2:"fst(last ([(Skip, s)])) = Skip" by fastforce
  moreover have 3:"(n,\<Gamma>,(c2, snd(last [(Skip, s)]))#xs) \<in> cptn_mod_nest_call" 
    using c2incptn by auto  
  moreover have "(c2,s)#xs=(map (lift c2) [])@(c2, snd(last [(Skip, s)]))#xs" 
    by (auto simp add:lift_def)
  moreover have "s=t" using eq_toSeq SeqSkipc by blast
  ultimately show ?case by (simp add: CptnModNestSeq2)   
next
  case (SeqThrowc c2 s1 xs)  
  have eq_st:"s=t" using eq_toSeq[OF SeqThrowc(3)] SeqThrowc by auto
  obtain ns where normals:"s=Normal ns" using SeqThrowc
    by (metis toSeq_not_Normal)
  have "(n,\<Gamma>, [(Throw, Normal ns)]) \<in> cptn_mod_nest_call" 
    by (simp add: cptn_mod_nest_call.CptnModNestOne) 
  then obtain ys where 
    ys_nil:"ys=[]" and 
    last:"(n, \<Gamma>, (Throw,  s)#ys)\<in> cptn_mod_nest_call"
    using normals 
   by auto
  moreover have "fst (last ((Throw, Normal ns)#ys)) = Throw" using ys_nil last by auto
  moreover have "snd (last ((Throw, Normal ns)#ys)) = Normal ns" using ys_nil last by auto
  moreover from ys_nil have "(map (lift c2) ys) = []" by auto  
  ultimately show ?case 
    using SeqThrowc.prems cptn_mod_nest_call.CptnModNestSeq3 eq_st normals by blast      

next
  case (CondTruec s1 b c1 c2)
  moreover obtain ns where normals:"s=Normal ns"
    by (metis (no_types) calculation(5) toSeq_not_Normal)
  moreover have "s=t"
    using calculation(5,6) eq_toSeq[OF calculation(4)]  by auto
  ultimately show ?case by (simp add: cptn_mod_nest_call.CptnModNestCondT)
next
  case (CondFalsec s1 b c1 c2)
  moreover obtain ns where normals:"s=Normal ns"
    by (metis (no_types) calculation(5) toSeq_not_Normal)
  moreover have "s=t"
    using calculation(5,6) eq_toSeq[OF calculation(4)]  by auto
  ultimately show ?case by (simp add: cptn_mod_nest_call.CptnModNestCondF)
next 
  case (WhileTruec s1 b c) 
  have sinb: "s1\<in>b" by fact
  obtain ns where normals:"s=Normal ns"
    by (metis (no_types) WhileTruec(5) toSeq_not_Normal)
  have eq_st:"s=t" using eq_toSeq[OF WhileTruec(4)] WhileTruec by auto
  have SeqcWhile: "(n,\<Gamma>, (Seq c (While b c), Normal ns) # xs) \<in> cptn_mod_nest_call"
    using WhileTruec.prems(1) eq_st normals by force
 have divseq:"(\<forall>s P Q zs. (Seq c (While b c), Normal ns) # xs=(Seq P Q, s)#zs \<longrightarrow>
                (\<exists>xs s'. ((n,\<Gamma>,(P, s)#xs) \<in> cptn_mod_nest_call  \<and> 
                           (zs=(map (lift Q) xs) \<or>
                           ((fst(((P, s)#xs)!length xs)=Skip \<and> 
                             (\<exists>ys. (n,\<Gamma>,(Q, snd(((P, s)#xs)!length xs))#ys) \<in> cptn_mod_nest_call \<and> 
                              zs=(map (lift (Q)) xs)@((Q, snd(((P, s)#xs)!length xs))#ys)))) \<or>
                           ((fst(((P, s)#xs)!length xs)=Throw \<and> 
                               snd(last ((P, s)#xs)) = Normal s' \<and>
                              (\<exists>ys.  (n,\<Gamma>,(Throw,Normal s')#ys) \<in> cptn_mod_nest_call \<and>
                      zs=(map (lift Q) xs)@((Throw,Normal s')#ys))))))                            
                 ))" using div_seq_nest [OF SeqcWhile] eq_st normals 
   unfolding seq_cond_nest_def by fast
{fix sa P Q zsa
       assume ass:"(Seq c (While b c), Normal ns) # xs = (Seq P Q, sa) # zsa"
       then have eqs:"c = P \<and> (While b c) = Q \<and> Normal ns = sa \<and> xs = zsa" by auto
       then have "(\<exists>xs s'. (n,\<Gamma>, (P, sa) # xs) \<in> cptn_mod_nest_call \<and>
                        (zsa = map (lift Q) xs \<or>              
                         fst (((P, sa) # xs) ! length xs) = Skip \<and>
                             (\<exists>ys. (n,\<Gamma>, (Q, snd (((P, sa) # xs) ! length xs)) # ys) \<in> cptn_mod_nest_call \<and>
                             zsa = map (lift Q) xs @ (Q, snd (((P, sa) # xs) ! length xs)) # ys) \<or>
                        ((fst(((P, sa)#xs)!length xs)=Throw \<and> 
                          snd(last ((P, sa)#xs)) = Normal s' \<and>
                          (\<exists>ys.  (n,\<Gamma>,(Throw,Normal s')#ys) \<in> cptn_mod_nest_call \<and>
                      zsa=(map (lift Q) xs)@((Throw,Normal s')#ys))
                        ))))" 
             using ass divseq by auto
    } note conc=this [of c "While b c" "Normal ns" xs] 
   then obtain xs' s' 
        where  split:"(n,\<Gamma>, (c, Normal ns) # xs') \<in> cptn_mod_nest_call \<and>
     (xs = map (lift (While b c)) xs' \<or>
      fst (((c, Normal ns) # xs') ! length xs') = Skip \<and>
      (\<exists>ys. (n,\<Gamma>, (While b c, snd (((c, Normal ns) # xs') ! length xs')) # ys)
            \<in> cptn_mod_nest_call \<and>
            xs =
            map (lift (While b c)) xs' @
            (While b c, snd (((c, Normal ns) # xs') ! length xs')) # ys) \<or>
      fst (((c, Normal ns) # xs') ! length xs') = Throw \<and>
      snd (last ((c, Normal ns) # xs')) = Normal s' \<and> 
      (\<exists>ys.  (n,\<Gamma>, ((Throw, Normal s')#ys)) \<in> cptn_mod_nest_call \<and>
      xs = map (lift (While b c)) xs' @ ((Throw, Normal s')#ys)))"  by blast
 then have "(xs = map (lift (While b c)) xs' \<or>
            fst (((c, Normal ns) # xs') ! length xs') = Skip \<and>
            (\<exists>ys. (n,\<Gamma>, (While b c, snd (((c, Normal ns) # xs') ! length xs')) # ys)
                  \<in> cptn_mod_nest_call \<and>
                  xs = map (lift (While b c)) xs' @
                  (While b c, snd (((c, Normal ns) # xs') ! length xs')) # ys) \<or>
            fst (((c, Normal ns) # xs') ! length xs') = Throw \<and>
            snd (last ((c, Normal ns) # xs')) = Normal s' \<and>
            (\<exists>ys.  (n,\<Gamma>, ((Throw, Normal s')#ys)) \<in> cptn_mod_nest_call \<and>
          xs = map (lift (While b c)) xs' @ ((Throw, Normal s')#ys)))" ..
 thus ?case
 proof{ 
   assume 1:"xs = map (lift (While b c)) xs'"  
   have 3:"(n, \<Gamma>, (c, Normal ns) # xs') \<in> cptn_mod_nest_call" using split by auto   
   then show ?thesis 
     using "1" cptn_mod_nest_call.CptnModNestWhile1 sinb normals eq_st
     by (metis WhileTruec.prems(4) toSeq.simps(1) xstate.inject(1))     
 next
   assume "fst (((c, Normal ns) # xs') ! length xs') = Skip \<and>
          (\<exists>ys. (n,\<Gamma>, (While b c, snd (((c, Normal ns) # xs') ! length xs')) # ys)
                \<in> cptn_mod_nest_call \<and>
                xs =
                map (lift (While b c)) xs' @
                (While b c, snd (((c, Normal ns) # xs') ! length xs')) # ys) \<or>
          fst (((c, Normal ns) # xs') ! length xs') = Throw \<and>
          snd (last ((c, Normal ns) # xs')) = Normal s' \<and>
          (\<exists>ys.  (n,\<Gamma>, ((Throw, Normal s')#ys)) \<in> cptn_mod_nest_call \<and>
          xs = map (lift (While b c)) xs' @ ((Throw, Normal s')#ys))"
   thus ?case
   proof
     assume asm:"fst (((c, Normal ns) # xs') ! length xs') = Skip \<and>
             (\<exists>ys. (n,\<Gamma>, (While b c, snd (((c, Normal ns) # xs') ! length xs')) # ys)
             \<in> cptn_mod_nest_call \<and>
             xs =
             map (lift (While b c)) xs' @
             (While b c, snd (((c, Normal ns) # xs') ! length xs')) # ys)"
     then obtain ys 
       where asm':"(n,\<Gamma>, (While b c, snd (last ((c, Normal ns) # xs'))) # ys)
                   \<in> cptn_mod_nest_call 
                   \<and> xs = map (lift (While b c)) xs' @
                       (While b c, snd (last ((c, Normal ns) # xs'))) # ys" 
              by (auto simp add: last_length)
     moreover have 3:"(n,\<Gamma>, (c, Normal ns) # xs') \<in> cptn_mod_nest_call" using split by auto
     moreover from asm have "fst (last ((c, Normal ns) # xs'))  = Skip"
          by (simp add: last_length) 
        ultimately show ?case using sinb normals eq_st  WhileTruec.prems(4)
          by (auto simp add:CptnModNestWhile2)
   next
    assume asm:" fst (((c, Normal ns) # xs') ! length xs') = Throw \<and>
          snd (last ((c, Normal ns) # xs')) = Normal s' \<and>
          (\<exists>ys.  (n,\<Gamma>, ((Throw, Normal s')#ys)) \<in> cptn_mod_nest_call \<and>
          xs = map (lift (While b c)) xs' @ ((Throw, Normal s')#ys))"   
     moreover have 3:"(n,\<Gamma>, (c, Normal ns) # xs') \<in> cptn_mod_nest_call" 
       using split by auto
     moreover from asm have "fst (last ((c, Normal ns) # xs'))  = Throw"
          by (simp add: last_length) 
        ultimately show ?case using sinb normals eq_st  WhileTruec.prems(4) 
          by (auto simp add:CptnModNestWhile3)
   qed
 }qed  
next
  case (WhileFalsec s1 b c) 
  thus ?case   using stepc.WhileFalsec[of s1 b \<Gamma> c] 
    by (simp add: cptn_mod_nest_call.CptnModNestSkip)
next
  case (Awaitc s1 b \<Gamma>a c t1)
  thus ?case using  stepc.Awaitc[of s1 b \<Gamma>a \<Gamma>] 
    by (simp add: cptn_mod_nest_call.CptnModNestSkip)
next
  case (AwaitAbruptc s1 b \<Gamma>a c t1 ta)
  thus ?case using stepc.AwaitAbruptc[of s1 b \<Gamma>a \<Gamma> c t1 ta] 
    by (simp add: cptn_mod_nest_call.CptnModNestThrow) 
next
  case (Callc p bdy s1)
  moreover have eq_st:"s=t" using eq_toSeq[OF Callc(5)] Callc by auto
  moreover obtain ns where normals:"s=Normal ns"
    by (metis (no_types) Callc(6) toSeq_not_Normal)
  ultimately show ?case
    by (metis LanguageCon.com.inject(6) SmallStepCon.redex.simps(7) option.distinct(1))         
next
  case (CallUndefinedc p s1)    
  then have seq:"\<Gamma>\<turnstile>\<^sub>c( (LanguageCon.com.Call p),toSeq s) \<rightarrow> (Skip,toSeq t)" 
    using stepc.CallUndefinedc[of \<Gamma> p s1] by auto
  thus ?case 
    using  CallUndefinedc CptnModNestSkip[OF seq _ _ _ CallUndefinedc(2)] 
    by force
next
  case (DynComc c s1)  
  moreover have eq_st:"s=t"
    using calculation(4) calculation(5) eq_toSeq[OF calculation(3)] by force
  moreover obtain ns where normals:"s=Normal ns"
    by (metis calculation(4) toSeq_not_Normal)
  moreover have "(n, \<Gamma>, (LanguageCon.com.DynCom c, Normal ns) # (c (fst ns), 
                           Normal ns) # xs) \<in> cptn_mod_nest_call"
    using DynComc.prems(1) DynComc.prems(4) 
      cptn_mod_nest_call.CptnModNestDynCom eq_st normals by fastforce
  then show ?case
    using DynComc.prems(4) eq_st normals by fastforce
next
  case (Catchc c1 s1 c1' t1 c2)
   have step: "\<Gamma>\<turnstile>\<^sub>c (c1, s1) \<rightarrow> (c1', t1)" by (simp add: Catchc.hyps(1))
  then have nsc1: "c1\<noteq>Skip" using stepc_elim_cases(1) by blast 
  have assum: "(n,\<Gamma>, (Catch c1' c2, t) # xs) \<in> cptn_mod_nest_call" 
  using Catchc.prems by blast
  have divcatch:"(\<forall>s P Q zs. (Catch c1' c2, t) # xs=(Catch P Q, s)#zs \<longrightarrow>
  (\<exists>xs s' s''. ((n,\<Gamma>,(P, s)#xs) \<in> cptn_mod_nest_call  \<and> 
             (zs=(map (lift_catch Q) xs) \<or>
             ((fst(((P, s)#xs)!length xs)=Throw \<and>
               snd(last ((P, s)#xs)) = Normal s' \<and>  s=Normal s''\<and>
               (\<exists>ys. (n,\<Gamma>,(Q, snd(((P, s)#xs)!length xs))#ys) \<in> cptn_mod_nest_call \<and> 
                zs=(map (lift_catch Q) xs)@((Q, snd(((P, s)#xs)!length xs))#ys)))) \<or>
                ((fst(((P, s)#xs)!length xs)=Skip \<and>  
                  (\<exists>ys. (n,\<Gamma>,(Skip,snd(last ((P, s)#xs)))#ys) \<in> cptn_mod_nest_call \<and>                   
                 zs=(map (lift_catch Q) xs)@((Skip,snd(last ((P, s)#xs)))#ys))                
                 ))))
   ))" using div_catch_nest [OF assum] by (auto simp add: catch_cond_nest_def)
   {fix sa P Q zsa
       assume ass:"(Catch c1' c2,t) # xs = (Catch P Q, sa) # zsa"
       then have eqs:"c1' = P \<and> c2 = Q \<and> t = sa \<and> xs = zsa" by auto
       then have "(\<exists>xs sv' sv''. ((n, \<Gamma>,(P, sa)#xs) \<in> cptn_mod_nest_call  \<and> 
             (zsa=(map (lift_catch Q) xs) \<or>
             ((fst(((P, sa)#xs)!length xs)=Throw \<and>
               snd(last ((P, sa)#xs)) = Normal sv' \<and>  t=Normal sv''\<and>
               (\<exists>ys. (n,\<Gamma>,(Q, snd(((P, sa)#xs)!length xs))#ys) \<in> cptn_mod_nest_call \<and> 
                zsa=(map (lift_catch Q) xs)@((Q, snd(((P, sa)#xs)!length xs))#ys)))) \<or>
                ((fst(((P, sa)#xs)!length xs)=Skip \<and>                  
                 (\<exists>ys. (n,\<Gamma>,(Skip,snd(last ((P, sa)#xs)))#ys) \<in> cptn_mod_nest_call \<and>                   
                 zsa=(map (lift_catch Q) xs)@((Skip,snd(last ((P, sa)#xs)))#ys))))))
   )"   using ass divcatch by blast
    } note conc=this [of c1' c2 t xs]    
     then obtain xs' sa' sa''
       where split:
         "(n,\<Gamma>, (c1', t) # xs') \<in> cptn_mod_nest_call \<and> 
          (xs = map (lift_catch c2) xs' \<or>
          fst (((c1', t) # xs') ! length xs') = Throw \<and>
          snd (last ((c1', t) # xs')) = Normal sa' \<and> t = Normal sa'' \<and>
          (\<exists>ys. (n,\<Gamma>, (c2, snd (((c1',t) # xs') ! length xs')) # ys) \<in> cptn_mod_nest_call \<and>
                xs = map (lift_catch c2) xs' @
                (c2, snd (((c1', t) # xs') ! length xs')) # ys) \<or>
          fst (((c1', t) # xs') ! length xs') = Skip \<and>
          (\<exists>ys. (n,\<Gamma>,(Skip,snd(last ((c1', t)#xs')))#ys) \<in> cptn_mod_nest_call \<and>                   
                 xs=(map (lift_catch c2) xs')@((Skip,snd(last ((c1', t)#xs')))#ys)))"          
        by blast
  then have "(xs = map (lift_catch c2) xs' \<or>
          fst (((c1', t) # xs') ! length xs') = Throw \<and>
          snd (last ((c1', t) # xs')) = Normal sa' \<and> t = Normal sa'' \<and>
          (\<exists>ys. (n,\<Gamma>, (c2, snd (((c1', t) # xs') ! length xs')) # ys) \<in> cptn_mod_nest_call \<and>
                xs = map (lift_catch c2) xs' @
                (c2, snd (((c1', t) # xs') ! length xs')) # ys) \<or>
          fst (((c1', t) # xs') ! length xs') = Skip \<and>
          (\<exists>ys. (n,\<Gamma>,(Skip,snd(last ((c1', t)#xs')))#ys) \<in> cptn_mod_nest_call \<and>                   
                 xs=(map (lift_catch c2) xs')@((Skip,snd(last ((c1', t)#xs')))#ys)))"          
        by auto
  thus ?case 
  proof{           
       assume c1'nonf:"xs = map (lift_catch c2) xs'"
       then have c1'cptn:"(n,\<Gamma>, (c1', t) # xs') \<in> cptn_mod_nest_call" using split by blast
       then have induct_step: "(n, \<Gamma>, (c1, s) # (c1',t)#xs') \<in> cptn_mod_nest_call"
         using Catchc.hyps(2) Catchc.prems(2) 
         by (simp add: Catchc.prems(4) Catchc.prems(5) a0')  
       then have "(Catch c1' c2, t)#xs = map (lift_catch c2) ((c1', t)#xs')"
            using c1'nonf
            by (simp add: CptnModCatch1 lift_catch_def)
       thus ?thesis 
            using c1'nonf c1'cptn induct_step 
       by (auto simp add: CptnModNestCatch1)
    next
      assume "fst (((c1', t) # xs') ! length xs') = Throw \<and>
                snd (last ((c1', t) # xs')) = Normal sa' \<and>t = Normal sa'' \<and>
                (\<exists>ys. (n,\<Gamma>, (c2, snd (((c1', t) # xs') ! length xs')) # ys) \<in> cptn_mod_nest_call \<and>
                xs =map (lift_catch c2) xs' @ (c2, snd (((c1', t) # xs') ! length xs')) # ys) \<or>
               fst (((c1', t) # xs') ! length xs') = Skip \<and>
                (\<exists>ys. (n,\<Gamma>,(Skip,snd(last ((c1', t)#xs')))#ys) \<in> cptn_mod_nest_call \<and>                   
                 xs=(map (lift_catch c2) xs')@((Skip,snd(last ((c1', t)#xs')))#ys))"  
      thus ?thesis
      proof
         assume assth:
               "fst (((c1', t) # xs') ! length xs') = Throw \<and>
                snd (last ((c1', t) # xs')) = Normal sa' \<and> t = Normal sa'' \<and>
                (\<exists>ys. (n,\<Gamma>, (c2, snd (((c1', t) # xs') ! length xs')) # ys) \<in> cptn_mod_nest_call \<and>
                xs =map (lift_catch c2) xs' @ (c2, snd (((c1', t) # xs') ! length xs')) # ys)"
             then have s'eqsa'': "t=Normal sa''" by auto
             then have snormal: "\<exists>ns. s=Normal ns"
               using Catchc.prems(4) Catchc.prems(5) a0' c_step local.step step_ce_notNormal by blast
             then obtain ys 
             where split':"(n,\<Gamma>, (c2, snd (((c1',t) # xs') ! length xs')) # ys) \<in> cptn_mod_nest_call \<and>
                xs =map (lift_catch c2) xs' @ (c2, snd (((c1', t) # xs') ! length xs')) # ys"
                using assth by auto    
         then have c1'cptn:"(n,\<Gamma>, (c1', t) # xs') \<in> cptn_mod_nest_call" 
              using split by blast
         then have induct_step: "(n,\<Gamma>, (c1, s) # (c1', t)#xs') \<in> cptn_mod_nest_call"
           using Catchc.hyps(2) Catchc.prems(2) SmallStepCon.redex.simps(11)
           by (simp add: Catchc.prems(4) Catchc.prems(5) a0')
         then have seqmap:"(Catch c1 c2, s)#(Catch c1' c2, t)#xs = 
                           map (lift_catch c2) ((c1,s)#(c1', t)#xs') @ 
                            (c2, snd (((c1', t) # xs') ! length xs')) # ys"
              using split' by (simp add: CptnModCatch3 lift_catch_def) 
        then have lastc1:"last ((c1, s) # (c1', t) # xs') = ((c1', t) # xs') ! length xs'"
             by (simp add: last_length) 
        then have lastc1skip:"fst (last ((c1, s) # (c1', t) # xs')) = Throw" 
             using assth by fastforce
        then have "snd (last ((c1, s) # (c1', t) # xs')) = Normal sa'"
             using assth by force
        thus ?thesis using snormal seqmap s'eqsa'' split' 
               cptn_mod_nest_call.CptnModNestCatch3 
              induct_step lastc1 lastc1skip
              using Cons_lift_catch_append
              by (metis)           
    next
        assume assm:" fst (((c1', t) # xs') ! length xs') = Skip \<and> 
                       (\<exists>ys. (n,\<Gamma>,(Skip,snd(last ((c1', t)#xs')))#ys) \<in> cptn_mod_nest_call \<and>                   
                      xs=(map (lift_catch c2) xs')@((Skip,snd(last ((c1', t)#xs')))#ys))"
        then have c1'cptn:"(n,\<Gamma>, (c1', t) # xs') \<in> cptn_mod_nest_call" 
          using split by blast
        then have induct_step: "(n,\<Gamma>, (c1, s) # (c1', t)#xs') \<in> cptn_mod_nest_call"
          using Catchc.hyps(2) Catchc.prems(2) SmallStepCon.redex.simps(11)        
          by (simp add: Catchc.prems(4) Catchc.prems(5) a0')
        then have "map (lift_catch c2) ((c1', t) # xs') = (Catch c1' c2, t) # map (lift_catch c2) xs'" 
          by (auto simp add: lift_catch_def)
        then obtain ys 
             where seqmap:"(Catch c1' c2, t)#xs = (map (lift_catch c2) ((c1', t)#xs'))@((Skip,snd(last ((c1', t)#xs')))#ys)"
        using assm by fastforce
        then have lastc1:"last ((c1, s) # (c1', t) # xs') = ((c1', t) # xs') ! length xs'"
                   by (simp add: last_length) 
        then have lastc1skip:"fst (last ((c1, s) # (c1', t) # xs')) = Skip" 
             using assm by fastforce
        then have "snd (last ((c1, s) # (c1', t) # xs')) = snd (last ((c1', t) # xs'))"
             using assm by force
        thus ?thesis 
            using assm c1'cptn induct_step lastc1skip seqmap 
            by (auto simp add:cptn_mod_nest_call.CptnModNestCatch2)
    qed
  }qed              
next
  case (CatchThrowc c2 s1)
  then obtain ns where ns:"s = Normal ns"
    by (metis toSeq_not_Normal)
  then have eq_st: "s=t" using  eq_toSeq[OF CatchThrowc(3)] CatchThrowc(4,5) by auto
  have c2incptn:"(n,\<Gamma>, (c2, Normal ns) # xs) \<in> cptn_mod_nest_call"
    using CatchThrowc.prems(1) eq_st ns by fastforce
  have 1:"(n,\<Gamma>, [(Throw, Normal ns)]) \<in> cptn_mod_nest_call" 
    by (simp add: cptn_mod_nest_call.CptnModNestOne)
  have 2:"fst(last ([(Throw, Normal ns)])) = Throw" by fastforce
  have 3:"(n,\<Gamma>,(c2, snd(last [(Throw, Normal ns)]))#xs) \<in> cptn_mod_nest_call"       
    using c2incptn by auto
  moreover have "(c2,Normal ns)#xs=
                (map (lift c2) [])@(c2, snd(last [(Throw, Normal ns)]))#xs" 
    by (auto simp add:lift_def)     
  ultimately show ?case using eq_st ns CptnModNestCatch3[OF 1 2] by fastforce
next
  case (CatchSkipc c2 s1)
  have "(n,\<Gamma>, [(Skip, s)]) \<in> cptn_mod_nest_call" 
    by (simp add: cptn_mod_nest_call.CptnModNestOne)
  then obtain ys where 
    ys_nil:"ys=[]" and 
    last:"(n,\<Gamma>, (Skip,  s)#ys)\<in> cptn_mod_nest_call"
    by auto
  moreover have "fst (last ((Skip,  s)#ys)) = Skip" using ys_nil last by auto
  moreover have "snd (last ((Skip,  s)#ys)) = s" using ys_nil last by auto
  moreover from ys_nil have "(map (lift_catch c2) ys) = []" by auto
  moreover have "s=t"
    using CatchSkipc.prems(4) CatchSkipc.prems(5) a0' eq_toSeq by blast
  ultimately show ?case using CatchSkipc.prems 
     by simp (simp add: cptn_mod_nest_call.CptnModNestCatch2 ys_nil)
next
  case (FaultPropc c f)
  moreover have "s=t"
    using calculation(6) calculation(7) eq_toSeq[OF a0'] by force
  moreover have "s=Fault f"  using calculation(7) calculation(8) eq_toSeq by force
  ultimately show ?case
    using stepc.FaultPropc[of c \<Gamma> f, OF FaultPropc(1,2)]
    by (metis cptn_mod_nest_call.CptnModNestSkip xstate.distinct(3)) 
next
  case (AbruptPropc c f)
  thus ?case
    by (metis cptn_mod_nest_call.CptnModNestSkip stepc.AbruptPropc toSeq.simps(1) xstate.distinct(1))
next
  case (StuckPropc c)
  thus ?case
    by (metis (no_types, lifting) cptn_mod_nest_call.CptnModNestSkip stepc.StuckPropc toSeq_not_stuck xstate.distinct(5))
qed


lemma not_func_redex_cptn_mod_nest_n_env: 
assumes a0:"\<Gamma>\<turnstile>\<^sub>c (P,s) \<rightarrow>\<^sub>e (P, t)" and
        a1:"(n,\<Gamma>,(P,t)#xs) \<in>  cptn_mod_nest_call"         
shows "(n,\<Gamma>,(P,s)#(P,t)#xs) \<in>  cptn_mod_nest_call"
  by (simp add: a0 a1 cptn_mod_nest_call.CptnModNestEnv)


lemma cptn_mod_nest_cptn_mod:"(n,\<Gamma>,cfs) \<in>  cptn_mod_nest_call  \<Longrightarrow> (\<Gamma>,cfs)\<in> cptn_mod"
  by (induct rule:cptn_mod_nest_call.induct, (auto simp:cptn_mod.intros )+)

lemma cptn_mod_cptn_mod_nest: "(\<Gamma>,cfs)\<in> cptn_mod \<Longrightarrow> \<exists>n. (n,\<Gamma>,cfs) \<in>  cptn_mod_nest_call"
proof (induct rule:cptn_mod.induct)
   case (CptnModSkip \<Gamma> P s t xs) 
   then obtain n where cptn_nest:"(n, \<Gamma>, (Skip, t) # xs) \<in> cptn_mod_nest_call" by auto      
    {assume asm:"\<forall>f. ((\<exists>sn. s = Normal sn) \<and> (\<Gamma> f) = Some Skip \<longrightarrow> P  \<noteq> Call f  )"     
     then have ?case using CptnModNestSkip[OF CptnModSkip(1) CptnModSkip(2) CptnModSkip(3) asm cptn_nest] by auto
    }note t1=this
    {assume asm:"\<not> (\<forall>f. ((\<exists>sn. s = Normal sn) \<and> (\<Gamma> f) = Some Skip \<longrightarrow> P  \<noteq> Call f))"
     then obtain f where asm:"((\<exists>sn. s = Normal sn) \<and> (\<Gamma> f) = Some Skip \<and> P  = Call f)" by auto 
      then obtain sn where normal_s:"s=Normal sn" by auto
      then have t_eq_s:"t=s" 
        using asm cptn_nest normal_s call_f_step_not_s_eq_t_false[OF CptnModSkip(1)] 
              eq_toSeq[OF CptnModSkip.hyps(3)] CptnModSkip.hyps(2) toSeq.simps(1) 
        by blast 
     then have "(Suc n, \<Gamma>,((Call f), Normal sn)#(Skip, Normal sn)#xs) \<in> cptn_mod_nest_call"
       using asm cptn_nest normal_s CptnModNestCall by fastforce        
     then have ?case using asm normal_s t_eq_s by fastforce
    }note t2 = this
    then show ?case using t1 t2 by fastforce  
next
   case (CptnModThrow \<Gamma> P s t xs)  
   then obtain n where cptn_nest:"(n, \<Gamma>, (Throw, t) # xs) \<in> cptn_mod_nest_call" by auto   
    {assume asm:"\<forall>f. ((\<exists>sn. s = Normal sn) \<and> (\<Gamma> f) = Some Throw \<longrightarrow> P  \<noteq> Call f  )"     
      then have ?case 
        using CptnModNestThrow[OF CptnModThrow(1) CptnModThrow(2) asm CptnModThrow(3)]
        using cptn_nest by blast
    }note t1=this
    { assume asm:"\<not> (\<forall>f. ((\<exists>sn. s = Normal sn) \<and> (\<Gamma> f) = Some Throw \<longrightarrow> P  \<noteq> Call f))"
      then obtain f where asm:"((\<exists>sn. s = Normal sn) \<and> (\<Gamma> f) = Some Throw \<and> P  = Call f)" by auto 
      then obtain sn where normal_s:"s=Normal sn" by auto
      then have t_eq_s:"t=s" 
        using asm cptn_nest normal_s eq_toSeq[OF CptnModThrow.hyps(3)]
          CptnModThrow.hyps(1) 
          call_f_step_not_s_eq_t_false[OF CptnModThrow.hyps(1)]  
        by fastforce       
     then have "(Suc n, \<Gamma>,((Call f), Normal sn)#(Throw, Normal sn)#xs) \<in> cptn_mod_nest_call"
       using asm cptn_nest normal_s CptnModNestCall by fastforce        
     then have ?case using asm normal_s t_eq_s by fastforce
    }note t2 = this
    then show ?case using t1 t2 by fastforce
next
   case (CptnModSeq2 \<Gamma> P0 s xs P1 ys zs) 
   obtain n where n:"(n, \<Gamma>, (P0, s) # xs) \<in> cptn_mod_nest_call" using CptnModSeq2(2) by auto
   also obtain m where m:"(m, \<Gamma>, (P1, snd (last ((P0, s) # xs))) # ys) \<in> cptn_mod_nest_call"
     using CptnModSeq2(5) by auto
   ultimately show ?case
   proof (cases "n\<ge>m") 
     case True thus ?thesis  
       using cptn_mod_nest_mono[of m \<Gamma> _ n] m n CptnModSeq2 cptn_mod_nest_call.CptnModNestSeq2 by blast
   next  
     case False 
     thus ?thesis
       using cptn_mod_nest_mono[of n \<Gamma> _ m] m n CptnModSeq2 
             cptn_mod_nest_call.CptnModNestSeq2 le_cases3 by blast      
   qed
next
   case (CptnModSeq3 \<Gamma> P0 s xs s' ys zs P1) 
   obtain n where n:"(n, \<Gamma>, (P0, Normal s) # xs) \<in> cptn_mod_nest_call" using CptnModSeq3(2) by auto
   also obtain m where m:"(m, \<Gamma>, (LanguageCon.com.Throw, Normal s') # ys) \<in> cptn_mod_nest_call"
     using CptnModSeq3(6) by auto
   ultimately show ?case
   proof (cases "n\<ge>m") 
     case True thus ?thesis  
       using cptn_mod_nest_mono[of m \<Gamma> _ n] m n CptnModSeq3 cptn_mod_nest_call.CptnModNestSeq3
       by blast
   next  
     case False 
     thus ?thesis
       using cptn_mod_nest_mono[of n \<Gamma> _ m] m n CptnModSeq3
             cptn_mod_nest_call.CptnModNestSeq3 le_cases3
      proof -
        have f1: "\<not> n \<le> m \<or> (m, \<Gamma>, (P0, Normal s) # xs) \<in> cptn_mod_nest_call"
          by (metis cptn_mod_nest_mono[of n \<Gamma> _ m] n)
        have "n \<le> m"
          using False by linarith
        then have "(m, \<Gamma>, (P0, Normal s) # xs) \<in> cptn_mod_nest_call"
          using f1 by metis
        then show ?thesis
          by (metis (no_types) CptnModSeq3(3) CptnModSeq3(4) CptnModSeq3(7) 
                   cptn_mod_nest_call.CptnModNestSeq3 m)
      qed          
   qed
next
   case (CptnModWhile2 \<Gamma> P s xs b zs ys) 
   obtain n where n:"(n, \<Gamma>, (P, Normal s) # xs) \<in> cptn_mod_nest_call" using CptnModWhile2(2) by auto
   also obtain m where 
     m:" (m, \<Gamma>, (LanguageCon.com.While b P, snd (last ((P, Normal s) # xs))) # ys) \<in> 
          cptn_mod_nest_call"
     using CptnModWhile2(7) by auto
   ultimately show ?case
   proof (cases "n\<ge>m") 
     case True thus ?thesis  
       using cptn_mod_nest_mono[of m \<Gamma> _ n] m n 
             CptnModWhile2 cptn_mod_nest_call.CptnModNestWhile2 by metis
   next  
     case False 
     thus ?thesis       
    proof -
      have f1: "\<not> n \<le> m \<or> (m, \<Gamma>, (P, Normal s) # xs) \<in> cptn_mod_nest_call"
        using cptn_mod_nest_mono[of n \<Gamma> _ m] n by presburger
      have "n \<le> m"
        using False by linarith
      then have "(m, \<Gamma>, (P, Normal s) # xs) \<in> cptn_mod_nest_call"
        using f1 by metis
      then show ?thesis
        by (metis (no_types) CptnModWhile2(3) CptnModWhile2(4) CptnModWhile2(5) 
                  cptn_mod_nest_call.CptnModNestWhile2 m)
    qed 
   qed
next
   case (CptnModWhile3 \<Gamma> P s xs b s' ys zs)
   obtain n where n:"(n, \<Gamma>, (P, Normal s) # xs) \<in> cptn_mod_nest_call" 
     using CptnModWhile3(2) by auto
   also obtain m where 
     m:" (m, \<Gamma>, (LanguageCon.com.Throw, Normal s') # ys) \<in> cptn_mod_nest_call"
     using CptnModWhile3(7) by auto
   ultimately show ?case
   proof (cases "n\<ge>m") 
     case True thus ?thesis  
     proof -
      have "(n, \<Gamma>, (LanguageCon.com.Throw, Normal s') # ys) \<in> cptn_mod_nest_call"
        using True cptn_mod_nest_mono[of m \<Gamma> _ n] m by presburger
      then show ?thesis
        by (metis (no_types) CptnModWhile3.hyps(3) CptnModWhile3.hyps(4) 
            CptnModWhile3.hyps(5) CptnModWhile3.hyps(8) cptn_mod_nest_call.CptnModNestWhile3 n)
     qed 
   next  
     case False 
     thus ?thesis  using m n cptn_mod_nest_call.CptnModNestWhile3 cptn_mod_nest_mono[of n \<Gamma> _ m]
       by (metis CptnModWhile3.hyps(3) CptnModWhile3.hyps(4) 
           CptnModWhile3.hyps(5) CptnModWhile3.hyps(8) le_cases)
   qed
next
  case (CptnModCatch2 \<Gamma> P0 s xs ys zs P1) 
  obtain n where n:"(n, \<Gamma>, (P0, s) # xs) \<in> cptn_mod_nest_call" using CptnModCatch2(2) by auto
   also obtain m where m:"(m, \<Gamma>, (LanguageCon.com.Skip, snd (last ((P0, s) # xs))) # ys) \<in> cptn_mod_nest_call"
     using CptnModCatch2(5) by auto
   ultimately show ?case
   proof (cases "n\<ge>m") 
     case True thus ?thesis  
       using cptn_mod_nest_mono[of m \<Gamma> _ n] m n 
             CptnModCatch2 cptn_mod_nest_call.CptnModNestCatch2 by blast
   next  
     case False 
     thus ?thesis
       using cptn_mod_nest_mono[of n \<Gamma> _ m] m n CptnModCatch2 
             cptn_mod_nest_call.CptnModNestCatch2 le_cases3 by blast      
   qed
next
  case (CptnModCatch3 \<Gamma> P0 s xs s' ys zs P1) 
   obtain n where n:"(n, \<Gamma>, (P0, Normal s) # xs) \<in> cptn_mod_nest_call" 
     using CptnModCatch3(2) by auto
   also obtain m where m:"(m, \<Gamma>, (ys, snd (last ((P0, Normal s) # xs))) # zs) \<in> cptn_mod_nest_call"
     using CptnModCatch3(6) by auto
   ultimately show ?case
   proof (cases "n\<ge>m") 
     case True thus ?thesis  
       using cptn_mod_nest_mono[of m \<Gamma> _ n] m n CptnModCatch3 cptn_mod_nest_call.CptnModNestCatch3
       by blast
   next  
     case False 
     thus ?thesis
       using cptn_mod_nest_mono[of n \<Gamma> _ m] m n CptnModCatch3 
             cptn_mod_nest_call.CptnModNestCatch3 le_cases3
      proof -
        have f1: "\<not> n \<le> m \<or> (m, \<Gamma>, (P0, Normal s) # xs) \<in> cptn_mod_nest_call"
          using \<open>\<And>cfs. \<lbrakk>(n, \<Gamma>, cfs) \<in> cptn_mod_nest_call; n \<le> m\<rbrakk> \<Longrightarrow> (m, \<Gamma>, cfs) \<in> cptn_mod_nest_call\<close> n by presburger
        have "n \<le> m"
          using False by auto
        then have "(m, \<Gamma>, (P0, Normal s) # xs) \<in> cptn_mod_nest_call"
          using f1 by meson
        then show ?thesis
          by (metis (no_types) \<open>P1 = map (lift_catch ys) xs @ (ys, snd (last ((P0, Normal s) # xs))) # zs\<close> \<open>fst (last ((P0, Normal s) # xs)) = LanguageCon.com.Throw\<close> \<open>snd (last ((P0, Normal s) # xs)) = Normal s'\<close> cptn_mod_nest_call.CptnModNestCatch3 m)
      qed      
   qed
 qed(fastforce intro: cptn_mod_nest_call.intros)+

lemma cptn_mod_same_n:
  assumes a0:"(\<Gamma>,cfs)\<in> cptn_mod" 
  shows "\<exists>n. (n,\<Gamma>,cfs) \<in>  cptn_mod_nest_call"
proof -
 show ?thesis using  cptn_mod_cptn_mod_nest
 by (metis a0 )
qed

lemma cptn_mod_same_n1:
  assumes a0:"(\<Gamma>,cfs)\<in> cptn_mod" and 
          a1:"(\<Gamma>,cfs1)\<in> cptn_mod"
  shows "\<exists>n. (n,\<Gamma>,cfs) \<in>  cptn_mod_nest_call \<and> (n,\<Gamma>,cfs1) \<in>  cptn_mod_nest_call"
proof -
 show ?thesis using cptn_mod_nest_mono cptn_mod_cptn_mod_nest
 by (metis a0 a1 cptn_mod_nest_mono2 leI)
qed

lemma cptn_mod_eq_cptn_mod_nest:
  "(\<Gamma>,cfs)\<in> cptn_mod \<longleftrightarrow> (\<exists>n. (n,\<Gamma>,cfs) \<in>  cptn_mod_nest_call)"
  using cptn_mod_cptn_mod_nest cptn_mod_nest_cptn_mod by auto

lemma cptn_mod_eq_cptn_mod_nest':
  "\<exists>n. ((\<Gamma>,cfs)\<in> cptn_mod \<longleftrightarrow> (n,\<Gamma>,cfs) \<in>  cptn_mod_nest_call)"
  using cptn_mod_eq_cptn_mod_nest by auto

lemma cptn_mod_eq_cptn_mod_nest1:
  "(\<Gamma>,cfs)\<in> cptn_mod = (\<exists>n. (n,\<Gamma>,cfs) \<in>  cptn_mod_nest_call)"
  using cptn_mod_cptn_mod_nest cptn_mod_nest_cptn_mod by auto


lemma cptn_eq_cptn_mod_nest:
  "(\<Gamma>,cfs)\<in> cptn = (\<exists>n. (n,\<Gamma>,cfs) \<in>  cptn_mod_nest_call)"
  using cptn_eq_cptn_mod_set cptn_mod_cptn_mod_nest cptn_mod_nest_cptn_mod by blast

subsection \<open>computation on nested calls limit\<close>
subsection \<open>Elimination theorems\<close>
lemma elim_cptn_mod_nest_step_c:
 assumes a0:"(n,\<Gamma>,cfg) \<in>  cptn_mod_nest_call" and
         a1:"cfg = (P,s)#(Q,t)#cfg1"         
 shows "\<Gamma>\<turnstile>\<^sub>c (P,toSeq s) \<rightarrow> (Q,toSeq t) \<or> \<Gamma>\<turnstile>\<^sub>c (P,s) \<rightarrow>\<^sub>e (Q,t)"
proof-
  have "(\<Gamma>,cfg) \<in>  cptn" using a0 cptn_mod_nest_cptn_mod
    using cptn_eq_cptn_mod_set by auto 
  then have "\<Gamma>\<turnstile>\<^sub>c (P,s) \<rightarrow>\<^sub>c\<^sub>e (Q,t)" using a1
    by (metis cptn_elim_cases(2))
  thus ?thesis
    using step_ce_not_step_e_step_c by blast  
qed

lemma elim_cptn_mod_nest_call_env:
 assumes a0:"(n,\<Gamma>,cfg) \<in>  cptn_mod_nest_call" and
         a1:"cfg = (P,s)#(P,t)#cfg1"  and
         a2:"\<forall>f. \<Gamma> f = Some (LanguageCon.com.Call f) \<and> 
                 (\<exists>sn. s = Normal sn) \<and> s = t \<longrightarrow> SmallStepCon.redex P \<noteq> LanguageCon.com.Call f"
 shows "(n,\<Gamma>,(P,t)#cfg1) \<in>  cptn_mod_nest_call"
 using a0 a1 a2
proof (induct arbitrary: P cfg1 s t rule:cptn_mod_nest_call.induct ) 
case (CptnModNestSeq1 n \<Gamma> P0 sa xs zs P1)
   then obtain xs' where "xs =  (P0, t)#xs'" unfolding lift_def by fastforce
   then have step:"(n, \<Gamma>, (P0, t) # xs') \<in> cptn_mod_nest_call" using CptnModNestSeq1 by fastforce        
   have "(P, t) = lift P1 (P0, t) \<and> cfg1 = map (lift P1) xs'"
      using CptnModNestSeq1.hyps(3) CptnModNestSeq1.prems(1) \<open>xs = (P0, t) # xs'\<close> by auto
    then have "(n, \<Gamma>, (LanguageCon.com.Seq P0 P1, t) # cfg1) \<in> cptn_mod_nest_call"
      by (meson cptn_mod_nest_call.CptnModNestSeq1 local.step)
    then show ?case
      using CptnModNestSeq1.prems(1) by fastforce  
next
  case (CptnModNestSeq2 n \<Gamma> P0 sa xs P1 ys zs) 
  thus ?case 
  proof (induct xs)
    case Nil thus ?case using Nil.prems(6) Nil.prems(7) by fastforce
  next
    case (Cons x xs') 
    then have x:"x=(P0,t)" 
    proof-
      have "zs=(Seq P0 P1,t)#cfg1" using Cons by fastforce
      thus ?thesis using Cons(7) unfolding lift_def
      proof -
        assume "zs = map (\<lambda>a. case a of (P, s) \<Rightarrow> (LanguageCon.com.Seq P P1, s)) (x # xs') @ 
                     (P1, snd (last ((P0, sa) # x # xs'))) # ys"
        then have "LanguageCon.com.Seq (fst x) P1 = LanguageCon.com.Seq P0 P1 \<and> snd x = t"
          by (simp add: \<open>zs = (LanguageCon.com.Seq P0 P1, t) # cfg1\<close> case_prod_beta)
        then show ?thesis
          by fastforce
      qed 
    qed
    then have step:"(n, \<Gamma>, (P0, t) # xs') \<in> cptn_mod_nest_call" using Cons by force         
    have "fst (last ((P0, t) # xs')) = LanguageCon.com.Skip"
      using Cons.prems(3) \<open>x = (P0, t)\<close> by force
    then show ?case
      using Cons.prems(4) Cons.prems(6) CptnModNestSeq2.prems(1) x 
            cptn_mod_nest_call.CptnModNestSeq2 local.step by fastforce
  qed          
next 
  case (CptnModNestSeq3 n \<Gamma> P0 sa xs s' ys zs P1) 
  thus ?case 
  proof (induct xs)
    case Nil thus ?case using Nil.prems(6) Nil.prems(7) by force
  next
    case (Cons x xs') 
    then have x:"x=(P0,t)" 
    proof-
      have zs:"zs=(Seq P0 P1,t)#cfg1" using Cons by fastforce
      have "(LanguageCon.com.Seq (fst x) P1, snd x) = lift P1 x"
         by (simp add: lift_def prod.case_eq_if)
      then have "LanguageCon.com.Seq (fst x) P1 = LanguageCon.com.Seq P0 P1 \<and> snd x = t"
         using Cons.prems(7) zs by force
      then show ?thesis
          by fastforce                
    qed
    then have step:"(n, \<Gamma>, (P0, t) # xs') \<in> cptn_mod_nest_call" using Cons by force         
    then obtain t' where t:"t=Normal t'" 
      using Normal_Normal Cons(2) Cons(5) cptn_mod_nest_cptn_mod cptn_eq_cptn_mod_set x
      by (metis snd_eqD)
    then show ?case using x Cons(5) Cons(6) cptn_mod_nest_call.CptnModNestSeq3 step
    proof -
      have "last ((P0, Normal t') # xs') = last ((P0, Normal sa) # x # xs')"
        using t x by force
      then have h:"fst (last ((P0, Normal t') # xs')) = LanguageCon.com.Throw"
        using Cons.prems(3) by presburger
      then show ?thesis
        using Cons.prems(4) Cons.prems(5) Cons.prems(7) 
              CptnModNestSeq3.prems(1) 
              cptn_mod_nest_call.CptnModNestSeq3[OF local.step[simplified t]] 
              t x
         by fastforce
    qed       
  qed       
next
  case (CptnModNestCatch1 n \<Gamma> P0 s xs zs P1) 
   then obtain xs' where "xs =  (P0, t)#xs'" unfolding lift_catch_def by fastforce
   then have step:"(n, \<Gamma>, (P0, t) # xs') \<in> cptn_mod_nest_call" using CptnModNestCatch1 by fastforce        
   have "(P, t) = lift_catch P1 (P0, t) \<and> cfg1 = map (lift_catch P1) xs'"
      using CptnModNestCatch1.hyps(3) CptnModNestCatch1.prems(1) \<open>xs = (P0, t) # xs'\<close> by auto
    then have "(n, \<Gamma>, (Catch P0 P1, t) # cfg1) \<in> cptn_mod_nest_call"
      by (meson cptn_mod_nest_call.CptnModNestCatch1 local.step)
    then show ?case
      using CptnModNestCatch1.prems(1) by fastforce  
next
  case (CptnModNestCatch2 n \<Gamma> P0 sa xs ys zs P1) 
  thus ?case 
  proof (induct xs)
    case Nil thus ?case using Nil.prems(6) Nil.prems(7) by force
  next
    case (Cons x xs') 
    then have x:"x=(P0,t)" 
    proof-
      have zs:"zs=(Catch P0 P1,t)#cfg1" using Cons by fastforce
      have "(LanguageCon.com.Catch (fst x) P1, snd x) = lift_catch P1 x"
         by (simp add: lift_catch_def prod.case_eq_if)
      then have "LanguageCon.com.Catch (fst x) P1 = LanguageCon.com.Catch P0 P1 \<and> snd x = t"
         using Cons.prems(6) zs by fastforce           
      then show ?thesis
          by fastforce                
    qed
    then have step:"(n, \<Gamma>, (P0, t) # xs') \<in> cptn_mod_nest_call" using Cons by force             
    have "fst (last ((P0, t) # xs')) = LanguageCon.com.Skip"
      using Cons.prems(3) x by auto
    then show ?case
      using Cons.prems(4) Cons.prems(6) CptnModNestCatch2.prems(1) 
            cptn_mod_nest_call.CptnModNestCatch2 local.step x by fastforce 
  qed          
next
  case (CptnModNestCatch3 n \<Gamma> P0 sa xs s' P1 ys zs) 
  thus ?case 
  proof (induct xs)
    case Nil thus ?case using Nil.prems(6) Nil.prems(7) by force
  next
    case (Cons x xs')
    then have x:"x=(P0,t)" 
    proof-
      have zs:"zs=(Catch P0 P1,t)#cfg1" using Cons by fastforce
      thus ?thesis using Cons(8) lift_catch_def unfolding lift_def
      proof -
        assume "zs = map (lift_catch P1) (x # xs') @ (P1, snd (last ((P0, Normal sa) # x # xs'))) # ys"
        then have "LanguageCon.com.Catch (fst x) P1 = LanguageCon.com.Catch P0 P1 \<and> snd x = t"
          by (simp add: case_prod_unfold lift_catch_def zs)          
        then show ?thesis
          by fastforce
      qed 
    qed
    then have step:"(n, \<Gamma>, (P0, t) # xs') \<in> cptn_mod_nest_call" using Cons by force
    then obtain t' where t:"t=Normal t'" 
      using Normal_Normal Cons(2) Cons(5) cptn_mod_nest_cptn_mod cptn_eq_cptn_mod_set x
      by (metis snd_eqD)
    then show ?case 
      using cptn_mod_nest_call.CptnModNestCatch3[OF local.step[simplified t]]
          Cons.prems(3) Cons.prems(4) Cons.prems(7) CptnModNestCatch3.hyps(4) 
             CptnModNestCatch3.hyps(5) CptnModNestCatch3.prems(1) x by fastforce
  qed   
qed(fastforce+)


lemma elim_cptn_mod_nest_not_env_call:
 assumes a0:"(n,\<Gamma>,cfg) \<in>  cptn_mod_nest_call" and
         a1:"cfg = (P,s)#(Q,t)#cfg1" and
         a2:"(\<forall>f. redex P \<noteq> Call f) \<or>  
             SmallStepCon.redex P = LanguageCon.com.Call fn \<and> \<Gamma> fn = None \<or>
            (redex P = Call fn \<and> (\<forall>sa. s\<noteq>Normal sa))"  
 shows "(n,\<Gamma>,(Q,t)#cfg1) \<in>  cptn_mod_nest_call"
 using a0 a1 a2
proof (induct arbitrary: P Q cfg1 s t rule:cptn_mod_nest_call.induct )
case (CptnModNestSeq1 n \<Gamma> P0 s xs zs P1)
   then obtain P0' xs' where "xs =  (P0', t)#xs'" unfolding lift_def by fastforce
   then have step:"(n, \<Gamma>, (P0', t) # xs') \<in> cptn_mod_nest_call" using CptnModNestSeq1 by fastforce        
   have Q:"(Q, t) = lift P1 (P0', t) \<and> cfg1 = map (lift P1) xs'"
     using CptnModNestSeq1.hyps(3) CptnModNestSeq1.prems(1) \<open>xs = (P0', t) # xs'\<close> by auto
   also then have "(n, \<Gamma>, (LanguageCon.com.Seq P0' P1, t) # cfg1) \<in> cptn_mod_nest_call"
     by (meson cptn_mod_nest_call.CptnModNestSeq1 local.step)
   ultimately show ?case
     using CptnModNestSeq1.prems(1)
     by (simp add: Cons_lift Q)   
next
  case (CptnModNestSeq2 n \<Gamma> P0 sa xs P1 ys zs) 
  thus ?case 
  proof (induct xs)
    case Nil thus ?case using Nil.prems(6) Nil.prems(7) by force
  next
    case (Cons x xs')
    then have x:"\<exists>P0'. x=(P0',t)" 
    proof-
      obtain P0'' where zs: "zs=(Seq P0'' P1,t)#cfg1" using Cons(7) Cons(8) 
        unfolding lift_def by (simp add: Cons_eq_append_conv case_prod_beta') 
      thus ?thesis using Cons(7) unfolding lift_def
      proof -
        assume "zs = map (\<lambda>a. case a of (P, s) \<Rightarrow> (LanguageCon.com.Seq P P1, s)) (x # xs') @ 
                     (P1, snd (last ((P0, sa) # x # xs'))) # ys"
        then have "LanguageCon.com.Seq (fst x) P1 = LanguageCon.com.Seq P0'' P1 \<and> snd x = t"
          by (simp add: zs case_prod_beta)
        also have "sa=s" using Cons by fastforce
        ultimately show ?thesis by (meson eq_snd_iff)           
      qed 
    qed
    then obtain P0' where x:"x=(P0',t)" by auto
    then have step:"(n, \<Gamma>, (P0', t) # xs') \<in> cptn_mod_nest_call" using Cons by force
    have "fst (last ((P0', t) # xs')) = LanguageCon.com.Skip"
      using Cons.prems(3) x by force
    then show ?case
      using Cons.prems(4) Cons.prems(6) CptnModNestSeq2.prems(1) x 
           local.step cptn_mod_nest_call.CptnModNestSeq2[of n \<Gamma> P0' t xs' P1 ys] Cons_lift_append
           by (metis (no_types, lifting) last_ConsR list.inject list.simps(3))        
  qed          
next 
  case (CptnModNestSeq3 n \<Gamma> P0 sa xs s' ys zs P1) 
  thus ?case 
  proof (induct xs)
    case Nil thus ?case using Nil.prems(6) Nil.prems(7) by force
  next
    case (Cons x xs') 
    then have x:"\<exists>P0'. x=(P0',t)"
    proof-
      obtain P0' where zs:"zs=(Seq P0' P1,t)#cfg1" using Cons(8) Cons(9) 
        unfolding lift_def
        unfolding lift_def by (simp add: Cons_eq_append_conv case_prod_beta')
      have "(LanguageCon.com.Seq (fst x) P1, snd x) = lift P1 x"
         by (simp add: lift_def prod.case_eq_if)
      then have "LanguageCon.com.Seq (fst x) P1 = LanguageCon.com.Seq P0' P1 \<and> snd x = t"
         using zs by (simp add: Cons.prems(7)) 
      then show ?thesis by (meson eq_snd_iff)                        
    qed
    then obtain P0' where x:"x=(P0',t)" by auto
    then have step:"(n, \<Gamma>, (P0', t) # xs') \<in> cptn_mod_nest_call"
    proof -
      have f1: "LanguageCon.com.Seq P0 P1 = P \<and> Normal sa = s"
        using CptnModNestSeq3.prems(1) by blast
      then have "SmallStepCon.redex P = SmallStepCon.redex P0"
        by (metis SmallStepCon.redex.simps(4))
      then show ?thesis
        using f1 Cons.prems(2) CptnModNestSeq3.prems(2) x by presburger
    qed      
    then obtain t' where t:"t=Normal t'" 
      using Normal_Normal Cons(2) Cons(5) cptn_mod_nest_cptn_mod cptn_eq_cptn_mod_set x
      by (metis snd_eqD)
    then show ?case using x Cons(5) Cons(6) cptn_mod_nest_call.CptnModNestSeq3 step
    proof -
      have "last ((P0', Normal t') # xs') = last ((P0, Normal sa) # x # xs')"
        using t x by force
      also then have "fst (last ((P0', Normal t') # xs')) = LanguageCon.com.Throw"
        using Cons.prems(3) by presburger
      ultimately show ?thesis
        using Cons.prems(4) Cons.prems(5) Cons.prems(7) 
              CptnModNestSeq3.prems(1) cptn_mod_nest_call.CptnModNestSeq3[of n \<Gamma> P0' t' xs' s' ys] 
              local.step t x  Cons_lift_append
      by (metis (no_types, lifting) list.sel(3))               
    qed       
  qed       
next
  case (CptnModNestCatch1 n \<Gamma> P0 s xs zs P1) 
   then obtain P0' xs' where xs:"xs =  (P0', t)#xs'" unfolding lift_catch_def by fastforce
   then have step:"(n, \<Gamma>, (P0', t) # xs') \<in> cptn_mod_nest_call" using CptnModNestCatch1 by fastforce        
   have Q:"(Q, t) = lift_catch P1 (P0', t) \<and> cfg1 = map (lift_catch P1) xs'"
      using CptnModNestCatch1.hyps(3) CptnModNestCatch1.prems(1) xs by auto
    then have "(n, \<Gamma>, (Catch P0' P1, t) # cfg1) \<in> cptn_mod_nest_call"
      by (meson cptn_mod_nest_call.CptnModNestCatch1 local.step)
    then show ?case
      using CptnModNestCatch1.prems(1) by (simp add:Cons_lift_catch Q)
next
  case (CptnModNestCatch2 n \<Gamma> P0 sa xs ys zs P1) 
  thus ?case 
  proof (induct xs)
    case Nil thus ?case using Nil.prems(6) Nil.prems(7) by force
  next
    case (Cons x xs') 
    then have x:"\<exists>P0'. x=(P0',t)" 
    proof-
      obtain P0' where zs:"zs=(Catch P0' P1,t)#cfg1" using Cons unfolding lift_catch_def
        by (simp add: case_prod_unfold)
      have "(LanguageCon.com.Catch (fst x) P1, snd x) = lift_catch P1 x"
         by (simp add: lift_catch_def prod.case_eq_if)
      then have "LanguageCon.com.Catch (fst x) P1 = LanguageCon.com.Catch P0' P1 \<and> snd x = t"
         using Cons.prems(6) zs by fastforce           
      then show ?thesis by (meson eq_snd_iff)          
    qed
    then obtain P0' where x:"x=(P0',t)" by auto
    then have step:"(n, \<Gamma>, (P0', t) # xs') \<in> cptn_mod_nest_call"     
      using Cons.prems(2) CptnModNestCatch2.prems(1) CptnModNestCatch2.prems(2) x by force

    have skip:"fst (last ((P0', t) # xs')) = LanguageCon.com.Skip"
      using Cons.prems(3) x by auto
    show ?case
    proof -
      have "(P, s) # (Q, t) # cfg1 = (LanguageCon.com.Catch P0 P1, sa) # map (lift_catch P1) (x # xs') @ 
              (LanguageCon.com.Skip, snd (last ((P0, sa) # x # xs'))) # ys"
        using CptnModNestCatch2.prems  Cons.prems(6) by auto
      then show ?thesis 
        using Cons_lift_catch_append Cons.prems(4) 
              cptn_mod_nest_call.CptnModNestCatch2[OF local.step skip] last.simps list.distinct(1)
              x 
        by (metis (no_types)  list.sel(3) x)
    qed
  qed          
next
  case (CptnModNestCatch3 n \<Gamma> P0 sa xs s' P1 ys zs) 
  thus ?case 
  proof (induct xs)
    case Nil thus ?case using Nil.prems(6) Nil.prems(7) by force
  next
    case (Cons x xs')
    then have x:"\<exists>P0'. x=(P0',t)" 
    proof-
      obtain P0' where zs:"zs=(Catch P0' P1,t)#cfg1" using Cons unfolding lift_catch_def
        by (simp add: case_prod_unfold)
      thus ?thesis using Cons(8) lift_catch_def unfolding lift_def
      proof -
        assume "zs = map (lift_catch P1) (x # xs') @ (P1, snd (last ((P0, Normal sa) # x # xs'))) # ys"
        then have "LanguageCon.com.Catch (fst x) P1 = LanguageCon.com.Catch P0' P1 \<and> snd x = t"
          by (simp add: case_prod_unfold lift_catch_def zs)          
        then show ?thesis by (meson eq_snd_iff)  
      qed 
    qed
    then obtain P0' where x:"x=(P0',t)" by auto
    then have step:"(n, \<Gamma>, (P0', t) # xs') \<in> cptn_mod_nest_call" using Cons
      using Cons.prems(2) CptnModNestCatch3.prems(1) CptnModNestCatch3.prems(2) x by force
    then obtain t' where t:"t=Normal t'" 
      using Normal_Normal Cons(2) Cons(5) cptn_mod_nest_cptn_mod cptn_eq_cptn_mod_set x
      by (metis snd_eqD)
    then show ?case 
    proof -
      have "last ((P0', Normal t') # xs') = last ((P0, Normal sa) # x # xs')"
        using t x by force
      also then have "fst (last ((P0', Normal t') # xs')) = LanguageCon.com.Throw"
        using Cons.prems(3) by presburger
      ultimately show ?thesis
        using Cons.prems(4) Cons.prems(5) Cons.prems(7) 
              CptnModNestCatch3.prems(1) cptn_mod_nest_call.CptnModNestCatch3[of n \<Gamma> P0' t' xs' s' P1] 
              local.step t x by (metis Cons_lift_catch_append list.sel(3)) 
    qed
  qed
next
case (CptnModNestWhile1 n \<Gamma> P0 s' xs b zs) 
  thus ?case
   using cptn_mod_nest_call.CptnModNestSeq1 list.inject by blast   
next
  case (CptnModNestWhile2 n \<Gamma> P0 s' xs b zs ys)  
  have "(LanguageCon.com.While b P0, Normal s') = (P, s) \<and> 
        (LanguageCon.com.Seq P0 (LanguageCon.com.While b P0), Normal s') # zs = (Q, t) # cfg1"
    using CptnModNestWhile2.prems by fastforce
  then show ?case
    using CptnModNestWhile2.hyps(1) CptnModNestWhile2.hyps(3) 
          CptnModNestWhile2.hyps(5) CptnModNestWhile2.hyps(6) 
          cptn_mod_nest_call.CptnModNestSeq2 by blast
next
  case (CptnModNestWhile3 n \<Gamma> P0 s' xs b zs) thus ?case
    by (metis (no_types) CptnModNestWhile3.hyps(1) CptnModNestWhile3.hyps(3) CptnModNestWhile3.hyps(5) 
                         CptnModNestWhile3.hyps(6) CptnModNestWhile3.hyps(8) CptnModNestWhile3.prems 
                         cptn_mod_nest_call.CptnModNestSeq3 list.inject)  
qed(fastforce+)

lemma elim_cptn_mod_nest_call_n_greater_zero:
 assumes a0:"(n,\<Gamma>,cfg) \<in>  cptn_mod_nest_call" and
         a1:"cfg = (P,Normal s)#(Q,t)#cfg1 \<and> P = Call f \<and> \<Gamma> f = Some Q \<and> P\<noteq>Q"
 shows  "n>0" 
  using a0 a1 by (induct rule:cptn_mod_nest_call.induct, fastforce+)


lemma elim_cptn_mod_nest_call_0_False:
 assumes a0:"(0,\<Gamma>,cfg) \<in>  cptn_mod_nest_call" and
         a1:"cfg = (P,Normal s)#(Q,t)#cfg1 \<and> P = Call f \<and> \<Gamma> f = Some Q \<and> P\<noteq>Q"
shows "PP"
using a0 a1 elim_cptn_mod_nest_call_n_greater_zero 
by fastforce

lemma elim_cptn_mod_nest_call_n_dec1:
 assumes a0:"(n,\<Gamma>,cfg) \<in>  cptn_mod_nest_call" and
         a1:"cfg = (P,Normal s)#(Q,t)#cfg1 \<and> P = Call f \<and> \<Gamma> f = Some Q \<and> t= Normal s \<and> P\<noteq>Q"
 shows "(n-1,\<Gamma>,(Q,t)#cfg1) \<in>  cptn_mod_nest_call"
 using a0 a1 
  by (induct rule:cptn_mod_nest_call.induct,fastforce+)

lemma elim_cptn_mod_nest_call_n_dec:
 assumes a0:"(n,\<Gamma>,(Call f,Normal s)#(the (\<Gamma> f),Normal s)#cfg1) \<in>  cptn_mod_nest_call" and
         a1:"\<Gamma> f = Some Q " and a2:"Call f\<noteq>the (\<Gamma> f)"
       shows "(n-1,\<Gamma>,(the (\<Gamma> f),Normal s)#cfg1) \<in>  cptn_mod_nest_call"
  using elim_cptn_mod_nest_call_n_dec1[OF a0] a1 a2
  by fastforce


lemma elim_cptn_mod_nest_call_n:
 assumes a0:"(n,\<Gamma>,cfg) \<in>  cptn_mod_nest_call" and
         a1:"cfg = (P, s)#(Q,t)#cfg1"          
 shows "(n,\<Gamma>,(Q,t)#cfg1) \<in>  cptn_mod_nest_call"
 using a0 a1 
proof (induct arbitrary: P Q cfg1 s t rule:cptn_mod_nest_call.induct )
case (CptnModNestCall n \<Gamma> bdy sa ys p)
  thus ?case using cptn_mod_nest_mono1 list.inject by blast
next 
case (CptnModNestSeq1 n \<Gamma> P0 s xs zs P1) 
   then obtain P0' xs' where "xs =  (P0', t)#xs'" unfolding lift_def by fastforce
   then have step:"(n, \<Gamma>, (P0', t) # xs') \<in> cptn_mod_nest_call" using CptnModNestSeq1 by fastforce        
   have Q:"(Q, t) = lift P1 (P0', t) \<and> cfg1 = map (lift P1) xs'"
     using CptnModNestSeq1.hyps(3) CptnModNestSeq1.prems(1) \<open>xs = (P0', t) # xs'\<close> by auto
   also then have "(n, \<Gamma>, (LanguageCon.com.Seq P0' P1, t) # cfg1) \<in> cptn_mod_nest_call"
     by (meson cptn_mod_nest_call.CptnModNestSeq1 local.step)
   ultimately show ?case
     using CptnModNestSeq1.prems(1)
     by (simp add: Cons_lift Q)   
next
  case (CptnModNestSeq2 n \<Gamma> P0 sa xs P1 ys zs) 
  thus ?case 
  proof (induct xs)
    case Nil thus ?case using Nil.prems(6) Nil.prems(7) by force
  next
    case (Cons x xs')
    then have x:"\<exists>P0'. x=(P0',t)" 
    proof-
      obtain P0'' where zs: "zs=(Seq P0'' P1,t)#cfg1" using Cons(7) Cons(8) 
        unfolding lift_def by (simp add: Cons_eq_append_conv case_prod_beta') 
      thus ?thesis using Cons(7) unfolding lift_def
      proof -
        assume "zs = map (\<lambda>a. case a of (P, s) \<Rightarrow> (LanguageCon.com.Seq P P1, s)) (x # xs') @ 
                     (P1, snd (last ((P0, sa) # x # xs'))) # ys"
        then have "LanguageCon.com.Seq (fst x) P1 = LanguageCon.com.Seq P0'' P1 \<and> snd x = t"
          by (simp add: zs case_prod_beta)
        also have "sa=s" using Cons by fastforce
        ultimately show ?thesis by (meson eq_snd_iff)           
      qed 
    qed
    then obtain P0' where x:"x=(P0',t)" by auto
    then have step:"(n, \<Gamma>, (P0', t) # xs') \<in> cptn_mod_nest_call" using Cons by force
    have "fst (last ((P0', t) # xs')) = LanguageCon.com.Skip"
      using Cons.prems(3) x by force
    then show ?case
      using Cons.prems(4) Cons.prems(6) CptnModNestSeq2.prems(1) x 
           local.step cptn_mod_nest_call.CptnModNestSeq2[of n \<Gamma> P0' t xs' P1 ys] Cons_lift_append
           by (metis (no_types, lifting) last_ConsR list.inject list.simps(3))        
  qed          
next 
  case (CptnModNestSeq3 n \<Gamma> P0 sa xs s' ys zs P1) 
  thus ?case 
  proof (induct xs)
    case Nil thus ?case using Nil.prems(6) Nil.prems(7) by force
  next
    case (Cons x xs') 
    then have x:"\<exists>P0'. x=(P0',t)"
    proof-
      obtain P0' where zs:"zs=(Seq P0' P1,t)#cfg1" using Cons(8) Cons(9) 
        unfolding lift_def
        unfolding lift_def by (simp add: Cons_eq_append_conv case_prod_beta')
      have "(LanguageCon.com.Seq (fst x) P1, snd x) = lift P1 x"
         by (simp add: lift_def prod.case_eq_if)
      then have "LanguageCon.com.Seq (fst x) P1 = LanguageCon.com.Seq P0' P1 \<and> snd x = t"
         using zs by (simp add: Cons.prems(7)) 
      then show ?thesis by (meson eq_snd_iff)                        
    qed
    then obtain P0' where x:"x=(P0',t)" by auto
    then have step:"(n, \<Gamma>, (P0', t) # xs') \<in> cptn_mod_nest_call" using Cons by fastforce         
    then obtain t' where t:"t=Normal t'" 
      using Normal_Normal Cons(2) Cons(5) cptn_mod_nest_cptn_mod cptn_eq_cptn_mod_set x
      by (metis snd_eqD)
    then show ?case using x Cons(5) Cons(6) cptn_mod_nest_call.CptnModNestSeq3 step
    proof -
      have "last ((P0', Normal t') # xs') = last ((P0, Normal sa) # x # xs')"
        using t x by force
      also then have "fst (last ((P0', Normal t') # xs')) = LanguageCon.com.Throw"
        using Cons.prems(3) by presburger
      ultimately show ?thesis
        using Cons.prems(4) Cons.prems(5) Cons.prems(7) 
              CptnModNestSeq3.prems(1) cptn_mod_nest_call.CptnModNestSeq3[of n \<Gamma> P0' t' xs' s' ys] 
              local.step t x  Cons_lift_append
      by (metis (no_types, lifting) list.sel(3))               
    qed       
  qed       
next
  case (CptnModNestCatch1 n \<Gamma> P0 s xs zs P1) 
   then obtain P0' xs' where xs:"xs =  (P0', t)#xs'" unfolding lift_catch_def by fastforce
   then have step:"(n, \<Gamma>, (P0', t) # xs') \<in> cptn_mod_nest_call" using CptnModNestCatch1 by fastforce        
   have Q:"(Q, t) = lift_catch P1 (P0', t) \<and> cfg1 = map (lift_catch P1) xs'"
      using CptnModNestCatch1.hyps(3) CptnModNestCatch1.prems(1) xs by auto
    then have "(n, \<Gamma>, (Catch P0' P1, t) # cfg1) \<in> cptn_mod_nest_call"
      by (meson cptn_mod_nest_call.CptnModNestCatch1 local.step)
    then show ?case
      using CptnModNestCatch1.prems(1) by (simp add:Cons_lift_catch Q)
next
  case (CptnModNestCatch2 n \<Gamma> P0 sa xs ys zs P1) 
  thus ?case 
  proof (induct xs)
    case Nil thus ?case using Nil.prems(6) Nil.prems(7) by force
  next
    case (Cons x xs') 
    then have x:"\<exists>P0'. x=(P0',t)" 
    proof-
      obtain P0' where zs:"zs=(Catch P0' P1,t)#cfg1" using Cons unfolding lift_catch_def
        by (simp add: case_prod_unfold)
      have "(LanguageCon.com.Catch (fst x) P1, snd x) = lift_catch P1 x"
         by (simp add: lift_catch_def prod.case_eq_if)
      then have "LanguageCon.com.Catch (fst x) P1 = LanguageCon.com.Catch P0' P1 \<and> snd x = t"
         using Cons.prems(6) zs by fastforce           
      then show ?thesis by (meson eq_snd_iff)          
    qed
    then obtain P0' where x:"x=(P0',t)" by auto
    then have step:"(n, \<Gamma>, (P0', t) # xs') \<in> cptn_mod_nest_call" using Cons by fastforce             
    have skip:"fst (last ((P0', t) # xs')) = LanguageCon.com.Skip"
      using Cons.prems(3) x by auto
    show ?case
    proof -
      have "(P, s) # (Q, t) # cfg1 = (LanguageCon.com.Catch P0 P1, sa) # map (lift_catch P1) (x # xs') @ 
              (LanguageCon.com.Skip, snd (last ((P0, sa) # x # xs'))) # ys"
        using CptnModNestCatch2.prems  Cons.prems(6) by auto
      then show ?thesis 
        using Cons_lift_catch_append Cons.prems(4) 
              cptn_mod_nest_call.CptnModNestCatch2[OF local.step skip] last.simps list.distinct(1)
              x 
        by (metis (no_types)  list.sel(3) x)
    qed
  qed          
next
  case (CptnModNestCatch3 n \<Gamma> P0 sa xs s' P1 ys zs) 
  thus ?case 
  proof (induct xs)
    case Nil thus ?case using Nil.prems(6) Nil.prems(7) by force
  next
    case (Cons x xs')
    then have x:"\<exists>P0'. x=(P0',t)" 
    proof-
      obtain P0' where zs:"zs=(Catch P0' P1,t)#cfg1" using Cons unfolding lift_catch_def
        by (simp add: case_prod_unfold)
      thus ?thesis using Cons(8) lift_catch_def unfolding lift_def
      proof -
        assume "zs = map (lift_catch P1) (x # xs') @ (P1, snd (last ((P0, Normal sa) # x # xs'))) # ys"
        then have "LanguageCon.com.Catch (fst x) P1 = LanguageCon.com.Catch P0' P1 \<and> snd x = t"
          by (simp add: case_prod_unfold lift_catch_def zs)          
        then show ?thesis by (meson eq_snd_iff)  
      qed 
    qed
    then obtain P0' where x:"x=(P0',t)" by auto
    then have step:"(n, \<Gamma>, (P0', t) # xs') \<in> cptn_mod_nest_call" using Cons by fastforce
    then obtain t' where t:"t=Normal t'" 
      using Normal_Normal Cons(2) Cons(5) cptn_mod_nest_cptn_mod cptn_eq_cptn_mod_set x
      by (metis snd_eqD)
    then show ?case 
    proof -
      have "last ((P0', Normal t') # xs') = last ((P0, Normal sa) # x # xs')"
        using t x by force
      also then have "fst (last ((P0', Normal t') # xs')) = LanguageCon.com.Throw"
        using Cons.prems(3) by presburger
      ultimately show ?thesis
        using Cons.prems(4) Cons.prems(5) Cons.prems(7) 
              CptnModNestCatch3.prems(1) cptn_mod_nest_call.CptnModNestCatch3[of n \<Gamma> P0' t' xs' s' P1] 
              local.step t x by (metis Cons_lift_catch_append list.sel(3)) 
    qed
  qed
next
case (CptnModNestWhile1 n \<Gamma> P0 s' xs b zs) 
  thus ?case
   using cptn_mod_nest_call.CptnModNestSeq1 list.inject by blast   
next
  case (CptnModNestWhile2 n \<Gamma> P0 s' xs b zs ys)  
  have "(LanguageCon.com.While b P0, Normal s') = (P, s) \<and> 
        (LanguageCon.com.Seq P0 (LanguageCon.com.While b P0), Normal s') # zs = (Q, t) # cfg1"
    using CptnModNestWhile2.prems by fastforce
  then show ?case
    using CptnModNestWhile2.hyps(1) CptnModNestWhile2.hyps(3) 
          CptnModNestWhile2.hyps(5) CptnModNestWhile2.hyps(6) 
          cptn_mod_nest_call.CptnModNestSeq2 by blast
next
  case (CptnModNestWhile3 n \<Gamma> P0 s' xs b zs) thus ?case
    by (metis (no_types) CptnModNestWhile3.hyps(1) CptnModNestWhile3.hyps(3) CptnModNestWhile3.hyps(5) 
                         CptnModNestWhile3.hyps(6) CptnModNestWhile3.hyps(8) CptnModNestWhile3.prems 
                         cptn_mod_nest_call.CptnModNestSeq3 list.inject)  
qed (fastforce+) 

lemma dropcptn_is_cptn1 [rule_format,elim!]:
  "\<forall>j<length c. (n,\<Gamma>,c) \<in> cptn_mod_nest_call \<longrightarrow> (n,\<Gamma>, drop j c) \<in> cptn_mod_nest_call"
proof -
  {fix j
   assume "j<length c \<and> (n,\<Gamma>,c) \<in> cptn_mod_nest_call"
   then have "(n,\<Gamma>, drop j c) \<in> cptn_mod_nest_call" 
   proof(induction j arbitrary: c)
     case 0 then show ?case by auto
   next
     case (Suc j) 
     then obtain a b c' where "c=a#b#c'"
       by (metis (no_types, hide_lams) Suc_less_eq length_Cons list.exhaust list.size(3) not_less0)
     then also have "j<length (b#c')" using Suc by auto
     ultimately moreover have "(n, \<Gamma>, drop j (b # c')) \<in> cptn_mod_nest_call" using elim_cptn_mod_nest_call_n[of n \<Gamma> c] Suc
       by (metis surj_pair) 
     ultimately show ?case by auto  
   qed
 } thus ?thesis by auto 
qed

definition min_call where
"min_call n \<Gamma> cfs \<equiv> (n,\<Gamma>,cfs) \<in>  cptn_mod_nest_call \<and> (\<forall>m<n. \<not>((m,\<Gamma>,cfs) \<in>  cptn_mod_nest_call))"

lemma minimum_nest_call:
  "(m,\<Gamma>,cfs) \<in> cptn_mod_nest_call \<Longrightarrow>
   \<exists>n. min_call n \<Gamma> cfs"
unfolding min_call_def
proof (induct arbitrary: m rule:cptn_mod_nest_call.induct) 
 case (CptnModNestOne) thus ?case using cptn_mod_nest_call.CptnModNestOne by blast 
next
  case (CptnModNestEnv \<Gamma> P s t n xs) 
  then have "\<not> \<Gamma>\<turnstile>\<^sub>c (P, toSeq s) \<rightarrow> (P, toSeq t)" 
   using mod_env_not_component step_change_p_or_eq_s by blast 
  then obtain min_n where min:"(min_n, \<Gamma>, (P, t) # xs) \<in> cptn_mod_nest_call \<and> 
                             (\<forall>m<min_n.  (m, \<Gamma>, (P, t) # xs) \<notin> cptn_mod_nest_call)" 
    using CptnModNestEnv by blast
  then have  "(min_n, \<Gamma>, (P,s)#(P, t) # xs) \<in> cptn_mod_nest_call"     
    using cptn_mod_nest_call.CptnModNestEnv CptnModNestEnv by blast
  also have "(\<forall>m<min_n. (m, \<Gamma>, (P, s)#(P, t) # xs) \<notin> cptn_mod_nest_call)"
    using elim_cptn_mod_nest_call_n min by fastforce    
  ultimately show ?case by auto  
next
  case (CptnModNestSkip \<Gamma> P s t n xs)    
  then obtain min_n where 
     min:"(min_n, \<Gamma>, (LanguageCon.com.Skip, t) # xs) \<in> cptn_mod_nest_call \<and>
        (\<forall>m<min_n. (m, \<Gamma>, (LanguageCon.com.Skip, t) # xs) \<notin> cptn_mod_nest_call)" 
    by auto
  then have "(min_n, \<Gamma>, (P,s)#(LanguageCon.com.Skip, t) # xs) \<in> cptn_mod_nest_call"
    using cptn_mod_nest_call.CptnModNestSkip CptnModNestSkip by blast
  also have "(\<forall>m<min_n. (m, \<Gamma>, (P, s)#(LanguageCon.com.Skip, t) # xs) \<notin> cptn_mod_nest_call)"
    using elim_cptn_mod_nest_call_n min by blast      
  ultimately show ?case by fastforce   
next
  case (CptnModNestThrow \<Gamma> P s t n xs) thus ?case    
    using elim_cptn_mod_nest_call_n[OF CptnModNestThrow(5)] 
     by (metis (no_types, lifting) cptn_mod_nest_call.CptnModNestThrow elim_cptn_mod_nest_call_n)    
next
  case (CptnModNestCondT n \<Gamma> P0 s xs b P1) thus ?case
    by (meson cptn_mod_nest_call.CptnModNestCondT elim_cptn_mod_nest_call_n)
next
  case (CptnModNestCondF n \<Gamma> P1 s xs b P0) thus ?case
    by (meson cptn_mod_nest_call.CptnModNestCondF elim_cptn_mod_nest_call_n)
next
  case (CptnModNestSeq1 n \<Gamma> P s xs zs Q) thus ?case
    by (metis (no_types, lifting) Seq_P_Not_finish cptn_mod_nest_call.CptnModNestSeq1 div_seq_nest)
next
  case (CptnModNestSeq2 n \<Gamma> P s xs Q ys zs) 
  then obtain min_p where 
     min_p:"(min_p, \<Gamma>, (P,  s) # xs) \<in> cptn_mod_nest_call \<and>
        (\<forall>m<min_p. (m, \<Gamma>, (P, s) # xs) \<notin> cptn_mod_nest_call)" 
    by auto 
  from CptnModNestSeq2(5) obtain min_q where
    min_q:"(min_q, \<Gamma>, (Q, snd (last ((P, s) # xs))) # ys) \<in> cptn_mod_nest_call \<and>
        (\<forall>m<min_q. (m, \<Gamma>, (Q, snd (last ((P, s) # xs))) # ys) \<notin> cptn_mod_nest_call)"
  by auto
  thus ?case
  proof(cases "min_p\<ge>min_q")
    case True
    then have "(min_p, \<Gamma>, (Q, snd (last ((P,s) # xs))) # ys) \<in> cptn_mod_nest_call"
      using min_q using cptn_mod_nest_mono by blast 
    then have "(min_p, \<Gamma>, (Seq P Q, s) # zs) \<in> cptn_mod_nest_call"
      using conjunct1[OF min_p] cptn_mod_nest_call.CptnModNestSeq2[of min_p \<Gamma> P s xs Q ys zs] 
            CptnModNestSeq2(6)  CptnModNestSeq2(3)
    by blast
    also have "\<forall>m<min_p. (m, \<Gamma>,(Seq P Q,s) # zs) \<notin> cptn_mod_nest_call"
      by (metis CptnModNestSeq2.hyps(3) CptnModNestSeq2.hyps(6) Seq_P_Ends_Normal div_seq_nest min_p)      
    ultimately show ?thesis by auto
  next
    case False 
    then have "(min_q, \<Gamma>, (P,  s) # xs) \<in> cptn_mod_nest_call"
      using min_p cptn_mod_nest_mono by force 
    then have "(min_q, \<Gamma>, (Seq P Q, s) # zs) \<in> cptn_mod_nest_call"
      using conjunct1[OF min_q] cptn_mod_nest_call.CptnModNestSeq2[of min_q \<Gamma> P s xs Q ys zs] 
            CptnModNestSeq2(6)  CptnModNestSeq2(3)
    by blast
    also have "\<forall>m<min_q. (m, \<Gamma>,(Seq P Q,s) # zs) \<notin> cptn_mod_nest_call"
     proof -
      {fix m
      assume min_m:"m<min_q"
      then have "(m, \<Gamma>,(Seq P Q, s) # zs) \<notin> cptn_mod_nest_call"
      proof -
      {assume ass:"(m, \<Gamma>, (Seq P Q, s) # zs) \<in> cptn_mod_nest_call"
       then obtain xs' s' s'' where 
          m_cptn:"(m, \<Gamma>, (P, s) # xs') \<in> cptn_mod_nest_call \<and> 
                   seq_cond_nest zs Q xs' P s s'' s' \<Gamma> m" 
         using  
          div_seq_nest[of m \<Gamma> "(LanguageCon.com.Seq P Q, s) # zs"]
          by fastforce
       then have "seq_cond_nest zs Q xs' P s s'' s' \<Gamma> m" by auto
       then have ?thesis
         using Seq_P_Ends_Normal[OF CptnModNestSeq2(6) CptnModNestSeq2(3) ass]
               min_m min_q 
         by (metis last_length)          
      } thus ?thesis by auto
      qed
      }thus ?thesis by auto
    qed  
    ultimately show ?thesis by auto
  qed
next
  case (CptnModNestSeq3 n \<Gamma> P s xs s' ys zs Q) 
  then obtain min_p where 
     min_p:"(min_p, \<Gamma>, (P, Normal s) # xs) \<in> cptn_mod_nest_call \<and>
        (\<forall>m<min_p. (m, \<Gamma>, (P, Normal s) # xs) \<notin> cptn_mod_nest_call)" 
    by auto 
  from CptnModNestSeq3(6) obtain min_q where
    min_q:"(min_q, \<Gamma>, (Throw, Normal s') # ys) \<in> cptn_mod_nest_call \<and>
        (\<forall>m<min_q. (m, \<Gamma>, (Throw, Normal s') # ys) \<notin> cptn_mod_nest_call)"
  by auto
  thus ?case
  proof(cases "min_p\<ge>min_q")
    case True 
    then have "(min_p, \<Gamma>, (Throw, Normal s') # ys) \<in> cptn_mod_nest_call"
      using min_q using cptn_mod_nest_mono by blast 
    then have "(min_p, \<Gamma>, (Seq P Q, Normal s) # zs) \<in> cptn_mod_nest_call"
      using conjunct1[OF min_p] cptn_mod_nest_call.CptnModNestSeq3[of min_p \<Gamma> P s xs s' ys zs Q] 
            CptnModNestSeq3(4)  CptnModNestSeq3(3) CptnModNestSeq3(7)
    by blast
    also have "\<forall>m<min_p. (m, \<Gamma>,(Seq P Q,Normal s) # zs) \<notin> cptn_mod_nest_call"
      by (metis CptnModNestSeq3.hyps(3) CptnModNestSeq3.hyps(4) CptnModNestSeq3.hyps(7) Seq_P_Ends_Abort div_seq_nest min_p)
    ultimately show ?thesis by auto
  next
    case False
    then have "(min_q, \<Gamma>, (P,  Normal s) # xs) \<in> cptn_mod_nest_call"
      using min_p cptn_mod_nest_mono by force 
    then have "(min_q, \<Gamma>, (Seq P Q, Normal s) # zs) \<in> cptn_mod_nest_call"
      using conjunct1[OF min_q] cptn_mod_nest_call.CptnModNestSeq3[of min_q \<Gamma> P s xs s' ys zs Q] 
            CptnModNestSeq3(4)  CptnModNestSeq3(3) CptnModNestSeq3(7)
    by blast
    also have "\<forall>m<min_q. (m, \<Gamma>,(Seq P Q,Normal s) # zs) \<notin> cptn_mod_nest_call"
      by (metis CptnModNestSeq3.hyps(3) CptnModNestSeq3.hyps(4) CptnModNestSeq3.hyps(7) Seq_P_Ends_Abort div_seq_nest min_q)     
    ultimately show ?thesis by auto
  qed 
next
  case (CptnModNestWhile1 n \<Gamma> P s xs b zs) 
  then obtain min_n where 
     min:"(min_n, \<Gamma>, (P, Normal s) # xs) \<in> cptn_mod_nest_call \<and>
        (\<forall>m<min_n. (m, \<Gamma>, (P, Normal s) # xs) \<notin> cptn_mod_nest_call)" 
    by auto
  then have "(min_n, \<Gamma>, (While b P, Normal s) # (Seq P (While b P), Normal s) # zs) \<in> cptn_mod_nest_call"
    using cptn_mod_nest_call.CptnModNestWhile1[of min_n \<Gamma> P s xs b zs] CptnModNestWhile1
    by meson 
  also have "\<forall>m<min_n. (m, \<Gamma>,(While b P, Normal s) # (Seq P (While b P), Normal s) # zs) \<notin> cptn_mod_nest_call"
    by (metis CptnModNestWhile1.hyps(4) Seq_P_Not_finish div_seq_nest elim_cptn_mod_nest_call_n min) 
  ultimately show ?case by auto
next
  case (CptnModNestWhile2 n \<Gamma> P s xs b zs ys) 
  then obtain min_n_p where 
     min_p:"(min_n_p, \<Gamma>, (P, Normal s) # xs) \<in> cptn_mod_nest_call \<and>
        (\<forall>m<min_n_p. (m, \<Gamma>, (P, Normal s) # xs) \<notin> cptn_mod_nest_call)" 
    by auto
  from CptnModNestWhile2 obtain min_n_w where
     min_w:"(min_n_w, \<Gamma>, (LanguageCon.com.While b P, snd (last ((P, Normal s) # xs))) # ys) \<in> cptn_mod_nest_call \<and>
        (\<forall>m<min_n_w. (m, \<Gamma>, (LanguageCon.com.While b P, snd (last ((P, Normal s) # xs))) # ys)
               \<notin> cptn_mod_nest_call)"
    by auto
  thus ?case 
  proof (cases "min_n_p\<ge>min_n_w")
    case True 
    then have "(min_n_p, \<Gamma>, 
      (LanguageCon.com.While b P, snd (last ((P, Normal s) # xs))) # ys) \<in> cptn_mod_nest_call"
      using min_w using cptn_mod_nest_mono by blast 
    then have "(min_n_p, \<Gamma>, (While b P, Normal s) # (Seq P (While b P), Normal s) # zs) \<in> cptn_mod_nest_call"
      using min_p cptn_mod_nest_call.CptnModNestWhile2[of min_n_p \<Gamma> P s xs b zs] CptnModNestWhile2
      by blast
    also have "\<forall>m<min_n_p. (m, \<Gamma>,(While b P, Normal s) # (Seq P (While b P), Normal s) # zs) \<notin> cptn_mod_nest_call"
      by (metis CptnModNestWhile2.hyps(3) CptnModNestWhile2.hyps(5) 
                Seq_P_Ends_Normal div_seq_nest elim_cptn_mod_nest_call_n min_p)    
    ultimately show ?thesis by auto  
  next
    case False
    then have False:"min_n_p<min_n_w" by auto
    then have "(min_n_w, \<Gamma>, (P, Normal s) # xs) \<in> cptn_mod_nest_call"
      using min_p  cptn_mod_nest_mono by force 
    then have "(min_n_w, \<Gamma>, (While b P, Normal s) # (Seq P (While b P), Normal s) # zs) \<in> cptn_mod_nest_call"
      using min_w min_p cptn_mod_nest_call.CptnModNestWhile2[of min_n_w \<Gamma> P s xs b zs] CptnModNestWhile2
      by blast
    also have "\<forall>m<min_n_w. (m, \<Gamma>,(While b P, Normal s) # (Seq P (While b P), Normal s) # zs) \<notin> cptn_mod_nest_call"      
    proof -
      {fix m
      assume min_m:"m<min_n_w"
      then have "(m, \<Gamma>,(While b P, Normal s) # (Seq P (While b P), Normal s) # zs) \<notin> cptn_mod_nest_call"
      proof -
      {assume "(m, \<Gamma>,(While b P, Normal s) # (Seq P (While b P), Normal s) # zs) \<in> cptn_mod_nest_call"
       then have a1:"(m, \<Gamma>,(Seq P (While b P), Normal s) # zs) \<in> cptn_mod_nest_call"      
         using elim_cptn_mod_nest_not_env_call by fastforce
       then obtain xs' s' s'' where 
          m_cptn:"(m, \<Gamma>, (P, Normal s) # xs') \<in> cptn_mod_nest_call  \<and> 
                   seq_cond_nest zs (While b P) xs' P (Normal s) s'' s' \<Gamma> m" 
         using  
          div_seq_nest[of m \<Gamma> "(LanguageCon.com.Seq P (LanguageCon.com.While b P), Normal s) # zs"]
          by fastforce
       then have "seq_cond_nest zs (While b P) xs' P (Normal s) s'' s' \<Gamma> m" by auto
       then have ?thesis unfolding seq_cond_nest_def
         by (metis CptnModNestWhile2.hyps(3) CptnModNestWhile2.hyps(5) Seq_P_Ends_Normal a1 last_length m_cptn min_m min_w)           
     } thus ?thesis by auto
     qed
     }thus ?thesis by auto
    qed
    ultimately show ?thesis by auto
  qed
next
  case (CptnModNestWhile3 n \<Gamma> P s xs b s' ys zs) 
  then obtain min_n_p where 
     min_p:"(min_n_p, \<Gamma>, (P, Normal s) # xs) \<in> cptn_mod_nest_call \<and>
        (\<forall>m<min_n_p. (m, \<Gamma>, (P, Normal s) # xs) \<notin> cptn_mod_nest_call)" 
    by auto
  from CptnModNestWhile3 obtain min_n_w where
     min_w:"(min_n_w, \<Gamma>, (Throw, snd (last ((P, Normal s) # xs))) # ys) \<in> cptn_mod_nest_call \<and>
        (\<forall>m<min_n_w. (m, \<Gamma>, (Throw, snd (last ((P, Normal s) # xs))) # ys)
               \<notin> cptn_mod_nest_call)"
    by auto
  thus ?case 
  proof (cases "min_n_p\<ge>min_n_w")
    case True 
    then have "(min_n_p, \<Gamma>, 
      (Throw, snd (last ((P, Normal s) # xs))) # ys) \<in> cptn_mod_nest_call"
      using min_w using cptn_mod_nest_mono by blast 
    then have "(min_n_p, \<Gamma>, (While b P, Normal s) # (Seq P (While b P), Normal s) # zs) \<in> cptn_mod_nest_call"
      using min_p cptn_mod_nest_call.CptnModNestWhile3[of min_n_p \<Gamma> P s xs b s' ys zs] 
            CptnModNestWhile3
      by fastforce
    also have "\<forall>m<min_n_p. (m, \<Gamma>,(While b P, Normal s) # (Seq P (While b P), Normal s) # zs) \<notin> cptn_mod_nest_call"
      by (metis CptnModNestWhile3.hyps(3) CptnModNestWhile3.hyps(5) CptnModNestWhile3.hyps(8) 
            Seq_P_Ends_Abort div_seq_nest elim_cptn_mod_nest_call_n min_p)    
    ultimately show ?thesis by auto  
  next
    case False
    then have False:"min_n_p<min_n_w" by auto
    then have "(min_n_w, \<Gamma>, (P, Normal s) # xs) \<in> cptn_mod_nest_call"
      using min_p  cptn_mod_nest_mono by force 
    then have "(min_n_w, \<Gamma>, (While b P, Normal s) # (Seq P (While b P), Normal s) # zs) \<in> cptn_mod_nest_call"
      using min_w min_p cptn_mod_nest_call.CptnModNestWhile3[of min_n_w \<Gamma> P s xs b s' ys zs] 
            CptnModNestWhile3
      by fastforce      
    also have "\<forall>m<min_n_w. (m, \<Gamma>,(While b P, Normal s) # (Seq P (While b P), Normal s) # zs) \<notin> cptn_mod_nest_call"
    proof -
      {fix m
      assume min_m:"m<min_n_w"
      then have "(m, \<Gamma>,(While b P, Normal s) # (Seq P (While b P), Normal s) # zs) \<notin> cptn_mod_nest_call"
      proof -
      {assume "(m, \<Gamma>,(While b P, Normal s) # (Seq P (While b P), Normal s) # zs) \<in> cptn_mod_nest_call"
       then have s1:"(m, \<Gamma>,(Seq P (While b P), Normal s) # zs) \<in> cptn_mod_nest_call"      
         using elim_cptn_mod_nest_not_env_call by fastforce
       then obtain xs' s' s'' where 
          m_cptn:"(m, \<Gamma>, (P, Normal s) # xs') \<in> cptn_mod_nest_call  \<and> 
                   seq_cond_nest zs (While b P) xs' P (Normal s) s'' s' \<Gamma> m" 
         using  
          div_seq_nest[of m \<Gamma> "(LanguageCon.com.Seq P (LanguageCon.com.While b P), Normal s) # zs"]
          by fastforce
       then have "seq_cond_nest zs (While b P) xs' P (Normal s) s'' s' \<Gamma> m" by auto
       then have ?thesis unfolding seq_cond_nest_def
         by (metis CptnModNestWhile3.hyps(3) CptnModNestWhile3.hyps(5) CptnModNestWhile3.hyps(8) Seq_P_Ends_Abort s1 m_cptn min_m min_w)       
     } thus ?thesis by auto
     qed
     }thus ?thesis by auto
    qed
    ultimately show ?thesis by auto
  qed
next
  case (CptnModNestCall n \<Gamma> bdy s xs f) thus ?case
  proof -
    { fix nn :: "nat \<Rightarrow> nat"
     obtain nna :: nat where
      ff1: "(nna, \<Gamma>, (bdy, Normal s) # xs) \<in> cptn_mod_nest_call \<and> (\<forall>n. \<not> n < nna \<or> (n, \<Gamma>, (bdy, Normal s) # xs) \<notin> cptn_mod_nest_call)"
      by (meson CptnModNestCall.hyps(2))
    moreover
    { assume "(nn (nn (Suc nna)), \<Gamma>, (bdy, Normal s) # xs) \<in> cptn_mod_nest_call"
      then have "\<not> Suc (nn (nn (Suc nna))) < Suc nna"
        using ff1 by blast
      then have "(nn (Suc nna), \<Gamma>, (LanguageCon.com.Call f, Normal s) # (bdy, Normal s) # xs) \<in> cptn_mod_nest_call \<longrightarrow> (\<exists>n. (n, \<Gamma>, (LanguageCon.com.Call f, Normal s) # (bdy, Normal s) # xs) \<in> cptn_mod_nest_call \<and> 
                (\<not> nn n < n \<or> (nn n, \<Gamma>, (LanguageCon.com.Call f, Normal s) # (bdy, Normal s) # xs) \<notin> cptn_mod_nest_call))"
        using ff1 by (meson CptnModNestCall.hyps(3) CptnModNestCall.hyps(4) cptn_mod_nest_call.CptnModNestCall less_trans_Suc) }
    ultimately have "\<exists>n. (n, \<Gamma>, (LanguageCon.com.Call f, Normal s) # (bdy, Normal s) # xs) \<in> cptn_mod_nest_call \<and> (\<not> nn n < n \<or> (nn n, \<Gamma>, (LanguageCon.com.Call f, Normal s) # (bdy, Normal s) # xs) \<notin> cptn_mod_nest_call)"
      by (metis (no_types) CptnModNestCall.hyps(3) CptnModNestCall.hyps(4) cptn_mod_nest_call.CptnModNestCall elim_cptn_mod_nest_call_n) }
   then show ?thesis
     by meson
  qed     
next 
 case (CptnModNestDynCom n \<Gamma> c s xs) thus ?case
   by (meson cptn_mod_nest_call.CptnModNestDynCom elim_cptn_mod_nest_call_n)
next
  case (CptnModNestGuard n \<Gamma> c s xs g f) thus ?case 
    by (meson cptn_mod_nest_call.CptnModNestGuard elim_cptn_mod_nest_call_n)   
next
 case (CptnModNestCatch1 n \<Gamma> P s xs  zs Q) thus ?case
   by (metis (no_types, lifting) Catch_P_Not_finish cptn_mod_nest_call.CptnModNestCatch1 div_catch_nest)
next
 case (CptnModNestCatch2 n \<Gamma> P s xs ys zs Q) 
 then obtain min_p where 
     min_p:"(min_p, \<Gamma>, (P,  s) # xs) \<in> cptn_mod_nest_call \<and>
        (\<forall>m<min_p. (m, \<Gamma>, (P, s) # xs) \<notin> cptn_mod_nest_call)" 
    by auto 
  from CptnModNestCatch2(5) obtain min_q where
    min_q:"(min_q, \<Gamma>, (Skip, snd (last ((P, s) # xs))) # ys) \<in> cptn_mod_nest_call \<and>
        (\<forall>m<min_q. (m, \<Gamma>, (Skip, snd (last ((P, s) # xs))) # ys) \<notin> cptn_mod_nest_call)"
  by auto
  thus ?case
  proof(cases "min_p\<ge>min_q")
    case True
    then have "(min_p, \<Gamma>, (Skip, snd (last ((P,s) # xs))) # ys) \<in> cptn_mod_nest_call"
      using min_q using cptn_mod_nest_mono by blast 
    then have "(min_p, \<Gamma>, (Catch P Q, s) # zs) \<in> cptn_mod_nest_call"
      using conjunct1[OF min_p] cptn_mod_nest_call.CptnModNestCatch2[of min_p \<Gamma> P s xs] 
            CptnModNestCatch2(6)  CptnModNestCatch2(3)
    by blast
    also have "\<forall>m<min_p. (m, \<Gamma>,(Catch P Q,s) # zs) \<notin> cptn_mod_nest_call"
     proof -
      {fix m
      assume min_m:"m<min_p"
      then have "(m, \<Gamma>,(Catch P Q, s) # zs) \<notin> cptn_mod_nest_call"
      proof -
      {assume ass:"(m, \<Gamma>, (Catch P Q, s) # zs) \<in> cptn_mod_nest_call"
       then obtain xs' s' s'' where 
          m_cptn:"(m, \<Gamma>, (P, s) # xs') \<in> cptn_mod_nest_call \<and> 
                   catch_cond_nest zs Q xs' P s s'' s' \<Gamma> m" 
         using  
          div_catch_nest[of m \<Gamma> "(Catch P Q, s) # zs"]
          by fastforce
       then have "catch_cond_nest zs Q xs' P s s'' s' \<Gamma> m" by auto
       then have "xs=xs'" 
         using Catch_P_Ends_Skip[OF CptnModNestCatch2(6) CptnModNestCatch2(3)]   
         by fastforce
       then have "(m, \<Gamma>, (P,s) # xs) \<in> cptn_mod_nest_call"
         using m_cptn by auto
       then have False using min_p min_m by fastforce
    } thus ?thesis by auto
    qed
    }thus ?thesis by auto
  qed
  ultimately show ?thesis by auto
  next
    case False
    then have "(min_q, \<Gamma>, (P,  s) # xs) \<in> cptn_mod_nest_call"
      using min_p cptn_mod_nest_mono by force 
    then have "(min_q, \<Gamma>, (Catch P Q, s) # zs) \<in> cptn_mod_nest_call"
      using conjunct1[OF min_q] cptn_mod_nest_call.CptnModNestCatch2[of min_q \<Gamma> P s xs ] 
            CptnModNestCatch2(6)  CptnModNestCatch2(3)
    by blast
    also have "\<forall>m<min_q. (m, \<Gamma>,(Catch P Q,s) # zs) \<notin> cptn_mod_nest_call"
     proof -
      {fix m
      assume min_m:"m<min_q"
      then have "(m, \<Gamma>,(Catch P Q, s) # zs) \<notin> cptn_mod_nest_call"
      proof -
      {assume ass:"(m, \<Gamma>, (Catch P Q, s) # zs) \<in> cptn_mod_nest_call"
       then obtain xs' s' s'' where 
          m_cptn:"(m, \<Gamma>, (P, s) # xs') \<in> cptn_mod_nest_call \<and> 
                   catch_cond_nest zs Q xs' P s s'' s' \<Gamma> m" 
         using  
          div_catch_nest[of m \<Gamma> "(Catch P Q, s) # zs"]
          by fastforce
       then have "catch_cond_nest zs Q xs' P s s'' s' \<Gamma> m" by auto
       then have ?thesis
         using Catch_P_Ends_Skip[OF CptnModNestCatch2(6) CptnModNestCatch2(3)]
               min_m min_q 
       by blast         
      } thus ?thesis by auto
      qed
      }thus ?thesis by auto
    qed  
    ultimately show ?thesis by auto
  qed
next
 case (CptnModNestCatch3 n \<Gamma> P s xs s' Q ys zs ) then obtain min_p where 
     min_p:"(min_p, \<Gamma>, (P, Normal s) # xs) \<in> cptn_mod_nest_call \<and>
        (\<forall>m<min_p. (m, \<Gamma>, (P, Normal s) # xs) \<notin> cptn_mod_nest_call)" 
    by auto 
  from CptnModNestCatch3(6)  CptnModNestCatch3(4) obtain min_q where
    min_q:"(min_q, \<Gamma>, (Q,  snd (last ((P, Normal s) # xs))) # ys) \<in> cptn_mod_nest_call \<and>
        (\<forall>m<min_q. (m, \<Gamma>, (Q,  snd (last ((P, Normal s) # xs))) # ys) \<notin> cptn_mod_nest_call)"
  by auto
  thus ?case
  proof(cases "min_p\<ge>min_q")
    case True
    then have "(min_p, \<Gamma>, (Q,  snd (last ((P, Normal s) # xs))) # ys) \<in> cptn_mod_nest_call"
      using min_q using cptn_mod_nest_mono by blast 
    then have "(min_p, \<Gamma>, (Catch P Q, Normal s) # zs) \<in> cptn_mod_nest_call"
      using conjunct1[OF min_p] cptn_mod_nest_call.CptnModNestCatch3[of min_p \<Gamma> P s xs s' Q ys zs] 
            CptnModNestCatch3(4)  CptnModNestCatch3(3) CptnModNestCatch3(7)
    by fastforce
    also have "\<forall>m<min_p. (m, \<Gamma>,(Catch P Q,Normal s) # zs) \<notin> cptn_mod_nest_call"
     proof -
      {fix m
      assume min_m:"m<min_p"
      then have "(m, \<Gamma>,(Catch P Q, Normal s) # zs) \<notin> cptn_mod_nest_call"
      proof -
      {assume ass:"(m, \<Gamma>, (Catch P Q,Normal s) # zs) \<in> cptn_mod_nest_call"
       then obtain xs' ns' ns'' where 
          m_cptn:"(m, \<Gamma>, (P, Normal s) # xs') \<in> cptn_mod_nest_call \<and> 
                   catch_cond_nest zs Q xs' P (Normal s) ns'' ns' \<Gamma> m" 
         using  
          div_catch_nest[of m \<Gamma> "(Catch P Q, Normal s) # zs"]
          by fastforce
       then have "catch_cond_nest zs Q xs' P (Normal s) ns'' ns' \<Gamma> m" by auto       
       then have "xs=xs'" 
         using  Catch_P_Ends_Normal[OF CptnModNestCatch3(7)  CptnModNestCatch3(3) CptnModNestCatch3(4)]   
         by fastforce
       then have "(m, \<Gamma>, (P,Normal s) # xs) \<in> cptn_mod_nest_call"
         using m_cptn by auto
       then have False using min_p min_m by fastforce
    } thus ?thesis by auto
    qed
    }thus ?thesis by auto
  qed
  ultimately show ?thesis by auto
  next
    case False
    then have "(min_q, \<Gamma>, (P,  Normal s) # xs) \<in> cptn_mod_nest_call"
      using min_p cptn_mod_nest_mono by force 
    then have "(min_q, \<Gamma>, (Catch P Q, Normal s) # zs) \<in> cptn_mod_nest_call"
      using conjunct1[OF min_q] cptn_mod_nest_call.CptnModNestCatch3[of min_q \<Gamma> P s xs s' ] 
            CptnModNestCatch3(4)  CptnModNestCatch3(3) CptnModNestCatch3(7)
    by blast
    also have "\<forall>m<min_q. (m, \<Gamma>,(Catch P Q,Normal s) # zs) \<notin> cptn_mod_nest_call"
     proof -
      {fix m
      assume min_m:"m<min_q"
      then have "(m, \<Gamma>,(Catch P Q, Normal s) # zs) \<notin> cptn_mod_nest_call"
      proof -
      {assume ass:"(m, \<Gamma>, (Catch P Q, Normal s) # zs) \<in> cptn_mod_nest_call"
       then obtain xs' ns' ns'' where 
          m_cptn:"(m, \<Gamma>, (P, Normal s) # xs') \<in> cptn_mod_nest_call \<and> 
                   catch_cond_nest zs Q xs' P (Normal s) ns'' ns' \<Gamma> m" 
         using  
          div_catch_nest[of m \<Gamma> "(Catch P Q, Normal s) # zs"]
          by fastforce
       then have "catch_cond_nest zs Q xs' P (Normal s) ns'' ns' \<Gamma> m" by auto
       then have ?thesis
         using Catch_P_Ends_Normal[OF CptnModNestCatch3(7) CptnModNestCatch3(3)  CptnModNestCatch3(4)]
               min_m min_q 
         by (metis last_length)                                
      } thus ?thesis by auto
      qed
      }thus ?thesis by auto
    qed  
    ultimately show ?thesis by auto
  qed  
qed

  lemma elim_cptn_mod_min_nest_call:
 assumes a0:"min_call n \<Gamma> cfg" and
         a1:"cfg = (P,s)#(Q,t)#cfg1" and
         a2:"(\<forall>f. redex P \<noteq> Call f) \<or>  
             SmallStepCon.redex P = LanguageCon.com.Call fn \<and> \<Gamma> fn = None \<or>
            (redex P = Call fn \<and> (\<forall>sa. s\<noteq>Normal sa)) \<or>
            (redex P = Call fn \<and> P=Q)"     
 shows "min_call n \<Gamma> ((Q,t)#cfg1)"
proof -
  have a0: "(n,\<Gamma>,cfg) \<in>  cptn_mod_nest_call" and
       a0': "(\<forall>m<n. (m, \<Gamma>, cfg) \<notin> cptn_mod_nest_call)"
  using a0 unfolding min_call_def by auto
  then have "(n,\<Gamma>,(Q,t)#cfg1) \<in>  cptn_mod_nest_call"  
    using a0 a1 elim_cptn_mod_nest_call_n by blast
  also have "(\<forall>m<n. (m, \<Gamma>, (Q,t)#cfg1) \<notin> cptn_mod_nest_call)"      
  proof-
  { assume "\<not>(\<forall>m<n. (m, \<Gamma>, (Q,t)#cfg1) \<notin> cptn_mod_nest_call)"
    then obtain m where 
      asm0:"m<n" and 
      asm1:"(m, \<Gamma>, (Q,t)#cfg1) \<in> cptn_mod_nest_call"
      by auto
    have ce:"\<Gamma>\<turnstile>\<^sub>c (P, s) \<rightarrow>\<^sub>c\<^sub>e (Q, t)"
      using a0 a1 cptn_elim_cases(2) cptn_eq_cptn_mod_nest by blast
    then have "\<Gamma>\<turnstile>\<^sub>c (P, s) \<rightarrow>\<^sub>e (Q, t) \<or> \<Gamma>\<turnstile>\<^sub>c (P, toSeq s) \<rightarrow> (Q, toSeq t)"
      using step_ce_dest by blast  
    then have "(m, \<Gamma>, cfg) \<in> cptn_mod_nest_call"     
    proof
      assume "\<Gamma>\<turnstile>\<^sub>c (P, s) \<rightarrow>\<^sub>e (Q, t)"
      then show ?thesis          
        using  a0 a1 a2 cptn_mod_nest_call.CptnModNestEnv          
        by (metis asm1 env_c_c')
    next
      assume a00:"\<Gamma>\<turnstile>\<^sub>c (P, toSeq s) \<rightarrow> (Q, toSeq t)"
      moreover have "P\<noteq>Q" using mod_env_not_component calculation by auto
      moreover have norm:"\<forall>ns ns'.
        (s = Normal ns \<or> s = Abrupt ns) \<and> (t = Normal ns' \<or> t = Abrupt ns') \<longrightarrow>
        snd ns = snd ns'"
        using calculation ce step_ce_notNormal step_dest1 by blast  
      then show ?thesis using mod_env_not_component a2 not_func_redex_cptn_mod_nest_n'[OF _ _ a00 norm]
        by (simp add: a1 asm1 calculation(2)) 
    qed      
    then have False using a0' asm0 by auto
  } thus ?thesis by auto qed
  ultimately show ?thesis unfolding min_call_def by auto
qed 

lemma elim_call_cptn_mod_min_nest_call:
 assumes a0:"min_call n \<Gamma> cfg" and
         a1:"cfg = (P,s)#(Q,t)#cfg1" and
         a2:"P = Call f \<and>  
             \<Gamma> f = Some Q \<and> (\<exists>sa. s=Normal sa) \<and> P\<noteq>Q"          
 shows "min_call (n-1) \<Gamma> ((Q,t)#cfg1)"
proof -
  obtain s' where a0: "(n,\<Gamma>,cfg) \<in>  cptn_mod_nest_call" and
       a0': "(\<forall>m<n. (m, \<Gamma>, cfg) \<notin> cptn_mod_nest_call)" and
       a2': "s= Normal s'" 
    using a0 a2 unfolding min_call_def by auto  
  then have "(n-1,\<Gamma>,(Q,t)#cfg1) \<in>  cptn_mod_nest_call" 
    using a1 a2 a2' elim_cptn_mod_nest_call_n_dec[of n \<Gamma> f s' cfg1 Q]
    by (metis (no_types, lifting) SmallStepCon.redex.simps(7) call_f_step_ce_not_s_eq_t_env_step 
           cptn_elim_cases(2) cptn_if_cptn_mod cptn_mod_nest_cptn_mod 
           elim_cptn_mod_nest_call_n_dec1 not_eq_not_env) 
  moreover have "(\<forall>m<n - 1. (m, \<Gamma>, (Q, t) # cfg1) \<notin> cptn_mod_nest_call)"
  proof -
    { fix m
      assume "m<n-1"
      then have "(m, \<Gamma>, (Q, t) # cfg1) \<notin> cptn_mod_nest_call"
      proof -
        obtain pp :: "('b \<times> 'c) \<times> 'c list" where
          f1: "s = Normal pp"
        using a2 by blast
          then have "(LanguageCon.com.Call f, Normal pp) = (P, s)"
            by (simp add: a2)
          then have f2: "Normal pp = t"
            by (metis (no_types) SmallStepCon.redex.simps(7) a0 a1 a2 call_f_step_ce_not_s_eq_t_env_step cptn_elim_cases(2) cptn_eq_cptn_mod_set cptn_mod_nest_cptn_mod not_eq_not_env)
          have "m < n - Suc 0"
            using \<open>m < n - 1\<close> by presburger
          then have f3: "m + Suc 0 < n"
            by (meson less_diff_conv)
          have "(LanguageCon.com.Call f, Normal pp) = (P, s)"
            using f1 by (simp add: a2)
          then show ?thesis
            using f3 f2 a0' a1 a2 cptn_mod_nest_call.CptnModNestCall by fastforce
        qed 
      }
      thus ?thesis by auto
    qed
    ultimately show ?thesis unfolding min_call_def by auto
qed

lemma skip_min_nested_call_0:
  assumes a0:"min_call n \<Gamma> cfg" and
          a1:"cfg = (Skip,s)#cfg1"
  shows "n=0"
proof -
  have asm0:"(n, \<Gamma>, cfg) \<in> cptn_mod_nest_call" and 
       asm1:"(\<forall>m<n. (m, \<Gamma>, cfg) \<notin> cptn_mod_nest_call)"  
       using a0 unfolding min_call_def by auto  
  show ?thesis using a1 asm0 asm1
  proof (induct cfg1 arbitrary: cfg s n)
    case Nil thus ?case
      using cptn_mod_nest_call.CptnModNestOne neq0_conv by blast
  next
    case (Cons x xs)
      then obtain Q s' where cfg:"cfg = (LanguageCon.com.Skip, s) # (Q,s') # xs" by force
      then have min_call:"min_call n \<Gamma> cfg" using Cons unfolding min_call_def by auto
      then have "(\<forall>f. SmallStepCon.redex Skip \<noteq> LanguageCon.com.Call f)" by auto
      then have "min_call n \<Gamma> ((Q, s')#xs)" 
        using elim_cptn_mod_min_nest_call[OF min_call cfg] cfg
        by simp
      thus ?case using Cons cfg unfolding min_call_def
      proof -
        assume a1: "(n, \<Gamma>, (Q, s') # xs) \<in> cptn_mod_nest_call \<and> (\<forall>m<n. (m, \<Gamma>, (Q, s') # xs) \<notin> cptn_mod_nest_call)"
        have "LanguageCon.com.Skip = Q"
          by (metis (no_types) \<open>(n, \<Gamma>, cfg) \<in> cptn_mod_nest_call\<close> cfg cptn_dest1_pair cptn_if_cptn_mod cptn_mod_nest_cptn_mod fst_conv last.simps last_length length_Cons lessI not_Cons_self2 skip_all_skip)
        then show ?thesis
          using a1 by (meson Cons.hyps)
      qed      
  qed
qed

lemma throw_min_nested_call_0:
  assumes a0:"min_call n \<Gamma> cfg" and
          a1:"cfg = (Throw,s)#cfg1"
  shows "n=0"
proof -
  have asm0:"(n, \<Gamma>, cfg) \<in> cptn_mod_nest_call" and 
       asm1:"(\<forall>m<n. (m, \<Gamma>, cfg) \<notin> cptn_mod_nest_call)"  
       using a0 unfolding min_call_def by auto  
  show ?thesis using a1 asm0 asm1
  proof (induct cfg1 arbitrary: cfg s n)
    case Nil thus ?case
      using cptn_mod_nest_call.CptnModNestOne neq0_conv by blast
  next
    case (Cons x xs)
       obtain s' where x:"x = (Skip,s') \<or> x = (Throw, s')" 
        using CptnMod_elim_cases(10)[OF cptn_mod_nest_cptn_mod[OF Cons(3)[simplified Cons(2)]]]    
              ce_Throw_toSkip cptn_elim_cases_pair(2) by auto
      then obtain Q where cfg:"cfg = (LanguageCon.com.Throw, s) # (Q,s') # xs"
        using Cons  by force
      then have min_call:"min_call n \<Gamma> cfg" using Cons unfolding min_call_def by auto
      then have "(\<forall>f. SmallStepCon.redex Skip \<noteq> LanguageCon.com.Call f)" by auto
      then have min_call':"min_call n \<Gamma> ((Q, s')#xs)" 
        using elim_cptn_mod_min_nest_call[OF min_call cfg] cfg
        by simp
      from x show ?case
      proof
        assume "x=(Skip,s')"
        thus ?thesis using skip_min_nested_call_0 min_call' Cons(2) cfg by fastforce
      next       
        assume "x=(Throw,s')"
        thus ?thesis using Cons(1,2) min_call' cfg unfolding min_call_def  
          by blast 
      qed      
  qed
qed



text \<open> function to calculate that there is not any subsequent where the nested call is n \<close>
definition cond_seq_1
where 
"cond_seq_1 n \<Gamma> c1 s xs c2 zs ys \<equiv> ((n,\<Gamma>, (c1, s)#xs) \<in> cptn_mod_nest_call \<and> 
                       fst(last((c1,s)#xs)) = Skip \<and>
                        (n,\<Gamma>,((c2, snd(last ((c1, s)#xs)))#ys)) \<in> cptn_mod_nest_call \<and>
                       zs=(map (lift c2) xs)@((c2, snd(last ((c1, s)#xs)))#ys))"

definition cond_seq_2
where
"cond_seq_2 n \<Gamma> c1 s xs c2 zs ys s' s'' \<equiv>  s= Normal s'' \<and> 
                    (n,\<Gamma>, (c1, s)#xs) \<in> cptn_mod_nest_call \<and> 
                    fst(last ((c1, s)#xs)) = Throw \<and>
                    snd(last ((c1, s)#xs)) = Normal s' \<and> 
                    (n,\<Gamma>,(Throw,Normal s')#ys) \<in> cptn_mod_nest_call \<and> 
                     zs=(map (lift c2) xs)@((Throw,Normal s')#ys)"

definition cond_catch_1
where 
"cond_catch_1 n \<Gamma> c1 s xs c2 zs ys \<equiv> ((n,\<Gamma>, (c1, s)#xs) \<in> cptn_mod_nest_call \<and> 
                       fst(last((c1,s)#xs)) = Skip \<and>
                        (n,\<Gamma>,((Skip, snd(last ((c1, s)#xs)))#ys)) \<in> cptn_mod_nest_call \<and>
                       zs=(map (lift_catch c2) xs)@((Skip, snd(last ((c1, s)#xs)))#ys))"

definition cond_catch_2
where
"cond_catch_2 n \<Gamma> c1 s xs c2 zs ys s' s'' \<equiv> s= Normal s'' \<and> 
                    (n,\<Gamma>, (c1, s)#xs) \<in> cptn_mod_nest_call \<and> 
                    fst(last ((c1, s)#xs)) = Throw \<and>
                    snd(last ((c1, s)#xs)) = Normal s' \<and> 
                    (n,\<Gamma>,(c2,Normal s')#ys) \<in> cptn_mod_nest_call \<and> 
                     zs=(map (lift_catch c2) xs)@((c2,Normal s')#ys)"

(* fun biggest_nest_call :: "('s,'p,'f,'e)com \<Rightarrow> 
                         ('s,'f) xstate \<Rightarrow> 
                         (('s,'p,'f,'e) config) list \<Rightarrow> 
                         ('s,'p,'f,'e) body \<Rightarrow> 
                         nat \<Rightarrow> bool"
where
 "biggest_nest_call (Seq c1 c2) s zs \<Gamma> n  = 
   (if (\<exists>xs. ((min_call n \<Gamma> ((c1,s)#xs)) \<and> (zs=map (lift c2) xs))) then
       let xsa = (SOME xs. (min_call n \<Gamma> ((c1,s)#xs)) \<and> (zs=map (lift c2) xs)) in
       (biggest_nest_call c1 s xsa \<Gamma> n)
    else if (\<exists>xs ys. cond_seq_1 n \<Gamma> c1 s xs c2 zs ys) then
         let xsa = (SOME xs. \<exists>ys. cond_seq_1 n \<Gamma> c1 s xs c2 zs ys);
             ysa = (SOME ys. cond_seq_1 n \<Gamma> c1 s xsa c2 zs ys) in
         if (min_call n \<Gamma> ((c2, snd(last ((c1, s)#xsa)))#ysa)) then True
         else (biggest_nest_call c1 s xsa \<Gamma> n)            
   else let xsa = (SOME xs. \<exists>ys s' s''. cond_seq_2 n \<Gamma> c1 s xs c2 zs ys s' s'') in
           (biggest_nest_call c1 s xsa \<Gamma> n))"      
|"biggest_nest_call (Catch c1 c2) s zs \<Gamma> n  = 
  (if (\<exists>xs. ((min_call n \<Gamma> ((c1,s)#xs)) \<and> (zs=map (lift_catch c2) xs))) then
    let xsa = (SOME xs. (min_call n \<Gamma> ((c1,s)#xs)) \<and> (zs=map (lift_catch c2) xs)) in
       (biggest_nest_call c1 s xsa \<Gamma> n)
    else if (\<exists>xs ys. cond_catch_1 n \<Gamma> c1 s xs c2 zs ys) then
         let xsa = (SOME xs. \<exists>ys. cond_catch_1 n \<Gamma> c1 s xs c2 zs ys) in            
                 (biggest_nest_call c1 s xsa \<Gamma> n)
   else let xsa = (SOME xs. \<exists>ys s' s''. cond_catch_2 n \<Gamma> c1 s xs c2 zs ys s' s'');
            ysa = (SOME ys. \<exists>s' s''. cond_catch_2 n \<Gamma> c1 s xsa c2 zs ys s' s'') in
         if (min_call n \<Gamma> ((c2, snd(last ((c1, s)#xsa)))#ysa)) then True
         else (biggest_nest_call c1 s xsa \<Gamma> n))"
|"biggest_nest_call _ _ _ _ _ = False"
*)

lemma min_call_less_eq_n:
  "(n,\<Gamma>, (c1, s)#xs) \<in> cptn_mod_nest_call \<Longrightarrow>     
   (n,\<Gamma>,(c2, snd(last ((c1, s)#xs)))#ys) \<in> cptn_mod_nest_call \<Longrightarrow>
   min_call p \<Gamma> ((c1, s)#xs) \<and> min_call q \<Gamma> ((c2, snd(last ((c1, s)#xs)))#ys) \<Longrightarrow>
   p\<le>n \<and> q\<le>n"
unfolding min_call_def
using le_less_linear by blast

lemma min_call_seq_less_eq_n':
  "(n,\<Gamma>, (c1, s)#xs) \<in> cptn_mod_nest_call \<Longrightarrow>     
   min_call p \<Gamma> ((c1, s)#xs)  \<Longrightarrow>
   p\<le>n"
unfolding min_call_def
using le_less_linear by blast

lemma min_call_seq2:
  "min_call n \<Gamma> ((Seq c1 c2,s)#zs) \<Longrightarrow>
   (n,\<Gamma>, (c1, s)#xs) \<in> cptn_mod_nest_call \<Longrightarrow> 
    fst(last ((c1, s)#xs)) = Skip \<Longrightarrow>
   (n,\<Gamma>,(c2, snd(last ((c1, s)#xs)))#ys) \<in> cptn_mod_nest_call \<Longrightarrow>
    zs=(map (lift c2) xs)@((c2, snd(last ((c1, s)#xs)))#ys) \<Longrightarrow>
   min_call n \<Gamma> ((c1, s)#xs) \<or> min_call n \<Gamma> ((c2, snd(last ((c1, s)#xs)))#ys)
   "
proof -
  assume a0:"min_call n \<Gamma> ((Seq c1 c2,s)#zs)" and
         a1:"(n,\<Gamma>, (c1, s)#xs) \<in> cptn_mod_nest_call" and
         a2:"fst(last ((c1, s)#xs)) = Skip" and
         a3:"(n,\<Gamma>,(c2, snd(last ((c1, s)#xs)))#ys) \<in> cptn_mod_nest_call" and
         a4:"zs=(map (lift c2) xs)@((c2, snd(last ((c1, s)#xs)))#ys)"
  then obtain p q where min_calls: 
    "min_call p \<Gamma> ((c1, s)#xs) \<and> min_call q \<Gamma> ((c2, snd(last ((c1, s)#xs)))#ys)"
    using a1 a3 minimum_nest_call by blast
  then have p_q:"p\<le>n \<and> q\<le>n" using a0 a1  a3 a4 min_call_less_eq_n by blast
  {
    assume ass0:"p<n \<and> q <n"     
    then have "(p,\<Gamma>, (c1, s)#xs) \<in> cptn_mod_nest_call" and
              "(q,\<Gamma>,(c2, snd(last ((c1, s)#xs)))#ys) \<in> cptn_mod_nest_call"
      using min_calls unfolding min_call_def by auto
    then have ?thesis
    proof (cases "p\<le>q")
      case True 
      then have q_cptn_c1:"(q, \<Gamma>, (c1, s) # xs) \<in> cptn_mod_nest_call" 
        using cptn_mod_nest_mono min_calls unfolding min_call_def  
        by blast
      have q_cptn_c2:"(q, \<Gamma>, (c2, snd (last ((c1, s) # xs))) # ys) \<in> cptn_mod_nest_call"
       using min_calls unfolding min_call_def by auto
      then have "(q,\<Gamma>,((Seq c1 c2,s)#zs)) \<in>cptn_mod_nest_call"
        using True min_calls a2 a4  CptnModNestSeq2[OF q_cptn_c1 a2 q_cptn_c2 a4] 
        by auto
      thus ?thesis using ass0 a0 unfolding min_call_def by auto
    next
      case False
      then have q_cptn_c1:"(p, \<Gamma>, (c1, s) # xs) \<in> cptn_mod_nest_call" 
        using  min_calls unfolding min_call_def  
        by blast
      have q_cptn_c2:"(p, \<Gamma>, (c2, snd (last ((c1, s) # xs))) # ys) \<in> cptn_mod_nest_call"
       using min_calls False unfolding min_call_def
       by (metis (no_types, lifting) cptn_mod_nest_mono2 not_less)
      then have "(p,\<Gamma>,((Seq c1 c2,s)#zs)) \<in>cptn_mod_nest_call"
        using False min_calls a2 a4  CptnModNestSeq2[OF q_cptn_c1 a2 q_cptn_c2 a4] 
        by auto
      thus ?thesis using ass0 a0 unfolding min_call_def by auto
    qed
  }note l=this
  {
    assume ass0:"p\<ge>n \<or> q \<ge>n" 
    then have ?thesis using p_q min_calls by fastforce
  }
  thus ?thesis using l by fastforce
qed

lemma min_call_seq3:
  "min_call n \<Gamma> ((Seq c1 c2,s)#zs) \<Longrightarrow>
   s= Normal s'' \<Longrightarrow>
   (n,\<Gamma>, (c1, s)#xs) \<in> cptn_mod_nest_call \<Longrightarrow> 
    fst(last ((c1, s)#xs)) = Throw \<Longrightarrow>
    snd(last ((c1, s)#xs)) = Normal s' \<Longrightarrow>
   (n,\<Gamma>,(Throw, snd(last ((c1, s)#xs)))#ys) \<in> cptn_mod_nest_call \<Longrightarrow>
    zs=(map (lift c2) xs)@((Throw, snd(last ((c1, s)#xs)))#ys) \<Longrightarrow>
   min_call n \<Gamma> ((c1, s)#xs)
   "
proof -
  assume a0:"min_call n \<Gamma> ((Seq c1 c2,s)#zs)" and
         a0':"s= Normal s''" and
         a1:"(n,\<Gamma>, (c1, s)#xs) \<in> cptn_mod_nest_call" and
         a2:"fst(last ((c1, s)#xs)) = Throw" and
         a2':"snd(last ((c1, s)#xs)) = Normal s'" and
         a3:"(n,\<Gamma>,(Throw, snd(last ((c1, s)#xs)))#ys) \<in> cptn_mod_nest_call" and
         a4:"zs=(map (lift c2) xs)@((Throw, snd(last ((c1, s)#xs)))#ys)"
  then obtain p where min_calls: 
    "min_call p \<Gamma> ((c1, s)#xs) \<and> min_call 0 \<Gamma> ((Throw, snd(last ((c1, s)#xs)))#ys)"
    using a1 a3 minimum_nest_call throw_min_nested_call_0  by metis
  then have p_q:"p\<le>n \<and> 0\<le>n" using a0 a1  a3 a4 min_call_less_eq_n by blast
  {
    assume ass0:"p<n \<and> 0 <n"     
    then have "(p,\<Gamma>, (c1, s)#xs) \<in> cptn_mod_nest_call" and
              "(0,\<Gamma>,(Throw, snd(last ((c1, s)#xs)))#ys) \<in> cptn_mod_nest_call"
      using min_calls unfolding min_call_def by auto
    then have ?thesis
    proof (cases "p\<le>0")
      case True 
      then have q_cptn_c1:"(0, \<Gamma>, (c1, Normal s'') # xs) \<in> cptn_mod_nest_call" 
        using cptn_mod_nest_mono min_calls a0' unfolding min_call_def  
        by blast
      have q_cptn_c2:"(0, \<Gamma>, (Throw, snd (last ((c1, s) # xs))) # ys) \<in> cptn_mod_nest_call"
       using min_calls unfolding min_call_def by auto
      then have "(0,\<Gamma>,((Seq c1 c2,s)#zs)) \<in>cptn_mod_nest_call"
        using True min_calls a2 a4 a2' a0'  CptnModNestSeq3[OF q_cptn_c1 ] 
        by auto
      thus ?thesis using ass0 a0 unfolding min_call_def by auto
    next
      case False
      then have q_cptn_c1:"(p, \<Gamma>, (c1, Normal s'') # xs) \<in> cptn_mod_nest_call" 
        using  min_calls a0' unfolding min_call_def  
        by blast
      have q_cptn_c2:"(p, \<Gamma>, (Throw, snd (last ((c1, s) # xs))) # ys) \<in> cptn_mod_nest_call"
       using min_calls False unfolding min_call_def
       by (metis (no_types, lifting) cptn_mod_nest_mono2 not_less)
      then have "(p,\<Gamma>,((Seq c1 c2,s)#zs)) \<in>cptn_mod_nest_call"
        using False min_calls a2 a4 a0' a2'  CptnModNestSeq3[OF q_cptn_c1]
        by auto       
      thus ?thesis using ass0 a0 unfolding min_call_def by auto
    qed
  }note l=this
  {
    assume ass0:"p\<ge>n \<or> 0 \<ge>n" 
    then have ?thesis using p_q min_calls by fastforce
  }
  thus ?thesis using l by fastforce
qed

lemma min_call_catch2:
  "min_call n \<Gamma> ((Catch c1 c2,s)#zs) \<Longrightarrow>   
   (n,\<Gamma>, (c1, s)#xs) \<in> cptn_mod_nest_call \<Longrightarrow> 
    fst(last ((c1, s)#xs)) = Skip \<Longrightarrow>    
   (n,\<Gamma>,(Skip, snd(last ((c1, s)#xs)))#ys) \<in> cptn_mod_nest_call \<Longrightarrow>
    zs=(map (lift_catch c2) xs)@((Skip, snd(last ((c1, s)#xs)))#ys) \<Longrightarrow>
   min_call n \<Gamma> ((c1, s)#xs)
   "
proof -
  assume a0:"min_call n \<Gamma> ((Catch c1 c2,s)#zs)" and        
         a1:"(n,\<Gamma>, (c1, s)#xs) \<in> cptn_mod_nest_call" and
         a2:"fst(last ((c1, s)#xs)) = Skip" and        
         a3:"(n,\<Gamma>,(Skip, snd(last ((c1, s)#xs)))#ys) \<in> cptn_mod_nest_call" and
         a4:"zs=(map (lift_catch c2) xs)@((Skip, snd(last ((c1, s)#xs)))#ys)"
  then obtain p where min_calls: 
    "min_call p \<Gamma> ((c1, s)#xs) \<and> min_call 0 \<Gamma> ((Skip, snd(last ((c1, s)#xs)))#ys)"
    using a1 a3 minimum_nest_call skip_min_nested_call_0  by metis
  then have p_q:"p\<le>n \<and> 0\<le>n" using a0 a1  a3 a4 min_call_less_eq_n by blast
  {
    assume ass0:"p<n \<and> 0 <n"     
    then have "(p,\<Gamma>, (c1, s)#xs) \<in> cptn_mod_nest_call" and
              "(0,\<Gamma>,(Skip, snd(last ((c1, s)#xs)))#ys) \<in> cptn_mod_nest_call"
      using min_calls unfolding min_call_def by auto
    then have ?thesis
    proof (cases "p\<le>0")
      case True 
      then have q_cptn_c1:"(0, \<Gamma>, (c1, s) # xs) \<in> cptn_mod_nest_call" 
        using cptn_mod_nest_mono min_calls  unfolding min_call_def  
        by blast
      have q_cptn_c2:"(0, \<Gamma>, (Skip, snd (last ((c1, s) # xs))) # ys) \<in> cptn_mod_nest_call"
       using min_calls unfolding min_call_def by auto
      then have "(0,\<Gamma>,((Catch c1 c2,s)#zs)) \<in>cptn_mod_nest_call"
        using True min_calls a2 a4    CptnModNestCatch2[OF q_cptn_c1 ] 
        by auto
      thus ?thesis using ass0 a0 unfolding min_call_def by auto
    next
      case False
      then have q_cptn_c1:"(p, \<Gamma>, (c1, s) # xs) \<in> cptn_mod_nest_call" 
        using  min_calls  unfolding min_call_def  
        by blast
      have q_cptn_c2:"(p, \<Gamma>, (Skip, snd (last ((c1, s) # xs))) # ys) \<in> cptn_mod_nest_call"
       using min_calls False unfolding min_call_def
       by (metis (no_types, lifting) cptn_mod_nest_mono2 not_less)
      then have "(p,\<Gamma>,((Catch c1 c2,s)#zs)) \<in>cptn_mod_nest_call"
        using False min_calls a2 a4   CptnModNestCatch2[OF q_cptn_c1]
        by auto       
      thus ?thesis using ass0 a0 unfolding min_call_def by auto
    qed
  }note l=this
  {
    assume ass0:"p\<ge>n \<or> 0 \<ge>n" 
    then have ?thesis using p_q min_calls by fastforce
  }
  thus ?thesis using l by fastforce
qed

lemma min_call_catch_less_eq_n:
  "(n,\<Gamma>, (c1, Normal s)#xs) \<in> cptn_mod_nest_call \<Longrightarrow>        
   (n,\<Gamma>,(c2, snd(last ((c1, Normal s)#xs)))#ys) \<in> cptn_mod_nest_call \<Longrightarrow>    
   min_call p \<Gamma> ((c1, Normal s)#xs) \<and> min_call q \<Gamma> ((c2, snd(last ((c1, Normal s)#xs)))#ys) \<Longrightarrow>
   p\<le>n \<and> q\<le>n"
unfolding min_call_def
using le_less_linear by blast

lemma min_call_catch3:
  "min_call n \<Gamma> ((Catch c1 c2,Normal s)#zs) \<Longrightarrow>
   (n,\<Gamma>, (c1, Normal s)#xs) \<in> cptn_mod_nest_call \<Longrightarrow> 
    fst(last ((c1, Normal s)#xs)) = Throw \<Longrightarrow>
    snd(last ((c1, Normal s)#xs)) = Normal s' \<Longrightarrow>
   (n,\<Gamma>,(c2, snd(last ((c1, Normal s)#xs)))#ys) \<in> cptn_mod_nest_call \<Longrightarrow>
    zs=(map (lift_catch c2) xs)@((c2, snd(last ((c1, Normal s)#xs)))#ys) \<Longrightarrow>
   min_call n \<Gamma> ((c1, Normal s)#xs) \<or> min_call n \<Gamma> ((c2, snd(last ((c1, Normal s)#xs)))#ys)
   "
proof -
  assume a0:"min_call n \<Gamma> ((Catch c1 c2,Normal s)#zs)" and
         a1:"(n,\<Gamma>, (c1, Normal s)#xs) \<in> cptn_mod_nest_call" and
         a2:"fst(last ((c1, Normal s)#xs)) = Throw" and
         a2':"snd(last ((c1, Normal s)#xs)) = Normal s'" and
         a3:"(n,\<Gamma>,(c2, snd(last ((c1, Normal s)#xs)))#ys) \<in> cptn_mod_nest_call" and
         a4:"zs=(map (lift_catch c2) xs)@((c2, snd(last ((c1, Normal s)#xs)))#ys)"
  then obtain p q where min_calls: 
    "min_call p \<Gamma> ((c1, Normal s)#xs) \<and> min_call q \<Gamma> ((c2, snd(last ((c1, Normal s)#xs)))#ys)"
    using a1 a3 minimum_nest_call by blast
  then have p_q:"p\<le>n \<and> q\<le>n" 
    using a1 a2 a2' a3 a4 min_call_less_eq_n by blast
  {
    assume ass0:"p<n \<and> q <n"     
    then have "(p,\<Gamma>, (c1, Normal s)#xs) \<in> cptn_mod_nest_call" and
              "(q,\<Gamma>,(c2, snd(last ((c1, Normal s)#xs)))#ys) \<in> cptn_mod_nest_call"
      using min_calls unfolding min_call_def by auto
    then have ?thesis
    proof (cases "p\<le>q")
      case True 
      then have q_cptn_c1:"(q, \<Gamma>, (c1,Normal s) # xs) \<in> cptn_mod_nest_call" 
        using cptn_mod_nest_mono min_calls unfolding min_call_def  
        by blast
      have q_cptn_c2:"(q, \<Gamma>, (c2, snd (last ((c1, Normal s) # xs))) # ys) \<in> cptn_mod_nest_call"
       using min_calls unfolding min_call_def by auto
      then have "(q,\<Gamma>,((Catch c1 c2, Normal s)#zs)) \<in>cptn_mod_nest_call"
        using True min_calls a2 a2' a4  CptnModNestCatch3[OF q_cptn_c1 a2 a2' q_cptn_c2 a4] 
        by auto
      thus ?thesis using ass0 a0 unfolding min_call_def by auto
    next
      case False
      then have q_cptn_c1:"(p, \<Gamma>, (c1, Normal s) # xs) \<in> cptn_mod_nest_call" 
        using  min_calls unfolding min_call_def  
        by blast
      have q_cptn_c2:"(p, \<Gamma>, (c2, snd (last ((c1, Normal s) # xs))) # ys) \<in> cptn_mod_nest_call"
       using min_calls False unfolding min_call_def
       by (metis (no_types, lifting) cptn_mod_nest_mono2 not_less)
      then have "(p,\<Gamma>,((Catch c1 c2,Normal s)#zs)) \<in>cptn_mod_nest_call"
        using False min_calls a2 a4  CptnModNestCatch3[OF q_cptn_c1 a2 a2' q_cptn_c2 a4] 
        by auto
      thus ?thesis using ass0 a0 unfolding min_call_def by auto
    qed
  }note l=this
  {
    assume ass0:"p\<ge>n \<or> q \<ge>n" 
    then have ?thesis using p_q min_calls by fastforce
  }
  thus ?thesis using l by fastforce
qed

lemma min_call_seq_c1_not_finish:
  "min_call n \<Gamma> cfg \<Longrightarrow>
   cfg = (LanguageCon.com.Seq P0 P1, s) # (Q, t) # cfg1 \<Longrightarrow>
   (n, \<Gamma>,(P0, s)#xs) \<in> cptn_mod_nest_call \<Longrightarrow>
   (Q, t) # cfg1 = map (lift P1) xs \<Longrightarrow>
   min_call  n \<Gamma> ((P0, s)#xs)
   "
proof -
  assume a0:"min_call n \<Gamma> cfg" and
        a1:" cfg = (LanguageCon.com.Seq P0 P1, s) # (Q, t) # cfg1" and
        a2:"(n, \<Gamma>,(P0, s)#xs) \<in> cptn_mod_nest_call" and
        a3:"(Q, t) # cfg1 = map (lift P1) xs" 
  then have "(n, \<Gamma>,(P0, s)#xs) \<in> cptn_mod_nest_call" using a2 by auto
  moreover have "\<forall>m<n. (m, \<Gamma>,(P0, s)#xs) \<notin> cptn_mod_nest_call"
  proof-
    {fix m
     assume ass:"m<n"
     {  assume ass1:"(m, \<Gamma>, (P0, s) # xs) \<in> cptn_mod_nest_call"
       then have "(m,\<Gamma>,cfg) \<in>  cptn_mod_nest_call" 
         using a1 a3 CptnModNestSeq1[OF ass1] by auto
       then have False using ass a0 unfolding min_call_def by auto
     }
     then have "(m, \<Gamma>, (P0, s) # xs) \<notin> cptn_mod_nest_call" by auto
    } then show ?thesis by auto
  qed
  ultimately show ?thesis unfolding min_call_def by auto
qed

lemma min_call_seq_not_finish:
  " min_call  n \<Gamma> ((P0, s)#xs) \<Longrightarrow>
   cfg = (LanguageCon.com.Seq P0 P1, s) #  cfg1 \<Longrightarrow>  
    cfg1 = map (lift P1) xs \<Longrightarrow>
   min_call n \<Gamma> cfg 
   "
proof -
  assume a0:"min_call  n \<Gamma> ((P0, s)#xs)" and
        a1:" cfg = (LanguageCon.com.Seq P0 P1, s) #  cfg1" and        
        a2:" cfg1 = map (lift P1) xs" 
  then have "(n, \<Gamma>,cfg) \<in> cptn_mod_nest_call" 
    using a0 a1 a2 CptnModNestSeq1[of n \<Gamma> P0 s xs "cfg1" P1] unfolding min_call_def 
    by auto
  moreover have "\<forall>m<n. (m, \<Gamma>,cfg) \<notin> cptn_mod_nest_call"
  proof-
    {fix m
     assume ass:"m<n"
     {  assume ass1:"(m, \<Gamma>, cfg) \<in> cptn_mod_nest_call"
       then have "(m,\<Gamma>,(P0, s)#xs) \<in>  cptn_mod_nest_call" 
         using a1 a2 by (metis (no_types) Seq_P_Not_finish div_seq_nest) 
       then have False using ass a0 unfolding min_call_def by auto
     }
     then have "(m, \<Gamma>, cfg) \<notin> cptn_mod_nest_call" by auto
    } then show ?thesis by auto
  qed
  ultimately show ?thesis unfolding min_call_def by auto
qed

lemma min_call_catch_c1_not_finish:
  "min_call n \<Gamma> cfg \<Longrightarrow>
   cfg = (LanguageCon.com.Catch P0 P1, s) # (Q, t) # cfg1 \<Longrightarrow>
   (n, \<Gamma>,(P0, s)#xs) \<in> cptn_mod_nest_call \<Longrightarrow>
   (Q, t) # cfg1 = map (lift_catch P1) xs \<Longrightarrow>
   min_call  n \<Gamma> ((P0, s)#xs)
   "
proof -
  assume a0:"min_call n \<Gamma> cfg" and
        a1:" cfg = (LanguageCon.com.Catch P0 P1, s) # (Q, t) # cfg1" and
        a2:"(n, \<Gamma>,(P0, s)#xs) \<in> cptn_mod_nest_call" and
        a3:"(Q, t) # cfg1 = map (lift_catch P1) xs" 
  then have "(n, \<Gamma>,(P0, s)#xs) \<in> cptn_mod_nest_call" using a2 by auto
  moreover have "\<forall>m<n. (m, \<Gamma>,(P0, s)#xs) \<notin> cptn_mod_nest_call"
  proof-
    {fix m
     assume ass:"m<n"
     {  assume ass1:"(m, \<Gamma>, (P0, s) # xs) \<in> cptn_mod_nest_call"
       then have "(m,\<Gamma>,cfg) \<in>  cptn_mod_nest_call" 
         using a1 a3 CptnModNestCatch1[OF ass1] by auto
       then have False using ass a0 unfolding min_call_def by auto
     }
     then have "(m, \<Gamma>, (P0, s) # xs) \<notin> cptn_mod_nest_call" by auto
    } then show ?thesis by auto
  qed
  ultimately show ?thesis unfolding min_call_def by auto
qed

lemma min_call_catch_not_finish:
  " min_call  n \<Gamma> ((P0, s)#xs) \<Longrightarrow>
   cfg = (LanguageCon.com.Catch P0 P1, s) #  cfg1 \<Longrightarrow>  
    cfg1 = map (lift_catch P1) xs \<Longrightarrow>
   min_call n \<Gamma> cfg 
   "
proof -
  assume a0:"min_call  n \<Gamma> ((P0, s)#xs)" and
        a1:" cfg = (Catch P0 P1, s) #  cfg1" and        
        a2:" cfg1 = map (lift_catch P1) xs" 
  then have "(n, \<Gamma>,cfg) \<in> cptn_mod_nest_call" 
    using a0 a1 a2 CptnModNestCatch1[of n \<Gamma> P0 s xs "cfg1" P1] unfolding min_call_def 
    by auto
  moreover have "\<forall>m<n. (m, \<Gamma>,cfg) \<notin> cptn_mod_nest_call"
  proof-
    {fix m
     assume ass:"m<n"
     {  assume ass1:"(m, \<Gamma>, cfg) \<in> cptn_mod_nest_call"
       then have "(m,\<Gamma>,(P0, s)#xs) \<in>  cptn_mod_nest_call" 
         using a1 a2 by (metis (no_types) Catch_P_Not_finish div_catch_nest) 
       then have False using ass a0 unfolding min_call_def by auto
     }
     then have "(m, \<Gamma>, cfg) \<notin> cptn_mod_nest_call" by auto
    } then show ?thesis by auto
  qed
  ultimately show ?thesis unfolding min_call_def by auto
qed

lemma seq_xs_no_empty: assumes
     seq:"seq_cond_nest ((Q,t)#cfg1) P1 xs P0 s s'' s' \<Gamma> n" and
     cfg:"cfg = (LanguageCon.com.Seq P0 P1, s) # (Q, t) # cfg1" and
     a0:"SmallStepCon.redex (LanguageCon.com.Seq P0 P1) = LanguageCon.com.Call f"
     shows"\<exists>Q' xs'. Q=Seq Q' P1 \<and> xs=(Q',t)#xs'"
using seq
unfolding lift_def seq_cond_nest_def
proof
    assume "(Q, t) # cfg1 = map (\<lambda>(P, s). (LanguageCon.com.Seq P P1, s)) xs"
    thus ?thesis by auto
next
  assume "fst (((P0, s) # xs) ! length xs) = LanguageCon.com.Skip \<and>
        (\<exists>ys. (n, \<Gamma>, (P1, snd (((P0, s) # xs) ! length xs)) # ys) \<in> cptn_mod_nest_call \<and>
              (Q, t) # cfg1 =
              map (\<lambda>(P, s). (LanguageCon.com.Seq P P1, s)) xs @
              (P1, snd (((P0, s) # xs) ! length xs)) # ys) \<or>
        fst (((P0, s) # xs) ! length xs) = LanguageCon.com.Throw \<and>
        snd (last ((P0, s) # xs)) = Normal s' \<and>
        s = Normal s'' \<and>
        (\<exists>ys. (n, \<Gamma>, (LanguageCon.com.Throw, Normal s') # ys) \<in> cptn_mod_nest_call \<and>
              (Q, t) # cfg1 =
              map (\<lambda>(P, s). (LanguageCon.com.Seq P P1, s)) xs @
              (LanguageCon.com.Throw, Normal s') # ys)"
  thus ?thesis
  proof 
    assume ass:"fst (((P0, s) # xs) ! length xs) = LanguageCon.com.Skip \<and>
        (\<exists>ys. (n, \<Gamma>, (P1, snd (((P0, s) # xs) ! length xs)) # ys) \<in> cptn_mod_nest_call \<and>
              (Q, t) # cfg1 =
              map (\<lambda>(P, s). (LanguageCon.com.Seq P P1, s)) xs @
              (P1, snd (((P0, s) # xs) ! length xs)) # ys)"
    show ?thesis 
    proof (cases xs)
      case Nil thus ?thesis using cfg a0 ass by auto
    next
      case (Cons xa xsa)
      then obtain a b where xa:"xa = (a,b)" by fastforce
      obtain pps :: "(('a \<times> 'b, 'c, 'd, 'e) LanguageCon.com \<times> (('a \<times> 'b) \<times> 'b list, 'd) xstate) list" where
           "(Q, t) = (Seq a P1, b) \<and> 
            cfg1 = map (\<lambda>(c, y). (Seq c P1, y)) xsa @ 
                      (P1, snd (((P0, s) # xs) ! length xs)) # pps"  
        using ass local.Cons xa by moura         
      then show ?thesis
        using local.Cons xa by auto
    qed      
  next
    assume ass:"fst (((P0, s) # xs) ! length xs) = LanguageCon.com.Throw \<and>
        snd (last ((P0, s) # xs)) = Normal s' \<and>
        s = Normal s'' \<and>
        (\<exists>ys. (n, \<Gamma>, (LanguageCon.com.Throw, Normal s') # ys) \<in> cptn_mod_nest_call \<and>
              (Q, t) # cfg1 =
              map (\<lambda>(P, s). (LanguageCon.com.Seq P P1, s)) xs @
              (LanguageCon.com.Throw, Normal s') # ys)"
    thus ?thesis
    proof (cases xs)
      case Nil thus ?thesis using cfg a0 ass by auto
    next
      case (Cons xa xsa)
      then obtain a b where xa:"xa = (a,b)" by fastforce
      obtain pps :: "(('a \<times> 'b, 'c, 'd, 'e) LanguageCon.com \<times> (('a \<times> 'b) \<times> 'b list, 'd) xstate) list" where
        "(Q, t) = (Seq a P1, b) \<and> 
            cfg1 = map (\<lambda>(c, y). (Seq c P1, y)) xsa @ (LanguageCon.com.Throw, Normal s') # pps"
          using ass local.Cons xa by moura
      then show ?thesis
        using local.Cons xa by auto
      qed           
  qed
qed

lemma catch_xs_no_empty: assumes
     seq:"catch_cond_nest ((Q,t)#cfg1) P1 xs P0 s s'' s' \<Gamma> n" and
     cfg:"cfg = (LanguageCon.com.Catch P0 P1, s) # (Q, t) # cfg1" and
     a0:"SmallStepCon.redex (LanguageCon.com.Catch P0 P1) = LanguageCon.com.Call f"
     shows"\<exists>Q' xs'. Q=Catch Q' P1 \<and> xs=(Q',t)#xs'"
using seq
unfolding lift_catch_def catch_cond_nest_def
proof
    assume "(Q, t) # cfg1 = map (\<lambda>(P, s). (LanguageCon.com.Catch P P1, s)) xs"
    thus ?thesis by auto
next
  assume "fst (((P0, s) # xs) ! length xs) = LanguageCon.com.Throw \<and>
    snd (last ((P0, s) # xs)) = Normal s' \<and>
    s = Normal s'' \<and>
    (\<exists>ys. (n, \<Gamma>, (P1, snd (((P0, s) # xs) ! length xs)) # ys) \<in> cptn_mod_nest_call \<and>
          (Q, t) # cfg1 = map (\<lambda>(P, s). (LanguageCon.com.Catch P P1, s)) xs @ 
                                          (P1, snd (((P0, s) # xs) ! length xs)) # ys) \<or>
    fst (((P0, s) # xs) ! length xs) = LanguageCon.com.Skip \<and>
    (\<exists>ys. (n, \<Gamma>, (LanguageCon.com.Skip, snd (last ((P0, s) # xs))) # ys) \<in> cptn_mod_nest_call \<and>
          (Q, t) # cfg1 =
          map (\<lambda>(P, s). (LanguageCon.com.Catch P P1, s)) xs @ 
                         (LanguageCon.com.Skip, snd (last ((P0, s) # xs))) # ys)"
  thus ?thesis
  proof 
    assume ass:"fst (((P0, s) # xs) ! length xs) = LanguageCon.com.Throw \<and>
                snd (last ((P0, s) # xs)) = Normal s' \<and>
                s = Normal s'' \<and>
                (\<exists>ys. (n, \<Gamma>, (P1, snd (((P0, s) # xs) ! length xs)) # ys) \<in> cptn_mod_nest_call \<and>
                  (Q, t) # cfg1 = map (\<lambda>(P, s). (LanguageCon.com.Catch P P1, s)) xs @ 
                                          (P1, snd (((P0, s) # xs) ! length xs)) # ys)"
    show ?thesis 
    proof (cases xs)
      case Nil thus ?thesis using cfg a0 ass by auto
    next
      case (Cons xa xsa)
      then obtain a b where xa:"xa = (a,b)" by fastforce
      obtain pps :: "(('a \<times> 'b, 'c, 'd, 'e) com \<times> (('a \<times> 'b) \<times> 'b list, 'd) xstate) list" where
        "(Q, t) = (Catch a P1, b) \<and> 
             cfg1 = map (\<lambda>(c, y). (Catch c P1, y)) xsa @ 
              (P1, snd (((P0, s) # xs) ! length xs)) # pps"
        using ass local.Cons xa by moura
      then show ?thesis
        using local.Cons xa by auto
      qed
  next
    assume ass:"fst (((P0, s) # xs) ! length xs) = LanguageCon.com.Skip \<and>
    (\<exists>ys. (n, \<Gamma>, (LanguageCon.com.Skip, snd (last ((P0, s) # xs))) # ys) \<in> cptn_mod_nest_call \<and>
          (Q, t) # cfg1 =
          map (\<lambda>(P, s). (LanguageCon.com.Catch P P1, s)) xs @ 
                         (LanguageCon.com.Skip, snd (last ((P0, s) # xs))) # ys)"
    thus ?thesis
    proof (cases xs)
      case Nil thus ?thesis using cfg a0 ass by auto
    next
      case (Cons xa xsa)
      then obtain a b where xa:"xa = (a,b)" by fastforce      
      obtain pps :: "(('a \<times> 'b, 'c, 'd, 'e) com \<times> (('a \<times> 'b) \<times> 'b list, 'd) xstate) list" where
          "(Q, t) = (Catch a P1, b) \<and> 
           cfg1 = map (\<lambda>(c, y). (Catch c P1, y)) xsa @ (Skip, snd (last ((P0, s) # xs))) # pps"
        using ass local.Cons xa by moura
      then show ?thesis
        using local.Cons xa by auto
    qed        
  qed
qed

lemma redex_call_cptn_mod_min_nest_call_gr_zero:
 assumes a0:"min_call n \<Gamma> cfg" and
         a1:"cfg = (P,s)#(Q,t)#cfg1" and
         a2:"redex P = Call f \<and>  
             \<Gamma> f = Some bdy \<and> (\<exists>sa. s=Normal sa) \<and> t=s" and
         a3:"\<Gamma>\<turnstile>\<^sub>c(P,toSeq s)\<rightarrow>(Q,toSeq t)"
 shows "n>0"
using a0 a1 a2 a3
proof (induct P arbitrary: Q cfg1 cfg s t n)
  case (Call f1)
  then obtain ns where "toSeq s = Normal ns"
    by (metis toSeq.simps(1)) 
  then show ?case using Call stepc_Normal_elim_cases(9)[of \<Gamma> f1 ns "(Q,Normal ns)"]
     elim_cptn_mod_nest_call_n_greater_zero unfolding min_call_def
    by (metis (no_types, lifting) Pair_inject xstate.simps(9))
next
  case (Seq P0 P1) 
  then obtain xs s' s'' where 
          p0_cptn:"(n, \<Gamma>,(P0, s)#xs) \<in> cptn_mod_nest_call"  and 
          seq:"seq_cond_nest ((Q,t)#cfg1) P1 xs P0 s s'' s' \<Gamma> n"
  using div_seq_nest[of n \<Gamma> cfg] unfolding min_call_def by blast
  then obtain m where min:"min_call m \<Gamma> ((P0, s)#xs)"
    using minimum_nest_call by blast 
  have xs':"\<exists>Q' xs'. Q=Seq Q' P1 \<and> xs=(Q',t)#xs'"
     using seq Seq seq_xs_no_empty
     by meson 
  then have "0<m" using Seq(1,5,6) min
    using SmallStepCon.redex.simps(4) stepc_elim_cases_Seq_Seq by fastforce
  thus ?case by (metis min min_call_def not_gr0 p0_cptn) 
next
  case (Catch P0 P1)
 then obtain xs s' s'' where 
          p0_cptn:"(n, \<Gamma>,(P0, s)#xs) \<in> cptn_mod_nest_call"  and 
          seq:"catch_cond_nest ((Q,t)#cfg1) P1 xs P0 s s'' s' \<Gamma> n"
  using div_catch_nest[of n \<Gamma> cfg] unfolding min_call_def by blast
  then obtain m where min:"min_call m \<Gamma> ((P0, s)#xs)"
    using minimum_nest_call by blast 
  obtain Q' xs' where xs':"Q=Catch Q' P1 \<and> xs=(Q',t)#xs'"
     using catch_xs_no_empty[OF seq Catch(4)] Catch by blast
  then have "0<m" using Catch(1,5,6) min
    using SmallStepCon.redex.simps(4) stepc_elim_cases_Catch_Catch by fastforce
  thus ?case by (metis min min_call_def not_gr0 p0_cptn)
qed(auto)

  

(* lemma elim_redex_call_cptn_mod_min_nest_call:
 assumes a0:"min_call n \<Gamma> cfg" and
         a1:"cfg = (P,s)#(Q,t)#cfg1" and
         a2:"redex P = Call f \<and>  
             \<Gamma> f = Some bdy \<and> (\<exists>sa. s=Normal sa) \<and> t=s " and
         a3:"biggest_nest_call P s ((Q,t)#cfg1) \<Gamma> n"  
 shows "min_call n \<Gamma> ((Q,t)#cfg1)"
using a0 a1 a2 a3 
proof (induct P arbitrary: Q cfg1 cfg s t n)  
  case Cond thus ?case by fastforce
next
  case (Seq P0 P1) 
  then obtain xs s' s'' where 
          p0_cptn:"(n, \<Gamma>,(P0, s)#xs) \<in> cptn_mod_nest_call"  and 
          seq:"seq_cond_nest ((Q,t)#cfg1) P1 xs P0 s s'' s' \<Gamma> n"
  using div_seq_nest[of n \<Gamma> cfg] unfolding min_call_def by blast
  
  show ?case using seq unfolding seq_cond_nest_def 
  proof
    assume ass:"(Q, t) # cfg1 = map (lift P1) xs"   
    then obtain Q' xs' where xs':"Q=Seq Q' P1 \<and> xs=(Q',t)#xs'"
      unfolding lift_def by fastforce
    then have ctpn_P0:"(P0, s) # xs = (P0, s) # (Q', t) # xs'" by auto
    then have min_p0:"min_call n \<Gamma> ((P0, s)#xs)"
      using min_call_seq_c1_not_finish[OF Seq(3) Seq(4) p0_cptn] ass by auto
    then have ex_xs:"\<exists>xs. min_call n \<Gamma> ((P0, s)#xs) \<and> (Q, t) # cfg1 = map (lift P1) xs" 
      using ass by auto
    then have min_xs:"min_call n \<Gamma> ((P0, s)#xs) \<and> (Q, t) # cfg1 = map (lift P1) xs" 
      using min_p0 ass by auto
    have "xs= (SOME xs. (min_call n \<Gamma> ((P0, s)#xs) \<and> (Q, t) # cfg1 = map (lift P1) xs))"
    proof -
      have "\<forall>xsa. min_call n \<Gamma> ((P0, s)#xsa) \<and> (Q, t) # cfg1 = map (lift P1) xsa \<longrightarrow> xsa = xs"
        using xs' ass by (metis map_lift_eq_xs_xs')
      thus ?thesis using min_xs some_equality by (metis (mono_tags, lifting))
    qed
    then have big:"biggest_nest_call P0 s ((Q', t) # xs') \<Gamma> n" 
      using biggest_nest_call.simps(1)[of P0 P1 s "((Q, t) # cfg1)" \<Gamma> n] 
            Seq(6) xs' ex_xs by auto         
    have reP0:"redex P0 = (Call f) \<and> \<Gamma> f = Some bdy \<and> 
              (\<exists>saa. s = Normal saa) \<and> t = s " using Seq(5) xs' by auto    
    have min_call:"min_call n \<Gamma> ((Q', t) # xs')" 
       using Seq(1)[OF min_p0 ctpn_P0 reP0] big xs' ass by auto
    thus ?thesis using min_call_seq_not_finish[OF min_call] ass xs' by blast
  next
    assume ass:"fst (((P0, s) # xs) ! length xs) = LanguageCon.com.Skip \<and>
                  (\<exists>ys. (n, \<Gamma>, (P1, snd (((P0, s) # xs) ! length xs)) # ys) \<in> cptn_mod_nest_call \<and>
                  (Q, t) # cfg1 = map (lift P1) xs @ (P1, snd (((P0, s) # xs) ! length xs)) # ys) \<or>
                fst (((P0, s) # xs) ! length xs) = LanguageCon.com.Throw \<and>
                  snd (last ((P0, s) # xs)) = Normal s' \<and>
                  s = Normal s'' \<and>
                  (\<exists>ys. (n, \<Gamma>, (LanguageCon.com.Throw, Normal s') # ys) \<in> cptn_mod_nest_call \<and>
                     (Q, t) # cfg1 = map (lift P1) xs @ (LanguageCon.com.Throw, Normal s') # ys)"
    {assume ass:"fst (((P0, s) # xs) ! length xs) = LanguageCon.com.Skip \<and>
            (\<exists>ys. (n, \<Gamma>, (P1, snd (((P0, s) # xs) ! length xs)) # ys) \<in> cptn_mod_nest_call \<and>
            (Q, t) # cfg1 = map (lift P1) xs @ (P1, snd (((P0, s) # xs) ! length xs)) # ys)"     
     have ?thesis 
     proof (cases xs)
       case Nil thus ?thesis using Seq ass by fastforce
     next
       case (Cons xa xsa)
       then obtain ys where 
         seq2_ass:"fst (((P0, s) # xs) ! length xs) = LanguageCon.com.Skip \<and> 
          (n, \<Gamma>, (P1, snd (((P0, s) # xs) ! length xs)) # ys) \<in> cptn_mod_nest_call \<and>
          (Q, t) # cfg1 = map (lift P1) (xa#xsa) @ (P1, snd (((P0, s) # xs) ! length xs)) # ys"
          using ass by auto 
        then obtain mq mp1 where 
         min_call_q:"min_call mq \<Gamma> ((P0, s) # xs)" and
         min_call_p1:"min_call mp1 \<Gamma> ((P1, snd (((P0, s) # xs) ! length xs)) # ys)"         
       using seq2_ass minimum_nest_call p0_cptn by fastforce               
       then have mp: "mq\<le>n \<and> mp1 \<le>n"
         using seq2_ass min_call_less_eq_n[of n \<Gamma> P0 s xs P1 ys  mq mp1] 
             Seq(3,4) p0_cptn by (simp add: last_length)
       have min_call:"min_call n \<Gamma> ((P0, s) # xs) \<or> 
             min_call n \<Gamma> ((P1, snd (((P0, s) # xs) ! length xs)) # ys)"
         using seq2_ass min_call_seq2[of n \<Gamma> P0 P1 s "(Q, t) # cfg1" xs ys] 
             Seq(3,4) p0_cptn by (simp add: last_length local.Cons)       
       from seq2_ass obtain Q' where Q':"Q=Seq Q' P1 \<and> xa=(Q',t)"          
       unfolding lift_def   
         by (metis (mono_tags, lifting) fst_conv length_greater_0_conv 
             list.simps(3) list.simps(9) nth_Cons_0 nth_append prod.case_eq_if prod.collapse snd_conv)  
       then have q'_n_cptn:"(n,\<Gamma>,(Q',t)#xsa)\<in>cptn_mod_nest_call" using p0_cptn Q' Cons
         using elim_cptn_mod_nest_call_n by blast 
       show ?thesis
       proof(cases "mp1=n")
         case True
         then have "min_call n \<Gamma> ((P1, snd (((P0, s) # xs) ! length xs)) # ys)"
           using min_call_p1 by auto
         then have min_P1:"min_call n \<Gamma> ((P1, snd ((xa # xsa) ! length xsa)) # ys)"
           using Cons seq2_ass by fastforce         
         then have p1_n_cptn:"(n, \<Gamma>,  (Q, t) # cfg1) \<in> cptn_mod_nest_call"
           using Seq.prems(1) Seq.prems(2) elim_cptn_mod_nest_call_n min_call_def by blast
         also then have "(\<forall>m<n. (m, \<Gamma>, (Q, t) # cfg1) \<notin> cptn_mod_nest_call)" 
         proof-
         { fix m
           assume ass:"m<n" 
           { assume Q_m:"(m, \<Gamma>, (Q, t) # cfg1) \<in> cptn_mod_nest_call"             
            then have False using min_P1 ass Q' Cons unfolding min_call_def
            proof -
              assume a1: "(n, \<Gamma>, (P1, snd ((xa # xsa) ! length xsa)) # ys) \<in> cptn_mod_nest_call \<and> (\<forall>m<n. (m, \<Gamma>, (P1, snd ((xa # xsa) ! length xsa)) # ys) \<notin> cptn_mod_nest_call)"
              have f2: "\<forall>n f ps. (n, f, ps) \<notin> cptn_mod_nest_call \<or> (\<forall>x c ca psa. ps \<noteq> (LanguageCon.com.Seq (c::('b, 'a, 'c,'d) LanguageCon.com) ca, x) # psa \<or> (\<exists>ps b ba. (n, f, (c, x) # ps) \<in> cptn_mod_nest_call \<and> seq_cond_nest psa ca ps c x ba b f n))"
                using div_seq_nest by blast
              have f3: "(P1, snd (last ((Q', t) # xsa))) # ys = (P1, snd (((P0, s) # xs) ! length xs)) # ys"
                by (simp add: Q' last_length local.Cons)
              have "fst (last ((Q', t) # xsa)) = LanguageCon.com.Skip"
                by (metis (no_types) Q' last_ConsR last_length list.distinct(1) local.Cons seq2_ass)
              then show ?thesis
                using f3 f2 a1 by (metis (no_types) Cons_lift_append Q' Seq_P_Ends_Normal Q_m ass seq2_ass)
            qed
           } 
         } then show ?thesis by auto
         qed           
         ultimately show ?thesis unfolding min_call_def by auto
       next
         case False
         then have "mp1<n" using mp by auto
         then have not_min_call_p1_n:"\<not> min_call n \<Gamma> ((P1, snd (last ((P0, s) # xs))) # ys)"
           using min_call_p1 last_length unfolding min_call_def by metis
         then have min_call:"min_call n \<Gamma> ((P0, s) # xs)" 
           using min_call last_length unfolding min_call_def by metis
         then have "(P0, s) # xs = (P0, s) # xa#xsa"
           using Cons by auto
         then have big:"biggest_nest_call P0 s (((Q',t))#xsa) \<Gamma> n"
         proof-
           have "\<not>(\<exists>xs. min_call n \<Gamma> ((P0, s)#xs) \<and> (Q, t) # cfg1 = map (lift P1) xs)"
             using min_call seq2_ass Cons
            proof -
              have "min_call n \<Gamma> ((LanguageCon.com.Seq P0 P1, s) # (Q, t) # cfg1)"
                using Seq.prems(1) Seq.prems(2) by blast
              then show ?thesis
                by (metis (no_types) Seq_P_Not_finish append_Nil2 list.simps(3) 
                          local.Cons min_call_def same_append_eq seq seq2_ass)
            qed
            moreover have "\<exists>xs ys. cond_seq_1 n \<Gamma> P0 s xs P1 ((Q, t) # cfg1) ys"
              using seq2_ass p0_cptn unfolding cond_seq_1_def 
              by (metis last_length local.Cons) 
            moreover have "(SOME xs. \<exists>ys. cond_seq_1 n \<Gamma> P0 s xs P1 ((Q, t) # cfg1) ys) = xs"  
            proof -
              let ?P = "\<lambda>xsa. \<exists>ys. (n, \<Gamma>, (P0, s) # xsa) \<in> cptn_mod_nest_call \<and>
                   fst (last ((P0, s) # xsa)) = LanguageCon.com.Skip \<and>
                   (n, \<Gamma>, (P1, snd (last ((P0, s) # xsa))) # ys) \<in> cptn_mod_nest_call \<and>
                   (Q, t) # cfg1 = map (lift P1) xsa @ (P1, snd (last ((P0, s) # xsa))) # ys"             
              have "(\<And>x. \<exists>ys. (n, \<Gamma>, (P0, s) # x) \<in> cptn_mod_nest_call \<and>
               fst (last ((P0, s) # x)) = LanguageCon.com.Skip \<and>
               (n, \<Gamma>, (P1, snd (last ((P0, s) # x))) # ys) \<in> cptn_mod_nest_call \<and>
               (Q, t) # cfg1 = map (lift P1) x @ (P1, snd (last ((P0, s) # x))) # ys \<Longrightarrow>
                   x = xs)"              
              by (metis Seq_P_Ends_Normal cptn_mod_nest_call.CptnModNestSeq2 seq)
              moreover have "\<exists>ys. (n, \<Gamma>, (P0, s) # xs) \<in> cptn_mod_nest_call \<and>
                   fst (last ((P0, s) # xs)) = LanguageCon.com.Skip \<and>
                   (n, \<Gamma>, (P1, snd (last ((P0, s) # xs))) # ys) \<in> cptn_mod_nest_call \<and>
                   (Q, t) # cfg1 = map (lift P1) xs @ (P1, snd (last ((P0, s) # xs))) # ys"
                using ass  p0_cptn by (simp add: last_length)               
              ultimately show ?thesis using some_equality[of ?P xs]
                 unfolding cond_seq_1_def by blast 
            qed
            moreover have "(SOME ys. cond_seq_1 n \<Gamma> P0 s xs P1 ((Q, t) # cfg1) ys) = ys"
            proof -
               let ?P = "\<lambda>ys. (n, \<Gamma>, (P0, s) # xs) \<in> cptn_mod_nest_call \<and>
                   fst (last ((P0, s) # xs)) = LanguageCon.com.Skip \<and>
                   (n, \<Gamma>, (P1, snd (last ((P0, s) # xs))) # ys) \<in> cptn_mod_nest_call \<and>
                   (Q, t) # cfg1 = map (lift P1) xs @ (P1, snd (last ((P0, s) # xs))) # ys"
                have "(n, \<Gamma>, (P0, s) # xs) \<in> cptn_mod_nest_call \<and>
                   fst (last ((P0, s) # xs)) = LanguageCon.com.Skip \<and>
                   (n, \<Gamma>, (P1, snd (last ((P0, s) # xs))) # ys) \<in> cptn_mod_nest_call \<and>
                   (Q, t) # cfg1 = map (lift P1) xs @ (P1, snd (last ((P0, s) # xs))) # ys"
                 using p0_cptn seq2_ass Cons   by (simp add: last_length) 
                then show ?thesis using some_equality[of ?P ys]
                 unfolding cond_seq_1_def by fastforce      
            qed
            ultimately have "biggest_nest_call P0 s xs \<Gamma> n"
              using not_min_call_p1_n Seq(6) 
                    biggest_nest_call.simps(1)[of P0 P1 s "(Q, t) # cfg1" \<Gamma> n]
              by presburger
            then show ?thesis  using Cons Q' by auto
          qed
          have C:"(P0, s) # xs = (P0, s) # (Q', t) # xsa" using Cons Q' by auto
          have reP0:"redex P0 = (Call f) \<and> \<Gamma> f = Some bdy \<and> 
            (\<exists>saa. s = Normal saa) \<and> t = s" using Seq(5) Q' by auto
          then have min_call:"min_call n \<Gamma> ((Q', t) # xsa)" using Seq(1)[OF min_call C reP0 big]
            by auto
          have p1_n_cptn:"(n, \<Gamma>,  (Q, t) # cfg1) \<in> cptn_mod_nest_call"
            using Seq.prems(1) Seq.prems(2) elim_cptn_mod_nest_call_n min_call_def by blast
          also then have "(\<forall>m<n. (m, \<Gamma>, (Q, t) # cfg1) \<notin> cptn_mod_nest_call)" 
          proof-
           { fix m
             assume ass:"m<n" 
             { assume Q_m:"(m, \<Gamma>, (Q, t) # cfg1) \<in> cptn_mod_nest_call" 
               then obtain xsa' s1 s1' where 
                  p0_cptn:"(m, \<Gamma>,(Q', t)#xsa') \<in> cptn_mod_nest_call"  and
                  seq:"seq_cond_nest cfg1 P1 xsa' Q' t s1 s1' \<Gamma> m"
               using div_seq_nest[of m \<Gamma> "(Q, t) # cfg1"] Q' by blast
               then have "xsa=xsa'" 
                 using seq2_ass 
                 Seq_P_Ends_Normal[of cfg1 P1 xsa Q' t ys m \<Gamma> xsa' s1 s1'] Cons
                 by (metis Cons_lift_append Q' Q_m last.simps last_length list.inject list.simps(3)) 
               then have False using min_call p0_cptn ass unfolding min_call_def by auto 
             } 
           } then show ?thesis by auto qed
             
         ultimately show ?thesis unfolding min_call_def by auto
       qed    
     qed
    }note l=this
    {assume ass:"fst (((P0, s) # xs) ! length xs) = LanguageCon.com.Throw \<and>
             snd (last ((P0, s) # xs)) = Normal s' \<and>
            s = Normal s'' \<and> (\<exists>ys. (n, \<Gamma>, (LanguageCon.com.Throw, Normal s') # ys) \<in> cptn_mod_nest_call \<and>
          (Q, t) # cfg1 = map (lift P1) xs @ (LanguageCon.com.Throw, Normal s') # ys)"          
     have ?thesis
     proof (cases "\<Gamma>\<turnstile>\<^sub>c(LanguageCon.com.Seq P0 P1, s) \<rightarrow> (Q,t)")
       case True 
       thus  ?thesis
       proof (cases xs)
          case Nil thus ?thesis using Seq ass by fastforce
       next
         case (Cons xa xsa)
         then obtain ys where 
           seq2_ass:"fst (((P0, s) # xs) ! length xs) = LanguageCon.com.Throw \<and>
             snd (last ((P0, s) # xs)) = Normal s' \<and>
            s = Normal s'' \<and>  (n, \<Gamma>, (LanguageCon.com.Throw, Normal s') # ys) \<in> cptn_mod_nest_call \<and>
           (Q, t) # cfg1 = map (lift P1) xs @ (LanguageCon.com.Throw, Normal s') # ys"
            using ass by auto 
         then have t_eq:"t=Normal s''" using Seq by fastforce
         obtain mq mp1 where 
           min_call_q:"min_call mq \<Gamma> ((P0, s) # xs)" and
           min_call_p1:"min_call mp1 \<Gamma> ((Throw, snd (((P0, s) # xs) ! length xs)) # ys)"         
         using seq2_ass minimum_nest_call p0_cptn by (metis last_length)
         then have mp1_zero:"mp1=0" by (simp add: throw_min_nested_call_0)
         then have min_call: "min_call n \<Gamma> ((P0, s) # xs)"  
           using seq2_ass min_call_seq3[of n \<Gamma> P0 P1 s "(Q, t) # cfg1" s'' xs s' ys]
             Seq(3,4) p0_cptn by (metis last_length)      
         have n_z:"n>0" using redex_call_cptn_mod_min_nest_call_gr_zero[OF Seq(3) Seq(4) Seq(5) True]
           by auto          
         from seq2_ass obtain Q' where Q':"Q=Seq Q' P1 \<and> xa=(Q',t)"          
           unfolding lift_def using Cons
          proof -
            assume a1: "\<And>Q'. Q = LanguageCon.com.Seq Q' P1 \<and> xa = (Q', t) \<Longrightarrow> thesis"
            have "(LanguageCon.com.Seq (fst xa) P1, snd xa) = ((Q, t) # cfg1) ! 0"
             using seq2_ass unfolding lift_def
              by (simp add: Cons case_prod_unfold)
            then show ?thesis
              using a1 by fastforce
          qed  
         have big_call:"biggest_nest_call P0 s ((Q',t)#xsa) \<Gamma> n"
         proof-
           have "\<not>(\<exists>xs. min_call n \<Gamma> ((P0, s)#xs) \<and> (Q, t) # cfg1 = map (lift P1) xs)"
             using min_call seq2_ass Cons Seq.prems(1) Seq.prems(2)
           by (metis Seq_P_Not_finish append_Nil2 list.simps(3) min_call_def same_append_eq seq)
           moreover have "\<not>(\<exists>xs ys. cond_seq_1 n \<Gamma> P0 s xs P1 ((Q, t) # cfg1) ys)" 
             using min_call seq2_ass p0_cptn Cons Seq.prems(1) Seq.prems(2) 
             unfolding cond_seq_1_def
            by (metis com.distinct(17) com.distinct(71) last_length 
                      map_lift_some_eq seq_and_if_not_eq(4))
           moreover have "(SOME xs. \<exists>ys s' s''. cond_seq_2 n \<Gamma> P0 s xs P1 ((Q, t) # cfg1) ys s' s'') = xs"
           proof-
             let ?P="\<lambda>xsa. \<exists>ys s' s''. s= Normal s'' \<and> 
                    (n,\<Gamma>, (P0, s)#xs) \<in> cptn_mod_nest_call \<and> 
                    fst(last ((P0, s)#xs)) = Throw \<and>
                    snd(last ((P0, s)#xs)) = Normal s' \<and> 
                    (n,\<Gamma>,(Throw,Normal s')#ys) \<in> cptn_mod_nest_call \<and> 
                     ((Q, t) # cfg1)=(map (lift P1) xs)@((Throw,Normal s')#ys)"
             have "(\<And>x. \<exists>ys s' s''. s= Normal s'' \<and> 
                    (n,\<Gamma>, (P0, s)#x) \<in> cptn_mod_nest_call \<and> 
                    fst(last ((P0, s)#x)) = Throw \<and>
                    snd(last ((P0, s)#x)) = Normal s' \<and> 
                    (n,\<Gamma>,(Throw,Normal s')#ys) \<in> cptn_mod_nest_call \<and> 
                     ((Q, t) # cfg1)=(map (lift P1) x)@((Throw,Normal s')#ys) \<Longrightarrow>
                    x=xs)" using map_lift_some_eq seq2_ass by fastforce
             moreover have "\<exists>ys s' s''. s= Normal s'' \<and> 
                    (n,\<Gamma>, (P0, s)#xs) \<in> cptn_mod_nest_call \<and> 
                    fst(last ((P0, s)#xs)) = Throw \<and>
                    snd(last ((P0, s)#xs)) = Normal s' \<and> 
                    (n,\<Gamma>,(Throw,Normal s')#ys) \<in> cptn_mod_nest_call \<and> 
                     ((Q, t) # cfg1)=(map (lift P1) xs)@((Throw,Normal s')#ys)" 
                using ass p0_cptn by (simp add: last_length Cons)
            ultimately show ?thesis using some_equality[of ?P xs]
                 unfolding cond_seq_2_def by blast
         qed
           ultimately have "biggest_nest_call P0 s xs \<Gamma> n"
            using  Seq(6) 
                  biggest_nest_call.simps(1)[of P0 P1 s "(Q, t) # cfg1" \<Gamma> n]
            by presburger
           then show ?thesis  using Cons Q' by auto
         qed         
         have min_call:"min_call n \<Gamma> ((Q',t)#xsa)" 
           using Seq(1)[OF min_call _ _ big_call] Seq(5) Cons Q' by fastforce   
         then have p1_n_cptn:"(n, \<Gamma>,  (Q, t) # cfg1) \<in> cptn_mod_nest_call"
            using Seq.prems(1) Seq.prems(2) elim_cptn_mod_nest_call_n min_call_def by blast   
         also then have "(\<forall>m<n. (m, \<Gamma>, (Q, t) # cfg1) \<notin> cptn_mod_nest_call)" 
          proof-
           { fix m
             assume ass:"m<n" 
             { assume Q_m:"(m, \<Gamma>, (Q, t) # cfg1) \<in> cptn_mod_nest_call" 
               then obtain xsa' s1 s1' where 
                  p0_cptn:"(m, \<Gamma>,(Q', t)#xsa') \<in> cptn_mod_nest_call"  and
                  seq:"seq_cond_nest cfg1 P1 xsa' Q' (Normal s'') s1 s1' \<Gamma> m"
               using div_seq_nest[of m \<Gamma> "(Q, t) # cfg1"] Q' t_eq by blast
               then have "xsa=xsa'" 
                 using seq2_ass 
                 Seq_P_Ends_Abort[of cfg1 P1 xsa s' ys Q' s'' m \<Gamma> xsa' s1 s1' ] Cons Q' Q_m
                 by (simp add: Cons_lift_append last_length t_eq)                 
               then have False using min_call p0_cptn ass unfolding min_call_def by auto 
             } 
           } then show ?thesis by auto qed          
         ultimately show ?thesis unfolding min_call_def by auto
       qed
     next
       case False 
       then have env:"\<Gamma>\<turnstile>\<^sub>c(LanguageCon.com.Seq P0 P1, s) \<rightarrow>\<^sub>e (Q,t)" using Seq
         by (meson elim_cptn_mod_nest_step_c min_call_def)
       moreover then have Q:"Q=Seq P0 P1" using env_c_c' by blast        
       ultimately show ?thesis using Seq
        proof -
          obtain nn :: "(('b, 'a, 'c,'d) LanguageCon.com \<times> ('b, 'c) xstate) list \<Rightarrow> 
                         ('a \<Rightarrow> ('b, 'a, 'c,'d) LanguageCon.com option) \<Rightarrow> nat \<Rightarrow> nat" where
            f1: "\<forall>x0 x1 x2. (\<exists>v3<x2. (v3, x1, x0) \<in> cptn_mod_nest_call) = (nn x0 x1 x2 < x2 \<and> (nn x0 x1 x2, x1, x0) \<in> cptn_mod_nest_call)"
            by moura
          have f2: "(n, \<Gamma>, (LanguageCon.com.Seq P0 P1, s) # (Q, t) # cfg1) \<in> cptn_mod_nest_call \<and> (\<forall>n. \<not> n < n \<or> (n, \<Gamma>, (LanguageCon.com.Seq P0 P1, s) # (Q, t) # cfg1) \<notin> cptn_mod_nest_call)"
            using local.Seq(3) local.Seq(4) min_call_def by blast
          then have "\<not> nn ((Q, t) # cfg1) \<Gamma> n < n \<or> (nn ((Q, t) # cfg1) \<Gamma> n, \<Gamma>, (Q, t) # cfg1) \<notin> cptn_mod_nest_call"
            using False env env_c_c'  not_func_redex_cptn_mod_nest_n_env 
            by (metis Seq.prems(1) Seq.prems(2) min_call_def)
          then show ?thesis
            using f2 f1 by (meson elim_cptn_mod_nest_call_n min_call_def)
        qed
     qed          
    }
    thus ?thesis using l ass by fastforce
  qed
next
  case (Catch P0 P1) 
then obtain xs s' s'' where 
          p0_cptn:"(n, \<Gamma>,(P0, s)#xs) \<in> cptn_mod_nest_call"  and 
          catch:"catch_cond_nest ((Q,t)#cfg1) P1 xs P0 s s'' s' \<Gamma> n"
  using div_catch_nest[of n \<Gamma> cfg] unfolding min_call_def by blast
  
  show ?case using catch unfolding catch_cond_nest_def 
  proof
    assume ass:"(Q, t) # cfg1 = map (lift_catch P1) xs"   
    then obtain Q' xs' where xs':"Q=Catch Q' P1 \<and> xs=(Q',t)#xs'"
      unfolding lift_catch_def by fastforce
    then have ctpn_P0:"(P0, s) # xs = (P0, s) # (Q', t) # xs'" by auto
    then have min_p0:"min_call n \<Gamma> ((P0, s)#xs)"
      using min_call_catch_c1_not_finish[OF Catch(3) Catch(4) p0_cptn] ass by auto
    then have ex_xs:"\<exists>xs. min_call n \<Gamma> ((P0, s)#xs) \<and> (Q, t) # cfg1 = map (lift_catch P1) xs" 
      using ass by auto
    then have min_xs:"min_call n \<Gamma> ((P0, s)#xs) \<and> (Q, t) # cfg1 = map (lift_catch P1) xs" 
      using min_p0 ass by auto
    have "xs= (SOME xs. (min_call n \<Gamma> ((P0, s)#xs) \<and> (Q, t) # cfg1 = map (lift_catch P1) xs))"
    proof -
      have "\<forall>xsa. min_call n \<Gamma> ((P0, s)#xsa) \<and> (Q, t) # cfg1 = map (lift_catch P1) xsa \<longrightarrow> xsa = xs"
        using xs' ass by (metis map_lift_catch_eq_xs_xs')
      thus ?thesis using min_xs some_equality by (metis (mono_tags, lifting))
    qed
    then have big:"biggest_nest_call P0 s ((Q', t) # xs') \<Gamma> n" 
      using biggest_nest_call.simps(2)[of P0 P1 s "((Q, t) # cfg1)" \<Gamma> n] 
            Catch(6) xs' ex_xs by auto          
    have reP0:"redex P0 = (Call f) \<and> \<Gamma> f = Some bdy \<and> 
              (\<exists>saa. s = Normal saa) \<and> t = s " using Catch(5) xs' by auto    
    have min_call:"min_call n \<Gamma> ((Q', t) # xs')" 
       using Catch(1)[OF min_p0 ctpn_P0 reP0] big xs' ass by auto
    thus ?thesis using min_call_catch_not_finish[OF min_call] ass xs' by blast
  next
    assume ass:"fst (((P0, s) # xs) ! length xs) = LanguageCon.com.Throw \<and>
                snd (last ((P0, s) # xs)) = Normal s' \<and>
                s = Normal s'' \<and>
               (\<exists>ys. (n, \<Gamma>, (P1, snd (((P0, s) # xs) ! length xs)) # ys) \<in> cptn_mod_nest_call \<and>
                  (Q, t) # cfg1 = map (lift_catch P1) xs @ (P1, snd (((P0, s) # xs) ! length xs)) # ys) \<or>
                   fst (((P0, s) # xs) ! length xs) = LanguageCon.com.Skip \<and>
                  (\<exists>ys. (n, \<Gamma>, (LanguageCon.com.Skip, snd (last ((P0, s) # xs))) # ys) \<in> cptn_mod_nest_call \<and>
                (Q, t) # cfg1 = map (lift_catch P1) xs @ (LanguageCon.com.Skip, snd (last ((P0, s) # xs))) # ys)" 
    {assume ass:"fst (((P0, s) # xs) ! length xs) = LanguageCon.com.Throw \<and>
                snd (last ((P0, s) # xs)) = Normal s' \<and>
                s = Normal s'' \<and>
               (\<exists>ys. (n, \<Gamma>, (P1, snd (((P0, s) # xs) ! length xs)) # ys) \<in> cptn_mod_nest_call \<and>
                  (Q, t) # cfg1 = map (lift_catch P1) xs @ (P1, snd (((P0, s) # xs) ! length xs)) # ys)"     
     have ?thesis 
     proof (cases xs)
       case Nil thus ?thesis using Catch ass by fastforce
     next
       case (Cons xa xsa)
       then obtain ys where 
         catch2_ass:"fst (((P0, s) # xs) ! length xs) = LanguageCon.com.Throw \<and>
                snd (last ((P0, s) # xs)) = Normal s' \<and>
                s = Normal s'' \<and>
                (n, \<Gamma>, (P1, snd (((P0, s) # xs) ! length xs)) # ys) \<in> cptn_mod_nest_call \<and>
                (Q, t) # cfg1 = map (lift_catch P1) xs @ (P1, snd (((P0, s) # xs) ! length xs)) # ys"
          using ass by auto 
        then obtain mq mp1 where 
         min_call_q:"min_call mq \<Gamma> ((P0, s) # xs)" and
         min_call_p1:"min_call mp1 \<Gamma> ((P1, snd (((P0, s) # xs) ! length xs)) # ys)"         
       using catch2_ass minimum_nest_call p0_cptn by fastforce               
       then have mp: "mq\<le>n \<and> mp1 \<le>n"
         using catch2_ass min_call_less_eq_n 
             Catch(3,4) p0_cptn by (metis last_length) 
       have min_call:"min_call n \<Gamma> ((P0, s) # xs) \<or> 
             min_call n \<Gamma> ((P1, snd (((P0, s) # xs) ! length xs)) # ys)"
         using catch2_ass min_call_catch3[of n \<Gamma> P0 P1 s'' "(Q, t) # cfg1" xs s' ys] 
             Catch(3,4) p0_cptn by (metis last_length)       
       from catch2_ass obtain Q' where Q':"Q=Catch Q' P1 \<and> xa=(Q',t)"          
       unfolding lift_catch_def
        proof -
          assume a1: "\<And>Q'. Q = LanguageCon.com.Catch Q' P1 \<and> xa = (Q', t) \<Longrightarrow> thesis"
          assume "fst (((P0, s) # xs) ! length xs) = LanguageCon.com.Throw \<and> snd (last ((P0, s) # xs)) = Normal s' \<and> s = Normal s'' \<and> (n, \<Gamma>, (P1, snd (((P0, s) # xs) ! length xs)) # ys) \<in> cptn_mod_nest_call \<and> (Q, t) # cfg1 = map (\<lambda>(P, s). (LanguageCon.com.Catch P P1, s)) xs @ (P1, snd (((P0, s) # xs) ! length xs)) # ys"
          then have "(LanguageCon.com.Catch (fst xa) P1, snd xa) = ((Q, t) # cfg1) ! 0"
            by (simp add: local.Cons prod.case_eq_if)
          then show ?thesis
            using a1 by force
        qed            
       then have q'_n_cptn:"(n,\<Gamma>,(Q',t)#xsa)\<in>cptn_mod_nest_call" using p0_cptn Q' Cons
         using elim_cptn_mod_nest_call_n by blast 
       show ?thesis
       proof(cases "mp1=n")
         case True
         then have "min_call n \<Gamma> ((P1, snd (((P0, s) # xs) ! length xs)) # ys)"
           using min_call_p1 by auto
         then have min_P1:"min_call n \<Gamma> ((P1, snd ((xa # xsa) ! length xsa)) # ys)"
           using Cons catch2_ass by fastforce         
         then have p1_n_cptn:"(n, \<Gamma>,  (Q, t) # cfg1) \<in> cptn_mod_nest_call"
           using Catch.prems(1) Catch.prems(2) elim_cptn_mod_nest_call_n min_call_def by blast
         also then have "(\<forall>m<n. (m, \<Gamma>, (Q, t) # cfg1) \<notin> cptn_mod_nest_call)" 
         proof-
         { fix m
           assume ass:"m<n" 
           { assume Q_m:"(m, \<Gamma>, (Q, t) # cfg1) \<in> cptn_mod_nest_call"   
             then have t_eq_s:"t=Normal s''" using Catch catch2_ass by fastforce                      
            then obtain xsa' s1 s1' where 
                  p0_cptn:"(m, \<Gamma>,(Q', t)#xsa') \<in> cptn_mod_nest_call"  and
                  catch_cond:"catch_cond_nest cfg1 P1 xsa' Q' (Normal s'') s1 s1' \<Gamma> m"
              using Q_m div_catch_nest[of m \<Gamma> "(Q, t) # cfg1"] Q' by blast
            have fst:"fst (last ((Q', Normal s'') # xsa)) = LanguageCon.com.Throw" 
              using catch2_ass Cons Q' by (simp add: last_length  t_eq_s)
            have cfg:"cfg1 = map (lift_catch P1) xsa @ (P1, snd (last ((Q', Normal s'') # xsa))) # ys"
              using catch2_ass Cons Q' by (simp add: last_length  t_eq_s)
            have snd:"snd (last ((Q', Normal s'') # xsa)) = Normal s'"
              using catch2_ass Cons Q' by (simp add: last_length  t_eq_s)
            then have "xsa=xsa' \<and> 
                   (m, \<Gamma>, (P1, snd (((Q', Normal s'') # xsa) ! length xsa)) # ys) \<in> cptn_mod_nest_call" 
              using catch2_ass Catch_P_Ends_Normal[OF cfg fst snd catch_cond] Cons
              by auto 
            then have False using min_P1 ass Q' t_eq_s unfolding min_call_def by auto              
           } 
         } then show ?thesis by auto
         qed           
         ultimately show ?thesis unfolding min_call_def by auto
       next
         case False
         then have "mp1<n" using mp by auto
         then have not_min_call_p1_n:"\<not> min_call n \<Gamma> ((P1, snd (last ((P0, s) # xs))) # ys)"
           using min_call_p1 last_length unfolding min_call_def by metis
         then have min_call:"min_call n \<Gamma> ((P0, s) # xs)" 
           using min_call last_length unfolding min_call_def by metis
         then have "(P0, s) # xs = (P0, s) # xa#xsa"
           using Cons by auto
         then have big:"biggest_nest_call P0 s (((Q',t))#xsa) \<Gamma> n"
         proof-
           have "\<not>(\<exists>xs. min_call n \<Gamma> ((P0, s)#xs) \<and> (Q, t) # cfg1 = map (lift_catch P1) xs)"
             using min_call catch2_ass Cons
            proof -
              have "min_call n \<Gamma> ((Catch P0 P1, s) # (Q, t) # cfg1)"
                using Catch.prems(1) Catch.prems(2) by blast
              then show ?thesis
                by (metis (no_types) Catch_P_Not_finish append_Nil2 list.simps(3) 
                     same_append_eq catch catch2_ass)
            qed
            moreover have "\<not>(\<exists>xs ys. cond_catch_1 n \<Gamma> P0 s xs P1 ((Q, t) # cfg1) ys)"
              unfolding cond_catch_1_def using catch2_ass 
              by (metis Catch_P_Ends_Skip LanguageCon.com.distinct(17) catch last_length)
            moreover have "\<exists>xs ys. cond_catch_2 n \<Gamma> P0 s xs P1 ((Q, t) # cfg1) ys s' s''"
              using catch2_ass p0_cptn unfolding cond_catch_2_def last_length
              by metis 
            moreover have "(SOME xs. \<exists>ys s' s''. cond_catch_2 n \<Gamma> P0 s xs P1 ((Q, t) # cfg1) ys s' s'') = xs"  
            proof -
              let ?P = "\<lambda>xsa. s = Normal s'' \<and>
                              (n, \<Gamma>, (P0, s) # xsa) \<in> cptn_mod_nest_call \<and>
                              fst (last ((P0, s) # xsa)) = LanguageCon.com.Throw \<and>
                              snd (last ((P0, s) # xsa)) = Normal s' \<and>
                               (n, \<Gamma>, (P1, Normal s') # ys) \<in> cptn_mod_nest_call \<and> 
                               (Q, t) # cfg1 = map (lift_catch P1) xsa @ (P1, Normal s') # ys"             
              have "(\<And>x. \<exists>ys s' s''. s = Normal s'' \<and>
                              (n, \<Gamma>, (P0, s) # x) \<in> cptn_mod_nest_call \<and>
                              fst (last ((P0, s) # x)) = LanguageCon.com.Throw \<and>
                              snd (last ((P0, s) # x)) = Normal s' \<and>
                               (n, \<Gamma>, (P1, Normal s') # ys) \<in> cptn_mod_nest_call \<and> 
                               (Q, t) # cfg1 = map (lift_catch P1) x @ (P1, Normal s') # ys \<Longrightarrow>
                   x = xs)"              
              by (metis Catch_P_Ends_Normal catch)
              moreover have "\<exists>ys. s = Normal s'' \<and>
                              (n, \<Gamma>, (P0, s) # xs) \<in> cptn_mod_nest_call \<and>
                              fst (last ((P0, s) # xs)) = LanguageCon.com.Throw \<and>
                              snd (last ((P0, s) # xs)) = Normal s' \<and>
                               (n, \<Gamma>, (P1, Normal s') # ys) \<in> cptn_mod_nest_call \<and> 
                               (Q, t) # cfg1 = map (lift_catch P1) xs @ (P1, Normal s') # ys"
                using ass  p0_cptn   by (metis (full_types) last_length )             
              ultimately show ?thesis using some_equality[of ?P xs]
                 unfolding cond_catch_2_def by blast 
            qed
            moreover have "(SOME ys. \<exists>s' s''. cond_catch_2 n \<Gamma> P0 s xs P1 ((Q, t) # cfg1) ys s' s'') = ys"
            proof -
               let ?P = "\<lambda>ysa. s = Normal s'' \<and>
                              (n, \<Gamma>, (P0, s) # xs) \<in> cptn_mod_nest_call \<and>
                              fst (last ((P0, s) # xs)) = LanguageCon.com.Throw \<and>
                              snd (last ((P0, s) # xs)) = Normal s' \<and>
                               (n, \<Gamma>, (P1, Normal s') # ysa) \<in> cptn_mod_nest_call \<and> 
                               (Q, t) # cfg1 = map (lift_catch P1) xs @ (P1, Normal s') # ysa"
                have "(\<And>x.  \<exists>s' s''. s = Normal s'' \<and>
                          (n, \<Gamma>, (P0, s) # xs) \<in> cptn_mod_nest_call \<and>
                          fst (last ((P0, s) # xs)) = LanguageCon.com.Throw \<and>
                          snd (last ((P0, s) # xs)) = Normal s' \<and>
                          (n, \<Gamma>, (P1, Normal s') # x) \<in> cptn_mod_nest_call \<and> (Q, t) # cfg1 = map (lift_catch P1) xs @ (P1, Normal s') # x \<Longrightarrow>
                          x = ys)" using catch2_ass by auto 
                moreover have "s = Normal s'' \<and>
                      (n, \<Gamma>, (P0, s) # xs) \<in> cptn_mod_nest_call \<and>
                       fst (last ((P0, s) # xs)) = LanguageCon.com.Throw \<and>
                       snd (last ((P0, s) # xs)) = Normal s' \<and>
                      (n, \<Gamma>, (P1, Normal s') # ys) \<in> cptn_mod_nest_call \<and> 
                       (Q, t) # cfg1 = map (lift_catch P1) xs @ (P1, Normal s') # ys"
                using ass  p0_cptn by (metis (full_types) catch2_ass last_length p0_cptn)             
                ultimately show ?thesis using some_equality[of ?P ys]
                 unfolding cond_catch_2_def by blast
            qed            
            ultimately have "biggest_nest_call P0 s xs \<Gamma> n"
              using not_min_call_p1_n Catch(6) 
                    biggest_nest_call.simps(2)[of P0 P1 s "(Q, t) # cfg1" \<Gamma> n]
              by presburger
            then show ?thesis  using Cons Q' by auto
          qed
          have C:"(P0, s) # xs = (P0, s) # (Q', t) # xsa" using Cons Q' by auto
          have reP0:"redex P0 = (Call f) \<and> \<Gamma> f = Some bdy \<and> 
            (\<exists>saa. s = Normal saa) \<and> t = s " using Catch(5) Q' by auto
          then have min_call:"min_call n \<Gamma> ((Q', t) # xsa)" using Catch(1)[OF min_call C reP0 big]
            by auto
          have p1_n_cptn:"(n, \<Gamma>,  (Q, t) # cfg1) \<in> cptn_mod_nest_call"
            using Catch.prems(1) Catch.prems(2) elim_cptn_mod_nest_call_n min_call_def by blast
          also then have "(\<forall>m<n. (m, \<Gamma>, (Q, t) # cfg1) \<notin> cptn_mod_nest_call)" 
          proof-
           { fix m
             assume ass:"m<n" 
             { assume Q_m:"(m, \<Gamma>, (Q, t) # cfg1) \<in> cptn_mod_nest_call" 
               then have t_eq_s:"t=Normal s''" using Catch catch2_ass by fastforce
               then obtain xsa' s1 s1' where 
                  p0_cptn:"(m, \<Gamma>,(Q', t)#xsa') \<in> cptn_mod_nest_call"  and
                  catch_cond:"catch_cond_nest cfg1 P1 xsa' Q' (Normal s'') s1 s1' \<Gamma> m"
               using Q_m div_catch_nest[of m \<Gamma> "(Q, t) # cfg1"] Q' by blast
               have fst:"fst (last ((Q', Normal s'') # xsa)) = LanguageCon.com.Throw" 
                 using catch2_ass Cons Q' by (simp add: last_length  t_eq_s)
              have cfg:"cfg1 = map (lift_catch P1) xsa @ (P1, snd (last ((Q', Normal s'') # xsa))) # ys"
                 using catch2_ass Cons Q' by (simp add: last_length  t_eq_s)
              have snd:"snd (last ((Q', Normal s'') # xsa)) = Normal s'"
                using catch2_ass Cons Q' by (simp add: last_length  t_eq_s)
               then have "xsa=xsa'" 
                 using catch2_ass Catch_P_Ends_Normal[OF cfg fst snd catch_cond] Cons
                 by auto 
               then have False using min_call p0_cptn ass unfolding min_call_def by auto 
             } 
           } then show ?thesis by auto qed
         ultimately show ?thesis unfolding min_call_def by auto
       qed    
     qed
    }note l=this
    {assume ass:"fst (((P0, s) # xs) ! length xs) = LanguageCon.com.Skip \<and>
             (\<exists>ys. (n, \<Gamma>, (LanguageCon.com.Skip, snd (last ((P0, s) # xs))) # ys) \<in> cptn_mod_nest_call \<and>
             (Q, t) # cfg1 = map (lift_catch P1) xs @ (LanguageCon.com.Skip, snd (last ((P0, s) # xs))) # ys)"
     have ?thesis
     proof (cases "\<Gamma>\<turnstile>\<^sub>c(Catch P0 P1, s) \<rightarrow> (Q,t)")
       case True 
       thus  ?thesis
       proof (cases xs)
          case Nil thus ?thesis using Catch ass by fastforce
       next
         case (Cons xa xsa)
         then obtain ys where 
           catch2_ass:"fst (((P0, s) # xs) ! length xs) = LanguageCon.com.Skip \<and>
             (n, \<Gamma>, (LanguageCon.com.Skip, snd (last ((P0, s) # xs))) # ys) \<in> cptn_mod_nest_call \<and>
             (Q, t) # cfg1 = map (lift_catch P1) xs @ (LanguageCon.com.Skip, snd (last ((P0, s) # xs))) # ys"
            using ass by auto 
         then have t_eq:"t=s" using Catch by fastforce
         obtain mq mp1 where 
           min_call_q:"min_call mq \<Gamma> ((P0, s) # xs)" and
           min_call_p1:"min_call mp1 \<Gamma> ((Skip, snd (((P0, s) # xs) ! length xs)) # ys)"         
         using catch2_ass minimum_nest_call p0_cptn by (metis last_length)
         then have mp1_zero:"mp1=0" by (simp add: skip_min_nested_call_0)
         then have min_call: "min_call n \<Gamma> ((P0, s) # xs)"  
           using catch2_ass min_call_catch2[of n \<Gamma> P0 P1 s "(Q, t) # cfg1" xs ys]
             Catch(3,4) p0_cptn by (metis last_length)      
         have n_z:"n>0" using redex_call_cptn_mod_min_nest_call_gr_zero[OF Catch(3) Catch(4) Catch(5) True]
           by auto          
         from catch2_ass obtain Q' where Q':"Q=Catch Q' P1 \<and> xa=(Q',t)"          
           unfolding lift_catch_def using Cons
          proof -
            assume a1: "\<And>Q'. Q = Catch Q' P1 \<and> xa = (Q', t) \<Longrightarrow> thesis"
            have "(Catch (fst xa) P1, snd xa) = ((Q, t) # cfg1) ! 0"
             using catch2_ass unfolding lift_catch_def
              by (simp add: Cons case_prod_unfold)
            then show ?thesis
              using a1 by fastforce
          qed  
         have big_call:"biggest_nest_call P0 s ((Q',t)#xsa) \<Gamma> n"
         proof-
           have "\<not>(\<exists>xs. min_call n \<Gamma> ((P0, s)#xs) \<and> (Q, t) # cfg1 = map (lift_catch P1) xs)"
             using min_call catch2_ass Cons
           proof -
             have "min_call n \<Gamma> ((Catch P0 P1, s) # (Q, t) # cfg1)"
               using Catch.prems(1) Catch.prems(2) by blast
             then show ?thesis
               by (metis (no_types) Catch_P_Not_finish append_Nil2 list.simps(3) 
                     same_append_eq catch catch2_ass)
           qed
           moreover have "(\<exists>xs ys. cond_catch_1 n \<Gamma> P0 s xs P1 ((Q, t) # cfg1) ys)"
             using catch2_ass p0_cptn unfolding cond_catch_1_def last_length
             by metis
           moreover have "(SOME xs. \<exists>ys. cond_catch_1 n \<Gamma> P0 s xs P1 ((Q, t) # cfg1) ys) = xs"
           proof -
             let ?P = "\<lambda>xsa. \<exists>ys. (n, \<Gamma>,(P0, s)#xs) \<in> cptn_mod_nest_call \<and> 
                            fst (last ((P0, s) # xs)) = LanguageCon.com.Skip \<and>
                             (n, \<Gamma>, (LanguageCon.com.Skip, 
                                snd (last ((P0, s) # xsa))) # ys) \<in> cptn_mod_nest_call \<and>
                             (Q, t) # cfg1 = map (lift_catch P1) xsa @ 
                               (LanguageCon.com.Skip, snd (last ((P0, s) # xsa))) # ys"
             have "\<And>xsa. \<exists>ys. (n, \<Gamma>,(P0, s)#xsa) \<in> cptn_mod_nest_call \<and> 
                             fst (last ((P0, s) # xs)) = LanguageCon.com.Skip \<and>
                             (n, \<Gamma>, (LanguageCon.com.Skip, 
                                snd (last ((P0, s) # xsa))) # ys) \<in> cptn_mod_nest_call \<and>
                             (Q, t) # cfg1 = map (lift_catch P1) xsa @ 
                               (LanguageCon.com.Skip, snd (last ((P0, s) # xsa))) # ys \<Longrightarrow>
                           xsa = xs"
             using Catch_P_Ends_Skip catch  catch2_ass map_lift_catch_some_eq by fastforce  
             moreover have "\<exists>ys. (n, \<Gamma>,(P0, s)#xs) \<in> cptn_mod_nest_call \<and>
                               fst (last ((P0, s) # xs)) = LanguageCon.com.Skip \<and>
                             (n, \<Gamma>, (LanguageCon.com.Skip, 
                                snd (last ((P0, s) # xs))) # ys) \<in> cptn_mod_nest_call \<and>
                             (Q, t) # cfg1 = map (lift_catch P1) xs @ 
                               (LanguageCon.com.Skip, snd (last ((P0, s) # xs))) # ys" 
               using ass p0_cptn by (simp add: last_length) 
             ultimately show ?thesis using some_equality[of ?P xs]
                 unfolding cond_catch_1_def by blast 
           qed           
           ultimately have "biggest_nest_call P0 s xs \<Gamma> n"
            using  Catch(6) 
                  biggest_nest_call.simps(2)[of P0 P1 s "(Q, t) # cfg1" \<Gamma> n]
            by presburger
           then show ?thesis  using Cons Q' by auto
         qed         
         have min_call:"min_call n \<Gamma> ((Q',t)#xsa)" 
           using Catch(1)[OF min_call _ _  big_call] Catch(5) Cons Q' by fastforce   
         then have p1_n_cptn:"(n, \<Gamma>,  (Q, t) # cfg1) \<in> cptn_mod_nest_call"
            using Catch.prems(1) Catch.prems(2) elim_cptn_mod_nest_call_n min_call_def by blast   
         also then have "(\<forall>m<n. (m, \<Gamma>, (Q, t) # cfg1) \<notin> cptn_mod_nest_call)" 
          proof-
           { fix m
             assume ass:"m<n" 
             { assume Q_m:"(m, \<Gamma>, (Q, t) # cfg1) \<in> cptn_mod_nest_call" 
               then obtain xsa' s1 s1' where 
                  p0_cptn:"(m, \<Gamma>,(Q', t)#xsa') \<in> cptn_mod_nest_call"  and
                  seq:"catch_cond_nest cfg1 P1 xsa' Q' t s1 s1' \<Gamma> m"
               using div_catch_nest[of m \<Gamma> "(Q, t) # cfg1"] Q' t_eq by blast
               then have "xsa=xsa'" 
                 using catch2_ass 
                 Catch_P_Ends_Skip[of cfg1 P1 xsa Q' t ys xsa' s1 s1']  
                 Cons Q' Q_m 
                 by (simp add:  last_length)                 
               then have False using min_call p0_cptn ass unfolding min_call_def by auto 
             } 
           } then show ?thesis by auto qed          
         ultimately show ?thesis unfolding min_call_def by auto
       qed
     next
       case False 
       then have env:"\<Gamma>\<turnstile>\<^sub>c(Catch P0 P1, s) \<rightarrow>\<^sub>e (Q,t)" using Catch
         by (meson elim_cptn_mod_nest_step_c min_call_def)
       moreover then have Q:"Q=Catch P0 P1" using env_c_c' by blast        
       ultimately show ?thesis using Catch
        proof -
          obtain nn :: "(('b, 'a, 'c,'d) LanguageCon.com \<times> ('b, 'c) xstate) list \<Rightarrow> ('a \<Rightarrow> ('b, 'a, 'c,'d) LanguageCon.com option) \<Rightarrow> nat \<Rightarrow> nat" where
            f1: "\<forall>x0 x1 x2. (\<exists>v3<x2. (v3, x1, x0) \<in> cptn_mod_nest_call) = (nn x0 x1 x2 < x2 \<and> (nn x0 x1 x2, x1, x0) \<in> cptn_mod_nest_call)"
            by moura
          have f2: "(n, \<Gamma>, (LanguageCon.com.Catch P0 P1, s) # (Q, t) # cfg1) \<in> cptn_mod_nest_call \<and> (\<forall>n. \<not> n < n \<or> (n, \<Gamma>, (LanguageCon.com.Catch P0 P1, s) # (Q, t) # cfg1) \<notin> cptn_mod_nest_call)"
            using local.Catch(3) local.Catch(4) min_call_def by blast
          then have "\<not> nn ((Q, t) # cfg1) \<Gamma> n < n \<or> (nn ((Q, t) # cfg1) \<Gamma> n, \<Gamma>, (Q, t) # cfg1) \<notin> cptn_mod_nest_call"
            using False env env_c_c'  not_func_redex_cptn_mod_nest_n_env 
            by (metis Catch.prems(1) Catch.prems(2) min_call_def)
          then show ?thesis
            using f2 f1 by (meson elim_cptn_mod_nest_call_n min_call_def)
        qed
     qed   
    }
    thus ?thesis using l ass by fastforce
  qed   
qed (fastforce)+
*)

lemma cptn_mod_nest_n_1:
  assumes a0:"(n,\<Gamma>,cfs) \<in>  cptn_mod_nest_call" and
          a1:"cfs=(p,s)#cfs'" and
          a2:"\<not> (min_call n \<Gamma> cfs)"
  shows "(n-1,\<Gamma>,cfs) \<in>  cptn_mod_nest_call"
using a0 a1 a2 
by (metis (no_types, lifting) Suc_diff_1 Suc_leI cptn_mod_nest_mono less_nat_zero_code min_call_def not_less)

lemma cptn_mod_nest_tl_n_1:
  assumes a0:"(n,\<Gamma>,cfs) \<in>  cptn_mod_nest_call" and
          a1:"cfs=(p,s)#(q,t)#cfs'" and
          a2:"\<not> (min_call n \<Gamma> cfs)"
  shows "(n-1,\<Gamma>,(q,t)#cfs') \<in>  cptn_mod_nest_call"
  using a0 a1 a2
by (meson elim_cptn_mod_nest_call_n cptn_mod_nest_n_1) 

lemma cptn_mod_nest_tl_not_min:
  assumes a0:"(n,\<Gamma>,cfg) \<in>  cptn_mod_nest_call" and
          a1:"cfg=(p,s)#cfg'" and
          a2:"\<not> (min_call n \<Gamma> cfg)"
  shows "\<not> (min_call n \<Gamma> cfg')"
proof (cases cfg')
  case Nil 
  have "(\<Gamma>, []) \<notin> cptn"
    using cptn.simps by auto
  then show ?thesis unfolding min_call_def
    using cptn_eq_cptn_mod_set cptn_mod_nest_cptn_mod local.Nil by blast  
next
  case (Cons xa cfga)
  then obtain q t where "xa = (q,t)" by fastforce
  then have "(n-1,\<Gamma>,cfg') \<in>  cptn_mod_nest_call"
    using a0 a1 a2 cptn_mod_nest_tl_n_1 Cons by fastforce
  also then have "(n,\<Gamma>,cfg') \<in>  cptn_mod_nest_call"
    using cptn_mod_nest_mono Nat.diff_le_self by blast
  ultimately show ?thesis unfolding min_call_def
    using a0 a2 min_call_def by force 
qed

definition cp :: "('g\<times>'l,'p,'f,'e) body \<Rightarrow> ('g\<times>'l,'p,'f,'e)com  \<Rightarrow>
                  (('g\<times>'l)\<times>('l list),'f) xstate \<Rightarrow> (('g,'l,'p,'f,'e) confs) set" where
  "cp \<Gamma> P s \<equiv> {(\<Gamma>1,l). l!0=(P,s) \<and> (\<Gamma>,l) \<in> cptn \<and> \<Gamma>1=\<Gamma>}"  

 

lemma cp_sub: 
  assumes a0: "(\<Gamma>,(x#l0)@l1) \<in> cp \<Gamma> P s"
  shows "(\<Gamma>,(x#l0)) \<in> cp \<Gamma> P s"
proof -
  have "(x#l0)!0 = (P,s)" using a0 unfolding cp_def by auto
  also have "(\<Gamma>,(x#l0))\<in>cptn" using a0 unfolding cp_def
  using cptn_dest_2 by fastforce
  ultimately show ?thesis using a0 unfolding cp_def by blast
qed


definition cpn :: "nat \<Rightarrow> ('g\<times>'l,'p,'f,'e) body \<Rightarrow> ('g\<times>'l,'p,'f,'e)com  \<Rightarrow> 
                  (('g\<times>'l)\<times>('l list),'f) xstate \<Rightarrow> (('g,'l,'p,'f,'e) confs) set" 
where
 "cpn n \<Gamma> P s \<equiv> {(\<Gamma>1,l). l!0=(P,s) \<and> (n,\<Gamma>,l) \<in> cptn_mod_nest_call \<and> \<Gamma>1=\<Gamma>}"


end
